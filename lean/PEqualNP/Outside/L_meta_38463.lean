import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38463

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
  Nat.testBit (4008372936 * 2 ^ 32 + 3940606144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x01002b15c61b8e3c#64 ++ 0x2f427f3fce7f9e7c#64 : BitVec 128),
   (0x401c984c1ab8a285#64 ++ 0xffbd98cc7fb8e38f#64 : BitVec 128),
   (0x82c160b06140555a#64 ++ 0xf7c1e0f071c0ffff#64 : BitVec 128),
   (0x08ee00ee81ed03e0#64 ++ 0x3bfe00ff81ff03f0#64 : BitVec 128),
   (0x04f7dd0001f6f800#64 ++ 0x3dffff0001fffc00#64 : BitVec 128),
   (0x10fbf6fb7c000000#64 ++ 0x3efffffffe000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [13, 8]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x01002b15c61b8e3c 0x2f427f3fce7f9e7c

def z1 : W := mkw 0x04f7dd0001f6f800 0x3dffff0001fffc00

def z2 : W := mkw 0x08ee00ee81ed03e0 0x3bfe00ff81ff03f0

def z3 : W := mkw 0x09ee0bef87ff8be4 0x3bfe1fff8fff03f0

def z4 : W := mkw 0x10fbf6fb7c000000 0x3efffffffe000000

def z5 : W := mkw 0x401c984c1ab8a285 0xffbd98cc7fb8e38f

def z6 : W := mkw 0x82c160b06140555a 0xf7c1e0f071c0ffff

def z7 : W := mkw 0x01000b05861b8a24 0x08021f0f8e3f0000

def z8 : W := mkw 0x82c140a021405142 0xd08180c031806183

def z9 : W := mkw 0x10ea22fb7c000000 0x3afe00fffe000000

def z10 : W := mkw 0x4008004c1a080285 0xc20000cc7e00038f

def z11 : W := mkw 0x92fbf6fb7d40555a 0xffffffffffc0ffff

def z12 : W := mkw 0x820020b06000055a 0xc20000f0700003ff

def z13 : W := mkw 0x92fbf6fb7c00055a 0xfefffffffe0003ff

def z14 : W := mkw 0x0000080482198224 0x2f42183fce7f827c

def z15 : W := mkw 0x082e004e80ad02a0 0x083e000f803f0000

def z16 : W := mkw 0x820160106000541a 0xc401e0007000fc0f

def z17 : W := mkw 0x00d5d80001f0f000 0x3dfdf80001f8fc00

def z18 : W := mkw 0x01002211c4010438 0x0000003380000070

def z19 : W := mkw 0x8aef60fee1ed57fa 0xffffe0fff1ffffff

def z20 : W := mkw 0x0018904818000000 0x3ebd98cc7e000000

def z21 : W := mkw 0x10e366b364000000 0x0042673380000000

def z22 : W := mkw 0x103a964b1c000000 0x083e1f0f8e000000

def z23 : W := mkw 0x4004080402b8a285 0xc100000001b8e38f

def z24 : W := mkw 0x401c984c1ab8a285 0x083c180c0e380000

def z25 : W := mkw 0xc6fffdfc7bfeffdf 0xfffffffc7fffffff

def z26 : W := mkw 0x0536bf15c6bfae3c 0x2f7e7f3fce7f9e7c

def z27 : W := mkw 0x4004000000a02081 0xc000000001806183

def z28 : W := mkw 0x86f7d4a021e47142 0xd0bd80c031806183

def z29 : W := mkw 0x04369d0000b6a800 0x083e1f00003f0000

def z30 : W := mkw 0x86f7fdb061f6fd5a 0xfffffff071ffffff

def z31 : W := mkw 0x1022060304000000 0x0002070380000000

def z32 : W := mkw 0x820000000140555a 0xc100000001c0ffff

def z33 : W := mkw 0x50fffeff7eb8a285 0x3efffffffe380000

def z34 : W := mkw 0x4008084c1a188285 0xef0018cc7e38838f

def z35 : W := mkw 0x01002b1146128c1c 0x04007f004e009c0c

def z36 : W := mkw 0x08ee00ea01e401c0 0x10bc00c001800180

def z37 : W := mkw 0x00ea00ea00000000 0x10bc00c000000000

def z38 : W := mkw 0x18ee22fffded03e0 0x3bfe00ffffff03f0

def z39 : W := mkw 0x48ee00ee9bed03e5 0xfbfe00ffffff03ff

def z40 : W := mkw 0x1011f6117c000000 0x0401ff007e000000

def z41 : W := mkw 0x00c000a000000000 0x32c000f000000000

def z42 : W := mkw 0x04e3450001465800 0x0042670000471c00

def z43 : W := mkw 0x401c984c1ab8a285 0x3dbd980c0fb8e000

def z44 : W := mkw 0x01002b15461a8e1c 0x2f007f0c4e389e0c

def z45 : W := mkw 0x820160106000541a 0xf781e0c07180ff8f

def z46 : W := mkw 0x09ee2bffc7ff8ffc 0x3ffe7fffcfff9ffc

def z47 : W := mkw 0x01002311c4030c38 0x0042673380471c70

def z48 : W := mkw 0x92fbf6fb7d405142 0xfeffffffff806183

def z49 : W := mkw 0x00e6000001e40000 0x39fe000001ff0000

def z50 : W := mkw 0x44ffdd4c1bfefa85 0xffffffcc7fffff8f

def z51 : W := mkw 0x00c1400001405000 0x35c1e00001c0fc00

def z52 : W := mkw 0x08ee00ea01e401c0 0x39fe00c001ff0180

def z53 : W := mkw 0x4110bb115e12ac1d 0xc401ff007e00fc0f

def z54 : W := mkw 0x411cbb5ddebbaebd 0xffffffffffffffff

def z55 : W := mkw 0x411c9b4d9ebbaaa5 0x083e1f0f8e3f0000

def z56 : W := mkw 0x401098001a10a005 0xc40198007e00e00f

def z57 : W := mkw 0x48fe98ee9bfda3e5 0xffff98ffffffe3ff

def z58 : W := mkw 0x0cffddee81fffbe0 0x3fffffff81fffff0

def z59 : W := mkw 0x00000904801b8a20 0x2f427f3f807f9e70

def z60 : W := mkw 0x04ffddea01f6f800 0x3fffffff81fffc00

def z61 : W := mkw 0x00e7400001e45000 0x3dffe00001fffc00

def z62 : W := mkw 0x401c984c1ab8a285 0xc93c180c0fb8e38f

def z63 : W := mkw 0x00ea00ea01400140 0x3bfe00ff81c003f0

def z64 : W := mkw 0x83002b15c75bdf7e 0xef427f3fcfffffff

def z65 : W := mkw 0x0100010080030c38 0x0000000000471c70

def z66 : W := mkw 0x0000000000000000 0x270000004000820c

def z67 : W := mkw 0x0411dd000012f800 0x0401ff000000fc00

def z68 : W := mkw 0x080800ee800903e0 0x020000ff800003f0

def z69 : W := mkw 0x082e00ee80ad03e0 0x0a3e00ff803f03f0

def z70 : W := mkw 0x0cf7dd0481fffbe0 0x3dffff0001fffff0

def z71 : W := mkw 0x00f6980001f4a000 0x3dff980001ffe000

def z72 : W := mkw 0x401cb85c5ab8a69d 0xfffdf8fc7ff8ffff

def z73 : W := mkw 0x01e62b15c7ff8e3c 0x3ffe7f3fcfff9e7c

def z74 : W := mkw 0x100822fb7c000000 0x020000fffe000000

def z75 : W := mkw 0x11fbf6fffe09063c 0x3efffffffe00027c

def z76 : W := mkw 0x82c140a021405142 0x0000000000000000

def z77 : W := mkw 0x09ee23ffc5ef0ff8 0x3bfe67ff81ff1ff0

def z78 : W := mkw 0x40ffdc4c1ab8a285 0xffffffcc7fb8e38f

def z79 : W := mkw 0x443e9d4c1abeaa85 0x083e1f0c0e3f0000

def z80 : W := mkw 0x01002b15c61b8e3c 0x05007f004e7f9e7c

def z81 : W := mkw 0x0000000000000000 0xd08180c031806183

def z82 : W := mkw 0x820000000000541a 0xc00000000000fc0f

def z83 : W := mkw 0x50fffeff7eb8a285 0xffffffffffb8e38f

def z84 : W := mkw 0x00ea00ea00000000 0x3afe00ff80000000

def z85 : W := mkw 0x18fff6fffded03e0 0x3fffffffffff03f0

def z86 : W := mkw 0x4108225dde0906bd 0xc20000fffe0003ff

def z87 : W := mkw 0x401c904818a02081 0xd0bd80c031806183

def z88 : W := mkw 0x18fe96ef9ded03e0 0x3bfe1fff8fff03f0

def z89 : W := mkw 0x48fe98ee1bfca3c5 0xffbd98cc7fb8e38f

def z90 : W := mkw 0x1111ff15fe1b8e3c 0x2f43ff3ffe7f9e7c

def z91 : W := mkw 0x0000090000128800 0x2d427f00007f9c00

def z92 : W := mkw 0x05f7ff15c7fffe3c 0x3fffff3fcffffe7c

def z93 : W := mkw 0x01002215c609063c 0x2b42003fce7f027c

def z94 : W := mkw 0x83002bb5e61b8f7e 0xef427ffffe7f9fff

def z95 : W := mkw 0x480800ee9a0903e5 0xc20000fffe0003ff

def z96 : W := mkw 0x92e366b36540555a 0x0042673380401c70

def z97 : W := mkw 0x0018904818000000 0xffbd98cc7f80e38f

def z98 : W := mkw 0x82c160b06140555a 0x0040603000401c70

def z99 : W := mkw 0x0014980000b0a000 0x083c180000380000

def z100 : W := mkw 0x00c000a001400140 0x0040003000400070

def z101 : W := mkw 0x0118bb5dde1b8e3c 0x3ffffffffe7f9e7c

def z102 : W := mkw 0x0000000000000000 0xf78180c07180e38f

def z103 : W := mkw 0xc2ddf8fc7bf8f7df 0xfffdf8fc7ff8ffff

def z104 : W := mkw 0x05f7ff11c5f7fc38 0x3dffff3381fffc70

def z105 : W := mkw 0x00ee00ea01e40000 0x3bfe00ff81ff0000

def z106 : W := mkw 0x11082bfffe1b8e3c 0x2f427ffffe7f9e7c

def z107 : W := mkw 0x483e984e9abda2a5 0x083e180f8e3f0000

def z108 : W := mkw 0x080c004c81ed03e0 0x3bbc00cc01ff03f0

def z109 : W := mkw 0x092e0b4f86bf8aa4 0x083e1f0f8e3f0000

def z110 : W := mkw 0x0000221144000000 0x0042673380000000

def z111 : W := mkw 0x01000904821b8e3c 0x01000000007f9e7c

def z112 : W := mkw 0x10fbd4ea38000000 0x10bd80c030000000

def z113 : W := mkw 0x00002b1144128800 0x2f427f3fce7f9c00

def z114 : W := mkw 0x0404090001f6f800 0x0100000001fffc00

def z115 : W := mkw 0x14fffffb7df6f800 0x3ffffffffffffc00

def z116 : W := mkw 0x0010900018000000 0x040198007e000000

def z117 : W := mkw 0x000c004c00a80280 0x3bbc00cc01b80380

def z118 : W := mkw 0x00c000a001400140 0x33c000f001c003f0

def z119 : W := mkw 0x113abf5fde1b8e3c 0x2f7e7f3fce7f9e7c

def z120 : W := mkw 0x0404090001f6f800 0x2d427f0001fffc00

def z121 : W := mkw 0x92fbf4fa7940555a 0xf7fde0f071c0ffff

def z122 : W := mkw 0x1001661164000000 0x0000670000000000

def z123 : W := mkw 0x0437dd0000b6f800 0x0c3fff00003ffc00

def z124 : W := mkw 0x01002215c609063c 0x0200003fce00027c

def z125 : W := mkw 0x0000000000000000 0x0000000000000000

def z126 : W := mkw 0x00e6000481ed0220 0x3bfe003f81ff0270

def z127 : W := mkw 0x0804000481ed03e0 0x0100000001ff03f0

def z128 : W := mkw 0x86f7dda021f6f942 0xfdffffc031fffd83

def z129 : W := mkw 0x103ab65b5c000000 0x2e7e7f3fce000000

def z130 : W := mkw 0x01002315c40b0e38 0x2b42673f807f1e70

def z131 : W := mkw 0x103a944a18000000 0x003c000000000000

def z132 : W := mkw 0x503e9e4f1eb8a285 0xffbf9fcfffb8e38f

def z133 : W := mkw 0x00ea22fb44000000 0x3efe7fffce000000

def z134 : W := mkw 0x82c140000140555a 0xf5c1e00001c0ffff

def z135 : W := mkw 0x0026000000a40000 0x083e0000003f0000

def z136 : W := mkw 0x48ee08ee83fda3e5 0xfbfe00ff81ffe3ff

def z137 : W := mkw 0x08ef40ee81ed53e0 0x3fffe0ff81fffff0

def z138 : W := mkw 0x18ffd4eeb9ed03e0 0x3bff80ffb1ff03f0

def z139 : W := mkw 0x0000010000020800 0x0042670000471c00

def z140 : W := mkw 0x0000201040000418 0x2740603040409e7c

def z141 : W := mkw 0x10fbd6eb3c000000 0x18bf9fcfbe000000

def z142 : W := mkw 0x01002b15c61b8e3c 0x06007f3fce009e7c

def z143 : W := mkw 0x00f3f61144000000 0x3effff3fce000000

def z144 : W := mkw 0x1019f6597c000000 0x3ebdffcc7e000000

def z145 : W := mkw 0x08e200a281450160 0x0042003380470070

def z146 : W := mkw 0x10fbf6fb7c000000 0xffffffffff80e38f

def z147 : W := mkw 0x0000221144000000 0x2e427f3fce000000

def z148 : W := mkw 0x40fe984c1bfca285 0xffff98cc7fffe38f

def z149 : W := mkw 0x820160106000541a 0xe741e0307040fe7f

def z150 : W := mkw 0x00c140a020000000 0x108180c030000000

def z151 : W := mkw 0x83c163b1e5435d7a 0x0042673380471c70

def z152 : W := mkw 0x08e600a281e50160 0x39fe003381ff0070

def z153 : W := mkw 0x92c962fb7d40555a 0xf7c1e0ffffc0ffff

def z154 : W := mkw 0x0000000480090220 0x2b42003f807f0270

def z155 : W := mkw 0x00c000a001400140 0x108000c001800180

def z156 : W := mkw 0x82c140a02140555a 0xd18180c031c0ffff

def z157 : W := mkw 0x080800ea000001c0 0x000000c000000180

def z158 : W := mkw 0x08ee22ffc5ed03e0 0x3ffe7fffcfff03f0

def z159 : W := mkw 0x51fffffffebbaebd 0xffffffffffffffff

def z160 : W := mkw 0x10fa96eb1c000000 0x3afe1fff8e000000

def z161 : W := mkw 0x00f3dd0000128800 0x3dffff00007f9c00

def z162 : W := mkw 0x401898481a10a005 0xfebd98cc7e00e00f

def z163 : W := mkw 0x10fbf6fb7d400140 0x3fffffffffc003f0

def z164 : W := mkw 0x83016b15e61bde3e 0xef43ff3ffe7ffe7f

def z165 : W := mkw 0x0000000000000000 0x2540600000409c00

def z166 : W := mkw 0x93fbffffff5bdf7e 0xffffffffffffffff

def z167 : W := mkw 0x082e004e80ad02a0 0x2b7e003f807f0270

def z168 : W := mkw 0x00fbd44818000000 0x3effffcc7e000000

def z169 : W := mkw 0x820020b06000055a 0x0000003000000070

def z170 : W := mkw 0x01002b1146128c1c 0x27407f304e409e7c

def z171 : W := mkw 0x92fbf6fb7c00541a 0xfefffffffe00fc0f

def z172 : W := mkw 0x08ee00ee81ed03e0 0xffff80fff1ffe3ff

def z173 : W := mkw 0x04f7d40001e47000 0x35fde00001c0fc00

def z174 : W := mkw 0x0cf7dda281f7f960 0x3dffff3381fffc70

def z175 : W := mkw 0x00002014c0090638 0x2f42603fc07f9e7c

def z176 : W := mkw 0x4004080402b8a285 0x0000000000380000

def z177 : W := mkw 0x00ee004c01ec0280 0x3bfe00cc01ff0380

def z178 : W := mkw 0x8ae360b2e145557a 0x0042603380471c70

def z179 : W := mkw 0x82c160b06000055a 0xf6c1e0f0700003ff

def z180 : W := mkw 0x04c5490001f6f800 0x35c1e00001fffc00

def z181 : W := mkw 0x08ee00ee81ed03e0 0x11bc00c001ff03f0

def z182 : W := mkw 0x0018904818000000 0x10bd80c030000000

def z183 : W := mkw 0x01c02bb5c75b8f7c 0x3fc27fffcfff9ffc

def z184 : W := mkw 0x10d1f6b17c000000 0x36c1fff07e000000

def z185 : W := mkw 0x082e004e80ad02a0 0x3bbe00cf81bf0380

def z186 : W := mkw 0x05e36711c5475c38 0x0042673380471c70

def z187 : W := mkw 0x411c994c9abbaebd 0xffbd98cc7fffffff

def z188 : W := mkw 0x04f7dd0001f6f800 0x18bf9f0001bf6000

def z189 : W := mkw 0x400008000210a005 0xc00000000000e00f

def z190 : W := mkw 0x14f7ffb365f6f800 0x3dffff3381fffc00

def z191 : W := mkw 0x96fffffb7df6fd5a 0xffffffffffffffff

def z192 : W := mkw 0xc20820fc7a0807df 0xc20000fc7e0003ff

def z193 : W := mkw 0x0404090000b6a800 0x00000000003f0000

def z194 : W := mkw 0x8200000001405142 0xc000000001806183

def z195 : W := mkw 0x04f7dd0403fefa04 0x3fffff0c4ffffe0c

def z196 : W := mkw 0x82c160b06140555a 0x36c1e0f070401c70

def z197 : W := mkw 0x082e004a00a40080 0x003c000000000000

def z198 : W := mkw 0x00c1400000000000 0x34c1e00000000000

def z199 : W := mkw 0x1411ff117c12f800 0x0401ff007e00fc00

def z200 : W := mkw 0x40ddd84c1bf8f285 0xfffdf8cc7ff8ff8f

def z201 : W := mkw 0x10fbd64b1c000000 0x3cffff0f8e000000

def z202 : W := mkw 0x8aef60fee1ed57fa 0x3bfe60ff81ff1ff0

def z203 : W := mkw 0x0000221144000000 0x04007f004e000000

def z204 : W := mkw 0x00ea00ee80090220 0x3bfe00ff807f0270

def z205 : W := mkw 0x83c16bb5e75bdf7e 0xffc3ffffffffffff

def z206 : W := mkw 0x09ee22ffc7ed07fc 0x3bfe00ffcfff03fc

def z207 : W := mkw 0x0000000480090220 0x01000000007f0270

def z208 : W := mkw 0x820160b06000555a 0xc601e0f07000ffff

def z209 : W := mkw 0x00fbd4ea00000000 0x3effffff80000000

def z210 : W := mkw 0x04e6090001f6f800 0x39fe000001fffc00

def z211 : W := mkw 0xd2fffeff7ff8f7df 0xfffffffffff8ffff

def z212 : W := mkw 0x00f3d40000000000 0x3cffff0000000000

def z213 : W := mkw 0x10f3f6b364000000 0x3cffff3380000000

def z214 : W := mkw 0x0504090483fffe3c 0x0100000001fffe7c

def z215 : W := mkw 0x08ee00ee81ed03e0 0x087e003f807f0070

def z216 : W := mkw 0x0000080402188204 0x2f00180c4e38820c

def z217 : W := mkw 0x82c160b06140555a 0x2740603040409e7c

def z218 : W := mkw 0x1111ff117e128c1c 0x0401ff007e009c0c

def z219 : W := mkw 0x11fbfffffe1b8e3c 0x3ffffffffe7f9e7c

def z220 : W := mkw 0x0804000481ed03e0 0x2b42003f81ff03f0

def z221 : W := mkw 0x820000000000055a 0xc0000000000003ff

def z222 : W := mkw 0x401498041ab8a285 0xc50198007fb8e38f

def z223 : W := mkw 0x481c984c9bfda3e5 0xffbd98cc7fffe3ff

def z224 : W := mkw 0x08e200a6814d0360 0x2b42003f807f0270

def z225 : W := mkw 0x00c160b060000000 0x36c1e0f070000000

def z226 : W := mkw 0x0100030184030820 0x0002070380070000

def z227 : W := mkw 0x0014980000b0a000 0x3dbd980001b8e000

def z228 : W := mkw 0x401c98481ab0a085 0xd4bd98c07f80e18f

def z229 : W := mkw 0x8ac960fee14957fa 0xf7c1e0fff1c0ffff

def z230 : W := mkw 0x183e964f9cad02a0 0x083e1f0f8e3f0000

def z231 : W := mkw 0x04f3dd000156f800 0x0443ff000047fc00

def z232 : W := mkw 0x00e6090001f68800 0x3dfe7f0001ff9c00

def z233 : W := mkw 0x110822fffe09063c 0x020000fffe00027c

def z234 : W := mkw 0x10fbfffb7c128800 0x3ffffffffe7f9c00

def z235 : W := mkw 0x820160106000541a 0x0000600000001c00

def z236 : W := mkw 0x04f7dd0001f6f800 0xffffffc071ffff8f

def z237 : W := mkw 0x01000904821b8e3c 0x2d427f00007f9e7c

def z238 : W := mkw 0x0008004800000000 0x3abc00cc00000000

def z239 : W := mkw 0x101096011c000000 0x00001f000e000000

def z240 : W := mkw 0x05369f0586bfaa24 0x083e1f0f8e3f0000

def z241 : W := mkw 0x04f7d40001e47000 0x10bd800001806000

def z242 : W := mkw 0x000c084c02b88284 0x3fbc18cc4fb8838c

def z243 : W := mkw 0x0436940000a42000 0x003c000000000000

def z244 : W := mkw 0x0804000001e401c0 0x0000000001800180

def z245 : W := mkw 0x10e366b364000000 0x2e427f3fce000000

def z246 : W := mkw 0x8aef40eea1ed53e2 0xfbff80ffb1ff63f3

def z247 : W := mkw 0x411cbb5ddebbaebd 0x2f7e7f3fce7f9e7c

def z248 : W := mkw 0x10fbf6fffc090220 0x3ffffffffe7f0270

def z249 : W := mkw 0x411cbb5d5ebaae9d 0xffbdffcc7fb8ff8f

def z250 : W := mkw 0x0411dd000012f800 0x2d43ff00007ffc00

def z251 : W := mkw 0xc3ddfbfdfffbffff 0xffffffffffffffff

def z252 : W := mkw 0x04f7dda001f6f940 0x3ffffff001fffff0

def z253 : W := mkw 0x05042b15c7fffe3c 0x2f427f3fcffffe7c

def z254 : W := mkw 0x0000000480090220 0x0200003f80000270

def z255 : W := mkw 0x0004000000a00000 0x39bc000001b80000

def z256 : W := mkw 0x01002215c609063c 0x2e427f3fce00027c

def z257 : W := mkw 0x82c160b06140555a 0xd0c1e0f031c07df3

def z258 : W := mkw 0x1cfffffffdfffbe0 0x3ffffffffffffff0

def z259 : W := mkw 0x100022117c000000 0x000000007e000000

def z260 : W := mkw 0x820000000140555a 0xf78180c071c0ffff

def z261 : W := mkw 0x82c162b16540555a 0xffc3ffffffc0ffff

def z262 : W := mkw 0x00e3440000000000 0x0042670000000000

def z263 : W := mkw 0x400c084c02b8a285 0xfbbc00cc01b8e38f

def z264 : W := mkw 0x08ee00ee81ed03e0 0x12bc00ff818003f0

def z265 : W := mkw 0x401c904818a02081 0x003c000000000000

def z266 : W := mkw 0x0100020586090224 0x0000000f8e000000

def z267 : W := mkw 0x04f7dd0001f6f800 0x14bdff000180fc00

def z268 : W := mkw 0x10fbf6fb7c000000 0x087e7f3f8e000000

def z269 : W := mkw 0x10fbf6fb7c000000 0x14bdffc07e000000

def z270 : W := mkw 0x10fbd4ea38000000 0x3cffffc030000000

def z271 : W := mkw 0x8bef6bffe7ffdffe 0xffffffffffffffff

def z272 : W := mkw 0x04f7ff1145f6f800 0x3fffff3fcffffc00

def z273 : W := mkw 0x82c160b06140555a 0xc140603001c0ffff

def z274 : W := mkw 0x0000090000128800 0x01000000007f9c00

def z275 : W := mkw 0x09082bffc61b8ffc 0x2f427fffce7f9ffc

def z276 : W := mkw 0x01002b1146128c1c 0x2d427f004e7f9c0c

def z277 : W := mkw 0xcafff8fefbfdf7ff 0xfffff8ffffffffff

def z278 : W := mkw 0x0000000000000000 0x2340003000400270

def z279 : W := mkw 0x0001400000005000 0x0401e0000000fc00

def z280 : W := mkw 0x0008004818000000 0x020000cc7e000000

def z281 : W := mkw 0x103a964b1c000000 0x3ebf9fcffe000000

def z282 : W := mkw 0x001098000010a000 0x040198000000e000

def z283 : W := mkw 0x8efffdfee1fffffa 0xfffffffff1ffffff

def z284 : W := mkw 0x10c962fb7c000000 0x36c1e0fffe000000

def z285 : W := mkw 0x103bf65b7c000000 0x0c3fff0ffe000000

def z286 : W := mkw 0x503e9e4f1eb8a285 0x083e1f0f8e380000

def z287 : W := mkw 0x00f7d40001e40000 0x3dffff0001ff0000

def z288 : W := mkw 0x0000221144000000 0x0200003fce000000

def z289 : W := mkw 0x10fff6ff7ca80280 0x3fffffffffb80380

def z290 : W := mkw 0x9211f6117c00541a 0xc401ff007e00fc0f

def z291 : W := mkw 0x000c004c80a902a0 0x3bfe00ff81ff03f0

def z292 : W := mkw 0x18ffd4ea39e401c0 0x10bd80c031800180

def z293 : W := mkw 0x82c000a00140555a 0xf3c000f001c0ffff

def z294 : W := mkw 0x04f7dd0001f6f800 0x087e7f00007f1c00

def z295 : W := mkw 0x401c994c1abaaa85 0xffffffcc7fffff8f

def z296 : W := mkw 0x00ee00ee00a80280 0x3bfe00ff81b80380

def z297 : W := mkw 0x92fbf6fb7d40555a 0x3efffffffe401c70

def z298 : W := mkw 0x4104090482bbaebd 0xc100000001ffffff

def z299 : W := mkw 0x04f7fd1041f6fc18 0x3fffff3041fffe7c

def z300 : W := mkw 0x0ce345a281475960 0x0042673380471c70

def z301 : W := mkw 0x01c16bb5e61b8e3c 0x3fc3fffffe7f9e7c

def z302 : W := mkw 0x83c16bb5e75bdf7e 0x2f427f3fce7f9e7c

def z303 : W := mkw 0x04f7dd0001f6f800 0x11bd800001fffc00

def z304 : W := mkw 0x000800ea00000000 0x020000ff80000000

def z305 : W := mkw 0x00e600a001e40140 0x3bfe00f001ff03f0

def z306 : W := mkw 0x401c984c1ab8a285 0x3ebd98cc7e380000

def z307 : W := mkw 0x113a9f4f9e1b8a24 0x083e1f0f8e3f0000

def z308 : W := mkw 0x820020104140555a 0xe740603041c0ffff

def z309 : W := mkw 0x040009000012f800 0x000000000000fc00

def z310 : W := mkw 0x92fbd4ea39405142 0xd0bd80c031806183

def z311 : W := mkw 0x10fbf6fb7c000000 0x12bd80fffe000000

def z312 : W := mkw 0x4008004818000081 0xc00000c030000183

def z313 : W := mkw 0x19ffffffffff8ffc 0x3fffffffffff9ffc

def z314 : W := mkw 0x401c904818a02081 0xf7bd80c07180e38f

def z315 : W := mkw 0x080800ee800903e0 0x2b4200ff807f03f0

def z316 : W := mkw 0x10fbd4ea38000000 0x3aff80ffb0000000

def z317 : W := mkw 0x10fbf6fb7d405000 0x3fffffffffc0fc00

def z318 : W := mkw 0x401c984c1ab8a285 0xca3c18cc7e38038f

def z319 : W := mkw 0x08ef60fee1ed03e0 0x3fffe0fff1ff03f0

def z320 : W := mkw 0x0000221144000418 0x2f427f3fce409e7c

def z321 : W := mkw 0x0000000000000000 0x338000c001800380

def z322 : W := mkw 0x00d9f0f878000000 0x3efdf8fc7e000000

def z323 : W := mkw 0x4804080483fda3e5 0xc100000001ffe3ff

def z324 : W := mkw 0x01000904821b8e3c 0x2b42003f807f9e7c

def z325 : W := mkw 0x501cbaff7eb8a285 0xffbd98ffffb8e38f

def z326 : W := mkw 0x0904090483ff8ffc 0x0100000001ff9ffc

def z327 : W := mkw 0x4110bb15de1bae3d 0xef43ff3ffe7ffe7f

def z328 : W := mkw 0x00c160b060000000 0xf7c1e0f07180e38f

def z329 : W := mkw 0x00f3d40000000000 0x10bd800000000000

def z330 : W := mkw 0x080c00ee80a903e0 0x3bbc00ff81b803f0

def z331 : W := mkw 0x82cd60fc61e857da 0xfffde0fc71f8ffff

def z332 : W := mkw 0x920822fb7c00055a 0xc20000fffe0003ff

def z333 : W := mkw 0x08ee00ea01e401c0 0x3afe00ff81800180

def z334 : W := mkw 0x0018b2595c000000 0x3efffffffe000000

def z335 : W := mkw 0x83016b116612dc1e 0xc401ff007e00fc0f

def z336 : W := mkw 0x400000001a000005 0xc00000007e00000f

def z337 : W := mkw 0x8ac560b4e1ed57fa 0xf7c1e0f071ffffff

def z338 : W := mkw 0x01002b11c6138c3c 0x04427f33ce479c7c

def z339 : W := mkw 0x18fff6fffcad02a0 0x3efffffffe3f0000

def z340 : W := mkw 0x04ffdd4819f6f800 0x3fffffcc7ffffc00

def z341 : W := mkw 0xc211f8107a10f41f 0xc401f8007e00fc0f

def z342 : W := mkw 0x0014990000b2a800 0x3dffff0001fffc00

def z343 : W := mkw 0x08ee09ee81ff8be0 0x3ffe7fff81ff9ff0

def z344 : W := mkw 0x8611fd106012fc1a 0xc401ff007000fc0f

def z345 : W := mkw 0x01000b0106128804 0x00001f000e000000

def z346 : W := mkw 0x08fe98ee81fda3e0 0x3fff98ff81ffe3f0

def z347 : W := mkw 0x04f3d50001465800 0x3cffff0000471c00

def z348 : W := mkw 0x01002b15c61b8e3c 0x0a021f3fce3f027c

def z349 : W := mkw 0x0cffddea01f6f9c0 0x3dffffc001fffd80

def z350 : W := mkw 0xc21df85c7ab8f69f 0xffbdf8cc7fb8ff8f

def z351 : W := mkw 0x5011fe117e10a005 0xc401ff007e00e00f

def z352 : W := mkw 0x44ffdc4c1bfcf285 0xffbd98cc7fb8e38f

def z353 : W := mkw 0x83c16bb16752dd5e 0xf7c1fff07fc0ffff

def z354 : W := mkw 0x10e344a220000000 0x0000000000000000

def z355 : W := mkw 0x0000000001400140 0x0100000001c003f0

def z356 : W := mkw 0x8a04000481ed57fa 0xc100000001ffffff

def z357 : W := mkw 0x0018904818000000 0x083c180c0e000000

def z358 : W := mkw 0x04369d0000b6a800 0x3dbf9f0001bfe000

def z359 : W := mkw 0x00fa90ea18000000 0x3eff98fffe000000

def z360 : W := mkw 0xc2d1f8b07b50f55f 0xf7c1f8f07fc0ffff

def z361 : W := mkw 0x0000000400080200 0x2b00000c00380200

def z362 : W := mkw 0x4014980402b8a285 0xfdbd980001b8e38f

def z363 : W := mkw 0x0800000081450160 0x0000000000470070

def z364 : W := mkw 0x86f7dd0001f6fd5a 0xfdffff0001ffffff

def z365 : W := mkw 0x401098041a18a205 0xef01980c7e38e20f

def z366 : W := mkw 0x48fe90ee99ed23e1 0xfbff80ffb1ff63f3

def z367 : W := mkw 0x86d1fdb06152fd5a 0xf7c1fff071c0ffff

def z368 : W := mkw 0x82c020b06140055a 0xf3c000f071c003ff

def z369 : W := mkw 0x0008004c00080280 0x020000cc00000380

def z370 : W := mkw 0x58fffefffffda3e5 0xffffffffffffe3ff

def z371 : W := mkw 0x50ffd4ea38a02081 0xd0bd80c031806183

def z372 : W := mkw 0x401c984c1ab8a285 0xd8bd98cc3fb86183

def z373 : W := mkw 0x0014980402b8a204 0x3fbd980c4fb8e20c

def z374 : W := mkw 0x14ffddea39f6f800 0x3dffffc031fffc00

def z375 : W := mkw 0x00e2000000000000 0x38fe000000000000

def z376 : W := mkw 0x441c994c1bfefa85 0xffbd98cc7fffff8f

def z377 : W := mkw 0x0000000000000000 0x29420000007f0000

def z378 : W := mkw 0x01002a15c619863c 0x2f00183fce38827c

def z379 : W := mkw 0x01ea2bffc61b8e3c 0x3ffe7fffce7f9e7c

def z380 : W := mkw 0x10fbd4ea38000000 0x3ebd98cc7e000000

def z381 : W := mkw 0x86e365b061465d5a 0xf7c3e7f071c7ffff

def z382 : W := mkw 0x00c160b061400140 0x37c1e0f071c003f0

def z383 : W := mkw 0x401c984c1ab8a285 0xcc3d980c7e38e00f

def z384 : W := mkw 0xc2ddf0f879e075db 0xf7fde0f071c0ffff

def z385 : W := mkw 0x92e366b36540555a 0xf7c3e7f3f1c0ffff

def z386 : W := mkw 0x14ffdf4b1df6f800 0x3dffff0f8ffffc00

def z387 : W := mkw 0x4004080402b8a285 0xf78180c071b8e38f

def z388 : W := mkw 0x090822ffc60907fc 0x020000ffce0003fc

def z389 : W := mkw 0x1011f6117c000000 0x2e43ff3ffe000000

def z390 : W := mkw 0x09ee09ee83ff8ffc 0x3bfe00ff81ff9ffc

def z391 : W := mkw 0xc2ddd0e839e071c3 0xd0bd80c031806183

def z392 : W := mkw 0x00e6000001e40000 0x10bc000001800000

def z393 : W := mkw 0x820020b06140555a 0xc30000f071c0ffff

def z394 : W := mkw 0x8aee00ee81ed57fa 0xfbfe00ff81ffffff

def z395 : W := mkw 0x0000080002108004 0x040018004e00800c

def z396 : W := mkw 0x0004000001e40000 0x0100000001ff0000

def z397 : W := mkw 0x01f3ff15c61b8e3c 0x3fffff3fce7f9e7c

def z398 : W := mkw 0x0000000000000000 0x368180c070000000

def z399 : W := mkw 0x01002b15c61b8e3c 0xffc3ffffffffffff

def z400 : W := mkw 0x82eb60fa6140555a 0xffffe0fff1c0ffff

def z401 : W := mkw 0x11e36fb7e61b8e3c 0x2f427f3fce7f9e7c

def z402 : W := mkw 0x82f3f4b06140555a 0xfffffff071c0ffff

def z403 : W := mkw 0x14ffd4ea39e47000 0x10bd80c031806000

def z404 : W := mkw 0x8a0820fee00907fa 0xc20000fff00003ff

def z405 : W := mkw 0x01000904821b8e3c 0x2f00180c4e7f9e7c

def z406 : W := mkw 0x10fbfeff7e188204 0x3ffffffffe38820c

def z407 : W := mkw 0x10fbf6fb7c000418 0x3ffffffffe409e7c

def z408 : W := mkw 0x400c004c1aa80285 0xfbbc00cc7fb8038f

def z409 : W := mkw 0x0cee09ee81fffbe0 0x3bfe00ff81fffff0

def z410 : W := mkw 0x40fe98ee1ab8a285 0xffff98ffffb8e38f

def z411 : W := mkw 0x820000000140555a 0x0000000000401c70

def z412 : W := mkw 0x00c160b060000000 0x0040603000000000

def z413 : W := mkw 0x8aef60fa61e455da 0xf7fde0f071c0ffff

def z414 : W := mkw 0x000c004c00a80280 0xffbd80cc71b8e38f

def z415 : W := mkw 0x82c140a021405142 0xf3c180f031c063f3

def z416 : W := mkw 0x8aef40ea21e451c2 0xd0bd80c031806183

def z417 : W := mkw 0x0000090000128800 0x04007f0000009c00

def z418 : W := mkw 0x82c160b06140555a 0xd28180f0718063ff

def z419 : W := mkw 0x0c04090481fffbe0 0x0100000001fffff0

def z420 : W := mkw 0x0000000000000000 0x358180000180e000

def z421 : W := mkw 0x0404000001e47000 0x0000000001806000

def z422 : W := mkw 0x04f7d50001e67800 0x10ffe70001c77c00

def z423 : W := mkw 0x4018984c1a18a285 0xc60198cc7e00e38f

def z424 : W := mkw 0x08ffd4ee81ed03e0 0x3fffffff81ff03f0

def z425 : W := mkw 0x00c1400001405000 0xf7c1e0c071c0ff8f

def z426 : W := mkw 0x04e34d000156d800 0x2d427f00007f9c00

def z427 : W := mkw 0x01002914c21b8e3c 0x27406030407f9e7c

def z428 : W := mkw 0x01002b15c61b8e3c 0x08427f3f8e7f1c70

def z429 : W := mkw 0x08ea00ee814d03e0 0x024200ff804703f0

def z430 : W := mkw 0x00f3d40001405000 0x3dffff0001c0fc00

def z431 : W := mkw 0x11fbfffffe1b8a24 0x3efffffffe3f0000

def z432 : W := mkw 0x82c160106140541a 0xf5c1e00071c0fc0f

def z433 : W := mkw 0x0822000280050020 0x0002000380070000

def z434 : W := mkw 0x01002b15c61b8e3c 0x0c027f0fce3f9c0c

def z435 : W := mkw 0x10fffefb7cb0a000 0x3fffffffffb8e000

def z436 : W := mkw 0x00002a1546188204 0x2f427f3fce38820c

def z437 : W := mkw 0x010022114600041c 0x000000004e00000c

def z438 : W := mkw 0x401c984c9ab9a2a5 0xffff98ffffffe3ff

def z439 : W := mkw 0x000c004800a00080 0x10bc00c001800180

def z440 : W := mkw 0x10fff6fb7de40000 0x3fffffffffff0000

def z441 : W := mkw 0x0000291040128c18 0x2f427f30407f9e7c

def z442 : W := mkw 0x50fbf6ff7e080285 0xfefffffffe00038f

def z443 : W := mkw 0x0804000480ad02a0 0x00000000003f0000

def z444 : W := mkw 0x0511ff114612fc1c 0x0401ff004e00fc0c

def z445 : W := mkw 0x0000000080010020 0x0042003380470070

def z446 : W := mkw 0x00c140a001405140 0x37c1e0f001c0fff0

def z447 : W := mkw 0x44f7dd0403fefa85 0xfdffff0001ffff8f

def z448 : W := mkw 0x00e200a200000000 0x0042003380000000

def z449 : W := mkw 0x04e7450001e65800 0x39fe670001ff1c00

def z450 : W := mkw 0x00eb60fa60000000 0x3effe0fff0000000

def z451 : W := mkw 0x4008004c1a080285 0x0000000c0e000000

def z452 : W := mkw 0x401c984c1ab8a285 0xd1bd80c031b8e38f

def z453 : W := mkw 0x08e6000481ed03e0 0x39fe000001ff03f0

def z454 : W := mkw 0x04f7dd0481fffa20 0x3fffff3f81fffe70

def z455 : W := mkw 0x08ee08ee83fd83e4 0x3ffe18ffcfff83fc

def z456 : W := mkw 0x04f7dc0001f4f000 0x3dbd980001b8e000

def z457 : W := mkw 0x83000904835bdf7e 0xc100000001ffffff

def z458 : W := mkw 0x00000904021a8a04 0x2f427f0c4e7f9e0c

def z459 : W := mkw 0x443e9d4c1abeaa85 0xffbf9fcc7fbfe38f

def z460 : W := mkw 0x09042b15c7ff8ffc 0x2f427f3fcfff9ffc

def z461 : W := mkw 0x0100231144020c18 0x0000670000001c00

def z462 : W := mkw 0x04f3dd000012f800 0x3cffff000000fc00

def z463 : W := mkw 0x08e600a681ed03e0 0x0142003381ff03f0

def z464 : W := mkw 0x411cba5ddeb9a6bd 0xffbd98ffffb8e3ff

def z465 : W := mkw 0x04369d0000b6a800 0x2d7e7f00007f9c00

def z466 : W := mkw 0x0414990001f6f800 0x3dbd980001fffc00

def z467 : W := mkw 0x08ea00ea81450160 0x3afe00ff80470070

def z468 : W := mkw 0x08e200a281450160 0x33c200f381c703f0

def z469 : W := mkw 0x481c98ee9ab9a3e5 0xffbd98ffffb8e3ff

def z470 : W := mkw 0x0000000000000000 0xc20000c07000038f

def z471 : W := mkw 0x0cef45ee81ef5be0 0x3bfe67ff81ff1ff0

def z472 : W := mkw 0x0415dd0000b2f800 0x3dbdff0001b8fc00

def z473 : W := mkw 0x0cffd4ee81ed73e0 0x3bff80ff81ff63f0

def z474 : W := mkw 0x40ddf8fc7ab8a285 0xfffdf8fc7fb8e38f

def z475 : W := mkw 0x08c400a481ed03e0 0x33c000f001ff03f0

def z476 : W := mkw 0x86f7fdb061f6fd5a 0x3dffff3001fffc70

def z477 : W := mkw 0x82c140a021405142 0xf5c1e0c031c0fd83

def z478 : W := mkw 0x100822fb7c000000 0x2e427ffffe000000

def z479 : W := mkw 0x08ee00ee81ed03e0 0x18be00cf81bf0180

def z480 : W := mkw 0x0011d40000000000 0x0401ff0000000000

def z481 : W := mkw 0x82c160b06140555a 0xd481e0c07180fd8f

def z482 : W := mkw 0x14f7ff117df6f800 0x3dffff007ffffc00

def z483 : W := mkw 0x001c904c18a80280 0x3fbd98cc7fb80380

def z484 : W := mkw 0x82c169b06152dd5a 0xffc3fff071ffffff

def z485 : W := mkw 0x000c004c00a80280 0x083c000c00380000

def z486 : W := mkw 0x08ee20fec1ed07f8 0x3ffe60ffc1ff9ffc

def z487 : W := mkw 0x08c800ee814903e0 0x33c000ff81c003f0

def z488 : W := mkw 0x180822fffc0903e0 0x020000fffe0003f0

def z489 : W := mkw 0x000028144218861c 0x2f40783c4e789e7c

def z490 : W := mkw 0x0000000000000000 0xc10000000180e38f

def z491 : W := mkw 0x002a004a00000000 0x083e000f80000000

def z492 : W := mkw 0xc204080403f8f7df 0xc100000001f8ffff

def z493 : W := mkw 0x401c904c18a82281 0xfbbd80cc31b86383

def z494 : W := mkw 0x82c168b46358d75e 0xffc1f8fc7ff8ffff

def z495 : W := mkw 0x00c1400001405000 0x0040600000401c00

def z496 : W := mkw 0x00f3f4b060000000 0x3efffff070000000

def z497 : W := mkw 0x48fe98ee9bfda3e5 0x3bfe18ff8fff03f0

def z498 : W := mkw 0x000000a000000140 0x020000f0000003f0

def z499 : W := mkw 0x0000201040000418 0x0400600040009c0c

def z500 : W := mkw 0x44f7dd001bf6f805 0xfdffff007ffffc0f

def z501 : W := mkw 0x441ddd4c1abafa85 0xffbdffcc7fb8ff8f

def z502 : W := mkw 0x01002b1146128c1c 0x2e427f3fce009c0c

def z503 : W := mkw 0x1011d40038000000 0x0001800030000000

def z504 : W := mkw 0x103ab6fb7c000000 0x0a3e1ffffe000000

def z505 : W := mkw 0x4008004c1a080285 0xf78180cc7f80e38f

def z506 : W := mkw 0x10f3f6b37c000000 0x0443ff33fe000000

def z507 : W := mkw 0x82c160b4e149577a 0xffc3e0fff1ffffff

def z508 : W := mkw 0x08ee00ee01ec03c0 0x3bbc00cc01b80380

def z509 : W := mkw 0x1008024b1c000000 0x0000000f8e000000

def z510 : W := mkw 0x00e2000001440000 0x0042000000470000

def z511 : W := mkw 0x0000000000000000 0x2c427f0000000000

def z512 : W := mkw 0x00f7dc0000b0a000 0x3dffff0001b8e000

def z513 : W := mkw 0x04f69d0001f6a800 0x39fe1f0001ff0000

def z514 : W := mkw 0x0dffffffc7fffffc 0x3fffffffcffffffc

def z515 : W := mkw 0x4004080402b8a285 0xef00180c4fb8e38f

def z516 : W := mkw 0x100022b364000000 0x0000003380000000

def z517 : W := mkw 0x820020b06000055a 0xf78180f07180e3ff

def z518 : W := mkw 0x44ffdd4c1bfefa85 0x3dffff0c0ffffc00

def z519 : W := mkw 0x01000b05861b8a24 0x2f021f0fce3f820c

def z520 : W := mkw 0x14fbfffb7c12f800 0x3efffffffe00fc00

def z521 : W := mkw 0x08000004800903e0 0x00000000000003f0

def z522 : W := mkw 0x54ffffff7ffefa85 0xffffffffffffff8f

def z523 : W := mkw 0x01002b15c61b8e3c 0x01426733807f9e7c

def z524 : W := mkw 0xc21c984c1bf8f7df 0xffbd98cc7ff8ffff

def z525 : W := mkw 0x0000000480090220 0x0802000f803f0000

def z526 : W := mkw 0x0032940000000000 0x083e1f0000000000

def z527 : W := mkw 0xc2ddd8ec3bf8f3c7 0xffbd98cc7fb8e38f

def z528 : W := mkw 0x143e9f4b1cb6a800 0x083e1f0f8e3f0000

def z529 : W := mkw 0x001c984818b0a000 0x3fbd98cc7fb8e000

def z530 : W := mkw 0x14fbf7fb7d465800 0x3efffffffe471c00

def z531 : W := mkw 0x08fe90ee99ed03e0 0x3fff98ffffff03f0

def z532 : W := mkw 0x01000904821b8a24 0x00000000003f0000

def z533 : W := mkw 0x04e3450001465800 0x35c3e70001c7fc00

def z534 : W := mkw 0x05f7ff1147f6fc1c 0x3dffff004ffffc0c

def z535 : W := mkw 0x50ffdcee3ab8a285 0xffbd98cc7fb8e38f

def z536 : W := mkw 0x00c160b061405000 0x37c1e0f071c0fc00

def z537 : W := mkw 0x01002311c4030c38 0x27426733c0479e7c

def z538 : W := mkw 0x00c1601041405418 0x37c1e03041c0fe7c

def z539 : W := mkw 0x820000a020000142 0xc00000c030000183

def z540 : W := mkw 0x05f7dd0483fffe3c 0x3dffff0001fffe7c

def z541 : W := mkw 0x82c160b06140555a 0xc24060f070401fff

def z542 : W := mkw 0x82c160b06140555a 0xc441e0307040fc7f

def z543 : W := mkw 0x83c163b1e5435d7a 0xf7c3e7f3f1c7ffff

def z544 : W := mkw 0x08ee004e81ed02a0 0x39fe000f81ff0000

def z545 : W := mkw 0x9afff6fffded57fa 0xffffffffffffffff

def z546 : W := mkw 0x830022b5e609077e 0xc20000fffe0003ff

def z547 : W := mkw 0x14e367b365465800 0x0042673380471c00

def z548 : W := mkw 0x0000000000000000 0xc40180007000e00f

def z549 : W := mkw 0x83c162b5e749577e 0xf7c1e0ffffc0ffff

def z550 : W := mkw 0x04d1dd000152f800 0x35c1ff0001c0fc00

def z551 : W := mkw 0x401cba5d5eb8a285 0xffffffffffb8e38f

def z552 : W := mkw 0x01c16b15c75bde3c 0x3fc3ff3fcffffe7c

def z553 : W := mkw 0x0004000400a80280 0x0100000001b80380

def z554 : W := mkw 0x0000201040000418 0xf7c1e0f071c0ffff

def z555 : W := mkw 0x00c149000152d800 0x3dc3ff0001fffc00

def z556 : W := mkw 0x01002315c60b0e3c 0x0242673fce471e7c

def z557 : W := mkw 0x01000b05861b8e3c 0x09021f0f8e7f9e7c

def z558 : W := mkw 0x01002b15c61b8a24 0x2e427f3fce3f0000

def z559 : W := mkw 0x0014900000a02000 0x10bd800001806000

def z560 : W := mkw 0x080000a280010160 0x0000003380000070

def z561 : W := mkw 0x010000048209063c 0x000000000000027c

def z562 : W := mkw 0x86f7f4b061e4755a 0xf7fde0f071c0ffff

def z563 : W := mkw 0x82c160b06000541a 0xf6c1e0f07000fc0f

def z564 : W := mkw 0x401c904c1aa82285 0xd2bd80cc7f80638f

def z565 : W := mkw 0x0000080402188204 0x010000000038820c

def z566 : W := mkw 0x8ae360b2e145557a 0xf7c3e0f3f1c7ffff

def z567 : W := mkw 0x18fbf6fbfd450160 0x3efffffffe470070

def z568 : W := mkw 0x11fbfffb7e128c1c 0x3efffffffe009c0c

def z569 : W := mkw 0x0000080402188204 0xff8198cc7fb8e38f

def z570 : W := mkw 0x100800ea38000000 0x000000c030000000

def z571 : W := mkw 0x10fbf4fa78000000 0x36fde0f070000000

def z572 : W := mkw 0x0010900000000000 0x3cbd980000000000

def z573 : W := mkw 0x01002b11c4138c38 0x2d427f33807f9c70

def z574 : W := mkw 0x01002215c609063c 0x2740603fce409e7c

def z575 : W := mkw 0x0cffdd4e81fffaa0 0x3dffff0f81fffc00

def z576 : W := mkw 0x49febbffdfffaffd 0xffffffffffffffff

def z577 : W := mkw 0x41082b5dde1b8ebd 0xef427ffffe7f9fff

def z578 : W := mkw 0x10e366b364000000 0x36c3e7f3f0000000

def z579 : W := mkw 0x0511ff15c61bfe3c 0x2f43ff3fce7ffe7c

def z580 : W := mkw 0x000020b060000000 0x020000f070000000

def z581 : W := mkw 0x15fffffffffffe3c 0x3ffffffffffffe7c

def z582 : W := mkw 0x82c160b06140555a 0x35c1e03001c0fc70

def z583 : W := mkw 0x82c160b06140555a 0x33c060f001c01ff0

def z584 : W := mkw 0x0000201040000418 0x020000304000027c

def z585 : W := mkw 0x4010900018002001 0xc001800030006003

def z586 : W := mkw 0x0000000000000000 0x2a42003f80000000

def z587 : W := mkw 0x04f7d40001e47000 0x39ff800001ff6000

def z588 : W := mkw 0x11fbf7fbfc030c38 0x3efffffffe471c70

def z589 : W := mkw 0x0114bb15c6bbae3c 0x3fffff3fcffffe7c

def z590 : W := mkw 0x0422050000060800 0x0002070000070000

def z591 : W := mkw 0x01000b05861b8a24 0x2d427f0f8e7f9c00

def z592 : W := mkw 0x18e366b3e5450160 0x0042673380470070

def z593 : W := mkw 0x400c084c1ab8a285 0xc30000cc7fb8e38f

def z594 : W := mkw 0x05e36f15c75fde3c 0x2f427f3fce7f9e7c

def z595 : W := mkw 0x09e223b3c5470d78 0x0042673380471c70

def z596 : W := mkw 0x83c169b4e35bdf7e 0xf7c1e0f071ffffff

def z597 : W := mkw 0x18fbf6fffc0903e0 0x3efffffffe0003f0

def z598 : W := mkw 0x082e004e81ed03e0 0x093e000f81ff03f0

def z599 : W := mkw 0x0000090000128800 0x08021f00003f0000

def z600 : W := mkw 0x0000000402080204 0x0200000c4e00020c

def z601 : W := mkw 0x50fff6fb7ca02081 0xfeffffffff806183

def z602 : W := mkw 0x10f3f6117c000000 0x3cffff007e000000

def z603 : W := mkw 0x48fe90ea19e421c1 0xd0bd80c031806183

def z604 : W := mkw 0x092e2b5fc6bf8ebc 0x2f7e7f3fce7f9e7c

def z605 : W := mkw 0x87f7ffb5e7ffff7e 0xffffffffffffffff

def z606 : W := mkw 0x0004080000b0a000 0x0100000001b8e000

def z607 : W := mkw 0x00c0000001400000 0x31c0000001c00000

def z608 : W := mkw 0x08ea00ee800903e0 0x3afe00ff800003f0

def z609 : W := mkw 0x10eb66fb64000000 0x3afe67ff80000000

def z610 : W := mkw 0x04f7fdb061f6f800 0x3ffffff071fffc00

def z611 : W := mkw 0x401c984818b0a081 0xfdbd98c031b8e183

def z612 : W := mkw 0x11e367b3e4030c38 0x0042673380471c70

def z613 : W := mkw 0x04109d000012a800 0x00001f0000000000

def z614 : W := mkw 0x01002311c4030c38 0x2e427f3fce471c70

def z615 : W := mkw 0x18fff6fb7de401c0 0x3effffffff800180

def z616 : W := mkw 0x82c140a021405142 0xf78180c07180e38f

def z617 : W := mkw 0x001c984c00b8a280 0x3fbd98cc01b8e380

def z618 : W := mkw 0x0808004e800902a0 0x0000000f80000000

def z619 : W := mkw 0x080c00ee81ed03e0 0x030000ff81ff03f0

def z620 : W := mkw 0x401098001a10a005 0x000018000e000000

def z621 : W := mkw 0x0000201040000000 0x2640603040000000

def z622 : W := mkw 0x0000000000000418 0x0100000000409e7c

def z623 : W := mkw 0x04369d0001f6f800 0x093e1f0001fffc00

def z624 : W := mkw 0x0000080000108000 0x2d00180000388000

def z625 : W := mkw 0x86f7fd1061f6fc1a 0xfdffff0071fffc0f

def z626 : W := mkw 0x40dc98ec1bf8a3c5 0xfffd98fc7ff8e3ff

def z627 : W := mkw 0x0100090002128c1c 0x0000000000009c0c

def z628 : W := mkw 0x0cffd4ea01e471c0 0x10bd80c001806180

def z629 : W := mkw 0xc2c568b463f8f7df 0xf7c1e0f071f8ffff

def z630 : W := mkw 0x00cc00ec01e803c0 0x3bfc00fc01f803f0

def z631 : W := mkw 0x401498001ab0a005 0xfdbd98007fb8e00f

def z632 : W := mkw 0x14fffffb7cb6a800 0x3efffffffe3f0000

def z633 : W := mkw 0x4411dd001a12f805 0xc401ff007e00fc0f

def z634 : W := mkw 0x483e984e9abda2a5 0xffbf98cfffbfe38f

def z635 : W := mkw 0x500822ff7e080285 0xc20000fffe00038f

def z636 : W := mkw 0x00c160b060000418 0x37c1e0f070409e7c

def z637 : W := mkw 0x411c9b4d9ebbaaa5 0xffbf9fcfffbfe38f

def z638 : W := mkw 0x86c569b061f6fd5a 0xf7c1e0f071ffffff

def z639 : W := mkw 0x4404090403fefa85 0xc100000001ffff8f

def z640 : W := mkw 0x04e74d0001f6f800 0x0142670001fffc00

def z641 : W := mkw 0x45ffff5ddffffebd 0xffffffffffffffff

def z642 : W := mkw 0x0000080402188204 0x0800180c0e380000

def z643 : W := mkw 0x820020b06000055a 0xe74060f070409fff

def z644 : W := mkw 0x00c020b041400558 0x37c060f041c09ffc

def z645 : W := mkw 0x86e365b061465d5a 0x0042673000471c70

def z646 : W := mkw 0x44ffdd4819f6f881 0xfdffffc031fffd83

def z647 : W := mkw 0x4cffddee9bfffbe5 0xffffffffffffffff

def z648 : W := mkw 0x92d1f6b17d40555a 0xf7c1fff07fc0ffff

def z649 : W := mkw 0x0000020104000000 0x08021f0f8e000000

def z650 : W := mkw 0x82c160b061405142 0xf6c1e0f071806183

def z651 : W := mkw 0x0018984c1a188204 0x3fbd98cc7e38820c

def z652 : W := mkw 0x18ef66ffe5ed03e0 0x3bfe67ff81ff03f0

def z653 : W := mkw 0x0cfe9dee81ffabe0 0x3bfe1fff81ff03f0

def z654 : W := mkw 0x0000000000000000 0x2e00180c4e000000

def z655 : W := mkw 0x82d5f8b061f0f55a 0xfffdf8f071f8ffff

def z656 : W := mkw 0x8604090001f6fd5a 0xc100000001ffffff

def z657 : W := mkw 0xc21cb8fc7ab8a7df 0xffbd98fc7fb8e3ff

def z658 : W := mkw 0x50fbfefb7e10a005 0xfefffffffe00e00f

def z659 : W := mkw 0x0000201040000418 0x0040603000401c70

def z660 : W := mkw 0x820020106000041a 0xc00000007000000f

def z661 : W := mkw 0x44ffd44819e47081 0xd0bd80c031806183

def z662 : W := mkw 0x401098001a10a005 0xf78198c07f80e38f

def z663 : W := mkw 0x82e760b061e4555a 0xffffe0f071ffffff

def z664 : W := mkw 0x00c162b164000000 0x3ec3fffffe000000

def z665 : W := mkw 0x01002b15c61b8e3c 0x0300003fce7f9e7c

def z666 : W := mkw 0x8aee20fee1ed07fa 0xfbfe00fff1ff03ff

def z667 : W := mkw 0x04f7dd0000b6a800 0x3cffff00003f0000

def z668 : W := mkw 0xc2c960fc7b4857df 0xf7c1e0fc7fc0ffff

def z669 : W := mkw 0x08ee00ea81e501e0 0x10fe00f381c701f0

def z670 : W := mkw 0x00c000a481490360 0x3bc200ff81ff03f0

def z671 : W := mkw 0x05f7df0587fffa24 0x3dffff0f8ffffc00

def z672 : W := mkw 0x401c984c1ab8a285 0x3bbc18cc0fb80380

def z673 : W := mkw 0x04e3440001445000 0x0000000000000000

def z674 : W := mkw 0x0000000001405000 0x0100000001c0fc00

def z675 : W := mkw 0x501dfe5d7eb8a285 0xffbdffcc7fb8e38f

def z676 : W := mkw 0x10fbf6fb7c000000 0x10ffe7f3b0000000

def z677 : W := mkw 0x401c984c1ab8a285 0x2f3c180c4e38820c

def z678 : W := mkw 0x0400010001465800 0x0000000000471c00

def z679 : W := mkw 0x0411d40000007000 0x0001800000006000

def z680 : W := mkw 0x4018904c1a080285 0xfebd98cc7e00038f

def z681 : W := mkw 0x01000b05861b8a24 0x2b421f3f8e7f0270

def z682 : W := mkw 0x08ee00ee80ad02a0 0x3afe00ff803f0000

def z683 : W := mkw 0x0401450000025800 0x0000670000001c00

def z684 : W := mkw 0x0001601060000000 0x0401e00070000000

def z685 : W := mkw 0x1019f6fb7c000000 0x0601fffffe000000

def z686 : W := mkw 0x8201400020005002 0xc001800030006003

def z687 : W := mkw 0x41042b15c6bbaebd 0xef427f3fcfffffff

def z688 : W := mkw 0x1018b2fb7c000000 0x3ebd98fffe000000

def z689 : W := mkw 0x0014980000b0a000 0xffbd98c071b8e38f

def z690 : W := mkw 0x00c000a001400140 0xf7c180f071c0e3ff

def z691 : W := mkw 0x00c1400001405000 0x1081800001806000

def z692 : W := mkw 0x04ffdd4c01fefa80 0x3fffffcc01ffff80

def z693 : W := mkw 0x82d9f0f87940555a 0xfffdf8fc7fc0ffff

def z694 : W := mkw 0x4000000402080285 0xc00000000000038f

def z695 : W := mkw 0x08ee00ea01e401c0 0x33fc00f001c003f0

def z696 : W := mkw 0x0c3e9d4e80bfaaa0 0x083e1f0f803f0000

def z697 : W := mkw 0x09e22bb7c75f8f7c 0x2f427f3fce7f9e7c

def z698 : W := mkw 0x14fff6fb7de47000 0x3effffffff806000

def z699 : W := mkw 0x401c904818a02081 0xfebd98cc7f806183

def z700 : W := mkw 0x0415dd0001f6f800 0x0501ff0001fffc00

def z701 : W := mkw 0x820160106140555a 0xc501e00071c0ffff

def z702 : W := mkw 0x04f7d40001e47000 0x3cffff0001806000

def z703 : W := mkw 0x00002215c4090220 0x2f427f3fce7f0270

def z704 : W := mkw 0x10eb66fb7c000000 0x024267fffe000000

def z705 : W := mkw 0x08e200a201440140 0x0000000000000000

def z706 : W := mkw 0x010c2b5dc6bb8ebc 0x3ffe7fffcfff9ffc

def z707 : W := mkw 0x86e364b06144555a 0xf7c1e0f071c0ffff

def z708 : W := mkw 0x01002b15c61b8e3c 0x0a427f3fce7f1e7c

def z709 : W := mkw 0x103a964b1c000000 0xffbf9fcfff80e38f

def z710 : W := mkw 0x48ee00ee81ed23e1 0xfbfe00ff81ff63f3

def z711 : W := mkw 0x103ab65b5c000418 0x2f7e7f3fce409e7c

def z712 : W := mkw 0x0504090482bfaa24 0x00000000003f0000

def z713 : W := mkw 0x82eb62fb6540555a 0xffffffffffc0ffff

def z714 : W := mkw 0x082e00ee81ed03e0 0x0b3e00ff81ff03f0

def z715 : W := mkw 0x0511ff114412fc18 0x0401ff000000fc00

def z716 : W := mkw 0x04f7dda001f6f800 0x3ffffff001fffc00

def z717 : W := mkw 0x92fbf6fb7c00055a 0x3efffffffe000070

def z718 : W := mkw 0x08ef40ee81ed53e0 0x3bfe60ff81ff1ff0

def z719 : W := mkw 0x140c2bfb7df6f800 0x030000fffffffc00

def z720 : W := mkw 0x10eb66fb64000000 0x3efe7fffce000000

def z721 : W := mkw 0x00f3dd000152d800 0x3dffff0001fffc00

def z722 : W := mkw 0x04f7d50001e67800 0x39ffe70001ff7c00

def z723 : W := mkw 0x8636bdb060b6ad5a 0xca3e1ff0703f03ff

def z724 : W := mkw 0x820000000140555a 0xd18180c031c0ffff

def z725 : W := mkw 0x04f7dd0001f6f800 0xfdffff0071fffc0f

def z726 : W := mkw 0x10fbd6eb3c000000 0x3ebf9fcffe000000

def z727 : W := mkw 0x44eb454c1b4e5a85 0xc24267cc7e471f8f

def z728 : W := mkw 0x96ffd4ea39e47142 0xd0bd80c031806183

def z729 : W := mkw 0x08ee00ea81e501e0 0x39fe00f381ff01f0

def z730 : W := mkw 0x82c160b06140555a 0xd1c1e0f031c0ffff

def z731 : W := mkw 0x1815f615fded03e0 0x0501ff007fff03f0

def z732 : W := mkw 0x923a964b1d40555a 0xc93e1f0f8fc0ffff

def z733 : W := mkw 0x401c90481aa02085 0xd0bd80c07f80618f

def z734 : W := mkw 0x04f7dd0019f6f800 0x3dffff007ffffc00

def z735 : W := mkw 0x8a2f605ee0ad56ba 0xcc3fe00ff03ffc0f

def z736 : W := mkw 0x0437dd0001f6f800 0x0d3fff0001fffc00

def z737 : W := mkw 0x01002315c40b0e38 0x2f427f3fce7f1e70

def z738 : W := mkw 0x82c140a02140555a 0xf5c1e0c031c0ffff

def z739 : W := mkw 0x441c994c1abeaa85 0xffbd98cc7fbfe38f

def z740 : W := mkw 0x401c984c1ab8a285 0xd6bd98cc7f80e38f

def z741 : W := mkw 0x82e364b06140555a 0xf7c3e7f071c0ffff

def z742 : W := mkw 0x10fa96eb1c000000 0x087e1f3f8e000000

def z743 : W := mkw 0x00f7d40001e45000 0x3dffff0001fffc00

def z744 : W := mkw 0xc2ddf8fc7bf8f7df 0x087c783c0e781c70

def z745 : W := mkw 0x82c160b06140555a 0xd38180f071c0ffff

def z746 : W := mkw 0x04f7dd0003f6f804 0x3dffff004ffffc0c

def z747 : W := mkw 0x04f69d0001f6a800 0x3dfe7f0001ff9c00

def z748 : W := mkw 0x50fbf6fb7c002001 0xfefffffffe006003

def z749 : W := mkw 0x04369d0000b6a800 0x0c3e7f00003f9c00

def z750 : W := mkw 0x82c140a02140555a 0xf78180c071c0ffff

def z751 : W := mkw 0x10fbd6eb1c000000 0x3effffff8e000000

def z752 : W := mkw 0x0437dd0000b6f800 0x3dbfff0001bffc00

def z753 : W := mkw 0x10fbf6fb7c000418 0x3efffffffe00027c

def z754 : W := mkw 0x4904090483ffaffd 0xc100000001ffffff

def z755 : W := mkw 0x04f7dda001f6f940 0xfffffff071ffffff

def z756 : W := mkw 0x090822ffc40907f8 0x020000ff800003f0

def z757 : W := mkw 0x001892491c000000 0x3ebf9fcffe000000

def z758 : W := mkw 0x10fbf65b7c000000 0x3cffff0ffe000000

def z759 : W := mkw 0x923ab6fb7c00055a 0xca3e1ffffe0003ff

def z760 : W := mkw 0x92fbf6fb7c00541a 0xffffffffff80ff8f

def z761 : W := mkw 0x002a225b44000000 0x2e7e7f3fce000000

def z762 : W := mkw 0x453e9f4d9ebfaaa5 0x083e1f0f8e3f0000

def z763 : W := mkw 0x401c984c1ab8a285 0xd5bd98c07fb8e38f

def z764 : W := mkw 0x820160106000541a 0xf7c1e0f071c0ffff

def z765 : W := mkw 0x18fbf6fb7c0001c0 0x3efffffffe000180

def z766 : W := mkw 0x10fa96eb1c000000 0x18be1fcf8e000000

def z767 : W := mkw 0x820020104140555a 0xf7c1e0f071c0ffff

def z768 : W := mkw 0x08e600a281e50160 0x3bfe00f381ff03f0

def z769 : W := mkw 0x001892491c000000 0x083e1f0f8e000000

def z770 : W := mkw 0x92fbf6fb7d40555a 0x087e7f3f8e401c70

def z771 : W := mkw 0x82c162b16540555a 0xf7c3e7f3f1c0ffff

def z772 : W := mkw 0x18ef44eea1ed03e0 0x3bfe00ff81ff03f0

def z773 : W := mkw 0x00e6000081e50020 0x39fe003381ff0070

def z774 : W := mkw 0x10fbf6fb7c000000 0xfeffffffff806183

def z775 : W := mkw 0x00ea00ee81490360 0x3bfe00ff81ff03f0

def z776 : W := mkw 0x10fbf6fb7c000000 0x3ffffffffe409c00

def z777 : W := mkw 0x441c9d4c1abaaa85 0xffbd9fcc7fb8e38f

def z778 : W := mkw 0x190822fffe0907fc 0x020000fffe0003fc

def z779 : W := mkw 0x8bc569b4e3ffdffe 0xf7c1e0f071ffffff

def z780 : W := mkw 0x08ea00ee800903e0 0x3bfe00ff807f03f0

def z781 : W := mkw 0x401c984c1ab8a285 0xdcbd98cc7fb8e18f

def z782 : W := mkw 0x82f3f6b16540555a 0xffffffffffc0ffff

def z783 : W := mkw 0x11fbddeeba1b8e3c 0x11bd80c0307f9e7c

def z784 : W := mkw 0x4104090482bbaaa5 0x00000000003f0000

def z785 : W := mkw 0x401c984c9ab9a2a5 0xffbd98ffffb8e3ff

def z786 : W := mkw 0x08ee00ee81ed03e0 0x13bc00ff81ff03f0

def z787 : W := mkw 0x10fbf6fb7d400000 0x3fffffffffc00000

def z788 : W := mkw 0x103a964b1c000000 0x0a3e1fcffe000000

def z789 : W := mkw 0x10fbf6fb7c000000 0x3afe7fff8e000000

def z790 : W := mkw 0x50e76eb766b8a285 0xc142673381b8e38f

def z791 : W := mkw 0x0014990000b2a800 0x2d7e7f00007f9c00

def z792 : W := mkw 0x00f3f61145405418 0x3fffff3fcfc0fe7c

def z793 : W := mkw 0x00ee00ea01e40140 0x3bfe00ff81ff03f0

def z794 : W := mkw 0x08ee00ea81e50160 0x3bfe00ff81ff0070

def z795 : W := mkw 0x92fbf6fb7d40555a 0xfeffffffffc07df3

def z796 : W := mkw 0x0904090483ff8be4 0x0100000001ff03f0

def z797 : W := mkw 0x08ee00ee81ed53e0 0x3bfe00ff81fffff0

def z798 : W := mkw 0x92fbf6fb7d40555a 0x3ffffffffe409e7c

def z799 : W := mkw 0x83c14ba5a75bdb66 0xd8839fcfbfbf6183

def z800 : W := mkw 0x00fbf6595c000000 0x3efffffffe000000

def z801 : W := mkw 0x92fbf6fb7c00041a 0xfefffffffe00000f

def z802 : W := mkw 0x0cef44ee81ed53e0 0x3bfe00ff81ff03f0

def z803 : W := mkw 0x10fbf6fb7c000000 0x18ffffffbe000000

def z804 : W := mkw 0x50fbf6fb7c000081 0xfefffffffe000183

def z805 : W := mkw 0x4c3e9d4e9abfaaa5 0x083e1f0f8e3f0000

def z806 : W := mkw 0x010822ffc609063c 0x020000ffce00027c

def z807 : W := mkw 0x401c984c9ab9a2a5 0xffbd98cc7fffe3ff

def z808 : W := mkw 0x8be363b3e5475d7a 0x0042673380471c70

def z809 : W := mkw 0x08ee00ee81ed03e0 0x0a7e00ff807f03f0

def z810 : W := mkw 0x04f7dd0001f6f800 0x3fffff0c4ffffc00

def z811 : W := mkw 0x103bd64b1c000000 0x0c3fff0f8e000000

def z812 : W := mkw 0x82c160b06140555a 0xffc3fff071c0ffff

def z813 : W := mkw 0x401c994c1abaaa85 0xffbd98cc7fffff8f

def z814 : W := mkw 0x05f7f615c7ed763c 0x12bd803fcf80627c

def z815 : W := mkw 0x103ab65b5c000000 0x0c3e7f0fce000000

def z816 : W := mkw 0x08ee004e81ed02a0 0x3bfe003f81ff0270

def z817 : W := mkw 0x103bd64b3c000000 0x083f9f0fbe000000

def z818 : W := mkw 0x00e600a481ed0360 0x3bfe00ff81ff03f0

def z819 : W := mkw 0x0000000000000418 0xf78180c071c0ffff

def z820 : W := mkw 0x4018904c1a080285 0xffbd98cc7f80e38f

def z821 : W := mkw 0x92fbf6fb7c000142 0xfefffffffe000183

def z822 : W := mkw 0x103bf6fb7c000000 0x0e3ffffffe000000

def z823 : W := mkw 0x10fbf6fb7d405000 0xffffffffffc0ff8f

def z824 : W := mkw 0x103ab65b5c000000 0x0a3e1f3fce000000

def z825 : W := mkw 0x04e7450001e65800 0x3dffe70001fffc00

def z826 : W := mkw 0x0904090482bf8aa4 0x00000000003f0000

def z827 : W := mkw 0x0004090000b28800 0x3dfe7f0001ff9c00

def z828 : W := mkw 0x41042914c2bbaebd 0xf7c1e0f071ffffff

def z829 : W := mkw 0x86f7dda021f6f942 0x3dffff0001fffc00

def z830 : W := mkw 0x04f7dd0000b6a800 0x3dffff00007f9c00

def z831 : W := mkw 0x0c19ddee801bfbe0 0x0601ffff8000fff0

def z832 : W := mkw 0x04f7dd0001f6f940 0x3dffff0001fffff0

def z833 : W := mkw 0x10fbf6fb7c000000 0x3ffffffffe400270

def z834 : W := mkw 0x92fbf6fb7d405142 0x3efffffffe000000

def z835 : W := mkw 0x0510bf114612ac1c 0x04007f004e009c0c

def z836 : W := mkw 0x00fab2fb5c000000 0x3efffffffe000000

def z837 : W := mkw 0x0104090483ff8e3c 0x0100000001ff9e7c

def z838 : W := mkw 0x41002b15c61bae3d 0xef427f3fce7ffe7f

def z839 : W := mkw 0x00002215c4090638 0x2f427f3fce7f9e7c

def z840 : W := mkw 0x82c140a02140555a 0xf3c180f031c0ffff

def z841 : W := mkw 0x92fbf6fb7d40555a 0xfefffffffe40fc7f

def z842 : W := mkw 0x92fbf6fb7d40555a 0xfeffffffff8063ff

def z843 : W := mkw 0x0cf7dd0001f6f9c0 0x3dffff0001fffd80

def z844 : W := mkw 0x9311ff117e12dc1e 0xc401ff007e00fc0f

def z845 : W := mkw 0x00f3d60104000000 0x3cffff0f8e000000

def z846 : W := mkw 0x1019f6fb7c000000 0x3ebdfffffe000000

def z847 : W := mkw 0x82e360b26140555a 0xf7c3e0f3f1c0ffff

def z848 : W := mkw 0x103bf65b7c000000 0x083e7f0f8e000000

def z849 : W := mkw 0x10f3f6117c000000 0x3effff3ffe000000

def z850 : W := mkw 0x14fbf6fb7c007000 0x3efffffffe006000

def z851 : W := mkw 0x00ee00ee80a902a0 0x3bfe00ff81ff03f0

def z852 : W := mkw 0x00d9f2f97c000000 0x3efffffffe000000

def z853 : W := mkw 0x08ee00ee81ed03e0 0x3ffe7fff81ff03f0

def z854 : W := mkw 0x00ee00ee81ed0220 0x3bfe00ff81ff0270

def z855 : W := mkw 0x08ee00ee81ed03e0 0x39fe003f81ff0070

def z856 : W := mkw 0x10ea22fb7c000000 0x3efe7ffffe000000

def z857 : W := mkw 0x82c162b16540555a 0xf7c1fff07fc0ffff

def z858 : W := mkw 0x8704090483ffff7e 0xc100000001ffffff

def z859 : W := mkw 0x04f3dd000012f800 0x3dffff00007ffc00

def z860 : W := mkw 0x411cb359dca32cb9 0xd0ffe7f3b1c77df3

def z861 : W := mkw 0x05c56914c3fffe3c 0x37c1e03041fffe7c

def z862 : W := mkw 0x04369d0000b6a800 0x087e7f00007f1c00

def z863 : W := mkw 0x10fbd64b1c000000 0x3effffcffe000000

def z864 : W := mkw 0x082e00ee80ad03e0 0x3bbe00ff81bf03f0

def z865 : W := mkw 0x4504090483fffebd 0xc100000001ffffff

def z866 : W := mkw 0x82c160b06140555a 0xffc3e0fff1c0ffff

def z867 : W := mkw 0x92fbf6fb7d40555a 0x3fffffffffc0fc70

def z868 : W := mkw 0x04f7dd0001f6f800 0x097e7f0001fffc00

def z869 : W := mkw 0x08ef44ee81ed03e0 0x3bfe67ff81ff03f0

def z870 : W := mkw 0x08ee00ee80ad02a0 0x3bfe00ff807f0270

def z871 : W := mkw 0x10fbf6fb7c000000 0x2e7e7f3fce000000

def z872 : W := mkw 0x01002b15c61b8e3c 0x3fc3fffffe7f9e7c

def z873 : W := mkw 0x401c904c1aa82285 0xf7bd80cc7f80e38f

def z874 : W := mkw 0x48f298a29b55a165 0xc4439833fe47e07f

def z875 : W := mkw 0x01002b15c61b8e3c 0xef43ff3ffe7ffe7f

def z876 : W := mkw 0x01002b15c61b8e3c 0x09427f3f8e7f9e7c

def z877 : W := mkw 0x08e600a681ed0360 0x3bfe003f81ff0270

def z878 : W := mkw 0x10f3f6b364000000 0x3effff3fce000000

def z879 : W := mkw 0x04f7dd0001f6f800 0x3fffff3f81fffc00

def z880 : W := mkw 0x1110bf115e128c1c 0x04007f004e009c0c

def z881 : W := mkw 0x82d9f2f97d40555a 0xffffffffffc0ffff

def z882 : W := mkw 0x8aef40eea1ed53e2 0xffff80fff1ffe3ff

def z883 : W := mkw 0x001c904c18a80280 0xffbd98cc7fb8e38f

def z884 : W := mkw 0x401c98481ab0a085 0xf7bd98c07f80e38f

def z885 : W := mkw 0x41002b15c61b8ebd 0xef427f3fce7f9fff

def z886 : W := mkw 0x82c000a00140555a 0xf7c180f071c0ffff

def z887 : W := mkw 0x10fbf6fb7c000000 0x0c7fff3ffe000000

def z888 : W := mkw 0x0cee00ee81ed73e0 0x3bfe00ff81ff63f0

def z889 : W := mkw 0x0004000480a90220 0x3bfe003f81ff0270

def z890 : W := mkw 0x00e2090000128800 0x3dfe7f00007f9c00

def z891 : W := mkw 0x44f7dd001bf6f805 0x3dffff000ffffc00

def z892 : W := mkw 0x93e367b3e5435d7a 0x0042673380471c70

def z893 : W := mkw 0x4110bb115e12ac1d 0x04007f004e009c0c

def z894 : W := mkw 0x18ee00eeb9ed03e0 0x3bfe00ffb1ff03f0

def z895 : W := mkw 0x08ee00ee81ed03e0 0x3ffe00ffc1ff83fc

def z896 : W := mkw 0x00c160b060000418 0xf7c1e0f071c0ffff

def z897 : W := mkw 0x08e600a281e50160 0x087e0033807f0070

def z898 : W := mkw 0x10fbf65b5c000000 0x3effff3fce000000

def z899 : W := mkw 0x000c084c02b88284 0xffbd98cc7fb8e38f

def z900 : W := mkw 0x0026090000b68800 0x2d7e7f00007f9c00

def z901 : W := mkw 0x401c98481ab0a085 0xfebd98cc7f80e18f

def z902 : W := mkw 0x92fbf6fb7c00055a 0xffffffffff80e3ff

def z903 : W := mkw 0xc311fb117e12fc1f 0xc401ff007e00fc0f

def z904 : W := mkw 0x08ef40ee81ed03e0 0x3fffe0ff81ff03f0

def z905 : W := mkw 0x04f7dd0001f6f800 0x0c7fff00007ffc00

def z906 : W := mkw 0x04f7dd0001f6f800 0x11ffe70001fffc00

def z907 : W := mkw 0x401c984c1ab8a285 0xfffdf8cc7ff8ff8f

def z908 : W := mkw 0x10fbf6fb7c000000 0x1cbfffcffe000000

def z909 : W := mkw 0x4104090482bbaebd 0x01000000007f9e7c

def z910 : W := mkw 0x82c162b16540555a 0xf7c1e0ffffc0ffff

def z911 : W := mkw 0x490822ffde0907fd 0xc20000fffe0003ff

def z912 : W := mkw 0x1108225fde09063c 0x0200003fce00027c

def z913 : W := mkw 0x82c160b06140555a 0xd681e0f07180ffff

def z914 : W := mkw 0x87e367b1e5475d7a 0x0042673380471c70

def z915 : W := mkw 0x00d5d90001f2f800 0x3dffff0001fffc00

def z916 : W := mkw 0x820160b06140555a 0xc701e0f071c0ffff

def z917 : W := mkw 0x103a964b1c000000 0x3cbf9f0f8e000000

def z918 : W := mkw 0x82c160b06140555a 0xffc3e0f071ffffff

def z919 : W := mkw 0x10fbf6fb7c000000 0x1abf9ffffe000000

def z920 : W := mkw 0x401c994c1abaaa85 0xffbf9fcc7fbfe38f

def z921 : W := mkw 0x8aee00eea1ed03e2 0xfbfe00ffb1ff03f3

def z922 : W := mkw 0x82c140000140555a 0xf7c1e0c071c0ffff

def z923 : W := mkw 0x04f7dd0000b6f800 0x3cffff00003ffc00

def z924 : W := mkw 0x401c98481ab0a085 0xfdbd98c07fb8e18f

def z925 : W := mkw 0x481c984e9ab9a2a5 0xffbd98cfffb8e38f

def z926 : W := mkw 0x103ab6fb7c000000 0x3ebf9ffffe000000

def z927 : W := mkw 0x0010990000128800 0x3dffff00007f9c00

def z928 : W := mkw 0x44f7dd0019f6f801 0xfdffff0031fffc03

def z929 : W := mkw 0x09ee2bfb47f68ddc 0x14bc7fc04f809d8c

def z930 : W := mkw 0x0504090483fffa24 0x0100000001fffc00

def z931 : W := mkw 0x01002b15c61b8e3c 0x2e427f3fce7f1c70

def z932 : W := mkw 0x481c984c9abda2a5 0xffbd98cc7fbfe38f

def z933 : W := mkw 0x401c984c9ab9a2a5 0xffbf98cfffbfe38f

def z934 : W := mkw 0x08ee00ee81ed03e0 0x3ffe18ffcfff03f0

def z935 : W := mkw 0x411c994c9abbaaa5 0x083c180c0e3f0000

def z936 : W := mkw 0x10fbf6fb7d440000 0x3efffffffe470000

def z937 : W := mkw 0x10fbd6eb3c000000 0x083e1f0f8e000000

def z938 : W := mkw 0x92c166b16540555a 0xf7c1e7f071c0ffff

def z939 : W := mkw 0x0104090482bb8ebc 0x0100000001ff9ffc

def z940 : W := mkw 0x92fbf6fb7d40541a 0xffffffffffc0fc0f

def z941 : W := mkw 0x04f7dd0001f6f800 0x18ffff0001ff7c00

def z942 : W := mkw 0x00002b1144128c18 0x2f427f3fce7f9e7c

def z943 : W := mkw 0x82c160b06140555a 0xffc1f8fc7fc0ffff

def z944 : W := mkw 0x08ee00ee80ad03e0 0x3afe00ff803f03f0

def z945 : W := mkw 0x08ef40eea1ed03e0 0x3bff80ffb1ff03f0

def z946 : W := mkw 0x92fbf6fb7c00541a 0x3efffffffe001c00

def z947 : W := mkw 0x510822fffe0906bd 0xc20000fffe0003ff

def z948 : W := mkw 0x10fbf6fb7c000418 0x3efffffffe401c70

def z949 : W := mkw 0x0415dd0000b2f800 0x3dffff0001fffc00

def z950 : W := mkw 0x0414990001f6f800 0x3dffff0001fffc00

def z951 : W := mkw 0x082e004e80ad02a0 0x0a3e003f803f0270

def z952 : W := mkw 0x00fbd4ea18000000 0x3efffffffe000000

def z953 : W := mkw 0x4108225dde0906bd 0x0200003fce00027c

def z954 : W := mkw 0x92fbf6fb7d405142 0xffffffffffc0fd83

def z955 : W := mkw 0x04f7dd0001f6f800 0x2d7e7f00007f9c00

def z956 : W := mkw 0x08ee00ee99ed03e0 0x3bfe00ffffff03f0

def z957 : W := mkw 0x411c994c9abbaaa5 0xffbd98cc7fbfe38f

def z958 : W := mkw 0x8aef40eea1ed53e2 0xffffe0ffb1fffff3

def z959 : W := mkw 0x08ee00ee81ed03e0 0x2b7e003f807f0270

def z960 : W := mkw 0x92fbf6fb7d40055a 0xffffffffffc003ff

def z961 : W := mkw 0x01002b15c61b8e3c 0x3fc3ff3fcffffe7c

def z962 : W := mkw 0x0104090482bbae3c 0x0100000001fffe7c

def z963 : W := mkw 0x1511ff117e12fc1c 0x0401ff007e00fc0c

def z964 : W := mkw 0x04f7dd0001f6f800 0x1cbfff0001bffc00

def z965 : W := mkw 0x04e74d0001f6d800 0x3dfe7f0001ff9c00

def z966 : W := mkw 0x401498001ab0a005 0xffbd98c07fb8e38f

def z967 : W := mkw 0x820020b06140555a 0xf78180f071c0ffff

def z968 : W := mkw 0x08ee00ee81ed03e0 0x097e003f81ff03f0

def z969 : W := mkw 0x87c569b4e3ffff7e 0xf7c1e0f071ffffff

def z970 : W := mkw 0x10fbf6fb7d400140 0x3efffffffe400070

def z971 : W := mkw 0x08ee00ee81ed03e0 0x3fff80ff81ffe3f0

def z972 : W := mkw 0x0032960104000000 0x083e1f0f8e000000

def z973 : W := mkw 0x04369d0000b6a800 0x3dffff0001fffc00

def z974 : W := mkw 0x8aef40eea1ed53e2 0x3bfe00ff81ff03f0

def z975 : W := mkw 0x01002b11c4138c38 0x2f427f3fce7f9c70

def z976 : W := mkw 0x92fbf6fb7c00541a 0xfffffffffe40fe7f

def z977 : W := mkw 0x10fbf6fb7c000418 0xffffffffffc0ffff

def z978 : W := mkw 0x86f7dd0021f6f802 0xfdffff0031fffc03

def z979 : W := mkw 0x01000b05861b8a24 0x2f427f3f8e7f9e70

def z980 : W := mkw 0x080c00ee81ed03e0 0x3bbc00ff81ff03f0

def z981 : W := mkw 0x002a024b04000000 0x083e1f0f8e000000

def z982 : W := mkw 0x10fbf6fb7c000000 0x3ffffffffe7f0000

def z983 : W := mkw 0x04f7dda001f6f940 0x3dffffc001fffd80

def z984 : W := mkw 0x00cc00ec81e903e0 0x3bfe00ff81ff03f0

def z985 : W := mkw 0x082e00ee80ad03e0 0x083e003f803f0070

def z986 : W := mkw 0x08ee00ee81ed03e0 0x3fff80fff1ff03f0

def z987 : W := mkw 0x08ee00ee81ed03e0 0xfbfe00ff81ffe3ff

def z988 : W := mkw 0x04f7dd0001f6f800 0x3fffffc001ffff80

def z989 : W := mkw 0x00e6010001e60800 0x39fe670001ff1c00

def z990 : W := mkw 0x820160106140555a 0xf781e0c071c0ffff

def z991 : W := mkw 0x820160b06000555a 0xf781e0f07180ffff

def z992 : W := mkw 0x401898481a10a005 0xffbd98cc7f80e38f

def z993 : W := mkw 0x00f7dd0000b2a800 0x3dffff0001fffc00

def z994 : W := mkw 0x401c904818a02081 0xffbd98cc7f80e38f

def z995 : W := mkw 0x10fbf6fb7c000000 0xfefffffffe00038f

def z996 : W := mkw 0x04f7dd0001f6f800 0x39fe7f0001ff1c00

def z997 : W := mkw 0x92e364b26140555a 0xf7c1e0f071c0ffff

def z998 : W := mkw 0x4cffd4ea19e471c1 0xd0bd80c031806183

def z999 : W := mkw 0x401c984c1ab8a285 0xffffffcc7fb8e38f

def z1000 : W := mkw 0x4c04090483fffbe5 0xc100000001ffffff

def z1001 : W := mkw 0x83002b15e61b8e3e 0xef427f3ffe7f9e7f

def z1002 : W := mkw 0x00329d0000128800 0x2d7e7f00007f9c00

def z1003 : W := mkw 0x92fbf6fb7c005002 0xfefffffffe006003

def z1004 : W := mkw 0xc30822fdfe0907ff 0xc20000fffe0003ff

def z1005 : W := mkw 0x10fbf6fb7d405140 0x3fffffffffc0fff0

def z1006 : W := mkw 0x00fbf6fb44000000 0x3effffffce000000

def z1007 : W := mkw 0x00f6990001f6a800 0x3dffff0001fffc00

def z1008 : W := mkw 0x1019f6597c000000 0x3efffffffe000000

def z1009 : W := mkw 0x103a964b1c000000 0x2c7e7f0f8e000000

def z1010 : W := mkw 0x18fbf6fb7d440140 0x3efffffffe000000

def z1011 : W := mkw 0x82e360b06140555a 0xffffe0f071c0ffff

def z1012 : W := mkw 0x0504090482bfae3c 0x01000000007f9e7c

def z1013 : W := mkw 0x0110bb115e128c1c 0x0401ff007e009c0c

def z1014 : W := mkw 0x9611ff117c12fc1a 0xc401ff007e00fc0f

def z1015 : W := mkw 0x92fbf6fb7c00555a 0xfefffffffe00ffff

def z1016 : W := mkw 0x10fbf6fb7c000000 0x0a7e7ffffe000000

def z1017 : W := mkw 0x00e7490001f6d800 0x3dffff0001fffc00

def z1018 : W := mkw 0x86f7dd0001f6f942 0xfdffff0001fffd83

def z1019 : W := mkw 0x48ee00ee9bed03e5 0x3bfe00ff8fff03f0

def z1020 : W := mkw 0x00ea22fb45400558 0x3ffe7fffcfc09ffc

def z1021 : W := mkw 0x9a0822fffc0907fa 0xc20000fffe0003ff

def z1022 : W := mkw 0x103ab6fb7c000000 0x2e7e7ffffe000000

def z1023 : W := mkw 0x103a964b1c000000 0x2a7e1f3f8e000000

def z1024 : W := mkw 0x08ee00ee81ed03e0 0x11fe00f381ff03f0

def z1025 : W := mkw 0x92c162b36540555a 0xf7c1e0f3f1c0ffff

def z1026 : W := mkw 0x001c984818b0a000 0xffbd98cc7fb8e38f

def z1027 : W := mkw 0x10fbf6fb7d400558 0x3fffffffffc09ffc

def z1028 : W := mkw 0x01002b15c61b8e3c 0x2b427f3f8e7f1e70

def z1029 : W := mkw 0x103a96eb3c000000 0x083e1fcfbe000000

def z1030 : W := mkw 0x10fbd64b1c000000 0x18bf9f0f8e000000

def z1031 : W := mkw 0x082e004e80ad02a0 0x3bfe00ff81ff03f0

def z1032 : W := mkw 0x00e2221144000000 0x3efe7f3fce000000

def z1033 : W := mkw 0x930822fffe09077e 0xc20000fffe0003ff

def z1034 : W := mkw 0x9affd4ea39e451c2 0xd0bd80c031806183

def z1035 : W := mkw 0x0018b2595c000000 0x2e7e7f3fce000000

def z1036 : W := mkw 0x00c020b041400558 0xf7c1e0f071c0ffff

def z1037 : W := mkw 0x04e74d0001f6f800 0x39fe670001fffc00

def z1038 : W := mkw 0x04f7dd0001f6f800 0x3cffff00007f1c00

def z1039 : W := mkw 0x08e6000481ed03e0 0x3bfe003f81ff03f0

def z1040 : W := mkw 0x080c00ee80a903e0 0x3bfe00ff81ff03f0

def z1041 : W := mkw 0x401c984c1ab8a285 0xfffd98fc7ff8e3ff

def z1042 : W := mkw 0x09c429b4c3ff8ffc 0x37c060f041ff9ffc

def z1043 : W := mkw 0x10fbf6fb7c005000 0x3efffffffe00fc00

def z1044 : W := mkw 0x0018984c1a188204 0xffbd98cc7fb8e38f

def z1045 : W := mkw 0x820020b06000055a 0xf7c1e0f071c0ffff

def z1046 : W := mkw 0x00000904821b8a24 0x2f427f3fce7f9e7c

def z1047 : W := mkw 0x103a964b1c000000 0x3abe1fcf8e000000

def z1048 : W := mkw 0x04f7dda001f6f940 0x3dffff3001fffc70

def z1049 : W := mkw 0x00f3f6b164000000 0x3efffffffe000000

def z1050 : W := mkw 0x04f7dda201f6f800 0x3dffff3381fffc00

def z1051 : W := mkw 0x04f7dd0001f6f800 0x3fffff3001fffe70

def z1052 : W := mkw 0x103ab65b5c000000 0x3efffffffe000000

def z1053 : W := mkw 0x0111ff1146128c1c 0x0401ff004e009c0c

def z1054 : W := mkw 0x04f7dd0001f6f800 0xfdffffc031fffd83

def z1055 : W := mkw 0x01002b15c61b8e3c 0xef427ffffe7f9fff

def z1056 : W := mkw 0x0108225dde09063c 0x020000fffe00027c

def z1057 : W := mkw 0x48ee00ee99ed03e1 0xfbfe00ffb1ff03f3

def z1058 : W := mkw 0x10fbf6fb7d405000 0x3effffffff806000

def z1059 : W := mkw 0x04f7dd0001f6f800 0x3fffffc071fffc00

def z1060 : W := mkw 0x103a964b1c000000 0x18bf9fcfbe000000

def z1061 : W := mkw 0x10fbd64b1d405000 0x3dffff0f8fc0fc00

def z1062 : W := mkw 0x00eb62fb64000000 0x3efffffffe000000

def z1063 : W := mkw 0x10fbf6fb7c000418 0x3efffffffe009c0c

def z1064 : W := mkw 0x10fbf6fb7d405418 0x3fffffffffc0fe7c

def z1065 : W := mkw 0x44f7dd001bf6f805 0xffffffc07fffff8f

def z1066 : W := mkw 0x0008004c80090220 0x3bfe00ff807f0270

def z1067 : W := mkw 0x0010b21144000000 0x3effff3fce000000

def z1068 : W := mkw 0x103ab6fb7c000000 0x083e1f3f8e000000

def z1069 : W := mkw 0x10fbf6fb7c000000 0x3ffffffffe00820c

def z1070 : W := mkw 0x080c004c81ed03e0 0x3bfe00ff81ff03f0

def z1071 : W := mkw 0x0415dd0001f6f800 0x3dbdff0001fffc00

def z1072 : W := mkw 0x82e360b06144555a 0xf7c3e0f071c7ffff

def z1073 : W := mkw 0x0018b2595c000418 0xffffffffffc0ffff

def z1074 : W := mkw 0x04f7dd0001f6f800 0x15bdff0001fffc00

def z1075 : W := mkw 0x401c994c9abbaaa5 0xffffffffffffffff

def z1076 : W := mkw 0x00e2000480090220 0x3bfe003f807f0270

def z1077 : W := mkw 0x92fbf6fb7d40555a 0xfefffffffe401fff

def z1078 : W := mkw 0x401c984c1ab8a285 0xdabd98cc7fb8638f

def z1079 : W := mkw 0x04f3dd000156d800 0x3dffff00007f9c00

def z1080 : W := mkw 0x10fa96eb1d400140 0x3bfe1fff8fc003f0

def z1081 : W := mkw 0x002a004e80090220 0x2b7e003f807f0270

def z1082 : W := mkw 0x01002b15c61b8e3c 0x2d427f3f8e7f9c70

def z1083 : W := mkw 0x0026000480ad0220 0x2b7e003f807f0270

def z1084 : W := mkw 0x44f7dd0003f6f805 0xfdffff0001fffc0f

def z1085 : W := mkw 0x401c904c1aa82285 0xfbbd80cc7fb8638f

def z1086 : W := mkw 0x08ee00ee81ed03e0 0x3ffe60ff81ff9ff0

def z1087 : W := mkw 0xc3c569b4e3fbffff 0xf7c1e0f071ffffff

def z1088 : W := mkw 0x10fa96eb1c000000 0x3eff9ffffe000000

def z1089 : W := mkw 0x400c004c1aa80285 0xffbd80cc7fb8e38f

def z1090 : W := mkw 0x48ee00ee83ed03e5 0xfbfe00ff81ff03ff

def z1091 : W := mkw 0x08ef40ee81ed53e0 0x3bff80ff81ff63f0

def z1092 : W := mkw 0x04e6090001f6f800 0x3dfe7f0001fffc00

def z1093 : W := mkw 0x04f7dda021f6f800 0x3dffffc031fffc00

def z1094 : W := mkw 0x08ee00ee81ed03e0 0xfbff80ffb1ff63f3

def z1095 : W := mkw 0x0014980402b8a204 0xffbd98cc7fb8e38f

def z1096 : W := mkw 0x8ae360b26144555a 0xf7c1e0f071c0ffff

def z1097 : W := mkw 0x96e367b365465d5a 0x0042673380471c70

def z1098 : W := mkw 0x08ee00ee81ed03e0 0x1abe00ff81bf03f0

def z1099 : W := mkw 0xc304090483fbffff 0xc100000001ffffff

def z1100 : W := mkw 0x04369d0001f6f800 0x2d7e7f0001fffc00

def z1101 : W := mkw 0x10fbd6eb3c000000 0x3cffffcfbe000000

def z1102 : W := mkw 0x0032b61144000000 0x2e7e7f3fce000000

def z1103 : W := mkw 0x923bf65b7c00541a 0xcc3fff0ffe00fc0f

def z1104 : W := mkw 0x92fbf6fb7d40555a 0x3fffffffffc01ff0

def z1105 : W := mkw 0x92fbf6fb7d40555a 0xfeffffffff80fd8f

def z1106 : W := mkw 0x10fa964b1c000000 0x38fe1f0f8e000000

def z1107 : W := mkw 0x4104090482bbaaa5 0xc100000001bfe38f

def z1108 : W := mkw 0x10fab6fb5c000000 0x3efe7fffce000000

def z1109 : W := mkw 0x00c1601041405418 0xf7c1e0f071c0ffff

def z1110 : W := mkw 0x10fbd6eb3c000000 0x3aff9fffbe000000

def z1111 : W := mkw 0x10fbf6fb7d405000 0x3efffffffe401c00

def z1112 : W := mkw 0x401c994c1abaaa85 0xffbdffcc7fb8ff8f

def z1113 : W := mkw 0x10fab6fb7c000000 0x3afe1ffffe000000

def z1114 : W := mkw 0x44f7dd0001f6f881 0xfdffff0001fffd83

def z1115 : W := mkw 0x082e004e81ed03e0 0x2b7e003f81ff03f0

def z1116 : W := mkw 0x0908225fc60906bc 0x0200003fce00027c

def z1117 : W := mkw 0x00c140a001405140 0xf7c1e0f071c0ffff

def z1118 : W := mkw 0x92fbd6eb3d405142 0xd8bf9fcfbf806183

def z1119 : W := mkw 0x103a964b1c000000 0x2e3e1f0fce000000

def z1120 : W := mkw 0x5111ff117e12ac1d 0xc401ff007e00fc0f

def z1121 : W := mkw 0x86f7dda021f6f942 0xffffffc071ffff8f

def z1122 : W := mkw 0x92fbf6fb7d405142 0xffffffffff80e38f

def z1123 : W := mkw 0x1cffd4ea39e471c0 0x10bd80c031806180

def z1124 : W := mkw 0x01002b15c61b8e3c 0x0c427f3fce7f9c7c

def z1125 : W := mkw 0x0437dd0000b6f800 0x083e7f00003f1c00

def z1126 : W := mkw 0x01002b15c61b8e3c 0x3fc27fffcfff9ffc

def z1127 : W := mkw 0x000c004c80a902a0 0x2b7e003f807f0270

def z1128 : W := mkw 0x10fbd64b1c000000 0x087e7f0f8e000000

def z1129 : W := mkw 0x10fbf6fb7c000000 0x16bdfffffe000000

def z1130 : W := mkw 0x8711ff116612fc1e 0xc401ff007e00fc0f

def z1131 : W := mkw 0x92fbf6fb7c00055a 0xfffffffffe409fff

def z1132 : W := mkw 0x82c160b06140555a 0xd581e0c071c0ffff

def z1133 : W := mkw 0x08ea00ee814d0360 0x3bfe00ff807f0270

def z1134 : W := mkw 0x10fbf6fb7c000000 0x3cffff3f8e000000

def z1135 : W := mkw 0x103a964b1c000000 0x0c3f9f0ffe000000

def z1136 : W := mkw 0x01002b15c61b8e3c 0xef427f3fcfffffff

def z1137 : W := mkw 0x14f7dd0039f6f800 0x3dffff0031fffc00

def z1138 : W := mkw 0x493e9b4f9ebfaaa5 0x083e1f0f8e3f0000

def z1139 : W := mkw 0x8b0822ffe60907fe 0xc20000fffe0003ff

def z1140 : W := mkw 0x08ee00ee81ed03e0 0xfbfe00fff1ff03ff

def z1141 : W := mkw 0x0008225944000000 0x3efe7fffce000000

def z1142 : W := mkw 0x10fbf6fb7c000000 0x3fffffffff800380

def z1143 : W := mkw 0x04f7d50001e65800 0x3dffff0001ff1c00

def z1144 : W := mkw 0x9ae366b3e545557a 0x0042673380471c70

def z1145 : W := mkw 0x401c984c1ab8a285 0xd3bd80cc7fb8e38f

def z1146 : W := mkw 0x8b04090483ffdffe 0xc100000001ffffff

def z1147 : W := mkw 0x10fbf6fb7d400140 0xffffffffffc0e3ff

def z1148 : W := mkw 0x10fbf6fb7d400140 0x3effffffff800180

def z1149 : W := mkw 0x8aee00ee81ed53e2 0xfbfe00ff81ff63f3

def z1150 : W := mkw 0x00f7dd0001f68800 0x3dffff0001ff9c00

def z1151 : W := mkw 0x00002b15c41b8a20 0x2f427f3fce7f9e70

def z1152 : W := mkw 0x04f7dd0001f6f800 0xfdffff0001ffff8f

def z1153 : W := mkw 0x082e004e80ad02a0 0x087e003f807f0070

def z1154 : W := mkw 0x86f7dda021f6f942 0xfffffff031fffff3

def z1155 : W := mkw 0x103bf65b7c000000 0x2e7fff3ffe000000

def z1156 : W := mkw 0x14fbf6fb7d445000 0x3efffffffe000000

def z1157 : W := mkw 0x04f7dd0001f6f800 0x3fffff0041fffe0c

def z1158 : W := mkw 0x401c984c1ab8a285 0xffff98ffffb8e38f

def z1159 : W := mkw 0x103a96eb1c000000 0x0a3e1fff8e000000

def z1160 : W := mkw 0x401c904c1aa82285 0xfebd98cc7f80638f

def z1161 : W := mkw 0x0cf7dda201f6f940 0x3dffff0001fffc00

def z1162 : W := mkw 0x0d04090483fffffc 0x0100000001fffffc

def z1163 : W := mkw 0x1018b2fb7c000000 0x3efffffffe000000

def z1164 : W := mkw 0x92fbf6fb7d405142 0xffffffffffc063f3

def z1165 : W := mkw 0x103ab65b7c000000 0x083e1f0ffe000000

def z1166 : W := mkw 0x0110bb114612ac1c 0x0401ff004e00fc0c

def z1167 : W := mkw 0x08ee00ee81ed03e0 0x3afe00ff807f0070

def z1168 : W := mkw 0x00ee004c81ed02a0 0x3bfe00ff81ff03f0

def z1169 : W := mkw 0x0437dd0000b6f800 0x2d7fff00007ffc00

def z1170 : W := mkw 0x08ee00ee81ed03e0 0x18fe00ff81ff01f0

def z1171 : W := mkw 0x10fbf6fb7c000000 0xfefffffffe00e00f

def z1172 : W := mkw 0x082e00ee80ad03e0 0x2b7e00ff807f03f0

def z1173 : W := mkw 0x513e9f4f9ebbaaa5 0x083e1f0f8e3f0000

def z1174 : W := mkw 0x14f7dda221f6f800 0x3dffff0001fffc00

def z1175 : W := mkw 0x103bf65b7c000000 0x3ebfffcffe000000

def z1176 : W := mkw 0x08e600a681ed03e0 0x39fe003381ff03f0

def z1177 : W := mkw 0x401c984c1ab8a285 0xffff98cc7fffe38f

def z1178 : W := mkw 0x08ef40ee81ed53e0 0xffffe0fff1ffffff

def z1179 : W := mkw 0x0108225dc60906bc 0x020000ffce0003fc

def z1180 : W := mkw 0x0904090482bf8ebc 0x01000000007f9e7c

def z1181 : W := mkw 0x48ee00ee9bed03e5 0xffff80ffffffe3ff

def z1182 : W := mkw 0x103ab65b5c000000 0x087e7f3f8e000000

def z1183 : W := mkw 0x4511ff115e12fc1d 0xc401ff007e00fc0f

def z1184 : W := mkw 0x00ea02eb04000000 0x3afe1fff8e000000

def z1185 : W := mkw 0x10fbf6fb7c000140 0x3efffffffe0003f0

def z1186 : W := mkw 0x10fbf6fb7c000000 0x3fffffffff80e000

def z1187 : W := mkw 0x04e7450001e65800 0x087e6700007f1c00

def z1188 : W := mkw 0x92e366b36540555a 0xffc3ffffffc0ffff

def z1189 : W := mkw 0x08ee00ee83ed03e4 0x3bfe00ffcfff03fc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z9,z4,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z11]),(0,[z0,z1,z2,z5,z12,z6,z13]),(0,[z14,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z15,z4,z5,z16]),(0,[z17,z0,z1,z2,z4,z5,z6])],[(0,[z18,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z19]),(0,[z20,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z22,z23,z5,z6]),(0,[z0,z1,z2,z4,z24,z5,z11])],[(0,[z0,z1,z2,z4,z5,z6,z25]),(0,[z0,z1,z26,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z27,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z28]),(0,[z0,z29,z1,z2,z4,z5,z30]),(0,[z0,z1,z2,z31,z4,z5,z6]),(0,[z0,z1,z2,z22,z4,z5,z32]),(0,[z0,z1,z2,z4,z5,z33,z6])],[(0,[z0,z1,z2,z4,z34,z5,z6]),(0,[z35,z1,z36,z2,z4,z5,z6]),(0,[z37,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z38,z5,z6]),(1,[z0,z1,z4,z5,z39,z6]),(0,[z0,z1,z2,z40,z4,z5,z6]),(0,[z41,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z22,z21,z5,z6])],[(0,[z0,z42,z1,z2,z22,z5,z6]),(0,[z0,z1,z2,z4,z43,z5,z6]),(0,[z44,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z45,z6])],[(0,[z35,z0,z1,z46,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z5,z6,z48]),(0,[z49,z0,z2,z4,z5,z50,z6]),(0,[z51,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z52,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z53,z54,z6]),(0,[z0,z1,z2,z4,z5,z55,z54]),(0,[z0,z1,z2,z4,z5,z50,z6]),(0,[z0,z29,z42,z2,z4,z5,z6]),(0,[z0,z1,z4,z56,z5,z57,z6])]],
   [[(0,[z49,z0,z1,z58,z4,z5,z6]),(0,[z59,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z60,z2,z4,z5,z6]),(0,[z61,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z62,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z64])],[(0,[z65,z0,z1,z2,z4,z5,z6]),(0,[z66,z0,z1,z2,z4,z5,z6]),(0,[z49,z0,z1,z4,z5,z57,z6]),(0,[z0,z67,z68,z2,z4,z5,z6]),(0,[z0,z1,z69,z2,z4,z5,z6]),(0,[z0,z1,z2,z70,z4,z5,z6]),(0,[z71,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z22,z5,z6])],[(0,[z0,z1,z2,z4,z5,z72,z6]),(0,[z0,z73,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z74,z22,z5,z6])],[(0,[z0,z1,z2,z4,z75,z5,z6]),(0,[z0,z1,z2,z4,z5,z76,z6]),(0,[z0,z1,z2,z77,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z78,z6]),(0,[z0,z1,z2,z4,z5,z79,z6]),(0,[z80,z0,z1,z2,z4,z5,z6])],[(0,[z81,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z82,z6]),(0,[z0,z1,z2,z5,z83,z6,z11])],[(1,[z84,z0,z1,z85,z5,z6])],[(0,[z0,z1,z2,z4,z5,z86,z6]),(1,[z47,z1,z2,z4,z87,z6]),(0,[z0,z1,z2,z4,z88,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z89,z6]),(0,[z0,z1,z2,z58,z22,z5,z6]),(0,[z0,z1,z2,z4,z90,z5,z6])],[(1,[z91,z92,z2,z4,z5,z6]),(0,[z93,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z94]),(0,[z0,z1,z2,z4,z5,z95,z6]),(0,[z0,z1,z2,z4,z5,z6,z96]),(0,[z0,z1,z2,z4,z6,z96,z11])],[(1,[z97,z0,z1,z2,z6,z11]),(0,[z0,z1,z2,z5,z6,z6,z11]),(0,[z0,z1,z2,z4,z24,z5,z98])],[(0,[z0,z1,z2,z4,z87,z5,z6]),(0,[z99,z0,z1,z2,z4,z5,z6]),(0,[z100,z0,z1,z2,z4,z5,z6]),(0,[z0,z101,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z22,z22,z5,z6]),(1,[z102,z0,z1,z2,z4,z103])],[(0,[z0,z1,z2,z4,z56,z54,z6]),(0,[z0,z1,z104,z2,z4,z5,z6]),(0,[z105,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z106,z5,z6])],[(0,[z0,z1,z2,z4,z5,z107,z6]),(0,[z0,z1,z108,z2,z4,z5,z6])],[(0,[z0,z1,z2,z109,z4,z5,z6]),(0,[z110,z0,z1,z2,z4,z5,z6]),(1,[z111,z1,z2,z112,z5,z6]),(0,[z0,z1,z2,z4,z5,z55,z6]),(0,[z113,z0,z1,z2,z4,z5,z6]),(0,[z0,z114,z1,z2,z115,z5,z6]),(0,[z116,z0,z1,z2,z4,z5,z6]),(0,[z117,z0,z1,z4,z5,z57,z6]),(0,[z118,z0,z1,z2,z5,z6,z11]),(0,[z0,z1,z2,z4,z119,z5,z6])],[(0,[z0,z120,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z121]),(0,[z49,z0,z1,z68,z4,z5,z6]),(0,[z0,z1,z2,z122,z4,z5,z6]),(0,[z0,z123,z1,z2,z4,z5,z6])]],
   [[(0,[z124,z0,z2,z74,z4,z5,z6]),(0,[z0,z114,z1,z2,z5,z6,z11])],[(0,[z125,z0,z1,z2,z4,z5,z6]),(0,[z126,z0,z1,z92,z4,z5,z6]),(0,[z111,z0,z1,z127,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z128]),(0,[z0,z1,z2,z129,z4,z5,z6]),(0,[z130,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z22,z5,z16,z6]),(0,[z0,z1,z2,z131,z22,z5,z6]),(0,[z0,z1,z2,z4,z5,z132,z6])],[(0,[z124,z0,z2,z4,z5,z6,z30]),(1,[z133,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z134,z6]),(0,[z117,z0,z1,z2,z4,z56,z6])],[(0,[z135,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z136,z6])],[(0,[z0,z1,z2,z137,z4,z5,z6]),(0,[z51,z0,z1,z2,z4,z5,z30])],[(0,[z0,z1,z2,z4,z138,z5,z6])],[(0,[z139,z0,z1,z2,z4,z5,z6]),(0,[z140,z0,z1,z2,z141,z5,z6]),(0,[z142,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z68,z4,z5,z6,z19])],[(1,[z143,z0,z1,z2,z5,z6]),(0,[z117,z0,z1,z2,z4,z57,z6]),(0,[z0,z1,z2,z144,z4,z5,z6]),(0,[z0,z1,z145,z2,z5,z6,z11]),(0,[z0,z1,z2,z4,z146,z5,z6])]],
   [[(0,[z147,z0,z1,z2,z112,z5,z6]),(0,[z0,z1,z2,z4,z5,z148,z6]),(0,[z0,z29,z2,z4,z5,z50,z6])],[(0,[z0,z1,z2,z4,z5,z149,z6]),(0,[z111,z1,z2,z112,z4,z5,z6]),(0,[z150,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z151]),(1,[z0,z1,z152,z4,z5,z6]),(0,[z0,z1,z152,z4,z10,z5,z6]),(0,[z0,z1,z2,z24,z5,z6,z11])],[(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z1,z2,z4,z5,z6,z153]),(0,[z0,z2,z4,z5,z50,z6,z30])],[(0,[z154,z84,z0,z1,z4,z5,z6]),(0,[z155,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z156])],[(0,[z0,z1,z157,z2,z4,z5,z6]),(0,[z0,z1,z127,z2,z40,z5,z6])],[(0,[z154,z49,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z158,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z159,z6]),(0,[z0,z1,z2,z160,z4,z5,z6])],[(0,[z161,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z12,z6,z30]),(0,[z0,z1,z2,z4,z162,z5,z6]),(1,[z0,z1,z2,z163,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z164])],[(0,[z165,z0,z1,z2,z4,z5,z6]),(0,[z124,z0,z2,z4,z10,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z166]),(0,[z0,z1,z167,z2,z4,z5,z6]),(0,[z168,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z169,z6]),(0,[z170,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z171]),(1,[z0,z1,z172,z4,z5,z6])]],
   [[(0,[z0,z173,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z174,z4,z5,z6]),(0,[z175,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z176,z5,z6,z11])],[],[(0,[z0,z1,z40,z4,z85,z5,z6])],[(0,[z177,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z178])],[(0,[z143,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z179,z6]),(0,[z118,z0,z1,z2,z22,z5,z6]),(0,[z0,z180,z1,z2,z22,z5,z6])],[(0,[z0,z1,z181,z2,z4,z5,z6]),(0,[z182,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z54,z6]),(0,[z0,z183,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z184,z4,z5,z6]),(0,[z0,z1,z185,z2,z4,z5,z6])],[(0,[z0,z1,z186,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z187,z6]),(0,[z0,z188,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z189,z5,z6]),(0,[z0,z1,z2,z4,z190,z5,z6]),(0,[z0,z1,z2,z5,z6,z11,z191]),(0,[z0,z1,z2,z4,z5,z6,z192])],[(0,[z91,z0,z29,z2,z4,z5,z6]),(0,[z35,z0,z1,z4,z5,z6,z19]),(0,[z0,z29,z1,z2,z4,z5,z12]),(0,[z0,z193,z1,z2,z5,z6,z11]),(0,[z0,z1,z2,z5,z6,z11,z11])]],
   [[(0,[z0,z1,z2,z4,z5,z194,z6]),(0,[z0,z1,z195,z2,z4,z5,z6]),(0,[z0,z1,z15,z58,z4,z5,z6]),(1,[z118,z0,z1,z4,z5,z19]),(0,[z20,z0,z1,z2,z5,z83,z6]),(0,[z0,z1,z2,z4,z5,z196,z6]),(0,[z0,z1,z2,z22,z5,z6,z103])],[(0,[z0,z1,z197,z2,z4,z5,z6]),(0,[z111,z0,z1,z2,z112,z5,z6]),(0,[z0,z67,z1,z58,z4,z5,z6]),(0,[z198,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z199,z5,z6]),(0,[z0,z42,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z200,z6]),(0,[z0,z1,z2,z4,z5,z6,z13]),(1,[z0,z1,z2,z201,z5,z6]),(0,[z0,z1,z15,z4,z5,z57,z6]),(0,[z0,z1,z2,z4,z5,z6,z202])],[(0,[z203,z0,z1,z2,z4,z5,z6]),(1,[z204,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z205]),(0,[z0,z67,z1,z4,z5,z57,z6])],[(0,[z0,z1,z2,z206,z4,z5,z6]),(0,[z207,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z208,z6]),(0,[z209,z0,z1,z2,z4,z5,z6]),(0,[z0,z210,z1,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z83,z6]),(0,[z0,z1,z2,z22,z5,z83,z6]),(0,[z0,z1,z2,z4,z5,z6,z211])],[(0,[z35,z0,z1,z36,z4,z5,z6]),(0,[z212,z111,z0,z1,z2,z5,z6]),(0,[z140,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z213,z4,z5,z6]),(0,[z0,z1,z2,z4,z24,z5,z103])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z91,z0,z92,z2,z4,z5,z6]),(1,[z0,z1,z214,z2,z5,z6]),(0,[z0,z1,z2,z22,z5,z8,z6]),(0,[z0,z1,z145,z2,z22,z5,z6]),(1,[z0,z1,z2,z24,z5,z11]),(1,[z0,z1,z215,z4,z5,z6]),(0,[z102,z0,z1,z2,z4,z24,z6])],[(0,[z111,z0,z114,z1,z2,z5,z6]),(1,[z216,z1,z2,z4,z54,z6]),(0,[z0,z1,z2,z4,z5,z217,z6]),(0,[z0,z1,z2,z74,z4,z5,z6])],[(0,[z0,z1,z214,z92,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z156,z6]),(0,[z0,z1,z4,z218,z219,z5,z6]),(0,[z0,z1,z2,z219,z5,z6,z11]),(0,[z0,z1,z220,z2,z4,z5,z6]),(1,[z0,z2,z4,z5,z6,z128]),(0,[z212,z0,z114,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z221,z6]),(0,[z0,z1,z2,z4,z222,z5,z6]),(0,[z0,z1,z2,z4,z5,z223,z6]),(1,[z0,z123,z2,z4,z5,z6]),(0,[z118,z0,z1,z2,z4,z5,z19])]],
   [[(0,[z0,z1,z224,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z191]),(0,[z0,z1,z2,z4,z5,z6,z30]),(0,[z225,z0,z1,z2,z4,z5,z11])],[(0,[z226,z0,z1,z2,z4,z5,z6]),(0,[z227,z0,z1,z2,z5,z6,z11]),(0,[z0,z1,z127,z2,z85,z5,z6])],[(1,[z0,z1,z2,z4,z228,z6]),(1,[z0,z1,z2,z141,z5,z6]),(0,[z7,z1,z2,z4,z5,z8,z6]),(0,[z0,z1,z2,z4,z5,z6,z229]),(0,[z0,z1,z2,z4,z230,z5,z6]),(0,[z0,z231,z1,z2,z4,z5,z6])],[(0,[z232,z0,z1,z2,z4,z5,z6]),(1,[z0,z2,z4,z233,z5,z6]),(0,[z20,z111,z0,z1,z2,z5,z6]),(0,[z49,z0,z2,z58,z4,z5,z6]),(0,[z97,z0,z1,z2,z5,z6,z11])],[(0,[z0,z1,z2,z58,z4,z5,z6])],[(0,[z0,z1,z2,z4,z234,z5,z6]),(0,[z0,z1,z2,z4,z5,z32,z205]),(0,[z0,z1,z2,z4,z5,z235,z6])],[(0,[z91,z0,z2,z74,z4,z5,z6]),(0,[z0,z42,z68,z2,z4,z5,z6]),(0,[z97,z0,z1,z2,z4,z6,z11]),(0,[z0,z1,z236,z2,z4,z5,z6])],[(0,[z232,z0,z2,z46,z4,z5,z6]),(0,[z237,z0,z1,z2,z4,z5,z6]),(0,[z238,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z22,z5,z6,z19]),(0,[z0,z1,z2,z239,z22,z5,z6])]],
   [[(0,[z91,z0,z2,z4,z5,z6,z30]),(0,[z0,z1,z240,z2,z4,z5,z6]),(0,[z0,z241,z1,z2,z5,z6,z11]),(0,[z242,z0,z1,z2,z4,z5,z6]),(0,[z216,z1,z2,z4,z5,z54,z6]),(0,[z0,z67,z1,z68,z4,z5,z6]),(0,[z102,z0,z1,z215,z4,z5,z6])],[(0,[z0,z243,z1,z2,z4,z5,z6]),(0,[z0,z1,z244,z2,z4,z5,z6]),(0,[z216,z0,z1,z2,z4,z54,z6]),(0,[z0,z1,z2,z245,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z246]),(0,[z0,z1,z2,z23,z5,z83,z6]),(0,[z0,z1,z2,z4,z5,z247,z6])],[(0,[z0,z1,z2,z4,z248,z5,z6]),(0,[z0,z1,z2,z5,z6,z30,z11]),(0,[z0,z1,z2,z160,z5,z16,z6])],[(0,[z91,z49,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z249,z6]),(0,[z0,z250,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z251]),(1,[z0,z252,z2,z4,z5,z6]),(1,[z225,z0,z1,z2,z5,z11])],[(0,[z0,z1,z92,z2,z22,z5,z6]),(0,[z0,z1,z253,z2,z4,z5,z6])],[(0,[z254,z0,z1,z2,z4,z5,z6]),(0,[z147,z84,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z131,z4,z5,z6]),(0,[z255,z0,z1,z2,z4,z5,z6]),(0,[z256,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z10,z5,z6]),(0,[z0,z1,z2,z22,z5,z50,z6])],[(0,[z0,z1,z2,z4,z5,z257,z6]),(0,[z0,z1,z2,z4,z258,z5,z6]),(0,[z0,z1,z2,z259,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z260,z6]),(0,[z0,z1,z2,z4,z24,z98,z6])],[(0,[z147,z0,z1,z2,z4,z5,z261]),(0,[z0,z1,z2,z4,z219,z5,z6]),(0,[z0,z1,z2,z4,z218,z5,z6]),(0,[z262,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z50,z6,z11]),(0,[z84,z0,z1,z4,z85,z5,z6]),(0,[z0,z1,z2,z4,z263,z5,z6])]],
   [[(0,[z0,z1,z264,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z265,z5,z6]),(0,[z0,z1,z2,z4,z5,z205,z11]),(0,[z51,z0,z1,z2,z4,z5,z12]),(1,[z0,z1,z2,z4,z6,z96])],[(0,[z0,z1,z36,z2,z5,z6,z11]),(1,[z0,z114,z2,z74,z5,z6]),(0,[z118,z0,z1,z2,z163,z5,z6])],[(0,[z266,z0,z1,z2,z4,z5,z6]),(0,[z0,z267,z1,z2,z4,z5,z6]),(0,[z216,z0,z1,z2,z4,z87,z6]),(0,[z216,z0,z1,z2,z5,z6,z11]),(1,[z0,z1,z137,z4,z5,z6]),(0,[z102,z0,z1,z2,z268,z5,z6])],[(0,[z154,z35,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z269,z4,z5,z6]),(0,[z147,z0,z1,z127,z2,z5,z6]),(0,[z0,z1,z2,z5,z12,z6,z11])],[(0,[z0,z1,z2,z270,z4,z5,z6]),(0,[z124,z0,z29,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z271]),(0,[z0,z1,z272,z2,z4,z5,z6]),(1,[z147,z1,z2,z219,z5,z6]),(0,[z140,z1,z2,z4,z5,z6,z205]),(0,[z0,z1,z2,z4,z5,z273,z6])],[(0,[z274,z0,z1,z2,z4,z5,z6]),(0,[z91,z0,z2,z4,z10,z5,z6]),(0,[z0,z1,z2,z275,z4,z5,z6]),(0,[z276,z0,z1,z2,z4,z5,z6]),(0,[z84,z0,z1,z2,z85,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z277]),(0,[z0,z1,z2,z22,z88,z5,z6])],[(0,[z278,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z55]),(0,[z279,z0,z1,z2,z4,z5,z6]),(0,[z280,z0,z1,z2,z4,z5,z6]),(1,[z117,z0,z1,z4,z57,z6]),(0,[z0,z1,z2,z281,z4,z5,z6])],[(0,[z282,z0,z1,z2,z4,z5,z6]),(0,[z0,z67,z29,z2,z4,z5,z6]),(0,[z227,z0,z1,z2,z22,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z283]),(0,[z118,z0,z1,z2,z4,z5,z16])],[(0,[z204,z0,z1,z4,z219,z5,z6]),(0,[z0,z1,z2,z22,z87,z5,z6]),(0,[z7,z0,z1,z2,z4,z24,z5]),(0,[z0,z1,z2,z4,z5,z8,z11]),(0,[z0,z1,z4,z10,z5,z39,z6]),(0,[z0,z1,z2,z284,z4,z5,z6]),(1,[z0,z1,z2,z285,z5,z6]),(0,[z0,z1,z2,z4,z5,z286,z6])],[(0,[z124,z0,z92,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z87,z57,z6]),(0,[z0,z1,z2,z129,z5,z8,z6]),(0,[z287,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z57,z6,z11])],[(0,[z288,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z289,z5,z6]),(0,[z0,z1,z2,z5,z6,z290,z11])],[(0,[z291,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z292,z5,z6]),(0,[z0,z1,z2,z4,z5,z293,z6]),(0,[z0,z1,z2,z22,z119,z5,z6]),(0,[z0,z294,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z295,z6]),(0,[z1,z36,z2,z46,z4,z5,z6]),(0,[z0,z29,z2,z58,z4,z5,z6]),(0,[z296,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z4,z98,z6]),(1,[z0,z1,z2,z5,z6,z297])],[(0,[z0,z241,z1,z2,z22,z5,z6]),(0,[z0,z1,z2,z4,z5,z298,z6]),(0,[z0,z2,z4,z5,z8,z6,z128]),(0,[z0,z1,z4,z5,z8,z6,z246]),(0,[z0,z1,z2,z22,z4,z5,z11])],[(0,[z241,z1,z92,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z261]),(0,[z0,z1,z299,z2,z4,z5,z6]),(0,[z0,z68,z2,z4,z5,z50,z6]),(0,[z0,z1,z2,z4,z85,z5,z6]),(0,[z102,z0,z1,z2,z4,z5,z11]),(0,[z0,z1,z2,z22,z5,z132,z6])]],
   [[(0,[z0,z1,z2,z300,z4,z5,z6]),(0,[z118,z0,z1,z2,z4,z5,z6]),(0,[z0,z301,z1,z2,z4,z5,z6]),(0,[z0,z180,z1,z2,z4,z5,z6])],[(0,[z0,z1,z58,z4,z5,z6,z19]),(0,[z51,z0,z29,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z302])],[(0,[z0,z303,z1,z2,z4,z5,z6]),(0,[z0,z1,z167,z4,z5,z8,z6]),(0,[z304,z0,z1,z2,z4,z5,z6]),(0,[z0,z114,z1,z2,z4,z5,z6]),(0,[z305,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z201,z4,z5,z6]),(0,[z0,z1,z2,z4,z306,z5,z6]),(0,[z0,z1,z2,z4,z5,z98,z6])],[(0,[z0,z1,z2,z4,z307,z5,z6]),(0,[z0,z1,z2,z4,z5,z308,z6]),(0,[z0,z309,z1,z2,z4,z5,z6]),(0,[z0,z1,z145,z4,z5,z6,z19]),(1,[z0,z1,z2,z5,z6,z171]),(0,[z102,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z310])],[(0,[z0,z1,z2,z311,z4,z5,z6]),(0,[z0,z1,z2,z4,z312,z5,z6]),(0,[z0,z1,z2,z4,z313,z5,z6]),(0,[z0,z1,z2,z4,z314,z5,z6])],[(0,[z0,z1,z315,z2,z4,z5,z6]),(0,[z0,z1,z2,z316,z4,z5,z6]),(0,[z47,z1,z2,z4,z87,z5,z6]),(0,[z0,z1,z2,z4,z317,z5,z6]),(0,[z0,z1,z2,z4,z318,z5,z6]),(0,[z0,z1,z2,z319,z4,z5,z6]),(0,[z320,z0,z1,z2,z5,z6,z11])],[(0,[z154,z0,z1,z2,z5,z6,z11]),(0,[z7,z47,z1,z2,z4,z5,z6]),(0,[z51,z0,z1,z137,z4,z5,z6]),(0,[z0,z1,z127,z2,z5,z6,z11]),(0,[z321,z0,z1,z2,z4,z5,z6]),(0,[z102,z0,z1,z2,z146,z5,z6]),(0,[z322,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z87,z50,z6]),(0,[z117,z0,z1,z145,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z323,z6])]],
   [[(1,[z124,z241,z2,z4,z5,z6]),(0,[z1,z2,z4,z87,z5,z54,z6]),(0,[z0,z1,z2,z4,z56,z87,z6]),(0,[z0,z67,z2,z4,z5,z6,z30]),(0,[z324,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z22,z5,z6,z6])],[(0,[z0,z1,z2,z4,z5,z325,z6]),(0,[z0,z1,z145,z2,z4,z5,z6])],[(0,[z0,z1,z2,z326,z46,z5,z6]),(0,[z0,z1,z2,z4,z5,z327,z6]),(0,[z328,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z176,z5,z6])],[(0,[z329,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z330,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z331]),(1,[z0,z1,z2,z22,z5,z11])],[(1,[z232,z0,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z23,z6]),(0,[z0,z1,z2,z4,z5,z6,z332]),(1,[z97,z0,z1,z2,z4,z6])],[(0,[z0,z1,z333,z2,z4,z5,z6]),(0,[z334,z0,z1,z2,z5,z54,z6]),(0,[z0,z1,z2,z4,z5,z6,z335]),(0,[z0,z1,z2,z4,z336,z5,z6]),(1,[z0,z1,z2,z5,z6,z13]),(1,[z0,z1,z2,z21,z23,z6])],[(0,[z0,z1,z2,z4,z5,z6,z337]),(0,[z338,z0,z1,z2,z4,z5,z6]),(0,[z118,z0,z252,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z339,z5,z6]),(0,[z0,z1,z340,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z341])],[(1,[z342,z0,z2,z4,z5,z6]),(0,[z102,z0,z236,z2,z4,z5,z6])]],
   [[(0,[z147,z0,z114,z1,z2,z5,z6]),(0,[z0,z2,z4,z233,z219,z5,z6]),(0,[z102,z0,z1,z2,z4,z5,z98])],[(0,[z0,z1,z2,z343,z4,z5,z6]),(0,[z143,z0,z1,z92,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z344])],[(0,[z345,z0,z1,z2,z4,z5,z6]),(0,[z102,z7,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z346,z4,z5,z6]),(0,[z51,z0,z2,z4,z5,z6,z30]),(0,[z0,z347,z1,z2,z4,z5,z6])],[(0,[z147,z0,z1,z2,z219,z5,z6]),(0,[z0,z1,z2,z22,z5,z54,z6]),(0,[z140,z0,z1,z2,z4,z24,z5]),(0,[z348,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z239,z4,z5,z6]),(0,[z0,z1,z2,z4,z24,z5,z32])],[(0,[z0,z1,z2,z349,z4,z5,z6]),(0,[z0,z114,z1,z2,z74,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z350]),(0,[z0,z1,z2,z4,z5,z351,z6])],[(0,[z0,z1,z2,z4,z5,z352,z6]),(0,[z0,z1,z2,z4,z5,z6,z353]),(0,[z0,z1,z2,z354,z4,z5,z6]),(0,[z355,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z356]),(0,[z357,z0,z1,z2,z22,z5,z6]),(0,[z0,z358,z1,z2,z4,z5,z6])],[(0,[z111,z0,z1,z2,z5,z6,z11]),(0,[z359,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z360]),(0,[z118,z0,z1,z15,z4,z5,z6])],[(0,[z361,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z362,z5,z6]),(0,[z0,z1,z363,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z364])]],
   [[(0,[z0,z1,z92,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z365,z5,z6]),(0,[z7,z1,z2,z4,z5,z54,z6]),(1,[z0,z2,z4,z5,z86,z6]),(0,[z0,z1,z2,z4,z5,z366,z6]),(0,[z0,z1,z2,z22,z5,z6,z205]),(1,[z227,z0,z2,z4,z50,z6]),(0,[z0,z1,z2,z4,z5,z32,z6])],[(0,[z0,z1,z2,z4,z5,z32,z8]),(0,[z0,z1,z2,z4,z5,z6,z367]),(0,[z0,z1,z2,z4,z5,z368,z6]),(0,[z369,z0,z1,z2,z4,z5,z6]),(0,[z0,z193,z1,z2,z4,z5,z6]),(0,[z0,z114,z1,z2,z22,z5,z6]),(0,[z0,z1,z2,z4,z5,z370,z6]),(0,[z0,z1,z2,z4,z5,z371,z6]),(0,[z0,z1,z2,z21,z4,z5,z260])],[(0,[z133,z0,z1,z2,z46,z5,z6]),(0,[z0,z1,z2,z4,z372,z5,z6]),(0,[z84,z0,z1,z2,z5,z6,z11])],[(0,[z373,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z374,z5,z6]),(0,[z0,z1,z2,z5,z54,z6,z11]),(0,[z375,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z376,z6])],[(0,[z377,z0,z1,z2,z4,z5,z6]),(0,[z124,z0,z1,z2,z5,z6,z11]),(0,[z378,z0,z1,z2,z4,z5,z6]),(0,[z0,z379,z1,z2,z4,z5,z6]),(0,[z0,z1,z127,z2,z22,z5,z6]),(0,[z0,z1,z2,z21,z5,z6,z11])],[(1,[z0,z1,z4,z218,z5,z6]),(0,[z0,z1,z2,z380,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z381]),(0,[z382,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z383,z5,z6])],[(0,[z91,z0,z1,z2,z4,z295,z6]),(0,[z124,z0,z241,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z384]),(0,[z0,z1,z2,z22,z5,z6,z30]),(1,[z0,z1,z2,z4,z5,z385]),(0,[z0,z1,z2,z4,z386,z5,z6]),(0,[z0,z1,z2,z4,z387,z5,z6])],[(0,[z0,z1,z2,z388,z4,z5,z6]),(0,[z0,z1,z2,z389,z4,z5,z6]),(0,[z0,z1,z2,z390,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z391])]],
   [[(0,[z392,z0,z1,z2,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z54,z6]),(0,[z0,z1,z2,z4,z5,z393,z6]),(0,[z0,z1,z2,z4,z5,z6,z394])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z395,z0,z1,z2,z4,z5,z6]),(0,[z396,z0,z1,z2,z4,z5,z6]),(0,[z0,z397,z1,z2,z4,z5,z6]),(0,[z398,z0,z1,z2,z4,z5,z6]),(0,[z0,z399,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z281,z5,z6])],[(0,[z291,z0,z1,z4,z5,z54,z6]),(0,[z7,z0,z1,z2,z5,z6,z11]),(0,[z0,z1,z2,z4,z115,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z400]),(0,[z0,z1,z2,z4,z401,z5,z6])],[(0,[z0,z67,z1,z145,z4,z5,z6]),(0,[z227,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z22,z5,z57,z6])],[(0,[z111,z0,z1,z2,z219,z5,z6]),(0,[z47,z1,z2,z4,z5,z6,z205]),(1,[z0,z1,z2,z5,z205,z11]),(0,[z0,z1,z2,z4,z5,z6,z402]),(0,[z0,z1,z2,z4,z403,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z404]),(0,[z405,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z11])],[(0,[z0,z1,z2,z22,z112,z5,z6]),(0,[z0,z42,z1,z2,z4,z50,z6]),(0,[z97,z0,z1,z2,z4,z5,z6])],[(0,[z154,z0,z1,z4,z56,z5,z6]),(0,[z0,z1,z2,z4,z406,z5,z6]),(0,[z0,z1,z2,z4,z407,z5,z6]),(0,[z0,z1,z2,z4,z408,z5,z6]),(0,[z0,z1,z2,z409,z4,z5,z6]),(1,[z51,z0,z2,z4,z5,z30]),(0,[z0,z1,z2,z4,z5,z410,z6]),(0,[z0,z1,z2,z4,z5,z411,z6]),(0,[z412,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z413]),(0,[z414,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z415,z6]),(0,[z342,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z69,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z416]),(0,[z0,z1,z2,z5,z16,z6,z11])],[(0,[z417,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z418,z6]),(0,[z47,z0,z1,z2,z4,z87,z6]),(0,[z0,z1,z2,z419,z4,z5,z6]),(0,[z420,z0,z1,z2,z4,z5,z6])],[(0,[z0,z241,z1,z2,z4,z5,z6]),(0,[z0,z421,z1,z2,z4,z5,z6]),(0,[z0,z422,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z423,z5,z6]),(0,[z0,z1,z2,z424,z4,z5,z6]),(0,[z425,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z12,z6]),(1,[z0,z1,z2,z268,z5,z6])],[(0,[z0,z426,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z22,z10,z5,z6])],[(0,[z427,z0,z1,z2,z22,z5,z6]),(1,[z428,z1,z2,z4,z5,z6])],[(1,[z126,z0,z1,z4,z5,z6]),(0,[z147,z111,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z5,z8,z11]),(0,[z0,z1,z429,z2,z4,z5,z6]),(0,[z430,z0,z1,z2,z5,z6,z11])],[],[(0,[z227,z124,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z261]),(0,[z0,z1,z2,z4,z431,z5,z6]),(0,[z0,z1,z2,z4,z5,z432,z6]),(1,[z0,z29,z2,z4,z5,z12]),(0,[z0,z1,z433,z2,z4,z5,z6]),(0,[z434,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z435,z5,z6]),(1,[z0,z42,z2,z4,z10,z6]),(0,[z84,z0,z1,z2,z22,z5,z6]),(1,[z0,z1,z2,z6,z96,z11])],[(0,[z436,z0,z1,z2,z4,z5,z6])],[(0,[z91,z124,z1,z2,z4,z5,z6]),(0,[z437,z0,z1,z2,z4,z5,z6]),(0,[z154,z0,z1,z2,z4,z438,z6]),(0,[z439,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z6,z332,z11]),(1,[z102,z0,z1,z2,z5,z11]),(0,[z102,z0,z1,z2,z4,z5,z103])],[(0,[z0,z1,z36,z2,z4,z5,z6]),(0,[z204,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z440,z5,z6]),(0,[z441,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z57,z6,z19])],[(0,[z216,z0,z1,z2,z4,z5,z6]),(0,[z0,z68,z2,z58,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z442,z6]),(0,[z0,z1,z443,z2,z5,z6,z11])],[(0,[z0,z1,z444,z2,z4,z5,z6]),(0,[z445,z0,z1,z2,z4,z5,z6]),(0,[z147,z20,z0,z1,z2,z5,z6]),(0,[z446,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z447,z6])],[(0,[z448,z0,z1,z2,z4,z5,z6]),(1,[z0,z449,z2,z4,z5,z6]),(0,[z450,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z48]),(0,[z0,z1,z2,z4,z451,z5,z6]),(0,[z102,z428,z1,z2,z4,z5,z6])]],
   [[(0,[z91,z1,z92,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z452,z5,z6]),(0,[z0,z1,z453,z2,z4,z5,z6])],[(0,[z0,z1,z454,z2,z4,z5,z6]),(0,[z0,z1,z2,z455,z4,z5,z6]),(0,[z0,z456,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z457]),(0,[z49,z0,z1,z2,z5,z6,z11]),(0,[z458,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z317,z5,z6]),(0,[z0,z1,z2,z4,z5,z459,z6]),(0,[z0,z1,z2,z460,z4,z5,z6])],[(0,[z461,z0,z1,z2,z4,z5,z6]),(0,[z0,z462,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z56,z5,z6,z11]),(0,[z0,z1,z463,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z6,z310,z11]),(0,[z0,z1,z215,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z464,z6]),(0,[z0,z465,z1,z2,z4,z5,z6]),(0,[z0,z466,z1,z2,z4,z5,z6]),(0,[z0,z1,z467,z2,z4,z5,z6]),(0,[z0,z1,z468,z2,z4,z5,z6])],[(0,[z140,z0,z1,z2,z5,z6,z11]),(1,[z7,z1,z2,z4,z5,z8]),(0,[z51,z0,z1,z69,z4,z5,z6])],[(0,[z0,z2,z4,z5,z86,z54,z6]),(0,[z49,z0,z1,z145,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z469,z6]),(0,[z227,z0,z42,z2,z4,z5,z6]),(0,[z0,z42,z2,z4,z5,z6,z30]),(0,[z470,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z85,z5,z6,z11]),(0,[z0,z1,z2,z285,z4,z5,z6]),(0,[z118,z0,z1,z4,z5,z6,z19])],[(0,[z0,z1,z2,z46,z5,z6,z11]),(0,[z140,z0,z1,z2,z407,z5,z6]),(1,[z0,z67,z68,z4,z5,z6]),(0,[z0,z1,z2,z471,z4,z5,z6]),(0,[z0,z472,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z146,z5,z6])],[(0,[z0,z1,z2,z473,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z474,z6]),(0,[z0,z1,z475,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z476])]],
   [[(0,[z0,z1,z2,z4,z5,z477,z6]),(0,[z0,z1,z2,z478,z4,z5,z6]),(0,[z84,z35,z0,z1,z4,z5,z6]),(0,[z0,z1,z479,z2,z4,z5,z6]),(0,[z480,z0,z1,z2,z4,z5,z6]),(0,[z212,z0,z2,z4,z115,z5,z6]),(0,[z0,z1,z2,z4,z5,z16,z6])],[(0,[z0,z1,z2,z4,z5,z481,z6]),(0,[z161,z0,z2,z4,z219,z5,z6]),(0,[z0,z1,z2,z4,z482,z5,z6]),(0,[z0,z449,z2,z4,z56,z5,z6]),(0,[z357,z0,z1,z2,z4,z5,z6])],[(0,[z91,z0,z1,z2,z5,z6,z11]),(0,[z0,z1,z2,z5,z8,z6,z11]),(0,[z483,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z484]),(0,[z0,z2,z74,z4,z115,z5,z6]),(0,[z0,z29,z2,z4,z5,z12,z6]),(0,[z485,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z145,z2,z4,z56,z6])],[(0,[z91,z0,z241,z2,z4,z5,z6]),(0,[z0,z1,z2,z486,z4,z5,z6]),(0,[z0,z1,z487,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z488,z5,z6]),(0,[z225,z0,z1,z2,z5,z6,z11]),(0,[z489,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z54,z57,z6]),(0,[z118,z0,z123,z2,z4,z5,z6]),(0,[z490,z0,z1,z2,z4,z5,z6]),(0,[z491,z0,z1,z2,z22,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z492])],[(1,[z0,z1,z2,z326,z5,z6]),(0,[z0,z1,z2,z4,z493,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z494]),(0,[z495,z0,z1,z2,z4,z5,z6]),(0,[z117,z0,z1,z2,z5,z6,z11])],[(0,[z0,z1,z68,z2,z5,z6,z11]),(0,[z496,z0,z1,z2,z4,z5,z6]),(0,[z320,z0,z1,z2,z4,z5,z6]),(1,[z0,z236,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z497,z6])]],
   [[(0,[z154,z0,z1,z2,z4,z5,z6]),(0,[z147,z0,z1,z2,z5,z6,z11]),(0,[z498,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z152,z2,z4,z5,z6]),(0,[z0,z1,z127,z2,z4,z5,z6]),(0,[z0,z1,z145,z2,z4,z57,z6])],[(0,[z499,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z141,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z500,z6])],[(0,[z91,z212,z0,z2,z4,z5,z6]),(0,[z0,z1,z36,z2,z22,z5,z6]),(0,[z0,z1,z2,z4,z5,z501,z6]),(0,[z0,z42,z2,z4,z10,z5,z6]),(0,[z502,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z56,z5,z6]),(0,[z225,z0,z1,z2,z4,z5,z32])],[(0,[z0,z1,z2,z503,z4,z5,z6]),(0,[z216,z0,z1,z2,z22,z5,z6]),(0,[z140,z0,z1,z2,z4,z5,z205]),(0,[z0,z1,z2,z504,z4,z5,z6]),(0,[z0,z1,z2,z4,z505,z5,z6]),(0,[z0,z1,z2,z506,z4,z5,z6]),(0,[z0,z1,z2,z5,z98,z6,z297])],[(0,[z0,z1,z2,z4,z5,z6,z507])],[(0,[z0,z1,z2,z4,z5,z438,z6]),(0,[z0,z1,z508,z2,z4,z5,z6]),(0,[z51,z0,z1,z2,z317,z5,z6]),(0,[z0,z1,z2,z5,z6,z11,z103])],[(0,[z0,z1,z2,z4,z5,z6,z385]),(0,[z0,z1,z2,z509,z22,z5,z6])],[(0,[z0,z1,z444,z92,z4,z5,z6]),(0,[z510,z0,z1,z2,z4,z5,z6]),(0,[z49,z0,z1,z2,z22,z5,z6]),(0,[z0,z1,z2,z4,z24,z5,z6])]],
   [[(0,[z511,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z5,z6,z11]),(0,[z0,z1,z2,z5,z6,z96,z11])],[(0,[z512,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z54,z50,z6]),(0,[z140,z0,z1,z2,z22,z5,z6]),(0,[z0,z2,z4,z10,z5,z50,z6]),(0,[z0,z513,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z160,z5,z6])],[(0,[z0,z1,z2,z514,z4,z5,z6]),(0,[z0,z1,z2,z4,z515,z5,z6]),(0,[z0,z29,z1,z2,z5,z6,z11])],[(0,[z0,z1,z2,z46,z22,z5,z6]),(0,[z0,z1,z2,z516,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z517,z6]),(0,[z0,z1,z2,z4,z5,z518,z6]),(0,[z519,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z5,z8,z6,z48]),(0,[z0,z1,z2,z4,z520,z5,z6]),(0,[z0,z1,z521,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z522,z6]),(0,[z0,z42,z1,z2,z4,z10,z6]),(0,[z523,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z524])],[(0,[z525,z0,z1,z2,z4,z5,z6]),(0,[z212,z0,z1,z2,z115,z5,z6]),(0,[z227,z0,z2,z4,z5,z50,z6]),(0,[z526,z0,z1,z2,z22,z5,z6]),(0,[z0,z1,z475,z2,z22,z5,z6]),(0,[z0,z1,z2,z22,z5,z32,z6])],[(0,[z0,z1,z2,z4,z5,z6,z527]),(0,[z0,z1,z2,z4,z528,z5,z6]),(0,[z0,z1,z2,z4,z163,z5,z6]),(0,[z0,z1,z2,z268,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z103])]],
   [[(0,[z91,z0,z1,z2,z22,z5,z6]),(0,[z35,z0,z1,z2,z5,z6,z11]),(0,[z111,z0,z1,z2,z4,z5,z6]),(0,[z147,z1,z2,z4,z219,z5,z6]),(0,[z212,z0,z1,z2,z5,z6,z11]),(0,[z529,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z530,z5,z6]),(1,[z0,z1,z2,z5,z6,z11]),(0,[z427,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z531,z4,z5,z6]),(0,[z532,z0,z1,z2,z5,z6,z11]),(0,[z0,z533,z1,z2,z4,z5,z6])],[(1,[z0,z1,z4,z5,z6,z246]),(0,[z225,z0,z1,z2,z22,z5,z6])],[(0,[z0,z1,z534,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z535,z6]),(0,[z536,z0,z1,z2,z4,z5,z6]),(0,[z537,z0,z1,z2,z4,z5,z6])],[(0,[z154,z0,z1,z46,z4,z5,z6]),(0,[z0,z1,z68,z15,z4,z5,z6]),(0,[z84,z0,z1,z2,z4,z5,z6]),(0,[z117,z0,z1,z2,z22,z5,z6]),(0,[z0,z1,z2,z22,z386,z5,z6]),(0,[z0,z1,z2,z22,z387,z5,z6])],[(0,[z538,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z539,z6]),(0,[z0,z1,z540,z2,z4,z5,z6]),(0,[z111,z0,z1,z2,z23,z5,z6]),(0,[z0,z1,z68,z2,z22,z5,z6]),(0,[z0,z1,z2,z4,z5,z541,z6]),(0,[z0,z1,z2,z4,z5,z542,z6])],[(0,[z124,z0,z1,z2,z4,z5,z6]),(0,[z154,z0,z1,z15,z4,z5,z6]),(0,[z147,z0,z1,z2,z22,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z543]),(0,[z0,z465,z2,z4,z5,z8,z6]),(0,[z0,z1,z544,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z4,z5,z6]),(0,[z0,z1,z2,z5,z6,z11,z545])],[(0,[z154,z0,z1,z2,z22,z5,z6]),(0,[z49,z35,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z10,z54,z6]),(1,[z212,z0,z2,z115,z5,z6]),(0,[z84,z0,z1,z127,z4,z5,z6]),(0,[z118,z0,z1,z2,z285,z5,z6]),(0,[z20,z0,z1,z2,z5,z6,z11])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z546]),(0,[z0,z1,z2,z22,z115,z5,z6]),(0,[z0,z1,z2,z4,z547,z5,z6]),(0,[z548,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z549]),(1,[z334,z0,z1,z2,z5,z6]),(0,[z0,z1,z4,z5,z16,z6,z19]),(0,[z0,z550,z1,z2,z4,z5,z6]),(0,[z0,z1,z15,z2,z5,z6,z11])],[(0,[z0,z1,z2,z4,z5,z551,z6]),(0,[z0,z67,z1,z2,z5,z6,z11]),(0,[z0,z552,z1,z2,z4,z5,z6]),(0,[z553,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z22,z5,z6,z11])],[(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z554,z0,z1,z2,z4,z5,z54]),(0,[z555,z0,z1,z2,z4,z5,z6]),(0,[z556,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z23,z5,z6]),(0,[z102,z0,z1,z2,z5,z6,z11])],[(0,[z0,z114,z2,z74,z4,z5,z6]),(1,[z0,z1,z127,z40,z5,z6]),(0,[z557,z0,z1,z2,z4,z5,z6]),(0,[z558,z0,z1,z2,z4,z5,z6])],[(0,[z559,z0,z1,z2,z4,z5,z6]),(0,[z154,z117,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z326,z4,z5,z6]),(1,[z291,z0,z1,z4,z5,z6]),(0,[z0,z1,z560,z2,z4,z5,z6]),(0,[z0,z1,z15,z145,z4,z5,z6])],[(0,[z0,z1,z2,z4,z4,z5,z6])],[(0,[z561,z0,z1,z2,z4,z5,z6]),(0,[z124,z241,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z562]),(0,[z0,z1,z2,z4,z5,z563,z6]),(1,[z0,z2,z4,z5,z500,z6])]],
   [[(0,[z91,z0,z1,z2,z4,z564,z6]),(0,[z565,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z53,z6]),(0,[z0,z1,z2,z4,z10,z87,z6]),(0,[z0,z1,z2,z22,z5,z12,z6]),(0,[z0,z1,z2,z4,z5,z6,z545]),(0,[z0,z1,z2,z4,z5,z6,z566])],[(1,[z0,z1,z2,z129,z5,z6]),(0,[z212,z0,z1,z2,z74,z5,z6]),(0,[z0,z29,z1,z2,z22,z5,z6]),(0,[z102,z0,z1,z2,z4,z5,z32])],[(0,[z0,z1,z2,z40,z5,z6,z11]),(0,[z0,z1,z2,z4,z567,z5,z6])],[(1,[z0,z1,z444,z4,z5,z6]),(0,[z124,z0,z68,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z568,z5,z6]),(0,[z569,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z23,z5,z6]),(0,[z102,z0,z294,z2,z4,z5,z6])],[(0,[z0,z1,z2,z570,z4,z5,z6]),(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z117,z35,z0,z1,z4,z5,z6]),(0,[z47,z0,z1,z2,z5,z6,z11]),(0,[z0,z1,z2,z571,z4,z5,z6]),(0,[z572,z0,z1,z2,z4,z5,z6]),(0,[z573,z0,z1,z2,z4,z5,z6]),(0,[z51,z0,z1,z2,z5,z6,z11]),(0,[z574,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z575,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z576,z6]),(0,[z35,z0,z1,z15,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z577,z6]),(0,[z0,z1,z2,z578,z4,z5,z6])],[(0,[z35,z0,z1,z2,z22,z5,z6]),(0,[z1,z2,z112,z4,z219,z5,z6]),(0,[z0,z1,z579,z2,z4,z5,z6]),(0,[z212,z0,z1,z2,z22,z5,z6]),(0,[z580,z0,z1,z2,z4,z5,z6]),(0,[z63,z0,z1,z2,z5,z6,z11])],[(0,[z0,z1,z2,z4,z581,z5,z6]),(0,[z111,z0,z1,z2,z22,z5,z6]),(1,[z0,z465,z2,z4,z5,z6]),(0,[z227,z0,z1,z2,z4,z50,z6]),(0,[z0,z1,z2,z4,z5,z582,z6]),(0,[z0,z1,z2,z4,z5,z583,z6]),(0,[z430,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z584,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z585,z5,z6]),(0,[z0,z1,z2,z22,z219,z5,z6]),(0,[z0,z1,z2,z23,z5,z6,z11])],[(0,[z586,z0,z1,z2,z4,z5,z6]),(0,[z0,z587,z1,z2,z4,z5,z6]),(0,[z491,z0,z1,z2,z4,z5,z6])],[(0,[z554,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z588,z5,z6]),(0,[z0,z589,z1,z2,z4,z5,z6]),(0,[z0,z590,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z504,z5,z6]),(0,[z591,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z592,z5,z6])],[(0,[z91,z227,z0,z2,z4,z5,z6]),(0,[z0,z449,z1,z2,z4,z5,z6])],[(0,[z7,z0,z1,z2,z4,z5,z205]),(0,[z0,z1,z2,z4,z593,z5,z6]),(0,[z0,z1,z594,z2,z4,z5,z6]),(0,[z428,z0,z1,z2,z4,z5,z6])],[(0,[z124,z0,z1,z2,z22,z5,z6]),(0,[z133,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z595,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z596]),(1,[z0,z1,z2,z5,z298,z6]),(0,[z0,z1,z2,z4,z597,z5,z6]),(0,[z20,z0,z1,z2,z22,z5,z6]),(0,[z0,z1,z598,z2,z4,z5,z6]),(1,[z0,z1,z2,z22,z5,z32])],[(0,[z599,z0,z1,z2,z4,z5,z6]),(0,[z600,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z601,z6]),(0,[z0,z1,z2,z602,z4,z5,z6]),(0,[z0,z1,z443,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z603,z6]),(0,[z0,z1,z2,z604,z4,z5,z6])],[(1,[z0,z1,z2,z4,z295,z6]),(0,[z0,z1,z2,z4,z5,z6,z605]),(1,[z154,z1,z46,z4,z5,z6]),(0,[z0,z1,z15,z4,z5,z16,z6]),(0,[z0,z1,z15,z2,z22,z5,z6])]],
   [[(0,[z35,z0,z1,z4,z56,z5,z6]),(0,[z147,z0,z1,z2,z4,z5,z156]),(0,[z0,z67,z1,z2,z22,z5,z6]),(0,[z606,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z6,z19,z11])],[(0,[z607,z0,z1,z2,z4,z5,z6]),(1,[z49,z0,z58,z4,z5,z6]),(0,[z0,z1,z608,z2,z4,z5,z6]),(0,[z0,z1,z2,z609,z4,z5,z6]),(0,[z0,z1,z610,z2,z4,z5,z6]),(0,[z102,z0,z1,z2,z22,z5,z6])],[(0,[z0,z1,z2,z4,z611,z5,z6]),(0,[z0,z1,z2,z4,z612,z5,z6]),(0,[z0,z613,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z509,z4,z5,z6]),(0,[z614,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z615,z5,z6]),(1,[z161,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z616,z6]),(0,[z7,z0,z1,z2,z22,z5,z6]),(0,[z49,z0,z1,z2,z4,z5,z6]),(0,[z617,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z618,z2,z4,z5,z6])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(1,[z554,z0,z1,z2,z4,z5]),(0,[z0,z1,z619,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z620,z5,z6])],[(1,[z140,z1,z2,z4,z5,z205])],[(1,[z0,z1,z2,z4,z564,z6]),(0,[z621,z0,z1,z2,z4,z5,z6]),(0,[z622,z0,z1,z2,z4,z5,z6]),(0,[z140,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z8,z6,z205]),(0,[z0,z1,z2,z4,z5,z39,z6]),(0,[z0,z2,z4,z56,z5,z500,z6]),(0,[z0,z623,z1,z2,z4,z5,z6])],[(0,[z624,z0,z1,z2,z4,z5,z6]),(0,[z140,z0,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z6,z625]),(1,[z20,z0,z1,z2,z83,z6]),(0,[z125,z0,z1,z2,z5,z6,z11]),(0,[z0,z1,z2,z31,z22,z5,z6])]],
   [[(0,[z0,z1,z2,z46,z4,z5,z6]),(1,[z0,z2,z388,z4,z5,z6]),(0,[z0,z1,z2,z5,z298,z54,z6]),(0,[z0,z1,z2,z22,z85,z5,z6]),(0,[z0,z1,z2,z40,z22,z5,z6]),(0,[z0,z1,z2,z4,z5,z626,z6]),(1,[z0,z1,z2,z4,z24,z98])],[(0,[z627,z0,z1,z2,z4,z5,z6]),(0,[z342,z0,z2,z4,z5,z54,z6]),(0,[z0,z1,z2,z628,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z629]),(0,[z0,z1,z2,z4,z5,z6,z290])],[(0,[z0,z1,z2,z4,z233,z5,z6]),(0,[z47,z0,z1,z2,z22,z5,z6]),(0,[z526,z0,z1,z2,z4,z5,z6]),(0,[z51,z0,z1,z2,z22,z5,z6]),(0,[z0,z1,z15,z2,z4,z5,z19]),(0,[z0,z1,z2,z5,z6,z11,z166]),(0,[z630,z0,z1,z2,z4,z5,z6])],[(0,[z154,z0,z67,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z631,z5,z6]),(0,[z0,z1,z2,z4,z632,z5,z6]),(0,[z0,z1,z2,z201,z5,z12,z6]),(0,[z20,z0,z1,z2,z4,z98,z6]),(0,[z0,z1,z2,z22,z5,z98,z6])],[(0,[z91,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z438,z6]),(0,[z0,z1,z2,z4,z5,z633,z6])],[(0,[z154,z0,z1,z4,z5,z6,z19]),(0,[z0,z1,z2,z4,z5,z634,z6]),(0,[z0,z1,z2,z4,z5,z635,z6]),(0,[z0,z1,z2,z4,z98,z6,z103])],[(0,[z636,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z6,z205,z11]),(0,[z0,z1,z2,z4,z5,z637,z6]),(0,[z0,z1,z2,z4,z5,z6,z638]),(0,[z0,z1,z2,z4,z5,z639,z6]),(0,[z51,z0,z1,z2,z504,z5,z6]),(0,[z0,z640,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z4,z23,z6]),(0,[z225,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z297])],[(0,[z0,z1,z2,z4,z5,z641,z6]),(0,[z49,z124,z0,z2,z4,z5,z6]),(1,[z35,z1,z36,z4,z5,z6]),(0,[z642,z0,z1,z2,z4,z5,z6]),(0,[z102,z140,z0,z1,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z4,z5,z643,z6]),(0,[z154,z0,z1,z40,z4,z5,z6]),(0,[z644,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z645]),(0,[z0,z1,z127,z40,z4,z5,z6]),(0,[z117,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z22,z56,z5,z6])],[(0,[z0,z1,z2,z4,z5,z646,z6]),(0,[z0,z1,z68,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z647,z6]),(0,[z0,z1,z2,z4,z5,z6,z648])],[(0,[z154,z0,z1,z36,z4,z5,z6]),(0,[z147,z0,z1,z2,z4,z5,z6]),(0,[z649,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z650,z6]),(0,[z0,z1,z252,z2,z4,z5,z6])],[(0,[z651,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z652,z5,z6])],[(0,[z0,z1,z2,z653,z4,z5,z6])],[(0,[z654,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z115,z5,z6,z11]),(0,[z0,z1,z2,z4,z5,z6,z655]),(0,[z0,z1,z2,z4,z5,z6,z656]),(0,[z0,z1,z2,z4,z5,z6,z657]),(0,[z0,z1,z2,z4,z5,z658,z6]),(0,[z0,z1,z2,z22,z24,z5,z6])],[(0,[z659,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z87,z5,z6,z11]),(0,[z0,z1,z2,z5,z6,z11,z211]),(0,[z0,z1,z2,z5,z32,z6,z11])],[(0,[z147,z0,z1,z2,z23,z5,z6]),(0,[z0,z1,z2,z4,z5,z660,z6])]],
   [[(0,[z154,z0,z1,z2,z4,z228,z6]),(1,[z0,z1,z167,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z661,z6]),(0,[z0,z1,z2,z4,z662,z5,z6]),(0,[z0,z1,z2,z5,z16,z6,z171])],[(0,[z91,z0,z68,z2,z4,z5,z6]),(0,[z147,z212,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z663])],[(0,[z35,z0,z67,z1,z4,z5,z6]),(0,[z0,z1,z2,z112,z4,z5,z6]),(0,[z664,z0,z1,z2,z4,z5,z6]),(0,[z665,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z666]),(0,[z0,z1,z2,z281,z5,z98,z6])],[(0,[z0,z1,z92,z2,z5,z6,z11]),(0,[z216,z47,z1,z2,z4,z5,z6]),(0,[z0,z667,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z668])],[(0,[z0,z1,z2,z4,z228,z5,z6]),(0,[z0,z1,z669,z2,z4,z5,z6]),(0,[z670,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z671,z2,z4,z5,z6]),(0,[z49,z0,z42,z2,z4,z5,z6]),(0,[z0,z29,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z672,z5,z6]),(0,[z125,z0,z1,z2,z22,z5,z6])],[(0,[z0,z673,z1,z2,z4,z5,z6]),(1,[z0,z1,z4,z5,z53,z6]),(0,[z674,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z145,z4,z56,z6])],[(0,[z35,z0,z1,z40,z4,z5,z6]),(0,[z0,z42,z1,z2,z5,z6,z11]),(0,[z0,z1,z2,z4,z5,z675,z6]),(0,[z102,z0,z1,z172,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z676,z4,z5,z6]),(0,[z0,z1,z2,z4,z677,z5,z6]),(0,[z49,z0,z67,z2,z4,z5,z6]),(0,[z0,z678,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z4,z83,z6]),(1,[z0,z1,z2,z4,z5,z260])],[(0,[z0,z679,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z680,z5,z6]),(0,[z681,z0,z1,z2,z4,z5,z6]),(0,[z102,z0,z1,z2,z4,z6,z103])],[(0,[z35,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z54,z6,z205]),(0,[z212,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z682,z2,z4,z5,z6]),(1,[z399,z1,z2,z4,z5,z6])],[(0,[z532,z0,z1,z2,z4,z5,z6]),(0,[z0,z683,z1,z2,z4,z5,z6]),(0,[z684,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z15,z2,z4,z5,z16])],[(0,[z0,z1,z2,z685,z4,z5,z6]),(0,[z0,z1,z2,z74,z5,z6,z11])],[(1,[z0,z1,z2,z407,z5,z6]),(0,[z84,z0,z1,z2,z40,z5,z6]),(0,[z0,z1,z2,z4,z5,z83,z6])],[(0,[z0,z1,z2,z4,z5,z686,z6]),(0,[z84,z111,z0,z1,z2,z5,z6]),(0,[z334,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z687,z6])],[(0,[z0,z1,z2,z4,z5,z8,z6]),(0,[z227,z0,z1,z2,z4,z10,z6]),(0,[z0,z1,z2,z688,z4,z5,z6]),(0,[z689,z0,z1,z2,z4,z5,z6]),(0,[z690,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z4,z5,z385])]],
   [[(0,[z691,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z692,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z693])],[(0,[z0,z1,z2,z4,z694,z5,z6]),(0,[z20,z0,z1,z2,z4,z5,z6]),(0,[z649,z0,z1,z2,z22,z5,z6]),(0,[z0,z1,z2,z172,z4,z5,z6])],[(0,[z0,z1,z214,z2,z4,z5,z6]),(0,[z0,z1,z695,z2,z4,z5,z6]),(0,[z0,z1,z2,z696,z4,z5,z6]),(0,[z0,z1,z2,z58,z5,z6,z11]),(0,[z0,z1,z2,z4,z5,z57,z6]),(0,[z0,z1,z2,z697,z4,z5,z6])],[(0,[z0,z1,z2,z4,z698,z5,z6]),(0,[z0,z1,z2,z4,z699,z5,z6]),(0,[z0,z2,z58,z4,z5,z6,z30]),(0,[z0,z700,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z701,z6]),(0,[z0,z1,z15,z2,z4,z5,z6]),(1,[z0,z294,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z564,z5,z6]),(0,[z0,z2,z388,z46,z4,z5,z6]),(0,[z0,z702,z1,z2,z4,z5,z6]),(0,[z0,z67,z1,z2,z4,z5,z6]),(0,[z703,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z145,z4,z56,z5,z6]),(0,[z0,z1,z2,z22,z4,z5,z6])],[(0,[z0,z1,z2,z704,z4,z5,z6]),(0,[z102,z399,z1,z2,z4,z5,z6]),(0,[z102,z0,z1,z2,z4,z5,z6])],[(0,[z212,z124,z0,z2,z4,z5,z6]),(0,[z102,z20,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z5,z98,z6,z11])],[(0,[z126,z0,z1,z2,z4,z5,z6]),(0,[z154,z1,z2,z46,z4,z5,z6]),(0,[z0,z1,z705,z2,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z5,z6]),(0,[z0,z706,z1,z2,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z5,z337,z11])],[(0,[z0,z1,z2,z4,z5,z707]),(0,[z140,z1,z2,z141,z5,z205]),(0,[z708,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z709,z5,z6])],[(0,[z124,z241,z2,z5,z6,z11]),(0,[z0,z1,z4,z5,z710,z6]),(0,[z47,z1,z2,z5,z205,z11]),(0,[z0,z1,z2,z711,z5,z11]),(0,[z0,z1,z2,z5,z638,z11])],[(0,[z143,z0,z1,z2,z5,z6]),(0,[z0,z1,z712,z2,z5,z6]),(0,[z0,z1,z2,z4,z438,z6]),(0,[z0,z1,z2,z5,z6,z713]),(0,[z0,z1,z714,z4,z5,z6]),(0,[z0,z1,z69,z317,z5,z6])],[(0,[z0,z114,z1,z2,z5,z261]),(0,[z0,z1,z715,z4,z5,z6]),(0,[z0,z114,z2,z5,z6,z332]),(0,[z0,z716,z2,z4,z5,z6])],[(0,[z320,z1,z2,z5,z205,z11]),(0,[z0,z1,z2,z5,z6,z717]),(0,[z0,z1,z718,z4,z5,z6])],[(0,[z0,z29,z2,z4,z295,z6]),(0,[z212,z561,z0,z2,z5,z6]),(0,[z232,z0,z2,z5,z6,z11]),(0,[z84,z627,z0,z1,z5,z6]),(0,[z20,z0,z1,z2,z551,z6]),(0,[z554,z0,z1,z2,z22,z5]),(0,[z0,z2,z74,z719,z5,z6]),(0,[z0,z1,z152,z5,z6,z11]),(0,[z0,z1,z137,z504,z5,z6]),(0,[z0,z1,z2,z5,z286,z11])],[(0,[z124,z2,z4,z106,z5,z6]),(0,[z0,z1,z2,z720,z5,z6]),(0,[z0,z1,z2,z4,z5,z156]),(0,[z0,z1,z2,z219,z5,z261]),(0,[z721,z0,z2,z4,z5,z6]),(0,[z102,z0,z1,z2,z407,z5])]],
   [[(0,[z0,z722,z2,z4,z5,z6]),(1,[z0,z2,z4,z5,z723]),(0,[z102,z0,z1,z172,z4,z103])],[(0,[z0,z1,z2,z228,z6,z11]),(0,[z216,z1,z2,z54,z6,z11]),(0,[z342,z0,z2,z5,z6,z11]),(0,[z0,z1,z2,z4,z5,z724]),(0,[z0,z725,z2,z4,z5,z6])],[(0,[z126,z124,z0,z4,z5,z6]),(0,[z154,z232,z0,z4,z5,z6]),(0,[z0,z2,z5,z86,z6,z11]),(0,[z0,z1,z2,z726,z5,z6]),(0,[z47,z1,z2,z22,z87,z6]),(0,[z7,z1,z2,z5,z8,z11]),(0,[z0,z2,z4,z727,z50,z6]),(0,[z0,z1,z2,z163,z5,z6]),(0,[z1,z2,z5,z6,z11,z728]),(0,[z97,z0,z1,z2,z24,z11])],[(0,[z0,z1,z729,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z730]),(0,[z14,z1,z2,z4,z54,z6]),(0,[z0,z1,z731,z85,z5,z6]),(0,[z0,z1,z172,z4,z5,z6]),(0,[z0,z1,z2,z22,z5,z732]),(0,[z399,z1,z172,z4,z5,z6])],[(0,[z91,z92,z2,z22,z5,z6]),(0,[z0,z1,z2,z4,z733,z6]),(0,[z0,z734,z2,z4,z5,z6]),(0,[z118,z0,z1,z4,z5,z735]),(0,[z0,z180,z2,z509,z5,z6]),(0,[z428,z1,z2,z146,z5,z6])],[(0,[z91,z26,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z298,z55]),(0,[z0,z736,z2,z4,z5,z6]),(0,[z737,z1,z2,z4,z5,z6]),(0,[z0,z301,z1,z2,z5,z11])],[(0,[z0,z1,z2,z4,z5,z738]),(0,[z232,z35,z0,z4,z5,z6]),(0,[z147,z101,z1,z2,z5,z6]),(0,[z59,z49,z0,z4,z5,z6]),(0,[z0,z1,z2,z739,z6,z11])],[(0,[z0,z1,z2,z4,z740,z6]),(0,[z0,z1,z2,z295,z6,z11]),(0,[z0,z1,z167,z4,z5,z6]),(1,[z0,z1,z2,z5,z732]),(0,[z97,z225,z0,z1,z2,z11])]],
   [[(0,[z35,z1,z579,z4,z5,z6]),(0,[z0,z1,z2,z307,z5,z11]),(0,[z0,z2,z5,z6,z128,z48]),(0,[z0,z180,z2,z74,z5,z6])],[(0,[z0,z1,z2,z4,z5,z741]),(0,[z0,z1,z2,z742,z5,z6]),(0,[z743,z0,z2,z5,z6,z11]),(0,[z0,z1,z2,z6,z96,z297]),(0,[z0,z1,z2,z4,z5,z744])],[(0,[z0,z1,z2,z4,z5,z745]),(0,[z0,z746,z2,z4,z5,z6]),(0,[z0,z1,z4,z408,z57,z6])],[(0,[z0,z747,z2,z4,z5,z6]),(0,[z227,z0,z2,z4,z727,z6]),(0,[z0,z236,z2,z268,z5,z6]),(0,[z102,z0,z1,z2,z5,z297])],[(0,[z49,z0,z300,z4,z5,z6]),(0,[z118,z0,z1,z4,z5,z19])],[(0,[z0,z1,z4,z5,z53,z6]),(0,[z0,z1,z2,z5,z748,z6]),(0,[z0,z749,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z750]),(0,[z0,z1,z2,z751,z5,z6]),(0,[z0,z1,z2,z201,z5,z6]),(0,[z0,z1,z145,z4,z56,z6]),(0,[z428,z236,z2,z4,z5,z6])],[(0,[z204,z0,z1,z4,z5,z6]),(0,[z111,z1,z2,z5,z6,z310]),(0,[z0,z752,z2,z4,z5,z6])],[(0,[z0,z1,z2,z753,z5,z6]),(0,[z0,z1,z2,z5,z754,z6]),(0,[z554,z291,z0,z1,z4,z5]),(0,[z0,z755,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z260])]],
   [[(0,[z0,z1,z2,z564,z6,z11]),(0,[z425,z0,z1,z2,z5,z11]),(0,[z0,z252,z2,z163,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z399,z1,z2,z4,z5,z6]),(0,[z0,z2,z756,z4,z5,z6]),(0,[z757,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z758,z5,z6]),(0,[z0,z1,z2,z5,z6,z759]),(0,[z0,z1,z2,z5,z6,z760]),(0,[z761,z0,z1,z2,z5,z6])],[(0,[z49,z0,z2,z4,z295,z6]),(0,[z0,z1,z2,z4,z5,z762]),(0,[z0,z1,z2,z4,z763,z6]),(0,[z0,z1,z2,z4,z5,z764]),(0,[z20,z0,z1,z2,z6,z96]),(0,[z0,z1,z215,z5,z6,z11])],[(0,[z0,z1,z2,z765,z5,z6]),(0,[z0,z1,z2,z766,z5,z6]),(0,[z0,z1,z2,z4,z5,z767]),(0,[z0,z1,z768,z4,z5,z6])],[(0,[z147,z2,z233,z219,z5,z6]),(0,[z769,z0,z1,z2,z5,z6]),(0,[z0,z42,z2,z4,z505,z6]),(0,[z0,z1,z152,z22,z5,z6]),(0,[z0,z123,z2,z5,z6,z11]),(0,[z102,z0,z1,z2,z5,z770])],[(0,[z0,z1,z2,z4,z5,z771]),(0,[z0,z1,z4,z772,z5,z6]),(0,[z773,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z774,z5,z6]),(0,[z0,z1,z2,z407,z5,z8]),(0,[z775,z0,z1,z5,z6,z11])],[(0,[z0,z1,z2,z776,z5,z6]),(0,[z147,z1,z2,z219,z5,z156]),(0,[z147,z161,z2,z219,z5,z6]),(0,[z291,z0,z1,z4,z56,z6])],[(0,[z0,z2,z4,z233,z5,z6]),(0,[z154,z232,z46,z4,z5,z6]),(0,[z35,z1,z4,z5,z327,z6]),(0,[z0,z1,z2,z4,z777,z6])]],
   [[(0,[z84,z0,z1,z248,z5,z6]),(0,[z130,z1,z2,z4,z87,z6])],[(0,[z0,z2,z4,z778,z5,z6]),(0,[z0,z1,z2,z5,z6,z779]),(0,[z357,z0,z1,z2,z5,z11])],[(0,[z0,z1,z780,z4,z5,z6]),(0,[z0,z1,z2,z4,z781,z6]),(0,[z204,z111,z0,z1,z5,z6]),(0,[z0,z1,z69,z5,z6,z11]),(0,[z20,z0,z1,z2,z132,z6]),(0,[z0,z1,z172,z22,z5,z6]),(0,[z0,z294,z215,z4,z5,z6])],[(0,[z0,z1,z2,z5,z6,z782]),(0,[z147,z1,z218,z219,z5,z6]),(0,[z0,z1,z2,z783,z5,z6]),(0,[z291,z0,z1,z4,z57,z6]),(0,[z0,z1,z2,z5,z784,z6])],[(0,[z0,z2,z4,z10,z295,z6]),(0,[z84,z0,z1,z2,z5,z261]),(0,[z0,z1,z2,z22,z5,z134]),(0,[z414,z0,z1,z4,z57,z6]),(0,[z0,z2,z22,z5,z500,z6])],[(0,[z49,z0,z343,z4,z5,z6]),(0,[z0,z1,z2,z4,z785,z6]),(0,[z357,z0,z1,z2,z132,z6])],[(0,[z0,z1,z786,z4,z5,z6]),(0,[z0,z1,z2,z787,z5,z6]),(0,[z0,z1,z2,z788,z5,z6]),(0,[z0,z1,z2,z789,z5,z6]),(0,[z20,z0,z1,z2,z790,z6]),(0,[z0,z1,z2,z21,z146,z6]),(0,[z791,z0,z2,z4,z5,z6])],[(0,[z792,z0,z1,z2,z5,z6]),(0,[z0,z252,z2,z4,z5,z6]),(0,[z793,z0,z1,z4,z5,z6]),(0,[z0,z1,z5,z39,z6,z11]),(0,[z0,z145,z4,z56,z500,z6]),(0,[z0,z236,z2,z146,z5,z6])]],
   [[(0,[z342,z0,z2,z4,z295,z6]),(0,[z0,z1,z794,z4,z5,z6]),(0,[z0,z152,z4,z5,z50,z6]),(0,[z102,z97,z0,z1,z2,z11])],[(0,[z91,z0,z152,z4,z5,z6]),(0,[z143,z0,z1,z444,z5,z6]),(0,[z20,z0,z1,z2,z5,z261]),(0,[z0,z1,z2,z5,z6,z795]),(0,[z0,z1,z2,z796,z5,z6]),(0,[z0,z1,z797,z4,z5,z6])],[(0,[z0,z1,z2,z5,z6,z798]),(0,[z0,z1,z2,z4,z5,z799]),(0,[z20,z0,z1,z2,z6,z297])],[(0,[z800,z0,z1,z2,z5,z6]),(0,[z49,z0,z454,z4,z5,z6]),(0,[z554,z399,z1,z2,z4,z5]),(0,[z140,z399,z1,z2,z4,z5]),(0,[z0,z1,z4,z5,z39,z6]),(0,[z118,z0,z1,z22,z5,z19])],[(0,[z0,z1,z2,z5,z6,z801]),(0,[z0,z1,z2,z5,z770,z11]),(0,[z0,z294,z2,z268,z5,z6])],[(0,[z0,z1,z802,z4,z5,z6]),(0,[z204,z0,z1,z22,z5,z6]),(0,[z0,z1,z2,z803,z5,z6]),(0,[z0,z114,z2,z74,z5,z6])],[(0,[z0,z1,z2,z5,z804,z6]),(0,[z0,z1,z4,z5,z53,z55]),(0,[z0,z1,z137,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z805]),(0,[z0,z806,z2,z4,z5,z6]),(0,[z225,z0,z1,z2,z5,z732]),(0,[z0,z1,z2,z578,z5,z11])],[(0,[z0,z1,z2,z4,z807,z6]),(0,[z0,z1,z2,z4,z6,z808]),(0,[z147,z397,z1,z2,z5,z6]),(0,[z0,z67,z487,z4,z5,z6]),(0,[z0,z1,z809,z4,z5,z6]),(0,[z102,z0,z1,z2,z21,z11])]],
   [[(0,[z147,z1,z2,z219,z5,z6]),(0,[z0,z810,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z799,z205]),(0,[z0,z449,z2,z5,z6,z11]),(0,[z0,z1,z215,z22,z5,z6])],[(0,[z216,z1,z2,z22,z54,z6]),(0,[z0,z1,z2,z811,z5,z6])],[(0,[z0,z1,z2,z4,z5,z812]),(0,[z0,z1,z2,z4,z813,z6]),(0,[z0,z814,z2,z4,z5,z6]),(0,[z0,z1,z2,z815,z5,z6]),(0,[z216,z334,z1,z2,z54,z6]),(0,[z0,z1,z2,z4,z5,z55]),(0,[z0,z123,z2,z22,z5,z6])],[(0,[z0,z1,z816,z4,z5,z6]),(0,[z0,z1,z2,z817,z5,z6]),(0,[z140,z1,z2,z5,z205,z11]),(0,[z0,z1,z40,z731,z5,z6])],[(0,[z818,z0,z1,z4,z5,z6]),(0,[z819,z0,z1,z2,z4,z5]),(0,[z0,z426,z2,z4,z10,z6]),(0,[z0,z449,z145,z4,z5,z6]),(0,[z0,z1,z2,z820,z6,z11])],[(0,[z0,z1,z2,z5,z6,z821]),(0,[z0,z1,z2,z22,z228,z6]),(0,[z0,z1,z2,z5,z415,z11]),(0,[z0,z1,z2,z822,z5,z6]),(0,[z0,z550,z68,z4,z5,z6]),(0,[z0,z1,z2,z823,z5,z6]),(0,[z84,z0,z1,z85,z5,z6]),(0,[z0,z1,z2,z5,z385,z11])],[(0,[z0,z1,z2,z5,z418,z11]),(0,[z47,z1,z2,z4,z87,z6]),(0,[z0,z1,z2,z731,z5,z6])],[(0,[z0,z1,z2,z824,z5,z6]),(0,[z216,z1,z2,z4,z55,z54]),(0,[z0,z825,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z732])]],
   [[(0,[z91,z92,z2,z4,z5,z6]),(0,[z0,z1,z2,z826,z5,z6]),(0,[z0,z67,z68,z5,z6,z11]),(0,[z102,z0,z1,z2,z4,z524])],[(0,[z291,z0,z1,z5,z298,z6]),(0,[z0,z1,z127,z731,z5,z6]),(0,[z827,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z6,z297])],[(0,[z161,z0,z4,z218,z5,z6]),(0,[z0,z1,z2,z5,z828,z6]),(0,[z0,z2,z4,z5,z6,z829]),(0,[z51,z0,z2,z5,z30,z11]),(0,[z0,z1,z2,z22,z5,z701]),(0,[z97,z0,z1,z2,z146,z6]),(0,[z102,z0,z1,z2,z4,z103])],[(0,[z241,z814,z2,z4,z5,z6]),(0,[z133,z35,z0,z1,z5,z6]),(0,[z0,z830,z2,z4,z5,z6]),(1,[z0,z2,z719,z5,z6]),(0,[z491,z0,z1,z88,z5,z6])],[(0,[z0,z1,z2,z5,z784,z55]),(0,[z664,z0,z1,z2,z5,z11]),(0,[z49,z0,z831,z4,z5,z6]),(0,[z0,z1,z69,z504,z5,z6]),(0,[z0,z832,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z98,z385])],[(0,[z0,z1,z2,z833,z5,z6]),(0,[z154,z1,z326,z46,z5,z6]),(0,[z35,z1,z4,z5,z6,z416]),(0,[z0,z1,z2,z5,z6,z834]),(0,[z227,z0,z2,z50,z6,z11]),(0,[z0,z1,z835,z4,z5,z6]),(0,[z102,z428,z1,z2,z5,z11])],[(0,[z0,z2,z4,z87,z500,z6]),(0,[z446,z0,z1,z4,z5,z19]),(0,[z0,z68,z4,z5,z633,z6])],[(0,[z836,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z205,z96,z11]),(0,[z0,z837,z1,z2,z5,z6]),(0,[z1,z2,z4,z5,z838,z6]),(0,[z839,z1,z2,z5,z6,z11]),(1,[z0,z1,z2,z4,z744])]],
   [[(0,[z124,z2,z275,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z840]),(0,[z0,z1,z4,z87,z39,z6]),(0,[z0,z1,z5,z6,z246,z11]),(0,[z0,z1,z2,z5,z6,z841]),(0,[z398,z0,z1,z2,z5,z11]),(0,[z0,z1,z2,z4,z24,z96]),(0,[z0,z294,z2,z146,z5,z6])],[(0,[z0,z1,z2,z5,z6,z842]),(0,[z133,z0,z1,z2,z5,z6]),(0,[z0,z2,z843,z4,z5,z6]),(0,[z0,z1,z5,z6,z11,z844]),(0,[z0,z236,z2,z5,z6,z11])],[(0,[z0,z4,z233,z218,z5,z6]),(0,[z845,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z24,z637]),(0,[z0,z2,z5,z8,z128,z11]),(0,[z0,z1,z2,z846,z5,z6]),(0,[z0,z1,z2,z4,z5,z847]),(0,[z0,z1,z2,z848,z5,z6]),(0,[z0,z1,z2,z5,z732,z11]),(0,[z532,z1,z2,z5,z6,z310]),(0,[z0,z399,z1,z2,z5,z11]),(0,[z0,z1,z2,z5,z6,z770])],[(0,[z0,z1,z2,z849,z5,z6]),(0,[z0,z1,z2,z850,z5,z6]),(0,[z851,z0,z1,z4,z5,z6]),(0,[z852,z0,z1,z2,z5,z6]),(0,[z81,z0,z1,z2,z5,z11]),(0,[z0,z1,z2,z22,z6,z96]),(0,[z0,z1,z2,z281,z24,z98])],[(0,[z51,z0,z2,z317,z5,z30]),(0,[z0,z1,z2,z22,z96,z11])],[(0,[z0,z1,z853,z4,z5,z6]),(0,[z0,z4,z5,z86,z53,z6]),(0,[z573,z1,z2,z4,z87,z6]),(0,[z0,z1,z137,z22,z5,z6])],[(0,[z854,z0,z1,z4,z5,z6]),(0,[z558,z1,z2,z4,z5,z8]),(0,[z0,z1,z855,z4,z5,z6])],[(0,[z0,z1,z2,z856,z5,z6]),(0,[z0,z1,z2,z4,z5,z857]),(0,[z320,z1,z2,z219,z5,z6]),(0,[z342,z0,z4,z5,z53,z6]),(0,[z7,z1,z2,z129,z5,z8]),(0,[z0,z1,z2,z22,z5,z402]),(0,[z0,z1,z4,z5,z735,z19]),(0,[z0,z1,z2,z21,z23,z260]),(0,[z0,z1,z2,z22,z5,z11]),(0,[z97,z532,z0,z1,z2,z6])]],
   [[(0,[z0,z1,z2,z5,z6,z858]),(0,[z0,z859,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z860,z6]),(0,[z0,z1,z152,z4,z5,z6]),(0,[z118,z0,z1,z163,z5,z19]),(0,[z20,z0,z1,z2,z5,z385])],[(0,[z0,z1,z861,z2,z5,z6]),(0,[z0,z1,z2,z5,z261,z11]),(0,[z0,z1,z2,z4,z860,z6]),(0,[z0,z1,z2,z22,z5,z55]),(0,[z0,z1,z2,z5,z6,z13]),(0,[z117,z0,z1,z22,z57,z6])],[],[(0,[z342,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z549,z11]),(0,[z357,z0,z1,z2,z5,z385])],[],[(0,[z0,z1,z2,z5,z477,z11]),(0,[z0,z862,z2,z4,z5,z6]),(0,[z102,z0,z236,z2,z5,z11])],[(0,[z0,z1,z2,z5,z481,z11]),(0,[z0,z67,z68,z22,z5,z6]),(0,[z0,z1,z2,z863,z5,z6]),(0,[z0,z1,z864,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z735])],[(0,[z0,z123,z2,z163,z5,z6])]],
   [[(0,[z0,z1,z2,z5,z865,z6]),(0,[z0,z1,z2,z4,z5,z866]),(0,[z0,z1,z2,z5,z6,z867]),(0,[z0,z868,z2,z4,z5,z6])],[(0,[z0,z1,z4,z438,z6,z19]),(0,[z204,z0,z4,z233,z5,z6]),(0,[z1,z2,z112,z783,z5,z6]),(0,[z0,z1,z869,z4,z5,z6]),(0,[z0,z1,z2,z5,z11,z629])],[(0,[z0,z1,z2,z22,z5,z261]),(0,[z0,z1,z870,z4,z5,z6]),(0,[z0,z1,z2,z871,z5,z6]),(0,[z49,z0,z471,z4,z5,z6]),(0,[z0,z2,z4,z10,z727,z6]),(0,[z872,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z790,z83,z6])],[(0,[z0,z1,z22,z5,z53,z6]),(0,[z536,z0,z1,z2,z5,z11]),(0,[z743,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z873,z6]),(0,[z0,z2,z4,z5,z86,z6]),(0,[z124,z0,z152,z4,z5,z6]),(0,[z0,z1,z145,z4,z874,z6]),(0,[z427,z1,z2,z131,z5,z6])],[(0,[z0,z29,z2,z4,z5,z368]),(0,[z875,z1,z2,z4,z5,z6]),(0,[z876,z1,z2,z4,z5,z6])],[(0,[z0,z1,z877,z4,z5,z6]),(0,[z0,z1,z2,z878,z5,z6]),(0,[z0,z879,z2,z4,z5,z6]),(0,[z0,z1,z4,z880,z5,z6])],[(0,[z0,z1,z2,z5,z6,z881]),(0,[z554,z334,z0,z1,z2,z5]),(0,[z0,z1,z4,z5,z6,z882]),(0,[z446,z0,z2,z4,z5,z30]),(0,[z1,z2,z4,z5,z6,z728]),(0,[z883,z0,z1,z2,z6,z11]),(0,[z0,z236,z2,z22,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z884,z6]),(0,[z1,z2,z4,z5,z885,z6])],[(0,[z0,z1,z2,z4,z5,z886]),(0,[z0,z1,z2,z887,z5,z6]),(0,[z0,z1,z2,z24,z96,z11]),(0,[z102,z0,z1,z2,z4,z96])],[(0,[z0,z1,z888,z4,z5,z6]),(0,[z889,z0,z1,z4,z5,z6])],[(0,[z91,z589,z2,z4,z5,z6]),(0,[z124,z241,z2,z22,z5,z6]),(0,[z890,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z891,z6]),(0,[z0,z1,z2,z6,z11,z892]),(0,[z102,z0,z294,z2,z5,z11])],[(0,[z0,z1,z214,z2,z5,z6]),(1,[z1,z2,z783,z5,z6]),(0,[z0,z1,z215,z4,z5,z6]),(0,[z0,z1,z2,z24,z5,z11]),(0,[z399,z1,z215,z4,z5,z6]),(0,[z0,z1,z4,z5,z893,z6])],[(0,[z0,z1,z4,z894,z5,z6]),(0,[z216,z1,z2,z4,z54,z6]),(0,[z0,z1,z895,z4,z5,z6]),(0,[z569,z1,z2,z4,z54,z6])],[(0,[z212,z0,z2,z234,z5,z6]),(0,[z0,z2,z4,z5,z6,z128]),(0,[z0,z1,z40,z568,z5,z6]),(0,[z896,z0,z1,z2,z4,z5]),(0,[z0,z123,z2,z4,z5,z6]),(0,[z0,z1,z897,z4,z5,z6])],[(0,[z0,z1,z2,z898,z5,z6]),(0,[z232,z0,z2,z22,z5,z6]),(0,[z899,z0,z1,z2,z4,z6]),(0,[z775,z0,z1,z4,z5,z6]),(0,[z291,z0,z1,z5,z6,z11]),(0,[z0,z1,z167,z5,z8,z11]),(0,[z900,z0,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z901,z6]),(0,[z0,z1,z2,z5,z205,z11]),(0,[z7,z1,z2,z5,z8,z48]),(0,[z0,z1,z2,z5,z6,z902])],[(0,[z91,z73,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z228,z6]),(0,[z0,z1,z2,z141,z5,z6]),(0,[z0,z1,z4,z5,z6,z903]),(0,[z0,z1,z904,z4,z5,z6]),(0,[z0,z1,z2,z5,z517,z11]),(0,[z0,z905,z2,z4,z5,z6]),(0,[z690,z0,z1,z2,z5,z11])],[(0,[z0,z2,z4,z10,z464,z6]),(0,[z0,z906,z2,z4,z5,z6]),(0,[z342,z0,z2,z22,z5,z6]),(0,[z0,z42,z152,z4,z5,z6]),(0,[z0,z1,z2,z21,z387,z6])],[(0,[z0,z1,z2,z4,z907,z6]),(0,[z0,z1,z2,z908,z5,z6]),(0,[z147,z204,z0,z1,z5,z6]),(1,[z1,z2,z4,z5,z799]),(0,[z0,z1,z15,z5,z16,z11]),(0,[z0,z1,z2,z5,z909,z6])],[(0,[z554,z0,z1,z2,z5,z298]),(0,[z0,z1,z2,z528,z5,z11]),(0,[z0,z1,z2,z22,z5,z293]),(0,[z0,z252,z4,z5,z6,z19]),(0,[z0,z1,z2,z268,z5,z260]),(0,[z102,z0,z1,z2,z268,z103])],[(0,[z0,z1,z2,z4,z5,z910]),(0,[z0,z2,z4,z5,z911,z6]),(0,[z0,z2,z4,z912,z5,z6])],[(0,[z0,z1,z2,z268,z5,z6]),(0,[z399,z1,z2,z268,z5,z6])],[(0,[z0,z1,z2,z4,z5,z913]),(0,[z0,z1,z2,z4,z6,z914]),(0,[z97,z111,z0,z1,z2,z6]),(0,[z915,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z916]),(0,[z0,z1,z2,z917,z5,z6]),(0,[z225,z0,z1,z2,z96,z11])]],
   [[(0,[z0,z1,z2,z4,z5,z918]),(0,[z0,z1,z2,z919,z5,z6]),(0,[z1,z2,z4,z783,z5,z6]),(0,[z102,z0,z1,z2,z11,z103])],[(0,[z0,z1,z2,z4,z920,z6]),(0,[z0,z1,z22,z5,z39,z6]),(0,[z428,z1,z2,z5,z6,z11])],[(0,[z126,z0,z1,z5,z6,z11]),(0,[z0,z1,z4,z5,z6,z921]),(0,[z0,z1,z2,z5,z663,z11]),(0,[z0,z1,z2,z4,z5,z922]),(0,[z0,z923,z2,z4,z5,z6]),(0,[z225,z0,z1,z2,z5,z11]),(0,[z102,z399,z1,z2,z4,z103])],[(0,[z0,z1,z2,z4,z924,z6]),(0,[z0,z465,z4,z5,z6,z246]),(0,[z0,z1,z2,z4,z925,z6]),(0,[z227,z0,z2,z22,z50,z6]),(0,[z0,z1,z2,z926,z5,z6]),(0,[z102,z0,z1,z215,z5,z11])],[(1,[z0,z831,z4,z5,z6]),(0,[z0,z2,z4,z631,z50,z6]),(0,[z927,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z6,z96,z11])],[(0,[z0,z1,z2,z268,z5,z32])],[(0,[z0,z2,z4,z5,z928,z6]),(0,[z216,z1,z2,z298,z54,z6]),(0,[z0,z1,z2,z407,z24,z5])],[(0,[z0,z1,z929,z4,z5,z6]),(0,[z0,z1,z930,z2,z5,z6]),(0,[z0,z137,z4,z5,z6,z30]),(0,[z97,z0,z1,z2,z83,z6]),(0,[z0,z1,z2,z4,z6,z96]),(0,[z931,z1,z2,z4,z5,z6])]],
   [[(0,[z291,z334,z0,z1,z5,z6]),(0,[z0,z1,z4,z56,z874,z6]),(0,[z0,z1,z2,z932,z6,z11])],[(0,[z0,z1,z2,z4,z933,z6]),(0,[z154,z1,z46,z5,z6,z11]),(0,[z0,z1,z934,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z935]),(0,[z0,z1,z2,z936,z5,z6]),(0,[z0,z1,z2,z4,z5,z723]),(0,[z0,z1,z2,z22,z5,z385]),(0,[z428,z294,z2,z4,z5,z6])],[(0,[z554,z0,z1,z2,z937,z5])],[(0,[z91,z143,z0,z2,z5,z6]),(0,[z49,z0,z58,z5,z6,z11]),(0,[z118,z0,z1,z285,z5,z19]),(0,[z399,z1,z2,z4,z5,z11])],[(0,[z147,z161,z0,z2,z5,z6]),(0,[z0,z1,z2,z5,z563,z11]),(0,[z0,z1,z2,z4,z5,z938]),(0,[z0,z939,z1,z2,z5,z6]),(0,[z0,z1,z2,z23,z6,z96]),(0,[z649,z1,z2,z119,z5,z6])],[(0,[z161,z0,z2,z5,z6,z11]),(0,[z291,z0,z1,z22,z5,z6]),(0,[z0,z1,z224,z4,z56,z6]),(0,[z117,z0,z1,z4,z57,z6]),(0,[z0,z1,z4,z874,z57,z6])],[(0,[z84,z0,z1,z731,z5,z6]),(0,[z0,z1,z443,z5,z6,z290])],[(0,[z7,z1,z2,z4,z5,z616]),(0,[z0,z1,z2,z5,z6,z940])]],
   [[(0,[z0,z941,z2,z4,z5,z6]),(0,[z554,z0,z2,z4,z5,z86]),(0,[z769,z0,z1,z2,z5,z55]),(1,[z0,z2,z4,z727,z6]),(0,[z0,z1,z2,z285,z5,z6]),(0,[z63,z0,z1,z85,z5,z6]),(0,[z0,z1,z2,z5,z790,z6]),(0,[z942,z1,z2,z5,z6,z11]),(0,[z0,z1,z2,z4,z6,z744])],[(0,[z140,z1,z2,z407,z5,z205]),(0,[z0,z1,z2,z4,z820,z6]),(0,[z51,z0,z2,z22,z5,z30])],[(0,[z0,z2,z388,z5,z6,z11]),(0,[z0,z1,z2,z4,z5,z943]),(0,[z0,z465,z2,z129,z5,z6]),(0,[z0,z67,z68,z4,z5,z6]),(0,[z0,z1,z2,z22,z5,z393]),(0,[z0,z1,z944,z4,z5,z6]),(0,[z0,z1,z127,z5,z6,z290]),(0,[z0,z123,z2,z285,z5,z6]),(0,[z0,z1,z2,z146,z5,z6]),(0,[z399,z1,z2,z146,z5,z6])],[(0,[z0,z1,z945,z4,z5,z6]),(0,[z0,z1,z145,z4,z423,z6]),(0,[z0,z42,z2,z10,z6,z11]),(0,[z0,z1,z69,z22,z5,z6]),(0,[z0,z1,z2,z5,z6,z946]),(0,[z0,z1,z2,z4,z790,z6])],[(0,[z0,z2,z4,z5,z947,z6]),(0,[z334,z0,z1,z5,z53,z6]),(0,[z0,z1,z2,z948,z5,z6]),(0,[z0,z1,z2,z4,z744,z103])],[(0,[z0,z949,z2,z4,z5,z6]),(0,[z0,z950,z2,z4,z5,z6]),(0,[z0,z1,z5,z298,z53,z6]),(0,[z51,z0,z2,z504,z5,z30])],[(0,[z0,z1,z951,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z261]),(0,[z952,z0,z1,z2,z5,z6]),(0,[z703,z84,z0,z1,z5,z6]),(0,[z0,z2,z4,z5,z953,z6])],[(0,[z0,z1,z4,z56,z249,z6]),(0,[z102,z0,z1,z172,z5,z11]),(0,[z428,z1,z2,z22,z5,z6])]],
   [[(0,[z126,z0,z1,z22,z5,z6]),(0,[z126,z0,z1,z214,z5,z6]),(0,[z0,z1,z2,z5,z6,z954]),(0,[z0,z67,z534,z4,z5,z6]),(0,[z0,z1,z2,z131,z5,z11]),(0,[z0,z1,z2,z5,z494,z11]),(0,[z0,z955,z2,z4,z5,z6]),(0,[z0,z1,z956,z4,z5,z6]),(0,[z0,z1,z145,z56,z6,z11]),(0,[z0,z1,z2,z23,z790,z6]),(0,[z0,z1,z2,z957,z6,z11])],[(0,[z0,z1,z4,z5,z6,z958]),(0,[z1,z36,z929,z4,z5,z6]),(0,[z35,z1,z36,z5,z6,z11]),(0,[z636,z0,z1,z2,z5,z11]),(0,[z0,z1,z959,z4,z5,z6]),(0,[z0,z465,z2,z5,z8,z11]),(0,[z0,z1,z2,z5,z6,z960]),(0,[z961,z1,z2,z4,z5,z6]),(0,[z839,z1,z2,z4,z5,z6]),(0,[z0,z1,z475,z239,z5,z6])],[(0,[z0,z1,z214,z444,z5,z6]),(0,[z49,z437,z0,z4,z5,z6]),(1,[z1,z2,z4,z860,z6]),(0,[z0,z962,z1,z2,z5,z6]),(0,[z0,z29,z2,z22,z5,z12]),(0,[z0,z1,z2,z5,z6,z171]),(0,[z0,z1,z145,z4,z662,z6])],[(0,[z0,z1,z4,z963,z5,z6]),(0,[z0,z964,z2,z4,z5,z6]),(0,[z0,z965,z2,z4,z5,z6]),(0,[z0,z1,z2,z23,z5,z261]),(0,[z0,z67,z4,z5,z95,z6]),(0,[z0,z1,z2,z4,z966,z6]),(0,[z0,z1,z2,z4,z5,z967]),(0,[z0,z236,z2,z4,z5,z6]),(0,[z0,z42,z2,z22,z10,z6]),(0,[z0,z1,z968,z4,z5,z6]),(0,[z102,z0,z1,z2,z4,z693]),(0,[z0,z1,z2,z21,z790,z6]),(0,[z399,z236,z2,z4,z5,z6])],[(0,[z0,z1,z2,z5,z6,z969]),(0,[z430,z0,z2,z115,z5,z6]),(0,[z0,z1,z2,z970,z5,z6])],[(0,[z212,z0,z1,z2,z5,z261]),(0,[z427,z1,z2,z112,z5,z6]),(0,[z1,z2,z4,z860,z54,z6]),(0,[z0,z1,z971,z4,z5,z6]),(0,[z689,z0,z2,z4,z50,z6]),(0,[z430,z0,z2,z5,z6,z191])],[(0,[z0,z58,z4,z5,z6,z663]),(0,[z0,z252,z2,z285,z5,z6])],[(0,[z124,z241,z2,z4,z5,z6]),(0,[z0,z1,z2,z22,z295,z6]),(0,[z972,z0,z1,z2,z5,z6]),(0,[z204,z161,z0,z4,z5,z6]),(0,[z0,z1,z218,z5,z6,z11]),(0,[z0,z1,z127,z390,z5,z6]),(0,[z0,z973,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z974]),(0,[z975,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z6,z297])]],
   [[(0,[z49,z0,z1,z4,z438,z6]),(0,[z0,z1,z2,z5,z6,z976]),(0,[z0,z1,z2,z5,z616,z11]),(0,[z0,z1,z2,z22,z5,z400]),(0,[z102,z0,z1,z2,z22,z103])],[(0,[z0,z2,z4,z54,z500,z6]),(0,[z554,z0,z1,z2,z977,z5]),(0,[z0,z1,z4,z5,z874,z6]),(0,[z0,z449,z2,z22,z5,z6])],[(0,[z0,z2,z4,z5,z6,z978]),(0,[z0,z1,z2,z5,z353,z11]),(0,[z291,z342,z0,z4,z5,z6]),(0,[z0,z1,z167,z5,z6,z11]),(0,[z979,z1,z2,z4,z5,z6]),(0,[z0,z1,z980,z4,z5,z6]),(0,[z0,z29,z2,z5,z12,z11]),(1,[z0,z1,z4,z874,z6])],[(0,[z232,z0,z2,z4,z5,z6]),(0,[z291,z0,z1,z4,z438,z6]),(0,[z0,z1,z2,z131,z5,z261]),(0,[z0,z1,z4,z54,z39,z6]),(0,[z320,z1,z2,z4,z5,z205]),(0,[z97,z0,z1,z2,z4,z6]),(0,[z97,z0,z1,z2,z6,z96])],[(0,[z0,z42,z4,z10,z39,z6]),(0,[z0,z1,z2,z21,z23,z6]),(0,[z0,z1,z2,z4,z24,z744])],[(0,[z1,z814,z2,z4,z5,z6]),(0,[z140,z1,z2,z22,z5,z205])],[(0,[z981,z0,z1,z2,z5,z6]),(0,[z0,z1,z4,z5,z6,z844]),(0,[z47,z1,z2,z87,z6,z11]),(0,[z0,z2,z4,z719,z5,z6])],[(0,[z161,z111,z0,z2,z5,z6]),(0,[z7,z1,z2,z22,z5,z8]),(0,[z7,z1,z2,z4,z5,z247])]],
   [[(0,[z0,z1,z2,z982,z5,z6]),(0,[z7,z465,z2,z4,z5,z8])],[(0,[z0,z983,z2,z4,z5,z6]),(0,[z0,z1,z2,z23,z187,z6]),(0,[z984,z0,z1,z4,z5,z6]),(0,[z7,z2,z4,z5,z8,z128]),(0,[z0,z1,z985,z4,z5,z6])],[(0,[z0,z2,z22,z5,z86,z6]),(0,[z0,z1,z986,z4,z5,z6]),(0,[z0,z1,z987,z4,z5,z6])],[(0,[z0,z1,z2,z129,z5,z156]),(0,[z425,z0,z2,z4,z5,z30]),(0,[z0,z988,z2,z4,z5,z6])],[(0,[z989,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z990]),(0,[z0,z1,z22,z880,z5,z6])],[(0,[z0,z68,z206,z4,z5,z6]),(0,[z147,z1,z2,z219,z5,z261]),(0,[z0,z1,z2,z4,z5,z991]),(0,[z0,z1,z2,z4,z992,z6])],[(0,[z0,z1,z4,z5,z6,z246]),(0,[z147,z204,z1,z219,z5,z6]),(0,[z993,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z994,z6]),(0,[z0,z1,z5,z6,z246,z48]),(0,[z0,z1,z2,z995,z5,z6]),(1,[z0,z1,z2,z790,z6])],[(0,[z0,z1,z2,z5,z650,z11]),(0,[z342,z0,z2,z4,z50,z6]),(0,[z212,z0,z2,z386,z5,z6]),(0,[z227,z0,z2,z4,z50,z6]),(0,[z0,z996,z2,z4,z5,z6])]],
   [[],[(0,[z0,z1,z2,z4,z5,z997]),(0,[z1,z2,z4,z5,z998,z6])],[(0,[z0,z1,z2,z4,z999,z6]),(0,[z35,z0,z449,z4,z5,z6]),(0,[z0,z1,z2,z937,z5,z6]),(0,[z0,z1,z2,z5,z1000,z6]),(0,[z1,z2,z4,z5,z6,z1001]),(0,[z0,z1,z2,z4,z96,z385]),(0,[z1002,z0,z2,z22,z5,z6])],[(0,[z0,z1,z2,z5,z6,z1003]),(0,[z0,z1,z167,z129,z5,z6]),(0,[z212,z0,z2,z115,z5,z6]),(0,[z0,z1,z2,z5,z6,z732]),(0,[z0,z1,z172,z268,z5,z6])],[(0,[z126,z143,z0,z1,z5,z6]),(0,[z0,z1,z4,z218,z5,z6]),(0,[z0,z2,z4,z5,z6,z1004]),(0,[z0,z2,z22,z5,z6,z128]),(0,[z0,z1,z2,z1005,z5,z6]),(0,[z0,z1,z15,z160,z5,z16])],[(0,[z1006,z0,z1,z2,z5,z6]),(0,[z154,z1,z46,z4,z438,z6]),(0,[z1007,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z1008,z5,z6]),(0,[z49,z0,z4,z5,z647,z6]),(0,[z0,z1,z2,z4,z5,z385]),(0,[z0,z294,z2,z5,z6,z11]),(0,[z428,z1,z172,z4,z5,z6])],[(0,[z0,z1,z2,z1009,z5,z6]),(0,[z0,z1,z2,z1010,z5,z6]),(0,[z0,z1,z2,z4,z5,z1011]),(0,[z0,z1,z1012,z2,z5,z6]),(0,[z0,z1013,z1,z4,z5,z6]),(0,[z0,z1,z5,z6,z11,z1014])],[(0,[z154,z388,z46,z4,z5,z6]),(0,[z0,z1,z2,z5,z6,z1015]),(0,[z0,z1,z2,z1016,z5,z6])]],
   [[(0,[z1017,z0,z2,z4,z5,z6]),(0,[z0,z2,z22,z233,z5,z6]),(0,[z0,z2,z4,z5,z6,z1018]),(0,[z216,z1,z4,z53,z54,z6]),(0,[z458,z1,z2,z4,z54,z6]),(0,[z1,z2,z4,z87,z860,z6]),(0,[z0,z2,z719,z115,z5,z6]),(0,[z0,z1,z4,z5,z1019,z6]),(0,[z0,z1,z127,z40,z5,z6]),(0,[z0,z1,z2,z281,z5,z6]),(0,[z0,z1,z2,z24,z98,z297])],[(0,[z291,z0,z1,z4,z5,z6]),(0,[z1020,z0,z1,z2,z5,z6]),(0,[z554,z342,z0,z2,z4,z5]),(0,[z569,z0,z1,z2,z5,z11]),(0,[z0,z465,z167,z4,z5,z6]),(0,[z0,z2,z5,z6,z11,z1021])],[(0,[z0,z1,z2,z1022,z5,z6]),(0,[z554,z0,z1,z2,z5,z11]),(0,[z0,z29,z2,z4,z5,z517]),(0,[z118,z0,z123,z4,z5,z19]),(0,[z0,z1,z2,z23,z5,z385])],[(0,[z0,z1,z2,z1023,z5,z6]),(0,[z0,z1,z1024,z4,z5,z6]),(0,[z342,z334,z0,z2,z5,z6])],[(0,[z143,z124,z0,z2,z5,z6]),(0,[z0,z1,z2,z719,z5,z6]),(0,[z0,z1,z2,z4,z739,z6]),(0,[z51,z0,z2,z4,z5,z723])],[(0,[z0,z1,z2,z129,z5,z6]),(0,[z0,z1,z2,z677,z5,z11]),(0,[z0,z1,z2,z4,z5,z1025]),(0,[z51,z0,z2,z4,z5,z30]),(1,[z0,z1,z4,z5,z735]),(0,[z1026,z0,z1,z2,z6,z11]),(0,[z102,z0,z1,z2,z4,z744])],[(0,[z0,z1,z2,z1027,z5,z6]),(0,[z1028,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z31,z387,z6])],[(0,[z0,z1,z2,z1029,z5,z6]),(0,[z0,z1,z2,z1030,z5,z6]),(0,[z342,z0,z2,z4,z5,z55]),(0,[z0,z1,z1031,z4,z5,z6]),(0,[z1032,z0,z1,z2,z5,z6]),(0,[z0,z1,z69,z4,z5,z6]),(0,[z0,z2,z5,z6,z11,z1033]),(0,[z1,z2,z5,z6,z11,z1034]),(0,[z1035,z0,z1,z2,z5,z6])]],
   [[(0,[z0,z1,z444,z5,z6,z11]),(1,[z1,z929,z4,z5,z6]),(0,[z154,z379,z1,z4,z5,z6]),(0,[z232,z133,z0,z2,z5,z6]),(0,[z1036,z0,z1,z2,z4,z5]),(0,[z47,z1,z2,z4,z860,z6]),(0,[z0,z1,z2,z711,z5,z6]),(0,[z1,z2,z4,z5,z8,z799]),(0,[z0,z1,z4,z5,z6,z1014]),(0,[z0,z1037,z2,z4,z5,z6]),(0,[z0,z1038,z2,z4,z5,z6])],[(0,[z0,z1,z1039,z4,z5,z6]),(0,[z0,z1,z1040,z4,z5,z6]),(0,[z154,z1,z604,z4,z5,z6]),(0,[z0,z1,z2,z711,z5,z8]),(0,[z883,z0,z1,z2,z4,z6]),(0,[z0,z1,z15,z4,z5,z45]),(0,[z0,z1,z215,z268,z5,z6])],[(0,[z305,z0,z58,z4,z5,z6]),(0,[z0,z29,z2,z201,z5,z12]),(0,[z84,z0,z1,z88,z5,z6])],[(0,[z0,z1,z2,z4,z1041,z6]),(0,[z0,z1,z2,z1042,z5,z6]),(0,[z428,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1043,z5,z6]),(0,[z0,z2,z4,z5,z6,z1021])],[(0,[z126,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z5,z8,z11]),(0,[z0,z465,z2,z5,z6,z11]),(0,[z0,z1,z2,z129,z5,z32]),(0,[z0,z2,z5,z500,z6,z11]),(0,[z1044,z0,z1,z2,z6,z11])],[(0,[z0,z1,z2,z4,z5,z1045]),(0,[z0,z1,z2,z4,z957,z6]),(0,[z1046,z1,z2,z4,z5,z6]),(0,[z212,z0,z2,z719,z5,z6]),(0,[z0,z1,z2,z5,z381,z11]),(0,[z382,z0,z1,z2,z5,z11]),(0,[z0,z1,z2,z1047,z5,z6]),(0,[z0,z1048,z2,z4,z5,z6]),(0,[z97,z0,z1,z2,z6,z211])],[(1,[z814,z2,z4,z5,z6]),(0,[z1049,z0,z1,z2,z5,z6]),(0,[z0,z29,z2,z4,z5,z12]),(0,[z0,z1050,z2,z4,z5,z6]),(0,[z102,z0,z1,z2,z96,z11])],[(0,[z0,z1051,z2,z4,z5,z6]),(0,[z154,z133,z0,z1,z5,z6]),(0,[z0,z1,z2,z1052,z5,z6]),(0,[z0,z1053,z1,z4,z5,z6]),(0,[z0,z42,z2,z4,z10,z6]),(0,[z117,z0,z1,z4,z874,z6]),(0,[z0,z1,z172,z146,z5,z6])]],
   [[(0,[z0,z2,z4,z5,z86,z55]),(0,[z0,z1054,z2,z4,z5,z6])],[(0,[z147,z1,z2,z783,z5,z6]),(0,[z0,z1,z2,z5,z298,z6]),(0,[z7,z1,z167,z4,z5,z8]),(0,[z1055,z1,z2,z4,z5,z6]),(0,[z0,z449,z145,z4,z56,z6]),(0,[z118,z0,z1,z5,z19,z11]),(0,[z0,z1,z2,z22,z5,z32]),(0,[z102,z0,z1,z2,z5,z11])],[(0,[z91,z444,z92,z4,z5,z6]),(0,[z0,z1056,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z295,z6]),(0,[z91,z92,z2,z5,z6,z11]),(0,[z0,z1,z4,z5,z1057,z6]),(0,[z0,z1,z2,z1058,z5,z6]),(0,[z154,z1,z46,z4,z5,z6]),(0,[z0,z1059,z2,z4,z5,z6]),(0,[z97,z0,z1,z2,z21,z6]),(0,[z0,z294,z2,z22,z5,z6])],[(0,[z0,z1,z4,z5,z415,z19]),(0,[z0,z1,z5,z53,z6,z11]),(0,[z0,z1,z2,z1060,z5,z6]),(0,[z0,z1,z2,z1061,z5,z6])],[(0,[z0,z2,z4,z295,z6,z30]),(0,[z91,z814,z2,z4,z5,z6]),(0,[z1062,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z1063,z5,z6]),(0,[z0,z449,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1064,z5,z6]),(0,[z0,z2,z326,z388,z5,z6]),(0,[z0,z2,z4,z5,z1065,z6])],[(0,[z1066,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z994,z6,z11])]],
   [[(0,[z124,z2,z4,z5,z577,z6]),(0,[z154,z0,z449,z4,z5,z6]),(0,[z554,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z317,z5,z6]),(0,[z1067,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z1068,z5,z6]),(0,[z0,z1,z15,z22,z5,z16]),(0,[z0,z236,z172,z4,z5,z6])],[(0,[z0,z1,z2,z1069,z5,z6]),(0,[z554,z1,z2,z4,z5,z205]),(0,[z140,z1,z2,z4,z5,z205]),(0,[z0,z4,z5,z6,z128,z246]),(0,[z0,z2,z129,z5,z6,z128])],[(0,[z1,z2,z929,z4,z5,z6]),(0,[z0,z1,z1070,z4,z5,z6]),(0,[z942,z1,z2,z4,z5,z6]),(0,[z51,z0,z137,z4,z5,z30]),(0,[z0,z1,z2,z5,z45,z11])],[(0,[z154,z133,z1,z46,z5,z6]),(0,[z7,z1,z2,z4,z5,z8])],[(0,[z0,z2,z388,z4,z5,z6]),(0,[z0,z1,z2,z112,z5,z261]),(0,[z0,z1071,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z24,z98])],[(0,[z91,z126,z0,z4,z5,z6]),(0,[z147,z97,z0,z1,z2,z6]),(0,[z0,z1,z2,z4,z5,z1072]),(0,[z0,z1,z2,z62,z5,z11]),(0,[z0,z1,z215,z146,z5,z6])],[(0,[z0,z1,z444,z22,z5,z6]),(0,[z1073,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z932,z6]),(1,[z399,z1,z2,z5,z11]),(0,[z0,z1,z2,z24,z5,z297])],[(0,[z0,z1074,z2,z4,z5,z6]),(0,[z0,z465,z2,z5,z6,z48]),(0,[z0,z1,z2,z4,z1075,z6]),(0,[z1076,z0,z1,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z723])]],
   [[(0,[z0,z68,z2,z4,z295,z6]),(0,[z0,z1,z2,z5,z6,z1077]),(0,[z0,z1,z2,z268,z5,z11])],[(0,[z0,z167,z4,z5,z6,z128]),(0,[z0,z1,z2,z5,z79,z11])],[(0,[z0,z1,z2,z4,z1078,z6]),(0,[z0,z1079,z2,z4,z5,z6]),(0,[z216,z291,z1,z4,z54,z6]),(0,[z1,z2,z5,z205,z310,z11]),(0,[z97,z0,z1,z2,z205,z11]),(0,[z0,z465,z2,z22,z5,z6]),(0,[z0,z1,z2,z1080,z5,z6]),(0,[z1081,z0,z1,z22,z5,z6])],[(0,[z35,z1,z36,z4,z5,z6]),(0,[z0,z2,z233,z5,z6,z11]),(0,[z0,z1,z2,z22,z5,z308]),(0,[z216,z342,z2,z4,z54,z6]),(0,[z1,z2,z5,z8,z205,z11]),(0,[z1082,z1,z2,z4,z5,z6]),(0,[z1083,z0,z1,z4,z5,z6]),(0,[z0,z2,z4,z5,z1084,z6]),(0,[z690,z0,z1,z4,z5,z19]),(0,[z0,z1,z15,z4,z5,z735]),(0,[z0,z1,z2,z22,z5,z693])],[(0,[z0,z1,z2,z4,z1085,z6]),(0,[z0,z1,z1086,z4,z5,z6]),(0,[z0,z1,z2,z5,z6,z1087]),(0,[z0,z29,z137,z4,z5,z6]),(0,[z0,z29,z2,z4,z5,z723]),(0,[z0,z1,z2,z1088,z5,z6]),(0,[z0,z1,z4,z5,z16,z735])],[(0,[z154,z73,z1,z4,z5,z6]),(0,[z0,z1,z2,z326,z5,z6]),(0,[z0,z2,z831,z4,z5,z6]),(0,[z0,z1,z2,z4,z1089,z6]),(0,[z0,z1,z4,z5,z1090,z6]),(0,[z721,z0,z2,z5,z6,z11])],[(0,[z0,z1,z1091,z4,z5,z6]),(0,[z0,z1092,z2,z4,z5,z6]),(0,[z111,z1,z2,z783,z5,z6]),(0,[z1002,z0,z2,z4,z5,z6]),(0,[z102,z428,z1,z2,z4,z103]),(0,[z0,z236,z215,z4,z5,z6])],[(0,[z0,z1093,z2,z4,z5,z6]),(0,[z342,z0,z2,z4,z10,z6]),(0,[z0,z1,z1094,z4,z5,z6]),(0,[z102,z0,z1,z2,z4,z72])]],
   [[(0,[z0,z2,z74,z75,z5,z6]),(0,[z0,z1,z5,z8,z246,z11]),(0,[z0,z2,z4,z5,z727,z6]),(0,[z0,z1,z2,z992,z6,z11])],[(0,[z1095,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z1096]),(0,[z7,z1,z4,z5,z8,z246]),(0,[z0,z1,z475,z40,z5,z6]),(0,[z20,z0,z1,z2,z146,z6]),(0,[z0,z1,z172,z5,z6,z11])],[(0,[z154,z1,z46,z22,z5,z6]),(0,[z0,z1,z2,z4,z6,z1097]),(0,[z0,z2,z4,z5,z723,z30]),(0,[z0,z1,z2,z5,z107,z11])],[(0,[z0,z1,z1098,z4,z5,z6]),(0,[z0,z1,z2,z5,z55,z11]),(0,[z0,z1,z2,z5,z6,z1099]),(0,[z7,z1,z2,z4,z5,z799]),(0,[z97,z0,z1,z2,z8,z11]),(0,[z0,z1,z15,z5,z16,z171]),(0,[z0,z1,z2,z119,z5,z11])],[(0,[z0,z1100,z2,z4,z5,z6]),(0,[z49,z0,z58,z22,z5,z6])],[(0,[z35,z1,z4,z90,z5,z6]),(0,[z0,z1,z137,z317,z5,z6]),(0,[z0,z1,z2,z21,z23,z385])],[(0,[z1,z2,z783,z219,z5,z6]),(0,[z161,z0,z2,z22,z5,z6]),(0,[z291,z0,z4,z5,z86,z6]),(0,[z0,z1,z15,z4,z5,z432])],[(0,[z0,z29,z2,z4,z5,z418]),(0,[z0,z1,z2,z1101,z5,z6]),(0,[z47,z1,z2,z4,z314,z6]),(0,[z1102,z0,z1,z2,z5,z6]),(0,[z118,z0,z252,z4,z5,z19]),(0,[z0,z1,z2,z5,z6,z1103])]],
   [[(0,[z0,z1,z2,z5,z6,z1104]),(0,[z0,z1,z2,z176,z6,z96])],[(0,[z0,z1,z2,z22,z564,z6]),(0,[z91,z143,z92,z2,z5,z6]),(0,[z0,z1,z2,z5,z6,z1105]),(0,[z0,z1,z2,z1106,z5,z6]),(0,[z0,z1,z2,z160,z5,z6]),(0,[z0,z294,z172,z4,z5,z6])],[(0,[z91,z92,z2,z4,z295,z6]),(0,[z0,z1,z2,z438,z6,z11]),(0,[z0,z1,z2,z5,z1107,z6])],[(0,[z0,z2,z388,z22,z5,z6]),(0,[z0,z1,z2,z1108,z5,z6]),(0,[z147,z379,z1,z2,z5,z6]),(0,[z111,z1,z253,z2,z5,z6]),(0,[z1,z2,z4,z5,z6,z799]),(0,[z0,z42,z2,z4,z423,z6]),(0,[z0,z1,z2,z22,z24,z98])],[(0,[z1109,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z1110,z5,z6]),(0,[z204,z0,z1,z5,z6,z11]),(0,[z0,z1,z22,z5,z6,z246]),(0,[z0,z1,z2,z1111,z5,z6]),(0,[z320,z97,z0,z1,z2,z6])],[(0,[z0,z1,z2,z4,z1112,z6]),(0,[z212,z0,z272,z2,z5,z6]),(0,[z0,z1,z831,z4,z5,z6]),(0,[z0,z1,z2,z1113,z5,z6]),(0,[z0,z1,z2,z4,z874,z6])],[(0,[z0,z1,z15,z4,z438,z6]),(0,[z0,z2,z4,z5,z1114,z6]),(0,[z0,z1,z1115,z4,z5,z6]),(0,[z0,z2,z1116,z4,z5,z6]),(0,[z102,z0,z236,z2,z4,z103])],[(0,[z0,z1,z2,z5,z6,z11]),(0,[z0,z1,z2,z22,z438,z6]),(0,[z35,z1,z929,z4,z5,z6]),(0,[z1117,z0,z1,z2,z4,z5]),(0,[z399,z1,z2,z5,z6,z11])]],
   [[(0,[z91,z126,z92,z4,z5,z6]),(0,[z216,z1,z2,z4,z860,z6]),(0,[z0,z1,z2,z5,z6,z1118])],[(0,[z91,z92,z2,z4,z564,z6]),(0,[z0,z1,z2,z407,z5,z6]),(0,[z0,z1,z2,z1119,z5,z6]),(0,[z97,z0,z1,z2,z22,z6])],[(0,[z35,z1,z36,z22,z5,z6]),(0,[z0,z1,z22,z218,z5,z6])],[(0,[z0,z1,z2,z22,z5,z156]),(0,[z0,z1,z4,z5,z1120,z6]),(0,[z0,z2,z4,z5,z6,z1121]),(0,[z0,z1,z2,z5,z6,z1122]),(0,[z1,z2,z4,z1123,z5,z6]),(0,[z1124,z1,z2,z4,z5,z6]),(0,[z328,z0,z1,z2,z5,z11]),(0,[z357,z97,z0,z1,z2,z11])],[(0,[z0,z2,z4,z5,z12,z723]),(0,[z0,z1125,z2,z4,z5,z6]),(0,[z526,z0,z2,z386,z5,z6])],[(0,[z117,z0,z1,z4,z438,z6]),(0,[z0,z1,z2,z977,z5,z6]),(0,[z1126,z1,z2,z4,z5,z6]),(0,[z399,z1,z2,z4,z5,z32]),(0,[z1127,z0,z1,z4,z5,z6])],[(0,[z554,z0,z1,z4,z5,z53]),(0,[z113,z212,z0,z2,z5,z6]),(0,[z0,z1,z2,z1128,z5,z6]),(0,[z0,z42,z152,z4,z10,z6])],[(0,[z0,z1,z2,z1129,z5,z6]),(0,[z0,z1,z4,z5,z6,z1130]),(0,[z0,z1,z2,z5,z6,z1131]),(0,[z150,z0,z1,z2,z5,z11]),(0,[z1,z2,z5,z54,z205,z11]),(0,[z61,z0,z58,z4,z5,z6]),(0,[z0,z294,z2,z4,z5,z6]),(0,[z399,z294,z2,z4,z5,z6])]],
   [[(0,[z124,z814,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1132]),(0,[z334,z0,z1,z2,z5,z6]),(0,[z0,z1,z1133,z4,z5,z6]),(0,[z0,z1,z167,z5,z6,z48]),(0,[z0,z1,z2,z1134,z5,z6]),(0,[z0,z1,z2,z1135,z5,z6]),(0,[z1136,z1,z2,z4,z5,z6])],[(0,[z0,z1,z4,z56,z438,z6]),(0,[z0,z1,z2,z5,z179,z11]),(0,[z0,z1,z2,z4,z727,z6]),(0,[z63,z0,z1,z5,z6,z545]),(0,[z102,z399,z1,z2,z5,z11])],[(0,[z1,z929,z46,z4,z5,z6]),(0,[z0,z2,z4,z1137,z5,z6]),(0,[z0,z1,z2,z4,z5,z1138]),(0,[z0,z2,z4,z5,z6,z1139]),(0,[z0,z1,z2,z22,z5,z121]),(0,[z0,z68,z831,z4,z5,z6]),(0,[z0,z1,z1140,z4,z5,z6]),(0,[z1141,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z1142,z5,z6])],[(0,[z91,z397,z2,z4,z5,z6]),(0,[z342,z0,z2,z5,z298,z6]),(0,[z0,z1,z167,z22,z5,z6]),(0,[z0,z1143,z2,z4,z5,z6]),(0,[z0,z1,z2,z6,z11,z1097])],[(0,[z49,z0,z174,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z1144]),(0,[z0,z1,z15,z4,z5,z16]),(0,[z320,z1,z2,z5,z6,z166]),(0,[z0,z1,z2,z96,z385,z11]),(0,[z102,z0,z294,z2,z4,z103])],[(0,[z0,z1,z2,z4,z1145,z6]),(0,[z227,z0,z2,z4,z295,z6]),(0,[z0,z1,z2,z5,z6,z1146]),(0,[z0,z1,z2,z1147,z5,z6]),(0,[z0,z252,z2,z5,z6,z11]),(0,[z0,z1,z2,z5,z196,z11]),(0,[z793,z0,z1,z5,z6,z11])],[(0,[z0,z1,z2,z1148,z5,z6]),(0,[z0,z1,z4,z5,z6,z1149]),(0,[z0,z114,z540,z2,z5,z6]),(0,[z0,z2,z4,z5,z500,z6]),(0,[z0,z2,z22,z912,z5,z6])],[(0,[z1150,z0,z2,z4,z5,z6]),(0,[z0,z1,z127,z2,z5,z261]),(0,[z111,z1,z2,z460,z5,z6]),(0,[z216,z554,z1,z2,z4,z54]),(0,[z1151,z1,z2,z4,z5,z6]),(0,[z102,z20,z0,z1,z2,z11])]],
   [[(0,[z0,z1,z2,z5,z208,z11]),(0,[z0,z1,z2,z387,z5,z11])],[(0,[z0,z1,z2,z407,z5,z205]),(0,[z0,z114,z2,z719,z5,z6]),(0,[z0,z1,z145,z22,z56,z6]),(0,[z0,z1152,z2,z4,z5,z6]),(0,[z102,z0,z1,z2,z24,z11]),(0,[z0,z1,z2,z5,z32,z732]),(0,[z102,z0,z1,z2,z146,z103])],[(0,[z0,z1,z444,z4,z5,z6]),(0,[z154,z706,z1,z4,z5,z6]),(0,[z0,z1,z2,z5,z6,z48]),(0,[z0,z1,z1153,z4,z5,z6])],[(0,[z0,z2,z4,z5,z6,z1154]),(0,[z0,z1,z2,z1155,z5,z6]),(1,[z0,z1,z731,z5,z6]),(0,[z0,z449,z4,z5,z57,z6]),(0,[z0,z1,z2,z22,z5,z260])],[(0,[z0,z1,z2,z5,z484,z11]),(0,[z0,z1,z2,z1156,z5,z6]),(0,[z0,z1,z2,z5,z156,z11]),(0,[z0,z1157,z2,z4,z5,z6]),(0,[z0,z1,z137,z5,z6,z11])],[(0,[z0,z1,z2,z22,z5,z6]),(0,[z0,z1,z2,z4,z1158,z6]),(0,[z0,z1,z2,z1159,z5,z6]),(0,[z0,z1,z2,z22,z5,z153]),(0,[z0,z1,z4,z731,z5,z6]),(0,[z399,z1,z2,z22,z5,z6])],[(0,[z0,z1,z2,z4,z1160,z6]),(0,[z0,z465,z2,z4,z5,z6]),(0,[z0,z2,z1161,z4,z5,z6]),(0,[z0,z1,z2,z5,z596,z11]),(0,[z102,z0,z1,z2,z4,z385]),(0,[z1081,z0,z1,z4,z5,z6]),(0,[z428,z1,z215,z4,z5,z6])],[(0,[z0,z1,z2,z1162,z5,z6]),(0,[z0,z1,z2,z230,z5,z11]),(0,[z0,z1,z2,z22,z5,z648])]],
   [[(0,[z0,z1,z2,z1163,z5,z6]),(0,[z0,z1,z2,z5,z507,z11]),(0,[z0,z1,z15,z4,z5,z481]),(0,[z0,z1,z2,z5,z6,z1164]),(0,[z334,z0,z2,z5,z86,z6]),(0,[z51,z0,z69,z4,z5,z30]),(0,[z117,z0,z1,z57,z6,z11]),(0,[z0,z1,z2,z4,z5,z735]),(0,[z97,z0,z1,z2,z22,z11])],[(0,[z0,z1,z129,z5,z6,z246]),(0,[z0,z1,z2,z1165,z5,z6]),(0,[z0,z1,z2,z504,z5,z6])],[(0,[z0,z67,z831,z4,z5,z6]),(0,[z0,z1166,z1,z4,z5,z6]),(0,[z0,z1,z1167,z4,z5,z6])],[(0,[z1168,z0,z1,z4,z5,z6]),(0,[z0,z2,z4,z5,z477,z30]),(0,[z0,z1,z2,z4,z98,z744])],[(0,[z232,z0,z2,z326,z5,z6]),(0,[z0,z1169,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1033]),(0,[z111,z1,z2,z5,z687,z6]),(0,[z0,z1,z1170,z4,z5,z6]),(0,[z0,z1,z2,z8,z96,z11]),(0,[z1,z2,z4,z5,z6,z1034]),(0,[z0,z1,z2,z1171,z5,z6]),(0,[z102,z0,z1,z215,z4,z103])],[(0,[z0,z1,z1172,z4,z5,z6]),(0,[z154,z1,z929,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1173]),(0,[z0,z2,z4,z1174,z5,z6]),(0,[z0,z1,z2,z1175,z5,z6])],[(0,[z124,z2,z4,z5,z6,z28]),(0,[z216,z2,z4,z86,z54,z6]),(0,[z554,z7,z1,z2,z4,z5]),(0,[z0,z831,z58,z4,z5,z6]),(0,[z0,z1,z1176,z4,z5,z6]),(0,[z0,z1,z2,z22,z5,z273]),(0,[z0,z1,z2,z5,z247,z11]),(0,[z97,z0,z1,z2,z6,z11])],[(0,[z0,z1,z2,z4,z1177,z6]),(0,[z133,z0,z2,z388,z5,z6]),(0,[z1026,z0,z1,z2,z4,z6]),(0,[z0,z1,z1178,z4,z5,z6]),(0,[z0,z193,z2,z5,z6,z332])]],
   [[(0,[z814,z92,z2,z4,z5,z6]),(0,[z49,z0,z58,z4,z5,z6]),(0,[z135,z0,z58,z4,z5,z6]),(0,[z0,z1179,z2,z4,z5,z6]),(0,[z0,z1,z2,z1180,z5,z6]),(0,[z428,z1,z2,z268,z5,z6])],[(0,[z84,z0,z1,z158,z5,z6]),(0,[z334,z0,z1,z2,z5,z55]),(0,[z7,z399,z1,z2,z4,z5]),(0,[z0,z1,z2,z5,z566,z11])],[(0,[z161,z0,z2,z4,z5,z6]),(0,[z111,z1,z2,z112,z5,z6]),(0,[z0,z1,z2,z5,z543,z11]),(0,[z0,z252,z15,z4,z5,z6])],[(0,[z0,z67,z1,z4,z438,z6]),(0,[z154,z1,z46,z4,z228,z6]),(0,[z0,z1,z2,z5,z257,z11]),(0,[z0,z42,z2,z4,z727,z6]),(0,[z0,z1,z4,z5,z1181,z6]),(0,[z0,z252,z2,z22,z5,z6]),(0,[z0,z1,z2,z5,z260,z11]),(0,[z0,z1,z2,z24,z98,z11])],[(0,[z0,z1,z2,z1182,z5,z6]),(0,[z0,z29,z2,z5,z12,z13])],[(0,[z0,z1,z2,z4,z564,z6]),(0,[z0,z1,z4,z5,z1183,z6]),(0,[z291,z0,z1,z4,z5,z55]),(0,[z0,z1,z2,z265,z5,z11]),(0,[z140,z1,z2,z4,z5,z799]),(0,[z1184,z0,z1,z2,z5,z6]),(0,[z0,z2,z5,z6,z128,z11]),(0,[z0,z1,z2,z1185,z5,z6]),(0,[z0,z1,z2,z1186,z5,z6]),(0,[z0,z1187,z2,z4,z5,z6]),(0,[z0,z1,z2,z6,z11,z1144])],[(0,[z1044,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z1188]),(0,[z20,z0,z1,z2,z83,z6])],[(0,[z91,z214,z92,z2,z5,z6]),(0,[z0,z1,z1189,z4,z5,z6]),(0,[z147,z1,z2,z119,z5,z6]),(0,[z0,z1,z2,z4,z6,z892]),(0,[z0,z2,z5,z298,z86,z6]),(0,[z0,z1,z2,z129,z5,z11])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 521).take 523) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1044).take 198) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1242)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [521, 523, 198] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 113).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 207).take 49).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [113, 94, 49] = true :=
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

end PEqualNP.Outside.L_meta_38463

theorem PEqualNP.Outside.L_meta_38463 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 3940606144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 3940606144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38463.solve