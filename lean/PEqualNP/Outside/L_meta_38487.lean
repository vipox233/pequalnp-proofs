import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38487

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
  Nat.testBit (4008372960 * 2 ^ 32 + 4006144192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x81005617190e31bc#64 ++ 0xfb44fe7f3b1e73fc#64 : BitVec 128),
   (0xc01930b14060d455#64 ++ 0xffbb31b1c4e3fc7f#64 : BitVec 128),
   (0x00c2c140af030a8a#64 ++ 0xb9c3c1c1ff038f8f#64 : BitVec 128),
   (0x02ec01ea06b40f60#64 ++ 0x7ffc01fe07fc0ff0#64 : BitVec 128),
   (0x04f7ea0007dbe000#64 ++ 0xf6fffe0007fff000#64 : BitVec 128),
   (0x08ffbdfdf0000000#64 ++ 0xecfffffff8000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [11, 9]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x00c2c140af030a8a 0xb9c3c1c1ff038f8f

def z1 : W := mkw 0x02ec01ea06b40f60 0x7ffc01fe07fc0ff0

def z2 : W := mkw 0x04f7ea0007dbe000 0xf6fffe0007fff000

def z3 : W := mkw 0x08ffbdfdf0000000 0xecfffffff8000000

def z4 : W := mkw 0x81005617190e31bc 0xfb44fe7f3b1e73fc

def z5 : W := mkw 0x830042020fbe3ffc 0x1300000007fe7ffc

def z6 : W := mkw 0xc01930b14060d455 0xffbb31b1c4e3fc7f

def z7 : W := mkw 0x00f7bc1510000000 0xecfffe7f38000000

def z8 : W := mkw 0x00c28140a6010a02 0xa8c3c1c1fc018c03

def z9 : W := mkw 0x000040000f030a8a 0xb9830181c7038f8f

def z10 : W := mkw 0x08e68d4cb0000000 0x0044ce4e38000000

def z11 : W := mkw 0x89ffbffff00c3134 0xeefffffff81c7070

def z12 : W := mkw 0xc0d3f151ef43da9f 0xb9c3f1c1ff03ff8f

def z13 : W := mkw 0x04e6ca00079b2000 0xf244fe00031e7000

def z14 : W := mkw 0x81001617100c3134 0x42043e3e001c7070

def z15 : W := mkw 0x08ffbdfdf0200440 0xfffffffffce00c70

def z16 : W := mkw 0x04f7aa0000d8e000 0xe6fffe0000fc7000

def z17 : W := mkw 0x00c2c140af030a8a 0x0040c0403b000380

def z18 : W := mkw 0xc01930b14060d455 0x4638303000e07070

def z19 : W := mkw 0x00004200010a2000 0xf244fe00031e7000

def z20 : W := mkw 0x00c2c340af0b2a8a 0xfbc7ffc1ff1fff8f

def z21 : W := mkw 0x81004202090e31bc 0x13000000031e73fc

def z22 : W := mkw 0xc0c2c140af63dedf 0xbbc3c1c1ffe3ffff

def z23 : W := mkw 0x810042020f0f3bbe 0x13000000071fffff

def z24 : W := mkw 0x81c2d757bf0f3bbe 0xfbc7ffffff1fffff

def z25 : W := mkw 0x00e4000006900000 0x76fc000007fc0000

def z26 : W := mkw 0x08ffbdfdf6900000 0xfefffffffffc0000

def z27 : W := mkw 0x04004200014be000 0x000000000003f000

def z28 : W := mkw 0xc81bbcb5f060d455 0xffbbffb1fce3fc7f

def z29 : W := mkw 0x022c00aa00b40560 0x7fbc01be04fc0c70

def z30 : W := mkw 0x083d3cbd50000000 0xecbf3fbfc0000000

def z31 : W := mkw 0x44ffeaa047fbe441 0xf6ffff80c7fffc03

def z32 : W := mkw 0x00c0014006000a00 0x0040004003000380

def z33 : W := mkw 0x0000400009020088 0x110000000302038c

def z34 : W := mkw 0x04f7a80006d1c000 0x76ff000007fd8000

def z35 : W := mkw 0x0002c000a903008a 0x8003c001f803800f

def z36 : W := mkw 0x04f52a0006d8e000 0x76fc3e0007fc7000

def z37 : W := mkw 0x04f7a80006d1c000 0x04bb000004e18000

def z38 : W := mkw 0x04f7eb40afdbea8a 0xffffffc1ffffff8f

def z39 : W := mkw 0x8102d615b90b309e 0x8003fe01f803f00f

def z40 : W := mkw 0xc01934b55060d455 0xfffffffffce3fc7f

def z41 : W := mkw 0x0000141510000000 0xe844fe7f38000000

def z42 : W := mkw 0x00c0014006000a00 0x39c001c007000f80

def z43 : W := mkw 0x04352a0000d8e000 0x463c3e0000fc7000

def z44 : W := mkw 0x08ffa9e8e6010a02 0x04bb0180c4018c03

def z45 : W := mkw 0x00ec15fd10000000 0xecfcffff38000000

def z46 : W := mkw 0x83ec57ff1fbe3ffc 0xfffcffff3ffe7ffc

def z47 : W := mkw 0xc4f7fa1147dbf015 0xf6fffe01c7fff00f

def z48 : W := mkw 0x00c2d555bf030a8a 0xf9c7ffffff038f8f

def z49 : W := mkw 0x48ffa9e8e060c441 0x04bb0180c4e18c03

def z50 : W := mkw 0x000040000903008a 0x000000000003800f

def z51 : W := mkw 0x040042000fdbea8a 0x1300000007ffff8f

def z52 : W := mkw 0x00c28140a0000000 0x0040c04038000000

def z53 : W := mkw 0x0400420007dbe000 0x1200000007fff000

def z54 : W := mkw 0x0cfffffdf7dbe000 0xfefffffffffff000

def z55 : W := mkw 0xc8ffbdfdf060d455 0xfffffffffce3fc7f

def z56 : W := mkw 0x02ec01ea06940b20 0x6cfc01fe031c0380

def z57 : W := mkw 0x0002c140a9030a8a 0x8903c1c1f8038f8f

def z58 : W := mkw 0x01004606190e21a8 0x7b44ce7e3b1c03f0

def z59 : W := mkw 0x080815fdf0000000 0x080001fff8000000

def z60 : W := mkw 0x81000002080411bc 0x01000000000003fc

def z61 : W := mkw 0x0413ea00014be000 0x8003fe000003f000

def z62 : W := mkw 0x8000000000001014 0x130000000002707c

def z63 : W := mkw 0x00c2c140a7030a02 0xb0c3c180c7038c03

def z64 : W := mkw 0x06ffebea07ffef60 0xfffffffe07fffff0

def z65 : W := mkw 0x00e44200079a2000 0xf6fcfe0007fe7000

def z66 : W := mkw 0x02ec01ea06b40f60 0x0db801fe04e00ff0

def z67 : W := mkw 0x04f7eb40a7dbea02 0xf6ffff80c7fffc03

def z68 : W := mkw 0xc23d30bb40f4d575 0x463c303e00fc7070

def z69 : W := mkw 0x02e4014a06940b20 0x0044004e031c0380

def z70 : W := mkw 0x0c13fe15f14be000 0x8003fe01f803f000

def z71 : W := mkw 0x0800054cb0000000 0x0000004e38000000

def z72 : W := mkw 0x0000400009020088 0xb940c0413b02038c

def z73 : W := mkw 0x083d3cbd50000000 0x443c3e3e00000000

def z74 : W := mkw 0x81005617190e31bc 0x4244fe7e3b1c73f0

def z75 : W := mkw 0xc21931fb4064df75 0xffbb31ffc4e3ffff

def z76 : W := mkw 0xc01972b1416af455 0xffffffb1c7fffc7f

def z77 : W := mkw 0xc400420007fbf455 0x1300000007fffc7f

def z78 : W := mkw 0x85357e1719def1bc 0xff7cfe7f3bfe73fc

def z79 : W := mkw 0x04f7ea000fdbe088 0xfffffe413ffff38c

def z80 : W := mkw 0x00ec01e800000000 0x6cfc01fe00000000

def z81 : W := mkw 0x0200000206b40f60 0x1300000007fc0ff0

def z82 : W := mkw 0x08ffbdfff0040120 0xfffffffffb1c03f0

def z83 : W := mkw 0xc10814b7582415fd 0x090001fff8000fff

def z84 : W := mkw 0xc00810b140201455 0x090001b1c0000c7f

def z85 : W := mkw 0x02c0014206b40f60 0x3bc001c007fc0ff0

def z86 : W := mkw 0x0035280000000000 0x443c3e0000000000

def z87 : W := mkw 0x04240a0000982000 0x00040e00001c0000

def z88 : W := mkw 0x00c28140a0000000 0xa8c3c1c1f8000000

def z89 : W := mkw 0x0affbdfff6b40f60 0xfffffffffffc0ff0

def z90 : W := mkw 0x022c00aa00b40560 0x463c003e00fc0070

def z91 : W := mkw 0x04f7ea0007dbe000 0xffffff81c7fffc0f

def z92 : W := mkw 0x000800a000200440 0x7fb801b004e00c70

def z93 : W := mkw 0xc2fd31fb46f4df75 0xffff31ffc7ffffff

def z94 : W := mkw 0x81c2c342af0f3bbe 0xbbc3c1c1ff1fffff

def z95 : W := mkw 0x001120000040c000 0xf6bb300004e3f000

def z96 : W := mkw 0xc0dbf1f1ef63dedf 0xfffbf1f1ffe3ffff

def z97 : W := mkw 0xc11976b7596ef5fd 0xffffffffffffffff

def z98 : W := mkw 0x08e6cd4cbf030a8a 0xb9c7cfcfff038f8f

def z99 : W := mkw 0x8000101100001014 0xfb0030310002707c

def z100 : W := mkw 0x88ffbdfdf0001014 0xfffffffff802707c

def z101 : W := mkw 0x00000140a8000a8a 0xb98301c1fc038f8f

def z102 : W := mkw 0xc11936b7506cf575 0x463c3e3e00fc7070

def z103 : W := mkw 0x81005615190a309c 0x8000fe013802700c

def z104 : W := mkw 0x0413ea00014be000 0xf247fe00031ff000

def z105 : W := mkw 0xccfffffdf7fbf455 0xfffffffffffffc7f

def z106 : W := mkw 0x00004140af030a8a 0x190001c1ff038f8f

def z107 : W := mkw 0x020801ea00240f60 0x090001fe00000ff0

def z108 : W := mkw 0x080815fdf0000000 0xe844fffff8000000

def z109 : W := mkw 0x02ee81e8a6b10e42 0x04bb0180c4e18c03

def z110 : W := mkw 0xc8fffdfdff63dedf 0xffffffffffe3ffff

def z111 : W := mkw 0x02ec41ea0fb60fe8 0xfffcc1ff3ffe0ffc

def z112 : W := mkw 0x89fffffdf90a309c 0xecfffffff802700c

def z113 : W := mkw 0x40dbe1e0ef63cecb 0xbdfbc1c1ffe38f8f

def z114 : W := mkw 0x00eec1e8af030a8a 0xfdffc1ffff038f8f

def z115 : W := mkw 0xc2fd31f946f0de55 0xffbb31b1c4e3fc7f

def z116 : W := mkw 0x020801ea00240f60 0x7b4401fe031c0ff0

def z117 : W := mkw 0x0000000200040120 0x7b44007e031c03f0

def z118 : W := mkw 0x001930b140000000 0xecbb31b1c0000000

def z119 : W := mkw 0xc00000000060d455 0x1300000004e3fc7f

def z120 : W := mkw 0x00d3e140af43ca8a 0xfffbf1c1ffe3ff8f

def z121 : W := mkw 0x02e6c14aaf970baa 0x0044c04e3b1c0380

def z122 : W := mkw 0x01004606190e21a8 0x0044ce4e3b1c0380

def z123 : W := mkw 0xc00810b140201455 0x0000003000000070

def z124 : W := mkw 0x00c28140a6010a02 0x00830180c4018c03

def z125 : W := mkw 0x000040000f030a8a 0x1100000007038f8f

def z126 : W := mkw 0x0000000000000000 0xb9830181c4038c0f

def z127 : W := mkw 0x08ffbdfdf0000000 0x447cfe7e38000000

def z128 : W := mkw 0xc8ffbdfdf060d455 0xeefffffff8e07070

def z129 : W := mkw 0x0813bc15f0000000 0xe847fe7ff8000000

def z130 : W := mkw 0x001934b550000000 0xecfffffff8000000

def z131 : W := mkw 0xc5fffeb75ffff5fd 0xffffffffffffffff

def z132 : W := mkw 0xc00010110060d455 0xfb00303104e3fc7f

def z133 : W := mkw 0x81001417180411bc 0x7b44007f3b1c03fc

def z134 : W := mkw 0xc01920a04060d455 0x17bb0180c4e3fc7f

def z135 : W := mkw 0x0813bc15f0000000 0x8003fe01f8000000

def z136 : W := mkw 0xcaffbdfff6f4df75 0xffffffffffffffff

def z137 : W := mkw 0x810056171f0f3bbe 0xfb44fe7f3f1fffff

def z138 : W := mkw 0x81c2d757bf0f3bbe 0xfb44fe7f3b1e73fc

def z139 : W := mkw 0xc2fd31fb46f4df75 0x7ffc31fe07fc7ff0

def z140 : W := mkw 0x00f7a80000000000 0xe4fffe0000000000

def z141 : W := mkw 0x04e6ca00079b2000 0x0044ce00031c0000

def z142 : W := mkw 0x81005617190e31bc 0xc204fe3f381e707c

def z143 : W := mkw 0x8000101100001014 0xfb8331b1c403fc7f

def z144 : W := mkw 0x00004200010a2000 0x12000000031e7000

def z145 : W := mkw 0xc41972b147fbf455 0xffbb31b1c7fffc7f

def z146 : W := mkw 0x04f7ea0007dbe000 0x16bb000007fff000

def z147 : W := mkw 0xc43d3ab140f8f455 0xffbf3fb1c4fffc7f

def z148 : W := mkw 0x06fd2bea06fcef60 0x7ffc3ffe07fc7ff0

def z149 : W := mkw 0x0000000000000000 0x80030001c003800f

def z150 : W := mkw 0x08fffdfdff030a8a 0xfdffffffff038f8f

def z151 : W := mkw 0x00c801e006200e40 0x7ff801f007e00ff0

def z152 : W := mkw 0x401920a04060c441 0x04bb0180c4e18c03

def z153 : W := mkw 0x020800aa00240560 0x0000003e00000070

def z154 : W := mkw 0x04f7aa0006d9e000 0x46bf3e0004fdf000

def z155 : W := mkw 0xc11976b5596af4dd 0xffbbffb1fce3fc7f

def z156 : W := mkw 0x06f7eb4a07dfeb20 0xf6fffe4e07fff380

def z157 : W := mkw 0xc0dbb1f1e661de57 0xffbb31b1c4e3fc7f

def z158 : W := mkw 0xc83d3cbd5060d455 0x463c3e3e00e07070

def z159 : W := mkw 0x081bbcb5f0000000 0xecbbffb1f8000000

def z160 : W := mkw 0x06ffeaaa07ffe560 0xf6fffe3e07fff070

def z161 : W := mkw 0x0000000000000000 0x1100000004038c0f

def z162 : W := mkw 0x08ee8decb0000000 0x6cfccffe38000000

def z163 : W := mkw 0x85f7fe171fdff1bc 0xfffffe7f3ffff3fc

def z164 : W := mkw 0x0000101100000000 0xe800303100000000

def z165 : W := mkw 0x00000140a0000a02 0x00000180c0000c03

def z166 : W := mkw 0x00c0014206040b20 0x7bc401fe071c0ff0

def z167 : W := mkw 0x89fffffff90e31bc 0xfffffffffb1e73fc

def z168 : W := mkw 0x020040020fb70fea 0x1300000007ff8fff

def z169 : W := mkw 0x02ec01e806b00e40 0x04b8018004e00c00

def z170 : W := mkw 0x81005213090e31bc 0xfb003031031e73fc

def z171 : W := mkw 0x04352a0000d8e000 0xf6bf3e0004fff000

def z172 : W := mkw 0x08113c1550000000 0x00003e0000000000

def z173 : W := mkw 0x04f7eb40afdbea8a 0xf6fffe403ffff380

def z174 : W := mkw 0x000800a000200440 0x090001b000000c70

def z175 : W := mkw 0x02ec01e806b00e40 0x76fc018007fc0c00

def z176 : W := mkw 0x81005615190a309c 0xfb00fe313802707c

def z177 : W := mkw 0x00c29555b0000000 0xe8c7fffff8000000

def z178 : W := mkw 0x81004200090a309c 0x000000000002700c

def z179 : W := mkw 0x00000140a8000a8a 0x090001c1f8000f8f

def z180 : W := mkw 0x08ffbdfdf0000000 0x0cbb01fff8000000

def z181 : W := mkw 0x0002c000a903008a 0xb983c181fc038c0f

def z182 : W := mkw 0x08e69d5db0000000 0xe844fe7f38000000

def z183 : W := mkw 0x00004202010e2120 0xfb44fe7e031e73f0

def z184 : W := mkw 0x000040000f030a8a 0xb940c0413f038f8f

def z185 : W := mkw 0x0200000200b40560 0x0200000000fc0070

def z186 : W := mkw 0x0cffa9e8e6d1c000 0x04bb0180c4e18000

def z187 : W := mkw 0x04f7ea0007dbe000 0x04ffce0007fd8000

def z188 : W := mkw 0x09fffffff90e21a8 0xecfffffffb1c0380

def z189 : W := mkw 0x08ffbdfdf6010a02 0xecfffffffc018c03

def z190 : W := mkw 0x04356a0007dbe000 0x563c3e0007fff000

def z191 : W := mkw 0xc11976b7596ef5fd 0xff7cfe7f3bfe73fc

def z192 : W := mkw 0x81001617100c3134 0xea44fe7f381c7070

def z193 : W := mkw 0x02e6c14aaf970baa 0xb9c7c1cfff1f8f8f

def z194 : W := mkw 0x09e6cf4eb90e21a8 0x0044ce4e3b1c0380

def z195 : W := mkw 0xc4fffbf1effbfedf 0xfffffff1ffffffff

def z196 : W := mkw 0x00c28140ae010a8a 0x098301c1fc018f8f

def z197 : W := mkw 0x0cffbdfdf6d1c000 0xecfffffffce18000

def z198 : W := mkw 0xc4fffab147fbf455 0xffffffb1c7fffc7f

def z199 : W := mkw 0xc813bc15f040d015 0x8003fe01f803f00f

def z200 : W := mkw 0x08ffe9e8ef030a8a 0xbdfbc1c1ff038f8f

def z201 : W := mkw 0x801930b140001014 0xffbb31b1c002707c

def z202 : W := mkw 0x00c0014006000a00 0x0080018004000c00

def z203 : W := mkw 0x0000000000200440 0x1300000004e00c70

def z204 : W := mkw 0x04e6cb40af9b2a8a 0xb9c7cfc1ff1f8f8f

def z205 : W := mkw 0xc2ec11fb46b41f75 0x7ffc01ffc7fc0fff

def z206 : W := mkw 0x02eec1eaafb70fea 0xffffc1ffffff8fff

def z207 : W := mkw 0x832c56bf19be35fc 0xff7cfe7f3bfe73fc

def z208 : W := mkw 0x000800a000200440 0x4638003000e00070

def z209 : W := mkw 0x00e4000206940120 0x7ffc007e07fc03f0

def z210 : W := mkw 0x00c2c00007030000 0xb9c3c181c7038c0f

def z211 : W := mkw 0xc01930b14060d455 0x7fb831b004e07c70

def z212 : W := mkw 0x8100141710041134 0x0000003e00000070

def z213 : W := mkw 0x80005211010a3014 0xfb44fe31031e707c

def z214 : W := mkw 0x04f7fe1517dbe000 0xfefffe7f3ffff000

def z215 : W := mkw 0xc11936b7506cf575 0xffbf3fbfc4fffc7f

def z216 : W := mkw 0x81000202000c3134 0x02000000001c7070

def z217 : W := mkw 0x04f7eb4007dbea00 0xffffffc007ffff80

def z218 : W := mkw 0x0413ea00a94be08a 0x8003fe01f803f00f

def z219 : W := mkw 0x02ec01ea06b40f60 0x17b8018007fc0ff0

def z220 : W := mkw 0xc00000000040d015 0x000000000003f00f

def z221 : W := mkw 0x0000020000082000 0x42043e00001c7000

def z222 : W := mkw 0x001120000040c000 0x4638300000e07000

def z223 : W := mkw 0x00c2c140af030a8a 0x8043c041fb03838f

def z224 : W := mkw 0x00004200010a2000 0x8000fe0000027000

def z225 : W := mkw 0x020801ea06b40f60 0x1b0001fe07fc0ff0

def z226 : W := mkw 0x080801e8e0000000 0x00000180c0000000

def z227 : W := mkw 0x00c2c140af030a8a 0x11830180c7038f8f

def z228 : W := mkw 0xc01930b14060d455 0xf6bb303004e3f070

def z229 : W := mkw 0x00116200014ae000 0xf6fffe0007fff000

def z230 : W := mkw 0x02ee81eaa6b50f62 0x7fff01fec7fd8ff3

def z231 : W := mkw 0x04356a0001dae000 0xf67cfe0003fe7000

def z232 : W := mkw 0x0400420007dbe000 0xf244fe0007fff000

def z233 : W := mkw 0x0437ea0001dbe000 0xc63ffe0000fff000

def z234 : W := mkw 0x08e68d4cb0000000 0xa8c7cfcff8000000

def z235 : W := mkw 0xc01930b140201455 0xedbb31b1c0000c7f

def z236 : W := mkw 0x89ffffffff0f3bbe 0xffffffffff1fffff

def z237 : W := mkw 0x02ec01ea06b40f60 0xffff01ffc7ff8fff

def z238 : W := mkw 0x0000400007030000 0x1000000007038000

def z239 : W := mkw 0x0813a800e0000000 0x00030000c0000000

def z240 : W := mkw 0xc01130114040d015 0x80033001c003f00f

def z241 : W := mkw 0x00c2c140af030a8a 0x1140c0403f038f8f

def z242 : W := mkw 0x00ffb8b140000000 0xecffffb1c0000000

def z243 : W := mkw 0x04f7ea000fdbea8a 0xf7fffe0007ffff8f

def z244 : W := mkw 0x00e4014006900a00 0x7ffc01c007fc0f80

def z245 : W := mkw 0x01004606190e21a8 0xf244fe4e3b1e7380

def z246 : W := mkw 0x0aee8deeb6b40f60 0x7ffccffe3ffc0ff0

def z247 : W := mkw 0xc01930b14060d455 0x46bb31b0c4e1fc73

def z248 : W := mkw 0x04f7ea0007dbe000 0x8047fe00031ff000

def z249 : W := mkw 0x0000040410000000 0x0044ce4e38000000

def z250 : W := mkw 0x0413ea0007dbe000 0x9203fe0007fff000

def z251 : W := mkw 0x811976b7590e31bc 0xfffffffffb1e73fc

def z252 : W := mkw 0x0a3d3cbf50b40560 0x463c3e3e00fc0070

def z253 : W := mkw 0xc8ffbdfdf0201455 0xedfffffff8000c7f

def z254 : W := mkw 0xc10856b7592e35fd 0xfb44fffffb1e7fff

def z255 : W := mkw 0x0cffbffdf0d8e000 0xeefffffff8fc7000

def z256 : W := mkw 0x08ffadecf0000000 0x04ffcfcef8000000

def z257 : W := mkw 0xc00000000060d455 0x0200000000e07070

def z258 : W := mkw 0x06e6cb4a079f2b20 0x0044ce4e031c0380

def z259 : W := mkw 0x81005617190e31bc 0x8044fe4f3b1e738c

def z260 : W := mkw 0x81005617190e31bc 0x0944ce7f3b1c03fc

def z261 : W := mkw 0x08ffbdfdf6000a00 0xfdffffffff000f80

def z262 : W := mkw 0xc4f7ea0007fbf455 0xf7fffe0007fffc7f

def z263 : W := mkw 0x08f7bc15f0000000 0xe4fffe01f8000000

def z264 : W := mkw 0x0affa9eae6b40f60 0x7fff01fec7fc0ff0

def z265 : W := mkw 0x0a0815fff0240f60 0x090001fff8000ff0

def z266 : W := mkw 0x00ec01e806900000 0x7efc01fe07fc0000

def z267 : W := mkw 0x81001417180411bc 0x0900007f380003fc

def z268 : W := mkw 0x01000606100c2120 0x00040e0e001c0000

def z269 : W := mkw 0x00028000a0010002 0x00030000c0018003

def z270 : W := mkw 0x00004002090601a8 0xfb44c07f3b1e03fc

def z271 : W := mkw 0xc1dbf7f7ff6fffff 0xffffffffffffffff

def z272 : W := mkw 0xc00810b14060d455 0x1b0001b1c4e3fc7f

def z273 : W := mkw 0x02e4014a06b40f60 0x1344004e07fc0ff0

def z274 : W := mkw 0x063d2aaa00fce560 0x463c3e3e00fc7070

def z275 : W := mkw 0x02ec01e806b00e40 0x6cfc01fe04e00c00

def z276 : W := mkw 0x81005615190a309c 0xb940fe413b02738c

def z277 : W := mkw 0x0000000000000000 0x09000181c0000c0f

def z278 : W := mkw 0x0000400009020088 0xb9c3c1c1ff038f8f

def z279 : W := mkw 0x401920a04060c441 0xbdbb0181c4e38c0f

def z280 : W := mkw 0x081bbdfdf0000000 0x8803fffff8000000

def z281 : W := mkw 0x81f7fe17190e31bc 0xfffffe7f3b1e73fc

def z282 : W := mkw 0xc41bfab1416bf455 0xffbbffb1c4e3fc7f

def z283 : W := mkw 0x00e6c00007930000 0xf6ffc00007ff8000

def z284 : W := mkw 0x08e68948a0000000 0x0000000000000000

def z285 : W := mkw 0x00ec01e800200440 0x7ffc01fe04e00c70

def z286 : W := mkw 0x81e456171f9e31bc 0xfffcfe7f3ffe73fc

def z287 : W := mkw 0x00c2c0000f030a8a 0xb1c3c00007038f8f

def z288 : W := mkw 0x0cf7ef4cb7dbe000 0xf6fffe4e3ffff000

def z289 : W := mkw 0x0000541519020088 0xf944fe7f3b02038c

def z290 : W := mkw 0x08fffdfdf9020088 0xfdfffffffb02038c

def z291 : W := mkw 0x48ffbdfdf060c441 0xecfffffffce18c03

def z292 : W := mkw 0x05e6ce061f9f21a8 0x0044ce4e3b1c0380

def z293 : W := mkw 0x001120000040c000 0x04bb000004e18000

def z294 : W := mkw 0x81004606190e31bc 0x1344ce4e3b1e73fc

def z295 : W := mkw 0x00fd31f940000000 0xecff31ffc0000000

def z296 : W := mkw 0x42fd21e846f0ce41 0x04bb0180c4e18c03

def z297 : W := mkw 0x8513fe15194bf09c 0x8003fe013803f00c

def z298 : W := mkw 0x8000141510001014 0xfb44fe7f3802707c

def z299 : W := mkw 0x00e4000006900000 0x00440000031c0000

def z300 : W := mkw 0x04e6ca00079b2000 0xb0c7ce00071f8000

def z301 : W := mkw 0x00f7a8000040c000 0xf6fffe0004e3f000

def z302 : W := mkw 0x00f7a940a0000000 0xecffffc1f8000000

def z303 : W := mkw 0x85353e1710dcf134 0x463c3e3e00fc7070

def z304 : W := mkw 0x00c2800006010000 0x0083000004018000

def z305 : W := mkw 0x0411620007dbe000 0xf6bb300007fff000

def z306 : W := mkw 0x0000400009020088 0x8000c0013802000c

def z307 : W := mkw 0x08fffdfdff030a8a 0xecfffffffb000380

def z308 : W := mkw 0x05f7ee061fdfe1a8 0xf6fffe4e3ffff380

def z309 : W := mkw 0x08ffa9e8e0000000 0x04bb0180c0000000

def z310 : W := mkw 0xc1004202096ef5fd 0x1300000007ffffff

def z311 : W := mkw 0x85e6de171f9f31bc 0xfb44fe7f3b1e73fc

def z312 : W := mkw 0x0000141510000000 0x8000fe0138000000

def z313 : W := mkw 0x04e6ca0007dbe000 0x1244ce0007fff000

def z314 : W := mkw 0x02eec1e8afb30eca 0xbdfbc1c1ffe38f8f

def z315 : W := mkw 0x02ec43ea07be2f60 0xfffcfffe07fe7ff0

def z316 : W := mkw 0xc1117615594af09d 0x8003fe01f803f00f

def z317 : W := mkw 0x0000000200040120 0x13000000031c03f0

def z318 : W := mkw 0x00ec01ea00040120 0x7ffc01fe031c03f0

def z319 : W := mkw 0x02e4014806900a00 0x0000000000000000

def z320 : W := mkw 0x0affbdfff0b40560 0xeefffffff8fc0070

def z321 : W := mkw 0x00f7a80006900000 0xf6fffe0007fc0000

def z322 : W := mkw 0x00ffa9e800000000 0xecfffffe00000000

def z323 : W := mkw 0x04fffab147dbe000 0xfeffffb1c7fff000

def z324 : W := mkw 0xc80815fdf0201455 0x090001fff8000c7f

def z325 : W := mkw 0x04f7eb40a7dbe000 0xfeffffc1fffff000

def z326 : W := mkw 0x00c00140ae000a8a 0x39c001c1ff000f8f

def z327 : W := mkw 0x000800a200240560 0x7ffc01fe07fc0ff0

def z328 : W := mkw 0x81005617190e31bc 0x53043e3e031e73fc

def z329 : W := mkw 0x0000000000000000 0xb90000010002000c

def z330 : W := mkw 0x083d3cbd50000000 0xec7cfe7f38000000

def z331 : W := mkw 0x04f7a80006d1c000 0xe4fffe0004e18000

def z332 : W := mkw 0x0efffffff7ffef60 0xfffffffffffffff0

def z333 : W := mkw 0x0000000200040120 0x0900007e000003f0

def z334 : W := mkw 0x00c2c140af030a8a 0x0940c1c1fb000f8f

def z335 : W := mkw 0x0cffebe8e7dbe000 0xf6ffff80c7fff000

def z336 : W := mkw 0x08ffbdfdf8000a8a 0xedfffffff8000f8f

def z337 : W := mkw 0x00c2c14007030a00 0xb9c3c1c007038f80

def z338 : W := mkw 0x00cac1e0af230eca 0xfffbc1f1ffe38fff

def z339 : W := mkw 0x00005615110a2000 0xfa44fe7f3b1e7000

def z340 : W := mkw 0xc9fffffff96ef5fd 0xffffffffffffffff

def z341 : W := mkw 0x00c2c00007030000 0xb0c3c00007038000

def z342 : W := mkw 0xc3fd77ff5ffefffd 0xffffffffffffffff

def z343 : W := mkw 0x04004200079b2000 0x00000000031c0000

def z344 : W := mkw 0x04112a000048e000 0x00003e0000007000

def z345 : W := mkw 0x0000000008000a8a 0x0100000000000f8f

def z346 : W := mkw 0x04f7ea00afdbe08a 0xf6fffe01fffff00f

def z347 : W := mkw 0xc01930b14060d455 0x5738303004e3fc7f

def z348 : W := mkw 0x85f7fe1717dff134 0xf6fffe3e07fff070

def z349 : W := mkw 0x830056171fbe3ffc 0xfb44fe7f3ffe7ffc

def z350 : W := mkw 0x0c3d3ebd50d8e000 0x463c3e3e00fc7000

def z351 : W := mkw 0x0000141510000000 0x40043e3e00000000

def z352 : W := mkw 0x01004202090e21a8 0x00000000031c0380

def z353 : W := mkw 0x830815ff18241ffc 0x090001ff38000ffc

def z354 : W := mkw 0x81004202090e31bc 0xbb40c0413b1e73fc

def z355 : W := mkw 0xc6fffbfb47ffff75 0xffffffffc7ffffff

def z356 : W := mkw 0x00f7a80000000000 0x04bb000000000000

def z357 : W := mkw 0x03ec47ee1fbe2fe8 0x7ffccffe3ffc0ff0

def z358 : W := mkw 0x00c0014000000000 0x28c001c000000000

def z359 : W := mkw 0x0000141510000000 0x0800007f38000000

def z360 : W := mkw 0x02fd31fb46b40f60 0xffff31ffc7fc0ff0

def z361 : W := mkw 0xc8ffb9f9e060d455 0xffbb31b1c4e3fc7f

def z362 : W := mkw 0x02ec01ea06b40f60 0x467c007e03fc03f0

def z363 : W := mkw 0x0400020000d8e000 0x0200000000fc7000

def z364 : W := mkw 0x04e4420007dbe000 0x76fc000007fff000

def z365 : W := mkw 0xc11972b3496ef5fd 0xffbb31b1c7ffffff

def z366 : W := mkw 0x0024000000900000 0x463c000000fc0000

def z367 : W := mkw 0x08f7bd5df0000000 0x8047fe4ff8000000

def z368 : W := mkw 0x00e6c140af930a8a 0xffffc1c1ffff8f8f

def z369 : W := mkw 0xc000101140001015 0x00000001c000000f

def z370 : W := mkw 0x81001617100c3134 0x7b443e7e031c73f0

def z371 : W := mkw 0x02fd21ea06f4cf60 0xffff31fe07fffff0

def z372 : W := mkw 0x08001415f0000000 0x00000001f8000000

def z373 : W := mkw 0x83e4575f1f9e3bbc 0xfb44fe7f3b1e73fc

def z374 : W := mkw 0x022c00aa00b40560 0x7f7c007e03fc03f0

def z375 : W := mkw 0x850042020fdff1bc 0x1300000007fff3fc

def z376 : W := mkw 0x810014151800109c 0x000000013800000c

def z377 : W := mkw 0x81005617190e31bc 0x1b00007f3b1e73fc

def z378 : W := mkw 0xc00811f1e8201edf 0x090001f1f8000fff

def z379 : W := mkw 0x81001557b8041bbe 0x090001fff8000fff

def z380 : W := mkw 0x06ffa9ea06f5cf60 0x7fff01fe07fd8ff0

def z381 : W := mkw 0x08ffbdfdf0000000 0x84bbff81f8000000

def z382 : W := mkw 0x0000000000000000 0x0000000000000000

def z383 : W := mkw 0x832c16bf10bc3574 0x463c3e3e00fc7070

def z384 : W := mkw 0xc00040000f63dedf 0x1300000007e3ffff

def z385 : W := mkw 0x02c801ea06240f60 0x39c001fe07000ff0

def z386 : W := mkw 0x0000000000000000 0x7b00003000000070

def z387 : W := mkw 0x08ffa9e8e0000000 0xacfbc1c1f8000000

def z388 : W := mkw 0x0ce6cf4cb79b2000 0x0044ce4e3b1c0000

def z389 : W := mkw 0x0000014000000a00 0x090001c000000f80

def z390 : W := mkw 0x08ca95fdf0000000 0xa8c3c1fff8000000

def z391 : W := mkw 0x02c2c142afb70fea 0xbbc3c1c1ffff8fff

def z392 : W := mkw 0x04f7a940a6d1ca02 0x04bb0180c4e18c03

def z393 : W := mkw 0x81004202090e31bc 0xf344fe00031e73fc

def z394 : W := mkw 0x0200014a00040b20 0x0000004e00000380

def z395 : W := mkw 0x000040000f030a8a 0x0000000003000380

def z396 : W := mkw 0x083d3dfdf0000000 0x4c3c3ffff8000000

def z397 : W := mkw 0x0002c000a903008a 0x0000c00038000000

def z398 : W := mkw 0x0cfffffdf14be000 0xecfffffff803f000

def z399 : W := mkw 0xc0cad1f1ef231edf 0xb9c3c1f1ff038fff

def z400 : W := mkw 0xc1117617594ef1bd 0xfb47fe7ffb1ff3ff

def z401 : W := mkw 0xc43d3ab140f8f455 0x463c3e3000fc7070

def z402 : W := mkw 0x08f7ad4cb0000000 0xe4fffe4e38000000

def z403 : W := mkw 0x01c2c746bf0f2baa 0x0044ce4e3b1c0380

def z404 : W := mkw 0x02ee81eaa6b40f60 0xffffc1fffffc0ff0

def z405 : W := mkw 0xc413fa11414bf015 0x8003fe01c003f00f

def z406 : W := mkw 0x00c2c140af030a8a 0x8083c181fc038c0f

def z407 : W := mkw 0xc20811fb40241f75 0x090001ffc0000fff

def z408 : W := mkw 0x00004200010a2000 0x0044ce00031c0000

def z409 : W := mkw 0x02ec01e806b00e40 0x7fb801b004e00c70

def z410 : W := mkw 0x04d3eb40af4bea8a 0xb9c3ffc1ff03ff8f

def z411 : W := mkw 0x8bffffffffbe3ffc 0xfffffffffffe7ffc

def z412 : W := mkw 0x00c0000006000000 0x30c0000007000000

def z413 : W := mkw 0x08240c0c10000000 0x00040e0e00000000

def z414 : W := mkw 0x02ec01ea00b40560 0x6efc01fe00fc0070

def z415 : W := mkw 0xc00810b140201455 0xb98301b1c4038c7f

def z416 : W := mkw 0xc1005617196ef5fd 0xfb44fe7f3fffffff

def z417 : W := mkw 0x02ec15ff16b40f60 0xfffcffff3ffc0ff0

def z418 : W := mkw 0xc01130114040d015 0xb9833181c403fc0f

def z419 : W := mkw 0x00c2c00007030000 0x0040c00003000000

def z420 : W := mkw 0x022c00aa06b40f60 0x573c003e07fc0ff0

def z421 : W := mkw 0x81001417180411bc 0xe944fe7f380003fc

def z422 : W := mkw 0x002c00a800000000 0x443c003e00000000

def z423 : W := mkw 0x06ec43ea07ffef60 0x7ffc01fe07fffff0

def z424 : W := mkw 0x81005617110e3134 0xf244fe3e031e7070

def z425 : W := mkw 0x04c2c340afdbea8a 0xbbc3c1c1ffffff8f

def z426 : W := mkw 0xc01130114040d015 0xf6bb3001c4e3f00f

def z427 : W := mkw 0x8913fe17f90e31bc 0xfb47fe7ffb1e73fc

def z428 : W := mkw 0x00c28140a6010a02 0xb9830181c4038c0f

def z429 : W := mkw 0x0affbdfdf6b00e40 0xecfffffffce00c00

def z430 : W := mkw 0x83ec43ea0fbe3ffc 0x7ffc01fe07fe7ffc

def z431 : W := mkw 0x04ffeaa007fbe440 0xffffffb007fffc70

def z432 : W := mkw 0xc00800a00060d455 0x7fb801b004e3fc7f

def z433 : W := mkw 0x02ec01eaaeb40fea 0x7ffc01fffffc0fff

def z434 : W := mkw 0x00d3e0000743c000 0xf6fbf00007e3f000

def z435 : W := mkw 0x00028000a0000000 0x8003c001f8000000

def z436 : W := mkw 0x81005615190a309c 0xe844fe7f3802700c

def z437 : W := mkw 0x89e6df5fb90e31bc 0xfb44fe7f3b1e73fc

def z438 : W := mkw 0x81005417190611bc 0xb940c07f3b0203fc

def z439 : W := mkw 0x0000000006000a00 0x1100000007000f80

def z440 : W := mkw 0x08ffbdfdf040c000 0xfefffffffce3f000

def z441 : W := mkw 0xc01970b14962d4dd 0xfffbf1f1ffe3ffff

def z442 : W := mkw 0x8000101100001014 0x4200303000007070

def z443 : W := mkw 0xc4fffab147fbf455 0xf6fffe3007fff070

def z444 : W := mkw 0x00c2c140a9020088 0xb9c3c1c1fb02038c

def z445 : W := mkw 0x01c2c746bf0f2baa 0xb9c7cfcfff1f8f8f

def z446 : W := mkw 0x0000000006010a02 0x0000000004018c03

def z447 : W := mkw 0x08ffbdfdf0000000 0xfdfffffffc038c0f

def z448 : W := mkw 0x04f7ea0007dbe000 0x467cfe0003fc7000

def z449 : W := mkw 0x0affa9e8e6b00e40 0x04bb0180c4e00c00

def z450 : W := mkw 0x00f7e940af030a8a 0xfdffffc1ff038f8f

def z451 : W := mkw 0x401930b14060c441 0xecbb31b1c4e18c03

def z452 : W := mkw 0x00c2c200070b2000 0xf2c7fe00071ff000

def z453 : W := mkw 0x00c2c140af030a8a 0xb940c0413b02038c

def z454 : W := mkw 0x0cfffffdf79b2000 0xecfffffffb1c0000

def z455 : W := mkw 0x00004200090a2088 0xfb44fe413b1e738c

def z456 : W := mkw 0x81ec57ff190e31bc 0xfffcffff3b1e73fc

def z457 : W := mkw 0x85f7ff57bfdffbbe 0xffffffffffffffff

def z458 : W := mkw 0x02ec01ea06b40f60 0x094401fe031c0ff0

def z459 : W := mkw 0x08028c04b0000000 0x0000ce0038000000

def z460 : W := mkw 0x0000141710040120 0xfb44fe7f3b1c03f0

def z461 : W := mkw 0x0000400009020088 0x0040c0403b000380

def z462 : W := mkw 0x022c00a800b00440 0x0438000000e00000

def z463 : W := mkw 0x001930b14040c000 0xfebb31b1c4e3f000

def z464 : W := mkw 0x82ec11fb06b41f74 0xfffc31ff07fe7ffc

def z465 : W := mkw 0xc01930b14040d015 0xecbb31b1c003f00f

def z466 : W := mkw 0x00ec00a006b00440 0x7ffc01b007fc0c70

def z467 : W := mkw 0xc00810b140201455 0x7fb801b1c4e00c7f

def z468 : W := mkw 0xc8ffbdfdf040d015 0xecfffffff803f00f

def z469 : W := mkw 0x02e4014a06940b20 0x7b44007e031c03f0

def z470 : W := mkw 0x81c2d757b90e31bc 0xfbc7fffffb1e73fc

def z471 : W := mkw 0x81005617190e31bc 0xfbc7ffffff1fffff

def z472 : W := mkw 0x020801ea00240f60 0x7fb801fe04e00ff0

def z473 : W := mkw 0x04d3ea00074be000 0xb0c3fe000703f000

def z474 : W := mkw 0xc01930b14060d455 0x84bb3181c4e3fc0f

def z475 : W := mkw 0x8913fe15f90a309c 0x8003fe01f802700c

def z476 : W := mkw 0x81005615190a309c 0xf244fe013b1e700c

def z477 : W := mkw 0x0000000000000000 0x3940004003000380

def z478 : W := mkw 0x02ec01ea06b40f60 0x46bc01be04fc0c70

def z479 : W := mkw 0xc01930b34064d575 0xffff31ffc7ffffff

def z480 : W := mkw 0x893d7ebf590e31bc 0xff7cfe7f3b1e73fc

def z481 : W := mkw 0x0200000206940b20 0x00000000031c0380

def z482 : W := mkw 0x02ec01ea06b40f60 0x04fc01ce07fc0f80

def z483 : W := mkw 0x02ec01e806b00e40 0x3df801c007e00f80

def z484 : W := mkw 0xc01930b14060d455 0xeebb31b1c0e07070

def z485 : W := mkw 0x04c2c20007dbe000 0xb2c3c00007fff000

def z486 : W := mkw 0x0402ca00010b2000 0x0000ce0000000000

def z487 : W := mkw 0x08ee9dfdf0000000 0x0844cffff8000000

def z488 : W := mkw 0x00c0014006000a00 0xb9c301c1c7038f8f

def z489 : W := mkw 0x000800a000200440 0x04b8018004e00c00

def z490 : W := mkw 0x00c28140a0000000 0xb9c3c1c1fc038c0f

def z491 : W := mkw 0xc0fd30b146f0d455 0xffff31b1c7fffc7f

def z492 : W := mkw 0x400000000060c441 0x0000000004e18c03

def z493 : W := mkw 0x0200000200240f60 0x0100000000000ff0

def z494 : W := mkw 0x0000000000000000 0xf200300000027000

def z495 : W := mkw 0x0afffdffffb70fea 0xffffffffffff8fff

def z496 : W := mkw 0x081935fdf0000000 0xecbb31fff8000000

def z497 : W := mkw 0x81c2d755bf0b3a9e 0xb9c3ffc1ff03ff8f

def z498 : W := mkw 0xc00810b140201455 0xfb0031b1c0027c7f

def z499 : W := mkw 0x00c2c000af03008a 0xb0c3c001ff03800f

def z500 : W := mkw 0x083fbcbdf0000000 0xc43ffe3ff8000000

def z501 : W := mkw 0x001120000040c000 0xffbb3181c4e3fc0f

def z502 : W := mkw 0x0000000200040120 0x4204003e001c0070

def z503 : W := mkw 0x08ffbdfdf0000000 0x44bf3fbec0000000

def z504 : W := mkw 0x40dba1e0e661ce43 0x04bb0180c4e18c03

def z505 : W := mkw 0x0000000000000000 0x00830180c4018c03

def z506 : W := mkw 0x830857ff192e3ffc 0xfb44ffff3b1e7ffc

def z507 : W := mkw 0x04e6880006910000 0x0000000000000000

def z508 : W := mkw 0x0cfffffdffdbea8a 0xffffffffffffff8f

def z509 : W := mkw 0x02eec1ea07b70f60 0xffffc1fe07ff8ff0

def z510 : W := mkw 0x08cad5fdff030a8a 0xb9c3c1ffff038f8f

def z511 : W := mkw 0x810856b7192e35fc 0xfffcffff3ffe7ffc

def z512 : W := mkw 0x81001417180411bc 0xfb00307f380273fc

def z513 : W := mkw 0x89ffbdfff80411bc 0xedfffffff80003fc

def z514 : W := mkw 0x0cfffebd57dbe000 0xf6fffe3e07fff000

def z515 : W := mkw 0x02cac1eaaf270fea 0xb9c3c1ffff038fff

def z516 : W := mkw 0x00f5200006d0c000 0xf6ff300007fff000

def z517 : W := mkw 0x00c2c140a903008a 0xa8c3c1c1f803800f

def z518 : W := mkw 0xc0fd31f94060d455 0xffff31ffc4e3fc7f

def z519 : W := mkw 0x401920a04060c441 0x7fbb01b0c4e18c73

def z520 : W := mkw 0x06ffa9e806f1ce40 0x04bb018004e18c00

def z521 : W := mkw 0x00c041400f030a8a 0x39c001c007038f8f

def z522 : W := mkw 0xc01130114040d015 0xfb033031c003f07f

def z523 : W := mkw 0x01004606190e21a8 0xb944ce4f3b1e038c

def z524 : W := mkw 0x00e4000000000000 0x64fc000000000000

def z525 : W := mkw 0x06ffebe807fbee40 0xf6ffff8007fffc00

def z526 : W := mkw 0xc0dbf0b14763d455 0xfffbf1b1c7e3fc7f

def z527 : W := mkw 0x04f7ea00014be000 0xe4fffe000003f000

def z528 : W := mkw 0x00c2c142af070baa 0xfbc7c1ffff1f8fff

def z529 : W := mkw 0x0413ea00014be000 0xf6bbfe0004e3f000

def z530 : W := mkw 0x401920a04060c441 0x0438000000e00000

def z531 : W := mkw 0x0000000000000000 0xe044fe0000000000

def z532 : W := mkw 0x85f7fe151fdbf09c 0xf6fffe013ffff00c

def z533 : W := mkw 0x8100161510083014 0x00003e0000007000

def z534 : W := mkw 0x0200000006b00e40 0x0000000004e00c00

def z535 : W := mkw 0x0413a8000041c000 0x0003000000018000

def z536 : W := mkw 0x02ec41ea0fb70fea 0x7ffc01fe07ff8fff

def z537 : W := mkw 0x0ae68d4eb6940b20 0x0044ce4e3b1c0380

def z538 : W := mkw 0x0400000006d1c000 0x0000000004e18000

def z539 : W := mkw 0x020801e800200e40 0x0000018000000c00

def z540 : W := mkw 0xc01130114060d455 0x93033001c4e3fc7f

def z541 : W := mkw 0x8000101300041134 0xfb44307f031e73fc

def z542 : W := mkw 0x0000000000000000 0xa840c04138000000

def z543 : W := mkw 0x001930b140000000 0xfdbb31b1c4038c0f

def z544 : W := mkw 0x00c2c140a7030000 0xb8c3c1c1ff038000

def z545 : W := mkw 0x81117617194ef1bc 0xfffffe7f3ffff3fc

def z546 : W := mkw 0x87ffffff1ffffffc 0xffffffff3ffffffc

def z547 : W := mkw 0x03e4474e1f9e2ba8 0x0044ce4e3b1c0380

def z548 : W := mkw 0x401120004040c001 0x00030000c0018003

def z549 : W := mkw 0x00000000a800008a 0x00000001f800000f

def z550 : W := mkw 0x84f7fa1107dbf014 0xfffffe3107fff07c

def z551 : W := mkw 0x08fd3dfd50000000 0x6cfc3ffe00000000

def z552 : W := mkw 0x0000000000000000 0xb083000004038000

def z553 : W := mkw 0x001920a040000000 0x04bb0180c0000000

def z554 : W := mkw 0x022c01ea00b40f60 0x4f3c01fe00fc0ff0

def z555 : W := mkw 0x04f7a80006d1c000 0xf6bb300004e3f000

def z556 : W := mkw 0xc2ec01ea06f4df75 0x7ffc01fe07ffffff

def z557 : W := mkw 0x00ec01e806000a00 0x7dfc01fe07000f80

def z558 : W := mkw 0x0000000006900000 0x1200000007fc0000

def z559 : W := mkw 0x0cf7fe15f7dbe000 0xf6fffe01fffff000

def z560 : W := mkw 0x00c2c140af030a8a 0x00c3c1c0ff018f83

def z561 : W := mkw 0x08fffdfdf903008a 0xecfffffff803800f

def z562 : W := mkw 0x8513fe17194ff1bc 0xfb47fe7f3b1ff3fc

def z563 : W := mkw 0x000801e800000000 0x080001fe00000000

def z564 : W := mkw 0x06eecbea07bf2f60 0x7ffccffe07fc0ff0

def z565 : W := mkw 0x81c057571f0e3bbc 0xfbc4ffff3f1e7ffc

def z566 : W := mkw 0x81005757b90e3bbe 0xfb44fffffb1e7fff

def z567 : W := mkw 0x08d3fd55ff030a8a 0xb9c3ffc1ff038f8f

def z568 : W := mkw 0x850056171fdff1bc 0xfb44fe7f3ffff3fc

def z569 : W := mkw 0x06ffebeaafffefea 0xffffffffffffffff

def z570 : W := mkw 0xc01930b14060d455 0xff38303100e2707c

def z571 : W := mkw 0x001930b140200440 0xffbb31b1c4e00c70

def z572 : W := mkw 0x0000000000000000 0x6844007e00000000

def z573 : W := mkw 0x02e4014a06940b20 0x76fc004e07fc0380

def z574 : W := mkw 0x020800a206b40f60 0x7fb801b007fc0ff0

def z575 : W := mkw 0x00c28140a6010a02 0x39c301c0c7018f83

def z576 : W := mkw 0x00004140a9020a8a 0xb940c1c1fb020f8f

def z577 : W := mkw 0x0224000a00940120 0x0004000e001c0000

def z578 : W := mkw 0xc01930b14060d455 0x4f3831b1c0e07c7f

def z579 : W := mkw 0x06f7ea0207ffef60 0xf7fffe0007fffff0

def z580 : W := mkw 0x08ffbcbd50000000 0xe4fffe3e00000000

def z581 : W := mkw 0xc01930b14060d455 0x890331b1c003fc7f

def z582 : W := mkw 0x001920a00060c440 0xffbb31b004e3fc70

def z583 : W := mkw 0xc01930b14060d455 0xc63b3031c0e3f07f

def z584 : W := mkw 0xc01bf0b1e963d4df 0xffbbf1b1fce3fc7f

def z585 : W := mkw 0x00000140a0000000 0x080001c1f8000000

def z586 : W := mkw 0x890857fff90e31bc 0xfb44fffffb1e73fc

def z587 : W := mkw 0x080815fdf8000a8a 0x090001fff8000f8f

def z588 : W := mkw 0x81005617190e31bc 0x8900fe7f380273fc

def z589 : W := mkw 0x08ffa9e8e0000000 0x6cff01fec0000000

def z590 : W := mkw 0xc11934b75864d5fd 0xffbb31fffce3ffff

def z591 : W := mkw 0x83eed7ffbfbf3ffe 0xffffffffffffffff

def z592 : W := mkw 0x00e4000006900000 0x04b8000004e00000

def z593 : W := mkw 0x01004604190a2088 0x0000ce0038000000

def z594 : W := mkw 0xc013f011e943d09f 0x8003f001f803f00f

def z595 : W := mkw 0x00c28140a6010a02 0x0000000000000000

def z596 : W := mkw 0x83ec15ff1eb41ffc 0x7ffc01ff3ffc0ffc

def z597 : W := mkw 0x02e4014a06940b20 0x39c401ce071c0f80

def z598 : W := mkw 0x401920a04060c441 0xf6bb3180c4e3fc03

def z599 : W := mkw 0x00e6880000000000 0x0044ce0000000000

def z600 : W := mkw 0x080814bd50000000 0x0000003e00000000

def z601 : W := mkw 0x0000000200040120 0x0044004e031c0380

def z602 : W := mkw 0x04f7e940afd3ca8a 0xbdfbc1c1ffe38f8f

def z603 : W := mkw 0x0afd3dff56b40f60 0x7ffc3ffe07fc0ff0

def z604 : W := mkw 0xc23d30bb40f4d575 0xffbf31bfc4fffc7f

def z605 : W := mkw 0x00f7ea00010a2000 0xf6fffe00031e7000

def z606 : W := mkw 0x0002c000af030a8a 0x9103c001ff038f8f

def z607 : W := mkw 0x0affbdfff6940b20 0xecfffffffb1c0380

def z608 : W := mkw 0x083d28a840000000 0x0438000000000000

def z609 : W := mkw 0x0435280000d0c000 0x0438000000e00000

def z610 : W := mkw 0xc01970b14f63dedf 0xffbb31b1c7e3ffff

def z611 : W := mkw 0xc0dbb1f1e060d455 0xfffbf1f1fce3fc7f

def z612 : W := mkw 0x04f7ea0007dbe000 0x84bbfe0004e3f000

def z613 : W := mkw 0xc4ffb8b146f1d455 0xffbb31b1c4e3fc7f

def z614 : W := mkw 0x02ec00aa06b40560 0x76fc003e07fc0070

def z615 : W := mkw 0x08ffb9f9e0000000 0xecbb31b1c0000000

def z616 : W := mkw 0xc000000000201455 0x0100000000000c7f

def z617 : W := mkw 0x08ec15fdf0000000 0x6cfc01fff8000000

def z618 : W := mkw 0x893d3ebf500c3134 0x463c3e3e001c7070

def z619 : W := mkw 0xc00000000060d455 0xbb830181c4e3fc7f

def z620 : W := mkw 0xc01930b14060d455 0x0dbb01b1c4e18c7f

def z621 : W := mkw 0x00dbb1f1e0000000 0xecfbf1f1f8000000

def z622 : W := mkw 0x0000000000000000 0xa8830181c0000000

def z623 : W := mkw 0x81004202090e31bc 0x7b44007e031e73fc

def z624 : W := mkw 0x8dffffffffdff1bc 0xfffffffffffff3fc

def z625 : W := mkw 0x00c28140a8000a8a 0xa9c3c1c1f8000f8f

def z626 : W := mkw 0x44ffa8a046f1c441 0x04bb0180c4e18c03

def z627 : W := mkw 0x801130110040d014 0xffbb303104e3f07c

def z628 : W := mkw 0x0002c00001030000 0x8003c00000038000

def z629 : W := mkw 0x81005617190e31bc 0x9300fe013b1e73fc

def z630 : W := mkw 0x0000000000000000 0x3980018004000c00

def z631 : W := mkw 0x04e6cb40af9b2a8a 0x0044ce403b1c0380

def z632 : W := mkw 0x000800a000000000 0x6cb801b000000000

def z633 : W := mkw 0x81001617100c3134 0xfb043e3f001e707c

def z634 : W := mkw 0xc0d931f14660de55 0xfffb31f1c7e3ffff

def z635 : W := mkw 0xc01130114040d015 0x0000300000007000

def z636 : W := mkw 0x00e4014800000000 0x0044004e00000000

def z637 : W := mkw 0x08d3bd55f0000000 0xa8c3ffc1f8000000

def z638 : W := mkw 0x000800a000200440 0xffbb01b1c4e38c7f

def z639 : W := mkw 0x0002c000a903008a 0xb943c041fb03838f

def z640 : W := mkw 0xc2fff1fbeff7dfff 0xfffff1ffffffffff

def z641 : W := mkw 0x0813fc15f903008a 0x8003fe01f803800f

def z642 : W := mkw 0x0000000000000000 0x72440000031c0000

def z643 : W := mkw 0x0000400001020000 0xb040c00003020000

def z644 : W := mkw 0x0000000000000000 0x76b8000004e00000

def z645 : W := mkw 0x08fffdfdf7030000 0xfcffffffff038000

def z646 : W := mkw 0x00c28140a0000000 0x00830180c0000000

def z647 : W := mkw 0xc0ffb8b14060d455 0xffffffb1c4e3fc7f

def z648 : W := mkw 0x0aec15fff6b40f60 0x7ffc01fffffc0ff0

def z649 : W := mkw 0x0011200000000000 0xe4bb300000000000

def z650 : W := mkw 0x01000406180401a8 0x0000004e38000380

def z651 : W := mkw 0x0013a80000000000 0x8003fe0000000000

def z652 : W := mkw 0x08ffa9e8e0000000 0xe4ffff80c0000000

def z653 : W := mkw 0x0600420207ffef60 0x1300000007fffff0

def z654 : W := mkw 0x04f7e80007d3c000 0xb4fbc00007e38000

def z655 : W := mkw 0xc81935fdf060d455 0xffbb31fffce3fc7f

def z656 : W := mkw 0x00c2c140af030a8a 0xb0c3c0403f038380

def z657 : W := mkw 0x80c2d151af031a9e 0xfbc3f1f1ff03ffff

def z658 : W := mkw 0x00c2c0000f030088 0xb9c3c0413f03838c

def z659 : W := mkw 0x00ec01e800000000 0x04b8018000000000

def z660 : W := mkw 0x000810b140000000 0x080001b1c0000000

def z661 : W := mkw 0x00c2c140af030a8a 0xa8c3c1c1fb000380

def z662 : W := mkw 0x0affbdfff0240f60 0xedfffffff8000ff0

def z663 : W := mkw 0x00c041400f020a88 0xb9c0c1c13f020f8c

def z664 : W := mkw 0x02e4000206b40f60 0x77fc000007fc0ff0

def z665 : W := mkw 0x02ec01ea00240f60 0x6dfc01fe00000ff0

def z666 : W := mkw 0x00c2c140af030a8a 0x39c0c1c03f000f80

def z667 : W := mkw 0xc01120000060d455 0xf7bb300004e3fc7f

def z668 : W := mkw 0x400800a040200441 0x00000180c0000c03

def z669 : W := mkw 0x890815fff80411bc 0x090001fff80003fc

def z670 : W := mkw 0x02eec1eaafb70fea 0x7ffcc1fe3ffc0ff0

def z671 : W := mkw 0x0200000206b40f60 0x7b44007e07fc0ff0

def z672 : W := mkw 0x8102d617b90f31be 0xfb47fe7ffb1ff3ff

def z673 : W := mkw 0x81c2d6171f0f31bc 0xfbc7fe7f3f1ff3fc

def z674 : W := mkw 0x04f7ea0207dfe120 0xfffffe7e07fff3f0

def z675 : W := mkw 0x00dbf1f1ef030a8a 0xfdfbf1f1ff038f8f

def z676 : W := mkw 0x800810b100201454 0xffb831b104e27c7c

def z677 : W := mkw 0xc200000206f4df75 0x1300000007ffffff

def z678 : W := mkw 0x04e6ca00079b2000 0x76fcce0007fc0000

def z679 : W := mkw 0x00f7e80007030000 0xf4fffe0007038000

def z680 : W := mkw 0x08fffffdf10a2000 0xfefffffffb1e7000

def z681 : W := mkw 0x81c2d557bf071bbe 0xb9c3c1ffff038fff

def z682 : W := mkw 0x020801eaa8240fea 0x090001fff8000fff

def z683 : W := mkw 0xc01931f1e860dedf 0xffbb31f1fce3ffff

def z684 : W := mkw 0x85f7ea020fdff1bc 0xf7fffe0007fff3fc

def z685 : W := mkw 0x02ffa9ea06b40f60 0xfffffffe07fc0ff0

def z686 : W := mkw 0x800050110902109c 0xfb40f0713b0273fc

def z687 : W := mkw 0x00ee81e8a0000000 0xecffc1fff8000000

def z688 : W := mkw 0x08e6cd4cbf030a8a 0x0044ce4e3b000380

def z689 : W := mkw 0x0011301140000000 0x80033001c0000000

def z690 : W := mkw 0x00c2800000000000 0xa0c3c00000000000

def z691 : W := mkw 0x42fd21ea46f4cf61 0x7fff01fec7fd8ff3

def z692 : W := mkw 0x04ffebe807dbe000 0xfefffffe07fff000

def z693 : W := mkw 0x001930b140000000 0x4438303000000000

def z694 : W := mkw 0x8000101100001014 0x800030010002700c

def z695 : W := mkw 0x000000000040c000 0x1200000004e3f000

def z696 : W := mkw 0x8000101100001014 0x090000310000007c

def z697 : W := mkw 0x83ec17ff16bc3f74 0x7ffc3ffe07fc7ff0

def z698 : W := mkw 0x04f7ea00079b2000 0xe4fffe00031c0000

def z699 : W := mkw 0x00000140a8000a8a 0x0000004038000380

def z700 : W := mkw 0x81001617180c31bc 0x4b043e7f381c73fc

def z701 : W := mkw 0x0000000008000088 0x090000413800038c

def z702 : W := mkw 0xc83d3cbd5060d455 0xffbf3fbfc4e3fc7f

def z703 : W := mkw 0x01005617190e21a8 0xe844fe7f3b1c0380

def z704 : W := mkw 0x001120000040c000 0x800330000003f000

def z705 : W := mkw 0xc21930b346f4df75 0xffbb31b1c7ffffff

def z706 : W := mkw 0x00c28140a6000a00 0xb9c3c1c1ff000f80

def z707 : W := mkw 0x00c0155510000000 0xe8c4ffff38000000

def z708 : W := mkw 0x830815ffb8241ffe 0x090001fff8000fff

def z709 : W := mkw 0xc4eedab147bb3455 0x0944cfb1c31c0c7f

def z710 : W := mkw 0x083fbcbdf0000000 0xecbfffbff8000000

def z711 : W := mkw 0xc8ffbdfdf060d455 0xeffffffff8e07c7f

def z712 : W := mkw 0x083d7cbd5f030a8a 0x553c3e3e07038f8f

def z713 : W := mkw 0xc30042020ffefffd 0x1300000007ffffff

def z714 : W := mkw 0x04f7eb40afdbea8a 0xf6ffffc0ffffff83

def z715 : W := mkw 0x00244200019a2000 0xf67cfe0003fe7000

def z716 : W := mkw 0x02ec01ea06b50f62 0x7ffc01fe07fd8ff3

def z717 : W := mkw 0x0a13bc17f6b40f60 0x9303fe01fffc0ff0

def z718 : W := mkw 0x411966a6596ee5e9 0x04ffcfcefffd8f83

def z719 : W := mkw 0x030042020fbe2fe8 0x1300000007fc0ff0

def z720 : W := mkw 0x08ffadecb0000000 0xecfffffe38000000

def z721 : W := mkw 0x08ffbdfdf6010a02 0xfdffffffff018f83

def z722 : W := mkw 0x85117e15194af09c 0x8000fe013802700c

def z723 : W := mkw 0xc8ffbdfdf661de57 0xfffffffffce3fc7f

def z724 : W := mkw 0x0011341550000000 0xe847fe7ff8000000

def z725 : W := mkw 0x89ffebeae90e31bc 0x17bb0180c31e73fc

def z726 : W := mkw 0xc01930b14060d455 0xffffffb1c4e3fc7f

def z727 : W := mkw 0xc913fe15f94af09d 0x8003fe01f803f00f

def z728 : W := mkw 0x81004202090e31bc 0x02000000031c73f0

def z729 : W := mkw 0x810042020f0e3bbc 0x13000000071e7ffc

def z730 : W := mkw 0x022c01ea06b40f60 0x5f3c01fe07fc0ff0

def z731 : W := mkw 0x04356a0007dbe000 0xf6bf3e0007fff000

def z732 : W := mkw 0xc10852b3492e35fd 0x1b0001b1c31e7fff

def z733 : W := mkw 0x081bbcbdf0000000 0x8003fe3ff8000000

def z734 : W := mkw 0x850042020fdffbbe 0x1300000007ffffff

def z735 : W := mkw 0x000814b510000000 0xecfcffff38000000

def z736 : W := mkw 0x08ffbdfdf6000a00 0xfdffffffff038f8f

def z737 : W := mkw 0xc50042020ffff5fd 0x1300000007ffffff

def z738 : W := mkw 0xc10854b7592615fd 0xb9c3c1ffff038fff

def z739 : W := mkw 0x81004202090e31bc 0x13000000071fffff

def z740 : W := mkw 0x04352a0000d8e000 0x767c3e0003fc7000

def z741 : W := mkw 0x04f7ab40a6d9ea02 0x46bf3f80c4fdfc03

def z742 : W := mkw 0x810842a2092e35fc 0x7fb801b007fe7ffc

def z743 : W := mkw 0x4affbdfdf6f0ce41 0xecfffffffce18c03

def z744 : W := mkw 0x02ee89ea06b40f60 0x7ffccffe07fc0ff0

def z745 : W := mkw 0x022c00aa00b40560 0x7ffc01fe07fc0ff0

def z746 : W := mkw 0x00f7a80006d0c000 0xf6fffe0007fff000

def z747 : W := mkw 0xc81934bd5060d455 0xffbb31bfc4e3fc7f

def z748 : W := mkw 0x00c2c140af030a8a 0xf9c7c1ffff038f8f

def z749 : W := mkw 0x04352a0000d8e000 0xe67cfe0000fc7000

def z750 : W := mkw 0x00c2c140af030a8a 0x0000000003000380

def z751 : W := mkw 0xc93d3ebf506cf575 0x463c3e3e00fc7070

def z752 : W := mkw 0x00e443400f9a2a88 0xfffcffc13ffe7f8c

def z753 : W := mkw 0xc01120000060d455 0xffbb3181c4e3fc7f

def z754 : W := mkw 0x04f7ea0007dbe000 0x46fffe0007fdf000

def z755 : W := mkw 0x02ee81eaa6b40f60 0x7ffcc1fe3ffc0ff0

def z756 : W := mkw 0x870042020ffffffc 0x1300000007fffffc

def z757 : W := mkw 0x88ffbdfdf040d014 0xfffffffffce3f07c

def z758 : W := mkw 0x0000000000000000 0xb9c3c1c1fc038c0f

def z759 : W := mkw 0xc10814b750241575 0x0000003e00000070

def z760 : W := mkw 0xc31972b34ffefffd 0xffbb31b1c7ffffff

def z761 : W := mkw 0x00ffbcb550000000 0xecfffffff8000000

def z762 : W := mkw 0x04f7aa0000d8e000 0xf6fffe0004fff000

def z763 : W := mkw 0x85f7bc171ed5d1bc 0x0dbb007f3ce183fc

def z764 : W := mkw 0x02e6c148af930a8a 0xb9c3c1c1ff038f8f

def z765 : W := mkw 0x04f7eb40a7dbea02 0xffffffc0c7ffff83

def z766 : W := mkw 0x83cad5ffbf271ffe 0xb9c3c1ffff038fff

def z767 : W := mkw 0x08e69d5db0000000 0xe8c7fffff8000000

def z768 : W := mkw 0x00e6c140af930a8a 0xbdfbc1c1ffe38f8f

def z769 : W := mkw 0x02ee81eaa6b50f62 0xffffc1fffffd8ff3

def z770 : W := mkw 0x8300420209be35fc 0x1300000003fe73fc

def z771 : W := mkw 0x48ffbdfdf060c441 0xfefffffffce3fc03

def z772 : W := mkw 0x81005617190e31bc 0x4b44fe7f3b1c73fc

def z773 : W := mkw 0xc10814b7582415fd 0x0900007f380003fc

def z774 : W := mkw 0x022ec0aaa9b705ea 0xc63fc03ff8ff807f

def z775 : W := mkw 0x04f7ea000fdbe088 0xf7fffe0007fff38c

def z776 : W := mkw 0x00e4141516900000 0xfefcfe7f3ffc0000

def z777 : W := mkw 0xc01930b14060d455 0xc6bb31b1c4e3fc7f

def z778 : W := mkw 0x811972b3490e31bc 0xffbb31b1c31e73fc

def z779 : W := mkw 0xc53d3eb750fcf575 0x463c3e3e00fc7070

def z780 : W := mkw 0x81004202090e31bc 0x00000000031e738c

def z781 : W := mkw 0x08ee8decb0000000 0x04fccfce38000000

def z782 : W := mkw 0x01004202090e21a8 0x13000000031c03f0

def z783 : W := mkw 0xc51972b34ffff5fd 0xffbb31b1c7ffffff

def z784 : W := mkw 0x020800a206b40f60 0x7ffc01fe07fc0ff0

def z785 : W := mkw 0x08ec15fdf0000000 0xecfcfffff8000000

def z786 : W := mkw 0x04352a0000d8e000 0x563c3e0004fff000

def z787 : W := mkw 0x04f7eb4007dbea00 0xf6fffe4007fff380

def z788 : W := mkw 0x04f7ea0007dbe000 0xc67ffe0003fff000

def z789 : W := mkw 0x080814bd50000000 0xe844fe7f38000000

def z790 : W := mkw 0xc8ffbdfdf040d015 0xecfffffff8007000

def z791 : W := mkw 0x08e69d5df0000000 0x0044ce4ff8000000

def z792 : W := mkw 0x08ffbdfdf0000000 0xfefffffffb1c0000

def z793 : W := mkw 0x022c00aa06b40f60 0x463c003e03fc03f0

def z794 : W := mkw 0xc0dbf1f1ef63dedf 0x4678f0703be073f0

def z795 : W := mkw 0x083fbcbdf0000000 0xec7ffe7ff8000000

def z796 : W := mkw 0xc10814b750241575 0x090001bfc0000c7f

def z797 : W := mkw 0x08ffbdfdf6900a00 0xfffffffffffc0f80

def z798 : W := mkw 0x0000000200040120 0x7ffc007e07fc03f0

def z799 : W := mkw 0x08f7bd5df0000000 0xa8c7ffcff8000000

def z800 : W := mkw 0x04f7eb40afdbea8a 0x467cfe403bfc7380

def z801 : W := mkw 0x04352a0000d8e000 0xe6bf3e0000fc7000

def z802 : W := mkw 0x08ffbdfdf0000000 0x4c7cfffff8000000

def z803 : W := mkw 0x04f7ea00a7dbe002 0xf6fffe00c7fff003

def z804 : W := mkw 0x0000040410000000 0x6844ce7e38000000

def z805 : W := mkw 0x851172130fdff1bc 0xffbb303107fff3fc

def z806 : W := mkw 0x08ffbdfdf0200440 0xeefffffff8e00070

def z807 : W := mkw 0x04f7ea0007dbe000 0xf7fffe0007fffc0f

def z808 : W := mkw 0x08ffbdfdf0000000 0x44fffffef8000000

def z809 : W := mkw 0x083d3cbd50000000 0xc43cfe3f38000000

def z810 : W := mkw 0xc00800a00060d455 0xffbb01b1c4e3fc7f

def z811 : W := mkw 0xc8ffbdfdf040d015 0xfdfffffffc03fc0f

def z812 : W := mkw 0x0cffbdfdf0d0c000 0xecfffffff8e00000

def z813 : W := mkw 0x0000040410000000 0xe044fe4e38000000

def z814 : W := mkw 0x830042020fbf3ffe 0x1300000007ffffff

def z815 : W := mkw 0x08ffbdfdf0900000 0xeefffffff8fc0000

def z816 : W := mkw 0x04e4420007dbe000 0xf6fcfe0007fff000

def z817 : W := mkw 0x04f7ea0007dbe000 0xfffffe3007fff070

def z818 : W := mkw 0x001122000048e000 0x463c3e0000fc7000

def z819 : W := mkw 0x00d3e200074be000 0xf6fffe0007fff000

def z820 : W := mkw 0x08e68d4cb0000000 0xb9c7cfcffc038c0f

def z821 : W := mkw 0x81005213090e31bc 0x53003030031e73fc

def z822 : W := mkw 0x8000141710041134 0xfb44fe7f3b1e73fc

def z823 : W := mkw 0x00c2c140af030a8a 0xfffbc1c1ffe38f8f

def z824 : W := mkw 0xc8ffbdfdf0201455 0xfffffffffce00c7f

def z825 : W := mkw 0x08ffbcbd50000000 0xecfffe7f38000000

def z826 : W := mkw 0x04f7ea0007dbe000 0xfefffe413ffff000

def z827 : W := mkw 0x08e69d5db0000000 0x0844ce7f38000000

def z828 : W := mkw 0x04f7ea000fdbe088 0xffffffc1ffffff8f

def z829 : W := mkw 0x04f52a0006d8e000 0x467c3e0003fc7000

def z830 : W := mkw 0x83c855ff1f261ffc 0xb9c0c1ff3f020ffc

def z831 : W := mkw 0xc90815fff82415fd 0x090001fff8000fff

def z832 : W := mkw 0x04f7eb40a7dbea02 0xfeffffc1fffffc03

def z833 : W := mkw 0x81004202090f31be 0x13000000031ff3ff

def z834 : W := mkw 0x81005617190e31bc 0xfb44fe7f3f1fffff

def z835 : W := mkw 0x04356a0001dae000 0x563c3e0003fe7000

def z836 : W := mkw 0x08f7bd5df0000000 0xe847fe7ff8000000

def z837 : W := mkw 0x000040000f030a8a 0xb9c3c1c1ff038f8f

def z838 : W := mkw 0xc11934b75064d575 0x4638303e00e07070

def z839 : W := mkw 0xc2f5315b46d4db35 0x8047304fc31ff38f

def z840 : W := mkw 0x00c2c340af0b2a8a 0xbbc3c1c1ff1fff8f

def z841 : W := mkw 0x801130110040d014 0xffbb31b1c4e3fc7f

def z842 : W := mkw 0xc8ffbdfdf0201455 0xecfffffff8000070

def z843 : W := mkw 0x0ae68d4cb6900a00 0x0044ce4e38000000

def z844 : W := mkw 0x08ffadecf0000000 0x047cce4e38000000

def z845 : W := mkw 0x06f7eb4807dbea00 0xf6fffe0007fff000

def z846 : W := mkw 0x4affa9e8e6f0ce41 0x04bb0180c4e18c03

def z847 : W := mkw 0x04f7aa0006d9e000 0xf6bf3e0004fff000

def z848 : W := mkw 0x0cffbdfdf6d1c000 0xfefffffffce3f000

def z849 : W := mkw 0x08e6c948af030a8a 0xb9c3c1c1ff038f8f

def z850 : W := mkw 0x81005617190e31bc 0xfb44fffffb1e7fff

def z851 : W := mkw 0x04356a0001dae000 0x467cfe0003fc7000

def z852 : W := mkw 0xc01134155040d015 0x8003fe01f803f00f

def z853 : W := mkw 0x08ffbcbdf0000000 0xe4fffe3ff8000000

def z854 : W := mkw 0x04356a0009dae088 0xff7cfe413bfe738c

def z855 : W := mkw 0x00e4141510000000 0xecfcfe7f38000000

def z856 : W := mkw 0x04f7ea000fdbea8a 0xf6fffe0007fff380

def z857 : W := mkw 0x000800a200240560 0x7f7c007e03fc03f0

def z858 : W := mkw 0x02e4000206b40f60 0x7ffc007e07fc0ff0

def z859 : W := mkw 0xc8ffbdfdf060d455 0xedfffffff803fc7f

def z860 : W := mkw 0x00e6c340af9b2a8a 0xffffffc1ffffff8f

def z861 : W := mkw 0x04f7ea0007dbe000 0xffffff8007fffc00

def z862 : W := mkw 0x81005617190e31bc 0x7b44fe7e3b1c73f0

def z863 : W := mkw 0x08ffbdfdf6d0c000 0xfefffffffffff000

def z864 : W := mkw 0x00c28140a8000a8a 0xb9c3c1c1fc038f8f

def z865 : W := mkw 0x08ee9dfdf0000000 0x0044ce7e38000000

def z866 : W := mkw 0x0024020000982000 0x463c3e0000fc7000

def z867 : W := mkw 0xcaffbdfdf6f0de55 0xfffffffffce3fc7f

def z868 : W := mkw 0x00c2c140af030a8a 0x198301c1ff038f8f

def z869 : W := mkw 0xc01930b14060d455 0x1fbb01b1c4e3fc7f

def z870 : W := mkw 0x00f7bd55b0000000 0xecfffffff8000000

def z871 : W := mkw 0x0000141510000000 0xf944fe7f3802000c

def z872 : W := mkw 0x00e6c148af030a8a 0xb9c7c1cfff038f8f

def z873 : W := mkw 0x810042020f0f31bc 0x13000000071ff3fc

def z874 : W := mkw 0x830852b30fbe3ffc 0xffb831b107fe7ffc

def z875 : W := mkw 0x0437ea0001dbe000 0xf6bffe0004fff000

def z876 : W := mkw 0x81c29757b60d3b36 0x42873fbec41dfc73

def z877 : W := mkw 0xc01934b55060d455 0xffbb31fffce3fc7f

def z878 : W := mkw 0x081bbdfdf0000000 0xe847fffff8000000

def z879 : W := mkw 0x00ec01ea06940120 0x7ffc01fe07fc03f0

def z880 : W := mkw 0x0000000008000088 0xb98301c1fc038f8f

def z881 : W := mkw 0x81005617190e31bc 0xf244fe7e3b1e73f0

def z882 : W := mkw 0x0000040410000000 0xa844ce4f38000000

def z883 : W := mkw 0xc01934b55060d455 0x463c3e3e00e07070

def z884 : W := mkw 0x02ec01ea06b40f60 0x7ffc01ffc7fc0fff

def z885 : W := mkw 0x88e69d5db0001014 0xfb44fe7f3802707c

def z886 : W := mkw 0x08ffbdfdf0000000 0xecfffffffc018c03

def z887 : W := mkw 0x80f7bc151040d014 0xfffffe7f3ce3f07c

def z888 : W := mkw 0xc8e68d4cb060d455 0x1344ce4e3ce3fc7f

def z889 : W := mkw 0x08ffbdfdf6200e40 0xffffffffffe00ff0

def z890 : W := mkw 0xc1004202096ef5fd 0x1300000003fe73fc

def z891 : W := mkw 0x0002c140af030a8a 0x9903c1c1ff038f8f

def z892 : W := mkw 0xccffbdfdf6f1d455 0xfffffffffce3fc7f

def z893 : W := mkw 0x04f7ea0007dbe000 0x567cfe0007fff000

def z894 : W := mkw 0x04f7ea0007dbea02 0xf6fffe0007fffc03

def z895 : W := mkw 0x0002c140a9030a8a 0xb983c1c1fc038f8f

def z896 : W := mkw 0x0cf7eb48a7dbe000 0xf6fffe0007fff000

def z897 : W := mkw 0x0c0857fdf7dbe000 0x1a0001fffffff000

def z898 : W := mkw 0x01004202090e21a8 0x11000000031e038c

def z899 : W := mkw 0x050042020fdfe1a8 0x1200000007fff380

def z900 : W := mkw 0xc8193cb55060d455 0xffbb3fb1c4e3fc7f

def z901 : W := mkw 0x0affbdfdf6b10e42 0xecfffffffce18c03

def z902 : W := mkw 0x04f7eb40afdbea8a 0xf6ffff81fffffc0f

def z903 : W := mkw 0x04352a0000d8e000 0x76bc3e0004fc7000

def z904 : W := mkw 0x00029415b0000000 0xe847fe7ff8000000

def z905 : W := mkw 0x04352b40a8d8ea8a 0x4f3c3fc1f8fc7f8f

def z906 : W := mkw 0x04f7ea0007dbe000 0xe6fffe0003fc7000

def z907 : W := mkw 0xc01920a04060d455 0xbfbb0181c4e3fc7f

def z908 : W := mkw 0x00e4054c10000000 0x0044ce4e38000000

def z909 : W := mkw 0x04f7eb4807dbe000 0xf6fffe4e07fff000

def z910 : W := mkw 0x48ffbdfdf060c441 0xfdfffffffce38c0f

def z911 : W := mkw 0x850042020f9f31bc 0x13000000031e73fc

def z912 : W := mkw 0x0000141510000000 0xc004fe3f38000000

def z913 : W := mkw 0xc81bbdfdf060d455 0x8903fffff803fc7f

def z914 : W := mkw 0x08e68d4cb6900000 0x76fcce4e3ffc0000

def z915 : W := mkw 0x06ee89ea06b50f60 0x7ffc01fe07fc0ff0

def z916 : W := mkw 0x001920a00060c440 0xffbb31b1c4e3fc7f

def z917 : W := mkw 0x08ffbdfdf040c000 0xeefffffff8e07000

def z918 : W := mkw 0x00c2c0000f030088 0xb9c3c1c1ff038f8f

def z919 : W := mkw 0x022c00aa00b40560 0x467c007e03fc03f0

def z920 : W := mkw 0x48ffbdfdf060c441 0xfffffffffce18c73

def z921 : W := mkw 0x02ec01ea06b40f60 0x1fb801fe07fc0ff0

def z922 : W := mkw 0x00353c1510000000 0xec7cfe7f38000000

def z923 : W := mkw 0x0413ea00014be000 0xf6fffe0007fff000

def z924 : W := mkw 0x02ec01ea00b40560 0x7ffc01fe03fc03f0

def z925 : W := mkw 0x0aee89eaa6b40f60 0x7ffc01fe07fc0ff0

def z926 : W := mkw 0x00ec05ec10000000 0x6cfccffe38000000

def z927 : W := mkw 0x08ffbdfdf0000000 0xedfffffff8000c0f

def z928 : W := mkw 0x83ec57fd1fba3edc 0x84b8ff813ce27c0c

def z929 : W := mkw 0x08ffbdfdf0000000 0x6cfcfffe38000000

def z930 : W := mkw 0x08ee8decb0000000 0xecffcffff8000000

def z931 : W := mkw 0x0affbdfdf6900a00 0xecfffffff8000000

def z932 : W := mkw 0x08ffbdfdf6b00440 0xfffffffffffc0c70

def z933 : W := mkw 0x830814bf182415fc 0x0900007f380003fc

def z934 : W := mkw 0x0011341510000000 0xecfffe7f38000000

def z935 : W := mkw 0x48ffbdfdf661ce43 0xecfffffffce18c03

def z936 : W := mkw 0x04f7eb40afdbe08a 0xfeffffc1fffff00f

def z937 : W := mkw 0x81004202090e31bc 0x01000000031c03fc

def z938 : W := mkw 0x04e6ca00079b2000 0x00000000031c0000

def z939 : W := mkw 0x0002c000af030a8a 0xb983c181ff038f8f

def z940 : W := mkw 0x00f7ea00014ae000 0xf6fffe0007fff000

def z941 : W := mkw 0x08e68d4cb0000000 0x0844cfcff8000000

def z942 : W := mkw 0x81005617190e31bc 0xfb47fe7ffb1ff3ff

def z943 : W := mkw 0xc813bc15f040d015 0xfb47fe7ff803f07f

def z944 : W := mkw 0x08ffbdfdf040c000 0xecfffffffce18000

def z945 : W := mkw 0x04356a0007dbe000 0x463c3e0003fc7000

def z946 : W := mkw 0xc83fbcbdf060d455 0xffbfffbffce3fc7f

def z947 : W := mkw 0xc83d3cbd5060d455 0xfffffffffce3fc7f

def z948 : W := mkw 0x08e68d4cb0000000 0x00c7cfcef8000000

def z949 : W := mkw 0x08ffbdfdf0200440 0xecfffffffce00c00

def z950 : W := mkw 0xc113f615f94bf09f 0x8003fe01f803f00f

def z951 : W := mkw 0x00c0155516000a00 0xf9c4ffff3f000f80

def z952 : W := mkw 0x02ec01eaa6b40f60 0x7ffc01fffffc0ff0

def z953 : W := mkw 0x00c28140a6000a00 0xb9c3c1c1ff038f8f

def z954 : W := mkw 0xc01934b55060d455 0xffbbffb1fce3fc7f

def z955 : W := mkw 0x04352a0000d8e000 0xf63c3e0000fe7000

def z956 : W := mkw 0x08ffbdfdf060c440 0xfffffffffce3fc70

def z957 : W := mkw 0x04f7eb40afdbea8a 0xfffffe413ffff38c

def z958 : W := mkw 0x08ffbdfdf0000000 0xfefffffff8027000

def z959 : W := mkw 0x0aee8decb6b00e40 0x04fccfce3ce00c00

def z960 : W := mkw 0x04f7eb40a7dbea02 0xffffff81c7fffc0f

def z961 : W := mkw 0x00e6c140af930a8a 0xb9c7c1c1ff1f8f8f

def z962 : W := mkw 0x08ffbdfdf0000000 0x8847fffff8000000

def z963 : W := mkw 0x04e6c940af930a8a 0xb9c3c1c1ff038f8f

def z964 : W := mkw 0xc8ffbdfdf0201455 0xfdfffffffc038c7f

def z965 : W := mkw 0xc8ffbdfdf060d455 0xfefffffffce3f070

def z966 : W := mkw 0x00c2c340af0b2a8a 0xb9c3ffc1ff03ff8f

def z967 : W := mkw 0x83004202092e3ffc 0x13000000031e7ffc

def z968 : W := mkw 0x0000141510000000 0xf944fe7f3b000380

def z969 : W := mkw 0x02ec01ea06b40f60 0xfffc31fe07fe7ff0

def z970 : W := mkw 0x0000141510000000 0xe8c7fffff8000000

def z971 : W := mkw 0xc1117213494ef1bd 0x93033001c31ff3ff

def z972 : W := mkw 0x04f7aa0000d8e000 0x467cfe0000fc7000

def z973 : W := mkw 0x08ffbdfdf0000000 0xfcfffffffc038000

def z974 : W := mkw 0x08ffadecf0000000 0xacffcfcff8000000

def z975 : W := mkw 0x0000141510000000 0xfa44fe7f3b1c0000

def z976 : W := mkw 0x02ee81eaa6b50f62 0x7ffc01fe07fc0ff0

def z977 : W := mkw 0x00001555b0000000 0xe844fffff8000000

def z978 : W := mkw 0x02ec01ea06b40f60 0xfffc01ff07fe0ffc

def z979 : W := mkw 0x0002c140a9030a8a 0xb943c1c1fb038f8f

def z980 : W := mkw 0x08e69d5db0000000 0x8044fe4f38000000

def z981 : W := mkw 0x00004202090e21a8 0xfb44fe7f3b1e73fc

def z982 : W := mkw 0x81004202090e31bc 0xbb000001031e73fc

def z983 : W := mkw 0xc01920a04060d455 0x7fbb01b0c4e3fc7f

def z984 : W := mkw 0x81005617190e31bc 0x8944fe7f3b1e73fc

def z985 : W := mkw 0xc80815fdf0201455 0xfb44fffff8027c7f

def z986 : W := mkw 0x00c29555b6010a02 0xe8c7fffffc018c03

def z987 : W := mkw 0x00c2c140af030a8a 0xf9c7ffc1ff038f8f

def z988 : W := mkw 0x04f7ea00a7dbe000 0xf6fffe01fffff000

def z989 : W := mkw 0x08e68d4cb0000000 0x6844ce7e38000000

def z990 : W := mkw 0x401934b55060c441 0xecfffffffce18c03

def z991 : W := mkw 0x800810b100201454 0xffbb31b1c4e3fc7f

def z992 : W := mkw 0x08113c1550000000 0xe844fe7f38000000

def z993 : W := mkw 0x81004202090e31bc 0x01000000000273fc

def z994 : W := mkw 0x88ffbdfdf0001014 0xfffffffffc03fc7f

def z995 : W := mkw 0x08ee9dfdf0000000 0xe844fffff8000000

def z996 : W := mkw 0x02ec01ea06b40f60 0xfffcc1ff3ffc0ff0

def z997 : W := mkw 0x0813bd5df0000000 0x8003fe4ff8000000

def z998 : W := mkw 0x04f7eb40a7dbe000 0xf6fffe403ffff000

def z999 : W := mkw 0xc01934b55060d455 0xffbf3fbfc4e3fc7f

def z1000 : W := mkw 0x80ec15fd10201454 0xfffcffff3ce27c7c

def z1001 : W := mkw 0x08f7ad4cf0000000 0x0047ce4ef8000000

def z1002 : W := mkw 0xc00014151060d455 0xfb44fe7f3ce3fc7f

def z1003 : W := mkw 0xc01934b55060d455 0xee7cfe7f38e07070

def z1004 : W := mkw 0x061bebea016fef60 0x8903fffe0003fff0

def z1005 : W := mkw 0x08f7ad4cb040c000 0xf6fffe4e3ce3f000

def z1006 : W := mkw 0xc81bbcb5f060d455 0xfffffffffce3fc7f

def z1007 : W := mkw 0x02ec01ea06b40f60 0xffff01fe07ff8ff0

def z1008 : W := mkw 0x00f5620007dae000 0xf6fffe0007fff000

def z1009 : W := mkw 0x080a9dfdf0000000 0x0800cffff8000000

def z1010 : W := mkw 0x830042020f9e3bbc 0x13000000031e73fc

def z1011 : W := mkw 0x000815fd10000000 0xe844ffff38000000

def z1012 : W := mkw 0x08ffbdfdf040c000 0xfffffffffce3fc0f

def z1013 : W := mkw 0x04f7ab40a0d8e000 0xeeffffc1f8fc7000

def z1014 : W := mkw 0x0cffbdfdf6d1ca02 0xecfffffffce18c03

def z1015 : W := mkw 0x02ec01ea06b40f60 0x7fff01fec7fd8ff3

def z1016 : W := mkw 0x08ffbdfdf6010a02 0xecfffffff8000000

def z1017 : W := mkw 0x022c01ea00b40f60 0x7f7c01fe03fc0ff0

def z1018 : W := mkw 0x81c043420f0e3bbc 0x3bc001c0071e7ffc

def z1019 : W := mkw 0x060042020fffefea 0x1300000007ffffff

def z1020 : W := mkw 0x08e68d4cb6010a02 0x0044ce4e38000000

def z1021 : W := mkw 0x04f7eb40afdbea8a 0xffffffc03fffff80

def z1022 : W := mkw 0xc11962a2496ef5fd 0x17bb0180c7ffffff

def z1023 : W := mkw 0x0437ea00a9dbe08a 0xc63ffe01f8fff00f

def z1024 : W := mkw 0x04f7eb40afdbea8a 0xf7ffff80c7ffff8f

def z1025 : W := mkw 0x04f7eb40a7dbea00 0xffffffc1ffffff80

def z1026 : W := mkw 0x00c2c140af030a8a 0x9183c181ff038f8f

def z1027 : W := mkw 0xc01930b14060d455 0x97bb3181c4e3fc7f

def z1028 : W := mkw 0x0813bc15f0000000 0xc007fe3ff8000000

def z1029 : W := mkw 0x81c2c342af0f3bbe 0x13830180c71fffff

def z1030 : W := mkw 0x04f7ea0007dbe000 0x96bbfe0007fff000

def z1031 : W := mkw 0xc8ffbdfdf060d455 0xfffffffff8e2707c

def z1032 : W := mkw 0x00ffa9e8a0000000 0xecfffffff8000000

def z1033 : W := mkw 0x08f7ad4cb0000000 0x447cfe4e38000000

def z1034 : W := mkw 0x0cf7ea00e7dbe000 0xf6fffe00c7fff000

def z1035 : W := mkw 0x08e68d4cb6000a00 0x39c4cfce3f000f80

def z1036 : W := mkw 0x04f7ea0007dbe000 0xc6bffe0004fff000

def z1037 : W := mkw 0x0000141510000000 0x4044fe7e38000000

def z1038 : W := mkw 0x02e4014a06940b20 0x7ffc007e07fc03f0

def z1039 : W := mkw 0x04f7ea00afdbea8a 0xf7fffe01ffffff8f

def z1040 : W := mkw 0x81005617190e31bc 0xfbc4ffff3f1e7ffc

def z1041 : W := mkw 0x02ee81eaa6b40f60 0xffffc1ffffff8fff

def z1042 : W := mkw 0x81005617190e31bc 0xea44fe7f3b1c73f0

def z1043 : W := mkw 0xc8ffbdfdf060d455 0xedfffffffce18c7f

def z1044 : W := mkw 0x04f7eb4007dbea00 0xf6ffff8007fffc00

def z1045 : W := mkw 0x04f7ea0007dbe000 0xf67cfe0003fe7000

def z1046 : W := mkw 0xc01930b14060d455 0x8dbb31b1c4e3fc7f

def z1047 : W := mkw 0x080815fdf0000000 0x0844cffff8000000

def z1048 : W := mkw 0x08e68d4cb0000000 0x28c4cfce38000000

def z1049 : W := mkw 0x02ec00aa06b40560 0x7ffc007e07fc03f0

def z1050 : W := mkw 0x0affbdfdf6b00e40 0xfefffffffffc0c00

def z1051 : W := mkw 0x04f7eb40a7dbe000 0xf6ffff80c7fff000

def z1052 : W := mkw 0x81117615194af09c 0x8003fe013803f00c

def z1053 : W := mkw 0x04f7ea0007dbe000 0xfeffff81c7fff000

def z1054 : W := mkw 0x02ec01ea06b40f60 0xfffcfffe07fc0ff0

def z1055 : W := mkw 0x00004140a9020a8a 0xb9c3c1c1ff038f8f

def z1056 : W := mkw 0x00c2c140a9020088 0xb9c3c1c1ff038f8f

def z1057 : W := mkw 0x04f7eb40afdbea8a 0xf7fffe403fffff8f

def z1058 : W := mkw 0x03e6c74ebf9f2baa 0x0044ce4e3b1c0380

def z1059 : W := mkw 0x08f7ad4cb0000000 0xecffffcff8000000

def z1060 : W := mkw 0x00028140a8010a8a 0x090301c1f8018f8f

def z1061 : W := mkw 0x04f7ea00afdbe08a 0xfffffe41fffff38f

def z1062 : W := mkw 0x04f7ea00afdbe08a 0xf6fffe003ffff000

def z1063 : W := mkw 0x08dbbdfdf0000000 0xa8c3fffff8000000

def z1064 : W := mkw 0x08029c15b0000000 0xe844fe7f38000000

def z1065 : W := mkw 0x08e68d4cb6000a00 0x0044ce4e3b000380

def z1066 : W := mkw 0x8d13fe15f94bf09c 0x8003fe01f803f00c

def z1067 : W := mkw 0x04f7eb4007dbe000 0xfeffffc007fff000

def z1068 : W := mkw 0x44f7ea0047dbe001 0xf6fffe00c7fff003

def z1069 : W := mkw 0x0437ea0001dbe000 0x463cfe0000fc7000

def z1070 : W := mkw 0x80c29555b0001014 0xfbc7fffffc03fc7f

def z1071 : W := mkw 0x04f52a0006d8e000 0x46bc3e0004fc7000

def z1072 : W := mkw 0x04c2c340af9b2a8a 0xb9c3c1c1ff1f8f8f

def z1073 : W := mkw 0x04356a0007dbe000 0xf67cfe0007fff000

def z1074 : W := mkw 0x00c2c140af030a8a 0x80c3c1c1ff038f8f

def z1075 : W := mkw 0x04f56a0007dae000 0xf6fcfe0007fe7000

def z1076 : W := mkw 0x00004200010a2000 0xf6fcfe0007fe7000

def z1077 : W := mkw 0x08ffbdfdf0000000 0x0cffcffff8000000

def z1078 : W := mkw 0x08ee8decb0200440 0x7ffccffe3ce00c70

def z1079 : W := mkw 0xc513fe15594bf09d 0x8003fe01f803f00f

def z1080 : W := mkw 0x0813bc15f0000000 0x8047fe4ff8000000

def z1081 : W := mkw 0x4cffbdfdf6f1c441 0xecfffffffce18c03

def z1082 : W := mkw 0xc81bbdfdf060d455 0xffbbfffffce3fc7f

def z1083 : W := mkw 0x81005213090e31bc 0x1b000031031e73fc

def z1084 : W := mkw 0x08ffbdfdf0200440 0xfffffffffce38c7f

def z1085 : W := mkw 0x08ffbdfdf0000000 0xfdfffffff802000c

def z1086 : W := mkw 0x88ffbdfdf0201454 0xfffffffffce27c7c

def z1087 : W := mkw 0x04e6ca00079b2000 0xf6fcfe0007fe7000

def z1088 : W := mkw 0x00ec01ea00240560 0x7ffc01fe07fc0ff0

def z1089 : W := mkw 0x04f7ea0007dbe000 0xf6fffe01c7fff00f

def z1090 : W := mkw 0x00c2c140af030a8a 0xfbc7c1c1ff1f8f8f

def z1091 : W := mkw 0x08241c1d10000000 0xe844fe7f38000000

def z1092 : W := mkw 0x08ffbdfdf0000000 0xfffffffff8000070

def z1093 : W := mkw 0x0aec01eae6b40f60 0x7ffc01fec7fc0ff0

def z1094 : W := mkw 0x04f56a0007dbe000 0x76fc3e0007fff000

def z1095 : W := mkw 0x00e4155d10000000 0xe844fe7f38000000

def z1096 : W := mkw 0x81001617100c3134 0xfb44fe7f3b1c73f0

def z1097 : W := mkw 0xc01930b14060d455 0xfffbf1f1fce3fc7f

def z1098 : W := mkw 0xc8ffbdfdf060d455 0xeefffffff8e3f07f

def z1099 : W := mkw 0x04f7ea0007dbe000 0x76fcfe0007fc7000

def z1100 : W := mkw 0x08ee8decb0000000 0x0844cffe38000000

def z1101 : W := mkw 0x0800155db0000000 0xe844fe7f38000000

def z1102 : W := mkw 0x08f7bd5df0000000 0xe4fffe4ff8000000

def z1103 : W := mkw 0x00e6c940af030a8a 0xb9c7cfc1ff038f8f

def z1104 : W := mkw 0x02ec00aa06b40f60 0x77fc003e07fc0ff0

def z1105 : W := mkw 0x083d3dfdf0000000 0xec7cfffff8000000

def z1106 : W := mkw 0x81004202094ef1bc 0x1300000007fff3fc

def z1107 : W := mkw 0x81004202092e35fc 0x1300000007fe7ffc

def z1108 : W := mkw 0x04f7ea000fdbea8a 0xffffff81c7ffff8f

def z1109 : W := mkw 0xc11972b3496ef5fd 0x5738303003fe73fc

def z1110 : W := mkw 0x04f7ea0007dbe000 0x56bf3e0007fff000

def z1111 : W := mkw 0xc4fffeb557fbf455 0xfffffffffffffc7f

def z1112 : W := mkw 0x8b0815fff8241ffc 0x090001fff8000ffc

def z1113 : W := mkw 0x00c2c140af030a8a 0xfbc3c1f1ff038fff

def z1114 : W := mkw 0x8000141510001014 0xe844fe7f3802700c

def z1115 : W := mkw 0x083fbdfdf0000000 0xcc3ffffff8000000

def z1116 : W := mkw 0x08ee9dfdf0000000 0x6cfccffff8000000

def z1117 : W := mkw 0x04f7ea0007dbe000 0xfefffe7e07fff000

def z1118 : W := mkw 0xca0815fff0241f75 0x090001fff8000fff

def z1119 : W := mkw 0x08ffbdfdf0000000 0xfdfffffffb000380

def z1120 : W := mkw 0x8000141510001014 0xea44fe7f38007070

def z1121 : W := mkw 0x0cffbdfdf041c000 0xecfffffff8018000

def z1122 : W := mkw 0xc0ffbcb55060d455 0xfffffffffce3fc7f

def z1123 : W := mkw 0x04f7eb400fdbea8a 0xffffffc007ffff8f

def z1124 : W := mkw 0x00e68c0410000000 0x0044ce4e38000000

def z1125 : W := mkw 0x00c28544b0000000 0xa8c7cfcff8000000

def z1126 : W := mkw 0x81005617190e31bc 0xfbc7fe7f3f1ff3fc

def z1127 : W := mkw 0x04f7ea0001dbe000 0xe6fffe0000fff000

def z1128 : W := mkw 0x42ec01ea46b40f61 0x7ffc01fec7fc0ff3

def z1129 : W := mkw 0xc01920a04060d455 0xf7bb3180c4e3fc7f

def z1130 : W := mkw 0x0000141510000000 0xf9c7fffffc038c0f

def z1131 : W := mkw 0x04f7aa0006d9e000 0x463c3e0000fc7000

def z1132 : W := mkw 0x04356a0001dae000 0xc63cfe0000fe7000

def z1133 : W := mkw 0x810814b7182415fc 0x090001ff38000ffc

def z1134 : W := mkw 0x04f7eb4007dbea00 0xffffffc1c7ffff8f

def z1135 : W := mkw 0x08f7bd5db0000000 0xecfffe7f38000000

def z1136 : W := mkw 0x08ffbdfdf6000000 0xfcffffffff000000

def z1137 : W := mkw 0x04f7aa0006d9e000 0xe6fffe0004fdf000

def z1138 : W := mkw 0x0411620007dbe000 0xf6fffe0007fff000

def z1139 : W := mkw 0x0024000200940120 0x7f7c007e03fc03f0

def z1140 : W := mkw 0x083d3cbd50000000 0x447cfe7e38000000

def z1141 : W := mkw 0x02ec01ea06b40f60 0x4f7c01fe03fc0ff0

def z1142 : W := mkw 0x022c00aa06b40f60 0x7f7c007e07fc0ff0

def z1143 : W := mkw 0x02ec15fd16b00e40 0xecfcffff3ce00c00

def z1144 : W := mkw 0x001120000040c000 0xf6fffe0004e3f000

def z1145 : W := mkw 0x022c00aa06b40f60 0x7fbc01be07fc0ff0

def z1146 : W := mkw 0x0000141510000000 0x8800fe7f38000000

def z1147 : W := mkw 0xc8ffbdfdf040d015 0xfefffffffce3f00f

def z1148 : W := mkw 0x08ca95fdf0000000 0xe8c7fffff8000000

def z1149 : W := mkw 0x04f7ea000fdbea8a 0xfffffe413fffff8f

def z1150 : W := mkw 0x0000141510000000 0x0844ce7f38000000

def z1151 : W := mkw 0x08ffbdfdf6000a00 0xecfffffffb000380

def z1152 : W := mkw 0x81005617190e31bc 0xfbc7fffffb1e73fc

def z1153 : W := mkw 0xc2fd35ff56f4df75 0xffffffffffffffff

def z1154 : W := mkw 0x002c14bd10000000 0xec7cfe7f38000000

def z1155 : W := mkw 0xc30815ff58241ffd 0x090001fff8000fff

def z1156 : W := mkw 0x06ffa9e8a6f1ce42 0x04bb0180c4e18c03

def z1157 : W := mkw 0xc01930b14060d455 0xffff31ffc4e3fc7f

def z1158 : W := mkw 0x04356a0001dbe000 0x463c3e0000fff000

def z1159 : W := mkw 0x0000141510000000 0x8044fe4f38000000

def z1160 : W := mkw 0x05e6cf46bf9f2baa 0x0044ce4e3b1c0380

def z1161 : W := mkw 0x08ffbdfdf6900000 0xecfffffffce00000

def z1162 : W := mkw 0x00ee95fdb0000000 0xecfffffff8000000

def z1163 : W := mkw 0x04352a0006d9e000 0x463c3e0004fdf000

def z1164 : W := mkw 0x04f7ea000fdbe088 0xf6fffe403ffff380

def z1165 : W := mkw 0x08ee8decf0000000 0x0044cfcef8000000

def z1166 : W := mkw 0x0813bc15f0000000 0x8803fe7ff8000000

def z1167 : W := mkw 0x02ee81eaa6b40f60 0x7fff01fec7fc0ff0

def z1168 : W := mkw 0x81004202090e31bc 0x73440000031e73fc

def z1169 : W := mkw 0x00c28140ae010a8a 0x39c301c1ff018f8f

def z1170 : W := mkw 0x022c00aa00b40560 0x573c003e03fc03f0

def z1171 : W := mkw 0x08ffbdfdf0000000 0xc4bfffbff8000000

def z1172 : W := mkw 0x08ee9dfdf0000000 0xa8c7cffff8000000

def z1173 : W := mkw 0x0837bc1df0000000 0x8007fe0ff8000000

def z1174 : W := mkw 0x04f7ea000fdbe08a 0xf6fffe0007fff00f

def z1175 : W := mkw 0x81005617190f31be 0xfb44fe7f3b1ff3ff

def z1176 : W := mkw 0x0ce68d4cb6910000 0x0044ce4e38000000

def z1177 : W := mkw 0xc8ffbdfdf060d455 0xfffffffffce07c70

def z1178 : W := mkw 0x030042020f9e2ba8 0x00000000031c0380

def z1179 : W := mkw 0x08f7ad4cb0000000 0x8047fe4e38000000

def z1180 : W := mkw 0xc1004202092e35fd 0x13000000031e7fff

def z1181 : W := mkw 0x04f7ea0007dbea00 0xf7fffe0007ffff80

def z1182 : W := mkw 0x04f52b4006d8ea00 0x7ffc3fc007fc7f80

def z1183 : W := mkw 0x48ffbdfdf040c001 0xecfffffff8018003

def z1184 : W := mkw 0x48ffbdfdf0200441 0xecfffffff8000c03

def z1185 : W := mkw 0xc01930b14060d455 0xfffb31f1c7e3ffff

def z1186 : W := mkw 0x81004202090e31bc 0xbb830181c71fffff

def z1187 : W := mkw 0xc0dbf5f5ff63dedf 0xffffffffffe3ffff

def z1188 : W := mkw 0xc1004202094ef1bd 0x13000000031ff3ff

def z1189 : W := mkw 0xca3d3cbf50f4d575 0x463c3e3e00fc7070

def z1190 : W := mkw 0x8513fe15b94bf09e 0x8003fe01f803f00f

def z1191 : W := mkw 0x48ffadecf060c441 0x04ffcfcefce18c03

def z1192 : W := mkw 0x04356a000fdbea8a 0x573c3e0007ffff8f

def z1193 : W := mkw 0x83ec43ea0fbe3ffc 0x17b8018007fe7ffc

def z1194 : W := mkw 0x00e4014206940b20 0x7ffc01fe07fc0ff0

def z1195 : W := mkw 0x810042020f0f3bbe 0x13000000031e73fc

def z1196 : W := mkw 0x08e68d4cb6900000 0x0044ce4e3b1c0000

def z1197 : W := mkw 0x00000140a8000a8a 0x098301c1fc018f8f

def z1198 : W := mkw 0x830814bf10241574 0x0000003e00000070

def z1199 : W := mkw 0x0000141510000000 0xfb44fe7f38000070

def z1200 : W := mkw 0x00c28140ae010a8a 0xa9c3c1c1fc018f8f

def z1201 : W := mkw 0x04f7ea0007dbe000 0xfffffe4007fff380

def z1202 : W := mkw 0x001934b550000000 0xec7cfe7f38000000

def z1203 : W := mkw 0x81005617190e31bc 0x5344fe7e3b1e73fc

def z1204 : W := mkw 0xc81935fdf060d455 0xfffffffffce3fc7f

def z1205 : W := mkw 0x08ffbdfdf0000a02 0xecfffffff8000c03

def z1206 : W := mkw 0x830815ff10241f74 0x090001fe00000ff0

def z1207 : W := mkw 0x04f7ea0007dbe000 0x84fffe0007fff000

def z1208 : W := mkw 0xc33d36bf50fcf575 0x463c3e3e00fc7070

def z1209 : W := mkw 0x08ffbdfdf040c000 0xecfffffff803f000

def z1210 : W := mkw 0x0cf7ad4cb6d1c000 0x04ffce4e3ce18000

def z1211 : W := mkw 0x88ffbdfdf0001014 0xeefffffff8007070

def z1212 : W := mkw 0x00e6c200079b2000 0xf6fffe0007fff000

def z1213 : W := mkw 0xc8ffbdfdf0001015 0xecfffffff800000f

def z1214 : W := mkw 0x00c801e206240f60 0x7ffc01fe07fc0ff0

def z1215 : W := mkw 0x02ee81ea06b40f60 0xffffc1fe07fc0ff0

def z1216 : W := mkw 0x0437ea0007dbe000 0xd63ffe0007fff000

def z1217 : W := mkw 0x08e68d4cb0000000 0xe044fe4e38000000

def z1218 : W := mkw 0x08ffbdfdf0000000 0xfdfffffffc000c00

def z1219 : W := mkw 0x00e4020006982000 0x76fc3e0007fc7000

def z1220 : W := mkw 0x85004202094ff1bc 0x13000000031ff3fc

def z1221 : W := mkw 0x06e6cb4aaf9f2baa 0x0044ce4e3b1c0380

def z1222 : W := mkw 0x08fd3dfd50000000 0xecfcffff38000000

def z1223 : W := mkw 0x08ffbdfdf0000000 0x84ffffcff8000000

def z1224 : W := mkw 0x04f7aa0006d8e000 0xf6fffe0007fc7000

def z1225 : W := mkw 0x08e68d4cb6010a02 0x00c7cfcefc018c03

def z1226 : W := mkw 0x081bbdfdf0000000 0xecbbfffff8000000

def z1227 : W := mkw 0xc0fd35fd5060d455 0xfffffffffce3fc7f

def z1228 : W := mkw 0x00c2c140af030a8a 0x09c3c1c1ff018f8f

def z1229 : W := mkw 0x810052130f0f3bbe 0xfb8331b1c71fffff

def z1230 : W := mkw 0x81005213090e31bc 0x93003001031e73fc

def z1231 : W := mkw 0x08ffbdfdf0000a00 0xedfffffff8000f80

def z1232 : W := mkw 0x08028c04b0000000 0x0044ce4e38000000

def z1233 : W := mkw 0x02ec01ea06b40f60 0x46fc01fe07fc0ff0

def z1234 : W := mkw 0x08028d4cb0000000 0x0000ce4e38000000

def z1235 : W := mkw 0x000814b550000000 0xe844fffff8000000

def z1236 : W := mkw 0x08ffadecf0000000 0x6cffcffef8000000

def z1237 : W := mkw 0xc8f7bd5df040d015 0x8047fe4ff803f00f

def z1238 : W := mkw 0x02ec01ea06b40f60 0x6efc01fe03fc03f0

def z1239 : W := mkw 0x08001415f0000000 0xe844fe7ff8000000

def z1240 : W := mkw 0x01004606190e21a8 0xfb44fe7e3b1e73f0

def z1241 : W := mkw 0x08e69d5db0000000 0x4044fe7e38000000

def z1242 : W := mkw 0x81005617190e31bc 0xfffcfe7f3ffe73fc

def z1243 : W := mkw 0x81004202090e31bc 0x7b000030031e73fc

def z1244 : W := mkw 0xc8ffbdfdf060d455 0xeefffffffce1fc73

def z1245 : W := mkw 0x08ffbdfdf6000a00 0xecfffffffc000c00

def z1246 : W := mkw 0x08ffbdfdf0000000 0xc47ffe7ff8000000

def z1247 : W := mkw 0x00c28544b0000000 0x0044ce4e38000000

def z1248 : W := mkw 0x00c2c140af930a8a 0xbbc3c1c1ffff8f8f

def z1249 : W := mkw 0x85f7ea020fdff1bc 0x17bb000007fff3fc

def z1250 : W := mkw 0x00005617110e2120 0xfb44fe7f3b1e73f0

def z1251 : W := mkw 0x000800a000200440 0x7ffc01fe04e00c70

def z1252 : W := mkw 0x04352a0006d8e000 0x563c3e0007fc7000

def z1253 : W := mkw 0x04e6cb40af9b2a8a 0xffffcfc1ffff8f8f

def z1254 : W := mkw 0x02ee81eaa6b50f62 0xffff01ffc7ff8fff

def z1255 : W := mkw 0x00dbb5f5f0000000 0xecfffffff8000000

def z1256 : W := mkw 0x020801ea06b40f60 0x7fb801fe07fc0ff0

def z1257 : W := mkw 0x04f7ea0007dbe000 0xf6ffff80c7fffc03

def z1258 : W := mkw 0x04f52a0000d8e000 0x66fc3e0000fc7000

def z1259 : W := mkw 0x000814b510200440 0xfffcffff3ce00c70

def z1260 : W := mkw 0x02ee81ea06b50f60 0x7fff01fe07fd8ff0

def z1261 : W := mkw 0x083d3cbd50000000 0xecfffffff8000000

def z1262 : W := mkw 0x0cffbdfdf6910000 0xecfffffff8000000

def z1263 : W := mkw 0x0affbdfdf6b00e40 0xfffffffffce00c70

def z1264 : W := mkw 0x08240c0c10000000 0x0044ce4e38000000

def z1265 : W := mkw 0x00c29555b0000000 0xe844fe7f38000000

def z1266 : W := mkw 0xc01930b14060d455 0xffff31b1c7fffc7f

def z1267 : W := mkw 0x8000141510001014 0xe944fe7f3800007c

def z1268 : W := mkw 0x020801ea00240f60 0x7ffc01fe07fc0ff0

def z1269 : W := mkw 0x02ec01ea06b40f60 0x7ffc01fe07ff8fff

def z1270 : W := mkw 0xc10815f7f8241fff 0x090001fff8000fff

def z1271 : W := mkw 0x04c2cb40af0b2a8a 0xb9c3cfc1ff038f8f

def z1272 : W := mkw 0x081935fdf0000000 0xecfffffff8000000

def z1273 : W := mkw 0xc00814b550201455 0x090001fff8000c7f

def z1274 : W := mkw 0x00c2c140af030a8a 0x8983c1c1fc038f8f

def z1275 : W := mkw 0x08f7bc15f0000000 0xecfffe7ff8000000

def z1276 : W := mkw 0xc8ffbdfdf060d455 0x467cfe7e38e07070

def z1277 : W := mkw 0x080815fdf0000000 0x8800fffff8000000

def z1278 : W := mkw 0x0800054cb0000000 0x0044ce4e38000000

def z1279 : W := mkw 0xc1117615594af09d 0x8000fe013802700c

def z1280 : W := mkw 0xc10042020f6fffff 0x1300000007ffffff

def z1281 : W := mkw 0x00c041400f020a88 0xb9c3c1c1ff038f8f

def z1282 : W := mkw 0x08ffbdfdf6900000 0xecfffffffb1c0000

def z1283 : W := mkw 0x88ffbdfdf0001014 0xecfffffff802700c

def z1284 : W := mkw 0x02ec01ea06b40f60 0x0dfc01fe07fc0ff0

def z1285 : W := mkw 0x08e68d4cb0000000 0x8047ce4ff8000000

def z1286 : W := mkw 0x0437aa0000d8e000 0xc63ffe0000fc7000

def z1287 : W := mkw 0x04f7eb40a7dbea02 0xf6fffe0007fff000

def z1288 : W := mkw 0x81e442020f9e31bc 0x77fc000007fe73fc

def z1289 : W := mkw 0x083fbcbdf0000000 0x443cfe3e38000000

def z1290 : W := mkw 0xc01930b14060d455 0x57bb31b0c4e3fc7f

def z1291 : W := mkw 0x8500420209def1bc 0x1300000003fe73fc

def z1292 : W := mkw 0x00c28140ae010a8a 0xb98301c1fc038f8f

def z1293 : W := mkw 0x00e6c140af030a8a 0xfdffc1c1ff038f8f

def z1294 : W := mkw 0x02e4014a06940b20 0x00000000031c0380

def z1295 : W := mkw 0x08ee9dfdb0000000 0xecfcffff38000000

def z1296 : W := mkw 0x02ec01ea06b40f60 0x57bc01be07fc0ff0

def z1297 : W := mkw 0x04f7eb40afdbea8a 0xfeffffc1fffff380

def z1298 : W := mkw 0x81004202090e31bc 0x3b400040031e73fc

def z1299 : W := mkw 0xc83fbcbdf060d455 0xc63ffe3ff8e3f07f

def z1300 : W := mkw 0x0affbdfdf0b00440 0xecfffffff8e00000

def z1301 : W := mkw 0x04f7eb400fdbea88 0xffffffc13fffff8c

def z1302 : W := mkw 0x88ffbdfdf0001014 0xedfffffff800007c

def z1303 : W := mkw 0x04f7eb40afdbe088 0xffffffc1fffff38c

def z1304 : W := mkw 0x00004140af030a8a 0xb98301c1ff038f8f

def z1305 : W := mkw 0x08ffbdfdf0000000 0x8cbbfffff8000000

def z1306 : W := mkw 0x08f7ad4cb0000000 0x04ffce4e38000000

def z1307 : W := mkw 0x02ec01ea06b40f60 0x577c007e07fc0ff0

def z1308 : W := mkw 0x01004202090e21a8 0x12000000031e7380

def z1309 : W := mkw 0x04f7aa0000d8e000 0x46bf3e0000fc7000

def z1310 : W := mkw 0x0437ea0001dbe000 0xf67ffe0003fff000

def z1311 : W := mkw 0x0000141510000000 0xfa44fe7f38027000

def z1312 : W := mkw 0xc11972b34f6fffff 0xffbb31b1c7ffffff

def z1313 : W := mkw 0x02ec01ea06b40f60 0x7f7c007e03fc03f0

def z1314 : W := mkw 0x04f7ea0001dae000 0xf6fffe0003fe7000

def z1315 : W := mkw 0xc8ffbdfdf6f0d455 0xfffffffffffffc7f

def z1316 : W := mkw 0x0413ea0007dbe000 0xf6bbfe0007fff000

def z1317 : W := mkw 0x04f52a0006d8e000 0xf6ff3e0007fff000

def z1318 : W := mkw 0x00f7ea00079a2000 0xf6fffe0007fe7000

def z1319 : W := mkw 0x00e69c1510000000 0xe844fe7f38000000

def z1320 : W := mkw 0x0013bc1510000000 0xe847fe7f38000000

def z1321 : W := mkw 0x02ec01eaa6b40f62 0x7ffc01fec7fc0ff3

def z1322 : W := mkw 0x050042020f9f21a8 0x00000000031c0380

def z1323 : W := mkw 0xc1cad5f7ff271fff 0xb9c3c1ffff038fff

def z1324 : W := mkw 0x081bbcb5f0000000 0xecfffffff8000000

def z1325 : W := mkw 0x48ffbdfdf060c441 0xecfffffff8e00000

def z1326 : W := mkw 0x00fd35fd50000000 0xecfffffff8000000

def z1327 : W := mkw 0x04f7ea00afdbe08a 0xffffff81fffffc0f

def z1328 : W := mkw 0xc8ffbdfdf0201455 0xfffffffff8027c7f

def z1329 : W := mkw 0x08268c0cb0000000 0x0004ce0e38000000

def z1330 : W := mkw 0xc8ffbdfdf040d015 0xfffffffff803f07f

def z1331 : W := mkw 0xc8ffbdfdf660de55 0xffffffffffe3ffff

def z1332 : W := mkw 0x00d3e340af4bea8a 0xffffffc1ffffff8f

def z1333 : W := mkw 0x810042020f9e31bc 0x1300000007fe73fc

def z1334 : W := mkw 0x04f7eb40afdbea8a 0xf6fffe41fffff38f

def z1335 : W := mkw 0x08ffbdfdf0010002 0xecfffffff8018003

def z1336 : W := mkw 0x04352a0000d8e000 0x46bf3e0004fdf000

def z1337 : W := mkw 0x0effa9e8e6f1ce40 0x04bb0180c4e18c00

def z1338 : W := mkw 0x04f7aa0006d9e000 0x76ff3e0007fdf000

def z1339 : W := mkw 0x04356a0001dae000 0xf6fffe0007fff000

def z1340 : W := mkw 0x00c2c340af0b2a8a 0xb9c7cfc1ff1f8f8f

def z1341 : W := mkw 0x04f7eb40a7dbe000 0xffffffc1fffffc0f

def z1342 : W := mkw 0x04352a0000d8e000 0xffbf3f81c4fffc0f

def z1343 : W := mkw 0x00c2c140af030a8a 0x8943c1c1fb038f8f

def z1344 : W := mkw 0x04f7ea000fdbe088 0xf6fffe013ffff00c

def z1345 : W := mkw 0x001122000048e000 0xf6bf3e0004fff000

def z1346 : W := mkw 0x08e68d4cb0000000 0x64fcce4e38000000

def z1347 : W := mkw 0x81004202090e31bc 0x02000000001e707c

def z1348 : W := mkw 0x08d3bd55f0000000 0xe8c7fffff8000000

def z1349 : W := mkw 0x00c2941510000000 0xe8c7fe7f38000000

def z1350 : W := mkw 0xc83d3cbd5060d455 0xff7cfe7f38e2707c

def z1351 : W := mkw 0x00c2c140a9030a8a 0xa9c3c1c1f8038f8f

def z1352 : W := mkw 0x08ffbdfdf0000000 0xecfffffff803800f

def z1353 : W := mkw 0x08ffbdfdf0200440 0xedfffffff8000c70

def z1354 : W := mkw 0x08ffbdfdf0000000 0xec7cfe7f38000000

def z1355 : W := mkw 0x08ffbdfdf0000000 0xfefffffffce00000

def z1356 : W := mkw 0x00ffbdfd10000000 0xecffffff38000000

def z1357 : W := mkw 0x00c00140ae000a8a 0xb9c301c1ff038f8f

def z1358 : W := mkw 0x00116200014ae000 0xf67cfe0003fe7000

def z1359 : W := mkw 0x08ffbdfdf0000000 0xe4fffe7e38000000

def z1360 : W := mkw 0xc1005617590e31bd 0xfb44fe7ffb1e73ff

def z1361 : W := mkw 0xc8ffbdfdf060d455 0xecfffffffce3fc0f

def z1362 : W := mkw 0x010042020f0f2baa 0x00000000031c0380

def z1363 : W := mkw 0x00116200094ae088 0xffffffc1ffffff8f

def z1364 : W := mkw 0x04352a0000d8e000 0xc63f3e0000fff000

def z1365 : W := mkw 0x08f7bd5df0000000 0x0044fe4e38000000

def z1366 : W := mkw 0x0affbdfdf6b00e40 0xfdffffffffe00f80

def z1367 : W := mkw 0x0002c000a903008a 0xb9c3c1c1ff038f8f

def z1368 : W := mkw 0x81005617190e31bc 0xc244fe7f3b1e73fc

def z1369 : W := mkw 0x08ffbdfdf6010000 0xecfffffffc018000

def z1370 : W := mkw 0x81004202090e3bbe 0x13000000031e7fff

def z1371 : W := mkw 0x0effbdfdf6f1ce40 0xecfffffffce18c00

def z1372 : W := mkw 0x0cffbdfdf6d1c000 0xfefffffffffd8000

def z1373 : W := mkw 0x00ec00a206b40560 0x7ffc01fe07fc0ff0

def z1374 : W := mkw 0x08ffbdfdf6010a02 0xfdfffffffc038c0f

def z1375 : W := mkw 0x04f7ea0007dbe000 0xfffffe0107fff00c

def z1376 : W := mkw 0x08ffadecf0000000 0xe4ffffcef8000000

def z1377 : W := mkw 0xc8ee9dfdf0201455 0x0944cffff8000c7f

def z1378 : W := mkw 0x0affbdfdf0200e40 0xecfffffff8000c00

def z1379 : W := mkw 0x00f7ac0410000000 0xe4fffe4e38000000

def z1380 : W := mkw 0x81004202090e31bc 0xf3003000031e73fc

def z1381 : W := mkw 0xc0dbb5f5f060d455 0xfffffffffce3fc7f

def z1382 : W := mkw 0x00c2c140af030a8a 0xfbc3f1c1ff03ff8f

def z1383 : W := mkw 0x04e6cb40af9b2a8a 0xfbc7ffc1ff1fff8f

def z1384 : W := mkw 0x08e68d4cb0000000 0xa844ce4f38000000

def z1385 : W := mkw 0xc00814b550201455 0xe944fffff8000c7f

def z1386 : W := mkw 0x0437aa0000d9e000 0x463f3e0000fdf000

def z1387 : W := mkw 0x00000140a8000a8a 0x890301c1f8038f8f

def z1388 : W := mkw 0x010042020f0f2baa 0x11000000071f8f8f

def z1389 : W := mkw 0x08e68d4cb0000000 0xa0c7ce4e38000000

def z1390 : W := mkw 0x08ee8decb0000000 0x447cce7e38000000

def z1391 : W := mkw 0x02ec01ea06b40f60 0xffff01ffc7fc0ff0

def z1392 : W := mkw 0x02ec01ea06b40f60 0x76fc007e07fc03f0

def z1393 : W := mkw 0x001134151040c000 0xfefffe7f3ce3f000

def z1394 : W := mkw 0x81116202094ef1bc 0xf7bb300007fff3fc

def z1395 : W := mkw 0x04f7bc1516d1c000 0xecfffe7f3ce18000

def z1396 : W := mkw 0xc01134155040d015 0xe847fe7ff803f00f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z3,z4,z6]),(0,[z9,z0,z1,z2,z10,z4,z6])],[(0,[z0,z1,z2,z3,z4,z11,z6])],[],[(0,[z0,z1,z2,z3,z4,z6,z12]),(0,[z0,z1,z13,z2,z3,z4,z6])],[(0,[z0,z1,z2,z10,z14,z4,z6]),(0,[z0,z1,z2,z3,z15,z4,z6])],[(0,[z0,z1,z16,z2,z3,z4,z6]),(0,[z17,z0,z1,z2,z3,z4,z18])],[(0,[z19,z20,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z22])],[(0,[z0,z1,z2,z23,z4,z24,z6]),(0,[z0,z25,z1,z2,z26,z4,z6]),(0,[z0,z1,z27,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z28])],[(0,[z0,z29,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z30,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z2,z3,z31,z4,z6])],[(0,[z32,z0,z1,z2,z3,z4,z6]),(0,[z33,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z34,z2,z3,z4,z6])],[(0,[z35,z0,z1,z36,z3,z4,z6]),(0,[z0,z1,z37,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z39,z6]),(0,[z17,z0,z1,z2,z21,z4,z6]),(1,[z0,z1,z2,z4,z6,z40])],[(0,[z41,z42,z0,z1,z2,z4,z6]),(0,[z1,z43,z2,z38,z3,z4,z6]),(0,[z0,z1,z2,z44,z3,z4,z6]),(0,[z0,z45,z1,z2,z4,z46,z6]),(0,[z0,z1,z2,z3,z4,z6,z47]),(0,[z41,z0,z48,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z49,z4,z6])],[(0,[z50,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z51,z2,z3,z4,z6]),(0,[z52,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z53,z2,z3,z4,z6]),(0,[z0,z1,z2,z54,z4,z6,z55]),(0,[z0,z56,z1,z2,z3,z4,z6])],[(1,[z57,z1,z2,z3,z4,z6]),(0,[z0,z58,z1,z2,z3,z4,z6]),(0,[z0,z1,z53,z59,z3,z4,z6]),(0,[z0,z1,z2,z60,z21,z4,z6])]],
   [[(0,[z41,z0,z1,z61,z2,z4,z6]),(0,[z0,z1,z2,z3,z62,z4,z6])],[(0,[z0,z1,z53,z2,z4,z6,z55]),(0,[z63,z0,z1,z2,z3,z4,z6])],[(0,[z41,z0,z1,z2,z4,z24,z6]),(0,[z0,z61,z2,z64,z3,z4,z6]),(1,[z0,z65,z1,z3,z4,z6]),(0,[z0,z66,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z67,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z68]),(0,[z41,z0,z69,z1,z2,z4,z6])],[(0,[z0,z1,z2,z3,z70,z4,z6]),(0,[z0,z1,z2,z71,z3,z4,z6])],[(0,[z72,z0,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z73,z21,z4,z6]),(1,[z0,z1,z2,z3,z74,z6]),(0,[z0,z1,z2,z3,z4,z6,z75]),(0,[z0,z1,z2,z3,z4,z6,z76]),(0,[z0,z1,z2,z3,z4,z6,z77])],[(0,[z0,z1,z2,z3,z4,z78,z6]),(0,[z0,z1,z2,z79,z3,z4,z6]),(0,[z0,z80,z81,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z82,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z83])],[(0,[z0,z1,z38,z3,z4,z84,z6]),(0,[z0,z85,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z64,z3,z4,z6])],[(0,[z86,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z87,z2,z3,z4,z6]),(0,[z88,z0,z1,z2,z10,z4,z6]),(1,[z0,z80,z2,z89,z4,z6])],[(0,[z0,z81,z90,z2,z3,z4,z6]),(1,[z41,z0,z1,z38,z4,z6]),(0,[z0,z1,z2,z91,z3,z4,z6]),(0,[z92,z0,z2,z3,z4,z6,z93]),(0,[z0,z1,z2,z21,z4,z94,z6])],[(0,[z95,z0,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z96,z55]),(0,[z0,z1,z2,z64,z4,z6,z55]),(0,[z0,z1,z2,z3,z4,z97,z55]),(0,[z0,z1,z2,z98,z3,z4,z6]),(0,[z0,z1,z2,z99,z4,z100,z6])],[(1,[z101,z1,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z6,z102])],[(0,[z42,z0,z1,z2,z10,z4,z6]),(0,[z0,z25,z2,z3,z103,z4,z6]),(0,[z0,z1,z104,z2,z3,z4,z6])],[(0,[z0,z1,z61,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z94,z6]),(0,[z0,z1,z2,z4,z6,z55,z105])],[(0,[z41,z0,z1,z43,z3,z4,z6]),(0,[z106,z0,z1,z2,z3,z4,z6])],[(0,[z0,z107,z1,z38,z3,z4,z6]),(1,[z0,z1,z2,z108,z4,z6])]],
   [[(0,[z0,z1,z109,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z110]),(0,[z0,z1,z111,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z112,z6]),(0,[z0,z1,z2,z3,z113,z4,z6])],[(0,[z0,z1,z2,z10,z4,z24,z6]),(0,[z41,z0,z1,z2,z4,z18,z6])],[(0,[z0,z114,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z115]),(0,[z0,z116,z1,z2,z3,z4,z6])],[(0,[z117,z92,z0,z2,z3,z4,z6]),(0,[z118,z0,z1,z2,z3,z4,z119])],[(0,[z0,z1,z2,z99,z21,z4,z6])],[(0,[z0,z120,z1,z2,z3,z4,z6])],[(0,[z0,z121,z1,z2,z3,z4,z6]),(0,[z0,z122,z1,z2,z3,z14,z6])],[(0,[z0,z1,z2,z3,z4,z123,z6]),(0,[z124,z0,z1,z67,z3,z4,z6]),(2,[z0,z1,z2,z4,z40])],[(0,[z88,z0,z1,z2,z73,z4,z6]),(0,[z125,z0,z1,z16,z3,z4,z6])],[(0,[z126,z0,z1,z2,z127,z4,z6]),(1,[z0,z1,z2,z4,z6,z128]),(0,[z0,z1,z2,z129,z3,z4,z6]),(1,[z130,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z131]),(0,[z0,z1,z2,z3,z4,z132,z6])],[(0,[z0,z1,z2,z3,z133,z4,z6]),(0,[z0,z1,z2,z3,z4,z134,z6])],[(0,[z0,z1,z2,z135,z4,z6,z55]),(0,[z0,z1,z2,z4,z6,z55,z136])],[(0,[z0,z1,z2,z3,z4,z137,z6]),(0,[z0,z1,z2,z3,z4,z138,z6]),(0,[z0,z1,z2,z3,z4,z6,z139])],[(0,[z0,z1,z43,z3,z103,z4,z6]),(1,[z0,z140,z1,z54,z4,z6]),(0,[z0,z1,z141,z3,z4,z84,z6])],[(0,[z0,z1,z2,z3,z142,z4,z6]),(0,[z0,z1,z2,z3,z143,z4,z6]),(0,[z144,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z126,z41,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z145]),(0,[z41,z0,z1,z146,z2,z4,z6])],[(0,[z0,z1,z43,z3,z4,z6,z147]),(0,[z0,z1,z2,z148,z3,z4,z6])],[(0,[z149,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z38,z21,z4,z6]),(0,[z41,z0,z1,z2,z150,z4,z6]),(0,[z41,z125,z0,z1,z2,z4,z6]),(0,[z0,z151,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z152,z4,z6,z55])],[(0,[z35,z0,z1,z2,z21,z4,z6]),(0,[z19,z0,z1,z38,z3,z4,z6]),(0,[z0,z122,z1,z43,z3,z4,z6])],[(0,[z0,z153,z1,z38,z3,z4,z6]),(1,[z0,z1,z154,z3,z4,z6]),(1,[z0,z45,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z155]),(0,[z0,z1,z2,z156,z3,z4,z6]),(0,[z0,z1,z2,z3,z152,z4,z55])],[(0,[z0,z1,z2,z3,z4,z6,z157]),(0,[z0,z1,z2,z3,z4,z6,z158])],[(0,[z35,z0,z1,z43,z3,z4,z6]),(0,[z0,z1,z2,z159,z3,z4,z6]),(0,[z0,z122,z1,z2,z3,z4,z97])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z125,z0,z1,z2,z21,z4,z6])],[(0,[z35,z90,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z160,z3,z4,z6]),(0,[z161,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z162,z3,z4,z6]),(0,[z41,z0,z1,z2,z59,z4,z6]),(1,[z19,z0,z1,z3,z163,z6]),(0,[z164,z0,z1,z2,z3,z4,z6])],[(0,[z165,z0,z1,z2,z3,z4,z6]),(0,[z125,z0,z1,z43,z3,z4,z6]),(0,[z0,z1,z43,z3,z4,z6,z96]),(0,[z166,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z37,z2,z108,z4,z6]),(1,[z0,z1,z2,z4,z6,z55])],[(0,[z0,z1,z2,z21,z4,z167,z6])],[(0,[z0,z168,z1,z2,z3,z4,z6]),(0,[z0,z169,z1,z38,z3,z4,z6]),(1,[z0,z1,z2,z170,z4,z6])],[(0,[z126,z0,z1,z38,z3,z4,z6]),(0,[z0,z1,z171,z2,z3,z4,z6])],[(0,[z0,z1,z2,z172,z3,z4,z6]),(0,[z118,z0,z1,z2,z3,z4,z6])],[(0,[z17,z0,z1,z173,z3,z4,z6]),(0,[z174,z0,z1,z2,z3,z4,z6]),(0,[z0,z80,z1,z2,z135,z4,z6]),(0,[z0,z175,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z167,z6])]],
   [[(0,[z0,z1,z2,z3,z176,z4,z6]),(0,[z9,z0,z1,z2,z3,z4,z6])],[(0,[z177,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z178,z4,z6]),(0,[z118,z0,z1,z2,z10,z4,z6])],[(0,[z179,z124,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z180,z3,z4,z6])],[(0,[z181,z0,z1,z2,z3,z4,z6])],[],[(0,[z0,z107,z1,z61,z3,z4,z6]),(0,[z0,z1,z2,z182,z3,z4,z6])],[(0,[z183,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z135,z3,z89,z4,z6]),(1,[z0,z1,z2,z3,z4,z134]),(0,[z184,z0,z1,z2,z3,z4,z6])],[(0,[z0,z185,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z186,z4,z6]),(0,[z0,z1,z187,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z188,z4,z6])],[(0,[z124,z0,z1,z2,z189,z4,z6]),(0,[z41,z0,z122,z1,z2,z4,z6])],[(1,[z0,z1,z190,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z191])],[(0,[z0,z1,z2,z3,z192,z4,z6]),(0,[z0,z193,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z194,z4,z6])],[],[(0,[z0,z1,z38,z3,z4,z6,z195]),(0,[z196,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z37,z2,z197,z4,z6]),(0,[z0,z1,z2,z10,z4,z6,z198]),(0,[z0,z1,z2,z4,z6,z199,z55]),(0,[z0,z1,z2,z49,z4,z6,z55])],[],[(1,[z1,z38,z3,z4,z24,z6]),(0,[z125,z0,z1,z2,z150,z4,z6]),(0,[z0,z1,z2,z14,z21,z4,z6])],[(0,[z0,z80,z2,z3,z89,z4,z6]),(0,[z0,z1,z2,z21,z4,z84,z6]),(0,[z0,z1,z2,z3,z200,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z201,z4,z6]),(0,[z0,z1,z2,z4,z6,z6,z55])],[(0,[z202,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z36,z3,z4,z6]),(0,[z203,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z204,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z205])],[(0,[z0,z81,z206,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z207,z6]),(0,[z208,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z53,z43,z3,z4,z6]),(0,[z0,z25,z107,z2,z3,z4,z6]),(0,[z0,z1,z37,z2,z3,z4,z6]),(0,[z0,z209,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z84,z6]),(0,[z0,z1,z2,z4,z119,z6,z55])],[],[(1,[z0,z209,z2,z3,z4,z6]),(0,[z0,z1,z37,z2,z4,z6,z55]),(0,[z0,z1,z37,z2,z10,z4,z6]),(0,[z210,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z178,z21,z4,z6]),(0,[z0,z1,z2,z3,z4,z119,z97])],[(0,[z0,z1,z2,z3,z4,z211,z6]),(0,[z0,z1,z38,z3,z89,z4,z6]),(0,[z0,z1,z38,z3,z212,z4,z6]),(0,[z0,z1,z2,z3,z213,z4,z6]),(0,[z0,z1,z2,z214,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z215]),(0,[z0,z1,z59,z3,z54,z4,z6]),(0,[z0,z1,z2,z216,z21,z4,z6])],[(1,[z0,z1,z217,z3,z4,z6]),(0,[z0,z1,z218,z2,z3,z4,z6]),(0,[z88,z0,z1,z2,z3,z4,z6]),(0,[z0,z219,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z99,z6,z97])],[(0,[z0,z1,z2,z3,z4,z220,z6])],[(0,[z0,z169,z1,z2,z129,z4,z6])],[(0,[z0,z1,z43,z38,z3,z4,z6]),(0,[z221,z0,z1,z2,z3,z4,z6]),(0,[z222,z0,z1,z2,z3,z4,z6]),(0,[z88,z0,z1,z2,z4,z6,z55])],[(0,[z42,z0,z1,z2,z3,z4,z6]),(0,[z86,z0,z1,z43,z3,z4,z6]),(0,[z223,z0,z1,z2,z3,z4,z6]),(0,[z0,z48,z1,z2,z3,z4,z6])],[(1,[z1,z38,z3,z4,z18,z6]),(0,[z92,z0,z1,z38,z3,z4,z6]),(0,[z224,z0,z1,z2,z3,z4,z6]),(0,[z0,z225,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z226,z3,z4,z6]),(0,[z227,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z228,z6]),(0,[z72,z0,z1,z2,z10,z4,z6]),(0,[z41,z0,z1,z2,z21,z4,z6]),(1,[z229,z0,z1,z3,z4,z6])],[(0,[z42,z0,z1,z2,z4,z6,z55]),(0,[z126,z17,z1,z2,z3,z4,z6]),(0,[z0,z25,z1,z61,z3,z4,z6]),(0,[z0,z1,z2,z89,z54,z4,z6])]],
   [[(0,[z42,z1,z206,z2,z3,z4,z6]),(0,[z0,z1,z43,z3,z89,z4,z6]),(0,[z0,z1,z230,z2,z3,z4,z6]),(0,[z0,z1,z231,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z99,z4,z6]),(0,[z0,z1,z232,z2,z3,z4,z6])],[(1,[z0,z1,z233,z3,z4,z6]),(0,[z0,z81,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z234,z3,z4,z6]),(0,[z117,z0,z61,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z235,z6])],[(0,[z0,z1,z2,z3,z4,z236,z6]),(0,[z0,z1,z237,z2,z3,z4,z6]),(0,[z41,z17,z0,z1,z2,z4,z6])],[(0,[z238,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z239,z3,z4,z6]),(0,[z0,z1,z2,z4,z240,z6,z55]),(0,[z95,z0,z1,z2,z10,z4,z6]),(0,[z241,z0,z1,z2,z3,z4,z6])],[(0,[z0,z242,z1,z2,z3,z4,z6])],[(1,[z0,z1,z243,z3,z4,z6])],[(0,[z0,z69,z206,z2,z3,z4,z6]),(0,[z0,z1,z61,z2,z10,z4,z6])],[(0,[z0,z0,z1,z38,z3,z4,z6]),(0,[z0,z244,z1,z38,z3,z4,z6]),(0,[z0,z1,z38,z3,z103,z4,z6]),(0,[z0,z245,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z10,z246,z4,z6])],[(0,[z0,z1,z2,z3,z4,z247,z6]),(0,[z0,z107,z1,z2,z10,z4,z6]),(0,[z0,z1,z248,z2,z3,z4,z6])],[(1,[z0,z1,z16,z3,z4,z6]),(0,[z249,z41,z0,z1,z2,z4,z6])],[(0,[z88,z0,z1,z190,z3,z4,z6]),(0,[z0,z1,z2,z3,z23,z4,z6]),(0,[z0,z1,z250,z2,z3,z4,z6]),(0,[z0,z1,z2,z135,z21,z4,z6]),(1,[z0,z169,z2,z3,z103,z6]),(0,[z0,z1,z2,z3,z4,z251,z6]),(0,[z0,z1,z3,z4,z6,z83,z97])],[(0,[z0,z1,z206,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z252,z4,z6]),(0,[z0,z65,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z4,z6,z253]),(0,[z0,z1,z2,z3,z4,z6,z254]),(0,[z0,z1,z2,z3,z4,z6,z199])],[(0,[z0,z1,z43,z3,z255,z4,z6]),(0,[z0,z1,z2,z256,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z257,z6]),(0,[z0,z1,z2,z258,z3,z4,z6]),(0,[z0,z1,z2,z3,z259,z4,z6]),(0,[z0,z1,z2,z10,z21,z4,z6]),(0,[z0,z1,z2,z10,z3,z4,z55])],[(0,[z0,z1,z2,z3,z260,z4,z6]),(1,[z0,z122,z1,z2,z3,z152])],[(0,[z0,z1,z2,z10,z99,z4,z6])]],
   [[],[(1,[z0,z1,z2,z261,z4,z6]),(0,[z0,z81,z1,z2,z89,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z105]),(0,[z0,z1,z2,z3,z4,z6,z262])],[(0,[z0,z1,z2,z263,z3,z4,z6])],[(0,[z0,z1,z38,z3,z4,z6,z96]),(0,[z0,z1,z2,z10,z4,z18,z6]),(0,[z0,z1,z37,z2,z3,z163,z6]),(0,[z0,z1,z2,z3,z264,z4,z6]),(0,[z0,z122,z1,z2,z21,z4,z6])],[(0,[z0,z1,z2,z4,z24,z6,z55]),(0,[z0,z1,z2,z3,z60,z4,z6])],[(0,[z0,z69,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z265,z4,z6]),(0,[z95,z0,z1,z3,z4,z6,z198]),(0,[z1,z141,z204,z2,z3,z4,z6])],[(0,[z117,z0,z90,z2,z3,z4,z6])],[],[(0,[z0,z266,z1,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z267,z4,z6])],[(0,[z177,z0,z1,z2,z4,z24,z6]),(0,[z0,z268,z1,z2,z3,z4,z6]),(0,[z41,z0,z81,z1,z2,z4,z6])],[(0,[z269,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z43,z3,z4,z6]),(1,[z0,z1,z2,z10,z4,z55])],[(0,[z270,z0,z1,z2,z3,z4,z6]),(0,[z0,z25,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z271]),(0,[z0,z1,z2,z3,z4,z272,z6]),(0,[z0,z273,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z217,z3,z4,z6]),(0,[z0,z80,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z274,z3,z4,z6]),(0,[z0,z275,z1,z2,z21,z4,z6])],[(0,[z0,z1,z2,z3,z276,z4,z6]),(0,[z277,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z43,z4,z6,z55]),(1,[z0,z1,z43,z10,z4,z6]),(1,[z0,z1,z231,z3,z4,z6]),(0,[z278,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z279,z4,z6]),(0,[z0,z1,z2,z280,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z281,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z136]),(1,[z0,z81,z2,z135,z4,z6])],[(0,[z0,z1,z2,z135,z150,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z282])],[(0,[z0,z283,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z284,z10,z4,z6])],[(0,[z0,z1,z38,z3,z4,z6,z93]),(0,[z179,z41,z0,z1,z2,z4,z6]),(0,[z126,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z10,z150,z4,z6]),(0,[z124,z0,z230,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z21,z4,z6]),(0,[z118,z0,z1,z2,z4,z6,z55]),(0,[z0,z285,z1,z2,z3,z4,z6])],[(0,[z126,z1,z2,z3,z4,z6,z96]),(0,[z0,z1,z2,z3,z4,z286,z6]),(0,[z0,z169,z1,z2,z10,z4,z6]),(0,[z287,z0,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z233,z3,z4,z6]),(0,[z126,z0,z1,z2,z10,z4,z6]),(0,[z0,z1,z2,z3,z288,z4,z6])],[(0,[z289,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z10,z267,z4,z6]),(0,[z0,z285,z1,z2,z4,z6,z55])],[(0,[z0,z1,z2,z3,z290,z4,z6]),(0,[z41,z0,z1,z2,z4,z46,z6]),(0,[z41,z92,z0,z1,z2,z4,z6]),(1,[z0,z1,z37,z3,z267,z6]),(0,[z0,z1,z2,z3,z291,z4,z6])],[(0,[z0,z1,z2,z292,z3,z4,z6]),(0,[z293,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z294,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z295,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z296,z4,z6])],[(1,[z0,z2,z3,z4,z297,z6]),(0,[z0,z1,z2,z267,z4,z6,z55]),(0,[z0,z1,z2,z3,z298,z4,z6])],[(0,[z0,z299,z1,z2,z3,z4,z6])],[(0,[z0,z1,z43,z3,z4,z6,z93]),(0,[z0,z1,z300,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z40])],[(0,[z0,z1,z2,z150,z89,z4,z6]),(0,[z41,z118,z0,z1,z2,z4,z6]),(0,[z0,z301,z1,z2,z3,z4,z6])],[(0,[z0,z302,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z54,z21,z4,z6]),(0,[z33,z0,z1,z2,z21,z4,z6])]],
   [[(0,[z0,z90,z2,z3,z103,z4,z6]),(0,[z179,z0,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z38,z10,z4,z6]),(1,[z17,z1,z2,z3,z4,z18]),(0,[z0,z1,z2,z3,z4,z303,z6])],[(0,[z304,z0,z1,z2,z3,z4,z6]),(0,[z41,z88,z0,z1,z2,z4,z6]),(0,[z0,z301,z1,z2,z4,z6,z55]),(0,[z0,z1,z305,z2,z10,z4,z6])],[(0,[z0,z1,z2,z3,z212,z4,z6]),(0,[z0,z1,z53,z2,z21,z4,z6])],[(0,[z306,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z127,z3,z4,z6]),(0,[z0,z1,z2,z3,z307,z4,z6]),(0,[z0,z1,z2,z59,z135,z4,z6]),(0,[z0,z1,z2,z308,z3,z4,z6])],[(0,[z0,z1,z38,z38,z3,z4,z6]),(1,[z0,z1,z2,z234,z4,z6]),(0,[z0,z1,z2,z309,z3,z21,z6]),(0,[z0,z1,z2,z4,z6,z310,z97])],[(0,[z0,z1,z38,z3,z4,z6,z97]),(0,[z0,z1,z2,z3,z4,z311,z6])],[(0,[z42,z0,z1,z2,z261,z4,z6]),(0,[z312,z41,z0,z1,z2,z4,z6]),(0,[z0,z1,z313,z2,z3,z4,z6])],[(0,[z125,z1,z2,z73,z3,z4,z6]),(0,[z0,z1,z314,z2,z3,z4,z6]),(0,[z0,z1,z315,z2,z3,z4,z6]),(0,[z41,z19,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z316])],[],[(0,[z0,z1,z43,z3,z4,z6,z55]),(0,[z317,z0,z1,z2,z3,z4,z6]),(0,[z95,z0,z1,z141,z3,z4,z6]),(0,[z0,z318,z1,z2,z3,z4,z6])],[(0,[z0,z1,z233,z2,z3,z4,z6]),(1,[z88,z1,z2,z150,z4,z6]),(0,[z0,z319,z1,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z4,z119,z6])],[(0,[z0,z1,z2,z3,z320,z4,z6]),(0,[z72,z0,z1,z154,z3,z4,z6]),(0,[z0,z1,z2,z64,z21,z4,z6])],[(0,[z88,z0,z1,z43,z3,z4,z6]),(0,[z0,z321,z1,z2,z3,z4,z6])],[(1,[z177,z0,z1,z2,z4,z6]),(0,[z0,z322,z1,z2,z3,z4,z6])],[(0,[z72,z0,z1,z2,z3,z4,z6]),(0,[z0,z61,z2,z3,z103,z4,z6]),(0,[z0,z1,z2,z10,z98,z4,z6])],[(0,[z221,z0,z1,z43,z3,z4,z6]),(0,[z222,z0,z1,z43,z3,z4,z6]),(0,[z0,z1,z87,z43,z3,z4,z6]),(0,[z0,z1,z43,z3,z4,z6,z97]),(0,[z0,z1,z2,z21,z103,z4,z6]),(0,[z0,z1,z2,z4,z163,z6,z55]),(0,[z0,z1,z2,z323,z3,z4,z6])]],
   [[(0,[z42,z0,z1,z43,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z324]),(0,[z0,z122,z1,z2,z3,z99,z6])],[(0,[z0,z140,z1,z38,z3,z4,z6]),(0,[z72,z0,z1,z2,z4,z6,z55]),(1,[z196,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z325,z3,z4,z6]),(0,[z326,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z37,z3,z267,z4,z6]),(0,[z278,z1,z2,z3,z4,z6,z97]),(0,[z327,z0,z2,z3,z4,z6,z97])],[(0,[z0,z1,z2,z3,z328,z4,z6]),(0,[z329,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z103,z4,z6]),(0,[z92,z0,z1,z2,z3,z4,z6]),(0,[z95,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z310])],[(0,[z0,z1,z43,z2,z10,z4,z6]),(0,[z124,z0,z1,z2,z330,z4,z6]),(0,[z126,z0,z1,z2,z3,z74,z6]),(0,[z0,z1,z331,z2,z3,z4,z6])],[(0,[z41,z0,z1,z206,z2,z4,z6]),(0,[z0,z1,z2,z3,z332,z4,z6]),(0,[z333,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z37,z2,z3,z267,z6])],[(0,[z126,z1,z2,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z147]),(0,[z124,z0,z1,z2,z3,z24,z6]),(0,[z0,z1,z61,z2,z3,z4,z6]),(0,[z0,z2,z3,z103,z4,z46,z6]),(0,[z92,z0,z1,z2,z10,z4,z6]),(0,[z95,z0,z1,z2,z4,z6,z55])],[(0,[z0,z1,z38,z3,z14,z4,z6]),(0,[z0,z81,z1,z2,z3,z4,z6])],[(0,[z0,z107,z1,z2,z3,z4,z6]),(0,[z334,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z335,z4,z6])],[(0,[z1,z2,z3,z14,z4,z24,z6]),(0,[z0,z1,z61,z2,z4,z6,z55])],[(0,[z0,z1,z2,z3,z336,z4,z6]),(0,[z337,z0,z1,z2,z3,z4,z6]),(0,[z0,z81,z1,z2,z10,z4,z6])],[(0,[z0,z1,z141,z38,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z6,z96]),(0,[z0,z107,z1,z2,z4,z6,z55]),(0,[z0,z338,z1,z2,z3,z4,z6]),(0,[z339,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z55,z340])],[(0,[z341,z0,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z342]),(0,[z41,z0,z1,z2,z54,z4,z6]),(0,[z0,z1,z343,z2,z3,z4,z6])],[(0,[z0,z1,z344,z2,z3,z4,z6])],[(0,[z345,z0,z1,z2,z3,z4,z6])],[(0,[z117,z0,z206,z2,z3,z4,z6]),(0,[z0,z1,z2,z346,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z96]),(0,[z0,z1,z343,z2,z4,z6,z55])]],
   [[(0,[z0,z1,z2,z3,z4,z347,z6]),(0,[z0,z1,z2,z3,z4,z348,z6]),(0,[z0,z1,z53,z2,z59,z4,z6])],[(0,[z0,z1,z43,z3,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z349,z6]),(0,[z117,z41,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z350,z4,z6]),(0,[z351,z41,z0,z1,z2,z4,z6]),(0,[z0,z352,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z4,z100,z6])],[(1,[z0,z1,z3,z4,z353,z6])],[(0,[z0,z1,z2,z3,z354,z4,z6]),(0,[z0,z25,z1,z2,z280,z4,z6]),(0,[z144,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z152,z21,z4,z6])],[(0,[z0,z1,z206,z2,z10,z4,z6]),(0,[z41,z0,z1,z37,z2,z4,z6]),(0,[z0,z352,z1,z2,z4,z6,z55])],[],[(0,[z41,z35,z0,z1,z2,z4,z6]),(0,[z0,z1,z43,z3,z4,z6,z198]),(0,[z0,z1,z2,z3,z4,z6,z355]),(0,[z41,z0,z107,z1,z2,z4,z6]),(0,[z0,z356,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z256,z4,z6]),(0,[z0,z1,z357,z2,z3,z4,z6])],[(0,[z358,z0,z1,z2,z3,z4,z6]),(0,[z0,z169,z1,z2,z3,z46,z6]),(0,[z41,z0,z1,z2,z4,z163,z6]),(0,[z359,z41,z0,z1,z2,z4,z6]),(0,[z0,z1,z360,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z24,z6,z97]),(0,[z41,z0,z1,z2,z4,z240,z6]),(0,[z41,z95,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z361])],[(0,[z126,z1,z2,z3,z14,z4,z6]),(0,[z0,z362,z1,z2,z3,z4,z6])],[(0,[z0,z1,z363,z2,z3,z4,z6]),(0,[z0,z1,z364,z2,z3,z4,z6]),(0,[z19,z0,z1,z37,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z6,z365]),(0,[z0,z1,z2,z4,z6,z55,z55]),(0,[z0,z1,z2,z3,z152,z6,z97])],[(0,[z366,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z367,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z6,z93]),(0,[z0,z1,z2,z10,z54,z4,z6]),(1,[z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z4,z6,z158,z55])],[(0,[z19,z0,z107,z1,z3,z4,z6]),(0,[z19,z0,z1,z2,z3,z4,z6]),(0,[z249,z0,z1,z2,z3,z4,z6])],[(0,[z0,z153,z1,z2,z3,z4,z6]),(0,[z25,z368,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z369,z6])],[(0,[z0,z1,z2,z3,z370,z4,z6]),(0,[z117,z0,z1,z38,z3,z4,z6]),(0,[z0,z69,z1,z2,z10,z4,z6]),(0,[z19,z95,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z365])],[(0,[z0,z1,z2,z3,z4,z6,z93]),(0,[z19,z0,z1,z2,z4,z6,z55]),(0,[z19,z0,z1,z2,z10,z4,z6]),(0,[z249,z0,z1,z2,z10,z4,z6])]],
   [[(0,[z0,z1,z371,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z84,z6,z198])],[(0,[z0,z1,z2,z372,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z373,z6])],[(0,[z0,z90,z2,z3,z89,z4,z6]),(0,[z124,z0,z374,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z375,z6]),(0,[z0,z1,z2,z3,z197,z4,z6]),(0,[z41,z0,z1,z2,z152,z4,z6]),(0,[z0,z1,z2,z284,z3,z4,z6]),(0,[z118,z0,z1,z2,z21,z4,z6]),(0,[z118,z0,z1,z2,z3,z4,z55])],[],[(0,[z0,z1,z2,z3,z376,z4,z6]),(0,[z0,z1,z2,z3,z377,z4,z6])],[(0,[z118,z0,z1,z43,z3,z4,z6]),(0,[z0,z25,z1,z2,z10,z4,z6]),(0,[z0,z169,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z378,z6]),(0,[z0,z80,z1,z2,z10,z4,z6])],[(1,[z341,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z150,z4,z6,z55]),(0,[z0,z1,z2,z3,z379,z4,z6]),(0,[z0,z1,z2,z380,z3,z4,z6])],[(0,[z0,z1,z2,z381,z3,z4,z6]),(0,[z0,z169,z1,z2,z4,z6,z55]),(0,[z382,z41,z0,z1,z2,z4,z6])],[(0,[z126,z0,z1,z2,z4,z6,z55])],[],[(0,[z0,z1,z2,z3,z4,z6,z195])],[(0,[z0,z1,z2,z3,z4,z383,z6]),(0,[z0,z1,z2,z4,z84,z6,z253])],[(0,[z0,z1,z2,z21,z4,z6,z97])],[(0,[z0,z1,z43,z3,z4,z24,z6]),(0,[z126,z72,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z384,z6])],[(1,[z0,z25,z64,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z38,z3,z4,z6]),(0,[z0,z1,z43,z309,z3,z4,z6]),(0,[z0,z385,z1,z2,z3,z4,z6]),(0,[z0,z80,z1,z2,z89,z4,z6]),(0,[z41,z0,z1,z2,z135,z4,z6]),(0,[z386,z0,z1,z2,z3,z4,z6])],[(0,[z41,z72,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z387,z3,z4,z6]),(0,[z0,z1,z2,z3,z388,z4,z6]),(0,[z0,z1,z2,z10,z152,z4,z6]),(0,[z0,z1,z305,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z97])],[(0,[z0,z1,z38,z3,z4,z6,z55])],[(0,[z389,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z38,z4,z6,z55]),(0,[z0,z1,z43,z390,z3,z4,z6]),(0,[z0,z391,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z102])],[(0,[z382,z0,z1,z38,z3,z4,z6]),(0,[z0,z1,z392,z38,z3,z4,z6]),(0,[z0,z302,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z89,z4,z6]),(0,[z0,z1,z2,z3,z393,z4,z6])],[(0,[z0,z394,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z103,z4,z240,z6]),(0,[z0,z1,z37,z2,z21,z4,z6])],[(1,[z124,z1,z38,z3,z4,z6])],[(0,[z395,z0,z1,z2,z3,z4,z6])],[(0,[z179,z0,z1,z2,z10,z4,z6]),(0,[z41,z0,z1,z2,z4,z4,z6])],[(0,[z0,z1,z2,z396,z3,z4,z6]),(0,[z0,z1,z2,z10,z4,z46,z6]),(1,[z95,z0,z1,z3,z4,z198])],[(0,[z397,z0,z1,z2,z3,z4,z6]),(0,[z41,z0,z90,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z398,z4,z6]),(0,[z395,z0,z1,z2,z4,z6,z55])],[(0,[z88,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z399])],[(0,[z0,z1,z43,z3,z4,z18,z6]),(0,[z19,z0,z1,z2,z3,z163,z6]),(0,[z0,z1,z2,z3,z152,z99,z4])],[(0,[z117,z0,z25,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z400]),(0,[z0,z1,z2,z4,z84,z6,z55])],[]],
   [[(0,[z42,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z53,z2,z54,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z401]),(1,[z0,z1,z2,z402,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z40])],[(0,[z0,z1,z2,z3,z255,z4,z6]),(0,[z0,z403,z1,z2,z3,z4,z6])],[(0,[z72,z0,z1,z43,z3,z4,z6]),(0,[z0,z1,z43,z37,z3,z4,z6])],[],[(0,[z0,z1,z43,z2,z3,z4,z6]),(0,[z0,z1,z404,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z405])],[(0,[z0,z1,z43,z59,z3,z4,z6]),(0,[z406,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z407]),(0,[z408,z0,z1,z2,z3,z4,z6]),(0,[z0,z409,z1,z2,z3,z4,z6])],[(0,[z0,z1,z410,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z411,z6]),(0,[z0,z1,z2,z4,z375,z163,z6]),(0,[z41,z0,z1,z2,z3,z21,z6])],[(0,[z412,z0,z1,z2,z3,z4,z6]),(0,[z95,z0,z1,z43,z3,z4,z6]),(0,[z0,z1,z43,z2,z4,z6,z55]),(0,[z0,z1,z2,z413,z3,z4,z6])],[],[(0,[z0,z414,z1,z2,z3,z4,z6]),(0,[z92,z0,z1,z2,z4,z6,z55])],[(0,[z0,z1,z43,z3,z4,z415,z6]),(0,[z0,z1,z61,z43,z3,z4,z6]),(0,[z0,z140,z1,z2,z10,z4,z6]),(0,[z0,z1,z2,z413,z10,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z416])],[(0,[z41,z0,z1,z2,z38,z4,z6]),(0,[z126,z0,z1,z2,z3,z4,z96]),(0,[z0,z1,z2,z234,z4,z18,z6]),(1,[z0,z1,z2,z162,z4,z6]),(0,[z41,z227,z0,z1,z2,z4,z6])],[(0,[z0,z107,z1,z43,z3,z4,z6]),(0,[z41,z0,z1,z417,z2,z4,z6]),(0,[z0,z1,z2,z10,z4,z119,z6])],[(0,[z0,z1,z2,z3,z4,z418,z6]),(0,[z419,z0,z1,z2,z3,z4,z6]),(1,[z0,z420,z2,z3,z4,z6]),(0,[z0,z81,z1,z2,z4,z6,z55])],[(1,[z0,z1,z173,z3,z4,z6])],[(0,[z0,z90,z2,z3,z4,z6,z93]),(0,[z0,z1,z38,z3,z4,z6,z198]),(0,[z0,z1,z2,z3,z421,z4,z6]),(0,[z41,z0,z1,z141,z2,z4,z6])]],
   [[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z90,z1,z38,z3,z4,z6]),(0,[z0,z244,z1,z2,z3,z4,z6])],[(0,[z0,z1,z344,z43,z3,z4,z6]),(0,[z72,z1,z2,z3,z4,z24,z6]),(1,[z0,z1,z67,z3,z4,z6]),(0,[z0,z209,z2,z3,z4,z163,z6])],[(0,[z422,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z423,z3,z4,z6]),(0,[z0,z1,z2,z256,z99,z4,z6])],[(0,[z0,z1,z2,z3,z424,z4,z6]),(0,[z88,z0,z1,z2,z150,z4,z6]),(1,[z368,z1,z2,z3,z4,z6]),(0,[z0,z1,z425,z2,z3,z4,z6]),(0,[z95,z0,z1,z3,z267,z4,z6])],[(0,[z0,z1,z206,z2,z3,z4,z6]),(1,[z0,z1,z79,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z426,z6]),(0,[z0,z1,z2,z3,z4,z427,z6]),(0,[z0,z1,z141,z2,z10,z4,z6])],[(0,[z341,z0,z1,z2,z10,z4,z6]),(1,[z0,z362,z2,z3,z4,z6]),(0,[z0,z169,z1,z2,z3,z103,z6]),(0,[z428,z0,z1,z2,z3,z4,z6])],[(0,[z117,z0,z1,z2,z3,z46,z6]),(1,[z0,z1,z2,z429,z4,z6])],[(0,[z0,z1,z206,z2,z4,z6,z55])],[(0,[z0,z107,z1,z3,z267,z4,z6]),(0,[z0,z1,z2,z21,z4,z430,z6])],[(0,[z0,z1,z2,z431,z3,z4,z6])],[(0,[z41,z0,z1,z43,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z432,z6]),(0,[z41,z0,z1,z2,z4,z134,z6])],[(0,[z0,z1,z433,z2,z3,z4,z6]),(0,[z1,z2,z3,z14,z4,z18,z6]),(0,[z0,z434,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z135,z54,z4,z6]),(0,[z0,z2,z3,z4,z240,z6,z93])],[(0,[z0,z1,z2,z3,z4,z6,z253]),(0,[z0,z1,z2,z3,z4,z430,z6])],[(0,[z0,z1,z2,z3,z4,z6,z128])],[(0,[z0,z1,z363,z43,z3,z4,z6]),(0,[z0,z69,z1,z2,z3,z4,z6])],[(0,[z435,z0,z1,z2,z3,z4,z6]),(0,[z17,z0,z1,z38,z3,z4,z6]),(0,[z366,z0,z1,z43,z3,z4,z6]),(1,[z0,z1,z43,z21,z4,z6]),(0,[z0,z1,z2,z3,z436,z4,z6])]],
   [[(0,[z19,z0,z1,z43,z3,z4,z6]),(0,[z72,z1,z2,z3,z4,z18,z6]),(0,[z126,z0,z1,z2,z3,z4,z18]),(0,[z0,z1,z2,z10,z4,z437,z6])],[(0,[z0,z1,z43,z3,z438,z4,z6]),(1,[z0,z69,z2,z3,z4,z240]),(0,[z0,z69,z1,z2,z4,z6,z55])],[(0,[z0,z1,z2,z3,z261,z4,z6])],[(0,[z439,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z440,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z441]),(0,[z117,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z442,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z443]),(0,[z0,z25,z1,z2,z3,z4,z6]),(0,[z41,z0,z1,z53,z2,z4,z6]),(0,[z444,z0,z1,z2,z3,z4,z6]),(0,[z0,z445,z1,z2,z3,z4,z6])],[(0,[z179,z35,z1,z2,z3,z4,z6]),(0,[z446,z0,z1,z2,z3,z4,z6]),(0,[z0,z80,z1,z2,z3,z4,z6]),(0,[z92,z0,z1,z2,z3,z4,z240])],[(0,[z0,z1,z38,z3,z4,z24,z6]),(1,[z0,z1,z2,z447,z4,z6]),(0,[z126,z0,z1,z2,z21,z4,z6]),(0,[z117,z0,z169,z2,z3,z4,z6]),(0,[z117,z0,z1,z2,z4,z6,z55]),(0,[z117,z0,z1,z2,z10,z4,z6]),(0,[z0,z1,z146,z2,z3,z4,z6])],[(0,[z0,z25,z1,z2,z4,z6,z55])],[(0,[z0,z1,z38,z309,z3,z4,z6]),(0,[z0,z169,z1,z43,z3,z4,z6]),(0,[z0,z80,z1,z2,z4,z6,z55]),(0,[z0,z1,z2,z10,z4,z163,z6])],[(0,[z126,z0,z1,z43,z3,z4,z6]),(0,[z0,z1,z2,z10,z4,z240,z6]),(0,[z359,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z6,z55])],[(0,[z0,z1,z2,z3,z3,z4,z6]),(1,[z0,z230,z2,z3,z4,z6]),(1,[z0,z1,z2,z309,z21,z6])],[(1,[z0,z1,z448,z3,z4,z6]),(0,[z0,z1,z2,z3,z449,z4,z6]),(0,[z0,z1,z2,z267,z21,z4,z6])],[(0,[z179,z1,z43,z2,z3,z4,z6]),(0,[z0,z450,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z402,z4,z84,z6]),(0,[z0,z1,z2,z298,z4,z6,z55])],[(0,[z88,z0,z420,z2,z3,z4,z6]),(0,[z88,z1,z2,z3,z150,z4,z6]),(0,[z0,z65,z1,z3,z4,z46,z6]),(0,[z41,z0,z1,z2,z4,z167,z6]),(0,[z0,z1,z2,z3,z4,z6,z55])],[(0,[z19,z0,z1,z2,z3,z267,z6]),(0,[z0,z1,z2,z451,z21,z4,z6])]],
   [[(0,[z0,z1,z38,z3,z21,z4,z6]),(0,[z0,z452,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z170,z4,z6]),(0,[z453,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z454,z4,z6])],[(0,[z455,z0,z1,z38,z3,z4,z6]),(1,[z0,z1,z2,z189,z4,z6]),(0,[z0,z1,z2,z3,z4,z456,z6])],[(0,[z0,z1,z38,z3,z4,z457,z6]),(0,[z0,z458,z1,z2,z3,z4,z6])],[(0,[z0,z385,z1,z43,z3,z4,z6]),(0,[z0,z1,z2,z459,z3,z4,z6])],[(0,[z341,z1,z2,z38,z3,z4,z6]),(0,[z0,z1,z2,z4,z18,z6,z128]),(0,[z460,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z38,z3,z4,z18,z6]),(0,[z461,z0,z1,z2,z3,z4,z6])],[(0,[z0,z462,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z162,z4,z240,z6]),(0,[z463,z0,z1,z2,z3,z4,z6]),(1,[z0,z352,z1,z2,z4,z6]),(0,[z0,z1,z2,z459,z10,z4,z6]),(0,[z0,z1,z2,z3,z4,z464,z6])],[(0,[z72,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z4,z465,z6])],[(0,[z179,z0,z1,z2,z3,z4,z6]),(1,[z179,z1,z43,z3,z4,z6])],[(0,[z0,z1,z43,z3,z21,z4,z6]),(0,[z0,z1,z2,z59,z10,z4,z6]),(0,[z0,z466,z1,z2,z3,z4,z6]),(0,[z327,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z392,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z467,z6]),(0,[z92,z0,z1,z2,z3,z4,z93]),(1,[z0,z1,z2,z4,z6,z468])],[(0,[z0,z206,z2,z3,z103,z4,z6]),(0,[z179,z0,z1,z2,z4,z6,z55]),(0,[z0,z1,z43,z73,z3,z4,z6]),(0,[z0,z1,z43,z3,z99,z4,z6]),(0,[z0,z45,z1,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z309,z4,z6])],[(0,[z179,z1,z206,z2,z3,z4,z6]),(0,[z0,z1,z43,z141,z3,z4,z6]),(0,[z0,z1,z2,z330,z3,z4,z6]),(0,[z0,z1,z2,z10,z4,z167,z6]),(0,[z317,z0,z1,z2,z21,z4,z6])],[(0,[z0,z1,z38,z59,z3,z4,z6]),(0,[z101,z0,z1,z2,z3,z4,z6]),(0,[z382,z0,z1,z2,z10,z4,z6]),(0,[z0,z469,z1,z2,z3,z4,z6])],[(0,[z0,z352,z122,z1,z2,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z470,z6]),(0,[z0,z1,z2,z3,z4,z471,z6]),(0,[z0,z7,z1,z2,z4,z163,z6])],[(0,[z35,z0,z90,z2,z3,z4,z6]),(0,[z126,z179,z1,z2,z3,z4,z6]),(1,[z0,z107,z61,z3,z4,z6]),(0,[z0,z472,z1,z2,z3,z4,z6])],[(0,[z0,z1,z473,z2,z3,z4,z6]),(0,[z72,z0,z1,z2,z21,z4,z6]),(0,[z41,z0,z1,z2,z4,z84,z6])],[],[(0,[z0,z1,z2,z59,z89,z4,z6]),(0,[z0,z1,z2,z3,z4,z474,z6]),(0,[z0,z1,z2,z3,z4,z475,z6])],[(0,[z0,z1,z2,z3,z476,z4,z6]),(0,[z0,z1,z2,z4,z6,z324,z55])],[(0,[z477,z0,z1,z2,z3,z4,z6]),(1,[z42,z206,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z4,z6]),(0,[z0,z1,z2,z4,z18,z6,z55]),(0,[z19,z196,z1,z2,z3,z4,z6])],[(0,[z0,z1,z38,z3,z150,z4,z6]),(0,[z124,z0,z1,z38,z3,z4,z6]),(0,[z0,z478,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z479]),(0,[z92,z0,z1,z2,z21,z4,z6]),(0,[z95,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z21,z4,z6,z198])],[(0,[z0,z1,z43,z43,z3,z4,z6]),(0,[z0,z122,z1,z2,z3,z24,z6]),(1,[z0,z1,z53,z59,z4,z6]),(0,[z0,z1,z331,z2,z21,z4,z6])],[(0,[z0,z1,z2,z3,z4,z480,z6]),(0,[z0,z481,z1,z2,z3,z4,z6]),(0,[z0,z482,z1,z2,z3,z4,z6])],[(0,[z92,z0,z1,z43,z3,z4,z6]),(0,[z0,z483,z1,z2,z3,z4,z6]),(0,[z0,z1,z61,z2,z21,z4,z6]),(0,[z0,z140,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z330,z4,z6]),(0,[z0,z81,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z198])],[(0,[z0,z1,z2,z3,z4,z484,z6]),(0,[z0,z107,z1,z2,z21,z4,z6]),(0,[z312,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z4,z5,z6]),(0,[z95,z0,z1,z2,z440,z4,z6])],[(0,[z0,z140,z1,z2,z4,z6,z55])],[(0,[z0,z81,z1,z43,z3,z4,z6])],[(0,[z0,z1,z485,z2,z3,z4,z6]),(0,[z0,z1,z486,z2,z3,z4,z6]),(0,[z0,z1,z2,z487,z3,z4,z6])]],
   [[(0,[z488,z0,z1,z2,z3,z4,z6]),(0,[z95,z0,z1,z2,z3,z4,z84])],[(0,[z0,z1,z43,z3,z150,z4,z6]),(0,[z489,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z10,z4,z84,z6])],[],[(1,[z41,z0,z1,z2,z21,z6]),(0,[z490,z0,z1,z2,z3,z4,z6])],[(0,[z0,z0,z1,z43,z3,z4,z6]),(0,[z0,z1,z43,z3,z267,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z491]),(0,[z117,z0,z1,z2,z3,z103,z6]),(0,[z0,z1,z141,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z492,z4,z6])],[(0,[z341,z0,z1,z2,z3,z4,z6]),(0,[z0,z493,z1,z2,z3,z4,z6]),(0,[z494,z0,z1,z2,z3,z4,z6]),(0,[z0,z352,z1,z2,z21,z4,z6])],[(0,[z35,z42,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z495,z4,z6]),(0,[z0,z1,z2,z496,z3,z4,z6])],[(0,[z0,z1,z2,z217,z3,z4,z6]),(0,[z0,z1,z3,z4,z353,z46,z6]),(0,[z0,z1,z2,z3,z4,z497,z6]),(0,[z0,z1,z2,z3,z4,z498,z6]),(0,[z0,z1,z141,z2,z4,z6,z55]),(1,[z0,z1,z3,z4,z6,z83])],[(0,[z0,z1,z206,z43,z3,z4,z6]),(0,[z341,z0,z1,z2,z4,z6,z55]),(0,[z499,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z500,z3,z4,z6]),(0,[z0,z90,z1,z2,z10,z4,z6]),(1,[z0,z1,z2,z26,z4,z6])],[(0,[z501,z0,z1,z38,z3,z4,z6]),(1,[z0,z1,z91,z3,z4,z6]),(0,[z17,z0,z1,z171,z3,z4,z6])],[],[(0,[z502,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z503,z3,z4,z6]),(0,[z0,z1,z2,z3,z504,z4,z6])],[],[(0,[z505,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z506,z6]),(1,[z117,z0,z2,z3,z46,z6]),(1,[z20,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z316,z97])],[(0,[z0,z1,z2,z21,z4,z24,z6]),(0,[z0,z1,z507,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z38,z3,z508,z4,z6]),(0,[z19,z0,z1,z2,z21,z4,z6]),(1,[z0,z1,z141,z3,z4,z84])],[(0,[z126,z0,z362,z2,z3,z4,z6])],[(0,[z0,z1,z509,z2,z3,z4,z6]),(0,[z0,z69,z1,z43,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z340]),(0,[z0,z1,z2,z3,z4,z100,z6]),(1,[z0,z2,z3,z4,z6,z316])],[(0,[z0,z1,z2,z3,z4,z24,z6]),(0,[z41,z0,z25,z1,z2,z4,z6])],[(0,[z0,z1,z2,z243,z3,z4,z6]),(0,[z0,z81,z2,z135,z3,z4,z6]),(0,[z0,z1,z2,z4,z240,z6,z468]),(0,[z0,z1,z2,z510,z3,z4,z6]),(0,[z95,z0,z1,z2,z3,z4,z198]),(0,[z41,z41,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z3,z4,z511,z6]),(0,[z0,z1,z2,z3,z512,z4,z6]),(0,[z0,z1,z2,z309,z3,z4,z6]),(1,[z278,z1,z2,z3,z4,z6])],[(1,[z126,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z513,z6]),(0,[z0,z1,z2,z3,z246,z4,z6])],[(0,[z0,z1,z2,z3,z514,z4,z6]),(0,[z351,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z500,z4,z6]),(0,[z35,z0,z1,z346,z3,z4,z6]),(0,[z117,z0,z1,z43,z3,z4,z6]),(0,[z0,z1,z2,z390,z3,z4,z6]),(0,[z0,z1,z2,z150,z21,z4,z6]),(0,[z17,z0,z1,z2,z10,z4,z6]),(0,[z0,z1,z2,z309,z4,z6,z55]),(0,[z0,z1,z2,z21,z21,z4,z6])],[(0,[z0,z25,z1,z43,z3,z4,z6]),(1,[z0,z374,z2,z3,z4,z6]),(0,[z19,z0,z25,z1,z3,z4,z6]),(0,[z0,z515,z1,z2,z3,z4,z6]),(0,[z0,z169,z1,z2,z21,z4,z6])],[(0,[z0,z80,z1,z43,z3,z4,z6]),(0,[z0,z516,z1,z2,z3,z4,z6])],[(0,[z517,z0,z1,z2,z3,z4,z6])],[(0,[z1,z206,z2,z38,z3,z4,z6])],[(0,[z124,z1,z2,z38,z3,z4,z6]),(1,[z0,z1,z2,z3,z471,z6]),(0,[z0,z1,z2,z3,z4,z6,z518]),(0,[z0,z1,z2,z89,z4,z6,z55]),(0,[z0,z1,z2,z3,z519,z4,z6]),(0,[z92,z0,z69,z2,z3,z4,z6])],[(0,[z0,z206,z2,z3,z89,z4,z6]),(1,[z41,z0,z1,z43,z4,z6]),(0,[z0,z1,z2,z21,z4,z18,z6]),(0,[z0,z1,z2,z520,z3,z4,z6]),(1,[z0,z1,z2,z487,z4,z6])],[(0,[z0,z1,z2,z3,z4,z457,z6]),(0,[z521,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z522,z6])]],
   [[(1,[z0,z237,z2,z3,z4,z6]),(0,[z0,z523,z1,z2,z3,z4,z6]),(0,[z0,z524,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z525,z3,z4,z6])],[(0,[z41,z0,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z73,z10,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z526]),(0,[z0,z1,z2,z3,z4,z18,z6]),(0,[z0,z1,z527,z2,z3,z4,z6]),(0,[z0,z528,z1,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z38,z21,z4,z6]),(0,[z0,z1,z529,z2,z3,z4,z6])],[(0,[z0,z1,z38,z73,z3,z4,z6]),(0,[z0,z1,z38,z3,z99,z4,z6]),(0,[z0,z1,z2,z3,z530,z4,z6]),(0,[z0,z25,z1,z3,z267,z4,z6]),(0,[z531,z41,z0,z1,z2,z4,z6])],[(0,[z0,z1,z43,z3,z4,z119,z6]),(0,[z0,z1,z2,z3,z4,z532,z6])],[(0,[z0,z1,z2,z3,z533,z4,z6]),(0,[z0,z534,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z103,z4,z6,z55])],[(0,[z126,z0,z1,z448,z3,z4,z6]),(0,[z0,z1,z535,z2,z3,z4,z6])],[(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z536,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z537,z4,z6]),(0,[z0,z1,z538,z2,z3,z4,z6])],[(0,[z35,z0,z206,z2,z3,z4,z6]),(0,[z0,z1,z2,z59,z3,z4,z6])],[(0,[z0,z1,z2,z73,z89,z4,z6]),(0,[z72,z0,z1,z79,z3,z4,z6]),(0,[z0,z539,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z540,z6]),(0,[z0,z1,z2,z3,z541,z4,z6]),(0,[z542,z41,z0,z1,z2,z4,z6])],[(0,[z543,z0,z1,z2,z3,z4,z6])],[(0,[z179,z0,z1,z43,z3,z4,z6]),(0,[z544,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z59,z4,z6,z55]),(0,[z0,z1,z2,z3,z4,z545,z6])],[(0,[z382,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z415,z6]),(0,[z0,z1,z2,z3,z4,z546,z6])]],
   [[(0,[z0,z1,z36,z2,z3,z4,z6]),(0,[z0,z1,z547,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z548,z4,z6])],[(0,[z549,z0,z1,z2,z3,z4,z6]),(0,[z0,z69,z1,z2,z3,z4,z240]),(0,[z382,z0,z1,z2,z4,z6,z55])],[(0,[z101,z1,z141,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z550,z6])],[(0,[z0,z1,z2,z551,z3,z4,z6]),(0,[z552,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z150,z4,z6]),(0,[z553,z0,z1,z2,z3,z4,z6])],[(0,[z0,z554,z1,z2,z3,z4,z6]),(0,[z41,z0,z219,z1,z2,z4,z6]),(0,[z0,z1,z2,z10,z288,z4,z6]),(0,[z0,z1,z555,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z556])],[(0,[z0,z122,z1,z38,z3,z4,z6]),(0,[z0,z557,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z167,z6,z55])],[(0,[z41,z0,z1,z2,z73,z4,z6]),(0,[z57,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z43,z3,z54,z4,z6]),(0,[z0,z1,z43,z2,z21,z4,z6]),(0,[z1,z2,z73,z3,z150,z4,z6]),(0,[z558,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z559,z4,z6]),(0,[z0,z1,z2,z10,z4,z6,z6]),(0,[z560,z0,z1,z2,z3,z4,z6])],[(0,[z35,z0,z1,z38,z3,z4,z6]),(0,[z0,z368,z1,z2,z3,z4,z6])],[],[],[(0,[z0,z1,z2,z3,z561,z4,z6]),(0,[z179,z1,z2,z3,z4,z24,z6]),(0,[z41,z0,z169,z1,z2,z4,z6])],[(0,[z42,z0,z1,z2,z500,z4,z6]),(0,[z125,z0,z1,z38,z3,z4,z6]),(0,[z0,z1,z38,z3,z267,z4,z6]),(0,[z124,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z562,z6]),(0,[z0,z1,z3,z267,z4,z163,z6]),(0,[z1,z2,z3,z4,z6,z102,z97]),(0,[z249,z0,z122,z1,z2,z4,z6])],[(0,[z0,z140,z1,z43,z3,z4,z6]),(0,[z1,z2,z3,z4,z18,z6,z96]),(0,[z0,z1,z2,z10,z309,z4,z6])],[(0,[z563,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z564,z3,z4,z6]),(1,[z118,z0,z1,z2,z4,z55]),(0,[z0,z481,z1,z2,z4,z6,z55])]],
   [[(1,[z125,z1,z2,z73,z4,z6]),(0,[z124,z0,z1,z2,z10,z4,z6]),(0,[z0,z1,z2,z182,z152,z4,z6])],[(0,[z0,z1,z2,z3,z4,z565,z6]),(0,[z0,z1,z2,z3,z4,z566,z6]),(0,[z0,z1,z43,z135,z3,z4,z6]),(0,[z0,z1,z2,z567,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z93,z55])],[(0,[z41,z0,z1,z2,z103,z4,z6]),(1,[z0,z1,z2,z3,z99,z97])],[(0,[z0,z1,z43,z3,z4,z163,z6]),(1,[z0,z1,z2,z15,z4,z6]),(0,[z0,z1,z2,z3,z4,z568,z6])],[(0,[z0,z1,z38,z569,z3,z4,z6]),(0,[z0,z1,z38,z3,z152,z4,z6]),(0,[z0,z1,z43,z3,z4,z240,z6]),(0,[z0,z1,z43,z10,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z570,z6]),(0,[z571,z0,z1,z2,z3,z4,z6]),(0,[z117,z0,z2,z3,z4,z46,z6]),(0,[z0,z1,z2,z3,z451,z4,z6])],[],[(0,[z0,z1,z2,z3,z438,z4,z6]),(0,[z0,z69,z1,z2,z3,z4,z93]),(0,[z572,z41,z0,z1,z2,z4,z6])],[(0,[z0,z573,z1,z2,z3,z4,z6]),(0,[z0,z574,z1,z2,z10,z4,z6])],[(0,[z0,z1,z206,z2,z21,z4,z6]),(0,[z575,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z182,z4,z6])],[(0,[z0,z90,z1,z2,z3,z4,z6]),(0,[z341,z0,z1,z43,z3,z4,z6]),(0,[z0,z140,z1,z53,z3,z4,z6]),(0,[z490,z0,z1,z2,z4,z6,z55])],[(0,[z576,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z309,z3,z167,z6])],[(0,[z0,z206,z2,z3,z4,z6,z93]),(0,[z0,z577,z1,z2,z3,z4,z6]),(0,[z179,z1,z2,z3,z4,z18,z6])],[(0,[z0,z90,z1,z2,z4,z6,z55]),(0,[z0,z1,z2,z3,z508,z4,z6]),(0,[z57,z25,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z5,z46,z6])],[(0,[z0,z1,z38,z3,z4,z46,z6])],[(0,[z0,z1,z2,z3,z4,z578,z6]),(0,[z0,z1,z43,z3,z152,z4,z6]),(0,[z0,z1,z2,z3,z74,z4,z6]),(0,[z41,z0,z1,z2,z4,z6,z96]),(0,[z0,z1,z2,z579,z3,z4,z6])],[(0,[z0,z1,z2,z580,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z581,z6]),(0,[z0,z122,z1,z2,z3,z152,z4])]],
   [[(0,[z41,z0,z80,z1,z2,z4,z6])],[(0,[z0,z1,z2,z10,z103,z4,z6])],[(0,[z0,z69,z1,z2,z21,z4,z6])],[(0,[z125,z0,z1,z2,z73,z4,z6])],[(0,[z582,z0,z1,z2,z3,z4,z6]),(0,[z0,z169,z1,z2,z429,z4,z6])],[(0,[z0,z1,z53,z38,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z583,z6]),(0,[z0,z1,z2,z3,z4,z6,z584]),(0,[z585,z0,z1,z2,z3,z4,z6]),(0,[z126,z0,z1,z91,z3,z4,z6]),(1,[z0,z1,z2,z367,z4,z6])],[(0,[z0,z1,z43,z3,z4,z46,z6]),(0,[z0,z1,z2,z3,z429,z4,z6]),(0,[z0,z1,z2,z3,z4,z586,z6])],[(0,[z0,z1,z2,z587,z3,z4,z6]),(0,[z17,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z588,z4,z6]),(0,[z117,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z589,z3,z4,z6])],[(0,[z0,z25,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z590]),(1,[z0,z1,z2,z4,z97,z55]),(0,[z0,z122,z1,z2,z3,z152,z6])],[(0,[z0,z80,z1,z2,z21,z4,z6])],[(0,[z0,z1,z2,z3,z4,z591,z6]),(0,[z17,z0,z1,z2,z4,z6,z55]),(0,[z0,z592,z1,z2,z3,z4,z6]),(0,[z0,z593,z1,z2,z3,z4,z6]),(1,[z92,z0,z2,z3,z4,z93])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z594,z6])],[(0,[z595,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z596,z6])],[(0,[z0,z597,z1,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z4,z6,z93]),(0,[z19,z0,z1,z3,z4,z163,z6])],[(0,[z0,z1,z38,z3,z4,z119,z6]),(0,[z0,z1,z2,z3,z598,z4,z6]),(0,[z0,z1,z2,z3,z21,z4,z6])]],
   [[(0,[z0,z25,z2,z64,z3,z4,z6]),(0,[z0,z599,z1,z2,z10,z4,z6])],[(0,[z0,z1,z2,z73,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z353,z6]),(0,[z0,z1,z2,z3,z99,z4,z6])],[(0,[z0,z1,z38,z600,z3,z4,z6]),(0,[z601,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z602,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z3,z603,z4,z6]),(0,[z0,z1,z2,z73,z4,z6,z55]),(0,[z0,z1,z2,z3,z440,z4,z6])],[(1,[z249,z0,z1,z2,z4,z6])],[(1,[z35,z90,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z604]),(1,[z0,z1,z2,z23,z4,z6]),(0,[z126,z0,z1,z2,z447,z4,z6]),(0,[z0,z605,z1,z2,z3,z4,z6])],[(0,[z606,z0,z1,z2,z3,z4,z6])],[(1,[z1,z204,z2,z3,z4,z6])],[(0,[z126,z0,z1,z2,z3,z471,z6]),(0,[z0,z1,z2,z3,z607,z4,z6])],[(0,[z0,z1,z2,z608,z3,z4,z6]),(0,[z0,z1,z154,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z10,z4,z6])],[(0,[z455,z0,z1,z2,z3,z4,z6]),(0,[z0,z374,z1,z2,z3,z4,z6])],[(0,[z0,z1,z609,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z610]),(0,[z126,z0,z237,z2,z3,z4,z6])],[(0,[z179,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z611]),(0,[z0,z1,z2,z3,z4,z297,z6])],[(0,[z0,z69,z2,z3,z4,z240,z6])],[(0,[z41,z341,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z6,z97,z55])]],
   [[(0,[z0,z1,z612,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z613]),(0,[z41,z0,z1,z2,z4,z6,z97]),(0,[z0,z1,z417,z2,z3,z4,z6])],[(0,[z0,z1,z38,z3,z54,z4,z6]),(0,[z0,z614,z1,z2,z3,z4,z6]),(0,[z0,z1,z43,z3,z4,z78,z6]),(0,[z88,z0,z1,z325,z3,z4,z6]),(0,[z0,z1,z2,z615,z3,z4,z6])],[(1,[z1,z43,z38,z3,z4,z6]),(0,[z382,z0,z1,z43,z3,z4,z6]),(0,[z0,z1,z43,z64,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z616,z6]),(0,[z229,z0,z1,z3,z4,z6,z97])],[(0,[z124,z1,z2,z3,z14,z4,z6]),(0,[z0,z1,z2,z617,z3,z4,z6]),(0,[z164,z41,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z618,z6]),(1,[z0,z1,z2,z152,z4,z55])],[(0,[z41,z0,z1,z2,z89,z4,z6]),(0,[z117,z0,z2,z3,z4,z240,z6]),(0,[z0,z1,z2,z4,z6,z198,z55])],[(0,[z0,z1,z2,z3,z4,z619,z6])],[(0,[z1,z2,z38,z3,z4,z24,z6]),(0,[z0,z1,z2,z3,z4,z620,z6]),(0,[z41,z0,z1,z2,z3,z4,z134])],[(0,[z0,z621,z1,z2,z3,z4,z6])],[(0,[z622,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z623,z4,z6]),(0,[z0,z1,z2,z3,z4,z624,z6]),(0,[z625,z0,z1,z2,z3,z4,z6])],[(0,[z0,z107,z1,z64,z3,z4,z6]),(0,[z0,z1,z2,z3,z267,z4,z6]),(0,[z0,z1,z2,z3,z626,z4,z6]),(0,[z0,z1,z2,z10,z10,z4,z6])],[(0,[z0,z1,z38,z135,z3,z4,z6]),(0,[z0,z1,z2,z3,z627,z4,z6])],[],[(0,[z628,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z38,z3,z4,z163,z6]),(0,[z0,z1,z2,z152,z291,z4,z6])],[(0,[z0,z1,z38,z3,z4,z240,z6]),(0,[z0,z1,z38,z10,z3,z4,z6]),(0,[z17,z0,z1,z2,z3,z4,z96])],[(1,[z0,z1,z38,z3,z4,z6]),(0,[z542,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z629,z4,z6]),(0,[z0,z140,z1,z3,z54,z4,z6]),(0,[z0,z140,z1,z2,z21,z4,z6])],[(0,[z35,z0,z1,z2,z3,z4,z6]),(0,[z630,z0,z1,z2,z3,z4,z6]),(0,[z41,z124,z0,z1,z2,z4,z6]),(0,[z41,z0,z1,z2,z4,z6,z40]),(0,[z0,z122,z1,z2,z10,z4,z6])]],
   [[(0,[z0,z1,z2,z569,z3,z4,z6]),(0,[z0,z1,z631,z38,z3,z4,z6]),(0,[z632,z0,z1,z2,z3,z4,z6]),(1,[z41,z0,z1,z2,z4,z134])],[(1,[z0,z1,z38,z10,z4,z6])],[(1,[z1,z206,z38,z3,z4,z6]),(0,[z35,z0,z1,z2,z10,z4,z6]),(0,[z41,z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z2,z3,z633,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z634]),(0,[z124,z0,z1,z2,z4,z6,z55]),(0,[z0,z1,z2,z10,z89,z4,z6])],[(0,[z124,z0,z1,z231,z3,z4,z6]),(1,[z0,z1,z2,z291,z4,z6])],[(0,[z0,z1,z2,z3,z4,z635,z6]),(0,[z0,z1,z2,z21,z4,z46,z6])],[(0,[z90,z1,z206,z2,z3,z4,z6]),(0,[z125,z0,z1,z2,z10,z4,z6]),(0,[z0,z1,z2,z135,z73,z4,z6]),(0,[z19,z0,z1,z3,z4,z84,z6]),(0,[z0,z636,z1,z2,z10,z4,z6])],[(0,[z0,z1,z2,z4,z46,z6,z55]),(0,[z0,z574,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z637,z3,z4,z6]),(0,[z0,z1,z141,z2,z21,z4,z6])],[(0,[z341,z0,z1,z2,z21,z4,z6])],[(0,[z638,z0,z1,z2,z3,z4,z6]),(0,[z639,z0,z1,z2,z3,z4,z6]),(0,[z95,z0,z1,z2,z487,z4,z6]),(1,[z327,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z640]),(1,[z72,z1,z2,z3,z24,z6])],[(0,[z0,z1,z43,z148,z3,z4,z6])],[(0,[z0,z90,z1,z43,z3,z4,z6]),(0,[z0,z1,z2,z641,z3,z4,z6]),(0,[z0,z1,z448,z2,z3,z4,z6]),(0,[z642,z0,z1,z2,z3,z4,z6])],[(0,[z125,z88,z1,z2,z3,z4,z6])],[(0,[z643,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z38,z3,z4,z167,z6])],[(0,[z0,z1,z141,z2,z3,z4,z84])],[(0,[z644,z0,z1,z2,z3,z4,z6]),(0,[z0,z107,z61,z2,z3,z4,z6])],[(0,[z501,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z325,z3,z4,z6]),(0,[z0,z25,z1,z64,z3,z4,z6])],[(0,[z42,z0,z206,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z645,z4,z6])],[(0,[z646,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z402,z3,z4,z6])],[],[(0,[z72,z124,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z119,z6])],[(0,[z0,z1,z51,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z647]),(0,[z0,z1,z2,z62,z21,z4,z6])],[(0,[z572,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z648,z4,z6]),(0,[z0,z1,z2,z309,z21,z4,z6])],[(0,[z0,z1,z43,z3,z4,z167,z6]),(0,[z0,z1,z2,z3,z26,z4,z6]),(0,[z649,z0,z1,z2,z3,z4,z6]),(0,[z0,z650,z1,z2,z3,z4,z6])],[(0,[z651,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z652,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z119,z6])],[(0,[z17,z0,z1,z43,z3,z4,z6]),(1,[z0,z1,z2,z129,z4,z6]),(0,[z0,z140,z1,z2,z59,z4,z6]),(0,[z41,z0,z1,z2,z3,z167,z6]),(0,[z0,z1,z2,z4,z6,z55,z110])],[(0,[z0,z1,z2,z14,z4,z6,z55]),(0,[z0,z1,z2,z173,z3,z4,z6]),(0,[z0,z1,z2,z653,z3,z4,z6])],[(0,[z42,z0,z90,z2,z3,z4,z6]),(0,[z0,z1,z2,z600,z3,z4,z6]),(0,[z0,z1,z654,z2,z3,z4,z6]),(0,[z0,z1,z2,z89,z21,z4,z6]),(0,[z0,z1,z53,z2,z10,z4,z6]),(0,[z52,z0,z1,z2,z10,z4,z6]),(0,[z0,z1,z2,z10,z3,z4,z119])],[(0,[z88,z0,z1,z38,z3,z4,z6]),(0,[z0,z1,z218,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z216,z4,z6]),(1,[z0,z1,z2,z4,z6,z310])]],
   [[(1,[z0,z1,z346,z3,z4,z6]),(0,[z0,z1,z2,z10,z4,z6,z96]),(0,[z0,z599,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z655]),(0,[z656,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z657,z4,z6])],[(0,[z658,z0,z1,z2,z3,z4,z6])],[(0,[z35,z1,z2,z38,z3,z4,z6]),(1,[z0,z404,z2,z3,z4,z6]),(0,[z0,z659,z1,z2,z3,z4,z6]),(0,[z660,z0,z1,z2,z3,z4,z6]),(0,[z661,z0,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z662,z4,z6])],[(0,[z663,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z71,z10,z4,z6])],[(0,[z0,z1,z141,z2,z3,z4,z198])],[(0,[z0,z664,z1,z2,z3,z4,z6]),(1,[z41,z0,z1,z2,z167,z6])],[(0,[z72,z0,z1,z2,z3,z24,z6]),(0,[z0,z1,z2,z64,z10,z4,z6]),(0,[z0,z665,z1,z2,z3,z4,z6])],[(0,[z0,z1,z3,z267,z4,z84,z6]),(0,[z0,z1,z2,z3,z152,z4,z119]),(0,[z0,z1,z2,z3,z99,z4,z97])],[(0,[z0,z420,z1,z2,z3,z4,z6]),(0,[z666,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z667,z6])],[(1,[z124,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z668,z4,z6]),(0,[z41,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z669,z6])],[(0,[z0,z1,z38,z64,z3,z4,z6]),(0,[z0,z1,z2,z3,z447,z4,z6]),(0,[z0,z1,z670,z2,z3,z4,z6]),(0,[z41,z0,z140,z1,z2,z4,z6]),(0,[z0,z671,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z672,z6]),(0,[z0,z1,z2,z3,z4,z673,z6]),(0,[z0,z169,z2,z3,z103,z4,z6]),(1,[z0,z1,z2,z10,z4,z119])],[(1,[z0,z1,z2,z127,z4,z6]),(0,[z0,z1,z2,z674,z3,z4,z6]),(0,[z0,z1,z2,z3,z54,z4,z6]),(0,[z41,z0,z1,z2,z4,z6,z55])],[(1,[z35,z1,z38,z3,z4,z6]),(0,[z0,z1,z43,z3,z4,z84,z6]),(0,[z0,z1,z2,z59,z21,z4,z6])],[(0,[z92,z0,z1,z2,z15,z4,z6]),(0,[z0,z675,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z437,z6]),(0,[z130,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z90,z69,z2,z3,z4,z6]),(0,[z0,z1,z609,z43,z3,z4,z6]),(0,[z0,z81,z1,z2,z135,z4,z6]),(0,[z0,z1,z2,z10,z4,z6,z93]),(0,[z0,z1,z2,z108,z3,z4,z6])],[(0,[z125,z0,z1,z243,z3,z4,z6]),(0,[z0,z1,z2,z3,z676,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z677])],[(0,[z0,z1,z678,z2,z3,z4,z6]),(0,[z382,z0,z1,z2,z21,z4,z6])],[(0,[z0,z679,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z680,z4,z6])],[(0,[z0,z2,z3,z4,z297,z163,z6]),(0,[z0,z1,z2,z21,z4,z163,z6]),(0,[z0,z1,z2,z3,z4,z681,z6]),(1,[z41,z0,z1,z2,z4,z6])],[(1,[z0,z1,z2,z280,z4,z6]),(0,[z0,z1,z2,z21,z4,z240,z6])],[(0,[z0,z1,z2,z3,z189,z4,z6]),(0,[z0,z1,z2,z135,z3,z4,z6]),(0,[z0,z1,z2,z99,z4,z6,z55])],[(0,[z0,z682,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z683]),(0,[z124,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z21,z4,z684,z6]),(0,[z229,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z685,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z163,z6]),(0,[z130,z0,z1,z2,z4,z6,z97])],[(0,[z0,z1,z2,z3,z686,z4,z6]),(1,[z0,z1,z171,z3,z4,z6]),(0,[z0,z1,z2,z135,z10,z4,z6]),(0,[z0,z1,z2,z3,z4,z240,z6]),(0,[z0,z1,z2,z10,z3,z4,z6])],[(0,[z0,z687,z1,z2,z3,z4,z6]),(0,[z17,z1,z2,z3,z4,z18,z6]),(1,[z0,z1,z2,z4,z6,z365])],[(0,[z0,z1,z38,z3,z4,z123,z6]),(0,[z531,z0,z1,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z214,z4,z6]),(0,[z0,z1,z2,z3,z4,z684,z6])],[(0,[z0,z1,z2,z688,z3,z4,z6]),(0,[z689,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z10,z4,z6,z55])],[(0,[z690,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z6,z97]),(0,[z41,z0,z1,z2,z3,z4,z40])],[(1,[z0,z1,z2,z4,z375,z6]),(1,[z0,z1,z2,z197,z4,z6]),(0,[z0,z1,z2,z10,z170,z4,z6])],[(0,[z179,z341,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z468]),(0,[z0,z122,z1,z2,z3,z4,z6])]],
   [[],[(0,[z124,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z691,z4,z6])],[(0,[z0,z1,z2,z692,z3,z4,z6]),(0,[z92,z0,z1,z2,z367,z4,z6]),(0,[z0,z122,z1,z2,z4,z6,z55]),(0,[z0,z1,z2,z10,z4,z6,z97])],[(0,[z88,z0,z404,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z64,z4,z6]),(0,[z0,z1,z2,z3,z152,z4,z6])],[(1,[z0,z1,z38,z4,z6,z55]),(0,[z124,z0,z1,z43,z3,z4,z6]),(0,[z693,z0,z1,z2,z3,z4,z6]),(1,[z126,z1,z2,z3,z4,z96]),(0,[z0,z1,z2,z3,z694,z4,z6]),(0,[z695,z0,z1,z2,z3,z4,z6])],[(0,[z35,z0,z1,z2,z4,z6,z55]),(0,[z0,z1,z190,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z696,z4,z6])],[(0,[z0,z1,z631,z2,z3,z4,z6]),(0,[z125,z0,z1,z2,z3,z4,z6]),(0,[z0,z636,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z697,z6]),(0,[z0,z20,z1,z2,z3,z4,z6]),(1,[z41,z0,z1,z2,z4,z40]),(1,[z0,z1,z2,z10,z4,z6]),(0,[z0,z1,z698,z2,z3,z4,z6])],[(0,[z118,z0,z1,z38,z3,z4,z6]),(0,[z1,z2,z38,z3,z4,z18,z6])],[(0,[z699,z0,z1,z2,z3,z4,z6]),(0,[z125,z0,z1,z2,z4,z6,z55]),(0,[z0,z275,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z700,z4,z6]),(0,[z701,z0,z1,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z4,z6,z198]),(1,[z0,z1,z2,z298,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z702]),(0,[z0,z703,z1,z2,z3,z4,z6])],[(0,[z704,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z705]),(0,[z0,z1,z2,z3,z4,z46,z6]),(0,[z0,z140,z1,z2,z54,z4,z6])],[(0,[z0,z90,z1,z2,z21,z4,z6]),(0,[z706,z0,z1,z2,z3,z4,z6]),(0,[z92,z0,z2,z3,z103,z4,z6])],[],[(1,[z0,z7,z1,z2,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z707,z0,z1,z2,z4,z6]),(0,[z0,z1,z3,z4,z708,z6]),(0,[z179,z1,z231,z3,z4,z6]),(0,[z118,z0,z1,z43,z4,z55]),(0,[z41,z0,z230,z2,z4,z6]),(0,[z0,z209,z2,z21,z4,z6]),(0,[z0,z1,z3,z4,z6,z709]),(0,[z0,z122,z1,z2,z4,z365])],[(0,[z0,z1,z2,z710,z4,z6]),(0,[z0,z1,z2,z4,z6,z711]),(0,[z124,z1,z38,z4,z6,z55]),(0,[z95,z0,z1,z3,z4,z198])],[(0,[z223,z1,z38,z3,z4,z6]),(0,[z1,z38,z3,z4,z6,z68]),(1,[z1,z2,z712,z4,z6]),(0,[z0,z1,z2,z4,z6,z713]),(0,[z0,z1,z714,z3,z4,z6])],[(0,[z638,z0,z2,z3,z4,z93]),(0,[z715,z0,z1,z3,z4,z6]),(0,[z0,z716,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z484,z55]),(0,[z41,z0,z1,z2,z99,z97])],[(0,[z0,z2,z717,z89,z4,z6]),(0,[z0,z1,z2,z3,z718,z6]),(0,[z0,z1,z719,z2,z4,z6])],[(0,[z1,z109,z38,z3,z4,z6]),(0,[z88,z1,z43,z150,z4,z6]),(0,[z0,z1,z2,z21,z137,z6]),(0,[z17,z1,z2,z4,z18,z55]),(0,[z0,z107,z61,z3,z4,z6]),(0,[z0,z1,z2,z720,z4,z6]),(0,[z0,z1,z2,z721,z4,z6]),(0,[z531,z0,z1,z2,z4,z40])],[],[(0,[z114,z1,z38,z3,z4,z6]),(0,[z0,z2,z3,z4,z722,z6]),(0,[z0,z1,z2,z402,z4,z6])],[(0,[z1,z38,z21,z4,z94,z6]),(0,[z0,z1,z2,z4,z6,z723]),(0,[z0,z107,z61,z4,z6,z55]),(0,[z724,z0,z1,z2,z4,z6]),(0,[z101,z1,z141,z3,z4,z84]),(0,[z0,z1,z2,z451,z4,z55])],[(0,[z229,z0,z1,z21,z4,z6])],[(0,[z42,z206,z2,z3,z4,z6]),(0,[z0,z1,z146,z2,z4,z40]),(1,[z0,z1,z2,z725,z6])],[(0,[z41,z0,z1,z2,z623,z6]),(0,[z41,z0,z1,z2,z4,z726]),(0,[z0,z2,z3,z4,z6,z727])],[(0,[z1,z38,z3,z4,z94,z6]),(0,[z196,z1,z43,z3,z4,z6]),(0,[z0,z1,z2,z150,z4,z40]),(0,[z0,z1,z2,z447,z74,z6]),(0,[z0,z1,z2,z728,z74,z6])],[(0,[z0,z1,z2,z729,z4,z6]),(0,[z42,z206,z2,z10,z4,z6]),(0,[z0,z730,z2,z3,z4,z6]),(0,[z0,z1,z731,z3,z4,z6]),(0,[z0,z169,z2,z429,z103,z6])],[(0,[z1,z38,z3,z4,z673,z6]),(0,[z125,z1,z38,z73,z4,z6]),(0,[z0,z1,z2,z4,z6,z732])],[(0,[z41,z0,z1,z16,z4,z6]),(0,[z0,z1,z3,z267,z6,z254])]],
   [[(0,[z0,z1,z38,z3,z99,z97]),(0,[z0,z1,z2,z733,z4,z6]),(0,[z0,z1,z2,z4,z734,z6]),(0,[z0,z25,z148,z3,z4,z6]),(0,[z735,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z736,z4,z6]),(0,[z41,z20,z1,z2,z4,z6]),(0,[z229,z0,z3,z4,z6,z316])],[(0,[z0,z1,z38,z15,z4,z6]),(0,[z1,z2,z38,z3,z471,z6]),(0,[z0,z1,z2,z4,z6,z737]),(0,[z101,z41,z1,z2,z4,z6])],[(0,[z0,z1,z3,z4,z6,z738]),(0,[z0,z237,z2,z3,z74,z6])],[(0,[z35,z90,z346,z3,z4,z6]),(0,[z0,z1,z43,z162,z4,z6]),(0,[z124,z374,z2,z3,z14,z6]),(0,[z41,z0,z1,z2,z456,z6]),(0,[z0,z1,z2,z59,z4,z40]),(1,[z0,z1,z2,z298,z97])],[(0,[z0,z420,z2,z3,z4,z6]),(0,[z0,z1,z16,z21,z4,z6]),(0,[z0,z1,z2,z739,z471,z6]),(0,[z571,z0,z1,z2,z4,z55]),(0,[z0,z1,z740,z3,z4,z6]),(0,[z41,z0,z1,z2,z377,z6]),(0,[z0,z1,z2,z3,z152,z718])],[(0,[z304,z1,z38,z3,z4,z6]),(0,[z0,z1,z741,z3,z4,z6]),(0,[z0,z1,z2,z4,z742,z6]),(0,[z0,z1,z2,z743,z4,z6]),(0,[z0,z744,z2,z10,z4,z6])],[(0,[z72,z1,z38,z3,z24,z6]),(0,[z1,z38,z3,z4,z681,z6]),(0,[z0,z1,z38,z182,z4,z6]),(0,[z0,z745,z2,z3,z4,z6]),(0,[z0,z746,z1,z3,z4,z6]),(0,[z0,z1,z2,z298,z6,z340])],[(0,[z0,z1,z2,z3,z4,z747]),(0,[z0,z420,z2,z4,z6,z55]),(0,[z748,z1,z2,z3,z4,z6]),(0,[z41,z0,z1,z749,z4,z6]),(0,[z41,z0,z1,z2,z21,z6]),(0,[z0,z1,z21,z4,z6,z83])],[(0,[z0,z1,z67,z3,z4,z6]),(0,[z750,z0,z1,z2,z4,z40]),(0,[z0,z1,z2,z99,z4,z365]),(0,[z1,z2,z4,z6,z55,z751])],[(0,[z0,z752,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z753]),(0,[z334,z1,z43,z3,z4,z6]),(0,[z0,z1,z754,z3,z4,z6]),(0,[z0,z746,z1,z4,z6,z55])],[(0,[z0,z755,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z756,z6])],[(0,[z0,z1,z79,z3,z4,z6]),(0,[z368,z1,z43,z3,z4,z6]),(0,[z0,z1,z67,z4,z6,z55]),(0,[z0,z1,z2,z4,z757,z6]),(0,[z0,z1,z3,z4,z6,z83]),(0,[z0,z1,z2,z4,z365,z55])],[(0,[z758,z0,z1,z2,z4,z40]),(0,[z1,z3,z4,z6,z759,z102])],[(0,[z0,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z4,z6,z760]),(0,[z0,z761,z1,z2,z4,z6]),(0,[z278,z229,z1,z3,z4,z6])],[(0,[z1,z38,z3,z143,z4,z6]),(0,[z0,z1,z91,z3,z4,z6]),(0,[z88,z1,z2,z98,z4,z6]),(0,[z0,z1,z762,z3,z4,z6]),(0,[z0,z1,z79,z4,z6,z55]),(1,[z0,z1,z3,z763,z6])],[(0,[z501,z1,z38,z3,z4,z18]),(0,[z428,z1,z2,z3,z14,z6]),(0,[z0,z362,z2,z4,z6,z55]),(0,[z764,z1,z2,z3,z4,z6]),(0,[z0,z1,z765,z3,z4,z6]),(0,[z92,z0,z1,z2,z4,z40]),(0,[z0,z1,z2,z4,z100,z97])]],
   [[(0,[z575,z1,z38,z3,z4,z6]),(0,[z0,z1,z3,z4,z766,z6]),(0,[z1,z2,z10,z4,z6,z102])],[(0,[z0,z1,z43,z256,z4,z6]),(0,[z0,z1,z2,z767,z4,z6]),(0,[z0,z1,z91,z4,z6,z55]),(0,[z0,z1,z91,z10,z4,z6]),(0,[z0,z1,z762,z4,z6,z55])],[(0,[z768,z1,z2,z3,z4,z6]),(0,[z0,z122,z1,z2,z4,z40]),(0,[z0,z769,z2,z21,z4,z6])],[(0,[z0,z1,z2,z4,z770,z6]),(0,[z0,z1,z2,z598,z4,z55]),(0,[z0,z1,z2,z771,z4,z6])],[(0,[z0,z1,z2,z3,z772,z6]),(0,[z0,z1,z38,z367,z4,z6]),(0,[z0,z1,z3,z4,z6,z773]),(0,[z0,z1,z2,z519,z4,z55]),(0,[z0,z1,z141,z3,z4,z84]),(0,[z0,z1,z2,z309,z725,z6])],[(0,[z35,z774,z2,z3,z4,z6]),(1,[z230,z38,z3,z4,z6]),(0,[z326,z1,z43,z3,z4,z6]),(0,[z117,z0,z2,z10,z46,z6]),(0,[z20,z1,z2,z10,z4,z6])],[(0,[z0,z1,z43,z21,z4,z6]),(0,[z249,z0,z1,z43,z4,z6]),(0,[z0,z1,z775,z3,z4,z6]),(0,[z0,z776,z1,z2,z4,z6]),(0,[z41,z0,z1,z2,z21,z134])],[(1,[z237,z38,z3,z4,z6]),(0,[z0,z1,z38,z129,z4,z6]),(0,[z0,z1,z38,z4,z97,z55]),(0,[z1,z2,z73,z712,z4,z6]),(0,[z368,z1,z3,z267,z4,z6])],[(0,[z0,z1,z2,z3,z4,z777]),(0,[z638,z1,z38,z3,z4,z6]),(0,[z0,z69,z2,z3,z4,z240]),(0,[z41,z278,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z778,z6])],[(0,[z92,z0,z38,z3,z4,z93]),(0,[z278,z1,z2,z3,z4,z6]),(0,[z0,z7,z2,z4,z297,z6])],[(0,[z35,z206,z38,z3,z4,z6]),(0,[z0,z1,z2,z440,z4,z6]),(0,[z0,z1,z2,z4,z76,z55]),(0,[z1,z2,z3,z4,z6,z779]),(0,[z0,z1,z2,z170,z6,z97]),(0,[z130,z1,z2,z4,z6,z102])],[(0,[z42,z206,z217,z3,z4,z6]),(0,[z17,z1,z173,z3,z4,z18]),(0,[z0,z1,z2,z780,z4,z6])],[(0,[z0,z1,z2,z500,z4,z6]),(0,[z0,z1,z53,z390,z4,z6]),(0,[z0,z1,z2,z781,z4,z6]),(0,[z0,z782,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z6,z783]),(0,[z278,z1,z2,z4,z6,z55]),(0,[z278,z1,z2,z10,z4,z6])],[(0,[z126,z1,z38,z10,z4,z6]),(0,[z0,z38,z3,z4,z6,z316]),(0,[z1,z43,z204,z3,z4,z6]),(0,[z0,z1,z2,z298,z21,z6]),(0,[z0,z352,z1,z2,z451,z4])],[(0,[z0,z1,z2,z447,z4,z6]),(0,[z0,z1,z2,z728,z4,z6])],[(0,[z341,z1,z38,z21,z4,z6]),(0,[z193,z1,z38,z3,z4,z6]),(0,[z0,z784,z2,z3,z4,z6]),(0,[z0,z352,z1,z2,z4,z365])]],
   [[(0,[z0,z374,z2,z10,z4,z6]),(0,[z0,z1,z2,z785,z4,z6]),(0,[z0,z1,z2,z537,z4,z55]),(0,[z0,z1,z786,z3,z4,z6])],[(0,[z0,z1,z787,z3,z4,z6]),(0,[z0,z1,z2,z10,z4,z611]),(0,[z0,z1,z2,z3,z471,z6])],[(0,[z0,z1,z788,z3,z4,z6]),(0,[z0,z230,z2,z3,z4,z6]),(0,[z41,z0,z1,z43,z4,z6]),(0,[z517,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z789,z4,z6]),(0,[z0,z784,z2,z10,z4,z6])],[(0,[z0,z1,z2,z4,z6,z790]),(0,[z0,z1,z43,z309,z21,z6]),(0,[z0,z2,z4,z316,z97,z55])],[(0,[z42,z206,z233,z3,z4,z6]),(0,[z0,z237,z2,z3,z4,z6]),(0,[z35,z90,z38,z3,z4,z6]),(0,[z0,z1,z38,z23,z4,z6]),(0,[z125,z1,z2,z4,z6,z158]),(0,[z0,z1,z2,z10,z471,z6]),(0,[z0,z1,z2,z791,z4,z6])],[(0,[z117,z206,z38,z3,z4,z6]),(0,[z124,z1,z38,z3,z14,z6]),(0,[z0,z230,z2,z4,z6,z55]),(0,[z0,z1,z2,z792,z4,z6]),(0,[z0,z80,z2,z717,z4,z6]),(0,[z572,z0,z417,z2,z4,z6])],[(0,[z1,z204,z38,z3,z4,z6]),(0,[z52,z1,z2,z98,z4,z6])],[(0,[z81,z206,z38,z3,z4,z6]),(0,[z0,z237,z2,z4,z6,z55]),(0,[z0,z1,z2,z284,z4,z40])],[(0,[z0,z774,z2,z3,z4,z6]),(0,[z0,z2,z4,z297,z6,z55]),(0,[z0,z793,z2,z3,z4,z6])],[(0,[z1,z392,z38,z3,z24,z6]),(0,[z0,z1,z2,z189,z4,z6]),(1,[z1,z2,z3,z4,z794])],[(0,[z656,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z99,z4,z40]),(0,[z0,z285,z2,z4,z6,z136])],[(0,[z0,z1,z2,z795,z4,z6]),(0,[z0,z1,z3,z4,z6,z796]),(0,[z0,z793,z2,z4,z6,z55]),(0,[z0,z481,z2,z4,z6,z199])],[(0,[z501,z0,z1,z3,z4,z195]),(0,[z17,z0,z1,z2,z4,z40])],[(0,[z244,z206,z38,z3,z4,z6]),(0,[z0,z1,z2,z797,z4,z6]),(0,[z0,z1,z231,z189,z4,z6]),(0,[z0,z1,z2,z3,z718,z4])],[(0,[z798,z0,z2,z3,z4,z6]),(0,[z0,z352,z1,z2,z4,z6])],[(0,[z41,z0,z1,z36,z4,z6]),(0,[z0,z1,z2,z799,z4,z6]),(0,[z126,z1,z800,z3,z4,z6]),(0,[z41,z72,z1,z2,z24,z6]),(0,[z0,z1,z801,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z802,z4,z6]),(0,[z490,z1,z2,z150,z4,z6])],[(0,[z0,z1,z803,z3,z4,z6]),(0,[z48,z1,z38,z3,z4,z6]),(0,[z0,z1,z38,z152,z4,z55]),(0,[z804,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z805,z6])],[(0,[z0,z1,z2,z806,z4,z6]),(0,[z0,z404,z325,z3,z4,z6]),(0,[z41,z0,z1,z231,z4,z6]),(0,[z0,z1,z2,z4,z6,z468]),(0,[z41,z327,z0,z2,z4,z6])],[(0,[z41,z35,z90,z2,z4,z6]),(0,[z0,z1,z807,z3,z4,z6]),(0,[z0,z1,z2,z808,z4,z6]),(0,[z0,z1,z2,z809,z4,z6])],[(0,[z42,z206,z2,z261,z4,z6]),(0,[z0,z1,z2,z3,z4,z810]),(0,[z0,z1,z2,z4,z6,z811]),(0,[z0,z1,z609,z3,z438,z6]),(0,[z0,z1,z2,z812,z4,z6])],[(0,[z1,z230,z38,z3,z4,z6]),(0,[z1,z231,z38,z3,z4,z6]),(0,[z813,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z814,z6]),(0,[z0,z1,z2,z815,z4,z6]),(0,[z210,z1,z38,z3,z4,z6]),(1,[z0,z1,z43,z4,z40]),(0,[z0,z1,z816,z3,z4,z6]),(0,[z0,z1,z2,z4,z155,z55])],[(0,[z1,z237,z38,z3,z4,z6]),(0,[z41,z0,z1,z173,z4,z6]),(0,[z0,z1,z817,z3,z4,z6]),(0,[z553,z0,z1,z2,z4,z55])],[(0,[z1,z38,z3,z4,z78,z6]),(0,[z818,z0,z1,z3,z4,z6]),(0,[z0,z819,z1,z3,z4,z6]),(0,[z0,z1,z2,z820,z4,z6]),(0,[z0,z1,z2,z821,z4,z6]),(0,[z0,z1,z2,z3,z822,z6]),(0,[z130,z0,z1,z2,z99,z97])],[(0,[z823,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z824])],[(0,[z0,z1,z2,z825,z4,z6]),(0,[z41,z0,z1,z826,z4,z6])],[(0,[z69,z206,z38,z3,z4,z6]),(0,[z126,z1,z38,z3,z74,z6]),(0,[z0,z1,z43,z402,z4,z6]),(0,[z0,z69,z2,z4,z240,z468]),(0,[z0,z1,z2,z827,z4,z6]),(0,[z0,z1,z828,z3,z4,z6])],[(0,[z41,z0,z1,z38,z21,z6]),(0,[z1,z38,z98,z3,z4,z6]),(0,[z41,z57,z1,z2,z4,z6]),(0,[z0,z1,z829,z3,z4,z6]),(0,[z196,z1,z2,z21,z4,z6]),(0,[z41,z0,z1,z2,z725,z6])],[(0,[z0,z1,z217,z500,z4,z6]),(0,[z35,z0,z1,z2,z4,z40]),(0,[z0,z7,z1,z43,z4,z6]),(0,[z0,z122,z1,z2,z3,z279]),(0,[z0,z1,z3,z4,z709,z198])],[(0,[z0,z1,z3,z4,z830,z6]),(0,[z0,z1,z3,z4,z6,z831]),(0,[z0,z1,z2,z309,z170,z6]),(0,[z0,z1,z832,z21,z4,z6])],[(0,[z0,z1,z2,z833,z4,z6]),(0,[z0,z1,z2,z3,z834,z6]),(0,[z0,z1,z53,z59,z4,z6]),(0,[z0,z1,z835,z21,z4,z6])]],
   [[(0,[z42,z206,z2,z4,z6,z55]),(0,[z269,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z836,z4,z6]),(0,[z837,z1,z2,z10,z4,z6]),(0,[z0,z352,z122,z1,z2,z152])],[(0,[z1,z2,z3,z4,z6,z838]),(0,[z0,z352,z1,z2,z4,z40])],[(0,[z0,z1,z38,z291,z4,z6]),(0,[z0,z1,z2,z330,z4,z6]),(0,[z0,z1,z2,z267,z4,z40]),(0,[z0,z1,z2,z4,z119,z365])],[(0,[z1,z38,z10,z4,z24,z6]),(0,[z126,z1,z2,z3,z4,z683]),(0,[z1,z2,z712,z150,z4,z6]),(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z81,z1,z2,z4,z40]),(0,[z0,z664,z2,z135,z4,z6]),(0,[z0,z2,z3,z4,z240,z839])],[(0,[z575,z206,z2,z3,z4,z6]),(0,[z125,z1,z2,z73,z4,z6]),(0,[z0,z1,z2,z24,z97,z55]),(0,[z840,z1,z2,z21,z4,z6])],[(0,[z0,z744,z2,z3,z4,z6])],[(0,[z0,z1,z233,z500,z4,z6]),(0,[z0,z1,z38,z3,z841,z4]),(0,[z0,z1,z231,z330,z4,z6]),(0,[z0,z1,z173,z21,z4,z6]),(0,[z0,z1,z2,z152,z97,z55]),(0,[z9,z1,z2,z413,z4,z6]),(0,[z0,z1,z2,z3,z99,z97])],[(0,[z0,z1,z2,z15,z4,z6])],[(0,[z1,z631,z38,z3,z4,z18]),(0,[z0,z1,z38,z4,z6,z842]),(0,[z327,z0,z38,z3,z4,z6]),(0,[z0,z420,z43,z3,z4,z6]),(0,[z117,z0,z1,z2,z4,z40]),(0,[z0,z1,z2,z843,z4,z6]),(0,[z351,z227,z1,z2,z4,z6])],[(0,[z0,z140,z1,z255,z4,z6]),(0,[z0,z1,z2,z152,z4,z40]),(0,[z0,z275,z2,z178,z4,z6]),(0,[z0,z1,z2,z10,z99,z97])],[],[(0,[z0,z1,z2,z844,z4,z6]),(0,[z368,z1,z2,z21,z4,z6]),(0,[z0,z1,z845,z3,z4,z6]),(0,[z0,z1,z2,z846,z6,z55])],[(0,[z0,z1,z2,z10,z4,z647])],[(0,[z0,z1,z847,z3,z4,z6]),(0,[z0,z362,z2,z21,z4,z6]),(0,[z0,z1,z2,z10,z4,z540]),(0,[z0,z69,z2,z3,z4,z839]),(0,[z0,z1,z2,z848,z4,z6])],[(0,[z455,z0,z1,z3,z163,z6]),(0,[z0,z1,z363,z390,z4,z6]),(0,[z0,z1,z2,z3,z4,z726]),(0,[z1,z2,z10,z849,z4,z6])],[(0,[z1,z38,z3,z4,z6,z139]),(0,[z0,z1,z2,z3,z850,z6]),(0,[z0,z81,z2,z4,z430,z6])]],
   [[(0,[z774,z1,z2,z3,z4,z6]),(0,[z8,z1,z38,z21,z4,z6]),(0,[z0,z362,z43,z3,z4,z6]),(0,[z0,z25,z3,z376,z4,z6]),(0,[z0,z1,z2,z152,z4,z100]),(0,[z0,z1,z851,z3,z4,z6])],[(0,[z0,z1,z43,z429,z4,z6]),(0,[z0,z1,z43,z26,z4,z6]),(0,[z0,z1,z2,z717,z4,z6]),(0,[z0,z1,z2,z4,z852,z40])],[(0,[z0,z1,z2,z853,z4,z6]),(0,[z0,z1,z854,z3,z4,z6]),(0,[z1,z38,z10,z4,z18,z6]),(0,[z1,z2,z3,z4,z18,z794]),(0,[z0,z855,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z46,z40])],[(0,[z1,z38,z148,z3,z4,z6]),(0,[z20,z1,z37,z3,z4,z6])],[(0,[z706,z1,z2,z150,z4,z6]),(0,[z0,z1,z2,z4,z610,z55]),(0,[z0,z1,z856,z3,z4,z6]),(0,[z0,z1,z2,z10,z4,z655]),(0,[z0,z1,z2,z10,z4,z667])],[(0,[z0,z109,z2,z3,z103,z6]),(0,[z20,z1,z2,z3,z4,z6]),(0,[z857,z0,z2,z3,z4,z6]),(0,[z20,z107,z1,z3,z4,z6]),(0,[z117,z0,z2,z3,z46,z6]),(0,[z0,z858,z2,z3,z4,z6]),(0,[z0,z1,z2,z284,z4,z55]),(0,[z0,z2,z21,z4,z6,z316])],[(0,[z0,z2,z4,z6,z316,z55])],[(0,[z283,z1,z38,z3,z4,z6]),(1,[z1,z38,z3,z471,z6]),(0,[z1,z38,z3,z4,z6,z158]),(0,[z41,z0,z1,z43,z167,z6]),(0,[z0,z1,z325,z10,z4,z6]),(0,[z1,z2,z3,z14,z471,z6]),(0,[z0,z1,z2,z4,z6,z859]),(0,[z0,z1,z856,z4,z6,z55])],[(0,[z65,z860,z1,z3,z4,z6]),(0,[z20,z1,z2,z4,z6,z55]),(0,[z118,z0,z1,z2,z4,z40])],[(0,[z0,z1,z861,z3,z4,z6]),(0,[z0,z1,z392,z3,z267,z6]),(0,[z1,z79,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z6,z316]),(0,[z41,z0,z1,z2,z294,z6])],[(0,[z0,z121,z1,z2,z4,z55]),(0,[z0,z1,z2,z367,z4,z6]),(0,[z249,z0,z1,z2,z170,z6])],[(0,[z0,z1,z2,z3,z862,z6]),(0,[z406,z90,z2,z3,z4,z6]),(0,[z41,z227,z1,z38,z4,z6]),(0,[z88,z0,z1,z2,z4,z40]),(0,[z0,z1,z2,z863,z4,z6]),(0,[z864,z1,z2,z3,z4,z6]),(0,[z95,z1,z204,z3,z4,z6]),(0,[z0,z1,z2,z182,z4,z134])],[(0,[z1,z38,z274,z3,z4,z6]),(0,[z0,z69,z43,z3,z4,z240]),(0,[z1,z2,z3,z4,z6,z751])],[(0,[z126,z1,z38,z3,z4,z6]),(0,[z0,z1,z38,z865,z4,z6]),(0,[z0,z1,z38,z4,z6,z310]),(0,[z866,z0,z1,z3,z4,z6]),(0,[z278,z1,z43,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z867]),(0,[z0,z2,z4,z375,z297,z6]),(0,[z41,z0,z1,z2,z21,z40]),(0,[z0,z1,z2,z4,z97,z55])],[(0,[z0,z1,z43,z440,z4,z6]),(0,[z41,z868,z1,z2,z4,z6]),(0,[z41,z0,z1,z2,z4,z869]),(0,[z864,z1,z2,z4,z6,z55])],[(0,[z41,z35,z1,z38,z4,z6]),(0,[z0,z870,z1,z2,z4,z6]),(0,[z871,z0,z1,z2,z4,z6]),(0,[z41,z92,z0,z2,z4,z93]),(0,[z872,z1,z2,z10,z4,z6])]],
   [[(0,[z0,z1,z43,z500,z4,z6]),(0,[z0,z374,z2,z3,z4,z6]),(0,[z0,z1,z2,z873,z4,z6]),(0,[z0,z404,z38,z3,z4,z6]),(0,[z126,z1,z38,z4,z6,z55]),(0,[z406,z1,z38,z3,z4,z6]),(0,[z41,z0,z404,z2,z4,z6]),(0,[z0,z1,z2,z4,z874,z6]),(0,[z0,z1,z2,z49,z97,z55])],[(0,[z0,z1,z875,z3,z4,z6]),(0,[z1,z2,z3,z876,z24,z6]),(0,[z0,z1,z2,z3,z4,z877]),(0,[z19,z0,z1,z2,z4,z40])],[(0,[z0,z90,z1,z2,z4,z40]),(0,[z0,z1,z631,z3,z4,z123]),(0,[z1,z300,z38,z3,z4,z6]),(0,[z0,z1,z43,z447,z4,z6]),(0,[z0,z1,z2,z4,z705,z55]),(0,[z41,z0,z1,z4,z353,z6]),(0,[z92,z0,z2,z10,z4,z93])],[(0,[z0,z352,z1,z38,z4,z6]),(0,[z0,z374,z2,z4,z6,z55])],[(0,[z0,z1,z448,z21,z4,z6]),(0,[z0,z1,z2,z878,z4,z6]),(0,[z0,z301,z1,z54,z4,z6]),(0,[z0,z1,z2,z4,z119,z40])],[(0,[z0,z302,z1,z508,z4,z6]),(0,[z0,z1,z2,z10,z4,z619]),(0,[z0,z1,z2,z487,z4,z6]),(0,[z0,z879,z2,z3,z4,z6]),(0,[z880,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z881,z6]),(0,[z0,z230,z43,z3,z4,z6]),(0,[z882,z0,z1,z2,z4,z6]),(0,[z41,z0,z1,z2,z170,z6])],[(0,[z130,z0,z1,z43,z4,z6]),(0,[z88,z420,z2,z150,z4,z6]),(0,[z0,z1,z2,z4,z883,z40])],[(0,[z0,z237,z43,z3,z4,z6])],[(0,[z0,z884,z2,z3,z4,z6]),(0,[z0,z230,z231,z3,z4,z6]),(0,[z0,z1,z2,z152,z4,z885]),(0,[z327,z0,z2,z4,z6,z310])],[(0,[z35,z90,z2,z3,z4,z6]),(0,[z0,z1,z38,z10,z4,z119]),(0,[z0,z1,z2,z886,z4,z6]),(0,[z0,z25,z64,z21,z4,z6]),(0,[z0,z1,z2,z887,z4,z6])],[(0,[z0,z1,z38,z127,z4,z6]),(0,[z1,z38,z3,z4,z6,z191]),(0,[z118,z0,z1,z2,z4,z888])],[(0,[z1,z314,z38,z3,z4,z6]),(0,[z72,z1,z2,z3,z471,z6]),(0,[z0,z1,z2,z889,z4,z6]),(0,[z0,z1,z2,z4,z6,z890]),(0,[z891,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z892])],[(0,[z35,z90,z2,z10,z4,z6]),(0,[z0,z1,z51,z59,z4,z6]),(0,[z0,z1,z43,z189,z4,z6]),(0,[z0,z1,z2,z4,z620,z55])],[(0,[z90,z774,z2,z3,z4,z6]),(0,[z0,z1,z893,z3,z4,z6]),(0,[z126,z1,z2,z127,z4,z96])],[(0,[z0,z1,z206,z2,z4,z40]),(0,[z1,z38,z3,z4,z303,z6]),(0,[z1,z204,z2,z10,z4,z6])]],
   [[(0,[z126,z1,z2,z4,z96,z55])],[(0,[z179,z1,z43,z21,z4,z6]),(0,[z0,z1,z894,z3,z4,z6]),(0,[z895,z1,z2,z3,z4,z6])],[(0,[z35,z1,z38,z10,z4,z6]),(0,[z124,z1,z38,z21,z4,z6]),(0,[z0,z45,z1,z43,z4,z6]),(0,[z125,z1,z243,z73,z4,z6]),(0,[z227,z0,z1,z2,z4,z40])],[(0,[z0,z1,z38,z280,z4,z6]),(0,[z0,z557,z2,z89,z4,z6]),(0,[z339,z0,z1,z2,z21,z6]),(0,[z0,z1,z3,z4,z763,z6]),(0,[z0,z1,z3,z896,z4,z6])],[(0,[z177,z1,z38,z4,z24,z6]),(0,[z41,z48,z1,z38,z4,z6]),(0,[z0,z1,z3,z897,z4,z6]),(0,[z0,z1,z2,z182,z4,z119])],[(0,[z95,z0,z1,z21,z4,z198]),(0,[z0,z352,z1,z2,z4,z97])],[(0,[z0,z1,z43,z4,z6,z468]),(0,[z0,z404,z2,z73,z4,z6]),(0,[z0,z1,z2,z54,z4,z40])],[(0,[z1,z43,z602,z3,z4,z6]),(0,[z0,z80,z417,z2,z4,z6]),(0,[z0,z1,z2,z4,z119,z888])],[(0,[z1,z38,z3,z4,z211,z6]),(0,[z0,z1,z38,z4,z6,z365]),(0,[z41,z0,z1,z43,z4,z40]),(0,[z0,z898,z1,z2,z4,z6]),(0,[z41,z0,z1,z2,z586,z6]),(0,[z249,z0,z1,z2,z4,z134]),(0,[z0,z1,z2,z899,z4,z6])],[(0,[z1,z43,z38,z10,z4,z6]),(0,[z0,z107,z61,z21,z4,z6]),(0,[z0,z1,z2,z21,z349,z6]),(0,[z0,z1,z4,z353,z6,z55])],[(0,[z0,z1,z2,z3,z4,z900]),(0,[z0,z1,z2,z901,z4,z6]),(0,[z0,z1,z43,z815,z4,z6])],[(0,[z0,z1,z902,z3,z4,z6]),(0,[z0,z1,z903,z3,z4,z6])],[(0,[z904,z0,z1,z2,z4,z6]),(0,[z0,z1,z38,z4,z375,z6]),(0,[z0,z1,z38,z197,z4,z6]),(0,[z0,z1,z2,z3,z4,z709])],[(0,[z1,z905,z38,z3,z4,z6]),(0,[z179,z230,z2,z3,z4,z6]),(0,[z0,z1,z906,z3,z4,z6]),(0,[z0,z1,z171,z10,z4,z6])],[(0,[z42,z206,z2,z21,z4,z6]),(0,[z179,z1,z448,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z907]),(0,[z0,z908,z1,z2,z4,z6]),(0,[z0,z1,z37,z2,z4,z40]),(0,[z0,z1,z909,z10,z4,z6]),(0,[z0,z1,z2,z3,z718,z97])],[(0,[z237,z2,z38,z3,z4,z6]),(0,[z179,z237,z2,z3,z4,z6]),(0,[z0,z1,z2,z10,z4,z702]),(0,[z0,z1,z2,z910,z4,z6]),(0,[z0,z285,z2,z89,z4,z6]),(0,[z0,z1,z2,z4,z911,z6])]],
   [[(0,[z912,z0,z1,z2,z4,z6]),(0,[z338,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z913]),(0,[z0,z1,z2,z914,z4,z6]),(0,[z0,z107,z1,z2,z4,z40]),(0,[z0,z2,z10,z4,z297,z6]),(0,[z0,z2,z915,z3,z4,z6]),(0,[z837,z1,z2,z3,z4,z6])],[(0,[z42,z206,z43,z3,z4,z6]),(0,[z916,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z917,z4,z6]),(0,[z0,z1,z2,z421,z21,z6]),(0,[z0,z1,z2,z4,z163,z40]),(0,[z918,z1,z2,z3,z4,z6]),(0,[z249,z0,z1,z2,z437,z6]),(0,[z0,z919,z2,z3,z4,z6])],[(0,[z1,z344,z38,z3,z4,z6]),(0,[z126,z1,z38,z3,z4,z96]),(0,[z0,z1,z2,z74,z6,z55]),(0,[z0,z219,z2,z135,z4,z6]),(0,[z0,z1,z2,z920,z4,z6]),(0,[z0,z1,z2,z4,z240,z40]),(0,[z19,z0,z1,z3,z545,z6]),(0,[z95,z0,z1,z2,z4,z40]),(0,[z41,z0,z921,z2,z4,z6])],[(0,[z0,z302,z1,z54,z4,z6]),(0,[z922,z0,z1,z2,z4,z6]),(0,[z0,z1,z923,z3,z4,z6]),(0,[z0,z122,z1,z2,z10,z152])],[(0,[z0,z924,z2,z3,z4,z6]),(0,[z0,z140,z1,z214,z4,z6]),(0,[z0,z2,z3,z925,z4,z6]),(0,[z0,z926,z1,z2,z4,z6])],[(0,[z0,z1,z38,z10,z4,z6]),(0,[z0,z1,z2,z927,z4,z6]),(0,[z86,z0,z1,z255,z4,z6]),(0,[z117,z0,z2,z3,z928,z6])],[(0,[z0,z1,z2,z929,z4,z6]),(0,[z0,z81,z2,z637,z4,z6]),(0,[z0,z1,z43,z330,z4,z6]),(0,[z118,z0,z1,z2,z4,z55]),(1,[z0,z1,z2,z3,z718])],[(0,[z0,z687,z2,z89,z4,z6]),(0,[z0,z1,z2,z930,z4,z6]),(0,[z0,z1,z43,z4,z5,z6]),(0,[z41,z0,z1,z448,z4,z6]),(0,[z0,z2,z3,z103,z928,z6]),(0,[z0,z1,z2,z62,z4,z365])],[(0,[z0,z1,z38,z298,z4,z6]),(0,[z0,z420,z2,z21,z4,z6]),(0,[z0,z1,z364,z59,z4,z6]),(0,[z0,z1,z2,z931,z4,z6]),(0,[z0,z209,z7,z2,z4,z6]),(0,[z0,z1,z2,z932,z4,z6]),(0,[z1,z3,z4,z6,z83,z102])],[(0,[z1,z206,z38,z10,z4,z6]),(0,[z0,z1,z3,z4,z933,z6]),(0,[z934,z0,z1,z2,z4,z6])],[(0,[z41,z0,z1,z2,z672,z6]),(0,[z0,z1,z2,z935,z4,z6]),(0,[z0,z1,z936,z3,z4,z6]),(0,[z0,z1,z2,z937,z4,z6]),(0,[z0,z1,z938,z2,z4,z40]),(0,[z939,z1,z2,z10,z4,z6])],[],[(0,[z41,z42,z206,z2,z4,z6]),(0,[z501,z0,z1,z3,z4,z198]),(0,[z0,z1,z2,z3,z841,z4]),(0,[z0,z1,z67,z21,z4,z6]),(0,[z0,z1,z2,z10,z4,z28]),(0,[z0,z940,z1,z3,z4,z6])],[(0,[z0,z1,z2,z941,z4,z6]),(0,[z41,z0,z1,z2,z437,z6])],[(0,[z0,z1,z2,z4,z6,z842]),(0,[z327,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z942,z6]),(0,[z72,z1,z2,z3,z24,z6]),(0,[z0,z1,z79,z21,z4,z6]),(0,[z0,z1,z2,z4,z6,z943]),(0,[z0,z1,z2,z944,z4,z6]),(0,[z0,z1,z2,z182,z4,z6]),(0,[z0,z1,z2,z3,z725,z6]),(0,[z0,z940,z1,z4,z6,z55]),(0,[z0,z1,z945,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z6,z946]),(0,[z1,z38,z3,z350,z4,z6]),(0,[z0,z1,z2,z4,z6,z947]),(0,[z0,z1,z2,z948,z4,z6]),(0,[z0,z1,z2,z949,z4,z6]),(0,[z542,z48,z1,z2,z4,z6])],[(0,[z0,z1,z38,z3,z4,z134]),(0,[z57,z1,z2,z280,z4,z6]),(0,[z327,z0,z2,z10,z4,z6])],[(0,[z72,z1,z2,z10,z24,z6]),(0,[z0,z2,z3,z4,z6,z950]),(0,[z0,z1,z91,z21,z4,z6]),(0,[z0,z1,z945,z4,z6,z55])],[(0,[z951,z0,z1,z2,z4,z6]),(0,[z0,z952,z2,z3,z4,z6]),(0,[z278,z1,z2,z3,z14,z6])],[(0,[z0,z870,z1,z38,z4,z6]),(0,[z953,z1,z2,z3,z4,z6]),(0,[z0,z921,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z4,z954]),(0,[z0,z1,z4,z6,z83,z55]),(0,[z0,z1,z955,z3,z4,z6])],[(0,[z0,z1,z2,z956,z4,z6]),(0,[z0,z1,z2,z4,z167,z40]),(0,[z0,z1,z957,z3,z4,z6])],[(0,[z1,z38,z4,z24,z6,z55]),(0,[z625,z1,z43,z3,z4,z6]),(0,[z41,z0,z1,z2,z74,z6]),(0,[z41,z0,z1,z171,z4,z6]),(0,[z0,z1,z2,z958,z4,z6])],[(0,[z1,z800,z38,z3,z4,z6]),(0,[z126,z1,z38,z3,z4,z18]),(0,[z0,z1,z800,z3,z4,z6]),(0,[z0,z1,z325,z3,z4,z6]),(0,[z953,z1,z2,z4,z6,z55])],[(0,[z0,z1,z2,z959,z4,z6]),(0,[z95,z20,z1,z3,z4,z6]),(0,[z19,z20,z1,z3,z163,z6]),(0,[z0,z1,z141,z21,z4,z84]),(0,[z0,z1,z960,z3,z4,z6])],[(0,[z117,z0,z43,z3,z46,z6]),(0,[z20,z1,z43,z3,z4,z6]),(0,[z0,z362,z2,z447,z4,z6]),(0,[z961,z1,z2,z3,z4,z6])],[(0,[z0,z1,z38,z4,z6,z40]),(0,[z1,z38,z4,z6,z158,z55]),(0,[z0,z1,z325,z4,z6,z55]),(0,[z41,z0,z1,z243,z4,z6]),(0,[z117,z368,z2,z3,z4,z6]),(0,[z0,z1,z2,z135,z4,z40]),(0,[z20,z1,z609,z3,z4,z6]),(0,[z0,z1,z775,z21,z4,z6])],[(0,[z72,z0,z1,z2,z4,z40]),(0,[z0,z1,z2,z962,z4,z6])],[(0,[z0,z1,z3,z99,z83,z97])],[(0,[z57,z1,z38,z3,z4,z6]),(0,[z1,z963,z2,z3,z4,z6]),(0,[z0,z1,z2,z725,z167,z6]),(0,[z278,z1,z2,z21,z4,z6])],[(0,[z0,z1,z43,z367,z4,z6]),(0,[z0,z85,z2,z135,z4,z6]),(0,[z0,z362,z448,z3,z4,z6]),(0,[z0,z1,z2,z449,z21,z6])],[(0,[z0,z1,z2,z4,z6,z964]),(0,[z872,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z6,z965]),(0,[z966,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z129,z4,z6]),(0,[z0,z122,z1,z2,z152,z291])],[(0,[z0,z1,z2,z4,z967,z6]),(0,[z0,z2,z3,z99,z316,z97])],[(0,[z968,z0,z1,z2,z4,z6]),(0,[z92,z0,z2,z3,z4,z93]),(0,[z0,z969,z2,z3,z4,z6])],[(0,[z0,z1,z38,z3,z74,z6]),(0,[z970,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z6,z971]),(0,[z0,z1,z2,z4,z4,z40]),(0,[z0,z1,z972,z10,z4,z6])],[(0,[z0,z1,z346,z3,z4,z6]),(1,[z774,z2,z3,z4,z6]),(0,[z0,z1,z2,z973,z4,z6]),(0,[z0,z374,z43,z3,z4,z6]),(0,[z0,z1,z331,z54,z4,z6])],[(0,[z0,z1,z2,z974,z4,z6]),(0,[z0,z1,z2,z21,z471,z6]),(0,[z975,z0,z1,z2,z4,z6]),(0,[z0,z25,z64,z26,z4,z6])],[(0,[z206,z218,z38,z3,z4,z6]),(0,[z0,z404,z2,z3,z4,z6]),(0,[z0,z80,z38,z89,z4,z6]),(0,[z106,z1,z43,z3,z4,z6]),(0,[z0,z230,z2,z21,z4,z6]),(0,[z0,z976,z2,z3,z4,z6]),(0,[z0,z65,z1,z10,z4,z6]),(0,[z0,z1,z2,z4,z437,z55])],[(0,[z0,z1,z346,z10,z4,z6]),(0,[z977,z0,z1,z2,z4,z6]),(0,[z0,z374,z231,z3,z4,z6]),(0,[z0,z1,z10,z4,z353,z6]),(0,[z95,z0,z1,z4,z198,z55])],[(0,[z391,z1,z38,z3,z4,z6]),(0,[z0,z1,z43,z3,z471,z6]),(0,[z0,z978,z2,z3,z4,z6]),(0,[z0,z237,z2,z21,z4,z6]),(0,[z979,z1,z2,z3,z4,z6]),(0,[z0,z61,z3,z4,z532,z6])],[(0,[z101,z1,z38,z3,z4,z6]),(0,[z0,z1,z43,z487,z4,z6]),(0,[z0,z404,z2,z4,z6,z55]),(0,[z0,z404,z2,z10,z4,z6]),(0,[z0,z1,z2,z980,z4,z6])],[(0,[z981,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z982,z4,z6]),(0,[z41,z0,z1,z37,z267,z6]),(0,[z490,z1,z2,z4,z6,z110])],[(0,[z41,z0,z1,z233,z4,z6]),(0,[z117,z0,z2,z3,z207,z6]),(0,[z1,z79,z3,z4,z18,z6]),(0,[z0,z2,z135,z717,z4,z6])],[(0,[z0,z122,z1,z43,z3,z152]),(0,[z41,z0,z1,z2,z4,z983]),(0,[z249,z0,z1,z2,z4,z6])],[(0,[z0,z1,z38,z108,z4,z6]),(0,[z8,z1,z2,z150,z4,z6]),(0,[z0,z1,z2,z23,z4,z6]),(0,[z0,z1,z2,z3,z984,z6]),(0,[z0,z1,z2,z4,z6,z985])],[(0,[z124,z1,z2,z3,z14,z6])],[(0,[z1,z204,z2,z3,z4,z6])]],
   [[(0,[z35,z90,z2,z4,z6,z55]),(0,[z986,z0,z1,z2,z4,z6]),(0,[z0,z1,z448,z447,z4,z6]),(0,[z41,z987,z1,z2,z4,z6]),(0,[z229,z0,z1,z3,z99,z97])],[(0,[z0,z1,z988,z3,z4,z6]),(0,[z0,z1,z2,z127,z4,z6]),(0,[z124,z1,z2,z10,z14,z6]),(0,[z0,z1,z2,z989,z4,z6]),(0,[z0,z1,z2,z3,z4,z869]),(0,[z0,z1,z2,z990,z4,z6]),(0,[z1,z2,z4,z102,z97,z55])],[(0,[z35,z1,z38,z3,z4,z6]),(0,[z1,z204,z2,z4,z6,z55]),(0,[z0,z1,z2,z21,z6,z416]),(0,[z1,z2,z4,z6,z310,z102])],[(0,[z41,z0,z1,z2,z370,z6]),(0,[z1,z38,z3,z4,z6,z102])],[(0,[z0,z1,z2,z3,z991,z4]),(0,[z0,z385,z61,z3,z4,z6])],[(0,[z35,z1,z38,z4,z6,z55]),(0,[z0,z1,z2,z38,z4,z40]),(0,[z0,z1,z2,z4,z441,z55]),(0,[z1,z173,z3,z4,z18,z6]),(0,[z0,z1,z141,z3,z4,z709]),(0,[z41,z0,z2,z4,z6,z316]),(0,[z327,z130,z0,z2,z4,z6])],[(0,[z244,z206,z2,z3,z4,z6]),(0,[z916,z0,z1,z38,z3,z4]),(0,[z0,z1,z417,z2,z4,z40])],[(0,[z0,z90,z2,z261,z4,z6]),(0,[z0,z1,z2,z992,z4,z6]),(0,[z0,z1,z38,z4,z6,z128])],[(0,[z41,z0,z1,z2,z4,z6]),(0,[z0,z404,z190,z3,z4,z6]),(0,[z0,z1,z2,z993,z4,z6])],[(0,[z1,z43,z38,z3,z4,z6]),(0,[z41,z124,z1,z38,z4,z6]),(0,[z125,z1,z16,z73,z4,z6]),(0,[z0,z1,z2,z4,z994,z6]),(0,[z0,z1,z2,z280,z4,z6]),(0,[z0,z1,z2,z995,z4,z6]),(0,[z0,z1,z141,z2,z4,z40]),(0,[z41,z0,z1,z2,z167,z134]),(0,[z0,z1,z2,z4,z888,z55]),(0,[z327,z2,z3,z4,z6,z102])],[(0,[z0,z996,z2,z3,z4,z6]),(0,[z0,z1,z2,z44,z21,z6]),(0,[z0,z1,z2,z152,z4,z55])],[(0,[z1,z38,z3,z4,z6,z399]),(0,[z118,z0,z1,z38,z4,z55]),(0,[z0,z1,z43,z812,z4,z6]),(0,[z41,z124,z1,z2,z14,z6]),(0,[z41,z0,z1,z2,z393,z6]),(0,[z0,z1,z2,z997,z4,z6])],[(0,[z1,z43,z38,z4,z6,z55]),(0,[z0,z1,z998,z3,z4,z6]),(0,[z41,z0,z1,z2,z4,z999])],[(0,[z0,z1,z171,z3,z4,z6]),(0,[z1,z43,z3,z4,z6,z102]),(0,[z95,z0,z1,z440,z4,z198]),(0,[z0,z1,z141,z402,z4,z84])],[(0,[z0,z1,z2,z3,z876,z6]),(0,[z0,z1,z909,z3,z4,z6]),(0,[z0,z1,z2,z1000,z4,z6]),(0,[z249,z0,z122,z1,z2,z152])],[(0,[z179,z1,z2,z3,z471,z6]),(0,[z0,z1,z2,z1001,z4,z6]),(0,[z0,z1,z2,z4,z1002,z6]),(0,[z0,z122,z1,z2,z298,z6]),(0,[z0,z1,z998,z10,z4,z6])]],
   [[(0,[z1,z38,z10,z98,z4,z6]),(0,[z0,z1,z171,z4,z6,z55]),(0,[z0,z1,z53,z4,z684,z6])],[(0,[z0,z1,z2,z4,z6,z1003]),(0,[z41,z0,z209,z2,z4,z6]),(0,[z95,z0,z1,z3,z4,z709])],[(0,[z124,z230,z38,z3,z4,z6]),(0,[z92,z0,z2,z3,z4,z839]),(0,[z0,z1,z2,z897,z4,z6])],[(0,[z1,z905,z2,z3,z4,z6]),(0,[z0,z61,z1004,z3,z4,z6]),(0,[z0,z1,z59,z897,z4,z6]),(0,[z0,z1,z2,z1005,z4,z6])],[(0,[z0,z1,z43,z2,z4,z40]),(0,[z41,z0,z362,z2,z4,z6]),(0,[z0,z1,z2,z4,z134,z40]),(0,[z0,z1,z305,z71,z4,z6])],[(0,[z0,z1,z38,z3,z4,z6]),(0,[z0,z1,z43,z917,z4,z6]),(0,[z0,z1,z2,z4,z6,z1006]),(0,[z0,z1,z2,z256,z99,z97])],[(0,[z0,z1007,z2,z3,z4,z6]),(0,[z0,z1008,z1,z3,z4,z6]),(0,[z0,z1,z2,z1009,z4,z6]),(0,[z0,z1,z2,z4,z1010,z6])],[(0,[z35,z90,z36,z3,z4,z6]),(0,[z120,z1,z43,z3,z4,z6]),(0,[z1011,z0,z1,z2,z4,z6]),(0,[z41,z0,z1,z2,z4,z134]),(0,[z229,z0,z1,z4,z97,z55])],[(0,[z0,z1,z38,z4,z6,z55]),(0,[z0,z1,z38,z1012,z4,z6]),(0,[z368,z1,z64,z3,z4,z6])],[(0,[z1,z206,z38,z3,z4,z6]),(0,[z0,z1,z1013,z3,z4,z6]),(0,[z124,z1,z38,z189,z4,z6]),(0,[z0,z1,z38,z1014,z4,z6]),(0,[z368,z1,z2,z26,z4,z6]),(0,[z41,z229,z0,z1,z4,z6])],[(0,[z1,z38,z234,z4,z18,z6]),(0,[z0,z1,z38,z170,z4,z6]),(0,[z0,z1015,z2,z3,z4,z6]),(0,[z0,z1,z2,z1016,z4,z6]),(0,[z0,z25,z1,z2,z4,z40]),(0,[z939,z1,z2,z3,z4,z6]),(0,[z41,z0,z122,z1,z2,z152])],[(0,[z0,z1017,z2,z3,z4,z6]),(0,[z0,z1,z631,z3,z4,z84]),(0,[z126,z1,z2,z10,z4,z96]),(0,[z0,z1,z2,z291,z4,z6])],[(0,[z1,z206,z38,z4,z6,z55]),(0,[z0,z362,z91,z3,z4,z6]),(0,[z0,z69,z2,z162,z4,z240]),(1,[z0,z1,z2,z4,z40])],[(0,[z0,z1,z2,z4,z1018,z6]),(0,[z0,z1,z38,z1019,z4,z6]),(0,[z0,z1,z43,z3,z99,z97]),(0,[z0,z1,z2,z1020,z4,z6]),(0,[z0,z1,z1021,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z1022]),(0,[z33,z1,z2,z4,z94,z6])],[(0,[z0,z1,z1023,z3,z4,z6]),(0,[z0,z385,z344,z3,z4,z6]),(0,[z0,z1,z43,z15,z4,z6]),(0,[z0,z1,z2,z298,z4,z6]),(0,[z0,z1,z2,z194,z4,z55])],[(0,[z72,z1,z154,z3,z24,z6]),(0,[z0,z107,z3,z4,z596,z6]),(0,[z0,z1,z53,z2,z4,z40])]],
   [[(0,[z0,z1,z1024,z3,z4,z6])],[(0,[z1,z631,z2,z3,z4,z18])],[(0,[z0,z1,z2,z127,z74,z6]),(0,[z0,z1,z3,z267,z506,z6]),(0,[z0,z1,z1025,z3,z4,z6]),(0,[z222,z1,z204,z3,z4,z6])],[(0,[z72,z1,z43,z3,z24,z6]),(0,[z0,z1,z43,z182,z4,z6]),(0,[z1026,z1,z2,z3,z4,z6]),(0,[z0,z169,z2,z129,z103,z6]),(0,[z41,z0,z1,z2,z4,z1027])],[(0,[z639,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z1028,z4,z6]),(0,[z0,z1,z2,z201,z4,z55]),(0,[z327,z0,z2,z4,z6,z55])],[(0,[z0,z1,z2,z4,z1029,z6]),(0,[z0,z1,z1030,z3,z4,z6])],[],[(0,[z287,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z1031])],[(0,[z0,z1032,z1,z2,z4,z6]),(0,[z126,z362,z38,z3,z4,z6])],[(0,[z0,z1,z2,z1033,z4,z6]),(0,[z0,z1,z3,z1034,z4,z6]),(0,[z117,z0,z2,z21,z46,z6]),(0,[z20,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z99,z310,z97])],[(0,[z0,z1,z2,z1035,z4,z6]),(0,[z1,z38,z3,z24,z6,z97]),(0,[z445,z1,z38,z3,z4,z6]),(0,[z499,z1,z38,z3,z4,z6]),(0,[z41,z17,z1,z2,z4,z18]),(0,[z0,z1,z2,z10,z4,z134])],[(0,[z422,z0,z2,z89,z4,z6]),(0,[z17,z1,z38,z3,z4,z18]),(0,[z177,z0,z1,z43,z4,z6]),(0,[z41,z0,z1,z190,z4,z6]),(0,[z95,z0,z1,z3,z4,z76]),(0,[z0,z1,z2,z3,z298,z97])],[(0,[z0,z1,z1036,z3,z4,z6]),(0,[z658,z1,z38,z3,z4,z6]),(0,[z0,z230,z67,z3,z4,z6]),(0,[z1037,z0,z1,z2,z74,z6])],[(0,[z0,z275,z2,z89,z4,z6]),(0,[z0,z860,z1,z3,z4,z6]),(0,[z0,z1038,z2,z3,z4,z6]),(0,[z359,z0,z1,z2,z4,z40])],[(0,[z0,z1,z91,z447,z4,z6])],[(0,[z0,z1,z38,z234,z4,z6]),(0,[z981,z0,z1,z38,z3,z6]),(0,[z125,z1,z2,z712,z4,z6]),(0,[z0,z362,z2,z3,z471,z6]),(0,[z0,z1,z1039,z3,z4,z6]),(1,[z0,z1,z2,z4,z888])]],
   [[(0,[z0,z1,z2,z3,z1040,z6]),(0,[z0,z1041,z2,z3,z4,z6])],[(0,[z126,z1,z38,z21,z4,z6]),(0,[z249,z0,z1,z38,z4,z6]),(0,[z0,z1,z2,z3,z1042,z6]),(0,[z0,z1,z2,z4,z6,z1043]),(0,[z278,z327,z2,z3,z4,z6])],[(0,[z0,z1,z1044,z3,z4,z6]),(0,[z124,z1,z38,z330,z4,z6]),(0,[z0,z1,z1045,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1046]),(0,[z20,z25,z1,z3,z4,z6]),(0,[z0,z1,z2,z1047,z4,z6]),(0,[z0,z122,z1,z2,z182,z152])],[(0,[z0,z1,z2,z1048,z4,z6]),(0,[z0,z209,z38,z3,z4,z6]),(0,[z0,z1049,z2,z3,z4,z6]),(0,[z0,z1,z67,z189,z4,z6]),(0,[z0,z1,z972,z3,z4,z6])],[(0,[z0,z1,z43,z129,z4,z6]),(0,[z0,z1,z43,z4,z97,z55]),(0,[z0,z374,z2,z21,z4,z6]),(0,[z0,z2,z3,z4,z6,z839]),(0,[z19,z0,z3,z297,z163,z6]),(0,[z0,z1,z2,z1050,z4,z6])],[(0,[z452,z1,z38,z3,z4,z6]),(0,[z0,z1,z1051,z3,z4,z6]),(0,[z117,z0,z45,z2,z46,z6]),(0,[z0,z2,z3,z4,z1052,z6])],[(0,[z0,z1,z2,z865,z4,z6]),(0,[z92,z0,z43,z3,z4,z93]),(0,[z0,z1,z1053,z3,z4,z6]),(0,[z57,z1,z2,z10,z4,z6]),(0,[z0,z65,z1,z3,z4,z6]),(0,[z0,z1054,z2,z3,z4,z6]),(0,[z1055,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z309,z4,z40]),(0,[z0,z1,z2,z4,z6,z310])],[(0,[z227,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z954]),(0,[z41,z0,z1,z4,z6,z83]),(0,[z1056,z1,z2,z3,z4,z6])],[(0,[z0,z25,z315,z3,z4,z6]),(0,[z0,z599,z1,z288,z4,z6])],[(0,[z126,z1,z2,z3,z74,z96]),(0,[z0,z65,z1,z4,z6,z55])],[(0,[z0,z1,z346,z4,z6,z55]),(0,[z0,z404,z43,z3,z4,z6]),(0,[z0,z43,z3,z4,z297,z6]),(0,[z0,z1,z1057,z3,z4,z6]),(0,[z1056,z1,z2,z4,z6,z55])],[(0,[z41,z0,z1,z154,z4,z6]),(0,[z1,z2,z21,z4,z6,z102])],[(0,[z0,z1,z217,z10,z4,z6]),(0,[z0,z1,z2,z10,z74,z6]),(0,[z0,z1,z2,z4,z84,z40])],[(0,[z0,z1,z1058,z2,z3,z4]),(0,[z41,z0,z1,z38,z4,z6]),(0,[z0,z1,z38,z1059,z4,z6]),(0,[z1060,z65,z1,z3,z4,z6]),(0,[z41,z0,z1,z2,z167,z6])],[(0,[z35,z90,z2,z21,z4,z6]),(0,[z179,z0,z1,z2,z4,z40]),(0,[z0,z1,z2,z739,z4,z6]),(0,[z0,z1,z1061,z3,z4,z6]),(0,[z0,z1,z37,z267,z6,z55]),(0,[z0,z1,z2,z4,z251,z55])],[(0,[z0,z1,z1062,z3,z4,z6]),(0,[z0,z1,z2,z1063,z4,z6]),(0,[z41,z368,z1,z2,z4,z6]),(0,[z0,z1,z2,z1064,z4,z6])]],
   [[(0,[z0,z206,z2,z261,z4,z6]),(0,[z0,z1,z2,z1065,z4,z6]),(0,[z0,z2,z3,z4,z1066,z6])],[(0,[z0,z1,z1067,z3,z4,z6]),(0,[z35,z90,z43,z3,z4,z6]),(0,[z0,z1,z43,z23,z4,z6])],[(0,[z124,z1,z43,z3,z14,z6]),(0,[z41,z0,z237,z2,z4,z6]),(0,[z101,z1,z2,z10,z4,z6]),(0,[z0,z1,z2,z4,z134,z55])],[(0,[z0,z266,z2,z89,z4,z6]),(0,[z0,z1,z3,z1068,z4,z6]),(0,[z0,z169,z1,z2,z4,z40]),(0,[z0,z1,z1069,z3,z4,z6]),(0,[z0,z1,z2,z10,z4,z119])],[(0,[z1,z38,z4,z18,z6,z128]),(0,[z1,z2,z3,z14,z876,z6]),(0,[z0,z237,z2,z447,z4,z6])],[(0,[z124,z1,z231,z3,z14,z6]),(0,[z0,z45,z1,z4,z353,z6]),(0,[z19,z0,z209,z3,z4,z6])],[(0,[z1,z43,z425,z3,z4,z6]),(0,[z0,z1,z2,z1070,z4,z6]),(0,[z0,z1,z448,z3,z471,z6]),(0,[z0,z107,z1004,z3,z4,z6]),(0,[z0,z1,z1071,z3,z4,z6]),(0,[z1,z1072,z2,z3,z4,z6])],[(0,[z0,z1,z1073,z3,z4,z6]),(0,[z1074,z1,z2,z3,z4,z6])],[(0,[z0,z169,z38,z3,z103,z6]),(0,[z572,z0,z1,z2,z4,z40])],[(0,[z0,z1,z1075,z3,z4,z6]),(0,[z0,z1,z38,z4,z6,z253]),(0,[z0,z1,z2,z4,z215,z55]),(0,[z0,z237,z448,z3,z4,z6]),(0,[z1,z1072,z2,z4,z6,z55])],[(0,[z88,z1,z325,z150,z4,z6]),(0,[z1076,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z1077,z4,z6]),(0,[z1,z141,z204,z3,z4,z84]),(0,[z130,z0,z2,z4,z6,z316])],[(0,[z0,z1,z2,z1078,z4,z6])],[(0,[z505,z1,z38,z3,z4,z6]),(0,[z41,z0,z1,z38,z4,z134]),(0,[z0,z1,z38,z4,z100,z6]),(0,[z0,z1,z67,z330,z4,z6])],[(0,[z122,z1,z38,z3,z24,z6]),(0,[z1,z43,z905,z3,z4,z6]),(0,[z0,z1,z43,z280,z4,z6]),(0,[z227,z1,z2,z73,z4,z6]),(0,[z0,z230,z2,z189,z4,z6]),(0,[z117,z0,z3,z353,z46,z6]),(0,[z0,z2,z3,z4,z6,z1079]),(0,[z0,z1,z2,z1080,z4,z6])],[(0,[z0,z1,z43,z152,z4,z55]),(0,[z1037,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z1081,z4,z6])],[(0,[z0,z1,z38,z261,z4,z6]),(0,[z1,z38,z3,z4,z471,z6]),(0,[z0,z1,z2,z4,z6,z1082]),(0,[z0,z1,z2,z1083,z4,z6])]],
   [[(0,[z124,z374,z38,z3,z4,z6]),(0,[z0,z1,z826,z3,z4,z6]),(0,[z289,z0,z1,z2,z21,z6])],[(1,[z0,z1,z38,z4,z40]),(0,[z41,z0,z107,z61,z4,z6]),(0,[z0,z2,z3,z4,z839,z93]),(0,[z19,z0,z1,z163,z6,z55]),(0,[z0,z1,z2,z4,z6,z365])],[(0,[z0,z1,z2,z1084,z4,z6]),(0,[z1,z38,z3,z4,z6,z401]),(0,[z0,z1,z2,z1085,z4,z6]),(0,[z0,z1,z2,z4,z1086,z6]),(0,[z0,z1,z1087,z3,z4,z6]),(0,[z0,z140,z1,z54,z4,z6]),(0,[z249,z0,z1,z2,z4,z40]),(0,[z0,z1088,z2,z3,z4,z6])],[(0,[z0,z1,z1089,z3,z4,z6]),(0,[z1090,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z298,z167,z6])],[(0,[z0,z1,z3,z4,z84,z590])],[(0,[z1,z38,z4,z18,z6,z55]),(0,[z543,z0,z1,z2,z4,z55]),(0,[z0,z1,z2,z1091,z4,z6]),(0,[z0,z1,z2,z1092,z4,z6]),(0,[z0,z1,z2,z197,z4,z6]),(0,[z0,z1,z2,z4,z375,z6]),(0,[z0,z122,z1,z2,z152,z21]),(0,[z0,z1088,z2,z4,z6,z55])],[],[(0,[z41,z0,z1,z2,z629,z6]),(0,[z0,z2,z3,z1093,z4,z6]),(0,[z229,z130,z0,z1,z4,z6])],[(0,[z0,z45,z1,z2,z4,z6]),(0,[z95,z0,z1,z487,z4,z198]),(0,[z41,z0,z1054,z2,z4,z6])],[(0,[z0,z1,z1094,z3,z4,z6]),(0,[z0,z69,z2,z3,z4,z418]),(0,[z0,z1,z905,z3,z4,z6]),(0,[z0,z1,z38,z10,z4,z55]),(0,[z72,z1,z2,z3,z876,z6]),(0,[z0,z321,z1,z54,z4,z6]),(1,[z0,z2,z3,z928,z6]),(0,[z41,z0,z1,z2,z296,z6]),(0,[z0,z1095,z1,z2,z4,z6])],[(0,[z0,z1,z2,z3,z1096,z6]),(0,[z92,z0,z2,z3,z4,z479]),(0,[z41,z0,z1,z2,z4,z1097])],[(0,[z42,z206,z2,z500,z4,z6]),(0,[z0,z1,z154,z10,z4,z6]),(0,[z126,z1,z2,z3,z4,z96]),(1,[z0,z1,z3,z4,z709])],[(0,[z0,z1,z2,z4,z6,z1098]),(0,[z41,z1,z206,z38,z4,z6]),(0,[z0,z1,z1099,z3,z4,z6]),(0,[z490,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z1100,z4,z6]),(0,[z0,z1,z2,z1101,z4,z6])],[(0,[z0,z1032,z1,z38,z4,z6]),(0,[z0,z1,z2,z1102,z4,z6]),(0,[z19,z0,z1,z3,z163,z6]),(0,[z229,z0,z1,z4,z6,z310])],[(0,[z0,z1,z2,z10,z4,z6]),(0,[z0,z81,z38,z135,z4,z6]),(1,[z0,z1,z897,z4,z6]),(0,[z41,z0,z1,z2,z4,z40]),(0,[z1103,z1,z2,z10,z4,z6])],[(0,[z490,z1,z38,z4,z6,z55]),(0,[z0,z1,z2,z1014,z4,z6]),(0,[z0,z1,z43,z291,z4,z6])]],
   [[(0,[z19,z0,z1,z10,z163,z6]),(0,[z0,z1,z141,z4,z84,z55])],[(0,[z0,z1,z53,z897,z4,z6])],[(0,[z0,z1104,z2,z3,z4,z6]),(0,[z0,z1,z43,z298,z4,z6]),(0,[z1060,z1,z2,z3,z4,z6]),(0,[z327,z0,z2,z21,z4,z6])],[(0,[z0,z1,z2,z1105,z4,z6]),(0,[z72,z1,z2,z21,z24,z6]),(0,[z0,z1,z2,z1106,z4,z6]),(0,[z0,z1,z2,z21,z725,z6]),(0,[z0,z1,z2,z182,z4,z55])],[(0,[z0,z1,z2,z1107,z4,z6]),(0,[z0,z1,z1108,z3,z4,z6])],[(0,[z327,z0,z43,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z1109])],[(0,[z1,z38,z3,z4,z497,z6]),(0,[z0,z230,z2,z330,z4,z6]),(0,[z17,z1,z171,z3,z4,z18]),(0,[z0,z7,z1,z2,z4,z6]),(0,[z19,z0,z209,z3,z163,z6]),(0,[z41,z0,z1,z1110,z4,z6]),(0,[z0,z1,z2,z4,z40,z1111])],[(0,[z1,z509,z38,z3,z4,z6]),(0,[z0,z1,z3,z4,z1112,z6]),(0,[z1113,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1114,z4,z6]),(0,[z531,z0,z1,z214,z4,z6]),(0,[z0,z1,z1108,z10,z4,z6])],[(0,[z0,z1,z2,z1115,z4,z6]),(0,[z0,z1,z2,z1116,z4,z6]),(0,[z0,z1,z1117,z3,z4,z6]),(0,[z41,z0,z1,z2,z251,z6]),(0,[z0,z1,z4,z6,z55,z1118])],[(0,[z35,z1,z217,z3,z4,z6]),(0,[z860,z1,z2,z3,z4,z6]),(0,[z8,z1,z2,z216,z4,z6]),(0,[z278,z1,z3,z4,z6,z83])],[(0,[z0,z1,z2,z1119,z4,z6]),(0,[z0,z374,z67,z3,z4,z6]),(0,[z0,z1,z2,z1120,z4,z6]),(0,[z0,z1,z2,z3,z4,z134])],[(0,[z0,z1,z38,z3,z4,z40]),(0,[z0,z1,z325,z21,z4,z6])],[],[(0,[z0,z1,z190,z3,z4,z6]),(0,[z0,z1,z2,z1121,z4,z6])],[(0,[z1,z38,z21,z4,z24,z6]),(0,[z515,z1,z38,z3,z4,z6]),(0,[z0,z81,z2,z717,z4,z6]),(0,[z0,z1,z2,z4,z6,z1122]),(0,[z1,z2,z4,z6,z102,z55])],[(0,[z0,z1,z1123,z3,z4,z6]),(0,[z0,z1124,z1,z2,z4,z6]),(0,[z1125,z0,z1,z2,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z1126,z6]),(0,[z0,z1,z190,z10,z4,z6]),(0,[z229,z1,z3,z4,z6,z102])],[(0,[z0,z1,z1127,z3,z4,z6]),(0,[z706,z206,z2,z3,z4,z6]),(0,[z0,z1,z392,z3,z212,z6]),(0,[z368,z2,z3,z103,z4,z6]),(0,[z117,z0,z2,z3,z286,z6]),(0,[z0,z1,z897,z54,z4,z6]),(0,[z0,z2,z3,z1128,z4,z6]),(0,[z41,z0,z1,z2,z4,z1129]),(0,[z0,z1,z2,z298,z97,z55])],[(0,[z1,z38,z3,z4,z24,z6]),(0,[z41,z0,z1,z38,z167,z6]),(0,[z1130,z0,z1,z2,z4,z6]),(0,[z0,z1,z1131,z3,z4,z6])],[(0,[z1,z38,z510,z3,z4,z6]),(0,[z0,z38,z3,z4,z297,z6]),(0,[z0,z1,z87,z3,z4,z415]),(0,[z19,z368,z1,z3,z4,z6]),(0,[z0,z1,z1132,z3,z4,z6]),(0,[z0,z1,z3,z4,z1133,z6]),(0,[z0,z209,z2,z4,z375,z6]),(0,[z0,z1,z2,z4,z6,z40])],[(0,[z0,z1,z91,z3,z471,z6]),(0,[z0,z1,z1134,z3,z4,z6]),(0,[z0,z1,z2,z1135,z4,z6]),(0,[z0,z1,z2,z298,z4,z40]),(0,[z278,z2,z3,z4,z6,z316])],[(0,[z0,z1,z2,z1136,z4,z6]),(0,[z0,z1,z1137,z3,z4,z6]),(0,[z0,z1,z2,z4,z885,z6]),(0,[z0,z1,z1138,z10,z4,z6]),(0,[z130,z0,z1,z2,z4,z119])],[(0,[z57,z1,z2,z3,z4,z6]),(0,[z341,z0,z1,z2,z4,z40]),(0,[z0,z1,z43,z4,z6,z964]),(0,[z0,z1,z2,z3,z4,z1027]),(0,[z92,z0,z2,z21,z4,z93]),(0,[z0,z1041,z2,z4,z6,z55]),(0,[z0,z1,z2,z822,z6,z55])],[(0,[z124,z1,z38,z3,z24,z6]),(0,[z528,z1,z38,z3,z4,z6]),(0,[z1139,z0,z2,z3,z4,z6]),(0,[z0,z237,z91,z3,z4,z6]),(0,[z0,z1,z146,z59,z4,z6]),(0,[z20,z1,z3,z4,z163,z6]),(0,[z0,z1,z2,z10,z4,z132]),(0,[z0,z1,z2,z1140,z4,z6])],[(0,[z0,z1,z346,z21,z4,z6]),(0,[z0,z1,z36,z10,z4,z6]),(0,[z88,z1,z38,z150,z4,z6]),(0,[z0,z1,z2,z4,z235,z55])],[(0,[z35,z614,z2,z3,z4,z6]),(0,[z95,z0,z1,z3,z4,z147]),(0,[z41,z0,z420,z2,z4,z6]),(0,[z57,z1,z2,z4,z6,z55]),(0,[z41,z0,z996,z2,z4,z6])],[(0,[z0,z1141,z2,z3,z4,z6]),(0,[z0,z1,z43,z4,z6,z310]),(0,[z0,z404,z2,z21,z4,z6]),(0,[z0,z1142,z2,z3,z4,z6]),(0,[z0,z1,z1143,z2,z4,z6]),(0,[z1144,z0,z1,z2,z4,z40]),(0,[z0,z1145,z2,z10,z4,z6])],[(0,[z1146,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z89,z4,z40])],[(0,[z0,z1,z217,z3,z4,z6]),(0,[z0,z1,z2,z3,z74,z6]),(0,[z0,z1,z2,z4,z6,z1147]),(0,[z0,z209,z2,z10,z4,z6]),(0,[z0,z1,z10,z4,z6,z83])],[(0,[z126,z1,z38,z447,z4,z6]),(0,[z41,z0,z1,z2,z328,z6]),(0,[z0,z1,z2,z3,z928,z6])],[(0,[z0,z1,z2,z1148,z4,z6]),(0,[z0,z219,z1,z2,z4,z40]),(0,[z0,z1,z1149,z3,z4,z6])],[(0,[z0,z1,z217,z4,z6,z55]),(0,[z196,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z4,z247,z55]),(0,[z278,z1,z2,z3,z471,z6]),(0,[z0,z80,z2,z89,z4,z6]),(0,[z1150,z0,z1,z2,z4,z6])]],
   [[(0,[z1,z206,z217,z3,z4,z6]),(0,[z0,z1,z2,z1151,z4,z6]),(0,[z1,z854,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z1152,z6]),(0,[z0,z169,z2,z3,z928,z6]),(0,[z351,z0,z1,z2,z4,z40]),(0,[z0,z1,z2,z4,z40,z1153])],[(0,[z1154,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z73,z4,z40]),(0,[z0,z1,z3,z4,z6,z1155]),(0,[z0,z352,z1,z2,z298,z6])],[(0,[z101,z1,z2,z3,z4,z6]),(0,[z0,z1,z38,z1156,z3,z6]),(0,[z1,z2,z3,z4,z6,z102]),(0,[z0,z1,z53,z4,z6,z324]),(0,[z41,z0,z1,z2,z4,z1157])],[(0,[z126,z237,z38,z3,z4,z6]),(0,[z0,z1,z43,z1063,z4,z6]),(0,[z0,z1,z1158,z3,z4,z6]),(0,[z1159,z0,z1,z2,z4,z6]),(0,[z1,z204,z2,z21,z4,z6])],[(0,[z1,z38,z3,z530,z4,z6]),(0,[z124,z1,z79,z3,z4,z6]),(0,[z0,z1,z2,z447,z471,z6]),(0,[z327,z229,z0,z3,z4,z6])],[(0,[z0,z1,z233,z3,z4,z6]),(0,[z1,z36,z38,z3,z4,z6]),(0,[z0,z1,z38,z1160,z3,z4]),(0,[z230,z2,z38,z3,z4,z6]),(0,[z101,z1,z2,z4,z6,z55]),(0,[z229,z0,z1,z10,z4,z6])],[(0,[z35,z1,z38,z21,z4,z6]),(0,[z0,z1,z2,z1161,z4,z6]),(0,[z0,z1,z2,z108,z4,z6]),(0,[z0,z1,z2,z4,z6,z888])],[(0,[z0,z1162,z1,z2,z4,z6]),(0,[z0,z1,z43,z10,z4,z119]),(0,[z41,z0,z25,z64,z4,z6]),(0,[z0,z1,z1163,z3,z4,z6]),(0,[z0,z2,z10,z4,z6,z316])],[(0,[z0,z1,z233,z10,z4,z6]),(0,[z0,z1,z43,z127,z4,z6]),(0,[z0,z1,z1164,z3,z4,z6]),(0,[z117,z0,z1,z2,z298,z6]),(0,[z0,z1,z2,z1165,z4,z6]),(0,[z0,z1,z2,z1166,z4,z6])],[(0,[z0,z1,z243,z3,z4,z6]),(0,[z0,z2,z3,z103,z6,z400]),(0,[z0,z1,z37,z267,z21,z6])],[(0,[z0,z1167,z2,z3,z4,z6]),(1,[z1,z2,z3,z876,z6]),(0,[z0,z237,z2,z3,z471,z6]),(0,[z0,z1,z2,z1168,z4,z6]),(0,[z1169,z1,z2,z3,z4,z6]),(0,[z0,z1170,z2,z3,z4,z6])],[(0,[z19,z0,z1,z3,z78,z6]),(0,[z0,z374,z2,z189,z4,z6]),(0,[z0,z1,z2,z21,z568,z6]),(0,[z0,z1,z331,z60,z4,z6]),(0,[z0,z301,z1,z4,z6,z105])],[(0,[z0,z1,z243,z10,z4,z6]),(0,[z0,z1,z2,z103,z4,z40]),(0,[z41,z196,z1,z2,z4,z6]),(0,[z0,z1,z2,z10,z4,z361])],[(0,[z181,z90,z2,z3,z4,z6]),(0,[z1,z43,z38,z21,z4,z6])],[(0,[z206,z38,z3,z103,z4,z6]),(0,[z368,z1,z38,z3,z4,z6]),(0,[z1,z38,z3,z4,z415,z6]),(0,[z0,z169,z2,z3,z103,z6])],[(0,[z0,z1,z2,z1171,z4,z6]),(0,[z124,z1,z2,z3,z424,z6]),(0,[z0,z1,z2,z4,z6,z253])]],
   [[(0,[z57,z1,z36,z3,z4,z6]),(0,[z0,z1,z2,z1172,z4,z6]),(0,[z0,z1,z2,z4,z6,z128]),(0,[z0,z1,z16,z10,z4,z6]),(0,[z72,z1,z2,z24,z6,z55]),(0,[z0,z1,z2,z1173,z4,z6]),(0,[z0,z25,z1004,z3,z4,z6]),(0,[z130,z0,z1,z2,z4,z6])],[(0,[z0,z1,z1174,z3,z4,z6]),(0,[z0,z1,z2,z3,z1175,z6]),(0,[z0,z404,z2,z150,z4,z6]),(0,[z0,z1,z171,z21,z4,z6]),(0,[z0,z169,z2,z10,z103,z6]),(0,[z0,z1,z2,z1176,z4,z6]),(0,[z0,z1,z141,z4,z84,z253]),(0,[z359,z0,z1,z146,z4,z6])],[(0,[z0,z1,z2,z4,z6,z1177]),(0,[z181,z1,z38,z3,z4,z6]),(1,[z0,z1004,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z983]),(0,[z0,z1,z1178,z2,z4,z6]),(0,[z0,z122,z1,z2,z3,z152])],[(0,[z41,z0,z1,z38,z4,z40]),(0,[z41,z0,z1,z2,z167,z40])],[(0,[z0,z1,z38,z256,z4,z6]),(0,[z0,z1,z2,z4,z40,z96]),(0,[z0,z1,z2,z1179,z4,z6]),(0,[z0,z1,z2,z4,z6,z1180])],[(0,[z0,z1,z2,z261,z4,z6]),(0,[z0,z1,z43,z4,z6,z365]),(0,[z126,z1,z2,z3,z4,z794])],[(0,[z0,z1,z1181,z3,z4,z6]),(0,[z0,z1,z1182,z3,z4,z6]),(0,[z0,z1,z2,z279,z4,z55]),(0,[z0,z1,z2,z1183,z4,z6])],[(0,[z1,z1182,z38,z3,z4,z6]),(0,[z0,z1,z2,z4,z145,z55]),(0,[z0,z1,z2,z1184,z4,z6]),(0,[z0,z1,z343,z4,z6,z324])],[(0,[z0,z1,z2,z3,z4,z1185]),(0,[z0,z1,z2,z1186,z4,z6]),(0,[z0,z1,z2,z4,z40,z1187])],[(0,[z0,z1,z38,z21,z4,z6]),(0,[z0,z1,z43,z4,z375,z6]),(0,[z0,z1,z43,z197,z4,z6]),(0,[z0,z1,z4,z5,z353,z6]),(0,[z0,z1,z2,z4,z6,z1188]),(0,[z1,z2,z4,z6,z55,z1189]),(0,[z278,z1,z828,z3,z4,z6])],[(0,[z0,z38,z3,z4,z1190,z6]),(0,[z0,z80,z1,z2,z4,z40]),(0,[z0,z1,z2,z1191,z4,z6])],[(0,[z0,z1,z154,z3,z4,z6]),(0,[z0,z1,z1192,z3,z4,z6]),(0,[z0,z7,z1,z38,z4,z6]),(0,[z501,z0,z1,z2,z4,z55]),(0,[z0,z1,z2,z4,z1193,z6])],[(0,[z88,z404,z2,z150,z4,z6]),(0,[z72,z1,z79,z3,z24,z6])],[(0,[z1,z206,z38,z21,z4,z6]),(0,[z0,z420,z325,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z244,z569,z3,z4,z6]),(0,[z0,z1194,z38,z3,z4,z6]),(0,[z41,z0,z1,z325,z4,z6]),(0,[z0,z1,z154,z4,z6,z55]),(0,[z0,z1,z2,z1195,z4,z6]),(0,[z92,z0,z2,z4,z93,z55]),(0,[z1103,z1,z2,z3,z4,z6]),(0,[z1,z2,z849,z3,z4,z6])],[(0,[z428,z1,z38,z3,z4,z6]),(0,[z126,z1,z43,z3,z4,z96]),(0,[z0,z1,z2,z1196,z4,z6]),(0,[z20,z1,z3,z4,z84,z6])]],
   [[(0,[z455,z1,z38,z3,z24,z6]),(0,[z41,z0,z1,z1030,z4,z6]),(0,[z1197,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z4,z6,z55]),(0,[z0,z1,z3,z4,z1198,z6]),(0,[z0,z1,z2,z1012,z4,z6]),(0,[z0,z25,z64,z280,z4,z6]),(0,[z0,z1,z10,z896,z4,z6])],[(0,[z0,z1,z43,z10,z4,z6]),(0,[z0,z1,z231,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z999]),(0,[z278,z1,z2,z3,z24,z6])],[(0,[z124,z1,z2,z14,z6,z55]),(0,[z1199,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z170,z4,z6]),(0,[z130,z0,z1,z2,z4,z40])],[(0,[z0,z374,z2,z330,z4,z6]),(0,[z0,z81,z2,z135,z4,z6]),(0,[z1200,z1,z2,z3,z4,z6]),(0,[z41,z748,z1,z2,z4,z6]),(0,[z278,z1,z2,z3,z99,z97])],[(0,[z0,z1,z1201,z3,z4,z6]),(0,[z606,z1,z38,z3,z4,z6]),(0,[z0,z352,z1,z43,z4,z6]),(0,[z0,z1,z231,z10,z4,z6]),(0,[z1202,z0,z1,z2,z4,z6]),(0,[z117,z0,z2,z5,z46,z6]),(0,[z0,z2,z3,z4,z240,z155])],[(0,[z0,z1,z2,z1019,z4,z6]),(0,[z0,z1,z38,z309,z21,z6]),(0,[z0,z1,z2,z3,z1203,z6]),(0,[z0,z1,z37,z197,z267,z6]),(0,[z0,z1,z2,z4,z6,z1204])],[],[(0,[z0,z1,z2,z1205,z4,z6]),(0,[z0,z1,z3,z4,z1206,z6]),(0,[z0,z1,z1207,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1208]),(0,[z0,z1,z2,z298,z4,z97])],[(0,[z0,z1,z2,z1209,z4,z6])],[(0,[z206,z38,z3,z4,z6,z93]),(0,[z126,z1,z173,z3,z4,z6]),(0,[z0,z574,z2,z135,z4,z6]),(0,[z0,z69,z2,z4,z240,z55]),(0,[z0,z1,z2,z1210,z4,z6])],[(0,[z341,z1,z38,z10,z4,z6]),(0,[z0,z1,z631,z2,z4,z55]),(0,[z0,z1,z2,z4,z1211,z6]),(0,[z0,z2,z21,z4,z297,z6])],[(0,[z0,z1212,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z143,z97]),(0,[z0,z1,z2,z49,z21,z6]),(0,[z2,z3,z4,z6,z316,z102])],[(0,[z1,z38,z3,z4,z578,z6]),(0,[z0,z1,z2,z3,z4,z1097]),(0,[z0,z1,z2,z688,z4,z55]),(0,[z0,z1,z2,z4,z6,z1213])],[(0,[z0,z1,z43,z3,z4,z134]),(0,[z0,z1214,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z297,z6]),(0,[z0,z1,z37,z10,z267,z6])]],
   [[(0,[z0,z1,z43,z1033,z4,z6]),(0,[z126,z1,z2,z3,z4,z441])],[(0,[z0,z1215,z2,z3,z4,z6]),(0,[z41,z1,z43,z38,z4,z6]),(0,[z0,z1,z2,z3,z4,z40])],[(0,[z0,z1,z1216,z3,z4,z6]),(0,[z0,z140,z1,z2,z4,z40]),(0,[z0,z1,z2,z1217,z4,z6])],[(0,[z0,z1,z2,z1218,z4,z6]),(0,[z0,z1,z190,z4,z6,z55]),(0,[z0,z1219,z1,z3,z4,z6]),(0,[z0,z1,z2,z4,z1220,z6]),(0,[z317,z0,z2,z4,z430,z6])],[(0,[z0,z1,z38,z1221,z3,z4]),(0,[z560,z1,z38,z3,z4,z6]),(0,[z179,z1,z905,z3,z4,z6]),(0,[z17,z1,z2,z3,z4,z18]),(0,[z368,z1,z61,z3,z4,z6]),(0,[z0,z1,z2,z10,z4,z40])],[(0,[z0,z1,z2,z1222,z4,z6]),(0,[z0,z1,z1138,z3,z4,z6])],[(0,[z0,z1,z217,z261,z4,z6]),(0,[z0,z1,z1004,z3,z4,z6])],[(0,[z0,z1,z43,z4,z6,z40]),(0,[z17,z1,z2,z10,z4,z18]),(0,[z0,z65,z45,z1,z4,z6])],[(0,[z0,z1,z36,z3,z4,z6]),(0,[z0,z1,z2,z234,z4,z6]),(0,[z124,z1,z67,z3,z14,z6]),(0,[z0,z1,z2,z1223,z4,z6])],[(0,[z41,z0,z1,z1117,z4,z6]),(0,[z1,z2,z3,z99,z102,z97])],[(0,[z0,z1,z1224,z3,z4,z6]),(0,[z57,z1,z43,z3,z4,z6]),(0,[z0,z1145,z2,z3,z4,z6]),(0,[z0,z65,z1,z21,z4,z6]),(0,[z0,z1,z2,z99,z21,z97]),(0,[z0,z122,z1,z2,z170,z6])],[(0,[z0,z1,z36,z4,z6,z55]),(0,[z0,z1,z2,z1225,z4,z6]),(0,[z41,z0,z1,z1024,z4,z6]),(0,[z278,z1,z2,z4,z97,z55])],[(0,[z42,z774,z2,z3,z4,z6]),(0,[z41,z341,z1,z38,z4,z6]),(0,[z0,z209,z2,z3,z4,z6]),(0,[z0,z1,z2,z1226,z4,z6]),(0,[z0,z1,z3,z4,z6,z1118]),(0,[z0,z1,z2,z4,z6,z1227]),(0,[z1228,z1,z2,z3,z4,z6]),(0,[z0,z1,z749,z3,z4,z6])],[(0,[z0,z1,z2,z1229,z4,z6]),(0,[z0,z1,z2,z1230,z4,z6])],[(0,[z0,z1,z2,z1231,z4,z6]),(0,[z222,z1,z38,z3,z4,z6]),(0,[z0,z1,z38,z402,z4,z6]),(0,[z72,z177,z1,z2,z24,z6]),(0,[z0,z1,z2,z1232,z4,z6])],[(0,[z0,z1,z233,z261,z4,z6]),(0,[z0,z1233,z2,z3,z4,z6]),(0,[z0,z362,z2,z127,z4,z6]),(0,[z0,z1,z2,z1234,z4,z6]),(0,[z868,z1,z2,z3,z4,z6]),(0,[z0,z209,z2,z4,z6,z55]),(0,[z1235,z0,z1,z2,z4,z6]),(0,[z130,z0,z1,z4,z6,z83])]],
   [[(0,[z206,z38,z3,z89,z4,z6]),(0,[z1,z38,z21,z4,z18,z6]),(0,[z0,z1,z43,z3,z74,z6]),(0,[z0,z1,z2,z1236,z4,z6]),(0,[z41,z0,z1,z2,z281,z6])],[(0,[z1,z609,z38,z3,z4,z6]),(0,[z41,z0,z1,z43,z21,z6]),(0,[z0,z1,z141,z3,z4,z415]),(0,[z177,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z10,z4,z432]),(0,[z0,z1,z2,z4,z6,z1237])],[(0,[z0,z1,z43,z1148,z4,z6]),(0,[z0,z1238,z2,z3,z4,z6]),(0,[z0,z1,z2,z1239,z4,z6]),(0,[z0,z1,z2,z152,z298,z4])],[(0,[z628,z1,z38,z3,z4,z6]),(0,[z126,z1,z38,z3,z471,z6]),(0,[z366,z0,z148,z3,z4,z6]),(0,[z0,z80,z43,z89,z4,z6]),(0,[z0,z1240,z1,z2,z3,z6])],[(0,[z1,z38,z3,z4,z18,z6]),(0,[z0,z1,z1110,z3,z4,z6]),(0,[z0,z1,z2,z1241,z4,z6]),(0,[z0,z1,z2,z3,z4,z1129]),(0,[z0,z1,z2,z3,z4,z888])],[(0,[z130,z0,z1,z38,z4,z6]),(0,[z368,z1,z2,z280,z4,z6]),(0,[z25,z368,z64,z3,z4,z6]),(0,[z0,z1,z2,z3,z1242,z6]),(0,[z0,z1,z2,z1243,z4,z6]),(0,[z229,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z4,z40,z40])],[(0,[z35,z1,z1182,z3,z4,z6]),(0,[z0,z1,z2,z1059,z4,z6]),(0,[z101,z1,z43,z3,z4,z6]),(0,[z0,z1,z2,z712,z4,z6]),(0,[z0,z2,z1004,z3,z4,z6])],[(0,[z0,z1,z38,z733,z4,z6]),(0,[z0,z1,z38,z4,z734,z6]),(0,[z0,z122,z1,z38,z3,z152]),(0,[z0,z1,z2,z4,z6,z1244]),(0,[z0,z1,z2,z10,z4,z888])],[(0,[z0,z1,z2,z1156,z3,z6]),(0,[z196,z1,z2,z10,z4,z6]),(0,[z229,z0,z1,z4,z6,z55])],[(0,[z0,z1,z2,z1245,z4,z6]),(0,[z0,z1,z2,z1246,z4,z6]),(0,[z0,z1,z38,z162,z4,z6]),(0,[z124,z0,z1,z2,z4,z40]),(0,[z0,z1,z2,z14,z97,z55])],[(0,[z0,z1,z43,z108,z4,z6]),(0,[z1247,z0,z1,z2,z4,z6]),(0,[z1248,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z1249,z6])],[(0,[z0,z1,z233,z4,z6,z55]),(0,[z0,z420,z38,z3,z4,z6]),(0,[z124,z1,z854,z3,z4,z6]),(0,[z183,z0,z25,z3,z4,z6]),(0,[z1250,z0,z1,z2,z3,z6]),(0,[z1251,z0,z1,z2,z4,z40])],[(0,[z0,z153,z218,z3,z4,z6]),(0,[z0,z1,z2,z14,z4,z40]),(0,[z0,z1,z1252,z3,z4,z6]),(0,[z1,z1253,z2,z3,z4,z6]),(0,[z0,z1254,z2,z3,z4,z6])],[(0,[z0,z1255,z1,z2,z4,z6]),(0,[z41,z0,z374,z2,z4,z6]),(0,[z1,z2,z3,z4,z18,z215]),(0,[z0,z65,z3,z103,z4,z6]),(0,[z0,z1,z37,z3,z763,z6]),(0,[z0,z1256,z2,z10,z4,z6])],[(0,[z0,z1,z38,z3,z4,z747]),(0,[z0,z1,z1257,z3,z4,z6]),(0,[z368,z1,z344,z3,z4,z6]),(0,[z0,z1,z1258,z3,z4,z6]),(0,[z1259,z0,z1,z2,z4,z6])],[(0,[z552,z1,z38,z3,z4,z6]),(0,[z0,z1,z243,z4,z6,z55]),(1,[z0,z2,z3,z4,z839]),(0,[z0,z1,z2,z3,z763,z6]),(0,[z0,z1,z2,z284,z170,z6])]],
   [[(0,[z0,z1,z16,z3,z4,z6]),(0,[z0,z45,z1,z38,z4,z6]),(0,[z0,z1,z38,z3,z4,z753]),(0,[z501,z0,z1,z38,z4,z55]),(0,[z1,z2,z3,z14,z6,z191])],[(0,[z0,z1260,z2,z3,z4,z6]),(0,[z88,z1,z2,z712,z4,z6]),(0,[z0,z1,z2,z1261,z4,z6]),(0,[z0,z2,z3,z928,z46,z6]),(0,[z0,z1,z2,z1262,z4,z6]),(0,[z130,z0,z1,z2,z4,z55]),(0,[z0,z1,z2,z1263,z4,z6])],[(0,[z0,z169,z43,z3,z103,z6]),(0,[z0,z43,z3,z4,z722,z6]),(0,[z124,z230,z2,z3,z14,z6]),(0,[z0,z1,z21,z4,z353,z6])],[(0,[z0,z362,z38,z3,z4,z6]),(0,[z576,z1,z43,z3,z4,z6]),(0,[z0,z1,z16,z4,z6,z55])],[(0,[z0,z1,z38,z429,z4,z6]),(0,[z0,z1,z38,z26,z4,z6]),(0,[z63,z1,z38,z3,z4,z6]),(0,[z0,z1,z43,z4,z6,z128]),(0,[z0,z1,z43,z1172,z4,z6]),(0,[z0,z1,z2,z1264,z4,z6]),(0,[z312,z0,z219,z2,z4,z6])],[(1,[z1,z905,z3,z4,z6]),(0,[z0,z1,z2,z4,z100,z6])],[(0,[z337,z1,z38,z3,z4,z6]),(0,[z126,z362,z2,z3,z4,z96]),(0,[z0,z1,z448,z127,z4,z6]),(0,[z1265,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z1266]),(0,[z0,z1,z3,z4,z353,z6]),(0,[z0,z1,z2,z1267,z4,z6])],[(0,[z0,z1,z37,z108,z267,z6]),(0,[z0,z1268,z2,z3,z4,z6])],[(0,[z0,z1269,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1270]),(0,[z1,z1271,z2,z3,z4,z6]),(0,[z0,z1,z2,z1272,z4,z6]),(0,[z0,z1,z2,z4,z1273,z40])],[(0,[z0,z1,z43,z261,z4,z6]),(0,[z544,z1,z38,z3,z4,z6]),(0,[z124,z1,z2,z189,z14,z6]),(0,[z17,z1,z2,z3,z4,z794]),(0,[z1274,z1,z2,z3,z4,z6])],[(0,[z149,z1,z38,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z794]),(0,[z0,z1,z2,z1275,z4,z6])],[(0,[z0,z1,z2,z4,z6,z1276]),(0,[z0,z1,z2,z1277,z4,z6]),(0,[z19,z0,z1,z375,z163,z6]),(0,[z0,z1,z2,z1278,z4,z6])],[(0,[z88,z48,z1,z2,z4,z6]),(0,[z0,z2,z3,z4,z6,z1279])],[(0,[z0,z1,z2,z4,z6,z1280])],[(0,[z488,z206,z2,z3,z4,z6]),(0,[z0,z107,z218,z3,z4,z6]),(0,[z1281,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z763,z163,z6]),(0,[z0,z769,z2,z3,z4,z6]),(0,[z278,z130,z1,z2,z4,z6]),(0,[z327,z0,z3,z4,z6,z83])],[(0,[z0,z69,z38,z3,z4,z240]),(0,[z126,z1,z2,z21,z4,z96]),(0,[z0,z1,z2,z1282,z4,z6]),(0,[z0,z1004,z64,z3,z4,z6])]],
   [[(0,[z0,z1,z631,z38,z4,z55]),(0,[z278,z1,z38,z3,z4,z6]),(0,[z117,z0,z2,z46,z6,z55]),(0,[z0,z1,z2,z4,z1283,z6]),(0,[z0,z1284,z2,z3,z4,z6])],[(0,[z0,z1,z38,z440,z4,z6]),(0,[z19,z196,z1,z3,z163,z6]),(0,[z19,z0,z1,z21,z163,z6])],[(0,[z0,z1,z43,z3,z4,z6]),(0,[z1,z448,z38,z3,z4,z6]),(0,[z41,z0,z1,z2,z354,z6]),(0,[z41,z1026,z1,z2,z4,z6]),(0,[z0,z1,z2,z10,z4,z55])],[(0,[z0,z1,z2,z1285,z4,z6]),(0,[z41,z183,z0,z1,z2,z6]),(0,[z0,z1,z4,z83,z97,z55])],[(0,[z0,z1,z1286,z3,z4,z6]),(0,[z41,z19,z0,z1,z163,z6])],[(0,[z0,z1,z43,z4,z6,z55]),(0,[z0,z1,z38,z447,z4,z6]),(0,[z0,z1,z1287,z3,z4,z6])],[(0,[z1,z38,z3,z4,z570,z6]),(0,[z0,z1,z2,z4,z1288,z6]),(0,[z0,z1,z2,z186,z21,z6]),(0,[z0,z703,z1,z2,z21,z6]),(0,[z0,z1,z2,z99,z100,z97])],[(0,[z0,z1,z43,z170,z4,z6]),(0,[z0,z1,z2,z1289,z4,z6]),(0,[z0,z1,z2,z4,z40,z93]),(0,[z41,z0,z1,z2,z4,z1290])],[(0,[z0,z81,z43,z135,z4,z6]),(0,[z0,z1,z231,z4,z6,z55]),(0,[z0,z1,z2,z388,z4,z55])],[(0,[z0,z230,z38,z3,z4,z6]),(0,[z0,z1,z38,z789,z4,z6])],[(0,[z0,z1,z2,z4,z1291,z6]),(0,[z460,z0,z1,z2,z21,z6]),(0,[z117,z0,z65,z3,z46,z6]),(0,[z0,z69,z1,z2,z4,z40]),(0,[z1292,z1,z2,z3,z4,z6])],[(0,[z341,z1,z38,z3,z4,z6]),(0,[z0,z237,z38,z3,z4,z6]),(0,[z1293,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z10,z4,z347]),(1,[z860,z1,z3,z4,z6]),(0,[z0,z1294,z1,z2,z4,z40])],[(0,[z488,z1,z38,z3,z4,z6]),(0,[z126,z1,z448,z3,z4,z96]),(0,[z1,z2,z3,z4,z6,z1189]),(0,[z0,z1,z2,z1295,z4,z6]),(0,[z41,z0,z1296,z2,z4,z6]),(0,[z0,z352,z1,z2,z49,z6]),(0,[z0,z1,z1297,z3,z4,z6])],[(0,[z0,z1,z2,z1298,z4,z6]),(0,[z341,z1,z38,z4,z6,z55]),(0,[z124,z1,z2,z14,z21,z6]),(0,[z117,z0,z2,z3,z511,z6]),(0,[z0,z1,z2,z21,z4,z134])],[(0,[z0,z1,z2,z4,z6,z1299]),(0,[z0,z1,z2,z1300,z4,z6]),(0,[z1,z2,z3,z4,z794,z96]),(0,[z0,z1,z1301,z3,z4,z6]),(0,[z0,z1,z37,z3,z267,z6]),(0,[z0,z1,z2,z4,z1302,z6])]],
   [[(0,[z0,z1,z38,z189,z4,z6]),(0,[z222,z0,z1,z3,z4,z147]),(0,[z0,z80,z2,z246,z4,z6]),(0,[z987,z1,z2,z3,z4,z6])],[(0,[z0,z1,z190,z21,z4,z6])],[(0,[z124,z1,z2,z330,z14,z6]),(0,[z41,z0,z1,z2,z427,z6]),(0,[z542,z0,z1,z2,z4,z40]),(0,[z0,z1,z1303,z3,z4,z6]),(0,[z1304,z1,z2,z10,z4,z6])],[(0,[z126,z1,z79,z3,z4,z6]),(0,[z0,z1,z2,z1305,z4,z6]),(0,[z19,z0,z1,z3,z763,z6]),(0,[z0,z1,z2,z1306,z4,z6]),(0,[z0,z1,z2,z4,z40,z55]),(0,[z0,z1,z2,z3,z718,z99])],[(0,[z0,z140,z1,z897,z4,z6])],[(0,[z221,z0,z1,z3,z78,z6]),(0,[z0,z1,z43,z3,z4,z40]),(0,[z0,z1307,z2,z3,z4,z6]),(0,[z395,z1,z2,z4,z6,z158]),(0,[z0,z2,z10,z925,z4,z6])],[(0,[z177,z0,z1,z38,z4,z6]),(0,[z0,z25,z64,z10,z4,z6]),(0,[z0,z1308,z1,z2,z4,z6]),(0,[z0,z1,z1309,z3,z4,z6])],[(0,[z0,z1,z1310,z3,z4,z6]),(0,[z1311,z0,z1,z2,z4,z6]),(0,[z0,z2,z4,z6,z55,z727])],[(0,[z17,z1,z43,z3,z4,z18]),(0,[z1,z2,z712,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z1312]),(0,[z0,z1313,z2,z3,z4,z6]),(0,[z117,z0,z65,z3,z4,z6])],[(0,[z0,z1,z38,z4,z6,z468]),(0,[z0,z1,z1314,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z1315]),(0,[z1,z204,z3,z4,z84,z6]),(0,[z0,z1,z2,z4,z40,z97]),(0,[z0,z1,z1137,z21,z4,z6]),(0,[z0,z1,z2,z4,z885,z55]),(0,[z0,z1,z1316,z10,z4,z6])],[(0,[z0,z1,z1317,z3,z4,z6]),(0,[z922,z0,z1,z43,z4,z6]),(0,[z57,z1,z2,z21,z4,z6]),(0,[z19,z0,z1,z3,z286,z6]),(0,[z0,z1318,z1,z3,z4,z6]),(0,[z0,z169,z2,z103,z6,z55]),(0,[z0,z1319,z1,z2,z4,z6])],[(0,[z1320,z0,z1,z2,z4,z6]),(0,[z41,z0,z65,z1,z4,z6]),(0,[z0,z140,z1,z288,z4,z6])],[(0,[z0,z1321,z2,z3,z4,z6]),(0,[z0,z1,z43,z234,z4,z6]),(0,[z0,z25,z674,z3,z4,z6]),(0,[z0,z1,z2,z1322,z4,z6])],[(0,[z1,z38,z3,z4,z591,z6]),(0,[z0,z1,z2,z3,z4,z794]),(0,[z0,z1,z2,z10,z4,z272]),(0,[z0,z1,z3,z4,z6,z1323])],[(0,[z124,z1,z38,z10,z4,z6]),(0,[z1139,z0,z43,z3,z4,z6]),(0,[z0,z1,z2,z1324,z4,z6]),(0,[z92,z0,z2,z367,z4,z93])],[(0,[z1,z38,z3,z657,z4,z6]),(0,[z450,z1,z43,z3,z4,z6]),(0,[z0,z1,z2,z1325,z4,z6]),(0,[z0,z1326,z1,z2,z4,z6]),(0,[z0,z1,z1327,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z1328]),(0,[z0,z3,z4,z6,z83,z316])]],
   [[(0,[z0,z1,z217,z21,z4,z6]),(0,[z0,z209,z43,z3,z4,z6]),(0,[z0,z1,z2,z21,z74,z6])],[(0,[z0,z1,z2,z1329,z4,z6]),(0,[z88,z1,z2,z150,z4,z6]),(0,[z41,z0,z1,z91,z4,z6]),(0,[z95,z0,z1,z10,z4,z198]),(0,[z278,z1,z2,z4,z6,z310])],[(0,[z41,z0,z169,z2,z103,z6])],[(0,[z0,z1,z2,z21,z436,z6])],[(0,[z42,z206,z38,z3,z4,z6]),(0,[z521,z1,z2,z73,z4,z6]),(0,[z0,z1,z91,z127,z4,z6]),(0,[z0,z1,z2,z4,z6,z1330])],[(0,[z455,z0,z1,z3,z457,z6]),(0,[z0,z244,z64,z3,z4,z6]),(0,[z0,z107,z61,z10,z4,z6]),(0,[z0,z1,z2,z214,z4,z40])],[(0,[z101,z1,z2,z21,z4,z6])],[],[(0,[z774,z206,z2,z3,z4,z6]),(0,[z196,z1,z2,z3,z4,z6]),(0,[z41,z95,z0,z1,z4,z198])],[(0,[z0,z1,z233,z21,z4,z6]),(0,[z0,z1,z2,z4,z6,z1331]),(0,[z0,z1,z38,z330,z4,z6]),(0,[z125,z0,z1,z2,z4,z40]),(0,[z970,z0,z1,z2,z471,z6]),(0,[z0,z1,z3,z4,z84,z709]),(0,[z0,z1332,z1,z3,z4,z6])],[(0,[z0,z1,z38,z4,z5,z6]),(0,[z0,z1,z2,z1333,z4,z6]),(0,[z0,z1,z1334,z3,z4,z6]),(0,[z0,z1,z832,z3,z4,z6])],[(0,[z1,z38,z3,z4,z672,z6]),(0,[z0,z1,z2,z1335,z4,z6]),(0,[z41,z1,z38,z4,z24,z6]),(0,[z0,z1,z2,z4,z479,z55]),(0,[z196,z1,z2,z4,z6,z55]),(0,[z41,z0,z2,z4,z297,z6]),(0,[z0,z1,z835,z3,z4,z6]),(0,[z0,z1,z1336,z3,z4,z6])],[(0,[z196,z1,z231,z3,z4,z6]),(0,[z0,z1,z2,z3,z1337,z6]),(0,[z860,z1,z3,z4,z46,z6]),(0,[z0,z209,z3,z267,z4,z6])],[(0,[z0,z1,z1338,z3,z4,z6]),(0,[z0,z1,z243,z21,z4,z6]),(0,[z0,z1,z2,z64,z4,z40]),(0,[z0,z1256,z2,z3,z4,z6]),(0,[z0,z1,z731,z10,z4,z6])],[(0,[z0,z1,z2,z1160,z3,z4]),(0,[z0,z1,z1339,z3,z4,z6]),(0,[z0,z1,z448,z3,z74,z6]),(0,[z57,z25,z64,z3,z4,z6]),(0,[z0,z81,z2,z4,z6,z199]),(0,[z0,z1170,z2,z21,z4,z6]),(0,[z0,z352,z1,z2,z152,z4])],[(0,[z0,z1,z2,z162,z4,z6]),(0,[z1340,z1,z2,z3,z4,z6]),(0,[z0,z1,z1341,z3,z4,z6])]],
   [[(0,[z126,z1,z38,z127,z4,z6]),(0,[z0,z1,z1342,z3,z4,z6]),(0,[z1343,z1,z2,z3,z4,z6]),(0,[z840,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z40,z198])],[(0,[z0,z1,z1344,z3,z4,z6]),(0,[z1345,z0,z1,z3,z4,z6]),(0,[z17,z1,z2,z234,z4,z18]),(0,[z0,z1,z2,z1346,z4,z6])],[(0,[z0,z1,z3,z4,z6,z759]),(0,[z0,z1,z173,z3,z4,z6]),(0,[z0,z169,z2,z21,z103,z6]),(0,[z0,z1,z1341,z4,z6,z55])],[(0,[z0,z1,z2,z1347,z4,z6]),(0,[z179,z1,z36,z3,z4,z6]),(0,[z0,z1,z2,z1348,z4,z6]),(0,[z88,z1,z190,z150,z4,z6]),(0,[z41,z1,z204,z2,z4,z6])],[(0,[z0,z420,z2,z10,z4,z6]),(0,[z101,z1,z448,z3,z4,z6]),(0,[z382,z0,z1,z2,z4,z40])],[(0,[z1349,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z6,z1350]),(0,[z0,z1,z173,z4,z6,z55]),(0,[z0,z1,z173,z10,z4,z6]),(0,[z1351,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1352,z4,z6]),(0,[z0,z1,z43,z4,z6,z253])],[(0,[z368,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z127,z471,z6])],[(0,[z0,z1,z67,z10,z4,z6]),(0,[z0,z2,z3,z103,z562,z6]),(0,[z0,z1,z2,z3,z4,z1157])],[(0,[z0,z362,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1190,z6]),(0,[z0,z1,z43,z4,z100,z6]),(0,[z125,z1,z2,z4,z94,z6]),(0,[z0,z1,z2,z1353,z4,z6]),(0,[z327,z0,z2,z3,z99,z97])],[(0,[z41,z1,z38,z4,z18,z6]),(0,[z0,z237,z2,z127,z4,z6]),(0,[z368,z1,z2,z4,z6,z55]),(0,[z368,z1,z2,z10,z4,z6]),(0,[z0,z1,z2,z429,z4,z6]),(0,[z0,z755,z2,z10,z4,z6])],[(0,[z0,z1,z79,z10,z4,z6]),(0,[z126,z1,z91,z3,z4,z96]),(0,[z41,z0,z1,z2,z4,z877]),(0,[z0,z574,z2,z459,z4,z6])],[(0,[z20,z1,z38,z3,z4,z6]),(0,[z117,z0,z38,z3,z46,z6]),(0,[z8,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z1354,z4,z6]),(0,[z0,z362,z2,z10,z4,z6]),(0,[z0,z1,z2,z1355,z4,z6]),(0,[z0,z1356,z1,z2,z4,z6]),(0,[z1357,z1,z2,z3,z4,z6]),(0,[z0,z122,z1,z2,z3,z718])],[(0,[z0,z1,z2,z256,z4,z6]),(0,[z0,z703,z1,z2,z3,z152])],[(0,[z41,z0,z1,z2,z470,z6]),(0,[z41,z0,z1,z2,z471,z6]),(0,[z1358,z0,z1,z3,z4,z6]),(0,[z0,z1,z4,z6,z310,z83])],[(0,[z0,z1,z2,z1359,z4,z6]),(0,[z41,z0,z1,z79,z4,z6]),(0,[z0,z1,z154,z21,z4,z6]),(0,[z0,z1,z2,z3,z6,z1360]),(0,[z0,z1,z2,z4,z6,z1361]),(0,[z0,z1,z3,z267,z763,z6])]],
   [[(0,[z0,z2,z3,z717,z4,z6]),(0,[z164,z0,z1,z2,z4,z40])],[(0,[z638,z0,z1,z2,z4,z55]),(0,[z41,z0,z1,z346,z4,z6]),(0,[z0,z1362,z1,z2,z4,z6]),(0,[z0,z1,z2,z10,z4,z518]),(0,[z0,z1,z2,z4,z725,z6])],[(0,[z0,z1,z2,z21,z4,z6]),(0,[z1363,z0,z1,z3,z4,z6])],[(0,[z9,z1,z38,z3,z4,z6]),(0,[z0,z420,z190,z3,z4,z6]),(0,[z41,z0,z1,z2,z541,z6]),(0,[z41,z0,z1,z141,z4,z84])],[(0,[z41,z0,z1,z217,z4,z6]),(0,[z0,z1,z1364,z3,z4,z6]),(0,[z0,z1,z141,z10,z4,z84])],[(0,[z0,z1,z2,z1365,z4,z6]),(0,[z41,z1,z2,z4,z6,z102])],[(0,[z0,z1,z38,z500,z4,z6]),(0,[z9,z1,z38,z10,z4,z6]),(0,[z0,z1,z43,z10,z4,z55]),(0,[z41,z0,z1,z67,z4,z6]),(0,[z0,z1,z231,z21,z4,z6]),(0,[z117,z41,z0,z2,z46,z6])],[(0,[z42,z0,z1,z2,z4,z40]),(0,[z1,z38,z3,z4,z635,z6]),(0,[z0,z374,z38,z3,z4,z6]),(0,[z0,z1,z51,z600,z4,z6]),(0,[z0,z1194,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z480,z6]),(0,[z19,z0,z7,z1,z163,z6]),(0,[z0,z1,z2,z4,z590,z55]),(0,[z0,z48,z1,z2,z4,z40])],[(0,[z1,z2,z3,z4,z876,z6]),(0,[z41,z0,z1,z2,z520,z6]),(0,[z0,z1,z305,z59,z4,z6]),(0,[z1200,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z298,z6,z97])],[(0,[z455,z1,z2,z3,z24,z6]),(0,[z0,z1,z2,z1366,z4,z6]),(0,[z1367,z1,z2,z3,z4,z6]),(0,[z0,z2,z4,z6,z310,z316])],[(0,[z517,z90,z2,z3,z4,z6]),(0,[z126,z41,z1,z2,z4,z96]),(0,[z0,z1,z61,z2,z4,z40]),(0,[z312,z0,z1,z2,z4,z40]),(0,[z0,z122,z1,z2,z152,z55])],[(0,[z0,z1,z38,z3,z471,z6]),(0,[z126,z1,z2,z447,z4,z96]),(0,[z0,z114,z2,z89,z4,z6]),(0,[z0,z65,z1,z4,z5,z6])],[(0,[z0,z1,z2,z3,z1368,z6]),(0,[z0,z1,z2,z1369,z4,z6]),(0,[z0,z1,z38,z487,z4,z6]),(0,[z0,z1,z2,z1370,z4,z6]),(0,[z0,z1,z2,z192,z21,z6]),(0,[z0,z1,z2,z4,z24,z40]),(0,[z0,z1,z2,z1371,z4,z6]),(0,[z0,z1,z2,z1372,z4,z6])],[(0,[z0,z1373,z2,z3,z4,z6]),(0,[z0,z636,z2,z246,z4,z6]),(0,[z0,z1,z2,z1374,z4,z6])],[(0,[z0,z1,z43,z4,z1291,z6]),(0,[z0,z1,z1375,z3,z4,z6]),(0,[z126,z1,z2,z3,z471,z96]),(0,[z92,z0,z2,z15,z4,z93]),(0,[z0,z1,z2,z1376,z4,z6]),(0,[z0,z1,z2,z4,z6,z1377]),(0,[z144,z0,z1,z4,z684,z6])],[(0,[z341,z1,z905,z3,z4,z6]),(0,[z0,z1,z2,z4,z465,z55]),(0,[z0,z1,z2,z309,z21,z6])]],
   [[(0,[z0,z1,z448,z3,z4,z6]),(0,[z327,z0,z2,z4,z97,z55])],[(0,[z126,z237,z2,z3,z4,z96])],[(0,[z179,z41,z1,z43,z4,z6]),(0,[z0,z230,z2,z10,z4,z6]),(0,[z0,z1,z2,z1378,z4,z6]),(0,[z1304,z1,z2,z3,z4,z6]),(0,[z0,z1379,z1,z2,z4,z6])],[(0,[z0,z1,z448,z4,z6,z55]),(0,[z0,z1,z448,z10,z4,z6]),(0,[z0,z169,z1,z2,z298,z6]),(0,[z0,z1,z2,z1380,z4,z6]),(0,[z818,z1,z3,z4,z6,z102])],[(0,[z0,z43,z3,z4,z6,z316]),(0,[z0,z1,z2,z4,z6,z1381]),(0,[z0,z237,z2,z10,z4,z6]),(0,[z17,z1,z2,z4,z18,z128]),(0,[z1382,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z99,z97,z55])],[(0,[z0,z1296,z2,z3,z4,z6]),(0,[z57,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z21,z4,z40]),(0,[z1,z1383,z2,z3,z4,z6])],[(0,[z1,z38,z23,z4,z24,z6]),(0,[z0,z1,z2,z1384,z4,z6]),(0,[z0,z25,z64,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z839]),(0,[z0,z1,z2,z4,z1385,z6])],[(0,[z0,z1,z38,z797,z4,z6]),(0,[z124,z1,z2,z3,z876,z6]),(0,[z0,z1,z2,z3,z846,z6]),(0,[z0,z1,z1386,z3,z4,z6]),(0,[z1387,z1,z2,z3,z4,z6]),(0,[z0,z1388,z1,z2,z4,z6])],[(0,[z126,z0,z1,z2,z4,z40]),(0,[z17,z1,z2,z21,z4,z18]),(0,[z41,z0,z1,z2,z4,z907])],[(0,[z0,z1,z2,z1389,z4,z6]),(0,[z1,z43,z410,z3,z4,z6]),(0,[z9,z1,z2,z73,z4,z6]),(0,[z0,z25,z64,z4,z6,z55]),(0,[z0,z1,z1316,z3,z4,z6])],[(0,[z0,z1,z2,z1390,z4,z6]),(0,[z126,z41,z1,z38,z4,z6]),(0,[z0,z1,z2,z3,z4,z1290]),(0,[z0,z1391,z2,z3,z4,z6]),(0,[z0,z362,z2,z3,z74,z6]),(1,[z0,z2,z717,z4,z6]),(0,[z463,z0,z1,z2,z4,z55]),(0,[z0,z1,z4,z6,z55,z831])],[(0,[z1,z38,z3,z4,z39,z6]),(0,[z0,z1,z2,z4,z18,z40]),(0,[z0,z1,z2,z4,z474,z55])],[(0,[z0,z1,z36,z21,z4,z6]),(0,[z0,z1,z91,z3,z74,z6])],[(0,[z0,z1,z2,z1221,z3,z4]),(0,[z179,z1,z43,z3,z4,z6]),(0,[z0,z1392,z2,z3,z4,z6]),(0,[z0,z1,z37,z3,z438,z6]),(0,[z1393,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z1394,z6]),(0,[z278,z1,z1131,z3,z4,z6])],[(0,[z124,z1,z38,z3,z4,z6]),(0,[z41,z0,z1,z43,z4,z134]),(0,[z72,z1,z2,z23,z24,z6]),(0,[z0,z2,z3,z4,z928,z6]),(0,[z0,z1,z1395,z2,z4,z6])],[(0,[z0,z1,z2,z471,z6,z55]),(0,[z0,z1,z2,z4,z1396,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 486) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 486).take 491) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 977).take 478) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1455).take 100) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1555)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [486, 491, 478, 100] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 92).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 92).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 186).take 99).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 285).take 102).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 387).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 478).take 34).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [92, 94, 99, 102, 91, 34] = true :=
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

end PEqualNP.Outside.L_meta_38487

theorem PEqualNP.Outside.L_meta_38487 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 4006144192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 4006144192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38487.solve