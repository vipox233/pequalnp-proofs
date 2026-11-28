import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47108

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
  Nat.testBit (4008241888 * 2 ^ 32 + 3940608640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x8001170b0c2c30ab#64 ++ 0xdf433f3f1cfc71ff#64 : BitVec 128),
   (0x811c4b5961658665#64 ++ 0xffbccfd9e3678e67#64 : BitVec 128),
   (0x04c0a0a0b682db86#64 ++ 0xefc0f0e1ff87ff87#64 : BitVec 128),
   (0x08ee00f403d00d50#64 ++ 0x7dff00fe03f80ff8#64 : BitVec 128),
   (0x12f7fd0003ff6000#64 ++ 0x76ffff0003fff000#64 : BitVec 128),
   (0x22fbfeffd8000000#64 ++ 0x7afffffffc000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [4, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [13, 10]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x04c0a0a0b682db86 0xefc0f0e1ff87ff87

def z1 : W := mkw 0x082e005401500450 0x103f001e00780078

def z2 : W := mkw 0x08ee00f403d00d50 0x7dff00fe03f80ff8

def z3 : W := mkw 0x12f7fd0003ff6000 0x76ffff0003fff000

def z4 : W := mkw 0x22fbfeffd8000000 0x7afffffffc000000

def z5 : W := mkw 0x8001170b0c2c30ab 0xdf433f3f1cfc71ff

def z6 : W := mkw 0x811c4b5961658665 0xffbccfd9e3678e67

def z7 : W := mkw 0x00d4e90003e74000 0x76fcff0003e7f000

def z8 : W := mkw 0x81144b0961658225 0xf6bccf01e3678007

def z9 : W := mkw 0x04c000a0b6809b86 0xedc000e1ff800f87

def z10 : W := mkw 0x2210e800d0000000 0x0000c000e0000000

def z11 : W := mkw 0x8001160b0c0010ab 0xdb433f3f1c0001ff

def z12 : W := mkw 0x93feeb5963f7c665 0xffbccfd9e3678e67

def z13 : W := mkw 0x9104010023ffe665 0x8500000003fffe67

def z14 : W := mkw 0x04c0a0a0b282cb04 0x6ac0f0e1ff038e00

def z15 : W := mkw 0x0000000004001082 0xdf43303f1cfc71ff

def z16 : W := mkw 0x00c0a0a090000000 0x6ac0f0e1fc000000

def z17 : W := mkw 0x040000002682db86 0x850000000387ff87

def z18 : W := mkw 0x2211fe0bd8000000 0x0200ff01fc000000

def z19 : W := mkw 0x26fbfefffe82db86 0xffffffffff87ff87

def z20 : W := mkw 0x04c0a0a096825982 0x004030201c807180

def z21 : W := mkw 0x811c4b5941650461 0x103c0f1800600060

def z22 : W := mkw 0x8114490021658665 0xf7bccf0003678e67

def z23 : W := mkw 0x12f75d0003fd2000 0x74ff0f0003f80000

def z24 : W := mkw 0x8108025960008665 0xef80c0d9e3078e67

def z25 : W := mkw 0xa11c4bfff9658665 0xffbccfffff678e67

def z26 : W := mkw 0x223bfe5fd8000000 0x123fff1ffc000000

def z27 : W := mkw 0x8401170b2eaefbaf 0xdf433f3f1fffffff

def z28 : W := mkw 0x200802ffd8000000 0x080000fffc000000

def z29 : W := mkw 0x223b5e5f48000000 0x103f0f1e00000000

def z30 : W := mkw 0x22fffeffdbd00000 0x7efffffffff80000

def z31 : W := mkw 0x0004000003d00000 0x0400000003f80000

def z32 : W := mkw 0x9bfffffd63ffef75 0xffffffffe3ffffff

def z33 : W := mkw 0x8001170b0c2c30ab 0x87003f011cfc71ff

def z34 : W := mkw 0x00184a5940000000 0x7abccfd9e0000000

def z35 : W := mkw 0x22e3b4a698000000 0x004330261c000000

def z36 : W := mkw 0x81dc4bf963e58f65 0xfffccff9e3e78fe7

def z37 : W := mkw 0x1004010003ff6000 0x0400000003fff000

def z38 : W := mkw 0x2afffeffdbd00d50 0x7ffffffffff80ff8

def z39 : W := mkw 0x22fae8f4d0000000 0x20bcc0c0e0000000

def z40 : W := mkw 0x88ee01f407fc3dfb 0xfdff00fe03fc7fff

def z41 : W := mkw 0x8504010027e7dfe7 0x8500000003e7ffe7

def z42 : W := mkw 0x00c0a0002282c204 0xefc0f0c1e387fe07

def z43 : W := mkw 0x26fbfefffc02d286 0xfafffffffc07f007

def z44 : W := mkw 0x0808005400000450 0x0000001e00000078

def z45 : W := mkw 0x0000000000000000 0x0043002600980198

def z46 : W := mkw 0x32ffffffdbff6000 0x7efffffffffff000

def z47 : W := mkw 0x8108025960008665 0x890000d9e0000e67

def z48 : W := mkw 0x00000100002c2000 0x0400000000fc7000

def z49 : W := mkw 0x08ee00f403d00d50 0x7dbc00d803600e60

def z50 : W := mkw 0x002a005400000000 0x103f001e00000000

def z51 : W := mkw 0x16f7fda0b7fffb86 0xffffffe1ffffff87

def z52 : W := mkw 0x02f3fe0b08000000 0x7affff3f1c000000

def z53 : W := mkw 0x12e3b400029a6000 0x0043300000987000

def z54 : W := mkw 0x93ffff5963ffe665 0xffffffd9e3fffe67

def z55 : W := mkw 0x080800f400000d50 0x090000fe00000ff8

def z56 : W := mkw 0x02f3fc0000000000 0x72ffff0000000000

def z57 : W := mkw 0x811c4b59656db6ef 0xffbccfd9e3ffffff

def z58 : W := mkw 0x0c0800f4b4009fd6 0x890000fffc000fff

def z59 : W := mkw 0x0804000001500450 0x0000000000780078

def z60 : W := mkw 0x0000000020008204 0xef80c0c1e3078e07

def z61 : W := mkw 0x85dcebf9f7e7dfe7 0xfffcfff9ffe7ffe7

def z62 : W := mkw 0x08ee00f403d00d50 0x20bc00c003000e00

def z63 : W := mkw 0x88ef17ff0ffc3dfb 0xffff3fff1ffc7fff

def z64 : W := mkw 0x93f7ff0963ffe225 0xf6ffff01e3fff007

def z65 : W := mkw 0x32fee8f4d3d34000 0x20bcc0c0e3038000

def z66 : W := mkw 0x00011500002c2000 0x56433f0000fc7000

def z67 : W := mkw 0x00e6000003d00000 0x7dff003e03f801f8

def z68 : W := mkw 0x0001160b08000000 0x5a433f3f1c000000

def z69 : W := mkw 0x8104010021658665 0x8500000003678e67

def z70 : W := mkw 0x040000a0b4009b86 0x890000e1fc000f87

def z71 : W := mkw 0x81184b5960258665 0x8b00cfd9e0078e67

def z72 : W := mkw 0x931dff59616fe665 0xffbcffd9e367fe67

def z73 : W := mkw 0x04c1b6abbe82db86 0xffc3ffffff87ff87

def z74 : W := mkw 0x00c0a00000000000 0x62c0f00000000000

def z75 : W := mkw 0x1404010027fffb86 0x8500000003ffff87

def z76 : W := mkw 0x200800f4d0000000 0x000000c0e0000000

def z77 : W := mkw 0x08ea00f402900910 0x78ff00fe00980198

def z78 : W := mkw 0x08ee005403d00450 0x74ff001e03f80078

def z79 : W := mkw 0x2611fe0bfc02d286 0x8200ff01fc07f007

def z80 : W := mkw 0x08ef15f403fc2d50 0x7fff3ffe03fc7ff8

def z81 : W := mkw 0x00195e5b48000000 0x7afffffffc000000

def z82 : W := mkw 0x811d5f5b6d6db6ef 0xffffffffffffffff

def z83 : W := mkw 0x0000000004001082 0xcf4030211c847187

def z84 : W := mkw 0x84c1b7abbeaefbaf 0xffc3ffffffffffff

def z85 : W := mkw 0x2afbfeffd8000d50 0x7bfffffffc000ff8

def z86 : W := mkw 0x89ff5fff6ffdbfff 0xffffffffffffffff

def z87 : W := mkw 0x02e3b40000000000 0x0043300000000000

def z88 : W := mkw 0x000000020c00108a 0x000000261c000198

def z89 : W := mkw 0x08ee00f403d00d50 0x20ff00e603980f98

def z90 : W := mkw 0x893e4b5d61758675 0xffbfcfdfe37f8e7f

def z91 : W := mkw 0x0ceea0f4b7d2dfd6 0xfffff0ffffffffff

def z92 : W := mkw 0x000c005001400440 0x7dff00fe03f80ff8

def z93 : W := mkw 0x0000000000000000 0x1003001e00780078

def z94 : W := mkw 0xa311ff0bf8258225 0x8200ff01fc078007

def z95 : W := mkw 0x8001170b082c2029 0x10030f1e00780078

def z96 : W := mkw 0x00104a0940000000 0x0200cf01e0000000

def z97 : W := mkw 0x000114020c08308a 0x5d43303e1cf871f8

def z98 : W := mkw 0x0001140000082000 0x0043300000987000

def z99 : W := mkw 0x32fffeffdbd34000 0x7affffffff038000

def z100 : W := mkw 0x2afee8f4d3d00d50 0x7dffc0fee3f80ff8

def z101 : W := mkw 0x81104b0940250021 0x00000f0000000000

def z102 : W := mkw 0x0000000000000000 0x5d43003e00f801f8

def z103 : W := mkw 0x8001170b0c2c30ab 0x82003f011c047007

def z104 : W := mkw 0x18ee01f403ff6d50 0x7dff00fe03fffff8

def z105 : W := mkw 0x04c0a0a0b682db86 0x894030e1fc807f87

def z106 : W := mkw 0x12f7ff0b0bff6000 0x7effff3f1ffff000

def z107 : W := mkw 0x811d5f5b6d6db6ef 0xffbcffd9ff67fe67

def z108 : W := mkw 0x8000020b0c0010ab 0xcf40303f1c8471ff

def z109 : W := mkw 0x12f7fd0003ff6000 0x7fffff3e03fff1f8

def z110 : W := mkw 0x80000309042c30ab 0xdf000f1900fc71ff

def z111 : W := mkw 0x0000a00000024000 0x0200f0000007f000

def z112 : W := mkw 0x81144b0961658665 0x8700cf01e3678e67

def z113 : W := mkw 0x0804000003d00d50 0x0500000003f80ff8

def z114 : W := mkw 0x8100010020258225 0x8000000000078007

def z115 : W := mkw 0x08ea00f400000d50 0x79ff00fe00000ff8

def z116 : W := mkw 0xa00802ffdc0010ab 0x890000fffc0001ff

def z117 : W := mkw 0xa3feebfdf1658665 0xffbccfd9e3678e67

def z118 : W := mkw 0x811d5f5b496d2469 0x103f0f1e00780078

def z119 : W := mkw 0x00c000a002800900 0x6dc000e003800f80

def z120 : W := mkw 0x1237fd00017f6000 0x123fff00007ff000

def z121 : W := mkw 0x00c0a00002824000 0x66c0f0000387f000

def z122 : W := mkw 0x082e00f401500d50 0x193f00fe00780ff8

def z123 : W := mkw 0x00011500042c3082 0xdf433f211cfc7187

def z124 : W := mkw 0x12f7fda093ff6000 0x7effffe1fffff000

def z125 : W := mkw 0x0400a000b682db86 0x8700f001ff87ff87

def z126 : W := mkw 0x880802ff0c001dfb 0x890000ff1c000fff

def z127 : W := mkw 0x02f2e80000000000 0x20bcc00000000000

def z128 : W := mkw 0x12fffdf403ff6000 0x7efffffe03fff000

def z129 : W := mkw 0x80000100042c30ab 0x8500000000fc71ff

def z130 : W := mkw 0x92f7ff0903ff6021 0xffffff1903fff067

def z131 : W := mkw 0x011c495061658644 0x76bccfc0e3678e00

def z132 : W := mkw 0x0400a000b402d286 0x8200f001fc07f007

def z133 : W := mkw 0x040000002402d286 0x800000000007f007

def z134 : W := mkw 0x0000000020008204 0x2080c0c0e3038e00

def z135 : W := mkw 0x0000010000240000 0x56000f0000640000

def z136 : W := mkw 0x811c4b5941650461 0x7abccfd9e0600060

def z137 : W := mkw 0x00ea00f400000000 0x78ff00fe00000000

def z138 : W := mkw 0xa3fbfffff8258225 0xfafffffffc078007

def z139 : W := mkw 0x8100000020008665 0x8100000000000e67

def z140 : W := mkw 0x0008025940000000 0x080000d9e0000000

def z141 : W := mkw 0x0104000021418644 0x0000000003038e00

def z142 : W := mkw 0x011c485061418644 0x20bcc0c0e3038e00

def z143 : W := mkw 0x22f3fe0bd8000000 0x72ffff01fc000000

def z144 : W := mkw 0x891c4b5963f58f75 0xffbccfd9e3ff8fff

def z145 : W := mkw 0x000114020c08308a 0xcf4330271c9c719f

def z146 : W := mkw 0x12f6e80003d34000 0x20bcc00003038000

def z147 : W := mkw 0x12f3fd00002f6000 0x72ffff000007f000

def z148 : W := mkw 0x80011500042c30ab 0xd7433f0000fc71ff

def z149 : W := mkw 0x0014490001650000 0x76bccf0003678000

def z150 : W := mkw 0x04c0a0a096825982 0x6ac0f0e1fc807180

def z151 : W := mkw 0x1afffdf403ff6d50 0x7ffffffe03fffff8

def z152 : W := mkw 0x00e6000003d00000 0x74ff000003f80000

def z153 : W := mkw 0x1afee8f403d34d50 0x20bcc0c003038e00

def z154 : W := mkw 0x8000020b0c0010ab 0xdd43003f1cf801ff

def z155 : W := mkw 0x10000000029a6000 0x0000000000987000

def z156 : W := mkw 0x0000000002800900 0x0500000003800f80

def z157 : W := mkw 0x882f175f097c2479 0x103f0f1e00780078

def z158 : W := mkw 0x81104b0960258225 0x8200cf01e0078007

def z159 : W := mkw 0x08e200a402900910 0x0043002600980198

def z160 : W := mkw 0x011c4a5961418644 0x7abccfd9e3038e00

def z161 : W := mkw 0x8dfeebfdf7f7dff7 0xffffffffffffffff

def z162 : W := mkw 0x92375f0b0d7d30ab 0xdf7f3f3f1cfc71ff

def z163 : W := mkw 0x08ee00f403d00d50 0x6dfc00e003800f80

def z164 : W := mkw 0x0000020900000000 0x5a000f1900000000

def z165 : W := mkw 0x1611fd00b42ff286 0x8200ff01fc07f007

def z166 : W := mkw 0x1211fd00002f6000 0x0200ff000007f000

def z167 : W := mkw 0x811c4b5b6d6596ef 0xffbccfffff678fff

def z168 : W := mkw 0x04d8eaf9f682db86 0xfffcfff9ff87ff87

def z169 : W := mkw 0x81115f0b6c2db2af 0x8200ff01fc07f007

def z170 : W := mkw 0x8108025b6c0096ef 0x890000fffc000fff

def z171 : W := mkw 0x0000000000000000 0x0000000000000000

def z172 : W := mkw 0x0000a00090000000 0x0200f001fc000000

def z173 : W := mkw 0x0014490021658204 0xffbccfc1e3678e07

def z174 : W := mkw 0x8001170b0c2c30ab 0xda433f3f1c047007

def z175 : W := mkw 0x32fbfeffda9a6000 0x7afffffffc987000

def z176 : W := mkw 0x00ee00f401400440 0x7dff00fe03600e60

def z177 : W := mkw 0x12115d00002d2000 0x00000f0000000000

def z178 : W := mkw 0x80c1b7ab9c2c30ab 0xffc3fffffcfc71ff

def z179 : W := mkw 0xa23b5f5f4c2c30ab 0xdf7f3f3f1cfc71ff

def z180 : W := mkw 0x8000020b0c0010ab 0x800000011c000007

def z181 : W := mkw 0x8000030b0c2410ab 0xdf000f3f1c6401ff

def z182 : W := mkw 0x00eb16ff08000000 0x7aff3fff1c000000

def z183 : W := mkw 0x0400a000b402d286 0xcf40f021fc87f187

def z184 : W := mkw 0x0001140000000000 0x52433f0000000000

def z185 : W := mkw 0x8000020b0c0010ab 0x8900003f1c0001ff

def z186 : W := mkw 0x09fe48f463d18f54 0x7dffc0fee3fb8ff8

def z187 : W := mkw 0x04000000b4009286 0x80000001fc000007

def z188 : W := mkw 0x02f3fc0002824000 0x76ffff000387f000

def z189 : W := mkw 0x850802f9f4009fe7 0x890000f9fc000fe7

def z190 : W := mkw 0x22f3feafd8000000 0x0243ff27fc000000

def z191 : W := mkw 0x08eea0f403d24d50 0x7ffff0fe03fffff8

def z192 : W := mkw 0x12375d00017d2000 0x103f0f0000780000

def z193 : W := mkw 0xa2fbfeffdc0010ab 0xfbfffffffc0001ff

def z194 : W := mkw 0x000114020c08308a 0x004330261c987198

def z195 : W := mkw 0x8000030900240021 0xdf000f1900640067

def z196 : W := mkw 0x1efffdf4b7ffffd6 0xffffffffffffffff

def z197 : W := mkw 0x2afffeffd9500450 0x7afffffffc780078

def z198 : W := mkw 0x80000100042c30ab 0xcf4030211cfc71ff

def z199 : W := mkw 0x12f6e80003d34000 0x74ffc00003fb8000

def z200 : W := mkw 0x8105170b2d6db6ef 0xdf433f3f1fffffff

def z201 : W := mkw 0x0cee00f427d2dfd6 0xfdff00fe03ffffff

def z202 : W := mkw 0x89fe4bfd43f50d71 0x7dff0ffe03f80ff8

def z203 : W := mkw 0x0018485040000000 0x20bcc0c0e0000000

def z204 : W := mkw 0x04c0a0a0b682db86 0x854030201f87ff87

def z205 : W := mkw 0x011c485041410440 0x003c000000000000

def z206 : W := mkw 0x04cca0f0b7c2dfc6 0xfffcf0f9ffe7ffe7

def z207 : W := mkw 0x0001140208082008 0x0003000600180018

def z208 : W := mkw 0x8001170b0c2c30ab 0x82433f271c9c719f

def z209 : W := mkw 0x12ffff5943ff6000 0x7effffd9e3fff000

def z210 : W := mkw 0xa3ffffffd9650461 0x7afffffffc600060

def z211 : W := mkw 0x22fbfeffd8000000 0x22bcffc1fc000000

def z212 : W := mkw 0x13fee85063d3c644 0x20bcc0c0e3038e00

def z213 : W := mkw 0x12f7fd020fff708a 0x76ffff261ffff198

def z214 : W := mkw 0x0000000000000000 0x4d40002000800180

def z215 : W := mkw 0x92f7ff0b0fff70ab 0xf6ffff011ffff007

def z216 : W := mkw 0x00ea00f400000000 0x7dff00fe00f801f8

def z217 : W := mkw 0x88ee03fd03f40d71 0xffff0fff03fc0fff

def z218 : W := mkw 0x0010480000000000 0x72bccf0000000000

def z219 : W := mkw 0x32fffdf4d3ff6000 0x76ffffc0e3fff000

def z220 : W := mkw 0x04c0a0a0b4009b86 0xebc0f0e1fc000f87

def z221 : W := mkw 0x0026000001500000 0x103f000000780000

def z222 : W := mkw 0x02335c0000000000 0x103f0f0000000000

def z223 : W := mkw 0x22fbfeffdc001082 0xfffffffffc847187

def z224 : W := mkw 0x22fbfeffd8000000 0x30bfcfdee0000000

def z225 : W := mkw 0x0ceea0f4b7d2dfd6 0xeffcf0e1ff87ff87

def z226 : W := mkw 0x89fe4bfd63f58f75 0xffbccfd9e3678e67

def z227 : W := mkw 0x00d8eaf9d0000000 0x7afcfff9fc000000

def z228 : W := mkw 0x811c4a5961418665 0xa9bcc0d9e3038e67

def z229 : W := mkw 0x05dce8f0f7c3dfc6 0xeffcf0e1ff87ff87

def z230 : W := mkw 0x22fb5eff48000000 0x78ff0ffe00000000

def z231 : W := mkw 0x96f7ffabbffffbaf 0xffffffffffffffff

def z232 : W := mkw 0x890802fd60008f75 0x890000ffe0000fff

def z233 : W := mkw 0x1af7fd0003ff6d50 0x77ffff0003fffff8

def z234 : W := mkw 0x2201b40298000000 0x000030001c000000

def z235 : W := mkw 0x2219fe5bd8000000 0x7abcffd9fc000000

def z236 : W := mkw 0x04c0a0a096825982 0x66c0f0201f87f180

def z237 : W := mkw 0x00c0a0a090000000 0x004030201c000000

def z238 : W := mkw 0x26e3b4a69e825982 0x004330261c807180

def z239 : W := mkw 0x0000000004001082 0x004030201c807180

def z240 : W := mkw 0x84c1b7ab9eae79ab 0xdf433f3f1cfc71ff

def z241 : W := mkw 0x00ea00f400000000 0x20bc00c000000000

def z242 : W := mkw 0x04c0a0a0b682db86 0xa280f0c1ff07fe07

def z243 : W := mkw 0x0ce2a0a4b692db96 0xefc3f0e7ff9fff9f

def z244 : W := mkw 0x223b5effd8000000 0x183f0ffffc000000

def z245 : W := mkw 0x02fbfcf400000000 0x7afffffe00000000

def z246 : W := mkw 0x08ef14f60fd83dda 0x7dff30fe1ff87ff8

def z247 : W := mkw 0x00c0a0a090000000 0x2080c0c0e0000000

def z248 : W := mkw 0x011c485061418644 0x7dbcc0d8e3638e60

def z249 : W := mkw 0x8000030900240021 0xdf430f3f00fc01ff

def z250 : W := mkw 0x1014490003ff6000 0x76bccf0003fff000

def z251 : W := mkw 0x0000000000000000 0x5d00001800600060

def z252 : W := mkw 0x00e7150003fc2000 0x76ff3f0003fc7000

def z253 : W := mkw 0xa211ff0bdc2c30ab 0x8200ff01fc047007

def z254 : W := mkw 0x8000030920248225 0xff80cfd9e3678e67

def z255 : W := mkw 0x0008005000000000 0x78bc00d800000000

def z256 : W := mkw 0x16f7fda097ff7982 0x76ffff201ffff180

def z257 : W := mkw 0x080800f400000d50 0x000000c000000e00

def z258 : W := mkw 0x00c0a0a092824000 0x6ec0f0e1ff87f000

def z259 : W := mkw 0x92f7ff0b0fff70ab 0xffffff3f1ffff1ff

def z260 : W := mkw 0x84c0a1a0b6aefbaf 0xefc0f0e1ffffffff

def z261 : W := mkw 0x0400a0a0b402db86 0x8b00f0e1fc07ff87

def z262 : W := mkw 0x92f7fd0007ff70ab 0xf7ffff0003fff1ff

def z263 : W := mkw 0x8104010001650461 0x0000000000600060

def z264 : W := mkw 0x02f7fc0003d00000 0x76ffff0003f80000

def z265 : W := mkw 0x00155d00016d2000 0x76ffff0003fff000

def z266 : W := mkw 0x22fbfeffda824000 0x7effffffff87f000

def z267 : W := mkw 0x80155f0b0d6d30ab 0xffffff3f1ffff1ff

def z268 : W := mkw 0x0004000001400000 0x74bc000003600000

def z269 : W := mkw 0x81040100256db6ef 0x8500000003ffffff

def z270 : W := mkw 0x000800f400000000 0x080000fe00000000

def z271 : W := mkw 0x02f3fd00002c2000 0x76ffff0000fc7000

def z272 : W := mkw 0x32f7fda69bff6000 0x76ffff261ffff000

def z273 : W := mkw 0x893e4b5d41750471 0x103f0f1e00780078

def z274 : W := mkw 0x811c4b5961658665 0x923ccf19e0678067

def z275 : W := mkw 0x04c0a0a0b282cb04 0x2080c0c0e3038e00

def z276 : W := mkw 0x011c485061418644 0xefbcc0c1e3078e07

def z277 : W := mkw 0x223b5e5f48000000 0x7abfcfdfe0000000

def z278 : W := mkw 0x83ffff5961658665 0xffffffd9e3678e67

def z279 : W := mkw 0xa2fbffffdc2c30ab 0xfffffffffcfc71ff

def z280 : W := mkw 0x933f5f59617da665 0xffbfcfd9e37f8e67

def z281 : W := mkw 0x0000000000000000 0xcf00000100040007

def z282 : W := mkw 0xa2fbffffdc2c30ab 0xfafffffffc047007

def z283 : W := mkw 0x000000a000000900 0x090000e000000f80

def z284 : W := mkw 0x1afffd5403ff6450 0x76ffff1e03fff078

def z285 : W := mkw 0x240802fffc009b86 0x890000fffc000f87

def z286 : W := mkw 0x080c005003d00d50 0x7dbc00d803f80ff8

def z287 : W := mkw 0x1236480001510000 0x003c000000000000

def z288 : W := mkw 0x22fbfeffd8000000 0x7ffffffffcf801f8

def z289 : W := mkw 0x1215fd00016f6000 0x76bcff000367f000

def z290 : W := mkw 0x08ee00f401500450 0x78ff00fe00780078

def z291 : W := mkw 0xabfffffffbf58f75 0xffffffffffff8fff

def z292 : W := mkw 0x082e005401500450 0x003c000000000000

def z293 : W := mkw 0x0000000000000000 0x4640300000847000

def z294 : W := mkw 0x811c4b59656596e7 0xfffcfff9ffe7ffe7

def z295 : W := mkw 0x0010490000250000 0x0200cf0000078000

def z296 : W := mkw 0x12375d0003ff6000 0x143f0f0003fff000

def z297 : W := mkw 0x811c4b5961658665 0x953c0f1803678e67

def z298 : W := mkw 0x00c1b50002ae6000 0x76c3ff0003fff000

def z299 : W := mkw 0x0000000004001082 0x820030011c047007

def z300 : W := mkw 0x81dceb5963e7c665 0xfffcffd9e3e7fe67

def z301 : W := mkw 0x88ef17ff0bfc2d79 0x7dff0ffe03f80ff8

def z302 : W := mkw 0x20184affd8000000 0x7abccffffc000000

def z303 : W := mkw 0x16e3b4a0969a7982 0x004330201c987180

def z304 : W := mkw 0x1210e80000034000 0x0000c00000038000

def z305 : W := mkw 0x911c4b5963ffe665 0xffbccfd9e3fffe67

def z306 : W := mkw 0x082e005403d00d50 0x153f001e03f80ff8

def z307 : W := mkw 0x000000000408308a 0x0000000000987198

def z308 : W := mkw 0x8108025940000461 0x0000001800000060

def z309 : W := mkw 0x8001170b2c2cb2af 0xffc3ffffffffffff

def z310 : W := mkw 0x0804000003d00d50 0x0000000003000e00

def z311 : W := mkw 0x811c4b5961658665 0xffffcfffe3ff8fff

def z312 : W := mkw 0x800d175b0d6c34eb 0xffff3fff1ffc7fff

def z313 : W := mkw 0x8001160b0c0830ab 0x8943303f1c9871ff

def z314 : W := mkw 0x8109175b6c2cb6ef 0xdf433ffffcfc7fff

def z315 : W := mkw 0x00c0a0a0b0008204 0xefc0f0e1ff078e07

def z316 : W := mkw 0x0000000024009286 0xefc0f0e1ff87ff87

def z317 : W := mkw 0x2aff5eff4bd00d50 0x7dff0ffe03f80ff8

def z318 : W := mkw 0xa31dff5bf9658665 0xffbcffd9ff678e67

def z319 : W := mkw 0x12e3b50002be6000 0x56433f0000fc7000

def z320 : W := mkw 0x12f7fd0003ff6000 0x22bcff000307f000

def z321 : W := mkw 0x080c00f403d00d50 0x0d0000fe03f80ff8

def z322 : W := mkw 0x12f7fda003ff6900 0x7fffffe003ffff80

def z323 : W := mkw 0x8000020b08000029 0x0000001e00000078

def z324 : W := mkw 0x16f7fda0b3ffeb04 0x76ffffc0e3fffe00

def z325 : W := mkw 0x00e6000003d00000 0x20bc000003000000

def z326 : W := mkw 0x811c4b5961658665 0xa2bccfc1e3078e07

def z327 : W := mkw 0x92e3b70b0ebe70ab 0xdf433f3f1cfc71ff

def z328 : W := mkw 0x22d1feabd8000000 0x6ac0ffe1fc000000

def z329 : W := mkw 0xa3fffffff9658665 0xffffffffff678e67

def z330 : W := mkw 0x00c0a00006825082 0xefc0f0211f87f187

def z331 : W := mkw 0x92375f0b097d2029 0x103f0f1e00780078

def z332 : W := mkw 0x02fbfe5940000000 0x7affffd9e0000000

def z333 : W := mkw 0x8104030921658665 0xdf000f1903678e67

def z334 : W := mkw 0x08eea0f493d00d50 0x7ffff0fffff80ff8

def z335 : W := mkw 0x97fffff9f7ffffe7 0xfffffff9ffffffe7

def z336 : W := mkw 0x12f6e80003d34000 0x66fcf0000387f000

def z337 : W := mkw 0x89fe4bfd63f58f75 0xffffcfffe3ff8fff

def z338 : W := mkw 0x0004010001650000 0x0400000003678000

def z339 : W := mkw 0x12f3fc00029a6000 0x72ffff0000987000

def z340 : W := mkw 0x00c000a002800900 0x0040002000800180

def z341 : W := mkw 0x2afee8f4d3d00d50 0x20bcc0c0e3000e00

def z342 : W := mkw 0x22fffeffd9400440 0x7fffffffff600e60

def z343 : W := mkw 0x12e7b40003da6000 0x74ff300003f87000

def z344 : W := mkw 0x000114020c08308a 0x000030001c007000

def z345 : W := mkw 0x0ceea0f4b3d2cf54 0x20bcc0c0e3038e00

def z346 : W := mkw 0x08e200a402900910 0x6dc300e603980f98

def z347 : W := mkw 0x000c005001400440 0x103c001800600060

def z348 : W := mkw 0x8001170b0c2c30ab 0x99030f3f1c7801ff

def z349 : W := mkw 0x0008005000000440 0x090000d800000e60

def z350 : W := mkw 0x0001160b08000000 0x5f433f3f1cf801f8

def z351 : W := mkw 0x10e6010003ff6000 0x74ff000003fff000

def z352 : W := mkw 0x32ffffffd97d2000 0x7afffffffc780000

def z353 : W := mkw 0x14c4a1a0b7fffb86 0xefc0f0e1ffffff87

def z354 : W := mkw 0x22fbfeffda800900 0x7fffffffff800f80

def z355 : W := mkw 0x16f6e8a0b7d3db86 0xeffcf0e1ff87ff87

def z356 : W := mkw 0x0400a00094025082 0x000030001c007000

def z357 : W := mkw 0x2219feffd8000000 0x0a00fffffc000000

def z358 : W := mkw 0x2ae3b4a69a900910 0x004330261c980198

def z359 : W := mkw 0x10040100017d2000 0x0000000000780000

def z360 : W := mkw 0x82f3ff0b0c2c30ab 0xffffff3f1cfc71ff

def z361 : W := mkw 0x00c0a00002824000 0x2080c00003038000

def z362 : W := mkw 0x0004000001400440 0x0500000003600e60

def z363 : W := mkw 0x2afffeffdbd00d50 0x7affffffff000e00

def z364 : W := mkw 0x1215fd0003ff6000 0x0600ff0003fff000

def z365 : W := mkw 0x0400a000b402d286 0xef80f0c1ff07fe07

def z366 : W := mkw 0x0804000003d00d50 0x5d43003e03f80ff8

def z367 : W := mkw 0x840117abbc2cbbaf 0xdf433ffffcfc7fff

def z368 : W := mkw 0x80000100002c2029 0x0000000000780078

def z369 : W := mkw 0x12f7fd0003ff6000 0x30bfcf00037b8000

def z370 : W := mkw 0x1804010003ff6d50 0x0500000003fffff8

def z371 : W := mkw 0x0001160b08000000 0x02003f011c000000

def z372 : W := mkw 0x04c0a0a0b682db86 0xffc3f0ffffffffff

def z373 : W := mkw 0x8001170b0c2c30ab 0x95030f1e00fc71ff

def z374 : W := mkw 0x16f7fd0027fffb86 0xf7ffff0003ffff87

def z375 : W := mkw 0x811c4b5941650461 0xdf3c0f1900640067

def z376 : W := mkw 0x80144b0901650021 0xffbccf1903678067

def z377 : W := mkw 0x8001170b0c2c30ab 0x92033f1f1c7c707f

def z378 : W := mkw 0x02f3fca090000000 0x7affffe1fc000000

def z379 : W := mkw 0x00c0a0a094001082 0xefc0f0e1fc847187

def z380 : W := mkw 0x08ee00f407d01dd2 0xffff30ff1ffc7fff

def z381 : W := mkw 0x9005170b0fff70ab 0xdf433f3f1ffff1ff

def z382 : W := mkw 0x9004010007ff70ab 0x8500000003fff1ff

def z383 : W := mkw 0x0014480001410000 0x20bcc00003038000

def z384 : W := mkw 0x0000000000000000 0x0500000000f801f8

def z385 : W := mkw 0x04c0a0a0b682db86 0xa580c0c0e387ff87

def z386 : W := mkw 0x0ce2a0a496925992 0x004330261c987198

def z387 : W := mkw 0x04c1b4a29e8a798a 0x004330261c987198

def z388 : W := mkw 0x3affffffdbff6d50 0x7ffffffffffffff8

def z389 : W := mkw 0x20ea02ffd8000000 0x78ff00fffc000000

def z390 : W := mkw 0x22e3b4a698000000 0x6ac3f0e7fc000000

def z391 : W := mkw 0xaaffffffdffc3dfb 0xfffffffffffc7fff

def z392 : W := mkw 0x2afbfeffda900910 0x7afffffffc980198

def z393 : W := mkw 0x20c8a2ffd8000000 0x6ac0f0fffc000000

def z394 : W := mkw 0x10c4a10003ff6000 0x66c0f00003fff000

def z395 : W := mkw 0x22faeafdd0000000 0x7abccfd9e0000000

def z396 : W := mkw 0x08ea00f402900d50 0x094300fe00980ff8

def z397 : W := mkw 0x000c005021408644 0xffbcc0d9e3678e67

def z398 : W := mkw 0x0000000000000000 0x5443000000f80000

def z399 : W := mkw 0x1a3f5d54017d2450 0x103f0f1e00780078

def z400 : W := mkw 0x16d1fda0b6affb86 0xefc0ffe1ff87ff87

def z401 : W := mkw 0x811c4b5941650461 0x76bccf1803678060

def z402 : W := mkw 0x22fbfefff8008204 0xffffffffff078e07

def z403 : W := mkw 0xb3fffffffbffe665 0xfffffffffffffe67

def z404 : W := mkw 0x933f5f59417d2461 0x103f0f1800780060

def z405 : W := mkw 0xa3fbfefff8008665 0xfbfffffffc000e67

def z406 : W := mkw 0x8001170b082c2029 0x56433f1e00fc7078

def z407 : W := mkw 0x080000a400000910 0x0000002600000198

def z408 : W := mkw 0x32ffff5f4bff6000 0x76ffff1e03fff000

def z409 : W := mkw 0x8001170b082c2029 0xdf030f1f007c007f

def z410 : W := mkw 0x800c035901640461 0xffbc0fd903640e67

def z411 : W := mkw 0x8108035960248665 0xdf000fd9e0640e67

def z412 : W := mkw 0xa6fbfffffeaefbaf 0xffffffffffffffff

def z413 : W := mkw 0x1004000003d34000 0x0000000003038000

def z414 : W := mkw 0x04c1b5a0b6aefb86 0xffc3ffe1ffffff87

def z415 : W := mkw 0x22fbfe5f48000000 0x72ffff1e00000000

def z416 : W := mkw 0x000c005001400440 0x7dbc00d803600e60

def z417 : W := mkw 0x800115020c2c30ab 0x854330261cfc71ff

def z418 : W := mkw 0x040000a0b0008b04 0x000000c0e0000e00

def z419 : W := mkw 0x12f7fd0003ff6000 0x107f3f0000f87000

def z420 : W := mkw 0x1201b400000a6000 0x0000300000007000

def z421 : W := mkw 0x08e600a403d00910 0x74ff002603f80198

def z422 : W := mkw 0x0001160b0c001082 0xdf433f3f1c847187

def z423 : W := mkw 0x8000030900240021 0x82000f0100040007

def z424 : W := mkw 0x81115f0b6c2db2af 0xdf43ff3ffcfff1ff

def z425 : W := mkw 0x10000100002f6000 0x000000000007f000

def z426 : W := mkw 0x1afffdf403ff6d50 0x76ffffc003fffe00

def z427 : W := mkw 0x0000000000000000 0x6d8000c003000e00

def z428 : W := mkw 0x2efffeffffd2dfd6 0xffffffffffffffff

def z429 : W := mkw 0x81dcebf9f1658665 0xfffcfff9ff678e67

def z430 : W := mkw 0x08ee00f403d00d50 0x74ff00c003f80e00

def z431 : W := mkw 0x0822000400100010 0x0003000600180018

def z432 : W := mkw 0x04c0a0a092824900 0x0000000000000000

def z433 : W := mkw 0x81fe4b5963f58665 0xffffcfd9e3ff8e67

def z434 : W := mkw 0x80eb17ff0c2c30ab 0xffff3fff1cfc71ff

def z435 : W := mkw 0x88e317af0ebc39bb 0xdf433f3f1cfc71ff

def z436 : W := mkw 0x22ebb6ffd8000000 0x084330fffc000000

def z437 : W := mkw 0x00184a5960008204 0xffbccfd9e3078e07

def z438 : W := mkw 0x0000000000000000 0x0900003e000001f8

def z439 : W := mkw 0x22115e0b48000000 0x00000f0000000000

def z440 : W := mkw 0x1ae3b4a4029a6910 0x0043302600987198

def z441 : W := mkw 0x04c0a0a0b282cb04 0x6dc0c0e0e3838f80

def z442 : W := mkw 0x08ee00f423d08f54 0xffffc0ffe3ff8fff

def z443 : W := mkw 0x00e200a400000000 0x0043002600000000

def z444 : W := mkw 0x00e2000002900000 0x0043000000980000

def z445 : W := mkw 0x04c0a0a0b682db86 0xa980c0e1ff038f87

def z446 : W := mkw 0x26fae8f4f682db86 0xeffcf0e1ff87ff87

def z447 : W := mkw 0x80c117ab0eac39ab 0xffc33fff1ffc7fff

def z448 : W := mkw 0x26fbfeffde825982 0x7afffffffc807180

def z449 : W := mkw 0x12e3b4020e9a708a 0x004330261c987198

def z450 : W := mkw 0x891c4bfd61658f75 0xffbccfffe3678fff

def z451 : W := mkw 0x0000000000000000 0x5843003e00000000

def z452 : W := mkw 0x08e200a402900910 0x0000000000000000

def z453 : W := mkw 0x08ee00f403d00d50 0x78ff00fe03000e00

def z454 : W := mkw 0x04c0a000b682d286 0xe6c0f001ff87f007

def z455 : W := mkw 0x80000100042c30ab 0xdd43003e00fc71ff

def z456 : W := mkw 0x00fa4afd40000000 0x7affcfffe0000000

def z457 : W := mkw 0x0001160b08000000 0x10030f1e00000000

def z458 : W := mkw 0x12f7fd0007ff7082 0xffffff211ffff187

def z459 : W := mkw 0x8001170b0c2c30ab 0xd6433f011cfc7007

def z460 : W := mkw 0x811d5f59616da665 0xffffffd9e3fffe67

def z461 : W := mkw 0x04c0a0a0b682db86 0x20c0f0e0ff83ff80

def z462 : W := mkw 0x0ceea0f497d25dd2 0x7dff30fe1ff87ff8

def z463 : W := mkw 0x13fffd5063ffe644 0x76ffffc0e3fffe00

def z464 : W := mkw 0x02f7fd0001650000 0x76ffff0003678000

def z465 : W := mkw 0x04c0a0a0b682db86 0x8240f021fc87f187

def z466 : W := mkw 0x12f3fd0002bf6000 0x0243ff00009ff000

def z467 : W := mkw 0x1af7fda403ff6910 0x76ffff2603fff198

def z468 : W := mkw 0x080800f400000d50 0x5d4300fe00f80ff8

def z469 : W := mkw 0x85c4a1a0b7e7dfe7 0xefc0f0e1ffe7ffe7

def z470 : W := mkw 0x00c0000002800000 0x64c0000003800000

def z471 : W := mkw 0x08ee00f403d00d50 0x107f003e00f801f8

def z472 : W := mkw 0x8001170b0c2c30ab 0x8b003f3f1c0471ff

def z473 : W := mkw 0x24c8a2fffe82db86 0xefc0f0ffff87ff87

def z474 : W := mkw 0x22fbfeffd8000000 0x107f3f3e1c000000

def z475 : W := mkw 0x88ee02ff0fd01dfb 0xfdff00ff1ff80fff

def z476 : W := mkw 0x89ee01f423f58f75 0xfdff00fe03ff8fff

def z477 : W := mkw 0x00e6a00003d24000 0x76fff00003fff000

def z478 : W := mkw 0xa211ff0bdc2c30ab 0xdf43ff3ffcfc71ff

def z479 : W := mkw 0x04d4e9a0b7e7db86 0xfffcffe1ffe7ff87

def z480 : W := mkw 0x08c800f402800d50 0x6dc000fe03800ff8

def z481 : W := mkw 0x93ffff5943ff6461 0x76ffff1803fff060

def z482 : W := mkw 0x040000002682db86 0xcf4030211f87ff87

def z483 : W := mkw 0x12f7fd00017d2000 0x72ffff0000780000

def z484 : W := mkw 0xa23b5f5f482c2029 0x103f0f1e00780078

def z485 : W := mkw 0x0110480060018204 0x0000c000e0038000

def z486 : W := mkw 0x0000000020008204 0x890000c1e0000e07

def z487 : W := mkw 0x80e7170b0ffc30ab 0xffff3f3f1ffc71ff

def z488 : W := mkw 0x12f7fc0003db6000 0x20fff000039bf000

def z489 : W := mkw 0x00eaa0f490000000 0x7afff0fffc000000

def z490 : W := mkw 0x8001170b0c2c30ab 0x10433f3e1cf871f8

def z491 : W := mkw 0x001c4b5941650000 0x7ebccfd9e3678000

def z492 : W := mkw 0x12fffd5003ff6440 0x7fffffd803fffe60

def z493 : W := mkw 0x0000000002824000 0x040000000387f000

def z494 : W := mkw 0x1223140000182000 0x0003000000180000

def z495 : W := mkw 0x00184a5940000000 0x103c0f1800000000

def z496 : W := mkw 0x8000020900000021 0x8900001900000067

def z497 : W := mkw 0x22e3b6af98000000 0x5a433f3f1c000000

def z498 : W := mkw 0x082e005401500450 0x5d7f003e00f801f8

def z499 : W := mkw 0x2223140608000000 0x0003000600000000

def z500 : W := mkw 0x0c04000027d2dfd6 0x8500000003ffffff

def z501 : W := mkw 0x2008025f48000000 0x0000001e00000000

def z502 : W := mkw 0x00c000a002800900 0x7dc300fe03f80ff8

def z503 : W := mkw 0x12f7fd0023ffe204 0xffffffc1e3fffe07

def z504 : W := mkw 0x8510eb09f427d2a7 0x8200ff01fc07f007

def z505 : W := mkw 0x80195f5b4c2c30ab 0xfffffffffcfc71ff

def z506 : W := mkw 0x0000000000000000 0x4a4030211c000000

def z507 : W := mkw 0x04eaa0f4b682db86 0xfffff0ffff87ff87

def z508 : W := mkw 0x840002abbc009baf 0x890000fffc000fff

def z509 : W := mkw 0x000c005001400440 0x20bc00c003000e00

def z510 : W := mkw 0x0000000000000000 0x6a80c0c1e0000000

def z511 : W := mkw 0x851c4b5967e7dfe7 0xffbccfd9e3e7ffe7

def z512 : W := mkw 0x223b5e5f48000000 0x5a7f3f3f1c000000

def z513 : W := mkw 0x22fae8f4d0000000 0x6afcf0e1fc000000

def z514 : W := mkw 0xa10802fff8008665 0x890000fffc000e67

def z515 : W := mkw 0x040000002282cb04 0x0000000003038e00

def z516 : W := mkw 0x04e6a0a0b7d2db86 0xfffff0e1ffffff87

def z517 : W := mkw 0x22fbfcf6d8000000 0x20fff0e6fc000000

def z518 : W := mkw 0x811d5f5b696da66d 0xffbfcfdfe37f8e7f

def z519 : W := mkw 0x811d5f5b4d6d34eb 0xdf7f3f3f1cfc71ff

def z520 : W := mkw 0x0ceea0f4b3d2cf54 0x7dffc0fee3fb8ff8

def z521 : W := mkw 0x00c0a0a002824900 0x6fc0f0e00387ff80

def z522 : W := mkw 0x001c4a5941400440 0x7fbccfd9e3600e60

def z523 : W := mkw 0x26e3b4a6be82db86 0xefc3f0e7ff87ff87

def z524 : W := mkw 0xa2e3b7af9c2c30ab 0xdf433f3f1cfc71ff

def z525 : W := mkw 0x00c000a002800900 0x208000c003000e00

def z526 : W := mkw 0x26d1feabfe82db86 0xefc0ffe1ff87ff87

def z527 : W := mkw 0x81104b0960258225 0xdf00cf19e0678067

def z528 : W := mkw 0x22fae8f4d0000000 0x78ffc0fee0000000

def z529 : W := mkw 0x8001170b082c2029 0x5d430f3e00f801f8

def z530 : W := mkw 0x2a3f5e5f49500450 0x103f0f1e00780078

def z531 : W := mkw 0x9211ff0b0c2f70ab 0x8200ff011c07f007

def z532 : W := mkw 0x26fbfefffc009b86 0xfbfffffffc000f87

def z533 : W := mkw 0x00011500002c2000 0x5f433f3e00fc71f8

def z534 : W := mkw 0x08ef16ff0bd00d50 0x7fff3fff1ff80ff8

def z535 : W := mkw 0x8000030900240021 0x10000f1800600060

def z536 : W := mkw 0x12375d00017d2000 0x76bfcf00037f8000

def z537 : W := mkw 0x8001170b082c2029 0x5a433f3f1c780078

def z538 : W := mkw 0x040000a0b4009b86 0xcf4030e1fc847f87

def z539 : W := mkw 0x12e3b400029a6000 0x66c3f000039ff000

def z540 : W := mkw 0x81fe4bfd61658665 0xffffcfffe3678e67

def z541 : W := mkw 0x04c0a0a0b402d286 0xeac0f0e1fc07f007

def z542 : W := mkw 0x8001170b082c2029 0x00000f0000000000

def z543 : W := mkw 0x00c000a022808b04 0xefc0c0e1e3878f87

def z544 : W := mkw 0x80000000040010ab 0x81000000000001ff

def z545 : W := mkw 0x12f7fc0003d34000 0x72ffff0003038000

def z546 : W := mkw 0x0000000020008204 0x8500000003078e07

def z547 : W := mkw 0x89ee02fd63d08f75 0xfdff00ffe3f80fff

def z548 : W := mkw 0x00011500002c2000 0x02003f0000047000

def z549 : W := mkw 0x8001170b0c2c30ab 0xdf003f191c647067

def z550 : W := mkw 0x8000030b0c2c30ab 0x8d00003f1cfc71ff

def z551 : W := mkw 0x80000309042410a3 0xdf403f391ce471e7

def z552 : W := mkw 0x05dce8f0f3c3cf44 0x20bcc0c0e3038e00

def z553 : W := mkw 0x811c4b5961658665 0x30bccfd8e3638e60

def z554 : W := mkw 0x00c0a0a092800900 0x6fc0f0e1ff800f80

def z555 : W := mkw 0x04c0a0a096825982 0xcf4030211c847187

def z556 : W := mkw 0x8001170b0c2c30ab 0xcf403f211c847187

def z557 : W := mkw 0x36fffffffffffb86 0xffffffffffffff87

def z558 : W := mkw 0x0211fc0000000000 0x0200ff0000000000

def z559 : W := mkw 0x92f7ff0b0bff6029 0x76ffff1e03fff078

def z560 : W := mkw 0x00c000a000000000 0x68c000e000000000

def z561 : W := mkw 0x85ddfffbffefffef 0xffffffffffffffff

def z562 : W := mkw 0x0000000000000000 0x6680c00003078000

def z563 : W := mkw 0x8400010026aefbaf 0x8500000003ffffff

def z564 : W := mkw 0x06f3fca0b682db86 0xffffffe1ff87ff87

def z565 : W := mkw 0xa33f5f5f69658665 0xffbfcfdfe3678e67

def z566 : W := mkw 0x32e3b4a69a9a6000 0x004330261c987000

def z567 : W := mkw 0x2000020bd8000000 0x00000001fc000000

def z568 : W := mkw 0x00ee00f403d00000 0x7cff00fe03f80000

def z569 : W := mkw 0x00e2000000000000 0x70ff000000000000

def z570 : W := mkw 0x12f6e90003ff6000 0x24bcc00003fff000

def z571 : W := mkw 0x81104b0960258225 0xef80cfc1e3078e07

def z572 : W := mkw 0x26fae8f4f282cb04 0x20bcc0c0e3038e00

def z573 : W := mkw 0x8401b70bbc2ef2af 0x8200ff01fc07f007

def z574 : W := mkw 0x22f3fca698000000 0x72ffff261c000000

def z575 : W := mkw 0x00e600a003d00900 0x7dff00e003f80f80

def z576 : W := mkw 0x0014490001650000 0x103c0f0000600000

def z577 : W := mkw 0x0400000006825982 0x0000000000807180

def z578 : W := mkw 0x040000a0b682db86 0x8d0000e1ff87ff87

def z579 : W := mkw 0x22fbfeffdc08308a 0x7afffffffc987198

def z580 : W := mkw 0x12375d00017d2000 0x567f3f0000fc7000

def z581 : W := mkw 0x80011709002c2021 0xdf433f1900fc7067

def z582 : W := mkw 0x08ee00f403d00d50 0x25bc00c003f80ff8

def z583 : W := mkw 0x1aff5df403fd2d50 0x7dff0ffe03f80ff8

def z584 : W := mkw 0x84c0a2abbe82dbaf 0xefc0f0ffff87ffff

def z585 : W := mkw 0x9311ff09602fe225 0x8200ff01e007f007

def z586 : W := mkw 0x9211ff0b0c2f70ab 0xdf43ff3f1cfff1ff

def z587 : W := mkw 0x0800000002900910 0x0000000000980198

def z588 : W := mkw 0x00f6490003f50000 0x76ffcf0003ff8000

def z589 : W := mkw 0x22ffffffd9650000 0x7effffffff678000

def z590 : W := mkw 0x2211fe0bd8000000 0x5a43ff3ffc000000

def z591 : W := mkw 0x0000020b08000000 0x0800003f1c000000

def z592 : W := mkw 0x12e2a00002924000 0x0000000000000000

def z593 : W := mkw 0x040000a094001982 0x000000201c000180

def z594 : W := mkw 0x1211fd00002f6000 0x5643ff0000fff000

def z595 : W := mkw 0x93f7fd0023ffe665 0xf7ffff0003fffe67

def z596 : W := mkw 0x26fbfefffa82cb04 0x7affffffff038e00

def z597 : W := mkw 0x8904010023f58f75 0x8500000003ff8fff

def z598 : W := mkw 0x8000010000240021 0x8500000000640067

def z599 : W := mkw 0x85d0eba9f6a7dba7 0xefc0ffe1ff87ff87

def z600 : W := mkw 0x16f7fd00b7fff286 0xf6ffff01fffff007

def z601 : W := mkw 0x08ee00f403d00d50 0x29bc00fe03000ff8

def z602 : W := mkw 0x0001140208000000 0x004330261c000000

def z603 : W := mkw 0x80184b5940240021 0xffbccfd9e0640067

def z604 : W := mkw 0x0000000004001082 0x8500000000847187

def z605 : W := mkw 0x000000a090000000 0x080000e1fc000000

def z606 : W := mkw 0xa2fbffffd82c2029 0x7afffffffc780078

def z607 : W := mkw 0xa00917ffdc2c30ab 0xdf433ffffcfc71ff

def z608 : W := mkw 0x84c0a3a9b6a6dba7 0xffc0fff9ffe7ffe7

def z609 : W := mkw 0xa7ffffffffe7dfe7 0xffffffffffe7ffe7

def z610 : W := mkw 0x880917ff0c2c3dfb 0xdf433fff1cfc7fff

def z611 : W := mkw 0x22e2a0a490000000 0x0000000000000000

def z612 : W := mkw 0x0afffcf403d00d50 0x7ffffffe03f80ff8

def z613 : W := mkw 0x8100020960008225 0x80000001e0000007

def z614 : W := mkw 0x0cc8a0f4b682dfd6 0xefc0f0ffff87ffff

def z615 : W := mkw 0x0800000000000d50 0x0100000000000ff8

def z616 : W := mkw 0x80000100042c30ab 0x8000000000047007

def z617 : W := mkw 0x09fe48f463d18f54 0x20bcc0c0e3038e00

def z618 : W := mkw 0x0108005060008644 0x000000c0e0000e00

def z619 : W := mkw 0x200916ffd8000000 0x5a433ffffc000000

def z620 : W := mkw 0x22e3b4a69c08308a 0x004330261c987198

def z621 : W := mkw 0x12e7b50003ff6000 0x0443300003fff000

def z622 : W := mkw 0x8001170b08240021 0xdf433f3f1c640067

def z623 : W := mkw 0x1afee8f403d34d50 0x7dffc0fe03fb8ff8

def z624 : W := mkw 0x08fe49f403f50d50 0x7fffcffe03ff8ff8

def z625 : W := mkw 0x0000000020008204 0x8200c001e0078007

def z626 : W := mkw 0x0400000024009b86 0x8100000000000f87

def z627 : W := mkw 0x93ffff5b6ffff6ef 0xffffffffffffffff

def z628 : W := mkw 0x223a485440000000 0x003c000000000000

def z629 : W := mkw 0x1aefb4f403da6d50 0x7dff30fe03f87ff8

def z630 : W := mkw 0xa2fbffffd8240021 0xfffffffffc640067

def z631 : W := mkw 0x12f6e90003f74000 0x76bccf0003678000

def z632 : W := mkw 0x08e6000003d00d50 0x75ff000003f80ff8

def z633 : W := mkw 0x08fe4afd43d00d50 0x7fffcfffe3f80ff8

def z634 : W := mkw 0x811c4b5941650461 0x7dbc0fd803600e60

def z635 : W := mkw 0x2aefb4f69bd00d50 0x7dff30fe1ff80ff8

def z636 : W := mkw 0x00ea00f402800900 0x7dff00fe03800f80

def z637 : W := mkw 0x040000002682db86 0xef80c0c1e387ff87

def z638 : W := mkw 0x04c0a0a0b282cb04 0xef80c0c1e3078e07

def z639 : W := mkw 0x851c4bf9f5659fe7 0xffbccff9ff678fe7

def z640 : W := mkw 0x08c400a003d00d50 0x6dc000e003f80ff8

def z641 : W := mkw 0x00c000a006801982 0xefc030e11f847f87

def z642 : W := mkw 0x22fbfcf4d0000000 0x72ffffc0e0000000

def z643 : W := mkw 0x810c015021658665 0xfdbc00d803678e67

def z644 : W := mkw 0x22ebb4f698000000 0x78ff30fe1c000000

def z645 : W := mkw 0x00ee005003d00440 0x7dff00d803f80e60

def z646 : W := mkw 0x04c1b4a2be8afb8e 0xefc3f0e7ff9fff9f

def z647 : W := mkw 0x00011500002c2000 0x10030f0000780000

def z648 : W := mkw 0x85dcebf9f3e7cf65 0xffbccfd9e3678e67

def z649 : W := mkw 0x001c495001650440 0x7fbccfd803678e60

def z650 : W := mkw 0x22fbffffd82c2000 0x7efffffffcfc7000

def z651 : W := mkw 0x16e3b4a0b69afb86 0xefc3f0e1ff9fff87

def z652 : W := mkw 0x8401b70bbc2ef2af 0xdf43ff3ffcfff1ff

def z653 : W := mkw 0x851ceb59f567d6e7 0xffbcffd9ff67fe67

def z654 : W := mkw 0x80c1b70b0eae70ab 0xffc3ff3f1ffff1ff

def z655 : W := mkw 0x00c1b6ab98000000 0x7ac3fffffc000000

def z656 : W := mkw 0x323f5f5f497d2000 0x103f0f1e00780000

def z657 : W := mkw 0xb2ffffffdfff70ab 0xfffffffffffff1ff

def z658 : W := mkw 0x04c0a0a0b282cb04 0x66c0f0c0e387fe00

def z659 : W := mkw 0x0cee00f4b7d09fd6 0xfdff00fffff80fff

def z660 : W := mkw 0x9affffff0fff7dfb 0xffffffff1fffffff

def z661 : W := mkw 0x810c025961408665 0xfdbc00d9e3600e67

def z662 : W := mkw 0x040000a0b4009b86 0xef80c0e1ff078f87

def z663 : W := mkw 0x811c495061658665 0xa5bcc0c0e3678e67

def z664 : W := mkw 0x08e200a402900910 0x5d43003e00f801f8

def z665 : W := mkw 0x08e600a403d00d50 0x0543002603f80ff8

def z666 : W := mkw 0x882f175f0d7c34fb 0xdf7f3f3f1cfc71ff

def z667 : W := mkw 0x32f7ff0bdbff6000 0x76ffff01fffff000

def z668 : W := mkw 0x811d5f5b69658665 0xffffffffff678e67

def z669 : W := mkw 0x00c0a00002824000 0x0040300000807000

def z670 : W := mkw 0x811c4b5961658665 0x993c0fd9e0600e67

def z671 : W := mkw 0x0000000004001082 0x890000211c000187

def z672 : W := mkw 0x28ee02ffdbd00d50 0x7dff00fffff80ff8

def z673 : W := mkw 0x85c8a2f9f682dfe7 0xefc0f0f9ff87ffe7

def z674 : W := mkw 0x16f6e8a0b3d3cb04 0x20bcc0c0e3038e00

def z675 : W := mkw 0x8104010021658665 0xef80c0c1e3678e67

def z676 : W := mkw 0x08e314a60e98399a 0x004330261c987198

def z677 : W := mkw 0x200000a698000000 0x000000261c000000

def z678 : W := mkw 0xa3fffffffd6db6ef 0xffffffffffffffff

def z679 : W := mkw 0x0400a000b002c204 0x0000c000e0038000

def z680 : W := mkw 0x08ee00f403d00d50 0x30bf00de03780e78

def z681 : W := mkw 0x84c1b7abbeaefbaf 0xefc0ffe1ff87ff87

def z682 : W := mkw 0x080c00f401400d50 0x7dbc00fe03600ff8

def z683 : W := mkw 0x12d1fd0002af6000 0x66c0ff000387f000

def z684 : W := mkw 0x32fbffffd82f6000 0x7afffffffc07f000

def z685 : W := mkw 0x04c000a02682db86 0xedc000e00387ff87

def z686 : W := mkw 0x000115020c2c308a 0x56433f261cfc7198

def z687 : W := mkw 0x00cc00f003c00d40 0x7dfc00f803e00fe0

def z688 : W := mkw 0x81184b5960258225 0xfabccfd9e0078007

def z689 : W := mkw 0x0001170b082c2000 0x5e433f3f1cfc7000

def z690 : W := mkw 0xa33f5f5f49650461 0x103f0f1e00600060

def z691 : W := mkw 0x23fee8f4f1418644 0x20bcc0c0e3038e00

def z692 : W := mkw 0x810c035961658665 0x8d0000d9e3678e67

def z693 : W := mkw 0x04c0a0a096825982 0x6dc030e01f807f80

def z694 : W := mkw 0x8805170b0ffc3dfb 0xdf433f3f1ffc7fff

def z695 : W := mkw 0x8804010007fc3dfb 0x8500000003fc7fff

def z696 : W := mkw 0x3211ff0bd82f6000 0x0200ff01fc07f000

def z697 : W := mkw 0x81184a5960008665 0xfbbccfd9e0000e67

def z698 : W := mkw 0x22faeaffd8000000 0x28bcc0fffc000000

def z699 : W := mkw 0x0001160b0c08308a 0x5a433f3f1c987198

def z700 : W := mkw 0x280802ffd8000d50 0x090000fffc000ff8

def z701 : W := mkw 0x082e005401500450 0x7dbf00de03780e78

def z702 : W := mkw 0x0cc4a0a0b7d2dfd6 0xefc0f0e1ffffffff

def z703 : W := mkw 0x1005150003ff6000 0x56433f0003fff000

def z704 : W := mkw 0x8cefb7ffbffeffff 0xffffffffffffffff

def z705 : W := mkw 0x04c0a0002682db86 0xe7c0f0000387ff87

def z706 : W := mkw 0x23fffefff9418644 0x7affffffff038e00

def z707 : W := mkw 0x89f24bad62b58b35 0x8243cf27e09f819f

def z708 : W := mkw 0x22fbfeffd8082000 0x7afffffffc987000

def z709 : W := mkw 0x22fb5effd8000000 0x78ff0ffffc000000

def z710 : W := mkw 0x12f7fd020bff6000 0x76ffff261ffff000

def z711 : W := mkw 0x263b5e5f6e82db86 0x953f0f1e0387ff87

def z712 : W := mkw 0x1af7fda403ff6910 0x7fffff3e03fff1f8

def z713 : W := mkw 0x0c2ea054b552d6d6 0x923ff01ffc7ff07f

def z714 : W := mkw 0x88ef17ff0ffc3dfb 0xa2bc3fc11f047e07

def z715 : W := mkw 0xa2fae9f4d42c30ab 0xa5bcc0c0e0fc71ff

def z716 : W := mkw 0x02f7fd00016d2000 0x76ffff0003fff000

def z717 : W := mkw 0x22fbfeffd8000000 0x32bfffdffc000000

def z718 : W := mkw 0x00d5fd0003ef6000 0x76ffff0003fff000

def z719 : W := mkw 0x22fbfeffda800900 0x7affffffff000e00

def z720 : W := mkw 0x300c03ffdbff6000 0x0c0000fffffff000

def z721 : W := mkw 0x12f7fda003ff6900 0x76ffff2003fff180

def z722 : W := mkw 0x223b5e5fd8000000 0x103f0f1ffc000000

def z723 : W := mkw 0x16375da0b57dbb86 0x993f0fe1fc780f87

def z724 : W := mkw 0x12f7fd0003ff6000 0x32bfff00037ff000

def z725 : W := mkw 0x22fbfeffda824900 0x7fffffffff87ff80

def z726 : W := mkw 0x22fbfeffd8000900 0x7bfffffffc000f80

def z727 : W := mkw 0x1a19fdf4002f6d50 0x0b00fffe0007fff8

def z728 : W := mkw 0x891c4b5d61658675 0xffbccfdfe3678e7f

def z729 : W := mkw 0x22fbfeffd8000000 0x72ffffc1fc000000

def z730 : W := mkw 0x92f7fd0003ff6029 0x76ffff0003fff078

def z731 : W := mkw 0x9311ff0b6c2ff2af 0x8200ff01fc07f007

def z732 : W := mkw 0x08ee00f403d00d50 0xffff00ff03fc0fff

def z733 : W := mkw 0x12f7fd0003ff6000 0x72ffff000307f000

def z734 : W := mkw 0x2211fe0bd8000000 0x72bcff01fc000000

def z735 : W := mkw 0x00c0a0a0b282c204 0xefc0f0e1ff87fe07

def z736 : W := mkw 0x0014490001650000 0x76fcff0003e7f000

def z737 : W := mkw 0x22fbfeffd8000000 0x7effffffff078000

def z738 : W := mkw 0x22d9fefbd8000000 0x7afcfff9fc000000

def z739 : W := mkw 0x08ee00f403d00d50 0x7fff30fe03fc7ff8

def z740 : W := mkw 0x08ee00f403d00d50 0x197f00fe00f80ff8

def z741 : W := mkw 0x811c4b5961658665 0xabbccfd9e3078e67

def z742 : W := mkw 0x22f3feafd8000000 0x72ffff27fc000000

def z743 : W := mkw 0x0400a000b682db86 0xef80f0c1ff87ff87

def z744 : W := mkw 0x8001170b0c2c30ab 0x92433f3f1cfc71ff

def z745 : W := mkw 0x08ee00f403d00d50 0x7fffc0ffe3f80ff8

def z746 : W := mkw 0x12375d0003ff6000 0x567f3f0003fff000

def z747 : W := mkw 0x2219fe5bd8000000 0x123cff19fc000000

def z748 : W := mkw 0x3afbfeffda9a6910 0x7afffffffc987198

def z749 : W := mkw 0x811c4b5961658665 0xffbccfd9e3ff8fff

def z750 : W := mkw 0x02fbfcf490000000 0x7afffffffc000000

def z751 : W := mkw 0x81144b0961658225 0xffbccfc1e3678e07

def z752 : W := mkw 0x04c0a0a0b682db86 0xffc3f0e1ffffff87

def z753 : W := mkw 0x28ee00f4d3d00d50 0x7dff00fee3f80ff8

def z754 : W := mkw 0x16e3b4a29e9a798a 0x004330261c987198

def z755 : W := mkw 0x811c4b5961658665 0xefbccfc1e3078e07

def z756 : W := mkw 0x12f6e90003ff6000 0x76bccf0003fff000

def z757 : W := mkw 0x2a15fe0bdbd00d50 0x0700ff01fff80ff8

def z758 : W := mkw 0x0014490003e74000 0x76bccf0003e7f000

def z759 : W := mkw 0x811c4b5961658665 0xffbccfffe3678fff

def z760 : W := mkw 0x2ee3b4a69e925992 0x004330261c987198

def z761 : W := mkw 0x011c495061658644 0xffbccfc1e3678e07

def z762 : W := mkw 0x08eea0f493d00d50 0x7dffc0fee3f80ff8

def z763 : W := mkw 0x22fbfeffda800000 0x7effffffff800000

def z764 : W := mkw 0x36e3b4a69e9a7982 0x004330261c987180

def z765 : W := mkw 0x02f3fd0002ae6000 0x76ffff0003fff000

def z766 : W := mkw 0x84c1b7abbaaeeb2d 0x3083cfdee37b8e78

def z767 : W := mkw 0x85dcebf9d7e75de3 0x107c3f381ce071e0

def z768 : W := mkw 0x93ebb659629ae665 0x894330d9e0987e67

def z769 : W := mkw 0x223bfe5fd8000000 0x7abfffdffc000000

def z770 : W := mkw 0x00f75d0003fd2000 0x76ffff0003fff000

def z771 : W := mkw 0x22fbfeffd8000000 0x127fff3ffc000000

def z772 : W := mkw 0x04c0a0a0b682db86 0xffc0f0f9ffe7ffe7

def z773 : W := mkw 0xa50802fffc009fe7 0x890000fffc000fe7

def z774 : W := mkw 0x08ee00f403d00d50 0x30ff00fe03f80ff8

def z775 : W := mkw 0x0400a0a0b682db86 0x8f00f0e1ff87ff87

def z776 : W := mkw 0x811c4b5961658665 0xb9bccfd9e3638e67

def z777 : W := mkw 0x08e6000003d00d50 0x7dff003e03f80ff8

def z778 : W := mkw 0x22fbfeffda800900 0x7ffffffffff80ff8

def z779 : W := mkw 0x22fbfeffda900000 0x7afffffffc980000

def z780 : W := mkw 0x811d5f5b496d2469 0x103c0f1800600060

def z781 : W := mkw 0x00195e5b48000000 0x7abcffd9fc000000

def z782 : W := mkw 0x080c00f401400d50 0x7dff00fe03f80ff8

def z783 : W := mkw 0x00011500042c3082 0xdf433f3f1cfc71ff

def z784 : W := mkw 0x22fbfcf4d0000000 0x7affffe1fc000000

def z785 : W := mkw 0x81080259640096e7 0x890000f9fc000fe7

def z786 : W := mkw 0xa2fbfeffd8000021 0xfbfffffffc000067

def z787 : W := mkw 0x082e00f401500d50 0x5d7f00fe00f80ff8

def z788 : W := mkw 0x04c0a0a0b682db86 0xffc3f0ffff87ff87

def z789 : W := mkw 0x8001170b0c2c30ab 0x95433f3e1cfc71ff

def z790 : W := mkw 0x32f7fda493ff6000 0x76ffff0003fff000

def z791 : W := mkw 0x10c4a1a093ff6000 0x6ec0f0e1fffff000

def z792 : W := mkw 0x22f3fe0bd8000000 0x22bcff01fc000000

def z793 : W := mkw 0x811c4b5961658665 0xb2bccfd9e3678e67

def z794 : W := mkw 0x04c0a0a0b682db86 0xeac0f0e1ff07fe07

def z795 : W := mkw 0x92f6ea0b0fd350ab 0xa9bcc03f1f0381ff

def z796 : W := mkw 0x12f7fd0003ff6000 0x7effffc1e3fff000

def z797 : W := mkw 0x2233fe0bd8000000 0x123fff01fc000000

def z798 : W := mkw 0x81040100256596e7 0x8500000003e7ffe7

def z799 : W := mkw 0x12f7fda403ff6000 0x76ffff2603fff000

def z800 : W := mkw 0x1af7fd0003ff6d50 0x76ffff0003fffe00

def z801 : W := mkw 0xa611ff0bfc2ef2af 0x8200ff01fc07f007

def z802 : W := mkw 0x011c4a5961418644 0xffbccfd9e3078e07

def z803 : W := mkw 0x02f7fd0003e74000 0x76ffff0003e7f000

def z804 : W := mkw 0x811c4b5961658665 0xf6bccfc1e3678e07

def z805 : W := mkw 0x00155d00016d2000 0x76bcff000367f000

def z806 : W := mkw 0x92f7fd0003ff6021 0xf7ffff0003fff067

def z807 : W := mkw 0x8c04010027feffff 0x8500000003ffffff

def z808 : W := mkw 0x12f7fd020bff6008 0x76ffff0603fff018

def z809 : W := mkw 0x12f7fda003ff6900 0x7ffffffe03fffff8

def z810 : W := mkw 0x011d5c526d49b6ce 0x20fff0e6ff9bff98

def z811 : W := mkw 0x811c4b5961658665 0xffbfcfdfe37f8e7f

def z812 : W := mkw 0x2afbfeffda900d50 0x7bfffffffc980ff8

def z813 : W := mkw 0x8001170b0c2c30ab 0xffc33fff1ffc7fff

def z814 : W := mkw 0x12375d00017d2000 0x76ffff0003fff000

def z815 : W := mkw 0x26fbfeffda824900 0x7afffffffc000000

def z816 : W := mkw 0x223bfe5fd8000000 0x5a7fff3ffc000000

def z817 : W := mkw 0x04c0a0a0b682db86 0xe6c0f0c1ff87fe07

def z818 : W := mkw 0x2afbfeffd8000910 0x7afffffffc000198

def z819 : W := mkw 0x22fbfeffd8000000 0x22ffffe7fc000000

def z820 : W := mkw 0x04c0a0a0b682db86 0xef80f0c1ff07fe07

def z821 : W := mkw 0x2afbfeffd8000d50 0x7afffffffc000e00

def z822 : W := mkw 0x1404010027fff286 0x8400000003fff007

def z823 : W := mkw 0x2afbfeffd8000450 0x7afffffffc000078

def z824 : W := mkw 0x082e005403d00d50 0x5d7f003e03f80ff8

def z825 : W := mkw 0x12f7fc0003db6000 0x72ffff00039bf000

def z826 : W := mkw 0x22fbfeffd8000000 0x7afffffffc980198

def z827 : W := mkw 0x1af7fda403ff6910 0x76ffff0003fff000

def z828 : W := mkw 0x8001170b0c2c30ab 0x99433f3f1cf871ff

def z829 : W := mkw 0x9104010027fff6ef 0x8500000003ffffff

def z830 : W := mkw 0x80000309042410a3 0xdf433f3f1cfc71ff

def z831 : W := mkw 0xa3fbfeffd8000461 0x7afffffffc000060

def z832 : W := mkw 0x12f7fd0003ff6000 0x76ffff2603fff198

def z833 : W := mkw 0x00c000a026809b86 0xefc0f0e1ff87ff87

def z834 : W := mkw 0x12f7fda093ff6900 0x7fffffe1ffffff80

def z835 : W := mkw 0x04c0a0a0b402d286 0xefc0f0e1ff07fe07

def z836 : W := mkw 0x0ce2a0a4b692db96 0xffc3f0ffffffffff

def z837 : W := mkw 0x0018ea59d0000000 0x7abcffd9fc000000

def z838 : W := mkw 0x040000a0b4009b86 0xefc0f0e1ff87ff87

def z839 : W := mkw 0x2afbfeffd8100010 0x7afffffffc180018

def z840 : W := mkw 0x1237fd00017f6000 0x023cff000007f000

def z841 : W := mkw 0x8511ff0bfc2ff2af 0x8200ff01fc07f007

def z842 : W := mkw 0xa3e7b5a6b9658665 0x854330261f678e67

def z843 : W := mkw 0x32f7fd00d3ff6000 0x76ffff00e3fff000

def z844 : W := mkw 0x00184af9d0000000 0x7abccff9fc000000

def z845 : W := mkw 0x12f7fd0003ff6000 0x7effff211ffff000

def z846 : W := mkw 0x1233fd00002f6000 0x123fff000007f000

def z847 : W := mkw 0x02fbfe5b48000000 0x7afffffffc000000

def z848 : W := mkw 0x8001170b0c2c30ab 0xffc3fffffcfc71ff

def z849 : W := mkw 0x1c04010027ffffd6 0x8500000003ffffff

def z850 : W := mkw 0x12f3fd0002bf6000 0x72ffff00009ff000

def z851 : W := mkw 0x22fbfe5fd8000000 0x72ffff1ffc000000

def z852 : W := mkw 0x811c4b5961658665 0xffffcfffe3678e67

def z853 : W := mkw 0x06e3b4a096825982 0x004330201c807180

def z854 : W := mkw 0x811c4b5b69658665 0xffbccfffff678e67

def z855 : W := mkw 0x223b5effd8000000 0x7abfcffffc000000

def z856 : W := mkw 0x04c0a0a0b682db86 0xab80f0e1ff07ff87

def z857 : W := mkw 0x04c0a0a0b682db86 0xa2c0f0e1ff87ff87

def z858 : W := mkw 0x811c4b59616da66d 0xffbccfd9e37f8e7f

def z859 : W := mkw 0x1af7fda003ff6d50 0x7fffffe003fffff8

def z860 : W := mkw 0x02f3feab98000000 0x7afffffffc000000

def z861 : W := mkw 0x082e00f403d00d50 0x1d3f00fe03f80ff8

def z862 : W := mkw 0x8114490021658665 0xffbccfc1e3678e67

def z863 : W := mkw 0x1af7fd0003ff6910 0x76ffff0003fff198

def z864 : W := mkw 0x8108025b6c0096ef 0x890000d9fc000e67

def z865 : W := mkw 0x10155d0003ff6000 0x76ffff0003fff000

def z866 : W := mkw 0x81080259640096ef 0x890000d9e0000fff

def z867 : W := mkw 0x22fbfeffd8024000 0x7afffffffc07f000

def z868 : W := mkw 0x08ee00f403d00d50 0x157f003e03f80ff8

def z869 : W := mkw 0x80144b0921658225 0xffbccfd9e3678e67

def z870 : W := mkw 0x10e7150003ff6000 0x76ff3f0003fff000

def z871 : W := mkw 0x02f3fc0090000000 0x72ffff01fc000000

def z872 : W := mkw 0x32fbfeffd8182000 0x7afffffffc180000

def z873 : W := mkw 0x8504010027efffef 0x8500000003ffffff

def z874 : W := mkw 0x00c0a0002682d286 0xefc0f0e1ff87ff87

def z875 : W := mkw 0x22fbfeffd8000000 0x7ffffffffc600060

def z876 : W := mkw 0x18ee00f403d34d50 0x7dff00fe03fb8ff8

def z877 : W := mkw 0x0400a000b402d286 0xefc0f0e1ff87ff87

def z878 : W := mkw 0x22fbfeffda800900 0x7afffffffc800180

def z879 : W := mkw 0x06f3fca0b4009b86 0xfbffffe1fc000f87

def z880 : W := mkw 0x26e3b4a69e8a798a 0x004330261c987198

def z881 : W := mkw 0x00cc00f003c00d40 0x7dff00fe03f80ff8

def z882 : W := mkw 0x12f7fd0003ff6000 0x76bcff000367f000

def z883 : W := mkw 0x04c0a0a0b682db86 0xa780f0c1ff87ff87

def z884 : W := mkw 0x12f7fc0003d34000 0x76ffff000387f000

def z885 : W := mkw 0x12f7fd0003ff6000 0x7fffff1803fff060

def z886 : W := mkw 0x20195effd8000000 0x7afffffffc000000

def z887 : W := mkw 0x10d4e90003ff6000 0x76fcff0003fff000

def z888 : W := mkw 0x1ee3b4a4969a7992 0x004330261c987198

def z889 : W := mkw 0x08eea0f403d00d50 0x7ffff0fe03f80ff8

def z890 : W := mkw 0x12f7fd0003ff6000 0x7fffff2003fff180

def z891 : W := mkw 0x2afbfeffda900910 0x7afffffffc000000

def z892 : W := mkw 0x1237fd00017f6000 0x76bfff00037ff000

def z893 : W := mkw 0x0cc0a0a4b682db96 0xefc0f0e7ff87ff9f

def z894 : W := mkw 0x12f7fd00016f6000 0x76ffff000367f000

def z895 : W := mkw 0x20184a5bd8000000 0x7abccfd9fc000000

def z896 : W := mkw 0x811c4b5961658665 0xa7bccfc1e3678e67

def z897 : W := mkw 0x22fbfeffd8000000 0x7abcffd9fc000000

def z898 : W := mkw 0x22fbfeffda824000 0x7afffffffc807000

def z899 : W := mkw 0x02fbfef9d0000000 0x7afffff9fc000000

def z900 : W := mkw 0x223b5effd8000000 0x5a7f3ffffc000000

def z901 : W := mkw 0x082e005401500d50 0x113f001e00780ff8

def z902 : W := mkw 0x12f3fd00002f6000 0x22bcff000007f000

def z903 : W := mkw 0x81184a5960008665 0xffbccfd9e3078e67

def z904 : W := mkw 0x0000000024009286 0xef80f0c1ff07fe07

def z905 : W := mkw 0x08ee00f403d24d50 0x7dff00fe03fffff8

def z906 : W := mkw 0x12f7fd0003ff6000 0x34bfcf0003fff000

def z907 : W := mkw 0x811c4b5961658665 0xb5bccfd8e3678e67

def z908 : W := mkw 0x811c4b5961658665 0xfffccff9e3e78fe7

def z909 : W := mkw 0x22f3feabd8000000 0x7affffe1fc000000

def z910 : W := mkw 0x12f7fd0003ff6900 0x77ffff0003ffff80

def z911 : W := mkw 0x12d5fd0003ef6000 0x76fcff0003e7f000

def z912 : W := mkw 0x1215fd0003ff6000 0x76bcff0003fff000

def z913 : W := mkw 0x08ee00f403d00d50 0x7fff30ff1ff80ff8

def z914 : W := mkw 0x20fa4affd8000000 0x7affcffffc000000

def z915 : W := mkw 0x1efee8f4b3d3cf54 0x20bcc0c0e3038e00

def z916 : W := mkw 0x12f7fd0003ff6000 0x147f3f0003fff000

def z917 : W := mkw 0x1215fd00016f6000 0x22bcff000307f000

def z918 : W := mkw 0x12f7fda003ff6000 0x7effffe003fff000

def z919 : W := mkw 0x00f6e90003f74000 0x76ffff0003fff000

def z920 : W := mkw 0x12f75d0003ff6000 0x74ff0f0003fff000

def z921 : W := mkw 0x22fbfeffd8000000 0x38bfcffffc000000

def z922 : W := mkw 0x2219fe5bd8000000 0x22bcffc1fc000000

def z923 : W := mkw 0x06f3fc002682db86 0xf7ffff000387ff87

def z924 : W := mkw 0x12f7fd0003ff6440 0x77ffff0003fffe60

def z925 : W := mkw 0x22fbfeffd8082008 0x7afffffffc180018

def z926 : W := mkw 0x08eea0f493d00d50 0x7dff30fe1ff80ff8

def z927 : W := mkw 0x04c0a0a0b682db86 0xefc0f0e1ffffffff

def z928 : W := mkw 0x22fbfeffd8000000 0x7fffffffff000e00

def z929 : W := mkw 0x933f5f5b497d2469 0x103f0f1e00780078

def z930 : W := mkw 0x9504010027ffffe7 0x8500000003ffffe7

def z931 : W := mkw 0x22fbfeffd8000000 0x7afffffffc780078

def z932 : W := mkw 0x1af7fda403ff6910 0x7fffffe603ffff98

def z933 : W := mkw 0x12f7fda003ff6900 0x76ffffc003fffe00

def z934 : W := mkw 0x3af7fda69bff6910 0x76ffff261ffff198

def z935 : W := mkw 0x12f6e90003f74000 0x76fcff0003e7f000

def z936 : W := mkw 0x040802f9f4009b86 0x890000f9fc000f87

def z937 : W := mkw 0x08eea0f493d24d50 0x7ffff0fffffffff8

def z938 : W := mkw 0x80184b5960248225 0xffbccfd9e3678e67

def z939 : W := mkw 0x12f7fd0003ff6000 0x76ffff1e03fff078

def z940 : W := mkw 0x8508025964009fe7 0x890000d9e0000fe7

def z941 : W := mkw 0x16f7fda093ff6900 0x76ffff0003fff000

def z942 : W := mkw 0x893f5f5f497d2479 0x103f0f1e00780078

def z943 : W := mkw 0x8c0802ffbc009fff 0x890000fffc000fff

def z944 : W := mkw 0x8d04010027f7dff7 0x8500000003ffffff

def z945 : W := mkw 0x00ea00f402800900 0x7dff00fe03f80ff8

def z946 : W := mkw 0x20184affd8000000 0x183c0ffffc000000

def z947 : W := mkw 0x04c0a000b682d286 0xefc0f0c1ff87fe07

def z948 : W := mkw 0x22faeaffd8000000 0x7abccffffc000000

def z949 : W := mkw 0x22fbfeffd8000000 0x187f3ffffc000000

def z950 : W := mkw 0x12f7fd0003ff6000 0x22ffff00039ff000

def z951 : W := mkw 0x0ce3b4a69e9a799a 0x004330261c987198

def z952 : W := mkw 0x811c4b5961658665 0xffffcfd9e3ff8e67

def z953 : W := mkw 0x1237fd00017f6000 0x567fff0000fff000

def z954 : W := mkw 0xa40802fffc009baf 0x890000fffc000fff

def z955 : W := mkw 0x81040100256db6ef 0x850000000367fe67

def z956 : W := mkw 0x04c0a0a0b682db86 0xefc0f0ffff87ffff

def z957 : W := mkw 0x00d0e8a090000000 0x7afcffe1fc000000

def z958 : W := mkw 0x811c4b5961658665 0xfffcfff9ff678e67

def z959 : W := mkw 0x93f7fd0003ff6461 0x76ffff0003fff060

def z960 : W := mkw 0x22fbfcf6d8000000 0x72ffffe6fc000000

def z961 : W := mkw 0x12f7fd0093ff6000 0x76ffff01fffff000

def z962 : W := mkw 0x00ee005003d00440 0x7dff00fe03f80ff8

def z963 : W := mkw 0x082e005403d00d50 0x7dbf00de03f80ff8

def z964 : W := mkw 0x00faeafdd0000000 0x7afffffffc000000

def z965 : W := mkw 0x811c4b5961658665 0xfffcffd9e3e7fe67

def z966 : W := mkw 0x12f7fd0003ff6000 0xffffff0103fff007

def z967 : W := mkw 0x20eb16ffd8000000 0x7aff3ffffc000000

def z968 : W := mkw 0xa33f5f5f496d2469 0x103f0f1e00780078

def z969 : W := mkw 0x2aeea0f493d00d50 0x7dff00fe03f80ff8

def z970 : W := mkw 0x20d8eaffd8000000 0x7afcfffffc000000

def z971 : W := mkw 0x00144900016d2000 0x76bccf0003fff000

def z972 : W := mkw 0x2efee8f4f3d2cf54 0x20bcc0c0e3038e00

def z973 : W := mkw 0x26e2a0a4b682db86 0xefc0f0e1ff87ff87

def z974 : W := mkw 0x8504010025659fe7 0x8500000003678fe7

def z975 : W := mkw 0x32fbfeffd80a6000 0x7afffffffc007000

def z976 : W := mkw 0x08eea0f403d24d50 0x7dff30fe03f87ff8

def z977 : W := mkw 0x32fbfeffda9a6000 0x7effffffff9ff000

def z978 : W := mkw 0x22fbfeffd8000000 0xfffffffffc040007

def z979 : W := mkw 0x22faeafdd0000000 0x7afcfff9fc000000

def z980 : W := mkw 0x00ee00f401400440 0x7dff00fe03f80ff8

def z981 : W := mkw 0x1af7fd0003ff6450 0x76ffff0003fff078

def z982 : W := mkw 0x10144900016f6000 0x76bccf000367f000

def z983 : W := mkw 0x811c4a5961418665 0xfbbccfd9e3038e67

def z984 : W := mkw 0x04e2a0a4b682db86 0xefc3f0e7ff87ff87

def z985 : W := mkw 0x1aeea0f403d24d50 0x7dff00fe03f80ff8

def z986 : W := mkw 0x22fbfeffd8000000 0x7efffffffc847000

def z987 : W := mkw 0x890802ff6c009fff 0x890000fffc000fff

def z988 : W := mkw 0x1af7fd0003ff6d50 0x7fffff3e03fffff8

def z989 : W := mkw 0x04e2a0a0b682db86 0xfffff0e1ff87ff87

def z990 : W := mkw 0x22fbfeffd8000000 0x6afcffe1fc000000

def z991 : W := mkw 0x0dfee8f4f3d3cf54 0x20bcc0c0e3038e00

def z992 : W := mkw 0x2afbfeffd8000d50 0x7ffffffffcf80ff8

def z993 : W := mkw 0x08ee00f401500d50 0x79ff00fe00780ff8

def z994 : W := mkw 0x81040100256596ef 0x8500000003678fff

def z995 : W := mkw 0x080c005003d00d50 0x7dff00fe03f80ff8

def z996 : W := mkw 0x22fbfe5bd8000000 0x7affffd9fc000000

def z997 : W := mkw 0x02f7fc0003d24000 0x76ffff0003fff000

def z998 : W := mkw 0x32f7fd029bff6000 0x76ffff001ffff000

def z999 : W := mkw 0x223bfe5fd8000000 0x023cff01fc000000

def z1000 : W := mkw 0x1014490003ff6000 0x143c0f0003fff000

def z1001 : W := mkw 0x12f3fd00002f6000 0x76ffff0000fff000

def z1002 : W := mkw 0x00c0a0a0b4009286 0xefc0f0e1ff87ff87

def z1003 : W := mkw 0x81184b5960258225 0xffbccfd9e3078e07

def z1004 : W := mkw 0x001c4a5961408644 0xffbccfd9e3678e67

def z1005 : W := mkw 0x811c4b5b6965866d 0xffbccfdfe3678e7f

def z1006 : W := mkw 0x04e2a0a0b692db86 0xefc3f0e1ff9fff87

def z1007 : W := mkw 0x16e2a0a0b692db86 0xefc0f0e1ff87ff87

def z1008 : W := mkw 0xa2fbfeffd8000029 0x7afffffffc000078

def z1009 : W := mkw 0x911c4b59617da665 0xffbccfd9e37f8e67

def z1010 : W := mkw 0x12f7fd0003ff6000 0x30ffff0003fbf000

def z1011 : W := mkw 0x00e7b50003fe6000 0x76ffff0003fff000

def z1012 : W := mkw 0x1215fd00016f6000 0x76ffff0003fff000

def z1013 : W := mkw 0x22f3fe0bd8000000 0x7affff3ffc000000

def z1014 : W := mkw 0xb33f5f5f497d2461 0x103f0f1e00780060

def z1015 : W := mkw 0x0400a000b402d286 0xa280f0c1ff07fe07

def z1016 : W := mkw 0x10f6490003ff6000 0x76ffcf0003fff000

def z1017 : W := mkw 0x00fb5eff48000000 0x7afffffffc000000

def z1018 : W := mkw 0x2219feffd8000000 0x7abcfffffc000000

def z1019 : W := mkw 0x12f7fda093ff6000 0x76ffffc0e3fff000

def z1020 : W := mkw 0x811c495061658665 0xf7bccfc0e3678e67

def z1021 : W := mkw 0x08eea0f403d24d50 0x7dffc0fe03fb8ff8

def z1022 : W := mkw 0x8001170b0c2c30ab 0xffc3ff3f1ffff1ff

def z1023 : W := mkw 0x2219fe5bd8000000 0x7afffffffc000000

def z1024 : W := mkw 0x22fbfeffd8000000 0x7bfffffffc0001f8

def z1025 : W := mkw 0x891c4b5961758675 0xffbccfd9e37f8e7f

def z1026 : W := mkw 0x223b5e5f48000000 0x7afffffffc000000

def z1027 : W := mkw 0x22fbfeffd8000440 0x7bfffffffc000e60

def z1028 : W := mkw 0x20c8a2ffda824000 0x6ec0f0ffff87f000

def z1029 : W := mkw 0x1237fd0003ff6000 0x163fff0003fff000

def z1030 : W := mkw 0x12f7fd00017f6000 0x72ffff00007ff000

def z1031 : W := mkw 0x12f7fd0003ff6000 0x7effff3e03fff000

def z1032 : W := mkw 0x12375d0003ff6000 0x76bfcf0003fff000

def z1033 : W := mkw 0x85080259f40096e7 0x890000d9fc000e67

def z1034 : W := mkw 0x32f7fd060bff6000 0x76ffff0603fff000

def z1035 : W := mkw 0x04c0a0a0b682db86 0xefc3f0e7ff9fff9f

def z1036 : W := mkw 0x1af7fd0403ff6010 0x76ffff0603fff018

def z1037 : W := mkw 0x22fbfeffda824000 0x7affffffff038000

def z1038 : W := mkw 0x1215fd00016f6000 0x123cff000067f000

def z1039 : W := mkw 0x0400a0a0b402db86 0xef80f0e1ff07ff87

def z1040 : W := mkw 0x1af7fda403ff6d50 0x77ffff2603fffff8

def z1041 : W := mkw 0x32fbfeffda924000 0x7afffffffc000000

def z1042 : W := mkw 0x0404010027e7db86 0x8500000003e7ff87

def z1043 : W := mkw 0x0014e90001674000 0x76bcff000367f000

def z1044 : W := mkw 0x12375d00017f6000 0x103f0f00007ff000

def z1045 : W := mkw 0x2afbfeffda900910 0x7ffffffffcf801f8

def z1046 : W := mkw 0x240802fffc009286 0x880000fffc000007

def z1047 : W := mkw 0x08ee00f403d00d50 0x39bf00fe03780ff8

def z1048 : W := mkw 0x800c035921648665 0xffbccfd9e3678e67

def z1049 : W := mkw 0x082e005401500450 0x7dff00fe03f80ff8

def z1050 : W := mkw 0x850401002567d6e7 0x850000000367fe67

def z1051 : W := mkw 0x001c4b5961658204 0xffbccfd9e3678e07

def z1052 : W := mkw 0x00ebb6ff98000000 0x7afffffffc000000

def z1053 : W := mkw 0x12f7fda093ff6000 0x76ffff201ffff000

def z1054 : W := mkw 0x08ea00f400000d50 0x7dff00fe00f80ff8

def z1055 : W := mkw 0x22fbfeffd8000000 0x7ffffffffc800180

def z1056 : W := mkw 0x08ee005403d00d50 0x75ff001e03f80ff8

def z1057 : W := mkw 0x22fbfeffd8000000 0x7efffffffcf80000

def z1058 : W := mkw 0x811c4b5961658665 0xfabccfd9e3078e07

def z1059 : W := mkw 0x850802fbfc009fef 0x890000fffc000fff

def z1060 : W := mkw 0x12f7fd0003ff6000 0x77ffff0003fff1f8

def z1061 : W := mkw 0x0cc0a0a0b692db96 0xefc0f0e1ff9fff9f

def z1062 : W := mkw 0x22fbfeffd8000000 0x2abcfffffc000000

def z1063 : W := mkw 0xa10802fffc0096ef 0x890000fffc000fff

def z1064 : W := mkw 0x00d9fefbd8000000 0x7afffffffc000000

def z1065 : W := mkw 0x12f7fd0003ff6000 0x26bcff0003fff000

def z1066 : W := mkw 0x12f7fd0003ff6000 0x7fffffc003fffe00

def z1067 : W := mkw 0x12f7fd0003ff6000 0x127fff0000fff000

def z1068 : W := mkw 0x2c0802fffc009fd6 0x890000fffc000fff

def z1069 : W := mkw 0x0001160b0c001082 0xdf433f3f1cfc71ff

def z1070 : W := mkw 0x00e600a003d00900 0x7dff00fe03f80ff8

def z1071 : W := mkw 0x08ee00f493d00d50 0x7dff00fffff80ff8

def z1072 : W := mkw 0x12f3fc00029a6000 0x76ffff00039ff000

def z1073 : W := mkw 0x0010480020008204 0xffbccfc1e3078e07

def z1074 : W := mkw 0x0ceea0f493d24d50 0x7dff00fe03f80ff8

def z1075 : W := mkw 0x223bfeffd8000000 0x1a3ffffffc000000

def z1076 : W := mkw 0x9611ff0bbc2ff2af 0x8200ff01fc07f007

def z1077 : W := mkw 0x00184a5940000000 0x7afcfff9fc000000

def z1078 : W := mkw 0x00d0e80002824000 0x76fcff000387f000

def z1079 : W := mkw 0x2afbfeffda800d50 0x7fffffffff800ff8

def z1080 : W := mkw 0x12f7fd0003ff6000 0x66fcff000387f000

def z1081 : W := mkw 0x8d0802fdf4009ff7 0x890000fffc000fff

def z1082 : W := mkw 0x32fbfeffd8034000 0x7afffffffc038000

def z1083 : W := mkw 0x02f3fc0000024000 0x72ffff000007f000

def z1084 : W := mkw 0x00184a5b48000000 0x7abccffffc000000

def z1085 : W := mkw 0x12f3fd0002af6000 0x76ffff000387f000

def z1086 : W := mkw 0x08ee00f403d00d50 0x7fffc0fe03ff8ff8

def z1087 : W := mkw 0x9404010027fffbaf 0x8500000003ffffff

def z1088 : W := mkw 0x2afbfeffda900910 0x7fffffffff980f98

def z1089 : W := mkw 0x082e00f401500d50 0x7dbf00fe03780ff8

def z1090 : W := mkw 0x22f3fca698000000 0x7affffe7fc000000

def z1091 : W := mkw 0x08ee00f403d00d50 0x35bf00de03f80ff8

def z1092 : W := mkw 0xa11c4b5f69658665 0xffbccfdfe3678e67

def z1093 : W := mkw 0x22fbfeffd8000000 0x30fffffefc000000

def z1094 : W := mkw 0x001c495021658644 0xffbccfd9e3678e67

def z1095 : W := mkw 0x32f7fda69bff6000 0x7effffe7fffff000

def z1096 : W := mkw 0x811c4b59616da665 0xffbccfd9e3fffe67

def z1097 : W := mkw 0xa311ff0bfc2db2af 0x8200ff01fc07f007

def z1098 : W := mkw 0x040000002682db86 0xefc0f0e1ff87ff87

def z1099 : W := mkw 0x1211fd00002f6000 0x72bcff000007f000

def z1100 : W := mkw 0x8904010027fdbfff 0x8500000003ffffff

def z1101 : W := mkw 0x0ce2a0a4b692db96 0xefc0f0e1ff87ff87

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z8,z6]),(0,[z9,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z10,z4,z5,z6]),(0,[z0,z2,z3,z4,z11,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z12]),(0,[z0,z2,z3,z4,z5,z6,z13]),(0,[z14,z0,z2,z3,z4,z5,z6])],[(0,[z15,z0,z2,z3,z4,z5,z6]),(0,[z16,z17,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z18,z19,z5,z6]),(1,[z20,z2,z3,z4,z5,z21]),(0,[z0,z2,z3,z4,z5,z22,z6])],[(0,[z0,z2,z23,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z24,z6]),(0,[z0,z2,z3,z4,z5,z6,z25])],[(1,[z0,z2,z3,z26,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z27]),(0,[z0,z2,z3,z28,z29,z5,z6]),(0,[z0,z2,z3,z4,z30,z5,z6]),(0,[z31,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z32]),(0,[z0,z2,z3,z4,z33,z5,z6]),(0,[z34,z0,z2,z3,z35,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z36]),(0,[z16,z0,z2,z37,z3,z5,z6]),(0,[z0,z2,z3,z29,z38,z5,z6]),(0,[z0,z2,z3,z39,z38,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z40])],[(1,[z0,z2,z3,z5,z6,z41]),(0,[z42,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z43,z5,z6]),(0,[z0,z44,z2,z3,z4,z5,z6]),(0,[z45,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z46,z5,z47,z6]),(0,[z48,z0,z2,z3,z4,z5,z6]),(0,[z0,z49,z2,z3,z4,z5,z6])],[(0,[z50,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z51,z4,z46,z5,z6]),(0,[z52,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z53,z3,z4,z5,z54])]],
   [[(0,[z0,z55,z1,z3,z4,z5,z6]),(0,[z0,z2,z37,z51,z4,z5,z6]),(0,[z16,z56,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z57])],[(0,[z0,z2,z58,z3,z4,z5,z6]),(0,[z0,z59,z2,z3,z4,z5,z6]),(1,[z17,z2,z3,z29,z5,z6]),(0,[z60,z2,z3,z4,z5,z6,z61]),(0,[z0,z62,z2,z3,z4,z6,z63]),(0,[z0,z2,z3,z4,z5,z6,z64]),(0,[z0,z2,z3,z4,z65,z5,z6]),(0,[z0,z2,z37,z4,z5,z47,z6]),(0,[z66,z0,z2,z3,z4,z5,z6]),(0,[z67,z0,z2,z3,z4,z5,z6]),(0,[z68,z0,z2,z3,z5,z69,z6])],[(0,[z56,z70,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z71,z6]),(0,[z0,z2,z3,z4,z5,z6,z72]),(0,[z0,z73,z2,z3,z4,z5,z6])],[(0,[z74,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z75,z5,z6]),(0,[z0,z2,z3,z76,z4,z5,z6]),(0,[z0,z77,z2,z3,z4,z5,z6])],[(0,[z0,z78,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z79,z5,z6]),(0,[z60,z20,z2,z3,z4,z5,z6]),(1,[z60,z2,z3,z4,z5,z61]),(0,[z0,z2,z80,z3,z4,z5,z6]),(0,[z81,z0,z2,z3,z5,z6,z82])],[(1,[z83,z2,z3,z4,z6,z84]),(1,[z0,z2,z3,z85,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z86]),(0,[z87,z0,z2,z3,z4,z5,z6]),(0,[z88,z0,z2,z3,z4,z5,z6]),(0,[z0,z89,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z90])],[(0,[z60,z2,z91,z3,z4,z5,z6]),(0,[z20,z0,z2,z3,z35,z4,z5]),(0,[z92,z0,z3,z4,z5,z6,z82])]],
   [[(0,[z93,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z94])],[(0,[z83,z60,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z95,z5,z21,z6]),(0,[z96,z0,z2,z3,z4,z5,z6])],[(0,[z97,z0,z2,z3,z4,z5,z6]),(0,[z98,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z99,z5,z6]),(0,[z0,z2,z3,z4,z100,z5,z6])],[(0,[z0,z2,z3,z4,z5,z101,z6]),(0,[z102,z0,z2,z3,z4,z103,z6]),(0,[z0,z2,z3,z104,z4,z5,z6]),(0,[z105,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z106,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z84]),(0,[z2,z3,z4,z5,z21,z6,z61]),(0,[z34,z20,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z107])],[(0,[z0,z2,z3,z4,z108,z5,z6]),(0,[z60,z2,z3,z4,z95,z5,z6]),(0,[z0,z2,z3,z109,z4,z5,z6]),(0,[z0,z2,z3,z4,z110,z5,z6])],[(0,[z111,z0,z2,z3,z4,z5,z6]),(0,[z16,z0,z2,z3,z19,z5,z6]),(0,[z0,z2,z3,z4,z5,z112,z6]),(0,[z0,z113,z2,z3,z38,z5,z6]),(0,[z0,z2,z3,z4,z5,z114,z6]),(0,[z0,z115,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z116]),(0,[z0,z2,z3,z4,z5,z6,z117]),(0,[z2,z3,z4,z5,z6,z118,z82])],[(0,[z119,z0,z2,z120,z4,z5,z6]),(0,[z121,z0,z122,z3,z4,z5,z6]),(0,[z123,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z124,z4,z5,z6]),(0,[z125,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z126]),(0,[z127,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z128,z4,z5,z6]),(0,[z34,z0,z2,z3,z129,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z130])],[(0,[z131,z0,z2,z3,z4,z5,z6])],[(0,[z132,z0,z2,z3,z4,z5,z6]),(0,[z133,z0,z2,z3,z4,z5,z6]),(0,[z134,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z41]),(0,[z56,z0,z2,z3,z4,z5,z6]),(0,[z135,z0,z2,z3,z4,z5,z6]),(0,[z81,z0,z2,z3,z4,z5,z6])],[(0,[z121,z2,z3,z51,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z136,z6]),(0,[z83,z2,z3,z4,z5,z21,z6]),(0,[z137,z0,z113,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z138]),(0,[z0,z2,z3,z4,z5,z139,z6]),(0,[z140,z0,z2,z3,z4,z5,z6]),(0,[z141,z0,z2,z3,z4,z5,z6]),(0,[z142,z0,z2,z3,z4,z6,z82])],[(0,[z0,z55,z2,z3,z143,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z144]),(0,[z102,z0,z3,z4,z5,z6,z63]),(0,[z56,z0,z2,z4,z46,z5,z6])],[(0,[z145,z0,z2,z3,z4,z5,z6]),(0,[z137,z0,z2,z3,z38,z5,z6]),(0,[z0,z2,z146,z3,z4,z5,z6])],[(0,[z0,z113,z2,z147,z4,z5,z6]),(0,[z0,z2,z3,z4,z148,z5,z6]),(0,[z149,z0,z2,z3,z4,z5,z54]),(0,[z150,z0,z2,z3,z4,z5,z6])],[(0,[z0,z1,z3,z151,z4,z5,z6]),(1,[z152,z0,z151,z4,z5,z6]),(0,[z0,z2,z151,z28,z4,z5,z6]),(0,[z0,z2,z3,z153,z4,z5,z6]),(0,[z0,z2,z3,z4,z154,z5,z6]),(0,[z0,z2,z155,z3,z4,z5,z6])]],
   [[(0,[z156,z0,z2,z3,z4,z5,z6]),(0,[z56,z0,z2,z3,z18,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z157]),(0,[z0,z3,z4,z103,z5,z158,z6]),(0,[z0,z159,z2,z3,z4,z5,z158]),(0,[z160,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z161]),(0,[z132,z2,z3,z4,z5,z21,z6]),(0,[z0,z2,z3,z4,z5,z6,z162]),(0,[z0,z163,z2,z3,z4,z5,z6]),(0,[z164,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z165,z4,z5,z6]),(0,[z0,z55,z2,z166,z4,z5,z6]),(0,[z0,z2,z28,z4,z46,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z167]),(0,[z0,z168,z2,z3,z4,z5,z6]),(0,[z142,z0,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z169,z6]),(1,[z0,z2,z4,z5,z170,z6])],[(0,[z171,z0,z2,z3,z4,z5,z6]),(0,[z172,z0,z2,z3,z4,z5,z6]),(0,[z173,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z174,z5,z6]),(1,[z149,z0,z2,z4,z5,z54])],[(0,[z0,z2,z37,z3,z4,z5,z6]),(0,[z0,z2,z53,z3,z175,z5,z6]),(0,[z176,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z177,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z178,z6]),(0,[z0,z2,z3,z4,z5,z6,z179]),(0,[z0,z2,z3,z4,z180,z5,z6]),(0,[z0,z2,z3,z4,z181,z5,z6])],[(0,[z20,z0,z2,z53,z3,z4,z5]),(0,[z0,z2,z151,z4,z5,z47,z6]),(0,[z182,z0,z2,z3,z4,z5,z6]),(0,[z183,z0,z2,z3,z4,z5,z6]),(0,[z0,z159,z3,z4,z5,z158,z6]),(0,[z184,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z185,z5,z6]),(0,[z0,z2,z186,z3,z4,z5,z6])],[(0,[z187,z0,z2,z3,z4,z5,z6]),(1,[z188,z0,z2,z4,z5,z6]),(1,[z0,z2,z4,z5,z6,z189]),(0,[z0,z2,z3,z190,z4,z5,z6])]],
   [[(0,[z121,z0,z191,z3,z4,z5,z6]),(0,[z70,z2,z192,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z193]),(0,[z34,z0,z2,z3,z4,z5,z6]),(0,[z194,z0,z2,z3,z4,z195,z6])],[(0,[z0,z2,z3,z196,z4,z5,z6]),(0,[z0,z2,z3,z4,z197,z5,z6]),(0,[z0,z2,z3,z4,z198,z5,z6]),(0,[z0,z55,z2,z151,z4,z5,z6]),(0,[z0,z2,z199,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z200,z6])],[(0,[z0,z2,z201,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z202]),(0,[z0,z2,z37,z3,z18,z5,z6]),(0,[z203,z0,z2,z3,z4,z5,z6]),(0,[z204,z0,z2,z3,z4,z5,z6])],[(0,[z205,z0,z2,z3,z4,z5,z6]),(0,[z0,z206,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z118])],[(0,[z0,z2,z3,z18,z29,z5,z6]),(0,[z207,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z120,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z208,z5,z6]),(0,[z0,z2,z3,z209,z4,z5,z6])],[(0,[z70,z0,z2,z4,z5,z47,z6]),(0,[z0,z2,z3,z4,z5,z6,z210]),(0,[z34,z0,z2,z3,z18,z5,z6]),(0,[z0,z2,z3,z211,z4,z5,z6]),(0,[z149,z0,z2,z4,z185,z5,z6]),(0,[z0,z2,z3,z212,z4,z5,z6]),(0,[z0,z2,z3,z213,z4,z5,z6])],[(0,[z214,z0,z2,z3,z4,z5,z6]),(0,[z7,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z215]),(0,[z216,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z217])]],
   [[(0,[z218,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z219,z5,z6])],[(0,[z220,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z5,z69,z6])],[(0,[z221,z0,z2,z3,z4,z5,z6]),(0,[z222,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z223,z5,z6]),(0,[z0,z2,z3,z224,z4,z5,z6]),(0,[z0,z2,z225,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z226])],[(0,[z0,z2,z191,z3,z4,z5,z6]),(1,[z227,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z228,z6]),(0,[z0,z229,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z230,z4,z5,z6]),(0,[z0,z2,z3,z75,z51,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z231]),(0,[z0,z2,z3,z4,z5,z6,z232]),(1,[z0,z2,z53,z4,z5,z47])],[(0,[z83,z0,z2,z3,z4,z95,z6]),(0,[z0,z166,z3,z151,z4,z5,z6]),(0,[z0,z113,z2,z233,z4,z5,z6]),(0,[z0,z2,z3,z234,z4,z5,z6]),(1,[z0,z2,z3,z235,z5,z6]),(0,[z236,z0,z2,z3,z4,z5,z6])],[(0,[z237,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z238,z19,z5]),(0,[z239,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z240]),(0,[z241,z0,z2,z3,z4,z5,z6]),(0,[z102,z242,z2,z3,z4,z5,z6]),(1,[z2,z243,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z170,z6,z82])],[(0,[z121,z0,z2,z3,z244,z5,z6]),(0,[z245,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z246,z3,z4,z5,z6])]],
   [[(0,[z247,z0,z2,z3,z4,z5,z6]),(0,[z248,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z249,z5,z6]),(0,[z0,z2,z53,z3,z4,z5,z47]),(1,[z0,z2,z250,z4,z5,z6])],[(0,[z152,z0,z2,z166,z4,z5,z6]),(0,[z251,z0,z2,z3,z4,z5,z6]),(0,[z252,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z253])],[(0,[z0,z2,z3,z4,z254,z5,z6]),(0,[z255,z0,z2,z3,z4,z5,z6])],[(0,[z1,z2,z91,z3,z4,z5,z6]),(0,[z0,z55,z91,z3,z4,z5,z6]),(0,[z132,z2,z3,z4,z5,z6,z84]),(0,[z60,z0,z2,z3,z4,z5,z6]),(0,[z227,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z256,z4,z5,z6]),(0,[z0,z257,z2,z3,z4,z5,z6]),(1,[z137,z0,z3,z38,z5,z6]),(0,[z258,z0,z2,z3,z4,z5,z6]),(1,[z66,z0,z2,z4,z6,z259]),(0,[z0,z2,z3,z4,z5,z6,z260])],[(0,[z261,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z233,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z262])],[(0,[z0,z2,z3,z4,z5,z263,z6]),(0,[z264,z0,z2,z3,z4,z5,z6]),(0,[z265,z0,z2,z4,z5,z6,z82])],[(1,[z0,z2,z3,z266,z5,z6]),(0,[z66,z0,z2,z3,z4,z185,z6]),(0,[z0,z2,z3,z4,z5,z267,z6]),(0,[z68,z0,z2,z3,z4,z129,z6])],[(0,[z268,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z5,z269,z6])]],
   [[(0,[z0,z2,z4,z5,z6,z189,z61]),(0,[z270,z0,z2,z3,z4,z5,z6]),(0,[z271,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z4,z272,z5,z6])],[(0,[z16,z0,z2,z3,z29,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z273]),(0,[z0,z2,z3,z4,z5,z47,z6])],[(0,[z0,z2,z3,z4,z5,z274,z6]),(0,[z275,z0,z2,z3,z4,z6,z84]),(0,[z276,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z277,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z278]),(1,[z68,z0,z2,z3,z6,z279]),(0,[z0,z2,z250,z35,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z280]),(0,[z281,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z282]),(0,[z56,z0,z2,z37,z4,z5,z6]),(0,[z0,z2,z3,z4,z129,z5,z6])],[(0,[z283,z0,z2,z3,z4,z5,z6]),(0,[z0,z113,z91,z3,z4,z5,z6]),(0,[z0,z2,z3,z284,z4,z5,z6]),(0,[z0,z2,z3,z4,z285,z5,z6]),(0,[z0,z2,z37,z28,z4,z5,z6]),(0,[z0,z286,z2,z3,z4,z5,z6])],[(0,[z0,z2,z287,z3,z4,z5,z6]),(0,[z102,z0,z2,z3,z288,z5,z6]),(0,[z0,z159,z2,z289,z4,z5,z6]),(1,[z0,z2,z3,z4,z195,z82]),(0,[z0,z2,z3,z4,z5,z6,z82])],[]],
   [[(0,[z0,z290,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z291])],[(0,[z0,z292,z2,z3,z4,z5,z6]),(0,[z70,z0,z2,z3,z4,z5,z6]),(0,[z293,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z294]),(0,[z295,z0,z2,z3,z4,z5,z6])],[(0,[z119,z2,z91,z3,z4,z5,z6]),(1,[z0,z2,z296,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z297,z6]),(0,[z298,z0,z2,z3,z4,z5,z6])],[(0,[z299,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z300]),(0,[z0,z2,z3,z4,z5,z6,z301]),(0,[z0,z2,z53,z3,z302,z5,z6])],[(0,[z0,z2,z3,z303,z51,z4,z5]),(0,[z0,z2,z304,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z305])],[(0,[z0,z306,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z0,z2,z3,z5,z6,z41,z61]),(0,[z0,z2,z4,z5,z47,z6,z54]),(0,[z307,z0,z2,z3,z4,z5,z6]),(0,[z194,z142,z0,z2,z3,z4,z5])],[(1,[z119,z91,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z308,z6]),(0,[z0,z2,z3,z4,z5,z309,z6]),(0,[z60,z0,z2,z3,z4,z5,z61]),(0,[z0,z310,z2,z3,z4,z5,z6]),(0,[z102,z0,z2,z3,z4,z5,z311]),(0,[z0,z2,z3,z4,z5,z312,z6]),(0,[z0,z2,z3,z4,z313,z5,z6]),(0,[z0,z2,z3,z4,z5,z314,z6]),(0,[z315,z0,z2,z3,z4,z5,z6]),(0,[z316,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z317,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z318]),(0,[z149,z0,z2,z3,z4,z5,z47])]],
   [[(0,[z275,z2,z91,z3,z4,z5,z6]),(0,[z132,z0,z1,z3,z4,z5,z6]),(0,[z0,z2,z296,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z61]),(0,[z0,z2,z319,z3,z4,z5,z6])],[(0,[z149,z20,z0,z2,z3,z4,z5]),(0,[z0,z2,z320,z3,z4,z5,z6]),(0,[z0,z321,z2,z3,z4,z5,z6]),(1,[z265,z0,z2,z4,z5,z6])],[(0,[z0,z2,z3,z322,z4,z5,z6]),(0,[z0,z2,z3,z4,z323,z5,z6]),(0,[z0,z2,z3,z324,z4,z5,z6]),(0,[z0,z2,z146,z3,z4,z185,z6])],[(0,[z325,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z326]),(0,[z0,z2,z3,z4,z5,z6,z327])],[(0,[z0,z2,z3,z328,z4,z5,z6]),(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z34,z0,z2,z3,z4,z5,z329]),(0,[z0,z2,z3,z4,z5,z269,z6])],[(0,[z149,z70,z0,z2,z4,z5,z6]),(0,[z0,z2,z37,z192,z4,z5,z6]),(0,[z0,z159,z2,z3,z235,z5,z6]),(0,[z0,z2,z3,z46,z5,z69,z6]),(0,[z330,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z331]),(0,[z332,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z333,z6])],[(1,[z0,z334,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z335]),(0,[z83,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z336,z3,z4,z5,z6])]],
   [[(0,[z0,z159,z2,z3,z4,z5,z337]),(0,[z338,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z339,z3,z4,z5,z6])],[(0,[z340,z0,z2,z3,z4,z5,z6]),(1,[z242,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z103,z5,z6,z63])],[(1,[z0,z2,z120,z4,z5,z6]),(0,[z17,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z238,z5]),(0,[z0,z2,z3,z4,z341,z5,z6]),(0,[z0,z2,z3,z18,z39,z5,z6]),(0,[z0,z2,z3,z4,z342,z5,z6]),(0,[z0,z2,z343,z3,z4,z5,z6])],[(0,[z121,z70,z2,z3,z4,z5,z6]),(0,[z0,z2,z51,z151,z4,z5,z6]),(0,[z0,z113,z2,z3,z18,z5,z6]),(0,[z344,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z345,z3,z4,z5,z6]),(0,[z0,z346,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z326,z6])],[(0,[z347,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z348,z5,z6]),(1,[z275,z2,z3,z4,z95,z6]),(0,[z142,z0,z2,z3,z4,z5,z337]),(0,[z92,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z244,z4,z5,z6]),(0,[z349,z0,z2,z3,z4,z5,z6]),(0,[z350,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z351,z3,z4,z5,z6]),(0,[z0,z159,z2,z3,z4,z5,z6])]],
   [[(0,[z173,z0,z2,z3,z51,z4,z5]),(0,[z0,z2,z3,z4,z352,z5,z6]),(0,[z0,z2,z166,z146,z4,z5,z6]),(0,[z0,z2,z3,z353,z4,z5,z6])],[(0,[z119,z0,z2,z3,z354,z5,z6]),(0,[z0,z2,z3,z355,z4,z5,z6]),(1,[z0,z2,z3,z39,z129,z6])],[(0,[z356,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z357,z4,z5,z6]),(0,[z0,z2,z3,z4,z358,z5,z6])],[(0,[z60,z132,z2,z3,z4,z5,z6]),(0,[z0,z2,z359,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z360])],[(0,[z361,z0,z2,z3,z4,z5,z6]),(0,[z362,z0,z2,z3,z4,z5,z6]),(1,[z102,z0,z3,z4,z6,z63]),(0,[z102,z0,z2,z3,z4,z6,z63]),(0,[z0,z2,z3,z4,z363,z5,z6]),(0,[z0,z2,z4,z185,z5,z6,z259]),(0,[z68,z34,z0,z2,z3,z5,z6])],[(0,[z119,z0,z91,z3,z4,z5,z6]),(0,[z227,z0,z2,z3,z5,z6,z61]),(0,[z0,z2,z3,z4,z85,z5,z6]),(0,[z0,z2,z166,z4,z5,z47,z6]),(0,[z0,z2,z364,z3,z4,z5,z6]),(1,[z365,z2,z3,z4,z5,z6]),(0,[z149,z0,z2,z3,z4,z5,z6]),(0,[z0,z366,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z367]),(0,[z0,z2,z3,z4,z368,z5,z6]),(0,[z0,z2,z3,z4,z238,z5,z6]),(0,[z0,z2,z369,z3,z4,z5,z6]),(0,[z0,z2,z3,z370,z4,z5,z6]),(0,[z371,z0,z2,z3,z4,z5,z6])],[(0,[z0,z372,z2,z3,z4,z5,z6]),(0,[z149,z0,z2,z4,z46,z5,z6])]],
   [[(0,[z121,z0,z2,z28,z4,z5,z6]),(0,[z0,z2,z3,z4,z373,z5,z6]),(0,[z0,z113,z3,z18,z4,z5,z6]),(0,[z56,z0,z2,z3,z46,z5,z6])],[(0,[z0,z2,z3,z374,z4,z5,z6]),(1,[z0,z2,z3,z288,z5,z6]),(0,[z0,z2,z3,z35,z4,z5,z69])],[(0,[z132,z1,z2,z3,z4,z5,z6]),(0,[z70,z0,z2,z28,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z375,z6]),(0,[z0,z2,z3,z4,z5,z376,z6])],[(0,[z119,z0,z2,z322,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z34,z0,z2,z3,z5,z6,z329])],[(0,[z0,z2,z3,z4,z377,z5,z6]),(0,[z378,z0,z2,z3,z51,z5,z6]),(0,[z379,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z380,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z381]),(0,[z0,z2,z3,z4,z5,z6,z382])],[(0,[z0,z91,z3,z4,z38,z5,z6]),(0,[z121,z0,z2,z51,z4,z5,z6]),(0,[z2,z3,z4,z95,z5,z6,z84]),(0,[z383,z0,z2,z3,z4,z5,z6]),(1,[z316,z2,z3,z4,z5,z6])],[(0,[z121,z0,z2,z4,z5,z47,z6]),(0,[z60,z0,z2,z3,z4,z5,z21]),(0,[z384,z0,z2,z3,z4,z5,z6]),(0,[z385,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z386,z3,z4,z5,z6]),(0,[z70,z0,z2,z51,z4,z5,z6]),(0,[z0,z387,z2,z3,z4,z5,z6]),(0,[z0,z2,z151,z4,z5,z6,z259]),(0,[z0,z2,z3,z4,z388,z5,z6]),(0,[z0,z2,z3,z389,z4,z5,z6]),(0,[z0,z2,z3,z39,z4,z6,z279])],[(0,[z0,z2,z3,z390,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z391]),(1,[z0,z2,z3,z4,z5,z311])],[(1,[z0,z2,z3,z392,z5,z6]),(0,[z0,z2,z37,z3,z46,z5,z6])],[(0,[z0,z2,z3,z393,z4,z5,z6])],[(0,[z0,z2,z394,z3,z4,z5,z6]),(0,[z0,z2,z146,z151,z4,z5,z6]),(0,[z0,z2,z3,z395,z4,z5,z6])],[(0,[z0,z396,z2,z3,z4,z5,z6])],[(0,[z397,z0,z2,z3,z4,z5,z6]),(0,[z398,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z399,z4,z5,z6]),(0,[z0,z2,z3,z400,z4,z5,z6]),(0,[z34,z0,z2,z3,z46,z5,z6]),(0,[z0,z2,z53,z4,z5,z47,z6])],[(0,[z0,z2,z3,z4,z5,z401,z6]),(0,[z0,z2,z3,z4,z402,z5,z6]),(0,[z0,z2,z3,z39,z129,z5,z6])]],
   [[(0,[z0,z2,z3,z124,z4,z5,z6]),(0,[z83,z2,z3,z4,z5,z6,z84]),(1,[z56,z0,z2,z46,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z403]),(0,[z0,z2,z3,z4,z5,z6,z404]),(0,[z0,z2,z3,z4,z5,z6,z405])],[(0,[z0,z2,z3,z4,z406,z5,z6]),(0,[z0,z407,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z279])],[(0,[z70,z0,z2,z192,z4,z5,z6]),(0,[z16,z0,z306,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z408,z5,z6]),(0,[z0,z2,z3,z4,z409,z5,z6]),(0,[z0,z2,z3,z4,z5,z410,z6]),(0,[z365,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z158,z82]),(0,[z0,z2,z3,z4,z5,z411,z6])],[(0,[z0,z2,z3,z4,z5,z6,z412]),(0,[z0,z2,z3,z4,z5,z82,z337]),(0,[z0,z2,z413,z3,z4,z5,z6]),(0,[z0,z414,z2,z3,z4,z5,z6]),(0,[z66,z0,z2,z4,z5,z6,z259])],[(0,[z0,z2,z3,z415,z4,z5,z6]),(0,[z416,z0,z3,z4,z103,z5,z6]),(0,[z0,z2,z3,z4,z417,z5,z6]),(0,[z0,z2,z3,z4,z195,z5,z82])],[(1,[z0,z113,z3,z18,z5,z6])],[(0,[z418,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z419,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z61]),(0,[z0,z2,z420,z3,z4,z5,z6]),(0,[z0,z62,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z28,z4,z5,z6])],[(0,[z149,z121,z0,z2,z4,z5,z6]),(0,[z0,z62,z3,z4,z103,z5,z6]),(0,[z416,z0,z2,z3,z4,z5,z158]),(0,[z0,z421,z2,z3,z4,z5,z6])]],
   [[(0,[z422,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z35,z4,z272,z5,z6])],[(0,[z0,z2,z3,z4,z423,z5,z6]),(0,[z0,z2,z3,z4,z5,z424,z6])],[(0,[z0,z2,z425,z3,z4,z5,z6]),(0,[z0,z2,z3,z426,z4,z5,z6])],[(0,[z427,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z428,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z429]),(0,[z0,z2,z3,z4,z5,z170,z6])],[(0,[z0,z2,z91,z3,z4,z5,z6]),(0,[z0,z2,z3,z51,z4,z5,z6]),(0,[z0,z430,z2,z3,z4,z5,z6])],[(0,[z0,z431,z2,z3,z4,z5,z6]),(0,[z432,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z433]),(0,[z0,z2,z3,z4,z5,z434,z6]),(0,[z0,z2,z3,z4,z5,z6,z435]),(0,[z0,z2,z3,z436,z4,z5,z6])],[(1,[z437,z0,z2,z3,z4,z5]),(0,[z438,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z439,z4,z5,z6]),(0,[z0,z2,z3,z29,z4,z5,z6]),(0,[z0,z2,z3,z440,z4,z5,z6]),(0,[z0,z2,z3,z39,z4,z5,z6]),(1,[z92,z0,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z19,z46,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z189]),(0,[z441,z0,z2,z3,z4,z5,z6])],[(0,[z0,z122,z2,z3,z4,z5,z6]),(0,[z0,z2,z442,z3,z4,z5,z6]),(1,[z0,z2,z3,z143,z5,z6]),(0,[z443,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z18,z5,z6,z279])],[(0,[z121,z0,z2,z3,z4,z5,z6]),(0,[z437,z0,z2,z3,z4,z19,z5]),(0,[z0,z2,z3,z4,z95,z5,z6]),(0,[z444,z0,z2,z3,z4,z5,z6]),(0,[z102,z0,z62,z3,z4,z5,z6]),(0,[z445,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z446,z5,z6])],[(0,[z0,z2,z3,z4,z5,z447,z6]),(0,[z0,z2,z3,z4,z448,z5,z6]),(0,[z66,z0,z2,z3,z4,z6,z259]),(1,[z0,z2,z3,z35,z5,z69])],[(0,[z0,z3,z18,z4,z38,z5,z6]),(0,[z0,z2,z449,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z450]),(0,[z451,z0,z2,z3,z4,z5,z6]),(0,[z0,z452,z2,z3,z4,z5,z6]),(0,[z416,z0,z3,z4,z5,z6,z337]),(0,[z0,z2,z289,z3,z4,z5,z6]),(0,[z0,z453,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z69,z6])],[(0,[z454,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z455,z5,z6]),(0,[z456,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z192,z3,z4,z5,z6]),(0,[z457,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z458,z4,z5,z6]),(0,[z0,z55,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z459,z5,z6]),(0,[z102,z0,z2,z3,z211,z5,z6]),(0,[z149,z0,z2,z37,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z460]),(0,[z461,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z462,z3,z4,z5,z6]),(0,[z0,z2,z3,z38,z5,z6,z279]),(0,[z102,z372,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z302,z4,z5,z6])],[(0,[z0,z2,z192,z4,z46,z5,z6]),(0,[z102,z0,z2,z109,z4,z5,z6]),(0,[z0,z2,z53,z3,z4,z5,z6]),(0,[z0,z2,z3,z463,z4,z5,z6])],[(1,[z0,z2,z3,z303,z4,z5]),(0,[z0,z159,z2,z3,z392,z5,z6]),(0,[z464,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z75,z4,z5,z6]),(0,[z17,z0,z2,z3,z5,z69,z6]),(0,[z102,z0,z2,z320,z4,z5,z6]),(0,[z465,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z466,z3,z4,z5,z6])],[(0,[z0,z91,z3,z151,z4,z5,z6]),(0,[z16,z0,z2,z124,z4,z5,z6])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(1,[z0,z2,z467,z4,z5,z6]),(0,[z0,z468,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z469])],[(0,[z0,z2,z3,z4,z266,z5,z6]),(0,[z0,z2,z3,z4,z103,z5,z6])],[(0,[z470,z0,z2,z3,z4,z5,z6]),(0,[z0,z471,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z472,z5,z6]),(0,[z56,z0,z2,z3,z38,z5,z6]),(0,[z0,z2,z3,z4,z473,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z329]),(0,[z265,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z83,z275,z2,z3,z4,z5,z6]),(0,[z20,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z474,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z475]),(0,[z0,z2,z3,z4,z5,z6,z476])],[(0,[z477,z0,z2,z3,z4,z5,z6]),(0,[z188,z0,z2,z3,z4,z5,z6]),(0,[z275,z2,z3,z4,z95,z5,z6]),(0,[z0,z2,z3,z143,z4,z5,z6]),(0,[z0,z113,z2,z3,z4,z5,z6])],[(1,[z0,z191,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z478]),(0,[z0,z479,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z195,z6,z82])],[(0,[z0,z480,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z481]),(0,[z482,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z483,z3,z4,z5,z6]),(0,[z159,z2,z243,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z484])],[(1,[z132,z1,z3,z4,z5,z6]),(0,[z0,z2,z4,z285,z19,z5,z6]),(0,[z275,z0,z2,z3,z4,z95,z6]),(0,[z485,z0,z2,z3,z4,z5,z6])],[(0,[z132,z275,z2,z3,z4,z5,z6]),(0,[z486,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z487,z6]),(0,[z416,z0,z159,z3,z4,z5,z6]),(0,[z0,z2,z488,z3,z4,z5,z6])],[(0,[z20,z2,z3,z4,z5,z21,z6]),(0,[z0,z2,z3,z4,z5,z158,z6]),(0,[z0,z2,z146,z3,z4,z6,z259])]],
   [[(0,[z489,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z490,z5,z6]),(0,[z0,z55,z2,z3,z85,z5,z6]),(0,[z491,z0,z2,z3,z4,z5,z6])],[(0,[z2,z91,z3,z4,z5,z21,z6]),(1,[z0,z2,z4,z285,z5,z6]),(0,[z0,z2,z166,z28,z4,z5,z6]),(0,[z0,z2,z37,z3,z38,z5,z6]),(0,[z0,z2,z3,z492,z4,z5,z6]),(0,[z0,z2,z3,z4,z272,z5,z6]),(0,[z0,z2,z3,z4,z195,z5,z6]),(0,[z142,z0,z2,z3,z4,z195,z5])],[(0,[z493,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z494,z3,z4,z5,z6]),(0,[z17,z0,z2,z37,z3,z5,z6]),(0,[z495,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z46,z5,z6]),(0,[z0,z2,z3,z4,z496,z5,z6]),(0,[z0,z2,z3,z497,z4,z5,z6])],[(0,[z0,z498,z2,z3,z4,z5,z6]),(0,[z0,z2,z146,z4,z185,z5,z6]),(1,[z81,z0,z2,z3,z5,z6])],[(0,[z0,z2,z3,z499,z4,z5,z6])],[(0,[z0,z2,z500,z3,z4,z5,z6]),(0,[z34,z0,z2,z3,z38,z5,z6])],[(0,[z0,z2,z3,z501,z4,z5,z6]),(0,[z502,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z503,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z504]),(0,[z152,z0,z2,z3,z4,z5,z6]),(0,[z137,z0,z2,z3,z18,z5,z6]),(0,[z66,z0,z2,z146,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z505,z6])],[(0,[z0,z2,z3,z26,z4,z5,z6]),(0,[z0,z2,z166,z51,z4,z5,z6]),(0,[z506,z0,z2,z3,z4,z5,z6]),(0,[z0,z507,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z18,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z337]),(0,[z0,z2,z243,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z508]),(0,[z509,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z129,z5,z6,z279])],[(0,[z510,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z511]),(0,[z0,z2,z3,z512,z4,z5,z6]),(0,[z0,z2,z3,z513,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z514])],[(0,[z515,z0,z2,z3,z4,z5,z6]),(0,[z0,z516,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z517,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z518]),(0,[z20,z0,z2,z3,z4,z5,z61]),(0,[z0,z2,z3,z4,z5,z6,z519])],[(0,[z0,z2,z520,z3,z4,z5,z6]),(0,[z521,z0,z2,z3,z4,z5,z6]),(0,[z522,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z523,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z524])],[(0,[z525,z0,z2,z3,z4,z5,z6]),(0,[z56,z0,z2,z166,z4,z5,z6]),(0,[z0,z2,z3,z4,z526,z5,z6]),(0,[z0,z2,z3,z4,z5,z527,z6]),(0,[z0,z2,z3,z528,z4,z5,z6])],[(0,[z0,z2,z3,z4,z529,z5,z6]),(0,[z0,z2,z3,z4,z19,z5,z6]),(0,[z60,z34,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z530,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z531])],[(0,[z0,z2,z3,z4,z532,z5,z6]),(0,[z533,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z534,z3,z4,z5,z6])]],
   [[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z56,z0,z2,z3,z28,z5,z6]),(0,[z0,z3,z4,z5,z169,z6,z82])],[(0,[z0,z2,z3,z4,z535,z5,z6]),(0,[z0,z2,z536,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z537,z5,z6]),(1,[z0,z55,z166,z4,z5,z6]),(1,[z0,z2,z3,z211,z5,z6]),(0,[z538,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z539,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z540]),(0,[z541,z0,z2,z3,z4,z5,z6]),(1,[z372,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z542,z5,z6]),(0,[z17,z0,z2,z3,z19,z5,z6]),(0,[z56,z0,z2,z151,z4,z5,z6]),(1,[z0,z2,z109,z4,z5,z6]),(0,[z543,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z544,z5,z6]),(0,[z0,z2,z545,z3,z4,z5,z6])],[(0,[z546,z0,z2,z3,z4,z5,z6]),(0,[z0,z159,z2,z467,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z547])],[(0,[z548,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z320,z4,z5,z6]),(0,[z0,z2,z3,z4,z549,z5,z6]),(0,[z0,z2,z3,z4,z550,z5,z6])],[(0,[z0,z2,z3,z19,z38,z5,z6]),(0,[z0,z2,z3,z4,z5,z21,z6]),(0,[z0,z2,z3,z4,z551,z5,z6]),(0,[z0,z552,z2,z3,z4,z5,z6]),(0,[z416,z0,z2,z3,z4,z5,z337]),(0,[z0,z2,z3,z28,z5,z69,z6])]],
   [[(0,[z121,z56,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z553,z6]),(0,[z0,z62,z2,z3,z4,z103,z6])],[(0,[z119,z0,z2,z3,z4,z5,z6]),(0,[z554,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z158,z6,z337]),(0,[z68,z0,z2,z3,z4,z6,z279]),(0,[z555,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z556,z5,z6]),(0,[z0,z2,z3,z4,z557,z5,z6]),(0,[z16,z2,z3,z4,z19,z5,z6]),(0,[z437,z0,z2,z3,z4,z5,z6]),(0,[z558,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z37,z3,z28,z5,z6]),(0,[z66,z149,z0,z2,z4,z5,z6])],[(0,[z121,z0,z2,z192,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z559]),(0,[z0,z2,z147,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z169,z6])],[(0,[z560,z0,z2,z3,z4,z5,z6]),(0,[z16,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z37,z28,z5,z6]),(0,[z0,z2,z3,z129,z5,z69,z6]),(1,[z34,z0,z2,z3,z5,z329])],[(0,[z0,z55,z166,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z561]),(0,[z416,z0,z2,z3,z4,z5,z6]),(0,[z34,z0,z2,z3,z28,z5,z6])],[(0,[z275,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z119,z0,z2,z3,z26,z5,z6]),(0,[z562,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z563])],[(0,[z0,z2,z3,z4,z288,z5,z6]),(0,[z0,z564,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z69,z6,z329])],[(0,[z0,z2,z3,z4,z5,z6,z565]),(0,[z0,z2,z3,z4,z566,z5,z6])],[(0,[z0,z2,z166,z3,z4,z5,z6]),(0,[z0,z2,z3,z567,z4,z5,z6]),(0,[z568,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z147,z4,z5,z6])],[(0,[z152,z0,z3,z151,z4,z5,z6])],[(0,[z132,z0,z91,z3,z4,z5,z6]),(0,[z569,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z570,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z571,z6]),(0,[z16,z0,z2,z296,z4,z5,z6]),(0,[z0,z2,z3,z4,z572,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z573]),(0,[z0,z2,z3,z574,z4,z5,z6]),(0,[z68,z0,z2,z3,z39,z5,z6])]],
   [[(0,[z575,z0,z2,z3,z4,z5,z6]),(0,[z576,z0,z2,z3,z4,z5,z6]),(0,[z577,z0,z2,z3,z4,z5,z6]),(0,[z578,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z579,z5,z6])],[(0,[z0,z2,z580,z3,z4,z5,z6]),(0,[z60,z0,z2,z53,z3,z4,z5]),(0,[z152,z0,z55,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z581,z5,z6]),(0,[z0,z582,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z583,z4,z5,z6]),(0,[z0,z2,z3,z4,z392,z5,z6])],[(0,[z378,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z584]),(0,[z0,z2,z3,z4,z5,z6,z585])],[(1,[z0,z122,z3,z4,z5,z6]),(0,[z121,z0,z2,z3,z266,z5,z6]),(0,[z0,z2,z3,z303,z4,z5,z6]),(0,[z20,z0,z2,z3,z4,z5,z21]),(0,[z0,z2,z3,z4,z5,z6,z586]),(0,[z0,z587,z2,z3,z4,z5,z6]),(0,[z588,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z589,z5,z6])],[(0,[z0,z2,z3,z590,z4,z5,z6]),(0,[z591,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z592,z3,z4,z5,z6])],[(0,[z593,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z146,z4,z185,z6])],[(0,[z0,z113,z1,z3,z4,z5,z6]),(0,[z0,z2,z594,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z259]),(0,[z0,z2,z3,z4,z5,z6,z595])]],
   [[(0,[z0,z2,z3,z4,z596,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z597]),(0,[z68,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z598,z5,z6])],[(0,[z0,z2,z3,z4,z38,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z599])],[(0,[z0,z2,z3,z600,z4,z5,z6]),(1,[z378,z0,z2,z3,z5,z6]),(0,[z0,z601,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z175,z5,z6]),(0,[z602,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z603,z6])],[(0,[z16,z0,z334,z3,z4,z5,z6]),(0,[z604,z0,z2,z3,z4,z5,z6])],[(0,[z605,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z606]),(0,[z0,z2,z3,z235,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z607]),(0,[z0,z2,z3,z4,z5,z6,z608])],[(0,[z0,z2,z3,z4,z5,z6,z609]),(0,[z0,z2,z3,z29,z46,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z610]),(0,[z102,z416,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z611,z4,z5,z6])],[(0,[z0,z2,z612,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z613,z6]),(0,[z0,z2,z614,z3,z4,z5,z6]),(0,[z0,z615,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z616,z5,z6]),(0,[z0,z2,z617,z3,z4,z5,z6]),(0,[z618,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z185,z5,z47,z6]),(0,[z194,z0,z2,z3,z4,z5,z82])]],
   [[(0,[z0,z2,z3,z28,z19,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z63]),(0,[z0,z2,z3,z619,z4,z5,z6])],[(0,[z102,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z620,z4,z5,z6]),(0,[z0,z2,z621,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z622,z5,z6])],[(0,[z0,z2,z3,z623,z4,z5,z6]),(0,[z0,z2,z624,z3,z4,z5,z6])],[(0,[z625,z0,z2,z3,z4,z5,z6]),(0,[z626,z0,z2,z3,z4,z5,z6]),(0,[z83,z0,z2,z3,z4,z6,z84]),(1,[z0,z2,z233,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z627])],[(1,[z121,z2,z51,z4,z5,z6]),(0,[z0,z2,z3,z628,z4,z5,z6]),(0,[z137,z0,z3,z4,z38,z5,z6]),(0,[z0,z2,z3,z629,z4,z5,z6]),(0,[z34,z0,z2,z3,z4,z5,z69]),(0,[z0,z2,z3,z4,z5,z6,z630]),(0,[z0,z2,z631,z3,z4,z5,z6])],[(0,[z0,z632,z2,z3,z4,z5,z6]),(0,[z0,z2,z633,z3,z4,z5,z6])],[(0,[z56,z17,z0,z2,z3,z5,z6])],[(0,[z0,z2,z3,z4,z5,z634,z6]),(1,[z16,z2,z3,z19,z5,z6]),(0,[z17,z0,z2,z3,z29,z5,z6]),(0,[z0,z2,z3,z4,z635,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z118])]],
   [[(0,[z636,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z18,z5,z69,z6]),(0,[z0,z2,z3,z4,z5,z6,z311]),(1,[z0,z159,z3,z4,z5,z158]),(0,[z637,z0,z2,z3,z4,z5,z6]),(0,[z638,z0,z2,z3,z4,z5,z6])],[(0,[z119,z132,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z639]),(0,[z0,z640,z2,z3,z4,z5,z6]),(0,[z641,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z642,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z54]),(0,[z0,z2,z3,z35,z4,z5,z329])],[(0,[z2,z3,z29,z4,z19,z5,z6]),(0,[z0,z2,z3,z4,z5,z643,z6]),(0,[z0,z2,z3,z644,z4,z5,z6]),(0,[z645,z0,z2,z3,z4,z5,z6]),(0,[z0,z646,z2,z3,z4,z5,z6])],[(0,[z647,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z648]),(0,[z137,z0,z2,z3,z4,z5,z6]),(0,[z102,z0,z3,z4,z5,z158,z6]),(1,[z0,z2,z289,z4,z5,z6]),(0,[z142,z0,z2,z3,z4,z5,z158])],[(0,[z649,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z650,z5,z6]),(0,[z0,z2,z3,z651,z4,z5,z6]),(0,[z316,z2,z3,z4,z5,z6,z82]),(0,[z0,z2,z3,z5,z269,z6,z82])],[(0,[z0,z2,z3,z4,z5,z6,z652]),(0,[z0,z2,z3,z4,z5,z6,z653]),(0,[z0,z2,z3,z4,z5,z654,z6]),(0,[z655,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z656,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z657]),(0,[z658,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z659,z3,z4,z5,z6]),(0,[z0,z2,z192,z151,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z660]),(0,[z0,z2,z3,z4,z5,z661,z6]),(0,[z365,z159,z2,z3,z4,z5,z6]),(0,[z662,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z663,z6])],[(1,[z0,z2,z3,z354,z5,z6]),(0,[z2,z192,z3,z51,z4,z5,z6]),(0,[z0,z2,z3,z38,z5,z69,z6]),(0,[z242,z0,z2,z3,z4,z5,z6]),(1,[z0,z62,z3,z4,z103,z6]),(0,[z0,z2,z3,z4,z175,z5,z6]),(0,[z0,z664,z2,z3,z4,z5,z6])]],
   [[],[(0,[z60,z149,z0,z2,z3,z4,z5]),(0,[z149,z0,z2,z4,z5,z6,z54]),(0,[z0,z665,z2,z3,z4,z5,z6]),(1,[z194,z142,z0,z2,z3,z4])],[(0,[z188,z0,z2,z4,z19,z5,z6])],[(0,[z0,z2,z250,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z666]),(1,[z0,z2,z3,z244,z5,z6]),(0,[z34,z17,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z667,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z668])],[(0,[z669,z0,z2,z3,z4,z5,z6]),(0,[z34,z16,z0,z2,z3,z5,z6]),(0,[z102,z0,z2,z3,z4,z5,z326])],[(0,[z0,z2,z3,z4,z5,z670,z6]),(0,[z671,z0,z2,z3,z4,z5,z6]),(0,[z17,z2,z3,z29,z4,z5,z6]),(0,[z0,z2,z3,z4,z672,z5,z6]),(0,[z66,z0,z2,z4,z5,z47,z6]),(0,[z0,z2,z3,z4,z5,z6,z673])],[(0,[z119,z0,z1,z3,z4,z5,z6]),(0,[z0,z2,z3,z674,z4,z5,z6]),(0,[z0,z2,z334,z3,z4,z5,z6])]],
   [[],[(1,[z0,z2,z322,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z675,z6]),(0,[z0,z676,z2,z3,z4,z5,z6]),(1,[z416,z0,z3,z4,z5,z337]),(0,[z0,z2,z3,z677,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z678])],[(0,[z679,z0,z2,z3,z4,z5,z6]),(0,[z0,z680,z2,z3,z4,z5,z6]),(0,[z0,z2,z166,z4,z5,z6,z259]),(0,[z0,z2,z3,z4,z5,z6,z681]),(0,[z0,z682,z2,z3,z4,z5,z6])],[(0,[z0,z2,z683,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z684,z5,z6]),(0,[z685,z0,z2,z3,z4,z5,z6]),(0,[z686,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z166,z192,z4,z5,z6]),(0,[z687,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z688,z6])],[(0,[z16,z0,z2,z3,z5,z69,z6]),(0,[z60,z0,z2,z3,z35,z4,z5]),(0,[z68,z0,z2,z3,z5,z6,z279]),(0,[z0,z2,z3,z39,z4,z129,z6])],[(0,[z0,z2,z3,z467,z4,z5,z6]),(0,[z689,z0,z2,z3,z4,z5,z6]),(0,[z149,z0,z2,z53,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z690]),(0,[z0,z2,z3,z4,z691,z5,z6])],[(0,[z0,z2,z3,z151,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z692,z6])]],
   [[(0,[z149,z0,z2,z166,z4,z5,z6]),(0,[z693,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z4,z5,z6])],[(0,[z0,z1,z3,z4,z38,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z694]),(0,[z0,z2,z3,z4,z5,z6,z695]),(0,[z0,z2,z3,z4,z696,z5,z6]),(0,[z0,z2,z3,z4,z5,z697,z6]),(1,[z0,z2,z3,z302,z5,z6])],[(0,[z0,z2,z3,z698,z4,z5,z6]),(0,[z699,z0,z2,z3,z4,z5,z6]),(0,[z194,z142,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z700,z5,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z354,z5,z6]),(0,[z194,z0,z2,z3,z4,z5,z6])],[(1,[z0,z306,z3,z4,z5,z6]),(0,[z152,z0,z2,z151,z4,z5,z6])],[(0,[z2,z91,z3,z4,z5,z6,z84]),(1,[z173,z0,z2,z3,z4,z5]),(0,[z0,z701,z2,z3,z4,z5,z6]),(0,[z0,z2,z702,z3,z4,z5,z6]),(0,[z0,z2,z703,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z704]),(1,[z70,z2,z192,z4,z5,z6]),(0,[z149,z0,z2,z151,z4,z5,z6]),(0,[z705,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z173,z121,z2,z51,z4,z5]),(0,[z0,z2,z166,z143,z5,z6]),(0,[z102,z0,z3,z4,z311,z63]),(0,[z0,z2,z289,z235,z5,z6]),(0,[z0,z159,z3,z4,z5,z707]),(0,[z0,z2,z3,z708,z5,z6]),(0,[z92,z3,z4,z5,z6,z118])],[(0,[z0,z1,z3,z354,z5,z6]),(0,[z0,z2,z3,z709,z5,z6]),(0,[z2,z243,z289,z4,z5,z6]),(0,[z0,z2,z710,z4,z5,z6])],[(0,[z121,z2,z51,z266,z5,z6]),(0,[z0,z334,z3,z29,z5,z6]),(0,[z0,z2,z3,z711,z5,z6]),(0,[z0,z2,z233,z4,z5,z6]),(0,[z102,z0,z320,z4,z6,z63]),(0,[z0,z2,z3,z566,z5,z69])],[(0,[z121,z2,z51,z4,z5,z6]),(0,[z0,z191,z3,z266,z5,z6]),(0,[z56,z626,z0,z2,z5,z6]),(0,[z152,z0,z151,z4,z5,z6])],[(0,[z173,z378,z0,z2,z3,z5]),(0,[z372,z2,z3,z288,z5,z6]),(0,[z0,z2,z712,z4,z5,z6])],[(0,[z0,z713,z3,z4,z5,z6]),(0,[z0,z2,z109,z288,z5,z6]),(0,[z0,z3,z4,z5,z6,z714]),(0,[z0,z2,z3,z5,z6,z715]),(0,[z716,z0,z2,z4,z5,z6])],[(0,[z0,z2,z3,z717,z5,z6]),(0,[z718,z0,z2,z4,z5,z6]),(0,[z0,z3,z4,z5,z169,z6])],[(0,[z0,z2,z3,z719,z5,z6]),(0,[z0,z2,z320,z288,z5,z6]),(0,[z0,z159,z3,z4,z5,z158]),(0,[z0,z2,z3,z720,z5,z6])]],
   [[(0,[z0,z2,z721,z4,z5,z6]),(0,[z132,z471,z3,z4,z5,z6]),(0,[z0,z2,z3,z722,z5,z6])],[(0,[z0,z480,z166,z4,z5,z6])],[(0,[z70,z2,z723,z4,z5,z6]),(0,[z16,z168,z2,z3,z5,z6]),(0,[z0,z2,z289,z4,z5,z6])],[(0,[z0,z1,z322,z4,z5,z6]),(0,[z0,z2,z724,z4,z5,z6]),(0,[z188,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z189]),(0,[z0,z2,z3,z725,z5,z6]),(0,[z0,z2,z3,z211,z5,z311]),(0,[z34,z0,z2,z3,z5,z25])],[(0,[z0,z2,z3,z726,z5,z6]),(0,[z541,z1,z3,z4,z5,z6]),(0,[z372,z2,z3,z4,z5,z311]),(0,[z0,z2,z3,z4,z6,z715])],[(0,[z0,z2,z727,z4,z5,z6]),(0,[z0,z2,z109,z4,z5,z311])],[(0,[z0,z2,z3,z4,z5,z728]),(1,[z2,z723,z4,z5,z6]),(0,[z0,z2,z3,z729,z5,z6]),(0,[z0,z62,z3,z4,z103,z6])],[(0,[z0,z2,z320,z4,z5,z311])]],
   [[(0,[z0,z2,z4,z5,z6,z730]),(0,[z0,z3,z4,z5,z6,z731]),(0,[z194,z142,z0,z2,z3,z4])],[(0,[z188,z0,z2,z18,z5,z6]),(0,[z0,z732,z3,z4,z5,z6]),(0,[z0,z2,z733,z4,z5,z6]),(0,[z0,z665,z3,z18,z5,z6]),(0,[z0,z2,z3,z734,z5,z6]),(0,[z316,z92,z3,z4,z5,z6])],[(0,[z735,z2,z3,z4,z5,z6])],[(0,[z736,z0,z2,z4,z5,z6])],[],[(0,[z0,z2,z3,z737,z5,z6]),(0,[z0,z3,z4,z103,z424,z6])],[(0,[z0,z2,z3,z738,z5,z6])],[(0,[z2,z386,z3,z4,z5,z21]),(0,[z2,z192,z723,z4,z5,z6]),(0,[z227,z0,z2,z3,z5,z6]),(0,[z20,z0,z2,z3,z302,z5]),(0,[z0,z2,z720,z46,z5,z6])]],
   [[(0,[z121,z378,z0,z2,z5,z6]),(0,[z2,z3,z4,z95,z6,z519]),(0,[z416,z0,z3,z4,z5,z337])],[],[(0,[z2,z243,z3,z4,z5,z6]),(0,[z0,z739,z3,z4,z5,z6]),(0,[z0,z740,z3,z4,z5,z6]),(0,[z16,z188,z0,z2,z5,z6]),(0,[z0,z2,z3,z4,z5,z741])],[(0,[z0,z2,z3,z742,z5,z6]),(0,[z743,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z6,z714])],[(0,[z0,z2,z3,z4,z744,z6]),(0,[z0,z745,z3,z4,z5,z6]),(0,[z0,z2,z250,z4,z5,z6])],[(0,[z16,z334,z3,z19,z5,z6]),(0,[z0,z2,z746,z4,z5,z6]),(0,[z0,z2,z5,z6,z41,z189]),(0,[z0,z2,z3,z747,z5,z6]),(0,[z0,z2,z3,z748,z5,z6]),(0,[z0,z2,z3,z4,z5,z749])],[(0,[z750,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z751]),(1,[z0,z2,z3,z6,z715])],[(0,[z752,z2,z3,z4,z5,z6]),(0,[z137,z0,z3,z38,z5,z6]),(0,[z0,z3,z4,z753,z5,z6])]],
   [[(0,[z0,z2,z3,z754,z4,z5]),(0,[z0,z2,z3,z4,z5,z707]),(0,[z0,z2,z3,z302,z5,z6])],[(0,[z0,z2,z3,z4,z5,z755]),(0,[z0,z2,z756,z4,z5,z6])],[(0,[z437,z188,z0,z2,z4,z5]),(0,[z0,z3,z4,z757,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z758,z0,z2,z4,z5,z6]),(0,[z0,z55,z166,z143,z5,z6]),(0,[z0,z2,z3,z4,z5,z759]),(0,[z0,z2,z3,z5,z269,z6])],[(0,[z0,z306,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z760,z5]),(0,[z761,z0,z2,z3,z4,z5]),(0,[z0,z762,z3,z4,z5,z6]),(0,[z437,z17,z0,z2,z3,z5]),(0,[z0,z2,z4,z272,z5,z6])],[(0,[z0,z2,z3,z763,z5,z6]),(0,[z477,z0,z151,z4,z5,z6]),(0,[z173,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z764,z5]),(0,[z765,z0,z2,z4,z5,z6]),(0,[z83,z2,z3,z4,z6,z766]),(0,[z2,z3,z4,z5,z6,z767]),(0,[z137,z0,z3,z757,z5,z6]),(0,[z0,z2,z147,z38,z5,z6]),(0,[z0,z2,z4,z5,z47,z768])],[(0,[z0,z2,z3,z769,z5,z6]),(0,[z70,z2,z192,z4,z5,z6]),(0,[z121,z564,z2,z4,z5,z6]),(0,[z770,z0,z2,z4,z5,z6])],[(0,[z0,z2,z3,z771,z5,z6]),(0,[z7,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z285,z238,z5]),(0,[z772,z2,z3,z4,z5,z6]),(0,[z68,z0,z2,z3,z6,z279]),(0,[z68,z0,z2,z3,z6,z715])]],
   [[(0,[z0,z2,z4,z5,z6,z773]),(0,[z0,z774,z3,z4,z5,z6]),(0,[z20,z2,z3,z4,z5,z21]),(0,[z60,z479,z2,z3,z4,z5])],[(0,[z0,z2,z120,z354,z5,z6])],[(0,[z0,z2,z3,z26,z5,z6]),(0,[z102,z0,z3,z4,z6,z714]),(0,[z0,z2,z3,z4,z195,z82]),(0,[z265,z0,z4,z5,z169,z6])],[(0,[z222,z0,z2,z46,z5,z6]),(0,[z775,z2,z3,z4,z5,z6])],[],[(0,[z2,z713,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z776]),(0,[z227,z0,z2,z5,z6,z189]),(0,[z365,z159,z3,z4,z5,z158])],[(0,[z0,z2,z296,z4,z5,z6]),(0,[z0,z777,z3,z4,z5,z6])],[(0,[z0,z306,z296,z4,z5,z6]),(0,[z0,z2,z4,z566,z5,z47]),(0,[z149,z42,z0,z2,z4,z5])]],
   [[(0,[z0,z632,z151,z4,z5,z6]),(0,[z0,z55,z727,z4,z5,z6]),(0,[z149,z0,z2,z4,z5,z72]),(0,[z365,z2,z289,z4,z5,z6]),(0,[z0,z2,z175,z5,z47,z6])],[(0,[z0,z2,z3,z778,z5,z6]),(1,[z0,z3,z757,z5,z6])],[(0,[z119,z91,z3,z4,z5,z6]),(0,[z0,z2,z3,z75,z5,z6]),(0,[z173,z0,z2,z166,z4,z5]),(0,[z9,z2,z192,z4,z5,z6]),(0,[z0,z2,z3,z779,z5,z6]),(0,[z2,z3,z4,z5,z6,z780])],[(0,[z60,z2,z3,z4,z5,z61]),(0,[z781,z0,z2,z3,z5,z6])],[(0,[z121,z2,z723,z4,z5,z6]),(0,[z0,z2,z124,z5,z69,z6]),(0,[z0,z782,z3,z4,z5,z6]),(1,[z0,z2,z4,z5,z768])],[(0,[z783,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z784,z5,z6]),(0,[z0,z2,z4,z5,z785,z6]),(0,[z265,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z786]),(0,[z0,z3,z4,z195,z169,z82]),(0,[z0,z2,z4,z195,z170,z82]),(0,[z265,z0,z2,z5,z269,z6])],[(0,[z0,z787,z3,z4,z5,z6]),(0,[z0,z2,z37,z393,z5,z6]),(0,[z788,z2,z3,z4,z5,z6])],[(0,[z173,z0,z2,z3,z75,z5]),(0,[z0,z2,z3,z4,z789,z6]),(0,[z0,z2,z3,z4,z5,z326]),(0,[z0,z2,z4,z790,z5,z6])]],
   [[(0,[z0,z1,z233,z4,z5,z6]),(0,[z0,z2,z723,z4,z5,z6]),(0,[z0,z2,z791,z3,z5,z6]),(0,[z0,z2,z3,z792,z5,z6]),(0,[z34,z0,z2,z3,z5,z668])],[(0,[z119,z91,z3,z26,z5,z6]),(0,[z0,z2,z3,z4,z5,z793]),(0,[z794,z2,z3,z4,z5,z6]),(0,[z0,z664,z3,z4,z5,z158]),(0,[z0,z2,z4,z6,z795,z259]),(0,[z0,z2,z35,z272,z5,z69])],[(0,[z0,z334,z3,z4,z5,z6]),(0,[z0,z2,z796,z4,z5,z6]),(0,[z2,z3,z711,z19,z5,z6]),(0,[z242,z2,z320,z4,z5,z6]),(0,[z102,z0,z3,z4,z326,z63]),(0,[z0,z159,z3,z392,z5,z158])],[(0,[z0,z2,z4,z5,z47,z639]),(0,[z7,z227,z0,z2,z5,z6]),(0,[z0,z2,z3,z35,z448,z5]),(0,[z20,z2,z3,z4,z5,z767])],[(0,[z0,z2,z3,z797,z5,z6]),(0,[z437,z0,z2,z4,z285,z5]),(0,[z0,z2,z3,z5,z798,z6]),(0,[z0,z2,z799,z4,z5,z6]),(0,[z0,z2,z800,z4,z5,z6]),(0,[z0,z2,z3,z6,z715,z279]),(0,[z265,z0,z2,z4,z195,z82])],[],[(0,[z437,z16,z2,z3,z19,z5])],[(0,[z218,z0,z2,z46,z5,z6])]],
   [[(0,[z0,z3,z4,z5,z6,z801]),(0,[z802,z0,z2,z3,z4,z5]),(0,[z803,z0,z2,z4,z5,z6]),(1,[z2,z3,z4,z5,z767]),(0,[z0,z2,z3,z4,z5,z804]),(0,[z0,z113,z233,z18,z5,z6]),(0,[z805,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z806])],[(0,[z0,z2,z3,z5,z6,z807]),(0,[z437,z0,z2,z3,z28,z5]),(0,[z0,z2,z808,z4,z5,z6])],[(0,[z0,z2,z809,z4,z5,z6]),(0,[z810,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z811]),(0,[z0,z2,z28,z266,z5,z6]),(0,[z70,z2,z4,z5,z6,z673]),(0,[z60,z0,z2,z3,z302,z5]),(0,[z0,z2,z3,z812,z5,z6])],[(0,[z0,z2,z3,z4,z813,z6])],[(0,[z437,z0,z2,z3,z18,z5]),(0,[z0,z2,z814,z4,z5,z6]),(0,[z0,z2,z3,z39,z129,z6])],[(0,[z0,z2,z3,z815,z5,z6])],[(0,[z0,z2,z3,z816,z5,z6]),(0,[z17,z2,z3,z711,z5,z6]),(0,[z817,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z818,z5,z6]),(0,[z0,z2,z3,z819,z5,z6]),(0,[z820,z2,z3,z4,z5,z6])]],
   [[(0,[z16,z2,z3,z711,z5,z6]),(0,[z0,z2,z3,z821,z5,z6]),(0,[z102,z0,z3,z4,z6,z63])],[(0,[z365,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z822,z5,z6]),(0,[z0,z2,z51,z266,z5,z6]),(0,[z0,z727,z151,z4,z5,z6]),(0,[z0,z2,z4,z5,z170,z6])],[(0,[z258,z2,z51,z4,z5,z6]),(0,[z149,z0,z2,z4,z5,z54])],[(0,[z0,z2,z3,z823,z5,z6]),(0,[z2,z723,z51,z4,z5,z6]),(0,[z0,z824,z3,z4,z5,z6]),(0,[z16,z2,z3,z238,z19,z5]),(0,[z34,z577,z0,z2,z3,z5]),(0,[z102,z242,z3,z4,z6,z63]),(0,[z0,z2,z825,z4,z5,z6])],[(0,[z378,z0,z2,z37,z5,z6]),(0,[z0,z2,z3,z826,z5,z6]),(0,[z0,z2,z827,z4,z5,z6])],[(0,[z188,z0,z2,z266,z5,z6]),(0,[z0,z2,z3,z4,z828,z6]),(0,[z372,z2,z3,z211,z5,z6]),(0,[z0,z2,z3,z4,z6,z714])],[(0,[z0,z2,z109,z211,z5,z6]),(0,[z0,z3,z4,z103,z6,z714]),(0,[z0,z2,z3,z5,z6,z829]),(0,[z0,z2,z4,z5,z6,z768]),(0,[z316,z81,z2,z3,z5,z6])],[(0,[z0,z2,z3,z4,z830,z6]),(0,[z372,z2,z109,z4,z5,z6])]],
   [[(0,[z56,z0,z2,z266,z5,z6]),(0,[z0,z2,z3,z5,z6,z831]),(0,[z0,z2,z320,z211,z5,z6]),(0,[z0,z2,z832,z4,z5,z6]),(0,[z833,z2,z3,z4,z5,z6])],[(0,[z0,z2,z834,z4,z5,z6]),(0,[z835,z2,z3,z4,z5,z6]),(0,[z372,z2,z320,z4,z5,z6]),(0,[z416,z0,z3,z4,z5,z311]),(0,[z2,z836,z3,z4,z5,z6])],[(0,[z837,z0,z2,z3,z5,z6]),(0,[z316,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z118]),(0,[z838,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z195,z269,z82])],[(0,[z0,z2,z3,z839,z5,z6]),(0,[z554,z2,z3,z19,z5,z6]),(0,[z0,z2,z840,z4,z5,z6]),(0,[z60,z227,z0,z2,z3,z5]),(0,[z2,z243,z3,z235,z5,z6])],[(0,[z521,z91,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z841]),(0,[z68,z0,z2,z3,z505,z6]),(0,[z34,z0,z2,z3,z5,z842])],[(0,[z1,z713,z3,z4,z5,z6]),(0,[z0,z334,z124,z4,z5,z6]),(0,[z0,z2,z124,z19,z5,z6]),(0,[z0,z2,z4,z843,z5,z6]),(0,[z0,z2,z3,z4,z5,z311])],[(0,[z844,z0,z2,z3,z5,z6]),(0,[z0,z2,z845,z4,z5,z6]),(0,[z258,z56,z0,z2,z5,z6])],[(0,[z220,z2,z192,z4,z5,z6]),(0,[z0,z2,z846,z4,z5,z6]),(0,[z67,z0,z151,z4,z5,z6]),(0,[z847,z0,z2,z3,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z848,z6]),(0,[z34,z0,z2,z3,z5,z318]),(0,[z0,z2,z53,z302,z5,z47])],[(0,[z149,z593,z0,z2,z4,z5]),(0,[z188,z0,z2,z46,z5,z6])],[(0,[z0,z2,z3,z849,z5,z6]),(0,[z0,z113,z3,z328,z5,z6]),(0,[z0,z2,z850,z4,z5,z6])],[(0,[z0,z2,z3,z851,z5,z6]),(0,[z0,z2,z3,z4,z5,z852]),(0,[z0,z853,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z854]),(0,[z0,z2,z53,z4,z5,z47])],[(0,[z0,z2,z3,z855,z5,z6]),(0,[z0,z2,z28,z532,z5,z6]),(0,[z856,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z235,z5,z6]),(0,[z857,z2,z3,z4,z5,z6]),(0,[z56,z0,z2,z46,z5,z6])],[(0,[z0,z2,z3,z4,z5,z858]),(0,[z0,z3,z4,z6,z714,z63]),(0,[z0,z159,z467,z4,z5,z158])],[(0,[z0,z2,z859,z4,z5,z6])],[(0,[z860,z0,z2,z3,z5,z6]),(0,[z275,z2,z3,z4,z6,z766]),(0,[z0,z3,z4,z5,z158,z311])]],
   [[(0,[z0,z861,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z862]),(0,[z437,z16,z0,z2,z3,z5]),(0,[z0,z2,z863,z4,z5,z6]),(0,[z810,z0,z2,z3,z4,z82])],[(0,[z705,z2,z3,z29,z5,z6]),(0,[z0,z113,z3,z18,z5,z6]),(0,[z0,z2,z4,z5,z864,z6]),(0,[z0,z2,z865,z4,z5,z6])],[(0,[z159,z243,z3,z4,z5,z158]),(0,[z66,z0,z2,z4,z6,z259]),(0,[z0,z2,z4,z5,z866,z6])],[(0,[z0,z2,z3,z867,z5,z6]),(0,[z0,z2,z3,z757,z5,z6])],[(0,[z0,z868,z3,z4,z5,z6])],[(0,[z15,z2,z3,z4,z6,z84]),(0,[z0,z2,z3,z266,z5,z6]),(0,[z0,z2,z3,z4,z5,z869]),(0,[z0,z2,z870,z4,z5,z6])],[(0,[z871,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z872,z5,z6]),(0,[z0,z2,z3,z5,z6,z873]),(0,[z874,z2,z3,z4,z5,z6])],[(0,[z60,z2,z3,z4,z5,z767]),(0,[z0,z421,z151,z4,z5,z6]),(0,[z0,z2,z3,z875,z5,z6]),(0,[z0,z3,z876,z4,z5,z6]),(0,[z149,z0,z2,z175,z5,z6])]],
   [[(0,[z877,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z878,z5,z6]),(0,[z0,z879,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z880,z5]),(0,[z881,z0,z3,z4,z5,z6]),(0,[z0,z2,z882,z4,z5,z6])],[(0,[z0,z1,z3,z85,z5,z6]),(0,[z188,z0,z2,z4,z238,z5]),(0,[z2,z3,z4,z5,z21,z518]),(0,[z0,z2,z3,z4,z5,z767]),(0,[z883,z2,z3,z4,z5,z6]),(0,[z216,z0,z3,z38,z5,z6])],[(0,[z0,z2,z884,z4,z5,z6]),(0,[z0,z2,z885,z4,z5,z6]),(0,[z0,z2,z3,z886,z5,z6])],[(0,[z0,z2,z887,z4,z5,z6])],[(0,[z0,z2,z3,z888,z4,z5]),(0,[z0,z889,z3,z4,z5,z6]),(0,[z0,z2,z3,z143,z5,z6]),(0,[z56,z0,z2,z388,z5,z6]),(0,[z0,z2,z4,z185,z6,z795])],[(0,[z0,z2,z890,z4,z5,z6]),(0,[z0,z191,z3,z244,z5,z6]),(0,[z173,z121,z0,z2,z4,z5]),(0,[z83,z2,z3,z4,z309,z6])],[(0,[z92,z0,z3,z4,z5,z158]),(0,[z0,z2,z3,z35,z5,z69])]],
   [[(0,[z132,z713,z3,z4,z5,z6]),(0,[z0,z2,z3,z891,z5,z6]),(0,[z2,z243,z467,z4,z5,z6])],[(0,[z0,z2,z892,z4,z5,z6]),(0,[z149,z0,z2,z4,z5,z300]),(0,[z378,z0,z2,z3,z303,z5]),(0,[z60,z7,z0,z2,z4,z5]),(0,[z2,z3,z4,z5,z21,z767]),(0,[z2,z893,z3,z4,z5,z6]),(0,[z0,z2,z894,z4,z5,z6])],[(0,[z0,z2,z3,z895,z5,z6]),(0,[z0,z2,z3,z4,z5,z896]),(0,[z350,z0,z2,z3,z6,z279]),(0,[z0,z2,z3,z897,z5,z6]),(0,[z149,z0,z2,z4,z5,z305])],[(0,[z0,z2,z3,z898,z5,z6]),(0,[z899,z0,z2,z3,z5,z6]),(0,[z0,z334,z3,z5,z69,z6]),(1,[z810,z0,z2,z3,z4])],[(0,[z0,z2,z3,z900,z5,z6]),(0,[z0,z901,z3,z4,z5,z6]),(0,[z0,z2,z902,z4,z5,z6])],[(0,[z0,z3,z18,z757,z5,z6]),(0,[z0,z2,z3,z39,z455,z6])],[(0,[z0,z2,z3,z4,z5,z903]),(0,[z904,z2,z3,z4,z5,z6])],[(0,[z0,z91,z3,z354,z5,z6]),(0,[z0,z905,z3,z4,z5,z6]),(0,[z0,z2,z906,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z907])]],
   [[(0,[z0,z2,z3,z4,z5,z908]),(0,[z0,z2,z3,z909,z5,z6]),(0,[z685,z2,z3,z29,z5,z6]),(0,[z0,z564,z2,z46,z5,z6]),(0,[z316,z3,z4,z5,z169,z6]),(0,[z316,z2,z4,z5,z170,z6])],[(0,[z0,z2,z910,z4,z5,z6]),(0,[z713,z91,z3,z4,z5,z6]),(0,[z0,z2,z911,z4,z5,z6]),(0,[z2,z3,z4,z6,z766,z84]),(0,[z0,z2,z467,z4,z5,z6]),(0,[z0,z2,z912,z4,z5,z6])],[],[(0,[z0,z55,z683,z4,z5,z6]),(0,[z0,z321,z166,z4,z5,z6])],[(0,[z346,z91,z3,z4,z5,z6]),(0,[z0,z913,z3,z4,z5,z6]),(0,[z0,z2,z3,z914,z5,z6])],[(0,[z0,z2,z322,z354,z5,z6]),(0,[z0,z2,z3,z915,z4,z6]),(0,[z378,z0,z2,z151,z5,z6])],[(0,[z56,z0,z191,z4,z5,z6]),(0,[z0,z2,z916,z4,z5,z6]),(0,[z0,z2,z917,z4,z5,z6])],[(0,[z0,z2,z918,z4,z5,z6]),(0,[z919,z0,z2,z4,z5,z6]),(0,[z0,z2,z920,z4,z5,z6]),(0,[z0,z2,z3,z921,z5,z6]),(0,[z0,z2,z370,z28,z5,z6])]],
   [[(0,[z242,z2,z3,z4,z5,z6]),(0,[z0,z2,z289,z392,z5,z6]),(0,[z0,z2,z3,z922,z5,z6])],[(0,[z0,z2,z120,z4,z5,z6]),(0,[z0,z91,z322,z4,z5,z6])],[(0,[z0,z2,z3,z4,z238,z5]),(0,[z0,z923,z2,z3,z5,z6]),(0,[z0,z2,z924,z4,z5,z6]),(0,[z365,z2,z3,z235,z5,z6])],[(0,[z0,z2,z3,z925,z5,z6]),(0,[z0,z2,z3,z4,z5,z768])],[(0,[z0,z926,z3,z4,z5,z6]),(0,[z927,z2,z3,z4,z5,z6]),(0,[z0,z2,z146,z4,z6,z795])],[(0,[z0,z2,z3,z928,z5,z6]),(0,[z275,z2,z3,z4,z95,z6]),(0,[z0,z2,z46,z5,z692,z6])],[(0,[z2,z3,z4,z5,z6,z929])],[(0,[z81,z0,z2,z3,z5,z6])]],
   [[(0,[z0,z2,z120,z26,z5,z6]),(0,[z0,z2,z3,z5,z6,z930]),(0,[z0,z334,z296,z4,z5,z6]),(0,[z188,z0,z2,z38,z5,z6])],[(0,[z0,z2,z3,z931,z5,z6]),(0,[z437,z0,z2,z3,z46,z5]),(0,[z0,z2,z932,z4,z5,z6])],[(0,[z0,z2,z933,z4,z5,z6])],[(0,[z0,z2,z4,z934,z5,z6])],[(0,[z521,z2,z51,z4,z5,z6]),(0,[z34,z0,z2,z3,z5,z429]),(0,[z0,z2,z935,z4,z5,z6])],[(0,[z936,z0,z2,z4,z5,z6])],[(0,[z0,z937,z3,z4,z5,z6]),(0,[z0,z2,z272,z5,z69,z6])],[(0,[z56,z0,z334,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z938]),(0,[z227,z20,z0,z2,z3,z5])]],
   [[(0,[z119,z91,z120,z4,z5,z6]),(0,[z0,z2,z939,z4,z5,z6]),(0,[z121,z122,z51,z4,z5,z6]),(0,[z0,z2,z3,z288,z5,z6]),(0,[z2,z243,z3,z392,z5,z6])],[(0,[z0,z2,z4,z5,z6,z940]),(0,[z0,z2,z941,z4,z5,z6]),(0,[z92,z0,z4,z5,z170,z6])],[(0,[z489,z0,z3,z38,z5,z6]),(0,[z2,z3,z4,z5,z6,z942])],[(0,[z0,z2,z4,z5,z6,z943]),(0,[z0,z2,z3,z5,z6,z944]),(0,[z0,z2,z37,z124,z5,z6]),(0,[z945,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z158,z107])],[(0,[z0,z334,z3,z19,z5,z6]),(0,[z0,z2,z3,z946,z5,z6]),(0,[z947,z2,z3,z4,z5,z6]),(0,[z242,z2,z3,z4,z5,z326]),(0,[z0,z2,z4,z5,z6,z795])],[(0,[z0,z2,z3,z948,z5,z6]),(0,[z316,z2,z3,z5,z269,z6])],[(0,[z0,z2,z192,z266,z5,z6]),(0,[z378,z70,z0,z2,z5,z6]),(0,[z60,z7,z2,z4,z5,z61]),(0,[z152,z0,z727,z4,z5,z6]),(0,[z0,z2,z3,z211,z5,z6])],[(0,[z372,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z949,z5,z6]),(0,[z56,z0,z2,z124,z5,z6]),(0,[z0,z2,z950,z4,z5,z6])]],
   [[(0,[z0,z2,z951,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z952]),(1,[z0,z727,z4,z5,z6]),(0,[z0,z2,z109,z4,z5,z6]),(0,[z0,z77,z3,z38,z5,z6]),(0,[z97,z142,z0,z2,z3,z4]),(0,[z0,z2,z574,z46,z5,z6]),(1,[z0,z2,z4,z6,z795]),(0,[z81,z0,z2,z5,z170,z6])],[(0,[z0,z2,z953,z4,z5,z6]),(0,[z0,z2,z3,z392,z5,z6]),(0,[z265,z2,z4,z5,z6,z118])],[(0,[z60,z2,z3,z4,z5,z653]),(0,[z0,z2,z4,z5,z6,z954]),(0,[z0,z2,z3,z5,z69,z511]),(0,[z102,z372,z3,z4,z6,z63]),(0,[z0,z2,z3,z5,z955,z6])],[(0,[z7,z20,z0,z2,z4,z5]),(0,[z956,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z5,z842])],[(0,[z316,z2,z3,z4,z195,z82])],[(0,[z957,z0,z2,z3,z5,z6]),(0,[z0,z2,z4,z5,z768,z54])],[(0,[z0,z2,z3,z4,z5,z958]),(0,[z0,z2,z4,z5,z6,z959]),(0,[z0,z2,z3,z960,z5,z6])],[(0,[z0,z2,z961,z4,z5,z6]),(0,[z0,z191,z28,z4,z5,z6]),(0,[z962,z0,z3,z4,z5,z6])]],
   [[(0,[z0,z122,z3,z244,z5,z6]),(0,[z0,z963,z3,z4,z5,z6]),(0,[z60,z168,z2,z3,z4,z5]),(0,[z0,z366,z3,z18,z5,z6])],[(0,[z121,z191,z51,z4,z5,z6]),(0,[z188,z0,z2,z28,z5,z6]),(0,[z92,z81,z0,z3,z5,z6])],[(0,[z964,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z965]),(0,[z0,z2,z966,z4,z5,z6]),(0,[z0,z2,z3,z967,z5,z6])],[(0,[z0,z640,z3,z18,z5,z6]),(0,[z2,z3,z4,z5,z6,z968]),(0,[z0,z3,z4,z969,z5,z6]),(0,[z34,z0,z2,z272,z5,z6])],[(0,[z0,z2,z3,z970,z5,z6]),(0,[z0,z2,z3,z288,z5,z326]),(0,[z66,z0,z2,z4,z6,z795]),(0,[z0,z3,z5,z269,z169,z6]),(0,[z0,z2,z5,z269,z170,z6])],[(0,[z554,z91,z3,z4,z5,z6]),(0,[z0,z191,z51,z4,z5,z6]),(0,[z971,z0,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z972,z6]),(0,[z0,z191,z4,z5,z47,z6]),(0,[z2,z3,z4,z711,z5,z6]),(0,[z56,z0,z2,z667,z5,z6]),(0,[z2,z3,z4,z973,z5,z6])],[(0,[z0,z2,z3,z5,z6,z974]),(0,[z0,z55,z166,z85,z5,z6]),(0,[z0,z2,z3,z975,z5,z6]),(0,[z92,z0,z3,z4,z5,z337]),(0,[z0,z2,z621,z28,z5,z6])]],
   [[(0,[z0,z976,z3,z4,z5,z6]),(0,[z16,z188,z2,z19,z5,z6]),(0,[z0,z2,z3,z977,z5,z6]),(0,[z0,z2,z147,z4,z5,z6])],[(0,[z173,z0,z2,z151,z4,z5]),(0,[z17,z2,z3,z5,z6,z469]),(0,[z0,z396,z166,z4,z5,z6])],[(0,[z121,z378,z2,z51,z5,z6]),(0,[z0,z2,z3,z75,z303,z5]),(0,[z0,z2,z3,z978,z5,z6]),(0,[z0,z2,z3,z979,z5,z6]),(0,[z0,z2,z4,z185,z314,z6]),(0,[z980,z0,z3,z4,z5,z6]),(0,[z81,z0,z3,z5,z169,z6])],[(0,[z119,z713,z3,z4,z5,z6]),(0,[z372,z2,z3,z4,z5,z326]),(1,[z0,z3,z4,z5,z707]),(0,[z0,z2,z250,z35,z5,z69])],[(0,[z0,z2,z981,z4,z5,z6]),(0,[z0,z2,z109,z4,z5,z326]),(0,[z0,z2,z3,z129,z200,z6])],[(0,[z16,z2,z285,z19,z5,z6]),(0,[z437,z0,z2,z3,z4,z5]),(0,[z0,z2,z982,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z983]),(0,[z2,z3,z5,z269,z6,z118])],[(0,[z0,z91,z233,z4,z5,z6]),(0,[z984,z2,z3,z4,z5,z6]),(0,[z0,z2,z147,z18,z5,z6]),(0,[z92,z0,z3,z4,z5,z6]),(0,[z0,z3,z985,z4,z5,z6]),(0,[z92,z0,z3,z5,z269,z6])],[(0,[z636,z0,z3,z38,z5,z6])]],
   [[(0,[z0,z122,z3,z4,z5,z6]),(0,[z121,z2,z51,z244,z5,z6])],[(0,[z0,z2,z3,z986,z5,z6]),(1,[z2,z3,z4,z6,z766]),(0,[z0,z2,z440,z4,z5,z47]),(0,[z0,z2,z37,z700,z5,z6]),(0,[z0,z2,z4,z5,z6,z987]),(0,[z0,z2,z988,z4,z5,z6])],[(0,[z989,z2,z3,z4,z5,z6]),(0,[z242,z2,z3,z4,z5,z311]),(0,[z0,z2,z467,z235,z5,z6])],[(0,[z275,z2,z3,z4,z529,z6]),(0,[z0,z2,z3,z990,z5,z6]),(0,[z121,z2,z75,z51,z5,z6]),(0,[z0,z3,z4,z5,z6,z707]),(0,[z56,z0,z2,z696,z5,z6])],[(0,[z0,z2,z991,z3,z4,z6])],[(0,[z2,z3,z4,z95,z6,z766]),(0,[z102,z0,z3,z288,z6,z63]),(0,[z149,z0,z2,z4,z5,z460]),(0,[z0,z2,z3,z992,z5,z6]),(0,[z92,z0,z3,z4,z195,z82])],[(0,[z0,z993,z3,z4,z5,z6]),(0,[z378,z0,z2,z3,z5,z6]),(0,[z533,z0,z2,z4,z6,z259]),(0,[z0,z2,z3,z175,z5,z6]),(0,[z0,z2,z3,z5,z994,z6]),(0,[z0,z995,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z69,z57])],[(0,[z60,z227,z2,z3,z5,z61])]],
   [[(0,[z60,z2,z4,z5,z189,z61]),(0,[z0,z2,z3,z996,z5,z6]),(1,[z0,z2,z720,z5,z6])],[(0,[z997,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z303,z4,z5]),(0,[z0,z2,z4,z998,z5,z6])],[(0,[z0,z2,z3,z999,z5,z6]),(0,[z0,z2,z1000,z4,z5,z6]),(0,[z0,z2,z1001,z4,z5,z6]),(0,[z1002,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1003]),(0,[z173,z0,z2,z37,z4,z5]),(0,[z60,z2,z3,z4,z5,z294]),(0,[z2,z3,z4,z5,z6,z766]),(0,[z0,z115,z3,z38,z5,z6]),(0,[z0,z2,z4,z720,z5,z6])],[(0,[z1004,z0,z2,z3,z4,z5]),(0,[z3,z4,z5,z169,z6,z118])],[(0,[z102,z0,z109,z4,z6,z63])],[(0,[z149,z0,z191,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1005]),(0,[z1006,z2,z3,z4,z5,z6]),(0,[z102,z0,z3,z4,z312,z6]),(0,[z2,z3,z4,z195,z118,z82])],[(0,[z365,z2,z3,z392,z5,z6]),(0,[z0,z2,z4,z5,z47,z167])]],
   [[(0,[z258,z2,z3,z19,z5,z6]),(0,[z2,z3,z1007,z4,z5,z6]),(0,[z0,z2,z3,z39,z6,z715]),(0,[z0,z2,z3,z4,z5,z842])],[(0,[z0,z191,z3,z4,z5,z6]),(0,[z132,z498,z3,z4,z5,z6]),(0,[z188,z17,z0,z2,z5,z6]),(0,[z265,z81,z0,z2,z5,z6])],[(0,[z173,z70,z0,z2,z4,z5]),(0,[z0,z2,z3,z5,z6,z1008]),(0,[z0,z2,z3,z4,z5,z1009]),(0,[z0,z2,z1010,z4,z5,z6]),(0,[z0,z2,z3,z288,z5,z311])],[(0,[z1011,z0,z2,z4,z5,z6]),(0,[z378,z0,z2,z166,z5,z6]),(0,[z16,z2,z3,z19,z5,z6]),(0,[z0,z2,z124,z29,z5,z6])],[(0,[z132,z1,z3,z4,z5,z6]),(0,[z16,z306,z3,z19,z5,z6]),(0,[z20,z2,z3,z4,z523,z5]),(0,[z0,z2,z151,z143,z5,z6]),(0,[z0,z2,z1012,z4,z5,z6])],[(0,[z0,z334,z37,z3,z5,z6]),(0,[z0,z2,z3,z1013,z5,z6]),(0,[z2,z3,z4,z5,z6,z1014]),(0,[z1015,z2,z3,z4,z5,z6])],[(0,[z0,z2,z37,z374,z5,z6]),(0,[z0,z2,z1016,z4,z5,z6]),(0,[z1017,z0,z2,z3,z5,z6])],[(0,[z0,z2,z3,z1018,z5,z6])]],
   [[(0,[z0,z2,z4,z285,z5,z6]),(0,[z0,z2,z1019,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1020]),(0,[z34,z315,z0,z2,z3,z5])],[(0,[z20,z0,z2,z250,z4,z5]),(0,[z0,z3,z757,z38,z5,z6])],[(0,[z0,z1021,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1022,z6]),(0,[z60,z2,z3,z5,z41,z61]),(0,[z0,z2,z3,z1023,z5,z6])],[(0,[z0,z2,z3,z354,z5,z6]),(0,[z121,z2,z303,z51,z4,z5])],[(0,[z0,z2,z3,z1024,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1025]),(0,[z0,z2,z3,z1026,z5,z6]),(0,[z2,z3,z4,z5,z767,z61]),(0,[z0,z2,z3,z1027,z5,z6]),(0,[z316,z265,z2,z4,z5,z6])],[(0,[z16,z2,z296,z19,z5,z6])],[(0,[z575,z0,z151,z4,z5,z6]),(0,[z194,z810,z0,z2,z3,z4])]],
   [[(0,[z454,z1,z3,z4,z5,z6]),(0,[z0,z2,z3,z244,z5,z6]),(0,[z0,z2,z1028,z4,z5,z6]),(0,[z20,z2,z3,z651,z4,z5]),(0,[z0,z2,z3,z5,z842,z329])],[(0,[z16,z564,z2,z3,z5,z6]),(0,[z0,z2,z339,z46,z5,z6]),(0,[z66,z0,z2,z4,z267,z6]),(0,[z0,z2,z53,z4,z5,z768]),(0,[z81,z0,z2,z3,z195,z82])],[(0,[z0,z2,z1029,z4,z5,z6]),(0,[z0,z2,z1030,z4,z5,z6]),(0,[z0,z2,z1031,z4,z5,z6]),(1,[z0,z2,z3,z5,z842])],[(0,[z149,z0,z2,z266,z5,z6]),(0,[z0,z2,z1032,z4,z5,z6]),(0,[z142,z810,z0,z2,z3,z4])],[(0,[z0,z2,z4,z5,z6,z1033])],[(0,[z0,z2,z322,z4,z5,z6]),(0,[z0,z3,z727,z4,z5,z6])],[(0,[z437,z0,z2,z3,z38,z5]),(0,[z0,z2,z4,z1034,z5,z6]),(0,[z1035,z2,z3,z4,z5,z6]),(0,[z81,z2,z3,z5,z6,z118])],[(0,[z50,z0,z3,z38,z5,z6]),(0,[z0,z2,z1036,z4,z5,z6]),(0,[z0,z2,z3,z1037,z5,z6]),(0,[z34,z0,z334,z3,z5,z6]),(0,[z0,z2,z1038,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z842])]],
   [[(1,[z2,z3,z711,z5,z6]),(0,[z0,z2,z394,z28,z5,z6]),(0,[z1039,z2,z3,z4,z5,z6]),(0,[z0,z2,z1040,z4,z5,z6]),(0,[z810,z0,z2,z3,z4,z5])],[(0,[z2,z3,z29,z711,z5,z6]),(0,[z0,z55,z166,z4,z5,z6]),(0,[z416,z0,z3,z4,z5,z707]),(0,[z0,z2,z3,z1041,z5,z6]),(0,[z1042,z0,z2,z3,z5,z6])],[(0,[z119,z91,z3,z354,z5,z6])],[(1,[z713,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z766]),(0,[z0,z507,z3,z38,z5,z6])],[(0,[z0,z2,z322,z26,z5,z6]),(0,[z1043,z0,z2,z4,z5,z6]),(0,[z149,z0,z2,z503,z4,z5]),(0,[z0,z516,z151,z4,z5,z6]),(0,[z0,z2,z146,z4,z154,z6])],[(0,[z0,z2,z320,z4,z5,z6]),(0,[z0,z2,z1044,z4,z5,z6]),(0,[z92,z265,z0,z4,z5,z6]),(0,[z0,z2,z3,z1045,z5,z6])],[(0,[z378,z0,z2,z124,z5,z6]),(0,[z16,z2,z124,z19,z5,z6]),(0,[z0,z113,z3,z757,z5,z6])],[(0,[z0,z2,z4,z1046,z5,z6]),(0,[z34,z0,z2,z124,z5,z6])]],
   [[(0,[z0,z91,z3,z85,z5,z6]),(0,[z0,z1047,z3,z4,z5,z6]),(0,[z92,z0,z3,z4,z5,z311])],[(0,[z0,z2,z3,z4,z5,z1048]),(0,[z0,z1049,z3,z4,z5,z6])],[(0,[z0,z2,z3,z5,z6,z1050]),(0,[z0,z2,z266,z5,z47,z6]),(0,[z1051,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z249,z82]),(0,[z365,z2,z467,z4,z5,z6])],[(0,[z1052,z0,z2,z3,z5,z6]),(0,[z173,z0,z2,z4,z46,z5]),(0,[z0,z2,z37,z28,z5,z6]),(0,[z34,z0,z2,z3,z5,z329])],[(0,[z119,z91,z322,z4,z5,z6]),(0,[z0,z2,z1053,z4,z5,z6])],[(0,[z2,z3,z723,z4,z5,z6]),(0,[z0,z468,z166,z4,z5,z6]),(0,[z0,z2,z3,z358,z5,z69]),(0,[z0,z2,z28,z720,z5,z6])],[(0,[z378,z0,z2,z46,z5,z6]),(0,[z34,z0,z2,z3,z402,z5]),(0,[z0,z2,z53,z256,z4,z5]),(0,[z0,z113,z147,z18,z5,z6]),(0,[z0,z1054,z3,z4,z5,z6]),(0,[z0,z2,z37,z436,z5,z6])],[(0,[z0,z2,z3,z1055,z5,z6]),(0,[z121,z479,z2,z4,z5,z6]),(0,[z0,z1056,z3,z4,z5,z6]),(0,[z0,z2,z3,z1057,z5,z6]),(0,[z0,z3,z4,z5,z158,z707]),(0,[z0,z2,z3,z4,z6,z795])]],
   [[(0,[z0,z2,z3,z4,z5,z1058])],[(0,[z502,z91,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z41]),(0,[z0,z2,z4,z5,z6,z1059]),(0,[z0,z2,z1060,z4,z5,z6])],[],[(0,[z0,z3,z4,z5,z707,z337])],[(0,[z70,z2,z4,z473,z5,z6])],[(0,[z17,z2,z3,z29,z5,z6]),(0,[z7,z0,z2,z5,z6,z41]),(0,[z2,z1061,z3,z4,z5,z6]),(0,[z242,z2,z3,z288,z5,z6]),(0,[z0,z2,z3,z211,z5,z326])],[(0,[z0,z2,z3,z1062,z5,z6]),(0,[z0,z321,z3,z18,z5,z6]),(0,[z0,z159,z289,z4,z5,z158]),(0,[z0,z2,z37,z720,z5,z6]),(0,[z0,z2,z53,z175,z5,z47]),(0,[z0,z2,z4,z5,z6,z1063])],[(0,[z1064,z0,z2,z3,z5,z6]),(0,[z0,z2,z1065,z4,z5,z6]),(0,[z0,z2,z467,z392,z5,z6])]],
   [[(0,[z0,z2,z1066,z4,z5,z6]),(0,[z0,z2,z1067,z4,z5,z6]),(0,[z0,z2,z4,z1068,z5,z6]),(0,[z1069,z0,z2,z3,z4,z6]),(0,[z1070,z0,z3,z4,z5,z6]),(0,[z0,z1071,z3,z4,z5,z6]),(0,[z0,z2,z1072,z4,z5,z6]),(0,[z56,z0,z2,z684,z5,z6]),(0,[z1073,z0,z2,z3,z4,z5])],[(0,[z83,z2,z3,z4,z6,z84]),(0,[z0,z1074,z3,z4,z5,z6]),(0,[z0,z2,z3,z85,z5,z6]),(0,[z0,z2,z320,z4,z5,z326]),(0,[z149,z0,z2,z4,z5,z768])],[(0,[z0,z2,z3,z1075,z5,z6]),(0,[z0,z191,z192,z4,z5,z6]),(0,[z0,z122,z3,z266,z5,z6]),(0,[z0,z3,z4,z5,z6,z1076]),(0,[z17,z2,z3,z353,z5,z6]),(0,[z1077,z0,z2,z3,z5,z6]),(0,[z56,z0,z2,z720,z5,z6]),(0,[z1078,z0,z2,z4,z5,z6])],[(0,[z0,z2,z3,z1079,z5,z6]),(0,[z242,z2,z3,z211,z5,z6])],[],[(0,[z0,z2,z1080,z4,z5,z6]),(0,[z60,z0,z2,z250,z4,z5]),(0,[z242,z2,z109,z4,z5,z6]),(0,[z0,z2,z146,z4,z185,z6])],[(0,[z0,z2,z4,z5,z6,z1081]),(0,[z0,z2,z3,z1082,z5,z6]),(0,[z0,z4,z5,z170,z169,z6])],[(0,[z1083,z0,z2,z4,z5,z6]),(0,[z221,z0,z151,z4,z5,z6]),(0,[z1084,z0,z2,z3,z5,z6])]],
   [[(0,[z0,z166,z727,z4,z5,z6])],[(0,[z0,z2,z1085,z4,z5,z6]),(0,[z0,z1086,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z69,z842])],[(0,[z0,z2,z3,z5,z6,z1087])],[(0,[z0,z2,z124,z4,z5,z6]),(0,[z0,z2,z3,z1088,z5,z6])],[(0,[z0,z1089,z3,z4,z5,z6]),(0,[z0,z2,z3,z1090,z5,z6]),(0,[z0,z306,z124,z4,z5,z6]),(0,[z0,z1091,z3,z4,z5,z6]),(0,[z0,z2,z3,z129,z6,z715])],[(0,[z0,z2,z3,z4,z5,z1092]),(0,[z0,z2,z3,z1093,z5,z6]),(0,[z0,z159,z3,z235,z5,z158]),(0,[z810,z0,z2,z3,z4,z195])],[(0,[z1094,z0,z2,z3,z4,z5]),(0,[z0,z2,z4,z1095,z5,z6]),(0,[z102,z0,z3,z211,z6,z63]),(0,[z0,z62,z3,z4,z6,z714]),(0,[z0,z2,z3,z4,z5,z1096]),(0,[z0,z3,z4,z5,z6,z1097]),(0,[z1098,z2,z3,z4,z5,z6]),(0,[z0,z2,z1099,z4,z5,z6])],[(0,[z0,z2,z3,z5,z6,z1100]),(0,[z2,z1101,z3,z4,z5,z6]),(0,[z2,z4,z5,z170,z6,z118])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 548) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 548).take 526) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1074)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [548, 526] = true :=
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

end PEqualNP.Outside.L_meta_47108

theorem PEqualNP.Outside.L_meta_47108 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241888 * 2 ^ 32 + 3940608640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241888 * 2 ^ 32 + 3940608640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_47108.solve