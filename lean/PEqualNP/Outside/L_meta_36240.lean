import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36240

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
  Nat.testBit (4277074666 * 2 ^ 32 + 4272618152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x4004000001001025#64 ++ 0xfffb09118f03f0ff#64 : BitVec 128),
   (0xa4f81269348d4c92#64 ++ 0xf6f636e9749d4c93#64 : BitVec 128),
   (0x0a90470258a18518#64 ++ 0x2fafc70e78e18f1c#64 : BitVec 128),
   (0x0420b80d80560ac0#64 ++ 0x3d9ff80f80fe0fe0#64 : BitVec 128),
   (0x08c0efb000fbe000#64 ++ 0x1c7efff000fff000#64 : BitVec 128),
   (0x0f00fddfee000000#64 ++ 0x03feffffff000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [13, 12]⟩, ⟨.and, [9, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x0040a8b0005a6000 0x105038f0001e7000

def z1 : W := mkw 0x0420b80d80560ac0 0x3d9ff80f80fe0fe0

def z2 : W := mkw 0x08c0efb000fbe000 0x1c7efff000fff000

def z3 : W := mkw 0x0a90470258a18518 0x2fafc70e78e18f1c

def z4 : W := mkw 0x0f20fddfee560ac0 0x3ffffffffffe0fe0

def z5 : W := mkw 0x4004000001001025 0xfffb09118f03f0ff

def z6 : W := mkw 0xa4f81269348d4c92 0xf6f636e9749d4c93

def z7 : W := mkw 0x0000a89000522000 0x0000081000023000

def z8 : W := mkw 0x0f00fddfee000000 0x03feffffff000000

def z9 : W := mkw 0x0420b80d80560ac0 0x0004f00e00fc0f00

def z10 : W := mkw 0xa4f8ba6db4df4ed2 0xfffffeeff4ff4ff3

def z11 : W := mkw 0x0000000000000000 0x03fa09118f000000

def z12 : W := mkw 0xa4f81269348d4c92 0xf40436e8709d4c93

def z13 : W := mkw 0x08c0efb000fbe000 0xfefefff104fff093

def z14 : W := mkw 0x0210000258000518 0x2f8fc00e78e00f1c

def z15 : W := mkw 0x0b0045d26e000000 0x026007f07f000000

def z16 : W := mkw 0xa4f81269348d4c92 0x000436e8709c0c00

def z17 : W := mkw 0xa0d8026034894412 0xf6f206e174014093

def z18 : W := mkw 0x0b00ed96ca000000 0x0108c9168b000000

def z19 : W := mkw 0x0000000000000000 0x2fab01000801801c

def z20 : W := mkw 0x4a94470259a1953d 0xffffcf1fffe3ffff

def z21 : W := mkw 0x0f0055dfee000000 0x03e007ffff000000

def z22 : W := mkw 0x00c0022000894000 0x147636e0009d4000

def z23 : W := mkw 0x0ce0ffbd80ffeac0 0x3dffffff80ffffe0

def z24 : W := mkw 0x00400020005a6000 0x10000000001e7000

def z25 : W := mkw 0x0800ed900072a000 0x0808c9100062b000

def z26 : W := mkw 0xacf8fff934ffec92 0xfefefff974fffc93

def z27 : W := mkw 0xa4681069240c4882 0xf6f230e1041d4093

def z28 : W := mkw 0x030000426e000000 0x020000007f000000

def z29 : W := mkw 0x0400104924000000 0x0280000974000000

def z30 : W := mkw 0x0b00ed96ca000000 0x017efff68b000000

def z31 : W := mkw 0x0500b8dda6000000 0x005038f187000000

def z32 : W := mkw 0x0f90ffdffea18518 0x2fffffffffe18f1c

def z33 : W := mkw 0x0500b8dda6000000 0x000030e000000000

def z34 : W := mkw 0x0000a80480520240 0x0909c80680620360

def z35 : W := mkw 0xacf8576934adcc92 0xfefef7e974fdcc93

def z36 : W := mkw 0x0420b80d80560ac0 0x3ffff91f8ffe0fe0

def z37 : W := mkw 0x0a90470258a18518 0x0e2ec70078e1801c

def z38 : W := mkw 0xacf857f934adec92 0xf6f637f9749dfc93

def z39 : W := mkw 0x0000000000000000 0x2d8fc00e00e00f00

def z40 : W := mkw 0xa4f81269348d4c92 0xd27036e1741d4093

def z41 : W := mkw 0x4424b80d81561ae5 0xfffff91f8fffffff

def z42 : W := mkw 0x40c4022001fbf025 0xfc01000000fff0ff

def z43 : W := mkw 0x0a80470248a18108 0x0d2fc70608e1830c

def z44 : W := mkw 0x4a94470259a1953d 0xffafc70e78e3ffff

def z45 : W := mkw 0x08c0efb000fbe000 0x1476f6e000fd4000

def z46 : W := mkw 0x0000a80000520000 0x1c1ef80000fe0000

def z47 : W := mkw 0x0f00fddfee520000 0x1ffefffffffe0000

def z48 : W := mkw 0x0b00edd26e000000 0x027efff07f000000

def z49 : W := mkw 0x0400b80d80000000 0x019ef80f80000000

def z50 : W := mkw 0x0ad0efb258fbe518 0x3ffffffe78ffff1c

def z51 : W := mkw 0x0a00450248000000 0x2fafc70e78e00f00

def z52 : W := mkw 0x0000000000000000 0x0c2a010000018000

def z53 : W := mkw 0x0000000000000000 0x1c7a09100003f000

def z54 : W := mkw 0x004000b000086000 0x004000f000007000

def z55 : W := mkw 0x0290020258a18518 0x2f81000e78e18f1c

def z56 : W := mkw 0x08c0efb000fbe000 0x080cfff000feb000

def z57 : W := mkw 0x4004000001001025 0x090909108b02b06c

def z58 : W := mkw 0x00e0022000ffeac0 0x3c01000000ffffe0

def z59 : W := mkw 0x0f20fddfee040ac0 0x23ffffffff000fe0

def z60 : W := mkw 0x0a00450248000000 0x03aec70e78000000

def z61 : W := mkw 0x0090020010a18518 0x0000000000e00f00

def z62 : W := mkw 0x08c0efb000fbe000 0x1ffefff18ffff000

def z63 : W := mkw 0x0eb0ff0fd8f78fd8 0x3fbfff0ff8ff8ffc

def z64 : W := mkw 0x010000d026000000 0x004000f007000000

def z65 : W := mkw 0x0a90470258a18518 0x3fbfcf0ff8e38ffc

def z66 : W := mkw 0xacf8fff9348d4c92 0xf6fefff9749d4c93

def z67 : W := mkw 0x4424b80d81561ae5 0x3d9ff91f8bfebfec

def z68 : W := mkw 0x0000000000000000 0x3d9b0801800200e0

def z69 : W := mkw 0x0000000000000000 0xc260000004014013

def z70 : W := mkw 0xa0d8026034894412 0xc26006e074014013

def z71 : W := mkw 0xe4fc1269358d5cb7 0xffff3ff9ff9ffcff

def z72 : W := mkw 0x0a00450248208108 0x0bafc70e7860830c

def z73 : W := mkw 0x0fc0ffffeea9e000 0x03feffffff01f000

def z74 : W := mkw 0x0000000000000000 0x10100801800200e0

def z75 : W := mkw 0x4f04fddfef001025 0xffffffffff03f0ff

def z76 : W := mkw 0x48c4efb001fbf025 0xde7efff00ffff01f

def z77 : W := mkw 0x0a90470258a18518 0x03aec70e78e00f00

def z78 : W := mkw 0x0420b80d80560ac0 0x10103801801e00e0

def z79 : W := mkw 0x0a90470258a18518 0x022007007801801c

def z80 : W := mkw 0x0400104924000000 0x02f636e974000000

def z81 : W := mkw 0x0a90470258a18518 0x0004c60e70e00f00

def z82 : W := mkw 0x0040a8b0005a6000 0x000030e0001c0000

def z83 : W := mkw 0xaef8576b7cadcd9a 0x2faff7ee78fd8f1c

def z84 : W := mkw 0xa048006024084002 0xc04000e004004003

def z85 : W := mkw 0x0000a80480000000 0x0108c80680000000

def z86 : W := mkw 0x0420100900040880 0xf6f63009049d4c93

def z87 : W := mkw 0x0000a80000520000 0x3d9ff80e00fe0f00

def z88 : W := mkw 0x0ad0472258a9c518 0x3ffff7ee78fdcf1c

def z89 : W := mkw 0x0fc0ffffee894000 0x17feffffff9d4000

def z90 : W := mkw 0xa4f81269348d4c92 0xfffff6ef74fd4f93

def z91 : W := mkw 0x0400104924000000 0xf6f636e974014093

def z92 : W := mkw 0x00c0022000fbe000 0x1c7636e000fff000

def z93 : W := mkw 0x0420100d80040ac0 0x2181000f80000fe0

def z94 : W := mkw 0xa0d8026034894412 0x000006e070000000

def z95 : W := mkw 0x0880470000a18000 0x0c2ec70000e18000

def z96 : W := mkw 0x4004000001001025 0xff8100018f03f0ff

def z97 : W := mkw 0x00c0022000894000 0x14000000009d4000

def z98 : W := mkw 0x0000000000000000 0x1472000000014000

def z99 : W := mkw 0x0720104fee040ac0 0x2381000fff000fe0

def z100 : W := mkw 0x0000000000000000 0x1ffa09118f03f000

def z101 : W := mkw 0xa0f80220108d4c92 0xf47636e0009d4c93

def z102 : W := mkw 0xaff8fffffeadcd9a 0xfffffffffffdcf9f

def z103 : W := mkw 0xa4681069240c4882 0x000030e0001c0000

def z104 : W := mkw 0xeffcffffff8d5cb7 0xffffffffff9ffcff

def z105 : W := mkw 0x0420b80d80040880 0x359ef80f809c0c80

def z106 : W := mkw 0x0b0045924a000000 0x000001100b000000

def z107 : W := mkw 0xa4681069240c4882 0xd05030e1041c4083

def z108 : W := mkw 0x0a10450258208518 0x2b89c10e78608f1c

def z109 : W := mkw 0x00c0aab000fbe000 0x1c5038f000fff000

def z110 : W := mkw 0x0520b8dda6560ac0 0x3ddff8ff87fe0fe0

def z111 : W := mkw 0x4a94470259a1953d 0x2fafcf1efbe3bf7c

def z112 : W := mkw 0xa4f8126db48d4ed2 0xf7f736eff49d4ff3

def z113 : W := mkw 0xa4f81269348d4c92 0xffff3ee9f49f4cf3

def z114 : W := mkw 0x0420100900040880 0x34963009009c0c80

def z115 : W := mkw 0x0a00450248208108 0x0909c1060860830c

def z116 : W := mkw 0xa468b86da45e4ac2 0xfddff8ef84fe4fe3

def z117 : W := mkw 0x00c0022000fbe000 0x1c7a091000fff000

def z118 : W := mkw 0x0000000000000000 0x0000000000000000

def z119 : W := mkw 0x0210000258000518 0x2381000e78000f1c

def z120 : W := mkw 0x0090020010810410 0xf6f6060974814c93

def z121 : W := mkw 0x0b00edd6ee000000 0x0368cff6ff000000

def z122 : W := mkw 0x48c4efb001fbf025 0xfffffff18ffff0ff

def z123 : W := mkw 0x0090020010a18518 0x2c01000000e18f1c

def z124 : W := mkw 0x4094020011a1953d 0xfffb09118fe3ffff

def z125 : W := mkw 0x0f00fddfee000000 0x02703ff1ff000000

def z126 : W := mkw 0x4a94470259a1953d 0xefefc71e7fe1ff1f

def z127 : W := mkw 0xaff8fffffe8d4c92 0xf7feffffff9d4c93

def z128 : W := mkw 0x0090020010810410 0x26a6060870810c10

def z129 : W := mkw 0x0420100d80040ac0 0x0000000e00000f00

def z130 : W := mkw 0x0a00450248000000 0x0220070078000000

def z131 : W := mkw 0x0f00fd9fca000000 0x019ef91f8b000000

def z132 : W := mkw 0x08c0efb000fbe000 0x0004f6e000fc0000

def z133 : W := mkw 0x0020000000560ac0 0x3d8fc00e00fe0fe0

def z134 : W := mkw 0x0040a8b0005a6000 0x1c7a39f0001ff000

def z135 : W := mkw 0x4004000001001025 0xc26001100f01f01f

def z136 : W := mkw 0x0ad047b258a9e518 0x2fefc7fe78e1ff1c

def z137 : W := mkw 0x4004000001001025 0xd0500811870270e3

def z138 : W := mkw 0x0840edb0007ae000 0x1858f9f0007ef000

def z139 : W := mkw 0x4004000001001025 0xfc0100000003f0ff

def z140 : W := mkw 0xafd8fffffe894412 0xc3feffffff014013

def z141 : W := mkw 0x0a00ed9248000000 0x03fefffe78000000

def z142 : W := mkw 0xacf8fff934ffec92 0xf6f6f6e974fd4c93

def z143 : W := mkw 0xacf8fffdb4ffeed2 0xfffffffff4fffff3

def z144 : W := mkw 0x0800ed900072a000 0x1c1ef91000feb000

def z145 : W := mkw 0x0020a80000560ac0 0x3c1ff80000fe0fe0

def z146 : W := mkw 0x4f94ffdfffa1953d 0xffffffffffe3ffff

def z147 : W := mkw 0x0eb0ff0fd8f78fd8 0x3d9ffe0ff0fe0fe0

def z148 : W := mkw 0x4044a8b0015a7025 0xfffb39f18f1ff0ff

def z149 : W := mkw 0x0700104fee000000 0x0380000fff000000

def z150 : W := mkw 0xa0f80220108d4c92 0xf4000000009d4c93

def z151 : W := mkw 0x08c0efb000fbe000 0x3ffffff008fff01c

def z152 : W := mkw 0x4094020011811435 0xffff0f19ff83fcff

def z153 : W := mkw 0xaef8576b7cadcd9a 0xfffff7ef7cfdcf9f

def z154 : W := mkw 0xe0fc0220118d5cb7 0xfffb09118f9ffcff

def z155 : W := mkw 0x0420b80d80560ac0 0x00003000001c0000

def z156 : W := mkw 0x44241009010418a5 0xffff39198f9ffcff

def z157 : W := mkw 0x0000000000000000 0x3c010000000200e0

def z158 : W := mkw 0x4004000001001025 0xc3fa09118f01f01f

def z159 : W := mkw 0xa4f81269348d4c92 0xffff37e97c9dcc9f

def z160 : W := mkw 0x0000000000000000 0xf6f2000104014093

def z161 : W := mkw 0x0000000000000000 0x0004c00e00e00f00

def z162 : W := mkw 0xa428104924040882 0xc000000104000083

def z163 : W := mkw 0x0420b80d80560ac0 0x1014f80f80fe0fe0

def z164 : W := mkw 0x0500b8dda6000000 0x02f63ef9f7000000

def z165 : W := mkw 0x0fe0ffffeeffeac0 0x3fffffffffffffe0

def z166 : W := mkw 0x4004000001001025 0xcb6909108f03f07f

def z167 : W := mkw 0x08c047b000a9e000 0x147637f0009df000

def z168 : W := mkw 0x0020a80480560ac0 0x3d09c80680fe0fe0

def z169 : W := mkw 0xa0d8022010894412 0xc000000000014013

def z170 : W := mkw 0x0f90ffdffea18518 0x2faff7ee78e18f1c

def z171 : W := mkw 0xacf8fff934ffec92 0x1c7efff870fffc00

def z172 : W := mkw 0x4004000001001025 0xffffc91f8fe3ffff

def z173 : W := mkw 0xa468b8f9245e6882 0xd05038f1041e7083

def z174 : W := mkw 0x0c00fdd924000000 0x02fefff974000000

def z175 : W := mkw 0xe0dc026035895437 0xc26007f07f01f01f

def z176 : W := mkw 0x40c4022001895025 0xffff3ff18f9ff0ff

def z177 : W := mkw 0x08d0efb010fbe518 0x3c7ffff000ffff1c

def z178 : W := mkw 0x4424b80d81561ae5 0xfd9ff80f80ffffff

def z179 : W := mkw 0x00c0022000fbe000 0x1c00000000fff000

def z180 : W := mkw 0x08c0efb000fbe000 0x3dfffff180fff0e0

def z181 : W := mkw 0xa4e81269248d4882 0xd47636e1049d4083

def z182 : W := mkw 0x0000a80000520000 0x0004f00000fc0000

def z183 : W := mkw 0x0020000000560ac0 0x3c01000000fe0fe0

def z184 : W := mkw 0x0010000010000518 0x2001000000000f1c

def z185 : W := mkw 0x0a90470258a18518 0x2d09c10608e18f1c

def z186 : W := mkw 0x0f00fddfee000000 0xf7feffffff014093

def z187 : W := mkw 0x4f04fddfef001025 0x0bffffffff02b06c

def z188 : W := mkw 0x4804ed900172b025 0xfffbc9118f63f0ff

def z189 : W := mkw 0x00d0022010fbe518 0x3c01000000ffff1c

def z190 : W := mkw 0x0fd0fffffefbe518 0x3fffffffffffff1c

def z191 : W := mkw 0x0fc0ffffeefbe000 0x1ffefffffffff000

def z192 : W := mkw 0xaff8fffffeffec92 0xfffefffffffffc93

def z193 : W := mkw 0x0ac0efb248fbe000 0x1ffefffe78fff000

def z194 : W := mkw 0x08c047b000a9e000 0x006007f00001f000

def z195 : W := mkw 0x0000000000000000 0x019a080180000000

def z196 : W := mkw 0x0420b80d80560ac0 0x3dfff91f80ffffe0

def z197 : W := mkw 0x4004000001001025 0xf7f300018f0140ff

def z198 : W := mkw 0xa438104934040c92 0xe280000974000c93

def z199 : W := mkw 0x04b0ba0d90f78fd8 0x3d9ff80f80ff8ffc

def z200 : W := mkw 0x0090020010810410 0x2400000000810c10

def z201 : W := mkw 0x0000000000000000 0x0c0ec00000e00000

def z202 : W := mkw 0x0f00fddfee000000 0x007efffe70000000

def z203 : W := mkw 0xa0d8026034894412 0xd67636e0749d4013

def z204 : W := mkw 0x08c0efb000fbe000 0x10703ff0001ff000

def z205 : W := mkw 0x0420b80d80560ac0 0x2185f00f80fc0fe0

def z206 : W := mkw 0xa4f81269348d4c92 0xe2e006e974014c93

def z207 : W := mkw 0x0f00fddfee000000 0x0264f7fe7f000000

def z208 : W := mkw 0xa5f8bafdb68d4c92 0xf6f63ef9f79d4c93

def z209 : W := mkw 0x08d0efb010fbe410 0x3efefff870fffc10

def z210 : W := mkw 0xe0fc0220118d5cb7 0xfc010000009ffcff

def z211 : W := mkw 0x0bc0eff26efbe000 0x1e7efff07ffff000

def z212 : W := mkw 0x0f00fddfee72a000 0x0bfeffffff62b000

def z213 : W := mkw 0x4004000001001025 0xfe6101100f03f0ff

def z214 : W := mkw 0x0a80470248a18000 0x0faec70e78e18000

def z215 : W := mkw 0x0000000000000000 0x010809108b000000

def z216 : W := mkw 0x0800ed9000000000 0x007efff000000000

def z217 : W := mkw 0x0000000000000000 0x1050081000027000

def z218 : W := mkw 0x4004000001001025 0xefab01018f0180ff

def z219 : W := mkw 0x0f00fddfee000000 0x010cfffefb000000

def z220 : W := mkw 0x0500b8dda6000000 0x01def8ff87000000

def z221 : W := mkw 0xe4fc1269358d5cb7 0xf6f637f97f9dfc9f

def z222 : W := mkw 0x08c0efb000fbe000 0x007efff000fc0000

def z223 : W := mkw 0x0420100d80040ac0 0x00000001800000e0

def z224 : W := mkw 0x0f00fddfee000000 0x2fffffffffe00f00

def z225 : W := mkw 0xa4f81269348d4c92 0xd05436e9749c4c83

def z226 : W := mkw 0x0420b80d80560ac0 0xfffff80f84ff4ff3

def z227 : W := mkw 0xa4f81269348d4c92 0xc26436e8749d4c13

def z228 : W := mkw 0x4a04450249001025 0xffffcf1fff03f0ff

def z229 : W := mkw 0x0a90470258a18518 0x2c05c60e70e18f1c

def z230 : W := mkw 0x0400b80d80000000 0x3d9ff80f800200e0

def z231 : W := mkw 0x0700b84fee000000 0x039ef80fff000000

def z232 : W := mkw 0x4004000001001025 0xe38100018f0000ff

def z233 : W := mkw 0x0f00fddfee000000 0x2fffffffff01801c

def z234 : W := mkw 0x0ab0470258f78fd8 0x3fafc70e78ff8ffc

def z235 : W := mkw 0x0420100d80040ac0 0x3d9b080f80020fe0

def z236 : W := mkw 0x0420b80d80040ac0 0x219ff80f80000fe0

def z237 : W := mkw 0xe4fc1269358d5cb7 0xf7f736e9ff9d4cff

def z238 : W := mkw 0xa4f8ba6db4df4ed2 0xf6f63ee9f49f4cf3

def z239 : W := mkw 0x4a94470259a1953d 0xfffb0f11ff03f0ff

def z240 : W := mkw 0x0090020010a18518 0x2d8fc00e00e18f1c

def z241 : W := mkw 0x0400b80d80520000 0x1d9ef80f80fe0000

def z242 : W := mkw 0xaff8fffffe8d4c92 0x0004f6ee709c0c00

def z243 : W := mkw 0x0420100900040880 0x2080000900000c80

def z244 : W := mkw 0x00d0022010894410 0x36f636e8709d4c10

def z245 : W := mkw 0x0000000000000000 0xe280000104000093

def z246 : W := mkw 0x4a0445024920912d 0x0909c9168b62b36c

def z247 : W := mkw 0x0800ed9000000000 0x1c7efff00003f000

def z248 : W := mkw 0x0cc0ffbd80fbe000 0x1dfeffff80fff000

def z249 : W := mkw 0x4004000001001025 0xfd9b08018003f0ff

def z250 : W := mkw 0xaef8fffb7cffed9a 0xffffffff7cffff9f

def z251 : W := mkw 0x0ce0ffbd80ffeac0 0x0004f6ee00fc0f00

def z252 : W := mkw 0x0700b8dfee000000 0x03d038ffff000000

def z253 : W := mkw 0x0f00fddfee000000 0x0384f6efff000000

def z254 : W := mkw 0xa4f8126934adcd9a 0xfef736e974fdcf9f

def z255 : W := mkw 0x0420b80d80560ac0 0x3d9b3801801e00e0

def z256 : W := mkw 0xa4f81269348d4c92 0xf7fe3ff9ff9d4c93

def z257 : W := mkw 0xe4fc1269358d5cb7 0xfef736e9749ffcff

def z258 : W := mkw 0x4404b80d81001025 0xfffff91f8f03f0ff

def z259 : W := mkw 0x0040002000084000 0x105030e0001c4000

def z260 : W := mkw 0x0420b80d80560ac0 0x019ef80f80fc0f00

def z261 : W := mkw 0x4504b8dda7001025 0xd05038f1870270e3

def z262 : W := mkw 0x00c0022000894000 0x1c7e3ff0009ff000

def z263 : W := mkw 0x0000000000000000 0x022001000801801c

def z264 : W := mkw 0x0f80ffdfeea18000 0x0ffeffffffe18000

def z265 : W := mkw 0x4424b80d81561ae5 0xfddff81f87fe7fe3

def z266 : W := mkw 0x0400100d80000000 0x0180000f80000000

def z267 : W := mkw 0x4704104fef001025 0xe381000fff0000ff

def z268 : W := mkw 0x0020000000040880 0x34000000009c0c80

def z269 : W := mkw 0x4004000001001025 0x000001100b00b00c

def z270 : W := mkw 0x0080020000810000 0x0426060000810000

def z271 : W := mkw 0x0000000000000000 0x038000018f000000

def z272 : W := mkw 0xa4f8ba6db48d4c92 0xf7fefeeff49d4c93

def z273 : W := mkw 0x0a90470258a18518 0x090dc70e78e08f0c

def z274 : W := mkw 0x0200000248000000 0x0380000e78000000

def z275 : W := mkw 0x00c0022000fbe000 0x0000000000fc0000

def z276 : W := mkw 0x0b00ed96ca208108 0x0909c9168b60830c

def z277 : W := mkw 0x421400025900153d 0xe381000fff000fff

def z278 : W := mkw 0x0400b80d80000000 0x0010380180000000

def z279 : W := mkw 0x0000000000000000 0x3ffb09100803f01c

def z280 : W := mkw 0x0420100900040880 0x10103001001c0080

def z281 : W := mkw 0x0800ed9000000000 0x03fefff18f000000

def z282 : W := mkw 0xe4fcba6db5df5ef7 0xffffffffffffffff

def z283 : W := mkw 0x0bc047f26ea9e000 0x026007f07f01f000

def z284 : W := mkw 0x0000000000000000 0x1c0000000003f000

def z285 : W := mkw 0x0210000258000518 0x2fab010e78018f1c

def z286 : W := mkw 0x0840edb0005a6000 0x107efff0001e7000

def z287 : W := mkw 0x4004000001001025 0xe0010000000000ff

def z288 : W := mkw 0x4004000001001025 0xfddb0811870270e3

def z289 : W := mkw 0x0e00554b6c000000 0x03fef7ef7c000000

def z290 : W := mkw 0x0e90574b7ca18518 0x2ffff7ef7ce18f1c

def z291 : W := mkw 0x4004000001001025 0x0bfb09118f02b06c

def z292 : W := mkw 0x00c0aa2000fbe000 0x1c1ef80000fff000

def z293 : W := mkw 0xa4f81229108d4c92 0xf4963009009d4c93

def z294 : W := mkw 0x0000000000000000 0x0909080080020060

def z295 : W := mkw 0x0f0055db6e000000 0x02f637f97f000000

def z296 : W := mkw 0x08c0efb000fbe000 0x3dfffffe00ffff00

def z297 : W := mkw 0xa4f8ba6db4df4ed2 0x3d9ffeeff0fe0fe0

def z298 : W := mkw 0x0880ef0000f38000 0x1c3eff0000ff8000

def z299 : W := mkw 0x4004000001001025 0x1d7b09108b03f06c

def z300 : W := mkw 0x0f00fddfee000000 0x0004f6ee70000000

def z301 : W := mkw 0x0420100900040880 0x3d9f3809809e0ce0

def z302 : W := mkw 0x0000a80480520240 0x0000c00600600300

def z303 : W := mkw 0xa038000010040c92 0xe000000000000c93

def z304 : W := mkw 0x0000000000000000 0xf7fa09118f014093

def z305 : W := mkw 0x0f00fddfee000000 0x3fffffffff0200e0

def z306 : W := mkw 0x0f90574ffea18518 0x2fafc70fffe18f1c

def z307 : W := mkw 0x0f90ffdffea18518 0x0004f6ee70e00f00

def z308 : W := mkw 0x0a00450248000000 0x03fecf1fff000000

def z309 : W := mkw 0xa4f81269348d4c92 0x02f636e9749c0c00

def z310 : W := mkw 0x0a90ef0258f38518 0x3fbfff0e78ff8f1c

def z311 : W := mkw 0x4004000001001025 0xc20000000f00001f

def z312 : W := mkw 0x03000006ca000000 0x010000068b000000

def z313 : W := mkw 0xa4681069240c4882 0xd2f636e9741c4083

def z314 : W := mkw 0xa4781069340c4c92 0xf2d030e9741c4c93

def z315 : W := mkw 0x0ad0efb258fbe518 0x0004f6ee70fc0f00

def z316 : W := mkw 0xe43c104935041cb7 0xfffb0919ff03fcff

def z317 : W := mkw 0x0420b80d80560ac0 0x3496f00f00fc0f80

def z318 : W := mkw 0x4704104fef001025 0xfffb091fff03f0ff

def z319 : W := mkw 0x0ce0ffbd80ffeac0 0x1c7efff180fff0e0

def z320 : W := mkw 0x0b0045d26e000000 0x03fa0ff1ff000000

def z321 : W := mkw 0x4004000001001025 0xfc7b09100003f0ff

def z322 : W := mkw 0x0dc0fffda6fbe000 0x1c7efff187fff000

def z323 : W := mkw 0x0400b80d80000000 0x03fef91f8f000000

def z324 : W := mkw 0x0000a80480520240 0x2d8fc80e80e20f60

def z325 : W := mkw 0x0000000000000000 0xd050000104004083

def z326 : W := mkw 0xa4f8baf934df6c92 0xf6f63ef9749f7c93

def z327 : W := mkw 0x0fc0ffffeefbe000 0x03fefffffffc0000

def z328 : W := mkw 0xa438104db4040ed2 0xe381000ff4000ff3

def z329 : W := mkw 0x0ad0efb258fbe518 0x1c7efffe70ffff00

def z330 : W := mkw 0xaef8576b7cadcd9a 0xf6f6f6ef74fd4f93

def z331 : W := mkw 0x0b00ed96ca000000 0x0000c00600000000

def z332 : W := mkw 0x08c0efb000fbe000 0x1c08c91000fff000

def z333 : W := mkw 0x0490124934810410 0x26f636e974810c10

def z334 : W := mkw 0x0400b80d80520240 0x099ff80f80620360

def z335 : W := mkw 0x0000000000000000 0x3dfb09118003f0e0

def z336 : W := mkw 0x0f00fddfee000000 0x1ffeffffff03f000

def z337 : W := mkw 0x0f90ffdffe810410 0x27feffffff810c10

def z338 : W := mkw 0x0420b80d80560ac0 0x090df80e80fe0f60

def z339 : W := mkw 0x0a90470258a18518 0x23a1070e78018f1c

def z340 : W := mkw 0x4424100d81041ae5 0xe381000f8f000fff

def z341 : W := mkw 0x08c0efb000fbe000 0x1054fef000fe7000

def z342 : W := mkw 0x4004a80001521025 0xfffff9118ffff0ff

def z343 : W := mkw 0x0b0045d26e000000 0x03eec7fe7f000000

def z344 : W := mkw 0xa4d8126934894412 0xc2f636e974014013

def z345 : W := mkw 0x0f00554fee000000 0x03aec70fff000000

def z346 : W := mkw 0xa438104934040c92 0xf6963009749c0c93

def z347 : W := mkw 0x08c0efb480fbe240 0x1d7ffff680fff360

def z348 : W := mkw 0x0a90470258a18518 0x2385c60e78e00f1c

def z349 : W := mkw 0x4004000001001025 0xde7a09100f03f01f

def z350 : W := mkw 0x0f00fddfee000000 0x0054fefff7000000

def z351 : W := mkw 0x00c0022000a9e000 0x000000000001f000

def z352 : W := mkw 0x0f20fddfee560ac0 0x13feffffff1e00e0

def z353 : W := mkw 0x0a00ed924872a108 0x0909c9160862b30c

def z354 : W := mkw 0x0630b80fd8560fd8 0x3f9ff80ff8fe0ffc

def z355 : W := mkw 0x0000a80480520240 0x1d1ff80680fe0360

def z356 : W := mkw 0x0020000000040ac0 0x2001000000000fe0

def z357 : W := mkw 0x0ad0efb258fbe518 0x1e7efff078fff01c

def z358 : W := mkw 0xe43c104935041cb7 0xe3810009ff000cff

def z359 : W := mkw 0xe46c1069250c58a7 0xd05038f1871e70e3

def z360 : W := mkw 0x0ad047b258a9e518 0x026007f07801f01c

def z361 : W := mkw 0x0000000000520000 0x1c00000000fe0000

def z362 : W := mkw 0x00b0020010f78fd8 0x3c01000000ff8ffc

def z363 : W := mkw 0x0420b80d80560ac0 0x2989c80f80620fe0

def z364 : W := mkw 0xa0f80260348d4c92 0xf66006e0749d4c93

def z365 : W := mkw 0x0a90ef06d8f38758 0x2fafcf0ef8e38f7c

def z366 : W := mkw 0x0800450000208000 0x0808c10000608000

def z367 : W := mkw 0x04e0ba2d80ffeac0 0x3d9ff80f80ffffe0

def z368 : W := mkw 0xaaf8472258adcd9a 0xffafc70e78fdcf9f

def z369 : W := mkw 0x0000000480000240 0x0101000680000360

def z370 : W := mkw 0x0020000000560ac0 0x0000000000fc0f00

def z371 : W := mkw 0x0b0045d26e000000 0x000006e070000000

def z372 : W := mkw 0x0000000000000000 0xfffb0801840340f3

def z373 : W := mkw 0x0ce0ffbd80ffeac0 0x3d9ffeef80fe0fe0

def z374 : W := mkw 0x08c0efb000fbe000 0x1c1efee000fe0000

def z375 : W := mkw 0xa4f8ba6db4df4ed2 0x0004f6ee70fc0f00

def z376 : W := mkw 0x0f00fddfee520240 0x0bffffffff620360

def z377 : W := mkw 0x0000000000000000 0x007636e000000000

def z378 : W := mkw 0x00c0022000894000 0x000436e0009c0000

def z379 : W := mkw 0x08c0efb000fbe000 0x1c04f6e000fff000

def z380 : W := mkw 0x0000000000000000 0x2ffb09118f01801c

def z381 : W := mkw 0x0000a80480520240 0x3d9bc807806203e0

def z382 : W := mkw 0x0ad0efb258fbe518 0x2faff7ee78fd8f1c

def z383 : W := mkw 0x4a0445024920912d 0xfffbc9178f63f3ff

def z384 : W := mkw 0x4004000001001025 0xf6f201110f01f09f

def z385 : W := mkw 0x0f00fddfee000000 0x0388c91fff000000

def z386 : W := mkw 0x0420100d80040ac0 0x3597300f809c0fe0

def z387 : W := mkw 0x0a00450248208108 0x2fabc1060861831c

def z388 : W := mkw 0x0f00fddfee000000 0x019efeeff0000000

def z389 : W := mkw 0x0000000000000000 0x007a091000000000

def z390 : W := mkw 0x4004000001001025 0xf3d108118f0270ff

def z391 : W := mkw 0x0000000000000000 0x238100000800001c

def z392 : W := mkw 0x4094020011a1953d 0xfc01000000e3ffff

def z393 : W := mkw 0x0000000000000000 0x2181000e00000f00

def z394 : W := mkw 0x0420b80d80560ac0 0x3191380f801e0fe0

def z395 : W := mkw 0x0420b80d80560ac0 0x119ef80f801e00e0

def z396 : W := mkw 0x4004000001001025 0xd3fa09118f0270e3

def z397 : W := mkw 0xa0f8022010adcd9a 0xfc01000000fdcf9f

def z398 : W := mkw 0x0f00fddfee208108 0x0bffffffff60830c

def z399 : W := mkw 0x4424100d81041ae5 0xfffb091f8f03ffff

def z400 : W := mkw 0x0e00fd0fc8000000 0x03beff0ff8000000

def z401 : W := mkw 0x0f90ffdffea18518 0x03feffffff01801c

def z402 : W := mkw 0x0e90ff0fd8a18518 0x2fbfff0ff8e18f1c

def z403 : W := mkw 0x4004000001001025 0xd95909118f02f0ef

def z404 : W := mkw 0x0420b80d80560ac0 0x3c05f00e00fe0fe0

def z405 : W := mkw 0x0460b8bd805e6ac0 0x3ddff8ff80fe7fe0

def z406 : W := mkw 0x0a90470258a18518 0x2fffcf1fffe18f1c

def z407 : W := mkw 0x0a00ed06c8728348 0x0909c9068862836c

def z408 : W := mkw 0x0000a80000520000 0x10103800001e0000

def z409 : W := mkw 0x0800ed9000000000 0x0008c91000000000

def z410 : W := mkw 0x0880ef9000a18000 0x0c7efff000e18000

def z411 : W := mkw 0x0f20fd9fca560ac0 0x3d9ff91f8bfe0fe0

def z412 : W := mkw 0x4b04ed96cb001025 0x0909c9168b02b06c

def z413 : W := mkw 0x0a90ef9258a18518 0x2ffffffe78e18f1c

def z414 : W := mkw 0x0000a89000000000 0x005038f000000000

def z415 : W := mkw 0x0000000000000000 0x2d8b000000000000

def z416 : W := mkw 0x0880470000a18000 0x1c7ecf1000e3f000

def z417 : W := mkw 0x0090020010a18518 0x2ea7060870e18f1c

def z418 : W := mkw 0x0880470000a18000 0x2dafc70e00e18f00

def z419 : W := mkw 0x08c0efb000fbe000 0x0868cff00063f000

def z420 : W := mkw 0x0290020258810518 0x27a7060e78810f1c

def z421 : W := mkw 0x0700104fee000000 0x03f636efff000000

def z422 : W := mkw 0x0bc0efb6cafbe000 0x1d7efff68bfff000

def z423 : W := mkw 0x0040a8b0005a6000 0x1c5ef8f000fe7000

def z424 : W := mkw 0x0000000000000000 0x3d9fc80f80e20fe0

def z425 : W := mkw 0xa738104ffe040c92 0xe380000fff000c93

def z426 : W := mkw 0x4424b80d81561ae5 0xfffb39118f1ff0ff

def z427 : W := mkw 0x0f40fdffee5a6000 0x13feffffff1e7000

def z428 : W := mkw 0x0000000000208108 0x080100000060830c

def z429 : W := mkw 0x0420b80d80560ac0 0x3fbff90f88ff8ffc

def z430 : W := mkw 0x0800ed900072a000 0x087efff00062b000

def z431 : W := mkw 0x00c0aa2000db4000 0x1c7efee000ff4000

def z432 : W := mkw 0x0200000248000108 0x010100060800030c

def z433 : W := mkw 0x0000000000000000 0x02f2000104000000

def z434 : W := mkw 0x0800ed9000520000 0x1c7efff000fe0000

def z435 : W := mkw 0x4f04fddfef001025 0xc3feffffff01f01f

def z436 : W := mkw 0xa4f81269348d4c92 0xfefe3ff9749ffc93

def z437 : W := mkw 0xecfcfff935fffcb7 0xfffffff9fffffcff

def z438 : W := mkw 0x0eb0570b58a58d98 0x3fbff70f78fd8f9c

def z439 : W := mkw 0x0000000000000000 0xf400000000014093

def z440 : W := mkw 0xe46c1069250c58a7 0xfffb39f18f1ff0ff

def z441 : W := mkw 0x0500104da6000000 0x0000000187000000

def z442 : W := mkw 0x0000a80000520000 0x3d9ff80180fe00e0

def z443 : W := mkw 0x48c447b001a9f025 0xc26007f00f01f01f

def z444 : W := mkw 0x4004000001001025 0xd27009118f03f0ff

def z445 : W := mkw 0x0ca0ff0d80f78ac0 0x3dbfff0f80ff8fe0

def z446 : W := mkw 0x0800ed9000000000 0x0004f6e000000000

def z447 : W := mkw 0x0090020010810410 0x2faf070878818c1c

def z448 : W := mkw 0x0000000000000000 0x026001100f000000

def z449 : W := mkw 0x00c0022000894000 0x006006e000014000

def z450 : W := mkw 0x08c0efb000fbe000 0x0064f7f000fdf000

def z451 : W := mkw 0x4404104925001025 0xffff3ff9ff03f0ff

def z452 : W := mkw 0x0fb0ffdffef78fd8 0x3fffffffffff8ffc

def z453 : W := mkw 0x0cc0fff924fbe000 0x1efefff974fff000

def z454 : W := mkw 0x0800ed900072a000 0x1c7ac9100063f000

def z455 : W := mkw 0x4ce4ffbd81fffae5 0xffffffff8fffffff

def z456 : W := mkw 0x0000000000520240 0x0801000000620360

def z457 : W := mkw 0xa4f81269348d4c92 0xe28436e9749c0c93

def z458 : W := mkw 0x0f20fddfee560ac0 0x3d9ffeeff0fe0fe0

def z459 : W := mkw 0x0400104924000000 0x03fe3ff9ff000000

def z460 : W := mkw 0x0000000000000000 0x21810001800000e0

def z461 : W := mkw 0x0f20fddfee040880 0x37feffffff9c0c80

def z462 : W := mkw 0x00c0022000894000 0xf6f636e1049d4093

def z463 : W := mkw 0x4004000001001025 0x2fab09108b03b07c

def z464 : W := mkw 0x0420b84da4560ac0 0x3ffffeeff4fe0fe0

def z465 : W := mkw 0x4f04fddfef001025 0xd3feffffff0270e3

def z466 : W := mkw 0x0700104fee000000 0x03fa091fff000000

def z467 : W := mkw 0x0420100900560ac0 0x3c97300900fe0fe0

def z468 : W := mkw 0x0420b80d80560ac0 0x2d8ff00e00fc0f00

def z469 : W := mkw 0xa4f81269348d4c92 0xf6800009749d4c93

def z470 : W := mkw 0xa638104b7c040d9a 0xe381000f7c000f9f

def z471 : W := mkw 0xa4f8ba2d90df4ed2 0xfd9ff80f80ff4ff3

def z472 : W := mkw 0xa4681069240c4882 0xf4d630e9049c4c83

def z473 : W := mkw 0x0a90470258a18518 0x0224c70e78e18f1c

def z474 : W := mkw 0xa4f8126934ffec92 0xfef636e974fffc93

def z475 : W := mkw 0xabd847f27e894412 0xc26007f07f014013

def z476 : W := mkw 0x0f00fddfee000000 0x02f6f6ef74000000

def z477 : W := mkw 0x0100a89482000000 0x0000081083000000

def z478 : W := mkw 0x0ac0efb248fbe108 0x1d7ffff608fff30c

def z479 : W := mkw 0x00c0aab000db6000 0x14763ef0009f7000

def z480 : W := mkw 0xa4f8ba6934df4c92 0xfefefee974ff4c93

def z481 : W := mkw 0x0520b8dda6560ac0 0x105038f1871e00e0

def z482 : W := mkw 0xa4f81269348d4c92 0x349636e9709c0c80

def z483 : W := mkw 0x4004000001001025 0xc00000000001f01f

def z484 : W := mkw 0x4024000001561ae5 0xfffb09118fffffff

def z485 : W := mkw 0x0400b84da4000000 0x03fefeeff4000000

def z486 : W := mkw 0x4b0445d26f001025 0xc26007f07f01f01f

def z487 : W := mkw 0x0ce0ffbd80ffeac0 0x1c7efffe00ffff00

def z488 : W := mkw 0x0a00450248208108 0x000001000800800c

def z489 : W := mkw 0x421400025900153d 0xfffb091fff03ffff

def z490 : W := mkw 0x4004000001001025 0xc0000001870000e3

def z491 : W := mkw 0x0eb0570fd8a58fd8 0x2fafc70ff8e18ffc

def z492 : W := mkw 0x0090020010a18518 0x2fab010008e18f1c

def z493 : W := mkw 0x0e20fd0fc8560ac0 0x3fbfff0ff8fe0fe0

def z494 : W := mkw 0x4f24fddfef561ae5 0xffffffffffffffff

def z495 : W := mkw 0x0000000000000000 0x3fbb0901880380fc

def z496 : W := mkw 0x0a00450248000000 0x0108c10608000000

def z497 : W := mkw 0x0e20fd0fc8768bc8 0x3d9ff90f88fe8fec

def z498 : W := mkw 0x4804ed9001001025 0xfffffff18f03f0ff

def z499 : W := mkw 0x0880ef9000f3a000 0x0c2ecf1000e3b000

def z500 : W := mkw 0x0000a80480520240 0x0000080080020060

def z501 : W := mkw 0x0020000000560ac0 0x10000000001e00e0

def z502 : W := mkw 0xaff857fb7e8d4c92 0xf6f637f97f9d4c93

def z503 : W := mkw 0x0a90ef9258f3a518 0x2fafcf1e78e3bf1c

def z504 : W := mkw 0x0b9047d27ea18518 0x2fefc7fe7fe18f1c

def z505 : W := mkw 0x0f00fddfee000000 0x0158f9f78f000000

def z506 : W := mkw 0xa0f80220108d4c92 0x00000000009c0c00

def z507 : W := mkw 0x0420b80d80560ac0 0x34963809809e0ce0

def z508 : W := mkw 0x4004000001001025 0xc040001007007003

def z509 : W := mkw 0x0420100d80040ac0 0x2d8fc00f80e00fe0

def z510 : W := mkw 0x0000000000000000 0x080809100002b000

def z511 : W := mkw 0xaff8fffffe8d4c92 0xf6f6f6ef749d4c93

def z512 : W := mkw 0x0f20fddfee560ac0 0x03fefffffffc0f00

def z513 : W := mkw 0x40c4022001fbf025 0xfffb09118ffff0ff

def z514 : W := mkw 0xacf8fff934ffec92 0x0004f6e870fc0c00

def z515 : W := mkw 0x4004000001001025 0xd0000000000270e3

def z516 : W := mkw 0x0a90470258a18518 0xffffc70f7ce1cf9f

def z517 : W := mkw 0xaff8fffffe8d4c92 0x03feffffff9c0c00

def z518 : W := mkw 0x0880470000a18000 0x0020070000018000

def z519 : W := mkw 0x4004000001001025 0xdc7a09118703f0e3

def z520 : W := mkw 0x0a90470258a18518 0x26a6070878818c1c

def z521 : W := mkw 0x0a00450248000000 0x0004c60e70000000

def z522 : W := mkw 0x0b9047d27ea18518 0x026007f07f01801c

def z523 : W := mkw 0x0710104ffe000518 0x2381000fff000f1c

def z524 : W := mkw 0x4b04ed96cb001025 0xfffbc9178f03f0ff

def z525 : W := mkw 0x4fc4ffffeffbf025 0xfffffffffffff0ff

def z526 : W := mkw 0x4a94470259a1953d 0xefafc70fffe18fff

def z527 : W := mkw 0x0a00450248208108 0x0000c00600600300

def z528 : W := mkw 0x0a90470258a18518 0x2e21070078e18f1c

def z529 : W := mkw 0x0ce0ffb900ffe880 0x3cfefff900fffc80

def z530 : W := mkw 0x0a00450248000000 0x2fafc70e7801801c

def z531 : W := mkw 0x0090020010810410 0x2fafc60e70e10f10

def z532 : W := mkw 0x4ad4efb259fbf53d 0xffffffffffffffff

def z533 : W := mkw 0x0210000258000518 0x0000000e70000f00

def z534 : W := mkw 0x0720b84fee560ac0 0x3f9ff80ffffe0fe0

def z535 : W := mkw 0x0a90470258810410 0x27aec70e78810c10

def z536 : W := mkw 0x0000000000000000 0x2fafc10e08e18f1c

def z537 : W := mkw 0xaeb8574b7ca58d9a 0xefafc70f7ce18f9f

def z538 : W := mkw 0x0000004024000000 0x026006e074000000

def z539 : W := mkw 0xaf68fdffee0c4882 0xd3feffffff1c4083

def z540 : W := mkw 0x0000000000000000 0x0909c00600600300

def z541 : W := mkw 0x0a90470258a18518 0x03aec70e7801801c

def z542 : W := mkw 0x4004000001001025 0xeb8909118f02b0ff

def z543 : W := mkw 0x0420b80d80560ac0 0x1919f807807e03e0

def z544 : W := mkw 0x0000000000000000 0x018ec00e00000000

def z545 : W := mkw 0xaf38fddffe040c92 0xe3feffffff000c93

def z546 : W := mkw 0xaad847627ca9c51a 0xc26007e07c01c01f

def z547 : W := mkw 0xaff8fffffedf4ed2 0xffffffffffff4ff3

def z548 : W := mkw 0x4004a80481521265 0xfffbc9178f63f3ff

def z549 : W := mkw 0xaef8576b7c8d4c92 0xf7fef7ef7c9d4c93

def z550 : W := mkw 0x0a90470258a18518 0x0b29c7067861831c

def z551 : W := mkw 0x0540b8fda65a6000 0x105038f1871e7000

def z552 : W := mkw 0xa438104934040c92 0xe2f636e974000c93

def z553 : W := mkw 0x0400b80d80000000 0x2d9ff80f80e00f00

def z554 : W := mkw 0x0000000000000000 0x1c1a080000020000

def z555 : W := mkw 0x0000000000000000 0x02a6060870000000

def z556 : W := mkw 0x08c0efb000fbe000 0x0c2ef7e000fd8000

def z557 : W := mkw 0x0420100900040880 0x3d9ff00f00fc0f80

def z558 : W := mkw 0x4004000001001025 0xfd0909108b03f0ff

def z559 : W := mkw 0x0000a80000000000 0x001ef80000000000

def z560 : W := mkw 0x4004000001001025 0xefeb01100f01f01f

def z561 : W := mkw 0x0a00450248208108 0x2d8fc10e08e08f0c

def z562 : W := mkw 0xa4b8124934850c92 0xe6a6060974810c93

def z563 : W := mkw 0x000000000072a000 0x080000000062b000

def z564 : W := mkw 0x48c4efb001fbf025 0xfc7ffff000fff0ff

def z565 : W := mkw 0x4004000001001025 0x0000081083023060

def z566 : W := mkw 0x080045900020a000 0x000001100000b000

def z567 : W := mkw 0xe0dc026035895437 0xfffb0ff1ff03f0ff

def z568 : W := mkw 0x4004000001001025 0xffab01000803f0ff

def z569 : W := mkw 0x0b00ed96ca520240 0x0909c9168b620360

def z570 : W := mkw 0xaad847627ca9c51a 0xefefc7ee7ce1cf1f

def z571 : W := mkw 0xa0f80220108d4c92 0xf6a60608709d4c93

def z572 : W := mkw 0x04e01229008d4880 0x34f636e9009d4c80

def z573 : W := mkw 0x08c047b000a9e000 0x1c7a0ff00003f000

def z574 : W := mkw 0x0a90470258a18518 0x3fffcf1e78e3ff1c

def z575 : W := mkw 0x08c0472000fbe000 0x1c2ec70000fff000

def z576 : W := mkw 0x0f20fddfee560ac0 0x0004f6ee70fc0f00

def z577 : W := mkw 0x0500b8dda6000000 0x03fa39f18f000000

def z578 : W := mkw 0x4504b8dda7001025 0xfffb39f18f03f0ff

def z579 : W := mkw 0x0a90470258a18518 0x26a6c60e70e10f10

def z580 : W := mkw 0x0630100fd8040fd8 0x2381000ff8000ffc

def z581 : W := mkw 0x0090020010a18518 0x000000000001801c

def z582 : W := mkw 0x4004000001001025 0x080100000002b06c

def z583 : W := mkw 0x0ef0ffbfd8ffefd8 0x3ffffffff8fffffc

def z584 : W := mkw 0xaef8576b7cadcd9a 0xf6f637e97c9dcc9f

def z585 : W := mkw 0x4004a80481521265 0x0909c9168b62b36c

def z586 : W := mkw 0xeefc576b7dadddbf 0xffffffffffffffff

def z587 : W := mkw 0x4b0445d26f001025 0xfffb0ff1ff03f0ff

def z588 : W := mkw 0x08c047b000fbe000 0x1c6007f000fff000

def z589 : W := mkw 0xa438104934040c92 0x0000000870000c00

def z590 : W := mkw 0xa0f8022010ffec92 0xfc00000000fffc93

def z591 : W := mkw 0x0000000000000000 0xfefa09110403f093

def z592 : W := mkw 0x0080020000a18000 0x0c00000000e18000

def z593 : W := mkw 0x08c047b000a9e000 0x000006e000000000

def z594 : W := mkw 0x0420104924040880 0x36f636e9749c0c80

def z595 : W := mkw 0x0880470000a18000 0x0004c60000e00000

def z596 : W := mkw 0xa4f81269348d4c92 0x147636e8709d4c00

def z597 : W := mkw 0x0020000000560ac0 0x3d9b080180fe0fe0

def z598 : W := mkw 0x0460b8bd805e6ac0 0x105038f1801e70e0

def z599 : W := mkw 0x4004000001001025 0xe3fb09118f0000ff

def z600 : W := mkw 0x0420b80d80560ac0 0x1c1ef80e00fe0f00

def z601 : W := mkw 0x0000000000000000 0x090901000800800c

def z602 : W := mkw 0x0a90470258a18518 0x0000060070000000

def z603 : W := mkw 0x0890470010a18410 0x2eaec70870e18c10

def z604 : W := mkw 0x0800ed948072a240 0x0909c9168062b360

def z605 : W := mkw 0x0800459000000000 0x006007f000000000

def z606 : W := mkw 0x0b00ed96ca000000 0x03aecf1efb000000

def z607 : W := mkw 0xa0f8022010df4ed2 0xfc01000000ff4ff3

def z608 : W := mkw 0x0b90ef96daa18518 0x2fafcf1efbe18f1c

def z609 : W := mkw 0x0400b80d80000000 0x0004f00e00000000

def z610 : W := mkw 0x0a90470258a18518 0x2fab07007801801c

def z611 : W := mkw 0xa468b86da45e4ac2 0xd05038e1841e40e3

def z612 : W := mkw 0x0a10450258000518 0x23afc70e78000f1c

def z613 : W := mkw 0x0c00fd9d80000000 0x01feffff80000000

def z614 : W := mkw 0x0700104fee000000 0x0000000e70000000

def z615 : W := mkw 0x04e0ba2d80df4ac0 0x3dfffeef80ff4fe0

def z616 : W := mkw 0xa8d8eff034fbe412 0xde7efff074fff013

def z617 : W := mkw 0x4044a8b0015a7025 0xd05038f1871e70e3

def z618 : W := mkw 0x4a94470259a1953d 0xc26007107f01f01f

def z619 : W := mkw 0x0fc0ffffeefbe000 0x0004f6ee70fc0000

def z620 : W := mkw 0x0f10fddffe000518 0x23ffffffff000f1c

def z621 : W := mkw 0x0f90ffdffea18518 0x03feffffffe00f00

def z622 : W := mkw 0x08e0efb000ffeac0 0x3c7ffff000ffffe0

def z623 : W := mkw 0x0000000000000000 0x03aa010008000000

def z624 : W := mkw 0x0800ed900072a000 0x0000c00000600000

def z625 : W := mkw 0xaef8ff6ffcffcfda 0xffffffeffcffcfff

def z626 : W := mkw 0x0000000000000000 0x0050081187000000

def z627 : W := mkw 0xa0f80220108d4c92 0xf6f20001049d4c93

def z628 : W := mkw 0x4eb4ff0fd9f79ffd 0xffffff1fffffffff

def z629 : W := mkw 0xa7f8126ffe8d4c92 0xf7f636efff9d4c93

def z630 : W := mkw 0x0f00fddfee000000 0x03aef7ee78000000

def z631 : W := mkw 0x08c0472000a9c000 0x1c7ef7e000fdc000

def z632 : W := mkw 0xa018004034000412 0xc200000074000013

def z633 : W := mkw 0x0800450000000000 0x002ec70000000000

def z634 : W := mkw 0xa4f8ba6db4df4ed2 0xf6f6f6ef74fd4f93

def z635 : W := mkw 0xe4fc1269358d5cb7 0xf6f63ef9f79f7cf3

def z636 : W := mkw 0xa4f8126934df4ed2 0xfef736e974ff4ff3

def z637 : W := mkw 0xa438b84db4560ed2 0xff9ff80ff4fe0ff3

def z638 : W := mkw 0x4004000001001025 0x3d9b09118b02b0ec

def z639 : W := mkw 0x0420100d80560ac0 0x3d81000f80fe0fe0

def z640 : W := mkw 0x0eb0ff0fd8f78fd8 0x2faff70e78fd8f1c

def z641 : W := mkw 0x4424b80d81561ae5 0xff9ff80f8ffe0fff

def z642 : W := mkw 0x0010000010000410 0x2280000870000c10

def z643 : W := mkw 0xa4f81269348d4c92 0xf45030e1049d4c93

def z644 : W := mkw 0x0000000000000000 0x2c0100000001801c

def z645 : W := mkw 0xa0d8026034894412 0xe6e606e874814c13

def z646 : W := mkw 0x08c0efb000a9e000 0x007efff00001f000

def z647 : W := mkw 0x0880470000a18000 0x2fafc70008e1801c

def z648 : W := mkw 0xa0680020000c4882 0xd0000000001c4083

def z649 : W := mkw 0x0fc0ffffeefbe000 0x1c7efffe70fff000

def z650 : W := mkw 0x0000000000000000 0x2c01000000e00f00

def z651 : W := mkw 0x0420b80d80560ac0 0x1c1ef80180fe00e0

def z652 : W := mkw 0x0420b80d80560ac0 0x3c11380180fe0fe0

def z653 : W := mkw 0x0000000000000000 0x2486000800800c00

def z654 : W := mkw 0x08c0efb000894000 0x147efff0009d4000

def z655 : W := mkw 0x4004000001001025 0xe3e101118f01f0ff

def z656 : W := mkw 0x48c447b001a9f025 0xfffb0ff18f03f0ff

def z657 : W := mkw 0x04b0120910850c90 0x36b63609709d0c90

def z658 : W := mkw 0x0000000000000000 0x3ffb09118f0200e0

def z659 : W := mkw 0x0890470010a18518 0x2c2fc70000e18f1c

def z660 : W := mkw 0xa4f81269348d4c92 0x26a636e8709d0c10

def z661 : W := mkw 0x0000a80000520000 0x0808c80000620000

def z662 : W := mkw 0x0eb0ff0fd8f78fd8 0x0004f60e70fc0f00

def z663 : W := mkw 0x08c047b000a9e000 0x0c6ec7f000e1f000

def z664 : W := mkw 0x0b00ed96ca72a000 0x0908c9168b62b000

def z665 : W := mkw 0x0c20fd9d8076aac0 0x3d9ff91f80febfe0

def z666 : W := mkw 0x4004000001001025 0xf6f20811870370f3

def z667 : W := mkw 0x0400100900000000 0x0096300900000000

def z668 : W := mkw 0xaef8576b7cadcd9a 0x0004f6ee70fc0f00

def z669 : W := mkw 0x0420100900040880 0x00043008009c0c00

def z670 : W := mkw 0xa6f8126b7c8d4d9a 0xf7f736ef7c9d4f9f

def z671 : W := mkw 0x4004000001001025 0xfc5108118703f0ff

def z672 : W := mkw 0x0a90470258a18518 0x2d8fc60e70e00f00

def z673 : W := mkw 0x0000000000000000 0xfffb01010c01c09f

def z674 : W := mkw 0x0400104924000000 0x000436e870000000

def z675 : W := mkw 0x0a90470258a18518 0x0c2ec70e70e18f00

def z676 : W := mkw 0x0420b80900560880 0x3c9ef80900fe0c80

def z677 : W := mkw 0x0000000000000000 0x26a2000000010010

def z678 : W := mkw 0x4884470001a19025 0xffffcf118fe3f0ff

def z679 : W := mkw 0x0d00fddda6000000 0x007efff187000000

def z680 : W := mkw 0x0ad0472258fbe518 0x3fafc70e78ffff1c

def z681 : W := mkw 0x04c0126924894000 0x16f636e9749d4000

def z682 : W := mkw 0x4804ed900172b025 0x0909c9108b62b06c

def z683 : W := mkw 0x0b00ed96ca000000 0x03fac9178f000000

def z684 : W := mkw 0x4004000001001025 0xfef300010403f0ff

def z685 : W := mkw 0x0000000000000000 0x14163000009c0000

def z686 : W := mkw 0x0090020010810410 0x0004060870800c00

def z687 : W := mkw 0x0210000258000518 0x020000007800001c

def z688 : W := mkw 0x4004000001001025 0xff9b08018f0200ff

def z689 : W := mkw 0x4f04fddfef001025 0xe3ffffffff0000ff

def z690 : W := mkw 0xa568b8fda60c4882 0xd05038f1871c4083

def z691 : W := mkw 0x4024000001561ae5 0xfc01000000ffffff

def z692 : W := mkw 0x0000a80000520000 0x1c7ef91000fff000

def z693 : W := mkw 0xa8f8efb010ffec92 0xfc7efff000fffc93

def z694 : W := mkw 0x48c4efb001fbf025 0x1d7ffff08bfff06c

def z695 : W := mkw 0xa8d847f034a9e412 0xc26007f07401f013

def z696 : W := mkw 0x4004000001001025 0x010100008b00006c

def z697 : W := mkw 0x0090020010810410 0x0220060070010010

def z698 : W := mkw 0x0400104924000000 0x005030e104000000

def z699 : W := mkw 0xace8fff924ffe882 0xdc7efff104fff083

def z700 : W := mkw 0x0c20fd9d80560ac0 0x3dffffff80fe0fe0

def z701 : W := mkw 0x04b0ba0d90d70ed0 0x3fbffe0ff0ff0ff0

def z702 : W := mkw 0x0000000000000000 0x3492000100000080

def z703 : W := mkw 0x4424b80d81561ae5 0xd0503811871e70e3

def z704 : W := mkw 0xa438104934040c92 0xf6f2000974014c93

def z705 : W := mkw 0x0000000000000000 0x006001100001f000

def z706 : W := mkw 0x48c4efb001fbf025 0xdc7efff187fff0e3

def z707 : W := mkw 0x0ad0472258a9c518 0x2fefc7ee78e1cf1c

def z708 : W := mkw 0x00c0022000fbe000 0x1c5030e000fff000

def z709 : W := mkw 0x0f0055dfee000000 0x03eec7ffff000000

def z710 : W := mkw 0x0ad0472258a9e518 0x2fafc70e78e1ff1c

def z711 : W := mkw 0xa4f81269348d4c92 0xc00436e9749c0c83

def z712 : W := mkw 0x0420b80d80560ac0 0x3ddff81f80fe7fe0

def z713 : W := mkw 0x0420b80d80560ac0 0x119ef80f80fe0fe0

def z714 : W := mkw 0x0ad0efb258fbe518 0x3c05f6ee70ffff1c

def z715 : W := mkw 0xa0d8026034894412 0xc26436e0749d4013

def z716 : W := mkw 0x0b00edd6ee000000 0x03eecffeff000000

def z717 : W := mkw 0x0b0045d26e000000 0x026007f07f01801c

def z718 : W := mkw 0x0f00fddfee000000 0xffffffffff0340f3

def z719 : W := mkw 0x08c0efb000fbe000 0x1878fff0007ff000

def z720 : W := mkw 0x0eb0ff0fd8f78fd8 0x12303f01f81f80fc

def z721 : W := mkw 0x0a90470258a18518 0x3fafc70e78e38ffc

def z722 : W := mkw 0xaf28fddfee040882 0xc3feffffff000083

def z723 : W := mkw 0xa4f81269348d4c92 0xf6f6f6ef74fd4f93

def z724 : W := mkw 0x0f20fddfee040ac0 0x37ffffffff9c0fe0

def z725 : W := mkw 0x08c0efb000fbe000 0xfffffff184fff0f3

def z726 : W := mkw 0x0420b89d80562ac0 0x3d9ff81f80fe3fe0

def z727 : W := mkw 0xa4f81269348d4c92 0xc26036e0741d4013

def z728 : W := mkw 0x0420b80d80560ac0 0x099ff80f80fe0f60

def z729 : W := mkw 0x4004000001001025 0xffffc9118fe3f0ff

def z730 : W := mkw 0x0a90470258a18518 0x3fbff70e78fd8f1c

def z731 : W := mkw 0xa4f81269348d4c92 0xe6e636e8749d4c13

def z732 : W := mkw 0x4004000001001025 0xff8909118f03f0ff

def z733 : W := mkw 0x0420b80d80560ac0 0x3fbff80f80ff0ff0

def z734 : W := mkw 0x00c0aab000db6000 0x145038f0009f7000

def z735 : W := mkw 0x0a00450248000000 0x2fafc70e78e18f1c

def z736 : W := mkw 0x0ac0efb248fbe108 0x3ffffff608fff31c

def z737 : W := mkw 0xa4f81269348d4c92 0xd2f636e9741d4093

def z738 : W := mkw 0x0b2045d26e560ac0 0x3e6107f07ffe0fe0

def z739 : W := mkw 0x0720104fee040ac0 0x37f736efff9c0fe0

def z740 : W := mkw 0xa4681069240c4882 0xd27036e1741c4083

def z741 : W := mkw 0x0700b8dfee000000 0x03f63effff000000

def z742 : W := mkw 0x0520b8dda6560ac0 0x3d9ff8ef80fe0fe0

def z743 : W := mkw 0x0f20fddfee560ac0 0x090dfffefbfe0f60

def z744 : W := mkw 0x0ad0efb258fbe518 0x3ffffffff8fffffc

def z745 : W := mkw 0xa4681069240c4882 0xf6f636e9749c4c83

def z746 : W := mkw 0x08c0efb000fbe000 0x0c6ef7f000fdf000

def z747 : W := mkw 0x0040a8b0005a6000 0x3ffb39f0081ff01c

def z748 : W := mkw 0x0420b80d80560ac0 0xfffff90f8cffcfff

def z749 : W := mkw 0x08c0efb000fbe000 0x3c7ffff000fff0e0

def z750 : W := mkw 0xe43c104db5041ef7 0xe381000fff000fff

def z751 : W := mkw 0x0f20fddfee560ac0 0x2ffffffffffc0f00

def z752 : W := mkw 0x08c0efb000fbe000 0x3ffffff18ffff0e0

def z753 : W := mkw 0x0420104924040880 0xf6f636e9749d4c93

def z754 : W := mkw 0x0f00fddfee000000 0x019efffffb000000

def z755 : W := mkw 0x0f20fddfee040ac0 0x03feffffff0000e0

def z756 : W := mkw 0x0f00fddfee000000 0x00503ef1f7000000

def z757 : W := mkw 0x0090020010810410 0x2fafc70e78e18f1c

def z758 : W := mkw 0xa4f8126934adcd9a 0xfffff6ef74fdcf9f

def z759 : W := mkw 0x0420b80d80560ac0 0x3dfff91f80fe0fe0

def z760 : W := mkw 0x0f0055db6e000000 0x026437f87f000000

def z761 : W := mkw 0x0b0045d26e000000 0x026ec7f07f000000

def z762 : W := mkw 0x08c0efb000fbe000 0x107efff000fe7000

def z763 : W := mkw 0x08c0efb000fbe000 0x1efefff104fff000

def z764 : W := mkw 0x0f00fddfee000000 0x0ffeffffff018000

def z765 : W := mkw 0xa4f8126db48d4ed2 0xf6f636ef749d4f93

def z766 : W := mkw 0x4404104925001025 0xfef736e97403f0ff

def z767 : W := mkw 0x0f00fddfee520000 0x1ffefffffffff000

def z768 : W := mkw 0x0ad0efb258fbe518 0x3c7ffffe70ffff1c

def z769 : W := mkw 0x0a90470258a18518 0xffffcf1fffe1cf9f

def z770 : W := mkw 0x0a90470258a18518 0x3fbfcf0e78e38f1c

def z771 : W := mkw 0x0f00fddfee000000 0x03fa3ff1ff000000

def z772 : W := mkw 0x0a90470258a18518 0xffffcf0ffce3cfff

def z773 : W := mkw 0xe0fc0220118d5cb7 0xf4000000009f7cf3

def z774 : W := mkw 0x00c0022000fbe000 0x1c0436e000fff000

def z775 : W := mkw 0x0b0045d26e000000 0x3ffb0ff1ff0200e0

def z776 : W := mkw 0x07c0126feefbe000 0x1f80000ffffff000

def z777 : W := mkw 0x00c0aab000fbe000 0x1c0030e000fff000

def z778 : W := mkw 0x4b04ed96cb521265 0x0909c9168b62b36c

def z779 : W := mkw 0x08d0efb010fbe518 0x3dfffffe00ffff1c

def z780 : W := mkw 0x4a94470259a1953d 0xd054ce1ff7e27fe3

def z781 : W := mkw 0x0a90470258a18518 0x3fbfc70f78e18f9c

def z782 : W := mkw 0x0f00fddfee520000 0x3ffffffffffe0f00

def z783 : W := mkw 0x0420100d80040ac0 0x3d9ff00f80fc0fe0

def z784 : W := mkw 0x4004000001001025 0xebe909118f03f0ff

def z785 : W := mkw 0xa4f81269348d4c92 0xffff36e9749d4c93

def z786 : W := mkw 0xaad8472258a9c51a 0xefafc70e78e1cf1f

def z787 : W := mkw 0x00c0022000894000 0x147637f0009df000

def z788 : W := mkw 0x0420b84da4560ac0 0x3ddff8ef84fe0fe0

def z789 : W := mkw 0x0f00fddfee000000 0x13feffffff0200e0

def z790 : W := mkw 0x4ad447b259a9f53d 0xc26007f07f01f01f

def z791 : W := mkw 0x0020a80000560ac0 0x3d9ff80e00fe0fe0

def z792 : W := mkw 0x08c0efb000fbe000 0x1ffefff008fff000

def z793 : W := mkw 0x0f20fddfee560ac0 0x3fffffffffff8ffc

def z794 : W := mkw 0x0f00fddfee000000 0xc3feffffff014013

def z795 : W := mkw 0x0a90470258a18518 0x2b8dc70e78e08f1c

def z796 : W := mkw 0x0ad0efb258fbe518 0x1d7ffffe78ffff0c

def z797 : W := mkw 0x0f00fddfee000000 0x03aef7efff000000

def z798 : W := mkw 0x0420b80d80560ac0 0x3597f00f80fc0fe0

def z799 : W := mkw 0x0520b8dda6560ac0 0x3ffffefff7fe0fe0

def z800 : W := mkw 0x0040a8b0005a6000 0x107a39f0001e7000

def z801 : W := mkw 0x0ad0472258a9c518 0x3ffffffe78ffff1c

def z802 : W := mkw 0xa4f81269348d4c92 0xf6f637f97f9d4c93

def z803 : W := mkw 0xa0d8026034894412 0xd27036e0741d4013

def z804 : W := mkw 0xae68556b6c2cc98a 0xd959f1e70c7cc38f

def z805 : W := mkw 0x0a90470258a18518 0x0b2dc70e78e18f1c

def z806 : W := mkw 0x0a90470258a18518 0x26a6c70e78e18f1c

def z807 : W := mkw 0x0f20fddfee560ac0 0x12703ff1ff1e00e0

def z808 : W := mkw 0xe0fc0220118d5cb7 0xf4010000009d4cff

def z809 : W := mkw 0x0b0045d26e000000 0xf6f207f17f014093

def z810 : W := mkw 0x0ac0efb248fbe108 0x3dfffffe08ffff0c

def z811 : W := mkw 0xa5f8126db68d4c92 0xf6f636e9f79d4c93

def z812 : W := mkw 0x0420b80d80560ac0 0x3d19f80780fe0fe0

def z813 : W := mkw 0xa0d8aa64b4db4652 0xcb69cee6f4634373

def z814 : W := mkw 0x0f00fddfee72a108 0x0bffffffff62b30c

def z815 : W := mkw 0x0a90470258a18518 0x2d8fc60e70e18f1c

def z816 : W := mkw 0xa4f81269348d4c92 0xf7f736e97c9d4c9f

def z817 : W := mkw 0x0a90470258a18518 0x3fffc70e78e1cf1c

def z818 : W := mkw 0x0f00fddfee520000 0x0bfeffffff620000

def z819 : W := mkw 0x0520b84da6560ac0 0x3d9ff80f87fe0fe0

def z820 : W := mkw 0x0f00fddfee000000 0x13feffffff027000

def z821 : W := mkw 0x0f00554fee000000 0x03fef7efff000000

def z822 : W := mkw 0x0b0045d26e000000 0x03e007fe7f000000

def z823 : W := mkw 0x0a10450258208518 0x2bafc70e78608f1c

def z824 : W := mkw 0x0420b89d80560ac0 0x3ddff8ff80fe0fe0

def z825 : W := mkw 0x0840edb0007ae000 0x187efff0007ef000

def z826 : W := mkw 0xa4681069240c4882 0xf6f636e9741d4093

def z827 : W := mkw 0x0400b84da4000000 0x03feffffff000000

def z828 : W := mkw 0x0f2055db6e040880 0x36f637f97f9c0c80

def z829 : W := mkw 0x0ad0efb258fbe518 0x1054fefe70fe7f00

def z830 : W := mkw 0xa0f80220108d4c92 0xf6f636e8709d4c93

def z831 : W := mkw 0x0ad047b258a9e518 0x2fafc7ee78e18f1c

def z832 : W := mkw 0x08c0efb000fbe000 0x3dfffff000fff000

def z833 : W := mkw 0x0f20fddfee040ac0 0x2fffffffffe00fe0

def z834 : W := mkw 0x0290020258a18518 0x2f8fc00e78e18f1c

def z835 : W := mkw 0x0400104924000000 0x03f636e9ff000000

def z836 : W := mkw 0x0ad047b258a9e518 0x3ffff7fe78fdff1c

def z837 : W := mkw 0x0c00fdd924000000 0x03fefff9ff000000

def z838 : W := mkw 0x0700104fee000000 0x038436efff000000

def z839 : W := mkw 0x0040a8b0005a6000 0x1c5a38f0001e7000

def z840 : W := mkw 0x00d0022010894410 0xf6f636e9749d4c93

def z841 : W := mkw 0x0420b80d80560ac0 0x1d1ff80e80fe0f60

def z842 : W := mkw 0xa4f81269348d4c92 0xc00436e8709d4c13

def z843 : W := mkw 0x0210000258000518 0x2b89c00e78600f1c

def z844 : W := mkw 0x08c0efb000894000 0x1c7efff0009ff000

def z845 : W := mkw 0x0f00fddfee000000 0x007efffff7000000

def z846 : W := mkw 0xabf8efb6da8d4c92 0xf508c9168b9d4c93

def z847 : W := mkw 0x0a90470258a18518 0xffffcf1f7ce3ff9f

def z848 : W := mkw 0x0040a8b0005a6000 0x100030e0001e7000

def z849 : W := mkw 0xa4f8126934adec92 0xf6f636e9749dfc93

def z850 : W := mkw 0x0a90470258a18518 0x2fffcf1e78e18f1c

def z851 : W := mkw 0x0f20fddfee040880 0x13feffffff1c0080

def z852 : W := mkw 0xa4f81269348d4c92 0xfef736e9749f4cf3

def z853 : W := mkw 0xa4f81269348d4c92 0xc2f636e9749d4c13

def z854 : W := mkw 0x0f20fddfee040880 0xf7feffffff9d4c93

def z855 : W := mkw 0x0b0045d26e000000 0x020006e07f000000

def z856 : W := mkw 0x48c4efb001fbf025 0xe385f6e18ffc00ff

def z857 : W := mkw 0xa4f81269348d4c92 0xffff3ff97c9ffc9f

def z858 : W := mkw 0x0420b80d80560ac0 0x0105f00e80fc0f60

def z859 : W := mkw 0x4424b80d81561ae5 0xc264f11e0ffdff1f

def z860 : W := mkw 0x0420b80d80560ac0 0x3d9ff91f80febfe0

def z861 : W := mkw 0x0040a8b4805a6240 0x105038f0801e7060

def z862 : W := mkw 0xa4f81269348d4c92 0xf2f036e9741d4c93

def z863 : W := mkw 0x0f00fddfee208108 0x2fffffffff61831c

def z864 : W := mkw 0x0f00fddfee000000 0x3fffffffffe20fe0

def z865 : W := mkw 0x0040a8b0007ae000 0x185038f0007ef000

def z866 : W := mkw 0x0a90470258a18518 0x2f89c10e78e18f1c

def z867 : W := mkw 0x0f00fddfee000000 0x0bffffffff600300

def z868 : W := mkw 0x40d4022011fbf53d 0xfc01000000ffffff

def z869 : W := mkw 0x0250a8b2585a6518 0x33d138fe781e7f1c

def z870 : W := mkw 0x0420100900560ac0 0x3d9ff00f00fe0fe0

def z871 : W := mkw 0x08c0efb000fbe000 0x3c7ffff000ffff00

def z872 : W := mkw 0x0b0045d26e000000 0x004006f077000000

def z873 : W := mkw 0x0420b80d80560ac0 0x3d89c80f80fe0fe0

def z874 : W := mkw 0x0b0045d26e000000 0x03e007f1ff000000

def z875 : W := mkw 0x0420b80d80560ac0 0x3fbff90f88fe0fe0

def z876 : W := mkw 0xa4f8126db48d4ed2 0xfffff6eff4fd4ff3

def z877 : W := mkw 0x0f20fddfee560880 0x3ffefffffffe0c80

def z878 : W := mkw 0x0b0045d26e20a000 0x026007f07f00b000

def z879 : W := mkw 0x08c0472000a9c000 0x1c7efff000fff000

def z880 : W := mkw 0x0ce057bd80adeac0 0x21e107ff8001ffe0

def z881 : W := mkw 0x0a10450258208518 0x2381c00e78600f1c

def z882 : W := mkw 0x08c047b000fbe000 0x1c7637f000fff000

def z883 : W := mkw 0x0b0045d26e000000 0x03ea07f07f000000

def z884 : W := mkw 0x0420b80d80560ac0 0x3c97f00f00fe0fe0

def z885 : W := mkw 0x08c0efb480fbe000 0x1d7efff680fff000

def z886 : W := mkw 0x0420b80d80560ac0 0x3f9ff80f88fe0ffc

def z887 : W := mkw 0x0a90470258a18518 0x2ffff7ee78e18f1c

def z888 : W := mkw 0xa4f81269348d4c92 0xf47636e8709d4c93

def z889 : W := mkw 0x0420b84da4560ac0 0x3ffffffffffe0fe0

def z890 : W := mkw 0x0f00fddfee000000 0x0044f6fe77000000

def z891 : W := mkw 0x0420b80d80560ac0 0x3d85f00f80fe0fe0

def z892 : W := mkw 0x0f00fddfee72a240 0x0bffffffff62b360

def z893 : W := mkw 0x0f00fddfee000000 0x0004f6eff7000000

def z894 : W := mkw 0x0a10450258208518 0x2fabc10e78618f1c

def z895 : W := mkw 0x0420b80d80560ac0 0xfd9ff80f80ff4ff3

def z896 : W := mkw 0x0a90470258a18518 0x3fffcf1fffe38ffc

def z897 : W := mkw 0x0ac0efb248fbe000 0x3ffffffe78ffff00

def z898 : W := mkw 0x0bc0efb6cafbe108 0x1d7ffff68bfff30c

def z899 : W := mkw 0x00c0aa2000db4000 0x1c7efff000fff000

def z900 : W := mkw 0x08c0efb000fbe000 0x1004f6e000fe7000

def z901 : W := mkw 0x0ad0472258fbe518 0x3ffff7ee78ffff1c

def z902 : W := mkw 0xa4f81269348d4c92 0xf69636e9749c0c93

def z903 : W := mkw 0x0840edb0007ae000 0x105039f0001ef000

def z904 : W := mkw 0xa4f81269348d4c92 0xfffffeeff4ff4ff3

def z905 : W := mkw 0xa4f81269348d4c92 0xf49636e9709d4c93

def z906 : W := mkw 0x0bc0efb6cafbe000 0x1ffefffefbfff000

def z907 : W := mkw 0x0840edb0005a6000 0x10703ff0001e7000

def z908 : W := mkw 0x0f00fddfee000000 0x17feffffff9c0000

def z909 : W := mkw 0xa0d8026034894412 0xf6f636e8749d4c13

def z910 : W := mkw 0x010000d026000000 0x026006f077000000

def z911 : W := mkw 0xeadc47627da9d53f 0xc26007f07f01f01f

def z912 : W := mkw 0x08d0efb010fbe410 0x3ffffffe70ffff10

def z913 : W := mkw 0x0f00fddfee72a000 0x03feffffff600000

def z914 : W := mkw 0x0f20fddfee560ac0 0x0bfffffffffe0f60

def z915 : W := mkw 0xa4f81269348d4c92 0xe6a636e9749d0c93

def z916 : W := mkw 0x0420b80d80560ac0 0x1004f00e00fe0fe0

def z917 : W := mkw 0x08c0efb000fbe000 0x1476f7f000fdf000

def z918 : W := mkw 0xa4f8126db48d4ed2 0xf6f636e9f49d4cf3

def z919 : W := mkw 0xe42c1049250418a7 0xc0000001870000e3

def z920 : W := mkw 0x0420b80d80560ac0 0x3ffff91f8fffffe0

def z921 : W := mkw 0x4004000001001025 0xfd5909118f03f0ff

def z922 : W := mkw 0x00c0022000db6000 0x147636e0009f7000

def z923 : W := mkw 0xa4f81269348d4c92 0xfefef6e974fd4c93

def z924 : W := mkw 0x0bc0efb6cafbe000 0x1c7efff600fff000

def z925 : W := mkw 0x0f20fddfee040880 0x3ffffffffffc0f80

def z926 : W := mkw 0x0ac0efb248fbe000 0x1e7efff078fff000

def z927 : W := mkw 0x0f00fddfee522000 0x03feffffff023000

def z928 : W := mkw 0xa4f81269348d4c92 0xfffff7ef7cfdcf9f

def z929 : W := mkw 0x0420b80d80560ac0 0xfffff91f84fffff3

def z930 : W := mkw 0x0020000000560ac0 0x3d09c00600fe0fe0

def z931 : W := mkw 0x0f20fddfee560ac0 0x3fffffffffffffe0

def z932 : W := mkw 0x0420b80d80560ac0 0x3d8ff00e00fe0fe0

def z933 : W := mkw 0x0f00fddfee000000 0x03feffffffe00f00

def z934 : W := mkw 0xe0fc022011adddbf 0xfc01000000ffffff

def z935 : W := mkw 0x0420b80d80560ac0 0x0805f00e00fe0f60

def z936 : W := mkw 0x08c0efb000fbe000 0x3ffffffe08ffff1c

def z937 : W := mkw 0x0f20fddfee560ac0 0x3ddffefff7fe0fe0

def z938 : W := mkw 0xa0f80260348d4c92 0xf67636e0749d4c93

def z939 : W := mkw 0x08c0efb000fbe000 0x1c703ff000fff000

def z940 : W := mkw 0x0f20fddfee76aac0 0x3ffffffffffebfe0

def z941 : W := mkw 0xa4f8126db48d4ed2 0xffff3eeff49f4ff3

def z942 : W := mkw 0x0f00fddfee000000 0x3fffffffff03f0e0

def z943 : W := mkw 0x4004000001001025 0xfffb09118fe3ffff

def z944 : W := mkw 0x0040002000084000 0x105038f0001e7000

def z945 : W := mkw 0x0a90470258a18518 0x0004c60e70e18f1c

def z946 : W := mkw 0x08c0efb000fbe000 0x1c7efffe00ffff00

def z947 : W := mkw 0x0420b80d80560ac0 0x3fbffe0ff0fe0fe0

def z948 : W := mkw 0xac38fdd93476ac92 0xea88c9197462bc93

def z949 : W := mkw 0x0ac0efb248fbe108 0x1c7efff008fff00c

def z950 : W := mkw 0xa4f81269348d4c92 0xd00436e8709c4c83

def z951 : W := mkw 0x0f00fddfee000000 0x0378fff7ff000000

def z952 : W := mkw 0x08d0efb010fbe518 0x1c7efff000fff01c

def z953 : W := mkw 0x0b0045d26e000000 0x03680ff0ff000000

def z954 : W := mkw 0x0a90479258a18518 0x2fefc7fe78e18f1c

def z955 : W := mkw 0x0420b80d80560ac0 0x3ffff91f8fff8ffc

def z956 : W := mkw 0x08c0efb000fbe000 0x1e7efff00ffff000

def z957 : W := mkw 0x0040a8b0005a6000 0x105038f1801e70e0

def z958 : W := mkw 0x0ad0efb258fbe518 0xffffffff7cffff9f

def z959 : W := mkw 0x0420b80d80560ac0 0x219ff80f80fc0fe0

def z960 : W := mkw 0x0f20fddfee560ac0 0x23fffffffffc0fe0

def z961 : W := mkw 0x0a00ed9248000000 0x03feffffff000000

def z962 : W := mkw 0x0f00fddfee000000 0x03d4feffff000000

def z963 : W := mkw 0x0bd0efb6dafbe518 0x3ffffffefbffff1c

def z964 : W := mkw 0x0040a8b0005a6000 0x1858f8f0007e7000

def z965 : W := mkw 0x00c0aab000fbe000 0x105038f0001ff000

def z966 : W := mkw 0x0ad047b258a9e518 0x3fffcffe78e3ff1c

def z967 : W := mkw 0xa4f81269348d4c92 0xf6f63ef9f79d4c93

def z968 : W := mkw 0x0f00fddfee000000 0x0bffffffff00800c

def z969 : W := mkw 0x0020a80480560ac0 0x3d9bc80780fe0fe0

def z970 : W := mkw 0x004000b000086000 0x105030f0001c7000

def z971 : W := mkw 0xa4781069340c4c92 0xf2f636e9741c4c93

def z972 : W := mkw 0xe0fc022011fffcb7 0xfc01000000fffcff

def z973 : W := mkw 0x0f00fddfee000000 0x03e4f7ffff000000

def z974 : W := mkw 0x0ad0efb258fbe518 0x3e7ffff078ffff1c

def z975 : W := mkw 0x4a04ed924972b12d 0x0909c9168b62b36c

def z976 : W := mkw 0x0a90470258a18518 0x2fffc70f7ce18f1c

def z977 : W := mkw 0x0f00fddfee520240 0x3fffffffff6203e0

def z978 : W := mkw 0x0b0045d26e000000 0x1e7a0ff07f03f000

def z979 : W := mkw 0x0040a8b0005a6000 0x000038f0001e3000

def z980 : W := mkw 0x0f00fddfee000000 0x039efeefff000000

def z981 : W := mkw 0x4524b8dda7561ae5 0xd05038f1871e70e3

def z982 : W := mkw 0x0f00fddfee000000 0x0ffeffffffe00000

def z983 : W := mkw 0xa438104934040c92 0xf6f636e9749c0c93

def z984 : W := mkw 0x0ac0efb248fbe000 0x1c7efffe70fff000

def z985 : W := mkw 0x0ad0efb258fbe518 0x3d7ffff608ffff1c

def z986 : W := mkw 0x0f00fddfee000000 0x03feffffff01f000

def z987 : W := mkw 0x08c047b000a9e000 0x1c7ef7f000fdf000

def z988 : W := mkw 0x08c0efb000fbe000 0x10503ef0001e7000

def z989 : W := mkw 0x0f00fddfee000000 0x03eef7fe7f000000

def z990 : W := mkw 0x0f20fddfee560ac0 0x2385f6effffc0fe0

def z991 : W := mkw 0x0a90470258a18518 0x2d0dc70e78e18f1c

def z992 : W := mkw 0x0700104fee000000 0x03e006efff000000

def z993 : W := mkw 0x0f00fddfee208000 0x0bfeffffff608000

def z994 : W := mkw 0x0f00fddfee000000 0x23ffffffff000f00

def z995 : W := mkw 0x0040a8b0005a6000 0x13fa39f18f1e7000

def z996 : W := mkw 0xe73c104fff041cb7 0xe381000fff000cff

def z997 : W := mkw 0x08c0efb000fbe000 0x0c2efff000ffb000

def z998 : W := mkw 0x0a00450248208108 0x2fafc70e78e08f0c

def z999 : W := mkw 0x08c0efb000fbe000 0x1c1efee000fff000

def z1000 : W := mkw 0x0040a8b4805a6240 0x1959f8f6807e7360

def z1001 : W := mkw 0x08c0efb000fbe000 0x3c7ffff000fff01c

def z1002 : W := mkw 0x0720b84fee560ac0 0x3ffffeeffffe0fe0

def z1003 : W := mkw 0xe63c104b7d041dbf 0xe381000fff000fff

def z1004 : W := mkw 0x08c0efb000fbe000 0x1dfefffe00fff000

def z1005 : W := mkw 0x0b0045d26e000000 0x027637f07f000000

def z1006 : W := mkw 0x0420b80d80560ac0 0x3c1ff80e00fe0fe0

def z1007 : W := mkw 0x0f00fddfee000000 0xe3feffffff000093

def z1008 : W := mkw 0x4004000001001025 0xffff0f19ff03f0ff

def z1009 : W := mkw 0x4f04fddfef001025 0xfc05f6ee7003f0ff

def z1010 : W := mkw 0xa4f81269348d4c92 0xffff3ff9ff9f4cf3

def z1011 : W := mkw 0x04c0126924894000 0xf6f636e9749d4093

def z1012 : W := mkw 0x0ad0efb258fbe518 0x3efefff878fffc1c

def z1013 : W := mkw 0x0f00fddfee000000 0x3fffffffff03f01c

def z1014 : W := mkw 0x0a90470258a18518 0x0004c70e78e08f0c

def z1015 : W := mkw 0x00d0aab010db6410 0x36f63ef8709f7c10

def z1016 : W := mkw 0x0020a80480560ac0 0x0909c80680fe0f60

def z1017 : W := mkw 0x0b0045d26e000000 0x03fecfffff000000

def z1018 : W := mkw 0x0420b80d80560ac0 0x2005f00e00fc0fe0

def z1019 : W := mkw 0x0ac0efb248fbe000 0x1d7efff608fff000

def z1020 : W := mkw 0x0b00edd26e000000 0x03fefff1ff000000

def z1021 : W := mkw 0x0b0045d26e208108 0x026007f07f00800c

def z1022 : W := mkw 0xe4fc1269358d5cb7 0x090d3ff8fb9ebc6c

def z1023 : W := mkw 0x0520b8dda6560ac0 0x36f63ef9f79e0ce0

def z1024 : W := mkw 0x0b0045d6ee000000 0x036007f6ff000000

def z1025 : W := mkw 0x4004000001001025 0xffffc91f8f03f0ff

def z1026 : W := mkw 0x0420b80d80560ac0 0x298df80f80fe0fe0

def z1027 : W := mkw 0x0040a8b0005a6000 0x1c5038f0001ff000

def z1028 : W := mkw 0x0040a8b0005a6000 0x10763ef0001e7000

def z1029 : W := mkw 0x08c0efb000fbe000 0x1c64f7f000fff000

def z1030 : W := mkw 0x0040002000084000 0x1c7a39f0001ff000

def z1031 : W := mkw 0xa428b84da4560ac2 0xfd9ff80f84fe0fe3

def z1032 : W := mkw 0xa4d8126934894412 0xd6f636e9749d4013

def z1033 : W := mkw 0x0f00fddfee728348 0x0bffffffff62836c

def z1034 : W := mkw 0x08c0efb000fbe240 0x1c7ffff000fff360

def z1035 : W := mkw 0x0f00fddfee000000 0xd3feffffff004083

def z1036 : W := mkw 0x0f00fddfee520240 0x03feffffff600300

def z1037 : W := mkw 0x0f00fddfee000000 0x017efffefb000000

def z1038 : W := mkw 0x0b0045d26e000000 0x0368c7f67f000000

def z1039 : W := mkw 0xe0fc022011df5ef7 0xfc01000000ffffff

def z1040 : W := mkw 0x0090020010a18518 0x2fafc60e70e18f1c

def z1041 : W := mkw 0x08c0efb000fbe108 0x1c7ffff000fff30c

def z1042 : W := mkw 0x0f00fddfee520000 0x3ffffffffffe00e0

def z1043 : W := mkw 0x0ad0472258a9c518 0xfffff7ef7cfdcf9f

def z1044 : W := mkw 0x08c0efb000fbe000 0x006037f0001df000

def z1045 : W := mkw 0x0420b80d80560ac0 0x3ffff91f88fffffc

def z1046 : W := mkw 0xa4f81269348d4c92 0xf45436e9749d4c93

def z1047 : W := mkw 0x0f00fddfee000000 0x03feffffff01801c

def z1048 : W := mkw 0x0500104da6000000 0x02f636e9f7000000

def z1049 : W := mkw 0x08d0efb010fbe410 0x1e7efff070fff010

def z1050 : W := mkw 0x00c0022000a9e000 0x147636e0009df000

def z1051 : W := mkw 0x00c0aab000fbe000 0x1c5ef8f000fff000

def z1052 : W := mkw 0x0f00fddfee000000 0x036cfffeff000000

def z1053 : W := mkw 0x0ad0efb258fbe518 0x3ffffff078fff01c

def z1054 : W := mkw 0xa4f81269348d4c92 0xf7fef6ef749d4c93

def z1055 : W := mkw 0xa4f81269348d4c92 0xd67636e1749d4093

def z1056 : W := mkw 0x0ac0efb6c8fbe348 0x1d7ffff688fff36c

def z1057 : W := mkw 0x0700104b6e000000 0x02f636e97f000000

def z1058 : W := mkw 0x0bc0efb24afbe000 0x1c7efff00bfff000

def z1059 : W := mkw 0x0040a8b0005a6000 0x3ddb38f1801e70e0

def z1060 : W := mkw 0x0020a80480560ac0 0x3c01c00600fe0fe0

def z1061 : W := mkw 0x0700b84fee000000 0x03fefeefff000000

def z1062 : W := mkw 0x0f00fddfee000000 0x2fffffffff000000

def z1063 : W := mkw 0xa4f81269348d4ed2 0xf6f736e9749d4ff3

def z1064 : W := mkw 0xa4f81269348d4c92 0xd47636e9749d4c83

def z1065 : W := mkw 0x0140a8b4825a6000 0x105038f0831e7000

def z1066 : W := mkw 0x0040a8b0005a6000 0x1c5038f000fe7000

def z1067 : W := mkw 0x0400104924000000 0x02f63ef9f7000000

def z1068 : W := mkw 0x0f20fddfee040880 0x23feffffff000c80

def z1069 : W := mkw 0x08c0efb000db6000 0x147efff0009f7000

def z1070 : W := mkw 0x0420b80d80560ac0 0x3c15f80f80fe0fe0

def z1071 : W := mkw 0x08c0efb000fbe000 0x1e7efff008fff01c

def z1072 : W := mkw 0x0840edb0007ae000 0x1c7af9f0007ff000

def z1073 : W := mkw 0x08c0efb000fbe000 0x0004f6e000fdf000

def z1074 : W := mkw 0xa4f81269348d4c92 0xe2f636e9749c0c93

def z1075 : W := mkw 0x0f00fddfee000000 0x0104f6eefb000000

def z1076 : W := mkw 0x0ad0efb258fbe518 0x0264f7fe78fdff1c

def z1077 : W := mkw 0x0a90470258a18518 0x2ba9c70e78618f1c

def z1078 : W := mkw 0x0f0055db6e000000 0x03fe3ff9ff000000

def z1079 : W := mkw 0xa4f81269348d4c92 0xf7f636e9ff9d4c93

def z1080 : W := mkw 0x0f00fddfee72a000 0x1ffefffffffeb000

def z1081 : W := mkw 0x0a90470258a18518 0x2fafcf1efbe18f1c

def z1082 : W := mkw 0x0b00edd26e000000 0x03fefffe7f000000

def z1083 : W := mkw 0x0800ed9000520000 0x1c7efff000fff000

def z1084 : W := mkw 0x08c0efb000fbe000 0x1d7ffff008fff00c

def z1085 : W := mkw 0x0590baddb6a18518 0x2c5138f187e18f1c

def z1086 : W := mkw 0x08c0efb000fbe000 0xfc7efff000fff093

def z1087 : W := mkw 0x0f20fddfee560ac0 0x37fefffffffc0f80

def z1088 : W := mkw 0xa438104934040c92 0xfefa09197403fc93

def z1089 : W := mkw 0x0f20fddfee560ac0 0x1ffefffffffe0f00

def z1090 : W := mkw 0x0ad0efb258fbe518 0x1ffefffe78ffff00

def z1091 : W := mkw 0xa4f81269348d4c92 0xc20436e8749c0c13

def z1092 : W := mkw 0x0a90470258a18518 0x03aec70e78e18f1c

def z1093 : W := mkw 0x0500b8dda6000000 0x02703ef1f7000000

def z1094 : W := mkw 0x0f0055db6e000000 0x02e007f97f000000

def z1095 : W := mkw 0x0a10450258208518 0x0909c10e78608f0c

def z1096 : W := mkw 0x0290020258810518 0x2fafc60e78e10f1c

def z1097 : W := mkw 0x0040a8b0005a6000 0xf6f238f1041f7093

def z1098 : W := mkw 0xe43c104935041cb7 0xe2800009f7000cf3

def z1099 : W := mkw 0x08c047b000a9e000 0x006437f0009df000

def z1100 : W := mkw 0x0f00fddfee000000 0x3fffffffff0380fc

def z1101 : W := mkw 0x0210000258000518 0x2385c00e78e00f1c

def z1102 : W := mkw 0x0ad0efb258fbe410 0x3ffefffe78fffc10

def z1103 : W := mkw 0x0420b80d80560ac0 0x3ffff80f84fe0fe0

def z1104 : W := mkw 0x0040a8b0005a6000 0x105038f1871e7000

def z1105 : W := mkw 0xa4f8126db48d4c92 0xf7f636eff49d4c93

def z1106 : W := mkw 0x0f00fddfee520000 0x03fefffffffc0000

def z1107 : W := mkw 0x0b00edd6ee000000 0x02600ff0ff000000

def z1108 : W := mkw 0xa4f81269348d4c92 0xf6a636e8709d4c93

def z1109 : W := mkw 0x08c0efb000fbe000 0x3dffffff80ffffe0

def z1110 : W := mkw 0x0b0045d26e000000 0x2fefc7fe7fe00f00

def z1111 : W := mkw 0x0520b8dda6560ac0 0x3ffff9ff8ffe0fe0

def z1112 : W := mkw 0x0a90470258a18518 0x27a7c60e78e10f1c

def z1113 : W := mkw 0x0f00fddfee000000 0x2fffffffffe18f1c

def z1114 : W := mkw 0x0840edb0005a6000 0x1c7efff0001ff000

def z1115 : W := mkw 0x0b00edd26e000000 0x0268cff07f000000

def z1116 : W := mkw 0x0420b80d80560ac0 0x3d0df80e80fe0fe0

def z1117 : W := mkw 0x0f00fddfee000000 0x27feffffff800c00

def z1118 : W := mkw 0x0b00ed96ca000000 0x03fefffefb000000

def z1119 : W := mkw 0x0b9047925aa18518 0x2fafc71e7be18f1c

def z1120 : W := mkw 0x0a90470258a18518 0x2ea7c60e70e18f1c

def z1121 : W := mkw 0x08c0efb000fbe000 0xfffffff10cfff09f

def z1122 : W := mkw 0x0ad0efb258fbe518 0x12703ff0781ff01c

def z1123 : W := mkw 0x0b0045d26e000000 0x000007f07b000000

def z1124 : W := mkw 0x08c0efb000fbe000 0x0044f6f000fc7000

def z1125 : W := mkw 0x0840edb0005a6000 0x1c7efff000fe7000

def z1126 : W := mkw 0x0a90470258a18518 0x0204c60e78e00f1c

def z1127 : W := mkw 0x08c0efb000fbe000 0x1476fef000ff7000

def z1128 : W := mkw 0x0f20fddfee560ac0 0x0264f7fe7ffc0f00

def z1129 : W := mkw 0x0a90470258a18518 0x0e2ec70e78e18f1c

def z1130 : W := mkw 0x0ad0efb6d8fbe758 0x3ffffffef8ffff7c

def z1131 : W := mkw 0x0a90470258a18518 0x0bafc70e78e08f0c

def z1132 : W := mkw 0x030000426e000000 0x026006e07f000000

def z1133 : W := mkw 0x08c0efb000fbe000 0x0004f7f000fcb000

def z1134 : W := mkw 0x0a90470258a18518 0x2fafcf1e78e3bf1c

def z1135 : W := mkw 0x08c0efb000fbe000 0xdc7efff104fff083

def z1136 : W := mkw 0x0f00fddfee000000 0x0004fefef3000000

def z1137 : W := mkw 0x00c0aa2000fbe000 0x1c7efee000fff000

def z1138 : W := mkw 0x0f00fddfee000000 0x27feffffff010010

def z1139 : W := mkw 0x0a10450258000518 0x2fafc70e78e00f1c

def z1140 : W := mkw 0x0040a8b0005a6000 0x004030f0001c7000

def z1141 : W := mkw 0x08c0efb000fbe000 0x185cfff000fef000

def z1142 : W := mkw 0x0b00edd26e000000 0x02703ff07f000000

def z1143 : W := mkw 0xa4f81269348d4c92 0xf67036e1749d4c93

def z1144 : W := mkw 0x0f20fddfee560ac0 0x1054fefff7fe0fe0

def z1145 : W := mkw 0x0e00554b6c000000 0x03feffffff000000

def z1146 : W := mkw 0xa4f81269348d4c92 0xd05036e1741c4083

def z1147 : W := mkw 0x0ac0efb248fbe108 0x1c7efff600fff300

def z1148 : W := mkw 0x0b0045d26e000000 0xc26007f07f014013

def z1149 : W := mkw 0x0f0055dfee000000 0x03f637ffff000000

def z1150 : W := mkw 0x0800ed900072a000 0x1c7efff000feb000

def z1151 : W := mkw 0xa4f81269348d4c92 0xf4d636e9749c4c83

def z1152 : W := mkw 0x00c0aab000db6000 0x10703ef0001f7000

def z1153 : W := mkw 0x0f20fddfee560ac0 0x13fefffffffe0fe0

def z1154 : W := mkw 0x0500b8dda6000000 0x00543ef9f7000000

def z1155 : W := mkw 0x050010d926000000 0x02f636f977000000

def z1156 : W := mkw 0x00c0022000894000 0x1c7636e0009ff000

def z1157 : W := mkw 0x0500b8dda6000000 0x03fefefff7000000

def z1158 : W := mkw 0x0f0055db6e000000 0x03fef7ff7f000000

def z1159 : W := mkw 0x0040a8b0005a6000 0x107039f0001ff000

def z1160 : W := mkw 0x0420b80d80560ac0 0x3dfffeef80fe0fe0

def z1161 : W := mkw 0x0420b80d80560ac0 0x3d9ff91f8bfe0fe0

def z1162 : W := mkw 0x0f00fddfee000000 0x17feffffff014000

def z1163 : W := mkw 0x4004000001001025 0xffff39118f9ff0ff

def z1164 : W := mkw 0x00d0aab010fbe518 0x3c5138f000ffff1c

def z1165 : W := mkw 0x0f00fddfee000000 0x01defefff7000000

def z1166 : W := mkw 0x0420b80d80560ac0 0x191df80f80fe0fe0

def z1167 : W := mkw 0x08c0efb000fbe000 0x107efff0001ff000

def z1168 : W := mkw 0x0b0045d26e000000 0x2feb07f07f01801c

def z1169 : W := mkw 0x0a90470258a18518 0x2fafcf0ef8e38f7c

def z1170 : W := mkw 0x0a90470258a18518 0x2fefc71e7fe18f1c

def z1171 : W := mkw 0x0f20fddfee768bc8 0x3ffffffffffe8fec

def z1172 : W := mkw 0x0b00edd6ee000000 0x037efff6ff000000

def z1173 : W := mkw 0x0f20fddfee560ac0 0x3d9ffffffbfe0fe0

def z1174 : W := mkw 0xe0dc022011895437 0xc00000000001f01f

def z1175 : W := mkw 0xe0dc022011895437 0xfc0100000003f0ff

def z1176 : W := mkw 0x00d0022010fbe518 0x3ef736e870ffff1c

def z1177 : W := mkw 0x0f0055dfee000000 0x026007f1ff000000

def z1178 : W := mkw 0x0f00fddfee000000 0x0bfeffffff02b000

def z1179 : W := mkw 0x0b00edd6ee520240 0x0b69cff6ff620360

def z1180 : W := mkw 0x08c0efb000fbe000 0x3cfefff800fffc00

def z1181 : W := mkw 0x0bc0efb6cafbe240 0x1d7ffff68bfff360

def z1182 : W := mkw 0x0040a8b0005a6000 0x147238f0001f7000

def z1183 : W := mkw 0x0210000258000518 0x2fafc10e78e18f1c

def z1184 : W := mkw 0x0b00edd6ee000000 0x0260c7f67f000000

def z1185 : W := mkw 0x08c0efb480fbe240 0x1c7efff600fff300

def z1186 : W := mkw 0x4004000001001025 0xfffb091f8f03ffff

def z1187 : W := mkw 0x0a90470258a18518 0x2fafc70fffe18f1c

def z1188 : W := mkw 0x0a90470258a18518 0x3fafc70e78e3ff1c

def z1189 : W := mkw 0xa4f8126934adcd9a 0xf6f636e9749dcc9f

def z1190 : W := mkw 0x00c0aab000fbe000 0x1c763ef000fff000

def z1191 : W := mkw 0x08c0efb000fbe000 0x1c76f6e000fff000

def z1192 : W := mkw 0x0040a8b0005a6000 0x185839f0001ef000

def z1193 : W := mkw 0xa4f81269348d4c92 0xfffe3ff9ff9ffc93

def z1194 : W := mkw 0xa4f81269348d4c92 0xf7fe3ee9f49d4c93

def z1195 : W := mkw 0x08c0efb000fbe000 0x007efff000fdf000

def z1196 : W := mkw 0x4004000001001025 0xfe7109118f03f0ff

def z1197 : W := mkw 0x0f20fddfee560ac0 0xffffffffffff4ff3

def z1198 : W := mkw 0x0f20fddfee560ac0 0x1bffffffff7e03e0

def z1199 : W := mkw 0x0b0045d26e000000 0x02f207f17f000000

def z1200 : W := mkw 0x0020000000560ac0 0x3d9fc80f80fe0fe0

def z1201 : W := mkw 0x0420b80d80560ac0 0xfddff80f84fe4fe3

def z1202 : W := mkw 0x4004000001001025 0xde7a09118f03f0ff

def z1203 : W := mkw 0x0020a80480560ac0 0x3d1ff80680fe0fe0

def z1204 : W := mkw 0xa4f8126934adcd9a 0xf6f636e974fd4f93

def z1205 : W := mkw 0xa4f81269348d4d9a 0xf6f736e9749d4f9f

def z1206 : W := mkw 0x0a90470258a18518 0x2fbfcf0ff8e18f1c

def z1207 : W := mkw 0x0f20fddfee040ac0 0x3fffffffff020fe0

def z1208 : W := mkw 0x0420b80d80560ac0 0xfffff91f8fff4ff3

def z1209 : W := mkw 0x0420104924040880 0x3fff3ff9ff9e0ce0

def z1210 : W := mkw 0x0420b80d80560ac0 0x0004f00f80fc0fe0

def z1211 : W := mkw 0x0420b84da4560ac0 0x3f9ff80ff4fe0fe0

def z1212 : W := mkw 0x0f00fddfee000000 0x015cffffff000000

def z1213 : W := mkw 0x0ad0efb258fbe518 0x3efefffe70ffff10

def z1214 : W := mkw 0x4724104fef041ae5 0xe381000fff000fff

def z1215 : W := mkw 0x0f00fddfee000000 0x0004f7fe7b000000

def z1216 : W := mkw 0x0000a80000520000 0x3d9ff80f80fe0fe0

def z1217 : W := mkw 0xa4f81269348d4c92 0xffff3ff9ff9dcc9f

def z1218 : W := mkw 0x0f00fddfee000000 0x02f63ff9ff000000

def z1219 : W := mkw 0x0000a80480520240 0x3d9ff80e80fe0f60

def z1220 : W := mkw 0xe4fcba2d91df5ef7 0xfd9ff80f80ffffff

def z1221 : W := mkw 0x4004000001001025 0xdb7909118f03f0ff

def z1222 : W := mkw 0x08c0efb000fbe000 0x3ffffff188fff0fc

def z1223 : W := mkw 0x0ac0efb248fbe108 0x1ffffffe78fff30c

def z1224 : W := mkw 0x0ad0efb258fbe518 0x2faffffe78ffbf1c

def z1225 : W := mkw 0x0420b80d80560ac0 0x3dfff80f80ff4fe0

def z1226 : W := mkw 0x0f00fddb6e000000 0x02fefff97f000000

def z1227 : W := mkw 0x40c4022001895025 0xf7f736e18f9d40ff

def z1228 : W := mkw 0x0f00fddfee000000 0x23ffffffff0000e0

def z1229 : W := mkw 0x0f00fddfee000000 0x0bffffffff020060

def z1230 : W := mkw 0x0a90470258a18518 0x23a5c70e78e18f1c

def z1231 : W := mkw 0x0f0055dfee000000 0x026007fe7f000000

def z1232 : W := mkw 0x00d0022010894410 0x3fff3ff8789ffc1c

def z1233 : W := mkw 0x0f00fddfee000000 0x026037f07f000000

def z1234 : W := mkw 0xa4f81269348d4c92 0xfef736e974fd4f93

def z1235 : W := mkw 0xa4f81269348d4c92 0xf6fe3ff9749d4c93

def z1236 : W := mkw 0x0ad0efb258fbe518 0x1e7efffe78ffff1c

def z1237 : W := mkw 0x0420b80d80560ac0 0x3195f80f80fe0fe0

def z1238 : W := mkw 0x08c0efb000fbe000 0x1c7efff180fff0e0

def z1239 : W := mkw 0x0f00fddfee000000 0x03aefffefb000000

def z1240 : W := mkw 0xa4f81269348d4c92 0xf6f63ef9749f7c93

def z1241 : W := mkw 0xa4f81269348d4c92 0xf66436e8749d4c93

def z1242 : W := mkw 0x4004000001001025 0xffff3ff18f03f0ff

def z1243 : W := mkw 0x0a40edb2487ae108 0x1959f9f6087ef30c

def z1244 : W := mkw 0x0f00fddfee000000 0x03f6f6efff000000

def z1245 : W := mkw 0x0f00fddfee520240 0x1ffffffffffe0360

def z1246 : W := mkw 0x0f00fddfee000000 0x03e8cfffff000000

def z1247 : W := mkw 0x0a90470258a18518 0x2fefc71e78e1ff1c

def z1248 : W := mkw 0xa4f81269348d4c92 0xf6f63ee9f49f4cf3

def z1249 : W := mkw 0x08c0472000fbe000 0x1c7ef7e000fff000

def z1250 : W := mkw 0x08c047b000a9e000 0x107037f0001df000

def z1251 : W := mkw 0x0840edb0005a6000 0x1058f9f0001e7000

def z1252 : W := mkw 0x0a90470258a18518 0x23afc70e78e00f1c

def z1253 : W := mkw 0x0020a80480560ac0 0x3d8fc80e80fe0fe0

def z1254 : W := mkw 0xa4f81269348d4c92 0xf6f637f9749dfc93

def z1255 : W := mkw 0x0f00fddfee20a000 0x03feffffff00b000

def z1256 : W := mkw 0x00c0022000894000 0x14763ef0009f7000

def z1257 : W := mkw 0x0b0045d26e000000 0x02700ff1ff000000

def z1258 : W := mkw 0x08c0efb480fbe240 0x3dfffffe80ffff60

def z1259 : W := mkw 0xa4f81269348d4c92 0xf7f736e9f49d4cf3

def z1260 : W := mkw 0x0f20fddfee040ac0 0x03feffffff000f00

def z1261 : W := mkw 0x0a90470258a18518 0x2fafc70ff8e18ffc

def z1262 : W := mkw 0xa4f81269348d4c92 0xf6f637e97c9dcc9f

def z1263 : W := mkw 0xe43c104935041cb7 0xe28000097f000c9f

def z1264 : W := mkw 0x0ad047b258a9e518 0x36f637f8789dfc1c

def z1265 : W := mkw 0xa4f81269348d4c92 0xf68436e9749d4c93

def z1266 : W := mkw 0x0020000000560ac0 0x3c05c00e00fe0fe0

def z1267 : W := mkw 0x08c0efb000fbe000 0x1c2ef7e000fff000

def z1268 : W := mkw 0x0b00edd26e72a000 0x0a68cff07f62b000

def z1269 : W := mkw 0x0a90470258a18518 0x2e25c70e78e18f1c

def z1270 : W := mkw 0x0f20fddfee040880 0x3fffffffff9e0ce0

def z1271 : W := mkw 0x0400104924000000 0x02f637f97f000000

def z1272 : W := mkw 0x0b0045d26e000000 0x027a0ff07f000000

def z1273 : W := mkw 0x08c0efb000fbe000 0x1c58f9f000fff000

def z1274 : W := mkw 0x0840edb0007ae000 0x0808f9f0007eb000

def z1275 : W := mkw 0x0420b80d80560ac0 0x3ddff81f87fe0fe0

def z1276 : W := mkw 0x0b00edd6ee000000 0x0108cff6fb000000

def z1277 : W := mkw 0x0f00fddfee520000 0x13feffffff1e0000

def z1278 : W := mkw 0xa0f80220108d4c92 0xf7fa09118f9d4c93

def z1279 : W := mkw 0xa0d8026034894412 0xf6f636e1749d4093

def z1280 : W := mkw 0x00c0aab000db6000 0x1c7efef000ff7000

def z1281 : W := mkw 0x0ad0efb258fbe518 0x3faff7ee78ffff1c

def z1282 : W := mkw 0xa4f81269348d4c92 0xe00436e8709c0c93

def z1283 : W := mkw 0x0f2055dfee040ac0 0x23e107ffff000fe0

def z1284 : W := mkw 0x0040a8b0005a6000 0x1054f8f000fe7000

def z1285 : W := mkw 0x09c0efb482fbe000 0x1c7efff083fff000

def z1286 : W := mkw 0x0a90470258a18518 0xffafc70e78e1cf9f

def z1287 : W := mkw 0x0a90470258a18518 0x2d8fc70e78e08f0c

def z1288 : W := mkw 0xa4e81269248d4882 0xd6f636e9749d4083

def z1289 : W := mkw 0x0420b80d80560ac0 0x1c1ef80f80fe0fe0

def z1290 : W := mkw 0x08c0efb000fbe000 0x1dfefff180fff000

def z1291 : W := mkw 0x0a90470258a18518 0x0105c60e78e00f0c

def z1292 : W := mkw 0xa4f81269348d4c92 0xf6f236e1741d4093

def z1293 : W := mkw 0x00c002b000896000 0x147636f0009d7000

def z1294 : W := mkw 0x0420b80d80560ac0 0x3d9ff80f80ffffe0

def z1295 : W := mkw 0x0f00fddfee208108 0x03feffffff600300

def z1296 : W := mkw 0x0500b8dda6000000 0x03fe3ff9ff000000

def z1297 : W := mkw 0x0a90470258a18518 0x0d2fc70e78e18f0c

def z1298 : W := mkw 0x08c0efb000fbe000 0x087efff000feb000

def z1299 : W := mkw 0x0f00fddfee000000 0x02f6f7ff7f000000

def z1300 : W := mkw 0x0b0045d26e000000 0x02e607f87f000000

def z1301 : W := mkw 0x0a90470258a18518 0x0805c60e70e08f0c

def z1302 : W := mkw 0x0f00fddfee000000 0xffffffffff01c09f

def z1303 : W := mkw 0xeebc574b7da59dbf 0xefafc70fffe18fff

def z1304 : W := mkw 0x0840edb0007ae000 0x1050f8f0007e7000

def z1305 : W := mkw 0x08c0efb480fbe240 0x1c7efff080fff060

def z1306 : W := mkw 0x08c0efb000fbe000 0x086cfff000fff000

def z1307 : W := mkw 0x0d00fddda6000000 0x02fefff9f7000000

def z1308 : W := mkw 0x0f00fddfee000000 0x02f6fefff7000000

def z1309 : W := mkw 0x08c0efb000fbe000 0x1d7ffff600fff300

def z1310 : W := mkw 0x0f20fddfee560ac0 0x1ffefffffffe00e0

def z1311 : W := mkw 0x0f00fddfee000000 0x23ffffffff00001c

def z1312 : W := mkw 0x0420b80d80560ac0 0x2d8ff00f80fc0fe0

def z1313 : W := mkw 0x0a90470258a18518 0x3fffcf1fffe3ff1c

def z1314 : W := mkw 0x0b0045d26e000000 0x026007f07f01f000

def z1315 : W := mkw 0x4004000001001025 0xffff09198f83fcff

def z1316 : W := mkw 0xa8d8efb010fbe412 0xdc7efff000fff013

def z1317 : W := mkw 0x08c0efb000fbe000 0xde7efff004fff013

def z1318 : W := mkw 0xe46cb86da55e5ae7 0xd05038f1871e70e3

def z1319 : W := mkw 0x0f20fddfee560ac0 0x33ffffffff1e0fe0

def z1320 : W := mkw 0x0f00fddfee72a000 0x1ffeffffff63f000

def z1321 : W := mkw 0xe4fc1229118d5cb7 0xfd9f3809809ffcff

def z1322 : W := mkw 0x0ac0efb248fbe000 0x3ffffffe78fff01c

def z1323 : W := mkw 0x00c0aab000fbe000 0x105038f000fe7000

def z1324 : W := mkw 0x08c0efb000fbe000 0x3ffffff18ffff01c

def z1325 : W := mkw 0x08c0efb000fbe000 0x14763ff0009ff000

def z1326 : W := mkw 0xa4f81269348d4c92 0xc04436e8749c4c03

def z1327 : W := mkw 0x0f20fddfee040880 0x03feffffff9c0c00

def z1328 : W := mkw 0xe4bc124935851cb7 0xefaf0709ff818cff

def z1329 : W := mkw 0x00c0aab000db6000 0x10543ef0009e7000

def z1330 : W := mkw 0xa4f81269348d4c92 0xd27436e9749d4c93

def z1331 : W := mkw 0x0420b80d80560ac0 0x3dbff90f80ff8fe0

def z1332 : W := mkw 0xa4f81269348d4c92 0xf7fe37e97c9d4c93

def z1333 : W := mkw 0x08c0efb000fbe000 0x0004fef000fe3000

def z1334 : W := mkw 0x0a90479258a1a518 0x2fafc71e78e1bf1c

def z1335 : W := mkw 0xa4f81269348d4c92 0xd2f636e9749c4c83

def z1336 : W := mkw 0xa4f81269348d4c92 0xfefe37e9749dcc93

def z1337 : W := mkw 0x0420b80d80560ac0 0x3d9ff80f80ff8ffc

def z1338 : W := mkw 0x0520b89d82560ac0 0x3d9ff81f83fe0fe0

def z1339 : W := mkw 0x08c0efb480fbe240 0x3dfffff780fff3e0

def z1340 : W := mkw 0x08c0efb000fbe000 0x1c7efff187fff000

def z1341 : W := mkw 0x0b00edd26e520000 0x1e7efff07ffe0000

def z1342 : W := mkw 0x0a10450258208518 0x2f8fc10e78e08f1c

def z1343 : W := mkw 0x0ad0efb258fbe518 0x2feff7fe78fdff1c

def z1344 : W := mkw 0x08d0efb010fbe518 0x3efffff870ffff1c

def z1345 : W := mkw 0x0840edb0007ae000 0x1c5ef9f000fef000

def z1346 : W := mkw 0x0f00fddfee000000 0x37feffffff000080

def z1347 : W := mkw 0x0f00fddfee000000 0x1ffeffffff020000

def z1348 : W := mkw 0x4004000001001025 0xfffbc9178f63f3ff

def z1349 : W := mkw 0x0420100900040880 0x3d9ff80f80fe0fe0

def z1350 : W := mkw 0x08c0efb000fbe000 0x3cfefff100fff080

def z1351 : W := mkw 0x4004000001001025 0xf6f209118f03f0ff

def z1352 : W := mkw 0x0ac0efb248fbe000 0x1ffefffffffff000

def z1353 : W := mkw 0x0ad0472258a9c518 0x3fafc70e78fdcf1c

def z1354 : W := mkw 0x0040a8b0005a6000 0x105ef8f0001e7000

def z1355 : W := mkw 0x08c0efb000fbe000 0x1c7a3ff0001ff000

def z1356 : W := mkw 0x0420b80d80560ac0 0x3f9ff80f8ffe0fe0

def z1357 : W := mkw 0x0f00fddfee000000 0x0274ffffff000000

def z1358 : W := mkw 0x08c0efb000fbe000 0x1d7efff08bfff000

def z1359 : W := mkw 0x0f20fddfee560ac0 0x3f9ffeeffffe0fe0

def z1360 : W := mkw 0x0a90470258a18518 0xefefc70e7ce1cf1f

def z1361 : W := mkw 0x0420100d80560ac0 0x3d8fc00f80fe0fe0

def z1362 : W := mkw 0x4004000001001025 0xf3f109118f03f0ff

def z1363 : W := mkw 0x0000004024000000 0x03fa0ff1ff000000

def z1364 : W := mkw 0x0420b84da4560ac0 0x3d9ffeeff0fe0fe0

def z1365 : W := mkw 0xa4f81269348d4c92 0xf7f736ef749d4f93

def z1366 : W := mkw 0x0f00fddfee000108 0x03ffffffff00030c

def z1367 : W := mkw 0x08c0efb000fbe000 0x1c54fef000fff000

def z1368 : W := mkw 0x0a90470258a18518 0x2f85c60e78e18f1c

def z1369 : W := mkw 0x0bc0efb6cafbe000 0x1ffefff78ffff000

def z1370 : W := mkw 0x4004000001001025 0xd3fa09118f03f0ff

def z1371 : W := mkw 0x0040a8b0005a6000 0xd05038f1041e7083

def z1372 : W := mkw 0x0f00fddfee000000 0x027efffe7f000000

def z1373 : W := mkw 0x0b40edb6ca5a6000 0x1158f9f68b1e7000

def z1374 : W := mkw 0xa4f81269348d4c92 0xd67636e8749d4c13

def z1375 : W := mkw 0x0b0045d26e208108 0x0b69c7f67f60830c

def z1376 : W := mkw 0x08d0efb010fbe410 0x3ffffff878fffc1c

def z1377 : W := mkw 0x0ad0efb258fbe518 0x1f7ffff678fff31c

def z1378 : W := mkw 0x0f20fddfee560ac0 0x3fffffffff1e00e0

def z1379 : W := mkw 0x0040a8b0005a6000 0x1c7ef9f000fff000

def z1380 : W := mkw 0xa4f81269348d4c92 0xffff3ff9f49ffcf3

def z1381 : W := mkw 0x0a90470258a18518 0x3fffcf1ff8e3fffc

def z1382 : W := mkw 0x0f00fddfee520240 0x03feffffff020060

def z1383 : W := mkw 0x00400020005a6000 0x105030e0001e7000

def z1384 : W := mkw 0x0ad0efb258fbe518 0x3dfffffe70ffff00

def z1385 : W := mkw 0xe42c1049250418a7 0xe38100018f0000ff

def z1386 : W := mkw 0xa4681069240c4882 0xd05436e9741c4083

def z1387 : W := mkw 0x0ad0efb258fbe518 0x3fffffffffffff1c

def z1388 : W := mkw 0xe0fc0220118d5cb7 0xf4000000009dfc9f

def z1389 : W := mkw 0x0a90470258a18518 0x2f8fc60e78e00f1c

def z1390 : W := mkw 0x08d0efb010fbe410 0x1c7efff870fffc00

def z1391 : W := mkw 0x0f0055db6e000000 0x027037f17f000000

def z1392 : W := mkw 0xa4f81269348d4c92 0xffff3fe9fc9fccff

def z1393 : W := mkw 0x08d0efb010fbe410 0x3c7efff000fffc10

def z1394 : W := mkw 0x0f00fddfee208108 0x03feffffff00800c

def z1395 : W := mkw 0x0f20fddfee560ac0 0x2bffffffff620fe0

def z1396 : W := mkw 0x08c047b000a9e000 0x1c7e3ff0009ff000

def z1397 : W := mkw 0x08c0efb000fbe000 0xfffefff18ffff093

def z1398 : W := mkw 0x08c0efb000fbe000 0x0804f6e000feb000

def z1399 : W := mkw 0x0ad0472258a9c518 0x2faff7ee78fd8f1c

def z1400 : W := mkw 0xa4f81269348d4c92 0xfefe3ee9749f4c93

def z1401 : W := mkw 0x0f00fddfee000000 0x0204f6ee7f000000

def z1402 : W := mkw 0x0420b80d80560ac0 0x0004f80e80fe0f60

def z1403 : W := mkw 0x0f0055dfee000000 0x03fa0fffff000000

def z1404 : W := mkw 0x0f00fddfee000000 0x027efff1ff000000

def z1405 : W := mkw 0x00c0022000fbe000 0x1c7e3ff000fff000

def z1406 : W := mkw 0x0ad0efb258fbe518 0x1c7efff070fff000

def z1407 : W := mkw 0x0ad0efb258fbe518 0x090dfffe78febf0c

def z1408 : W := mkw 0x0f00fddfee000000 0xfffeffffff03f093

def z1409 : W := mkw 0xa4f81269348d4c92 0xf2d436e9749c4c93

def z1410 : W := mkw 0x00c0aab000fbe000 0x1c7a39f000fff000

def z1411 : W := mkw 0x0ad0efb258fbe518 0x1ffefffe78fff01c

def z1412 : W := mkw 0x0f00fddfee000000 0x038cffffff000000

def z1413 : W := mkw 0x08d0efb010fbe518 0x3ffffff008ffff1c

def z1414 : W := mkw 0x00c0aab000db6000 0x1c7e3ff0009ff000

def z1415 : W := mkw 0x0420b80d80560ac0 0x2d8ff80e80fe0f60

def z1416 : W := mkw 0x0420b84da4560ac0 0xfffffeeff4ff4ff3

def z1417 : W := mkw 0xa4f81269348d4c92 0xe2e436e9749d4c93

def z1418 : W := mkw 0x0f00fddfee000240 0x03ffffffff000360

def z1419 : W := mkw 0x0000004024000000 0x026007f07f000000

def z1420 : W := mkw 0xa4f81269348d4c92 0xfef636e9749ffc93

def z1421 : W := mkw 0x0040a8b0005a6000 0x3ddff8fe00fe7f00

def z1422 : W := mkw 0x0a90470258a18518 0x2005c60e70e00f1c

def z1423 : W := mkw 0x08c0efb000fbe000 0x1c5efef000fe7000

def z1424 : W := mkw 0x08d0efb010fbe410 0xfefefff974fffc93

def z1425 : W := mkw 0x0f20fddfee560ac0 0x37feffffff9e0ce0

def z1426 : W := mkw 0x08c0efb000a9e000 0x147efff0009df000

def z1427 : W := mkw 0x0a90470258a18518 0x2c2fc70e70e18f1c

def z1428 : W := mkw 0x08d0efb010fbe518 0x1c7efff000ffff00

def z1429 : W := mkw 0x08c0efb000fbe000 0x1d7ffff080fff060

def z1430 : W := mkw 0x0420b80d80560ac0 0x3d9ff90f88fe8fec

def z1431 : W := mkw 0x0f20fddfee560ac0 0x03feffffff1c0000

def z1432 : W := mkw 0x0a40edb2485a6000 0x13fefffe781e7000

def z1433 : W := mkw 0x0a90470258a18518 0xefafc70f7ce18f9f

def z1434 : W := mkw 0x0840edb0005a6000 0x1054fef0001e7000

def z1435 : W := mkw 0x08c0efb000fbe000 0x1074fff000fff000

def z1436 : W := mkw 0x08c0efb000fbe000 0x1c1efff000feb000

def z1437 : W := mkw 0x0f00fddfee520240 0x2fffffffffe20f60

def z1438 : W := mkw 0x08c0efb000fbe000 0x1efefff870fff000

def z1439 : W := mkw 0x0b0045d26e000000 0x0264c7fe7f000000

def z1440 : W := mkw 0x0b00edd26e000000 0x0264f7f07f000000

def z1441 : W := mkw 0x08c0efb000fbe000 0x3efefff000fff010

def z1442 : W := mkw 0x08c0efb000fbe000 0x1c0cfff000fff000

def z1443 : W := mkw 0xa4f8126934adcd9a 0xffff37e97cfdcf9f

def z1444 : W := mkw 0x0f0055dfee000000 0x038006efff000000

def z1445 : W := mkw 0xa4f8126934adcc92 0xfef636e974fdcc93

def z1446 : W := mkw 0x0040a8b0005a6000 0x145638f0009e7000

def z1447 : W := mkw 0x0700104fee000000 0x03fe3fffff000000

def z1448 : W := mkw 0xa4f81269348d4c92 0xfef736e9749dcc9f

def z1449 : W := mkw 0x0f00fddfee208108 0x2fffffffffe08f0c

def z1450 : W := mkw 0x4b04ed96cb72b025 0x0909c9168b62b06c

def z1451 : W := mkw 0x0f00fddfee000000 0x03f03fffff000000

def z1452 : W := mkw 0xe43c104935041cb7 0xe281000974000cff

def z1453 : W := mkw 0x0b00edd6ee000000 0x03facff7ff000000

def z1454 : W := mkw 0x0420b80d80560ac0 0xff9ff80f84fe0ff3

def z1455 : W := mkw 0x0420b80d80560ac0 0x3496f80f80fe0fe0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z8,z5,z6])],[(1,[z9,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z8,z5,z6,z10]),(0,[z11,z1,z2,z3,z8,z5,z12]),(0,[z1,z2,z13,z3,z8,z5,z6])],[(1,[z14,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z15,z5,z16,z6])],[(0,[z1,z2,z3,z8,z5,z17,z6]),(0,[z0,z1,z3,z18,z8,z5,z6]),(1,[z19,z1,z2,z8,z20,z6])],[(1,[z1,z2,z3,z21,z5,z6]),(0,[z22,z1,z3,z23,z8,z5,z6]),(0,[z24,z1,z2,z3,z8,z5,z6]),(0,[z1,z25,z2,z3,z8,z5,z26]),(0,[z1,z2,z3,z8,z5,z27,z6])],[(0,[z28,z1,z2,z3,z15,z5,z6]),(0,[z29,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z30,z8,z5,z6]),(0,[z1,z31,z2,z8,z32,z5,z6]),(0,[z1,z33,z2,z3,z8,z5,z6])],[(0,[z0,z1,z3,z23,z8,z5,z6]),(1,[z34,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z15,z8,z5,z6]),(0,[z34,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z35]),(0,[z11,z36,z2,z3,z8,z5,z6])],[(0,[z1,z2,z37,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z38]),(0,[z39,z1,z2,z3,z8,z5,z40]),(0,[z1,z2,z3,z4,z5,z41,z6]),(0,[z1,z2,z3,z8,z5,z42,z6]),(0,[z1,z2,z43,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z44,z6]),(0,[z1,z45,z2,z3,z8,z5,z6])]],
   [[(0,[z46,z1,z2,z3,z47,z5,z6]),(1,[z1,z2,z3,z48,z5,z6]),(0,[z49,z1,z3,z50,z8,z5,z6]),(0,[z1,z2,z51,z3,z8,z5,z6]),(0,[z52,z1,z2,z3,z8,z5,z6]),(0,[z53,z1,z3,z50,z8,z5,z6]),(0,[z54,z0,z1,z3,z8,z5,z6]),(0,[z55,z1,z2,z3,z8,z5,z6]),(1,[z1,z56,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z57,z16,z6])],[(0,[z58,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z59,z5,z6]),(0,[z1,z2,z3,z15,z5,z6,z10]),(0,[z1,z2,z60,z3,z15,z5,z6]),(0,[z1,z2,z3,z8,z5,z16,z10]),(0,[z1,z31,z2,z3,z8,z5,z6]),(0,[z61,z1,z2,z3,z8,z5,z6]),(0,[z11,z1,z62,z3,z8,z5,z6])],[(0,[z1,z1,z2,z3,z8,z5,z6]),(0,[z39,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z63,z8,z5,z6]),(0,[z64,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z65,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z66]),(0,[z1,z2,z3,z8,z5,z67,z6])],[(0,[z68,z1,z2,z3,z4,z5,z6]),(0,[z69,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z70,z71]),(0,[z1,z2,z72,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z73,z5,z6]),(0,[z74,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z15,z5,z75,z6]),(0,[z1,z2,z3,z8,z5,z76,z6]),(0,[z1,z2,z77,z3,z8,z5,z6])],[(0,[z78,z2,z79,z3,z8,z5,z6]),(0,[z80,z1,z2,z3,z15,z5,z6]),(1,[z1,z81,z50,z8,z5,z6]),(0,[z82,z0,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z83])],[(0,[z46,z0,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z84,z6]),(0,[z85,z1,z2,z3,z8,z5,z6]),(1,[z2,z3,z4,z5,z6,z10]),(0,[z1,z2,z3,z4,z5,z70,z6])],[(0,[z86,z1,z2,z3,z8,z5,z6]),(0,[z87,z1,z3,z50,z8,z5,z6]),(0,[z22,z1,z2,z88,z8,z5,z6]),(0,[z1,z2,z3,z8,z89,z5,z6]),(0,[z1,z2,z3,z8,z5,z12,z6])]],
   [[(0,[z39,z1,z2,z3,z8,z5,z90]),(1,[z1,z3,z50,z8,z5,z6]),(0,[z91,z1,z2,z3,z8,z5,z6]),(0,[z92,z1,z2,z3,z8,z5,z6])],[(0,[z93,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z94,z6]),(0,[z1,z2,z3,z8,z5,z10,z71]),(0,[z1,z95,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z96,z5,z6]),(0,[z97,z1,z2,z3,z8,z5,z6]),(0,[z98,z1,z2,z3,z8,z5,z6])],[(0,[z1,z99,z2,z3,z8,z5,z6]),(0,[z100,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z101,z6]),(0,[z1,z2,z3,z8,z5,z6,z102]),(0,[z1,z2,z3,z8,z5,z103,z6]),(0,[z1,z2,z3,z8,z5,z6,z104]),(0,[z105,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z59,z5,z6]),(0,[z1,z2,z3,z106,z15,z5,z6]),(0,[z0,z1,z3,z8,z5,z107,z6]),(1,[z1,z2,z108,z8,z5,z6]),(0,[z109,z1,z60,z3,z8,z5,z6]),(1,[z110,z2,z3,z8,z5,z6]),(0,[z80,z1,z31,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z111,z6])],[(1,[z1,z2,z3,z8,z5,z112]),(0,[z39,z1,z2,z79,z8,z5,z6]),(0,[z1,z2,z3,z15,z63,z5,z6]),(0,[z68,z1,z2,z3,z8,z5,z113]),(0,[z0,z114,z1,z3,z8,z5,z6]),(0,[z0,z1,z3,z8,z5,z20,z6]),(0,[z1,z2,z115,z3,z8,z5,z107]),(0,[z1,z2,z3,z8,z5,z116,z6]),(0,[z1,z2,z62,z3,z8,z5,z6]),(0,[z117,z1,z2,z3,z8,z5,z6])],[(0,[z118,z0,z1,z3,z8,z5,z6]),(1,[z0,z119,z1,z8,z5,z6]),(0,[z120,z1,z2,z3,z8,z5,z6])],[(0,[z19,z1,z2,z3,z15,z5,z6]),(1,[z1,z2,z3,z121,z5,z6]),(1,[z0,z1,z50,z8,z5,z6]),(0,[z1,z3,z50,z8,z5,z75,z6]),(0,[z0,z1,z3,z8,z5,z122,z6]),(0,[z123,z1,z2,z60,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z124,z6])],[(0,[z1,z2,z3,z125,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z126,z6]),(0,[z1,z3,z50,z8,z5,z6,z127]),(0,[z128,z1,z2,z3,z8,z5,z107])]],
   [[(0,[z28,z1,z2,z3,z8,z5,z6]),(0,[z129,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z130,z3,z15,z5,z6]),(0,[z1,z2,z3,z131,z8,z5,z6]),(0,[z1,z115,z3,z50,z8,z5,z6]),(0,[z1,z132,z3,z50,z8,z5,z6]),(0,[z1,z2,z60,z8,z32,z5,z6]),(0,[z133,z1,z2,z3,z8,z5,z6]),(0,[z134,z1,z81,z3,z8,z5,z6])],[(0,[z22,z1,z2,z3,z15,z5,z6]),(0,[z0,z1,z3,z8,z135,z5,z6])],[(0,[z1,z2,z3,z136,z8,z5,z6]),(0,[z1,z2,z81,z3,z8,z137,z6]),(0,[z128,z1,z138,z3,z8,z5,z6]),(0,[z80,z1,z2,z3,z139,z5,z6])],[(1,[z39,z2,z63,z8,z5,z6]),(0,[z34,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z15,z5,z107,z6]),(0,[z68,z1,z2,z65,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z140]),(0,[z1,z2,z141,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z142])],[(0,[z1,z2,z3,z8,z5,z6,z143]),(0,[z1,z144,z2,z3,z8,z5,z6]),(0,[z145,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z60,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z146,z6]),(0,[z1,z2,z3,z147,z8,z5,z6])],[(0,[z0,z1,z3,z8,z5,z148,z6]),(0,[z1,z149,z2,z3,z5,z150,z6]),(0,[z1,z2,z151,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z152,z6]),(1,[z128,z1,z2,z8,z5,z153]),(0,[z11,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z154])],[(0,[z155,z1,z2,z3,z8,z5,z6]),(1,[z0,z1,z3,z15,z5,z6]),(0,[z1,z2,z3,z15,z5,z122,z6]),(0,[z1,z2,z3,z8,z5,z156,z6]),(0,[z0,z119,z1,z3,z8,z5,z6]),(0,[z1,z25,z132,z3,z8,z5,z6])],[(0,[z39,z1,z2,z3,z4,z5,z6]),(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z157,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z158,z5,z6]),(0,[z109,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z159]),(0,[z160,z1,z2,z3,z8,z5,z71])]],
   [[(0,[z161,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z162,z6]),(0,[z163,z1,z2,z3,z8,z5,z6]),(1,[z1,z164,z2,z3,z5,z6]),(0,[z80,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z165,z5,z6]),(0,[z1,z2,z3,z8,z166,z5,z6]),(0,[z34,z1,z167,z3,z8,z5,z6]),(1,[z168,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z4,z5,z169,z6]),(0,[z1,z2,z3,z8,z170,z5,z6]),(0,[z1,z2,z3,z8,z16,z6,z71]),(0,[z1,z2,z3,z8,z5,z6,z171])],[(0,[z39,z1,z2,z3,z8,z172,z6]),(0,[z1,z2,z3,z8,z5,z173,z6]),(0,[z1,z2,z3,z174,z8,z5,z6]),(1,[z109,z1,z3,z8,z5,z6]),(0,[z11,z1,z2,z3,z8,z75,z6]),(0,[z1,z2,z3,z8,z5,z6,z175])],[(0,[z1,z3,z50,z8,z57,z5,z6]),(0,[z1,z2,z3,z8,z5,z176,z6]),(1,[z1,z177,z3,z8,z5,z6]),(0,[z1,z2,z81,z8,z137,z5,z6]),(0,[z1,z2,z3,z8,z5,z178,z6])],[(0,[z179,z1,z2,z3,z15,z5,z6]),(0,[z68,z1,z180,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z181,z6]),(0,[z1,z3,z8,z5,z122,z6,z26])],[(0,[z182,z1,z2,z3,z8,z5,z6]),(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z78,z2,z3,z8,z5,z41,z6]),(0,[z183,z1,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z106,z8,z5,z6]),(0,[z1,z3,z50,z8,z5,z6,z153]),(0,[z184,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z185,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z186,z5,z6]),(0,[z1,z2,z3,z8,z5,z187,z6])],[(0,[z1,z99,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z75,z6]),(0,[z1,z2,z3,z8,z5,z70,z107]),(0,[z1,z2,z3,z8,z5,z188,z6]),(0,[z1,z2,z3,z8,z137,z5,z6]),(0,[z1,z2,z8,z5,z20,z6,z153])]],
   [[(0,[z1,z2,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z127]),(0,[z119,z1,z95,z2,z8,z5,z6]),(0,[z189,z1,z3,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z190,z5,z6]),(0,[z1,z2,z3,z191,z5,z150,z6]),(0,[z1,z2,z3,z8,z5,z6,z192]),(1,[z1,z3,z193,z8,z5,z6]),(0,[z92,z1,z3,z18,z8,z5,z6])],[(0,[z1,z194,z3,z50,z8,z5,z6]),(0,[z195,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z6]),(1,[z196,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z197,z5,z6]),(0,[z1,z31,z2,z60,z3,z5,z6]),(0,[z19,z1,z2,z3,z8,z5,z6])],[(0,[z0,z1,z3,z8,z5,z198,z6]),(0,[z1,z199,z2,z3,z8,z5,z6]),(0,[z200,z1,z2,z3,z8,z5,z6])],[(0,[z201,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z202,z8,z5,z6])],[(0,[z93,z1,z3,z23,z8,z5,z6]),(0,[z93,z1,z2,z3,z8,z5,z203]),(1,[z1,z204,z3,z8,z5,z6]),(0,[z9,z2,z3,z8,z4,z5,z6]),(0,[z53,z205,z2,z3,z8,z5,z6]),(0,[z123,z1,z31,z2,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z206,z6]),(0,[z68,z1,z2,z3,z207,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z208]),(0,[z128,z1,z209,z3,z8,z5,z6]),(1,[z1,z2,z3,z18,z5,z150]),(0,[z1,z2,z3,z5,z6,z210,z71])],[(0,[z1,z2,z3,z15,z211,z5,z6]),(0,[z80,z1,z2,z3,z191,z5,z6]),(0,[z1,z25,z2,z3,z212,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z90]),(0,[z1,z2,z3,z8,z213,z5,z6]),(0,[z1,z2,z214,z3,z8,z5,z6]),(0,[z215,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z15,z15,z5,z6]),(0,[z1,z216,z2,z3,z15,z5,z6]),(0,[z1,z2,z50,z8,z5,z6,z153]),(0,[z217,z0,z1,z3,z8,z5,z6]),(0,[z0,z1,z3,z8,z218,z5,z6]),(0,[z19,z1,z2,z81,z8,z5,z6]),(1,[z1,z2,z3,z219,z5,z6])],[(0,[z1,z220,z2,z3,z8,z5,z6]),(0,[z1,z2,z79,z8,z5,z20,z6]),(0,[z1,z2,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z221]),(1,[z1,z95,z50,z8,z5,z6]),(0,[z1,z2,z115,z3,z8,z5,z153]),(0,[z1,z222,z2,z3,z8,z5,z6])],[(0,[z223,z1,z2,z3,z8,z5,z6]),(0,[z39,z1,z2,z3,z224,z5,z6]),(0,[z1,z2,z3,z15,z5,z198,z6]),(0,[z1,z2,z3,z8,z5,z225,z6]),(1,[z134,z1,z3,z8,z5,z6]),(0,[z1,z226,z2,z3,z8,z5,z6])],[(0,[z2,z3,z8,z4,z5,z6,z10]),(1,[z1,z2,z3,z8,z5,z227]),(0,[z68,z0,z1,z3,z8,z5,z6]),(0,[z1,z149,z3,z8,z191,z5,z6]),(0,[z1,z2,z3,z8,z5,z228,z6]),(1,[z1,z2,z229,z8,z5,z6]),(0,[z230,z1,z2,z3,z8,z5,z6])],[(0,[z179,z1,z3,z8,z5,z198,z6]),(0,[z128,z1,z2,z3,z8,z5,z153])],[(0,[z1,z231,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z57,z5,z6]),(0,[z80,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z15,z137,z5,z6]),(0,[z0,z1,z3,z8,z139,z5,z6]),(0,[z1,z132,z3,z8,z232,z5,z6]),(1,[z1,z2,z3,z233,z5,z6]),(0,[z1,z2,z229,z3,z8,z5,z6]),(0,[z160,z1,z2,z3,z219,z5,z6])],[(0,[z39,z78,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z234,z8,z5,z6]),(0,[z160,z0,z1,z3,z8,z5,z6]),(0,[z1,z149,z216,z2,z3,z5,z6]),(0,[z235,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z139,z5,z150,z6])],[(0,[z1,z2,z3,z4,z5,z6,z153]),(0,[z118,z1,z3,z50,z8,z5,z6]),(0,[z236,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z237]),(0,[z1,z2,z8,z32,z5,z20,z6]),(0,[z1,z2,z3,z8,z5,z16,z6])]],
   [[(0,[z46,z1,z194,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z238]),(0,[z1,z2,z3,z8,z5,z239,z6]),(0,[z9,z2,z3,z8,z135,z5,z6]),(0,[z179,z1,z2,z3,z8,z5,z6])],[(0,[z183,z1,z2,z3,z8,z5,z6]),(0,[z240,z1,z2,z3,z8,z5,z6]),(0,[z1,z31,z2,z3,z15,z5,z6]),(0,[z1,z95,z2,z50,z8,z5,z6]),(0,[z0,z179,z1,z3,z8,z5,z6]),(0,[z0,z1,z3,z8,z5,z6,z26]),(0,[z241,z1,z2,z3,z8,z5,z6]),(1,[z1,z138,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z242])],[(0,[z243,z1,z2,z3,z8,z5,z6]),(0,[z64,z1,z2,z3,z15,z5,z6]),(0,[z244,z1,z2,z3,z8,z5,z6]),(0,[z245,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z246,z6]),(0,[z1,z247,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z248,z8,z5,z6]),(0,[z1,z2,z3,z8,z249,z5,z6]),(0,[z114,z1,z3,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z250])],[(0,[z1,z2,z3,z251,z8,z5,z6]),(0,[z1,z252,z2,z3,z8,z5,z6]),(0,[z53,z1,z2,z3,z253,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z254]),(0,[z255,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z256]),(0,[z1,z2,z3,z8,z5,z6,z257])],[(0,[z1,z2,z3,z8,z5,z258,z6]),(0,[z259,z1,z2,z3,z8,z5,z6]),(0,[z260,z1,z2,z3,z8,z5,z6])],[(1,[z2,z79,z3,z4,z5,z6]),(0,[z19,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z10]),(0,[z1,z2,z115,z8,z5,z20,z6]),(0,[z1,z138,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z261,z6]),(0,[z262,z1,z2,z3,z8,z5,z6])],[(0,[z263,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z264,z5,z6]),(0,[z1,z3,z50,z8,z137,z5,z6]),(0,[z19,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z5,z265,z6])]],
   [[(0,[z266,z1,z2,z3,z8,z5,z6]),(1,[z1,z3,z50,z15,z5,z6]),(0,[z1,z3,z50,z8,z190,z5,z6]),(0,[z0,z1,z3,z8,z5,z150,z6]),(0,[z53,z22,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z267,z6]),(0,[z1,z2,z3,z18,z8,z5,z6])],[(0,[z22,z1,z2,z3,z4,z5,z6]),(0,[z268,z1,z2,z3,z8,z5,z6]),(0,[z1,z95,z2,z3,z15,z5,z6]),(0,[z34,z9,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z269,z5,z6]),(0,[z270,z1,z2,z3,z8,z5,z6]),(0,[z271,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z272]),(1,[z133,z2,z3,z8,z5,z6]),(0,[z160,z1,z2,z273,z8,z5,z6])],[(0,[z1,z2,z3,z23,z8,z5,z6]),(0,[z1,z2,z3,z15,z8,z5,z6]),(0,[z274,z1,z2,z3,z8,z5,z6]),(0,[z1,z216,z2,z3,z8,z5,z6]),(0,[z275,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z276,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z277,z6])],[(0,[z278,z1,z2,z3,z8,z5,z6]),(0,[z279,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z15,z23,z5,z6]),(0,[z280,z1,z2,z3,z8,z5,z6]),(0,[z0,z1,z79,z3,z8,z5,z6]),(0,[z1,z281,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z18,z5,z150,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z282]),(0,[z9,z1,z2,z3,z8,z135,z6]),(0,[z119,z1,z2,z115,z8,z5,z6]),(0,[z179,z1,z2,z3,z191,z5,z6]),(0,[z80,z1,z2,z3,z32,z5,z6]),(0,[z160,z1,z2,z3,z8,z5,z16])],[(0,[z123,z1,z2,z3,z15,z5,z6]),(1,[z68,z2,z3,z8,z41,z6]),(0,[z0,z1,z31,z3,z8,z5,z6]),(0,[z1,z2,z3,z283,z8,z5,z6]),(0,[z284,z1,z2,z3,z8,z5,z6]),(0,[z285,z1,z2,z3,z8,z5,z6]),(0,[z123,z1,z286,z3,z8,z5,z6])]],
   [[(1,[z49,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z287,z5,z6])],[(0,[z1,z2,z3,z8,z288,z5,z6]),(0,[z1,z2,z3,z15,z249,z5,z6]),(0,[z0,z1,z3,z8,z191,z5,z6]),(0,[z1,z2,z3,z289,z8,z5,z6])],[(0,[z1,z2,z81,z63,z8,z5,z6]),(0,[z1,z2,z3,z4,z165,z5,z6]),(1,[z183,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z8,z5,z10,z153]),(0,[z1,z2,z3,z290,z8,z5,z6]),(0,[z1,z2,z3,z8,z291,z5,z6])],[(0,[z292,z1,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z15,z5,z293,z6]),(0,[z294,z1,z2,z3,z8,z5,z6]),(0,[z9,z1,z3,z50,z8,z5,z6]),(0,[z34,z1,z2,z3,z295,z5,z6])],[(0,[z93,z9,z2,z3,z8,z5,z6]),(1,[z1,z296,z3,z8,z5,z6]),(0,[z9,z1,z2,z3,z8,z41,z6]),(1,[z1,z209,z3,z8,z5,z6]),(0,[z80,z1,z2,z3,z8,z5,z150]),(0,[z1,z2,z3,z8,z5,z6,z297])],[(0,[z39,z2,z3,z63,z8,z5,z6]),(0,[z1,z298,z2,z3,z8,z5,z6]),(0,[z179,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z15,z5,z6]),(0,[z123,z1,z31,z2,z3,z5,z6])],[(0,[z1,z132,z3,z23,z8,z5,z6]),(0,[z183,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z299,z5,z6])],[(0,[z1,z3,z50,z8,z5,z16,z6]),(0,[z1,z149,z2,z3,z300,z5,z6]),(0,[z128,z1,z2,z3,z8,z5,z6]),(0,[z301,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z137,z5,z6]),(0,[z0,z1,z3,z8,z4,z5,z6]),(0,[z302,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z303,z6]),(0,[z1,z2,z3,z8,z5,z107,z6]),(0,[z304,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z150,z16]),(0,[z160,z1,z56,z3,z8,z5,z6]),(0,[z160,z1,z2,z3,z8,z6,z71])],[(0,[z1,z3,z23,z8,z5,z198,z6]),(0,[z1,z2,z3,z8,z305,z5,z6]),(0,[z1,z2,z3,z8,z306,z5,z6]),(0,[z53,z1,z2,z3,z8,z232,z6]),(0,[z1,z2,z3,z8,z307,z5,z6]),(0,[z1,z31,z2,z3,z5,z150,z6]),(0,[z1,z2,z3,z8,z5,z20,z6]),(0,[z1,z2,z308,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z309,z6])],[(0,[z1,z2,z3,z310,z8,z5,z6]),(0,[z78,z1,z2,z3,z8,z5,z6]),(0,[z0,z78,z1,z3,z8,z5,z6]),(0,[z0,z1,z115,z3,z8,z5,z6]),(0,[z0,z1,z132,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z12])],[(0,[z1,z2,z3,z8,z311,z5,z6]),(0,[z49,z1,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z4,z232,z5,z6]),(0,[z53,z1,z2,z3,z15,z5,z6]),(0,[z1,z3,z8,z191,z5,z122,z6]),(0,[z312,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z122,z6]),(0,[z123,z1,z2,z3,z8,z5,z313])],[(0,[z1,z2,z3,z8,z5,z172,z6]),(0,[z1,z2,z3,z8,z5,z314,z6]),(0,[z1,z3,z315,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z316]),(0,[z1,z56,z2,z3,z8,z5,z6]),(0,[z317,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z48,z8,z5,z6]),(0,[z1,z2,z3,z18,z4,z5,z6]),(0,[z68,z1,z3,z50,z8,z5,z6]),(0,[z0,z1,z3,z8,z5,z6,z71]),(0,[z1,z2,z3,z8,z5,z318,z6])],[(0,[z1,z2,z3,z319,z8,z5,z6]),(0,[z1,z2,z3,z8,z135,z5,z6]),(0,[z1,z3,z50,z8,z5,z6,z10])],[(0,[z1,z2,z3,z320,z8,z5,z6]),(1,[z36,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z23,z4,z5,z6]),(0,[z1,z2,z3,z15,z4,z5,z6]),(0,[z1,z216,z2,z3,z4,z5,z6]),(0,[z1,z3,z50,z18,z8,z5,z6]),(0,[z160,z1,z3,z50,z8,z5,z6])],[(0,[z1,z25,z3,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z321,z5,z6]),(0,[z1,z2,z3,z322,z8,z5,z6]),(1,[z160,z1,z2,z3,z8,z71])],[(0,[z323,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z148,z6]),(0,[z123,z1,z2,z3,z8,z5,z6]),(0,[z133,z31,z2,z3,z8,z5,z6]),(0,[z324,z1,z2,z3,z8,z5,z6]),(1,[z1,z62,z3,z8,z5,z6])],[(0,[z1,z3,z50,z23,z8,z5,z6]),(0,[z1,z3,z50,z15,z8,z5,z6]),(0,[z1,z149,z2,z3,z5,z75,z6]),(0,[z325,z1,z2,z3,z8,z5,z6])],[(0,[z2,z3,z8,z5,z70,z6,z10]),(0,[z0,z1,z3,z8,z5,z6,z326]),(0,[z1,z2,z3,z8,z327,z5,z6]),(0,[z1,z2,z3,z5,z150,z6,z127])],[(0,[z1,z2,z3,z121,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z328,z6]),(1,[z1,z25,z3,z8,z5,z198]),(0,[z1,z25,z2,z3,z8,z5,z198]),(1,[z1,z3,z329,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z330]),(0,[z1,z2,z3,z331,z8,z5,z6]),(0,[z1,z332,z2,z3,z8,z5,z6])],[(0,[z292,z1,z2,z3,z8,z5,z6]),(0,[z0,z1,z3,z8,z5,z41,z6]),(0,[z1,z2,z3,z295,z8,z5,z6]),(0,[z1,z333,z2,z3,z8,z5,z6]),(0,[z134,z1,z2,z3,z8,z5,z6]),(0,[z334,z1,z2,z3,z8,z5,z6])],[(0,[z335,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z15,z5,z20,z6]),(0,[z9,z1,z2,z3,z320,z5,z6]),(0,[z1,z2,z3,z8,z336,z5,z6]),(0,[z1,z2,z3,z8,z337,z5,z6]),(0,[z338,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z186,z5,z6])]],
   [[(0,[z1,z2,z339,z3,z8,z5,z6]),(0,[z2,z79,z3,z63,z8,z5,z6]),(0,[z1,z2,z51,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z16,z6]),(0,[z1,z2,z3,z8,z5,z340,z6]),(1,[z1,z341,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z342,z6]),(1,[z1,z2,z3,z125,z5,z6]),(0,[z1,z2,z3,z343,z8,z5,z6]),(0,[z1,z31,z2,z3,z4,z5,z6]),(0,[z0,z9,z1,z3,z8,z5,z6]),(0,[z0,z1,z3,z8,z32,z5,z6]),(0,[z1,z132,z2,z3,z8,z232,z6]),(0,[z123,z1,z2,z81,z8,z5,z6]),(0,[z19,z1,z2,z3,z8,z137,z6])],[(0,[z1,z2,z3,z63,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z344,z6]),(0,[z0,z1,z3,z345,z8,z5,z6]),(0,[z0,z1,z81,z3,z8,z5,z6]),(0,[z53,z1,z3,z8,z5,z198,z6])],[(0,[z1,z2,z3,z8,z5,z346,z6]),(0,[z1,z132,z2,z3,z15,z5,z6]),(0,[z1,z2,z347,z3,z8,z5,z6]),(0,[z0,z123,z1,z3,z8,z5,z6]),(0,[z0,z1,z3,z300,z8,z5,z6]),(0,[z179,z1,z3,z8,z5,z122,z6]),(0,[z53,z1,z2,z348,z8,z5,z6]),(1,[z1,z151,z3,z8,z5,z6]),(0,[z1,z2,z3,z300,z8,z75,z6])],[(0,[z1,z2,z3,z8,z349,z5,z6]),(0,[z1,z2,z3,z15,z135,z5,z6]),(0,[z1,z2,z3,z207,z8,z5,z6]),(1,[z1,z2,z3,z350,z5,z6]),(0,[z160,z1,z2,z3,z186,z5,z6])],[(0,[z351,z1,z2,z3,z8,z5,z6]),(0,[z1,z3,z50,z63,z8,z5,z6]),(0,[z1,z2,z3,z8,z352,z5,z6]),(0,[z1,z2,z3,z8,z5,z107,z10]),(0,[z0,z1,z3,z8,z5,z70,z6]),(0,[z1,z353,z3,z50,z8,z5,z6]),(0,[z0,z1,z3,z3,z8,z5,z6]),(0,[z1,z354,z2,z3,z8,z5,z6]),(0,[z355,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z115,z8,z5,z107]),(0,[z11,z1,z2,z3,z5,z150,z6])],[(0,[z1,z2,z3,z21,z8,z5,z6]),(0,[z46,z1,z3,z23,z8,z5,z6]),(0,[z356,z1,z2,z3,z8,z5,z6]),(1,[z1,z3,z357,z8,z5,z6]),(0,[z49,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z191,z5,z75,z6]),(0,[z53,z1,z2,z3,z8,z5,z6]),(1,[z1,z3,z8,z5,z6,z358]),(0,[z1,z2,z3,z8,z5,z6,z359])],[(0,[z1,z2,z3,z4,z5,z6,z10]),(1,[z1,z2,z3,z320,z5,z6]),(0,[z1,z2,z3,z360,z8,z5,z6]),(0,[z1,z3,z8,z191,z5,z198,z6]),(0,[z1,z2,z3,z8,z5,z198,z6]),(1,[z1,z2,z3,z8,z5,z313])]],
   [[(0,[z361,z1,z2,z3,z8,z5,z6]),(0,[z362,z1,z2,z3,z8,z5,z6]),(1,[z1,z3,z50,z4,z5,z6]),(0,[z1,z3,z50,z8,z5,z107,z6]),(0,[z0,z80,z1,z3,z8,z5,z6]),(0,[z363,z1,z2,z3,z8,z5,z6]),(1,[z163,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z210])],[(0,[z1,z2,z3,z8,z5,z364,z6]),(0,[z1,z95,z2,z3,z4,z5,z6]),(0,[z240,z1,z2,z3,z15,z5,z6]),(0,[z1,z3,z50,z8,z5,z20,z6]),(1,[z262,z1,z3,z8,z5,z6])],[(0,[z14,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z365,z8,z5,z6]),(0,[z1,z366,z2,z3,z8,z5,z6])],[(0,[z1,z3,z50,z8,z5,z122,z6]),(0,[z0,z0,z1,z3,z8,z5,z6]),(0,[z1,z367,z2,z3,z8,z5,z6]),(1,[z1,z2,z348,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z368])],[(0,[z369,z1,z2,z3,z8,z5,z6]),(0,[z370,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z371,z15,z5,z6]),(0,[z372,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z373,z8,z5,z6]),(0,[z1,z2,z3,z18,z8,z5,z150])],[(0,[z183,z2,z3,z8,z5,z6,z10]),(0,[z1,z374,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z375]),(0,[z1,z2,z3,z8,z376,z5,z6]),(0,[z87,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z218,z5,z6]),(0,[z377,z1,z2,z3,z8,z5,z6]),(0,[z378,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z108,z3,z8,z5,z6]),(0,[z123,z1,z2,z3,z8,z5,z254]),(0,[z1,z379,z2,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z5,z6]),(0,[z1,z3,z50,z8,z135,z5,z6]),(0,[z380,z1,z2,z3,z8,z5,z6]),(0,[z381,z1,z2,z3,z8,z5,z6])],[(0,[z123,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z382,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z383,z6])]],
   [[(0,[z1,z2,z3,z8,z384,z5,z6]),(0,[z1,z2,z3,z385,z8,z5,z6]),(0,[z386,z1,z2,z3,z8,z5,z6]),(0,[z80,z1,z2,z3,z18,z5,z6]),(0,[z1,z2,z387,z3,z8,z5,z6])],[(0,[z1,z2,z3,z388,z8,z5,z6]),(1,[z114,z2,z3,z8,z5,z10]),(0,[z0,z1,z149,z3,z8,z5,z6]),(0,[z389,z1,z2,z3,z8,z5,z6])],[(0,[z39,z1,z2,z63,z8,z5,z6]),(0,[z183,z2,z3,z15,z8,z5,z6]),(0,[z1,z2,z3,z8,z390,z5,z6]),(0,[z1,z2,z353,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z139,z5,z6])],[(0,[z391,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z392,z6]),(0,[z11,z1,z2,z3,z8,z5,z256])],[(0,[z393,z1,z2,z3,z8,z5,z6]),(0,[z1,z194,z2,z3,z15,z5,z6]),(1,[z1,z2,z3,z8,z5,z90]),(0,[z183,z9,z2,z3,z8,z5,z6]),(0,[z394,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z115,z50,z8,z5,z6]),(0,[z395,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z396,z5,z6]),(0,[z1,z2,z3,z8,z5,z397,z6]),(0,[z1,z2,z3,z8,z398,z5,z6]),(1,[z11,z1,z2,z3,z75,z6]),(0,[z11,z80,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z8,z5,z399,z6]),(0,[z1,z2,z3,z400,z8,z5,z6]),(0,[z11,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z70,z16]),(0,[z1,z2,z3,z8,z57,z5,z71])],[(0,[z1,z2,z3,z8,z401,z5,z6]),(0,[z1,z2,z3,z402,z8,z5,z6]),(1,[z1,z50,z8,z5,z6,z153]),(0,[z119,z1,z3,z50,z8,z5,z6]),(0,[z1,z2,z3,z315,z8,z5,z6]),(0,[z1,z132,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z26]),(0,[z1,z2,z3,z8,z403,z5,z6]),(0,[z404,z1,z2,z3,z8,z5,z6])],[(0,[z1,z149,z3,z50,z8,z5,z6]),(0,[z0,z1,z405,z3,z8,z5,z6]),(1,[z205,z2,z3,z8,z5,z6]),(0,[z11,z1,z2,z406,z8,z5,z6]),(0,[z1,z2,z3,z18,z300,z5,z6])]],
   [[(0,[z1,z2,z407,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z8,z5,z6]),(0,[z68,z1,z2,z3,z8,z5,z227]),(0,[z408,z0,z1,z3,z8,z5,z6]),(0,[z1,z409,z2,z3,z8,z5,z6]),(0,[z1,z410,z2,z3,z8,z5,z6]),(0,[z128,z1,z2,z8,z5,z6,z153]),(0,[z1,z2,z3,z8,z411,z5,z6])],[(0,[z1,z2,z3,z4,z5,z107,z6]),(0,[z22,z1,z2,z3,z8,z5,z26])],[(0,[z78,z1,z2,z50,z8,z5,z6]),(0,[z351,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z20,z6]),(0,[z22,z179,z1,z3,z8,z5,z6]),(0,[z22,z1,z3,z8,z5,z6,z26]),(0,[z11,z1,z2,z3,z8,z139,z6]),(0,[z1,z2,z3,z8,z5,z412,z6])],[(0,[z46,z1,z2,z3,z15,z5,z6]),(0,[z1,z2,z63,z8,z5,z20,z6]),(0,[z49,z1,z2,z3,z4,z5,z6]),(0,[z53,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z50,z8,z5,z162,z6]),(0,[z1,z2,z3,z413,z8,z5,z6])],[(0,[z1,z2,z3,z4,z5,z122,z6]),(0,[z1,z2,z115,z3,z15,z5,z6]),(0,[z414,z1,z2,z3,z8,z5,z6])],[(0,[z1,z3,z3,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z150,z6])],[(0,[z194,z2,z3,z23,z8,z5,z6]),(0,[z53,z1,z2,z3,z8,z122,z6])],[(0,[z415,z1,z2,z3,z8,z5,z6]),(0,[z128,z1,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z371,z8,z5,z6]),(0,[z1,z3,z50,z8,z5,z198,z6]),(0,[z0,z1,z3,z8,z5,z6,z127]),(0,[z1,z416,z2,z3,z8,z5,z6]),(0,[z417,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z3,z23,z8,z5,z122,z6]),(0,[z1,z418,z2,z3,z8,z5,z6]),(0,[z1,z204,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z293,z6]),(0,[z1,z2,z3,z15,z139,z5,z6]),(0,[z1,z419,z2,z3,z8,z5,z6]),(0,[z7,z0,z1,z3,z8,z5,z6]),(0,[z80,z1,z149,z2,z3,z5,z6]),(0,[z420,z1,z2,z3,z8,z5,z6]),(0,[z1,z421,z25,z2,z3,z5,z6]),(0,[z123,z1,z2,z3,z32,z5,z6]),(0,[z1,z3,z18,z422,z8,z5,z6])],[(0,[z423,z1,z2,z3,z8,z5,z6]),(0,[z424,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z425])],[(0,[z1,z2,z79,z3,z8,z5,z6]),(0,[z78,z1,z2,z3,z352,z5,z6]),(0,[z1,z2,z3,z8,z5,z426,z6]),(0,[z78,z1,z2,z3,z15,z5,z6]),(0,[z118,z1,z2,z3,z15,z5,z6]),(0,[z0,z1,z3,z8,z427,z5,z6]),(0,[z1,z196,z2,z3,z8,z5,z6]),(0,[z428,z1,z2,z3,z8,z5,z6]),(1,[z429,z2,z3,z8,z5,z6]),(0,[z1,z430,z2,z3,z8,z5,z6])],[(0,[z431,z1,z2,z3,z8,z5,z6]),(0,[z432,z1,z2,z3,z8,z5,z6]),(0,[z119,z1,z2,z8,z5,z20,z6]),(0,[z1,z31,z2,z3,z300,z5,z6]),(0,[z433,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z219,z8,z5,z6])],[(0,[z46,z2,z3,z23,z8,z5,z6]),(0,[z1,z434,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z15,z5,z6,z26]),(0,[z1,z2,z3,z8,z5,z435,z6]),(0,[z24,z0,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z436]),(0,[z1,z2,z3,z8,z5,z6,z437]),(0,[z1,z2,z3,z8,z5,z16,z26])],[(0,[z0,z93,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z438,z8,z5,z6]),(0,[z1,z2,z60,z3,z32,z5,z6]),(0,[z439,z1,z2,z3,z8,z5,z6])],[(0,[z114,z1,z2,z3,z15,z5,z6]),(0,[z34,z0,z1,z3,z8,z5,z6]),(0,[z0,z1,z95,z3,z8,z5,z6]),(0,[z189,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z191,z5,z6]),(0,[z1,z60,z3,z193,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z440])],[(0,[z1,z194,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z172,z6]),(0,[z68,z2,z3,z8,z5,z41,z6]),(0,[z1,z2,z3,z8,z5,z70,z153]),(0,[z1,z441,z3,z50,z8,z5,z6]),(1,[z1,z2,z3,z253,z5,z6]),(0,[z442,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z443,z6])]],
   [[(0,[z54,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z444,z6]),(0,[z1,z2,z3,z445,z8,z5,z6]),(0,[z1,z446,z2,z3,z8,z5,z6]),(0,[z447,z1,z2,z3,z8,z5,z6])],[(0,[z34,z2,z3,z8,z4,z5,z6]),(0,[z448,z1,z2,z3,z8,z5,z6]),(1,[z9,z2,z3,z8,z135,z6]),(1,[z1,z216,z3,z191,z5,z6])],[(0,[z449,z1,z2,z3,z8,z5,z6]),(0,[z39,z0,z1,z3,z8,z5,z6]),(1,[z1,z450,z3,z8,z5,z6]),(1,[z1,z2,z3,z305,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z113]),(0,[z1,z3,z50,z8,z139,z5,z6]),(0,[z22,z1,z3,z8,z191,z5,z6]),(0,[z1,z2,z3,z8,z5,z451,z6]),(1,[z1,z13,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z452,z5,z6]),(0,[z1,z132,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z15,z5,z150,z6]),(0,[z114,z1,z2,z3,z8,z5,z70]),(0,[z22,z1,z3,z50,z8,z5,z6]),(0,[z1,z2,z8,z137,z5,z20,z6]),(0,[z1,z2,z3,z453,z8,z5,z6]),(0,[z1,z454,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z112]),(0,[z0,z1,z3,z8,z57,z5,z6]),(0,[z11,z404,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z455,z6]),(0,[z39,z2,z3,z8,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z6]),(0,[z456,z1,z2,z3,z8,z5,z6]),(0,[z0,z1,z3,z50,z8,z5,z6]),(0,[z82,z1,z2,z3,z8,z5,z6]),(0,[z53,z1,z2,z3,z8,z5,z457]),(0,[z1,z2,z3,z8,z458,z5,z6]),(1,[z459,z1,z2,z3,z5,z6])],[(0,[z46,z1,z2,z3,z8,z5,z6]),(0,[z460,z1,z2,z3,z8,z5,z6]),(0,[z93,z194,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z461,z5,z6]),(0,[z1,z3,z50,z8,z5,z6,z26]),(0,[z0,z1,z3,z8,z5,z6,z153]),(0,[z1,z132,z2,z3,z8,z122,z6]),(0,[z462,z1,z2,z3,z8,z5,z6]),(0,[z22,z1,z2,z108,z8,z5,z6]),(0,[z1,z2,z3,z8,z463,z5,z6]),(0,[z1,z464,z2,z3,z8,z5,z6]),(1,[z338,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z465,z6]),(0,[z1,z2,z115,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z127,z71]),(0,[z160,z1,z13,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z198,z6]),(0,[z53,z1,z2,z3,z336,z5,z6]),(0,[z1,z466,z2,z3,z8,z5,z6])],[(0,[z53,z1,z3,z8,z5,z122,z6]),(0,[z467,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z71])],[(0,[z22,z1,z194,z3,z8,z5,z6]),(0,[z1,z2,z3,z15,z18,z5,z6]),(0,[z68,z1,z2,z3,z8,z135,z6]),(0,[z1,z2,z3,z8,z5,z457,z6]),(1,[z1,z2,z60,z32,z5,z6]),(0,[z1,z2,z3,z8,z5,z313,z6]),(0,[z468,z1,z2,z3,z8,z5,z6]),(0,[z160,z338,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z15,z191,z5,z6]),(0,[z1,z2,z3,z8,z5,z469,z6]),(0,[z1,z216,z2,z3,z191,z5,z6]),(0,[z1,z2,z348,z3,z8,z5,z6]),(1,[z1,z2,z88,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z470]),(0,[z1,z2,z3,z8,z5,z6,z471])],[(0,[z118,z1,z2,z3,z8,z5,z6]),(0,[z0,z1,z194,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z472,z6]),(0,[z1,z2,z473,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z474]),(1,[z1,z2,z3,z8,z5,z457]),(0,[z19,z1,z2,z8,z5,z20,z6]),(0,[z1,z2,z3,z8,z5,z6,z475]),(0,[z1,z2,z3,z476,z8,z5,z6])],[(1,[z1,z2,z3,z224,z5,z6]),(1,[z423,z1,z3,z8,z5,z6]),(0,[z9,z1,z2,z3,z15,z5,z6]),(0,[z1,z3,z50,z8,z5,z6,z250]),(1,[z179,z1,z149,z3,z5,z6]),(0,[z477,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z115,z81,z8,z5,z6])],[(0,[z34,z2,z3,z8,z5,z41,z6]),(0,[z19,z1,z2,z3,z8,z5,z159]),(0,[z1,z2,z3,z8,z5,z153,z71]),(0,[z1,z2,z3,z478,z8,z5,z6]),(0,[z479,z1,z2,z3,z8,z5,z6]),(0,[z11,z1,z2,z3,z300,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z6,z480]),(0,[z1,z481,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z482,z6]),(0,[z1,z2,z3,z8,z461,z5,z6]),(0,[z179,z1,z149,z2,z3,z5,z6]),(1,[z1,z2,z3,z336,z5,z6])],[(0,[z1,z434,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z483,z5,z6]),(0,[z1,z2,z3,z8,z5,z484,z6]),(0,[z68,z1,z2,z3,z8,z41,z6]),(0,[z114,z1,z2,z3,z8,z5,z6]),(0,[z485,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z326]),(0,[z1,z2,z3,z8,z5,z486,z6])],[(0,[z1,z2,z180,z3,z8,z5,z6]),(0,[z1,z2,z3,z487,z8,z5,z6]),(0,[z1,z2,z3,z300,z139,z5,z6])],[(1,[z46,z3,z23,z8,z5,z6]),(0,[z1,z2,z488,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z139,z5,z6]),(0,[z1,z2,z3,z8,z5,z41,z6]),(0,[z1,z2,z3,z8,z5,z489,z6]),(0,[z1,z2,z81,z8,z32,z5,z6]),(0,[z1,z2,z177,z3,z8,z5,z6]),(1,[z80,z1,z2,z3,z5,z127])],[(0,[z1,z194,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z490,z5,z6]),(0,[z1,z2,z3,z8,z57,z5,z16])],[(0,[z1,z2,z3,z491,z8,z5,z6]),(0,[z11,z0,z1,z3,z8,z5,z6]),(0,[z492,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z203,z6]),(1,[z1,z2,z3,z352,z5,z6]),(1,[z1,z2,z3,z15,z5,z6]),(0,[z34,z2,z3,z8,z5,z70,z6]),(0,[z1,z3,z50,z8,z191,z5,z6]),(0,[z1,z2,z3,z493,z8,z5,z6]),(0,[z1,z2,z3,z8,z32,z5,z6]),(1,[z1,z286,z3,z8,z5,z6])],[(0,[z78,z1,z2,z79,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z26]),(0,[z1,z2,z3,z8,z5,z494,z6]),(0,[z1,z2,z3,z345,z8,z5,z6]),(0,[z179,z1,z132,z3,z8,z5,z6]),(0,[z1,z2,z3,z193,z8,z5,z6]),(0,[z1,z2,z81,z3,z8,z5,z6]),(0,[z1,z164,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z224,z5,z6]),(0,[z495,z1,z2,z3,z8,z5,z6]),(0,[z2,z79,z3,z8,z4,z5,z6]),(0,[z1,z2,z3,z15,z5,z6,z71]),(0,[z1,z421,z2,z3,z8,z5,z6]),(0,[z1,z2,z496,z3,z8,z5,z6]),(0,[z1,z2,z3,z497,z8,z5,z6]),(0,[z1,z2,z3,z300,z8,z5,z6]),(0,[z1,z2,z3,z5,z75,z6,z127])],[(0,[z1,z2,z3,z8,z5,z498,z6]),(0,[z1,z216,z3,z8,z191,z5,z6]),(0,[z31,z110,z2,z3,z8,z5,z6]),(0,[z1,z499,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z5,z6,z210])],[(0,[z1,z2,z3,z3,z8,z5,z6]),(0,[z500,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z70,z6]),(0,[z1,z405,z2,z3,z8,z5,z6]),(0,[z205,z1,z2,z3,z8,z5,z6])],[(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z501,z1,z2,z3,z8,z5,z6]),(0,[z160,z1,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z502])],[(0,[z1,z2,z115,z3,z4,z5,z6]),(0,[z1,z25,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z503,z8,z5,z6]),(0,[z80,z464,z2,z3,z8,z5,z6])],[(0,[z39,z1,z296,z3,z8,z5,z6]),(0,[z1,z3,z50,z8,z4,z5,z6]),(0,[z1,z2,z3,z504,z8,z5,z6]),(1,[z1,z2,z3,z207,z5,z6]),(0,[z1,z2,z3,z505,z8,z5,z6]),(0,[z80,z1,z2,z3,z8,z5,z107]),(0,[z1,z2,z3,z8,z5,z506,z6])],[(1,[z1,z2,z473,z8,z5,z6]),(1,[z1,z2,z3,z376,z5,z6]),(0,[z1,z81,z3,z50,z8,z5,z6]),(0,[z507,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z508,z5,z6]),(0,[z128,z1,z2,z3,z4,z5,z6]),(0,[z509,z1,z2,z3,z8,z5,z6]),(0,[z510,z1,z2,z3,z8,z5,z6]),(0,[z80,z1,z2,z3,z5,z6,z127])]],
   [[(0,[z0,z49,z1,z3,z8,z5,z6]),(0,[z34,z1,z3,z50,z8,z5,z6]),(0,[z262,z1,z3,z8,z5,z6,z71])],[(0,[z1,z79,z3,z50,z8,z5,z6]),(0,[z1,z2,z3,z15,z5,z41,z6]),(0,[z9,z1,z2,z3,z8,z5,z6]),(1,[z1,z347,z3,z8,z5,z6]),(0,[z1,z25,z2,z3,z8,z5,z70]),(0,[z19,z0,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z511])],[(0,[z78,z1,z2,z3,z4,z5,z6]),(0,[z118,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z512,z5,z6]),(0,[z1,z3,z50,z8,z5,z6,z71]),(0,[z0,z1,z3,z8,z232,z5,z6]),(0,[z1,z2,z3,z8,z5,z513,z6]),(0,[z1,z2,z3,z253,z8,z5,z6]),(0,[z11,z1,z379,z3,z8,z5,z6])],[(0,[z93,z1,z2,z3,z48,z5,z6]),(1,[z1,z2,z3,z343,z5,z6]),(0,[z1,z31,z3,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z514]),(0,[z1,z2,z3,z8,z515,z5,z6]),(1,[z1,z2,z516,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z517])],[(0,[z93,z1,z2,z3,z59,z5,z6]),(0,[z1,z518,z2,z3,z8,z5,z6]),(0,[z39,z1,z3,z50,z8,z5,z6]),(0,[z1,z2,z3,z15,z32,z5,z6])],[(0,[z1,z2,z3,z8,z519,z5,z6]),(0,[z19,z1,z2,z3,z233,z5,z6]),(0,[z1,z2,z8,z5,z107,z6,z153]),(1,[z1,z2,z3,z398,z5,z6])],[(1,[z1,z2,z3,z8,z5,z40]),(1,[z2,z3,z4,z5,z41,z6]),(0,[z114,z1,z2,z3,z4,z5,z6]),(0,[z114,z1,z2,z3,z8,z5,z10]),(0,[z1,z2,z520,z3,z8,z5,z6]),(0,[z1,z2,z3,z300,z191,z5,z6])],[(0,[z1,z2,z3,z4,z191,z5,z6]),(0,[z1,z2,z3,z8,z135,z20,z6]),(0,[z1,z2,z521,z3,z8,z5,z6]),(0,[z1,z2,z3,z522,z8,z5,z6]),(0,[z1,z523,z2,z3,z8,z5,z6]),(0,[z1,z110,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z524,z6])]],
   [[(0,[z1,z2,z3,z15,z5,z70,z6]),(0,[z217,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z525,z6]),(0,[z1,z2,z3,z8,z5,z526,z6]),(0,[z1,z81,z3,z329,z8,z5,z6]),(0,[z1,z2,z527,z3,z8,z5,z6]),(0,[z1,z2,z3,z422,z8,z5,z6]),(0,[z160,z1,z2,z516,z8,z5,z6])],[(0,[z183,z2,z79,z3,z8,z5,z6]),(0,[z1,z2,z528,z3,z8,z5,z6]),(0,[z1,z2,z3,z15,z5,z6,z502]),(0,[z1,z60,z3,z50,z8,z5,z6])],[(0,[z1,z194,z3,z8,z5,z122,z6]),(0,[z1,z2,z79,z3,z15,z5,z6]),(0,[z34,z183,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z529,z8,z5,z6]),(0,[z1,z2,z530,z3,z8,z5,z6]),(0,[z168,z1,z2,z3,z8,z5,z6])],[(0,[z93,z1,z3,z50,z8,z5,z6]),(0,[z68,z1,z2,z3,z8,z5,z6]),(0,[z531,z1,z2,z3,z8,z5,z6]),(0,[z1,z95,z3,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z532,z6]),(0,[z533,z1,z2,z3,z8,z5,z6]),(0,[z1,z534,z2,z3,z8,z5,z6]),(0,[z80,z1,z2,z3,z8,z5,z127]),(0,[z1,z2,z535,z3,z8,z5,z6])],[(0,[z536,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z512,z5,z6]),(0,[z1,z3,z50,z8,z490,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z537])],[(0,[z1,z2,z3,z300,z4,z5,z6]),(0,[z538,z1,z2,z3,z15,z5,z6]),(0,[z34,z1,z2,z3,z8,z5,z70]),(0,[z0,z1,z216,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z539])],[(0,[z540,z1,z2,z3,z8,z5,z6]),(0,[z39,z183,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z541,z3,z8,z5,z6]),(0,[z1,z3,z50,z8,z32,z5,z6]),(0,[z1,z2,z50,z8,z5,z20,z6]),(0,[z1,z2,z3,z8,z542,z5,z6]),(0,[z543,z1,z2,z3,z8,z5,z6]),(0,[z160,z1,z2,z3,z8,z5,z6])],[(0,[z93,z1,z2,z3,z8,z5,z112]),(0,[z544,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z50,z15,z5,z6]),(0,[z1,z25,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z545]),(0,[z1,z2,z3,z8,z5,z6,z546]),(0,[z1,z2,z3,z139,z5,z75,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z6,z547]),(0,[z1,z2,z3,z8,z5,z548,z6]),(0,[z1,z3,z50,z300,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z549]),(1,[z1,z379,z3,z8,z5,z6])],[(0,[z183,z0,z1,z3,z8,z5,z6]),(0,[z448,z1,z2,z3,z15,z5,z6]),(0,[z1,z2,z550,z3,z8,z5,z6]),(0,[z114,z1,z2,z3,z461,z5,z6]),(0,[z123,z1,z3,z50,z8,z5,z6]),(0,[z1,z551,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z552,z6]),(0,[z553,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z107,z71]),(0,[z1,z3,z8,z5,z6,z358,z71])],[(0,[z554,z1,z2,z3,z8,z5,z6]),(1,[z93,z194,z3,z8,z5,z6]),(0,[z39,z1,z2,z3,z125,z5,z6]),(0,[z1,z3,z50,z8,z5,z70,z6]),(1,[z1,z421,z2,z3,z5,z6]),(0,[z555,z1,z2,z3,z8,z5,z6]),(0,[z19,z1,z2,z3,z8,z5,z225]),(0,[z1,z556,z2,z3,z8,z5,z6]),(0,[z557,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z300,z8,z139,z6]),(0,[z1,z2,z3,z8,z558,z5,z6]),(0,[z459,z1,z2,z3,z8,z5,z6])],[(0,[z559,z1,z2,z3,z8,z5,z6]),(0,[z93,z1,z194,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z560,z5,z6]),(0,[z183,z49,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z71]),(0,[z1,z2,z561,z3,z8,z5,z6])],[(0,[z0,z1,z3,z8,z5,z562,z6]),(0,[z563,z1,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z198,z6,z26]),(0,[z1,z2,z3,z8,z5,z564,z6]),(0,[z1,z2,z3,z8,z5,z6,z127])],[(0,[z1,z2,z3,z211,z8,z5,z6]),(0,[z1,z2,z3,z15,z300,z5,z6]),(0,[z259,z0,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z565,z5,z6])],[(0,[z1,z566,z2,z3,z8,z5,z6]),(0,[z9,z1,z2,z3,z4,z5,z6]),(0,[z179,z1,z149,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z567]),(0,[z11,z1,z3,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z427,z5,z6]),(0,[z179,z1,z216,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z568,z5,z6])]],
   [[(0,[z1,z2,z3,z569,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z570]),(1,[z1,z132,z3,z8,z232,z6]),(0,[z1,z2,z3,z8,z5,z571,z6])],[(0,[z1,z572,z2,z3,z8,z5,z6]),(0,[z119,z1,z2,z3,z15,z5,z6]),(0,[z1,z573,z2,z3,z8,z5,z6]),(0,[z0,z1,z3,z8,z5,z75,z6]),(0,[z53,z1,z2,z574,z8,z5,z6]),(0,[z53,z1,z2,z3,z8,z5,z436]),(0,[z1,z2,z3,z32,z5,z150,z6]),(0,[z1,z575,z2,z3,z8,z5,z6]),(0,[z128,z1,z2,z115,z8,z5,z6]),(0,[z1,z2,z273,z3,z8,z5,z6])],[(0,[z1,z2,z3,z4,z135,z5,z6]),(0,[z1,z2,z3,z576,z4,z5,z6]),(0,[z1,z2,z3,z4,z483,z5,z6]),(0,[z1,z149,z2,z3,z15,z5,z6]),(0,[z80,z1,z3,z50,z8,z5,z6]),(0,[z1,z577,z2,z3,z8,z5,z6]),(0,[z80,z1,z2,z3,z8,z5,z153])],[(0,[z1,z2,z296,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z578,z6]),(0,[z1,z2,z209,z3,z8,z5,z6]),(0,[z1,z2,z579,z3,z8,z5,z6])],[(0,[z1,z580,z2,z3,z8,z5,z6]),(0,[z581,z1,z2,z3,z8,z5,z6]),(0,[z1,z132,z3,z8,z5,z6,z26]),(1,[z1,z2,z3,z8,z5,z254]),(1,[z1,z2,z3,z8,z5,z256]),(0,[z1,z2,z3,z8,z582,z5,z6]),(0,[z160,z1,z2,z3,z8,z57,z6])],[(0,[z1,z2,z3,z583,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z584]),(0,[z0,z22,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z18,z8,z5,z107])],[(0,[z1,z194,z3,z8,z5,z198,z6]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z585,z6]),(0,[z1,z2,z3,z300,z32,z5,z6]),(0,[z123,z1,z2,z8,z5,z20,z6]),(0,[z1,z2,z3,z8,z5,z6,z586]),(0,[z1,z2,z3,z18,z5,z75,z6])],[(0,[z1,z2,z3,z4,z32,z5,z6]),(0,[z1,z2,z3,z15,z5,z587,z6]),(0,[z1,z2,z81,z50,z8,z5,z6])]],
   [[(0,[z39,z1,z204,z3,z8,z5,z6]),(1,[z39,z2,z3,z4,z5,z6]),(0,[z1,z588,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z494,z6]),(0,[z538,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z227,z6]),(0,[z2,z3,z8,z135,z5,z41,z6]),(0,[z1,z2,z3,z8,z5,z589,z6]),(0,[z1,z2,z3,z88,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z590,z6]),(0,[z591,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z81,z8,z5,z6,z153]),(1,[z1,z2,z406,z8,z5,z6])],[(0,[z592,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z574,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z436]),(0,[z1,z2,z3,z8,z57,z5,z6])],[(0,[z183,z2,z3,z8,z5,z41,z6]),(0,[z1,z2,z3,z15,z5,z6,z127]),(0,[z1,z2,z3,z8,z137,z41,z6]),(0,[z1,z2,z3,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z16,z127]),(1,[z92,z1,z3,z8,z5,z6])],[(0,[z160,z1,z2,z3,z4,z5,z6]),(0,[z19,z1,z3,z50,z8,z5,z6]),(0,[z1,z3,z50,z8,z5,z532,z6]),(0,[z1,z2,z3,z8,z5,z6,z153])],[(1,[z1,z2,z3,z8,z5,z203]),(0,[z1,z593,z2,z3,z8,z5,z6]),(0,[z1,z25,z2,z3,z4,z5,z6]),(0,[z594,z1,z2,z3,z8,z5,z6]),(0,[z1,z25,z2,z3,z8,z5,z10]),(1,[z1,z167,z3,z8,z5,z6])],[(0,[z14,z1,z194,z2,z8,z5,z6]),(0,[z0,z1,z3,z63,z8,z5,z6]),(0,[z114,z2,z3,z8,z5,z6,z10]),(0,[z1,z595,z2,z3,z8,z5,z6]),(0,[z53,z1,z132,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z596,z6]),(0,[z123,z1,z177,z3,z8,z5,z6]),(0,[z597,z1,z2,z3,z8,z5,z6])],[(0,[z1,z598,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z599,z5,z6]),(0,[z600,z1,z2,z3,z8,z5,z6]),(0,[z601,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z115,z3,z398,z5,z6])],[(0,[z1,z2,z602,z3,z8,z5,z6]),(0,[z1,z2,z81,z3,z15,z5,z6]),(0,[z68,z1,z450,z3,z8,z5,z6]),(0,[z68,z1,z2,z3,z305,z5,z6]),(1,[z1,z2,z3,z8,z5,z113]),(0,[z1,z603,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z604,z2,z3,z8,z5,z6]),(0,[z1,z605,z2,z3,z15,z5,z6]),(0,[z0,z1,z2,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z198,z71]),(0,[z1,z2,z3,z606,z8,z5,z6])],[(0,[z1,z2,z3,z8,z135,z137,z6]),(0,[z1,z2,z3,z8,z5,z607,z6]),(0,[z1,z2,z3,z608,z8,z5,z6])],[(0,[z78,z1,z2,z3,z343,z5,z6]),(0,[z609,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z610,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z611,z6]),(0,[z1,z2,z612,z3,z8,z5,z6]),(0,[z22,z1,z2,z3,z8,z5,z198]),(0,[z1,z31,z2,z3,z5,z75,z6])],[(0,[z1,z2,z3,z613,z8,z5,z6]),(1,[z39,z1,z50,z8,z5,z6]),(0,[z2,z3,z8,z4,z5,z41,z6]),(0,[z1,z614,z2,z3,z8,z5,z6]),(0,[z1,z615,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z18,z8,z5,z127])],[(0,[z1,z2,z3,z8,z5,z6,z616]),(0,[z119,z1,z2,z3,z8,z5,z6]),(0,[z223,z1,z3,z50,z8,z5,z6]),(0,[z1,z132,z3,z8,z191,z5,z6]),(0,[z1,z2,z3,z329,z8,z5,z6]),(0,[z459,z1,z2,z3,z5,z6,z71])],[(0,[z9,z78,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z569,z4,z5,z6]),(0,[z1,z141,z3,z50,z8,z5,z6]),(0,[z1,z149,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z617,z6]),(0,[z1,z2,z3,z8,z5,z618,z6])],[(0,[z1,z2,z3,z8,z444,z5,z6]),(1,[z1,z2,z65,z8,z5,z6]),(0,[z1,z2,z3,z8,z619,z5,z6])],[(0,[z1,z2,z3,z15,z57,z5,z6]),(0,[z1,z2,z3,z8,z41,z20,z6]),(0,[z0,z119,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z620,z5,z6]),(0,[z1,z2,z3,z8,z621,z5,z6])]],
   [[(0,[z1,z2,z622,z3,z8,z5,z6]),(0,[z0,z1,z2,z3,z15,z5,z6]),(0,[z34,z1,z2,z3,z8,z5,z10]),(0,[z1,z3,z50,z8,z5,z150,z6]),(1,[z22,z1,z3,z8,z5,z26]),(0,[z623,z1,z2,z3,z8,z5,z6]),(0,[z19,z1,z341,z3,z8,z5,z6]),(1,[z479,z1,z3,z8,z5,z6])],[(0,[z581,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z15,z5,z6,z153]),(0,[z1,z624,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z16,z153]),(1,[z226,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z625]),(0,[z1,z2,z79,z3,z4,z5,z6]),(0,[z179,z1,z3,z50,z8,z5,z6]),(0,[z626,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z159]),(0,[z1,z2,z3,z8,z5,z627,z6])],[(0,[z1,z2,z3,z8,z5,z628,z6]),(0,[z423,z1,z79,z3,z8,z5,z6]),(0,[z183,z1,z3,z50,z8,z5,z6]),(0,[z22,z1,z2,z3,z8,z5,z70]),(0,[z119,z1,z2,z81,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z629]),(0,[z1,z3,z8,z232,z5,z122,z6]),(0,[z1,z429,z2,z3,z8,z5,z6]),(0,[z19,z1,z151,z3,z8,z5,z6]),(0,[z1,z2,z3,z630,z8,z5,z6]),(0,[z1,z631,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z632,z6]),(0,[z1,z633,z2,z3,z8,z5,z6]),(0,[z244,z1,z3,z50,z8,z5,z6]),(0,[z19,z1,z2,z3,z350,z5,z6])],[(0,[z1,z2,z3,z357,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z634]),(0,[z9,z2,z3,z8,z5,z6,z10]),(0,[z1,z3,z50,z583,z8,z5,z6]),(1,[z1,z3,z478,z8,z5,z6]),(1,[z404,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z358])],[(0,[z2,z3,z8,z5,z41,z6,z10]),(0,[z53,z196,z2,z3,z8,z5,z6]),(0,[z160,z226,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z50,z4,z5,z6]),(0,[z0,z1,z60,z3,z8,z5,z6]),(0,[z1,z2,z3,z516,z8,z5,z6])]],
   [[(1,[z1,z180,z3,z8,z5,z6]),(0,[z19,z163,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z107,z16])],[(0,[z46,z1,z2,z3,z21,z5,z6]),(0,[z39,z1,z2,z3,z8,z444,z6]),(0,[z594,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z547]),(0,[z1,z2,z3,z8,z5,z6,z635])],[(0,[z9,z2,z3,z23,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z636]),(0,[z1,z3,z50,z50,z8,z5,z6]),(0,[z1,z25,z3,z8,z5,z122,z6]),(0,[z1,z2,z3,z8,z5,z637,z6]),(0,[z1,z2,z3,z18,z8,z5,z153]),(0,[z11,z1,z2,z229,z8,z5,z6])],[(0,[z1,z605,z2,z3,z8,z5,z6]),(0,[z68,z1,z2,z3,z15,z5,z6]),(1,[z34,z2,z3,z8,z5,z70]),(0,[z1,z2,z3,z8,z638,z5,z6])],[(0,[z1,z2,z3,z8,z5,z40,z6]),(0,[z639,z1,z2,z3,z8,z5,z6]),(1,[z53,z1,z3,z8,z122,z6]),(0,[z1,z341,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z300,z5,z6,z127])],[(0,[z93,z2,z3,z8,z5,z41,z6]),(0,[z1,z2,z3,z640,z8,z5,z6]),(0,[z9,z1,z2,z3,z512,z5,z6]),(0,[z1,z216,z3,z50,z8,z5,z6]),(0,[z1,z441,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z641,z6]),(1,[z1,z2,z3,z212,z5,z6]),(0,[z1,z115,z3,z478,z8,z5,z6])],[(1,[z1,z2,z136,z8,z5,z6]),(0,[z279,z1,z3,z50,z8,z5,z6]),(0,[z53,z0,z1,z3,z8,z5,z6]),(0,[z642,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z643,z6]),(0,[z644,z1,z2,z3,z8,z5,z6]),(0,[z11,z1,z2,z3,z5,z75,z6]),(0,[z1,z2,z3,z8,z5,z150,z71])],[(0,[z1,z2,z3,z8,z5,z645,z6]),(1,[z78,z2,z79,z8,z5,z6]),(0,[z2,z3,z15,z8,z4,z5,z6]),(0,[z1,z646,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z232,z5,z6]),(0,[z1,z647,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z648,z6]),(0,[z1,z2,z3,z8,z649,z5,z6])]],
   [[(0,[z650,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z130,z3,z8,z5,z6]),(0,[z651,z1,z2,z3,z8,z5,z6]),(0,[z652,z1,z2,z3,z8,z5,z6])],[(0,[z653,z1,z2,z3,z8,z5,z6]),(0,[z49,z2,z3,z8,z4,z5,z6]),(0,[z119,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z150,z6]),(0,[z1,z2,z3,z15,z504,z5,z6]),(0,[z22,z1,z2,z3,z8,z5,z6]),(0,[z1,z654,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z655,z5,z6]),(0,[z1,z2,z3,z8,z5,z656,z6]),(0,[z1,z657,z2,z3,z8,z5,z6]),(0,[z1,z149,z2,z3,z4,z5,z6]),(0,[z658,z1,z2,z3,z8,z5,z6]),(0,[z0,z509,z1,z3,z8,z5,z6]),(0,[z0,z1,z3,z8,z137,z5,z6])],[(0,[z1,z2,z3,z8,z576,z5,z6]),(0,[z68,z1,z2,z473,z8,z5,z6]),(0,[z0,z1,z2,z3,z8,z5,z6]),(0,[z1,z659,z2,z3,z8,z5,z6]),(0,[z22,z1,z3,z8,z232,z5,z6]),(0,[z1,z2,z3,z8,z5,z660,z6])],[(0,[z661,z1,z2,z3,z8,z5,z6]),(0,[z9,z2,z3,z63,z8,z5,z6]),(0,[z1,z2,z3,z662,z8,z5,z6]),(0,[z1,z663,z2,z3,z8,z5,z6]),(0,[z1,z2,z81,z79,z8,z5,z6]),(0,[z1,z167,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z664,z8,z5,z6]),(0,[z1,z2,z3,z665,z8,z5,z6]),(0,[z1,z2,z3,z8,z666,z5,z6])],[(0,[z46,z93,z2,z3,z8,z5,z6]),(0,[z46,z1,z3,z50,z8,z5,z6]),(0,[z667,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z668])],[(0,[z1,z194,z132,z3,z8,z5,z6]),(0,[z68,z9,z2,z3,z8,z5,z6]),(0,[z1,z450,z2,z3,z8,z5,z6]),(0,[z669,z1,z2,z3,z8,z5,z6]),(1,[z0,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z670]),(0,[z1,z2,z3,z8,z671,z5,z6])],[(0,[z39,z1,z2,z50,z8,z5,z6]),(0,[z2,z3,z63,z8,z5,z41,z6]),(0,[z1,z2,z672,z3,z8,z5,z6]),(0,[z1,z3,z8,z232,z5,z198,z6]),(0,[z22,z1,z25,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z212,z5,z6]),(0,[z673,z1,z2,z3,z8,z5,z6]),(0,[z1,z164,z2,z115,z3,z5,z6]),(0,[z674,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z481,z2,z3,z4,z5,z6]),(0,[z1,z2,z675,z3,z8,z5,z6]),(0,[z676,z1,z2,z3,z8,z5,z6]),(0,[z677,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z81,z8,z137,z6])],[(0,[z1,z2,z3,z8,z5,z678,z6]),(0,[z1,z3,z360,z50,z8,z5,z6]),(0,[z128,z1,z3,z50,z8,z5,z6]),(0,[z0,z1,z25,z3,z8,z5,z6]),(0,[z1,z2,z3,z679,z8,z5,z6]),(0,[z1,z2,z3,z680,z8,z5,z6])],[(0,[z1,z2,z3,z8,z47,z5,z6]),(0,[z1,z681,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z682,z6]),(1,[z123,z1,z31,z2,z5,z6]),(1,[z464,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z683,z8,z5,z6])],[(0,[z34,z1,z2,z3,z15,z5,z6]),(0,[z1,z286,z2,z3,z8,z5,z6]),(0,[z1,z36,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z684,z5,z6])],[(0,[z685,z1,z2,z3,z8,z5,z6]),(0,[z78,z1,z3,z50,z8,z5,z6]),(0,[z119,z78,z1,z2,z8,z5,z6]),(0,[z34,z114,z2,z3,z8,z5,z6]),(0,[z686,z1,z2,z3,z8,z5,z6]),(0,[z168,z80,z2,z3,z8,z5,z6])],[(0,[z687,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z688,z5,z6]),(0,[z1,z2,z3,z15,z232,z5,z6]),(0,[z1,z2,z3,z8,z5,z689,z6]),(0,[z1,z2,z3,z8,z5,z6,z690])],[(0,[z39,z119,z1,z2,z8,z5,z6]),(0,[z1,z3,z50,z8,z5,z41,z6]),(0,[z1,z2,z3,z8,z5,z691,z6]),(1,[z1,z2,z3,z295,z5,z6]),(0,[z1,z25,z3,z8,z5,z198,z6]),(1,[z1,z3,z422,z8,z5,z6])],[(0,[z39,z1,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z4,z452,z5,z6]),(0,[z1,z2,z81,z3,z4,z5,z6]),(0,[z1,z1,z2,z3,z15,z5,z6]),(0,[z692,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z198,z16]),(0,[z1,z2,z3,z8,z5,z6,z693]),(0,[z1,z2,z3,z8,z5,z694,z6])]],
   [[(0,[z408,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z5,z6]),(0,[z1,z2,z81,z3,z8,z20,z6])],[(0,[z1,z2,z3,z8,z5,z169,z6]),(0,[z1,z2,z3,z8,z5,z562,z6]),(0,[z1,z2,z3,z8,z5,z6,z695])],[(0,[z0,z1,z3,z8,z5,z16,z6]),(0,[z1,z2,z3,z8,z696,z5,z6]),(0,[z19,z429,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z350,z8,z5,z6]),(0,[z1,z2,z115,z8,z5,z107,z6]),(1,[z1,z2,z273,z8,z5,z6])],[(0,[z697,z1,z2,z3,z8,z5,z6]),(0,[z34,z1,z2,z3,z376,z5,z6]),(0,[z698,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z699])],[(0,[z2,z3,z23,z8,z5,z41,z6]),(0,[z1,z2,z3,z8,z5,z587,z6]),(1,[z1,z50,z8,z5,z20,z6]),(0,[z414,z0,z1,z3,z8,z5,z6]),(0,[z0,z128,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z700,z8,z5,z6]),(0,[z1,z2,z3,z8,z233,z5,z6]),(0,[z1,z701,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z406,z8,z5,z6])],[(0,[z78,z1,z2,z63,z8,z5,z6]),(1,[z78,z1,z50,z8,z5,z6]),(0,[z702,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z703,z6]),(1,[z1,z115,z50,z8,z5,z6]),(0,[z119,z1,z2,z8,z5,z6,z153]),(0,[z1,z2,z3,z574,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z704,z6]),(0,[z1,z2,z3,z8,z5,z26,z71])],[(0,[z93,z1,z2,z3,z15,z5,z6]),(0,[z705,z1,z2,z3,z8,z5,z6]),(0,[z114,z1,z2,z3,z121,z5,z6]),(0,[z22,z1,z2,z3,z8,z5,z10]),(0,[z34,z1,z347,z3,z8,z5,z6]),(0,[z479,z1,z115,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z75,z6])],[(0,[z1,z194,z2,z136,z8,z5,z6]),(0,[z1,z79,z3,z357,z8,z5,z6]),(1,[z2,z3,z15,z4,z5,z6]),(0,[z658,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z50,z8,z232,z5,z6]),(0,[z1,z2,z3,z32,z5,z75,z6]),(1,[z1,z2,z3,z8,z5,z225]),(0,[z1,z2,z3,z8,z5,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z707,z8,z5,z6]),(0,[z39,z1,z50,z8,z5,z90]),(0,[z2,z3,z4,z5,z16,z10]),(0,[z2,z3,z4,z5,z6,z297]),(0,[z1,z2,z3,z4,z5,z254]),(0,[z708,z1,z3,z8,z5,z6]),(0,[z36,z2,z229,z8,z5,z6])],[(0,[z1,z50,z8,z5,z6,z90]),(0,[z2,z3,z4,z5,z67,z6]),(0,[z0,z1,z3,z709,z5,z6]),(0,[z1,z81,z478,z8,z5,z6])],[(0,[z1,z2,z710,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z711]),(0,[z712,z2,z3,z8,z5,z6]),(0,[z82,z1,z574,z8,z5,z6]),(0,[z713,z2,z3,z8,z5,z6])],[(0,[z1,z132,z3,z8,z688,z6]),(0,[z1,z204,z3,z125,z5,z6]),(0,[z1,z3,z714,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z715]),(0,[z1,z62,z229,z8,z5,z6])],[(0,[z1,z2,z3,z716,z5,z6]),(0,[z1,z2,z406,z4,z5,z6]),(0,[z1,z2,z3,z15,z5,z227]),(0,[z1,z2,z81,z15,z137,z6]),(0,[z1,z2,z229,z15,z5,z6]),(0,[z1,z164,z2,z3,z5,z6]),(0,[z1,z2,z3,z717,z5,z6]),(0,[z36,z2,z3,z5,z75,z6])],[(0,[z1,z2,z574,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z436]),(0,[z1,z2,z3,z718,z5,z6]),(0,[z1,z387,z50,z8,z5,z6])],[(0,[z92,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z569,z5,z150]),(0,[z82,z1,z3,z8,z218,z6]),(0,[z1,z421,z25,z3,z5,z198])],[(0,[z1,z296,z3,z8,z444,z6]),(0,[z1,z719,z3,z8,z5,z6]),(0,[z1,z2,z720,z8,z5,z6]),(0,[z2,z3,z360,z4,z5,z6]),(0,[z1,z2,z721,z8,z5,z6]),(0,[z240,z1,z50,z15,z5,z6]),(0,[z1,z2,z3,z5,z6,z722]),(0,[z1,z62,z3,z5,z75,z6])],[(0,[z1,z2,z3,z4,z5,z203]),(0,[z39,z2,z3,z4,z172,z6]),(0,[z1,z2,z3,z8,z5,z723]),(0,[z2,z3,z4,z5,z10,z71]),(0,[z317,z2,z3,z4,z5,z6]),(0,[z429,z3,z50,z8,z5,z6]),(0,[z1,z177,z3,z8,z5,z6]),(0,[z54,z509,z3,z8,z5,z6]),(0,[z53,z1,z348,z8,z122,z6]),(0,[z1,z2,z3,z724,z5,z6])],[(0,[z39,z2,z15,z63,z5,z6]),(0,[z1,z725,z3,z8,z5,z6])],[(0,[z1,z138,z3,z15,z5,z6]),(0,[z1,z353,z3,z8,z5,z162]),(0,[z1,z647,z50,z8,z5,z6]),(0,[z0,z726,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z727]),(0,[z728,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z4,z5,z113]),(0,[z2,z3,z4,z5,z116,z6]),(0,[z1,z550,z50,z8,z5,z6]),(0,[z53,z1,z3,z8,z122,z6]),(0,[z1,z341,z3,z233,z5,z6]),(0,[z11,z1,z2,z229,z75,z6])],[(0,[z1,z2,z3,z8,z729,z6]),(0,[z0,z1,z339,z8,z5,z6]),(0,[z1,z50,z8,z5,z246,z6])],[(0,[z1,z2,z730,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z731]),(0,[z1,z561,z50,z8,z5,z6])],[(0,[z1,z2,z273,z15,z5,z6]),(0,[z1,z2,z3,z8,z732,z6]),(0,[z733,z2,z3,z8,z5,z6]),(0,[z734,z1,z3,z8,z5,z6])],[(0,[z1,z2,z3,z47,z5,z6]),(0,[z39,z1,z50,z4,z5,z6]),(0,[z240,z2,z3,z4,z5,z6]),(0,[z1,z2,z735,z4,z5,z6]),(0,[z9,z3,z50,z8,z135,z6]),(0,[z123,z1,z31,z286,z5,z6]),(0,[z1,z3,z736,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z737]),(1,[z2,z3,z738,z5,z6]),(0,[z1,z739,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z740])],[(0,[z1,z115,z50,z15,z5,z6]),(0,[z1,z741,z2,z3,z5,z6]),(0,[z742,z2,z3,z8,z5,z6])],[(0,[z0,z1,z3,z8,z5,z40]),(0,[z1,z2,z65,z4,z5,z6]),(0,[z1,z2,z3,z743,z5,z6]),(0,[z1,z3,z744,z8,z5,z6]),(0,[z1,z450,z3,z8,z5,z113]),(0,[z53,z1,z3,z8,z148,z6]),(0,[z0,z1,z348,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z745]),(0,[z1,z273,z50,z8,z5,z6])],[(0,[z1,z746,z3,z8,z5,z6]),(0,[z479,z1,z3,z4,z5,z6]),(0,[z1,z50,z438,z8,z5,z6]),(0,[z747,z1,z50,z8,z5,z6]),(0,[z1,z2,z3,z219,z5,z6])],[(0,[z0,z1,z3,z8,z5,z6]),(0,[z226,z2,z3,z4,z5,z6]),(0,[z429,z2,z8,z5,z20,z6]),(0,[z748,z2,z3,z8,z5,z6])],[(0,[z1,z204,z3,z8,z5,z90]),(0,[z1,z2,z63,z8,z172,z6]),(0,[z87,z78,z50,z8,z5,z6]),(0,[z1,z749,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z6,z750]),(0,[z1,z50,z8,z5,z70,z153]),(0,[z1,z2,z3,z751,z5,z6]),(0,[z1,z2,z3,z186,z5,z16])],[(0,[z1,z752,z3,z4,z5,z6]),(0,[z753,z1,z2,z3,z8,z5]),(0,[z19,z1,z2,z15,z20,z6]),(0,[z1,z2,z3,z754,z5,z6]),(0,[z0,z1,z503,z8,z5,z6]),(0,[z1,z2,z574,z8,z5,z457]),(0,[z429,z2,z3,z8,z5,z159]),(0,[z404,z2,z3,z8,z5,z256])],[(0,[z1,z2,z3,z755,z5,z6]),(0,[z1,z2,z3,z756,z5,z6]),(0,[z757,z1,z2,z8,z5,z6]),(0,[z686,z1,z2,z8,z5,z153])],[(0,[z133,z2,z3,z125,z5,z6]),(0,[z39,z2,z63,z8,z444,z6]),(0,[z0,z3,z4,z5,z6,z10]),(0,[z2,z3,z4,z5,z107,z10]),(0,[z1,z3,z478,z4,z5,z6]),(0,[z464,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z15,z5,z758]),(0,[z1,z3,z15,z422,z5,z6]),(1,[z2,z65,z8,z41,z6]),(0,[z759,z2,z3,z8,z5,z6])],[(0,[z14,z93,z194,z8,z5,z6]),(0,[z168,z2,z3,z4,z5,z6]),(0,[z22,z1,z3,z8,z5,z616]),(0,[z1,z2,z574,z336,z5,z6]),(0,[z1,z2,z3,z336,z5,z436]),(0,[z1,z2,z3,z760,z5,z6])],[(0,[z1,z2,z3,z761,z5,z6]),(0,[z1,z3,z8,z5,z122,z436]),(0,[z1,z762,z3,z8,z5,z6]),(0,[z1,z151,z3,z8,z5,z225]),(0,[z1,z763,z3,z8,z5,z6])],[(0,[z1,z180,z3,z4,z5,z6]),(0,[z594,z2,z3,z8,z5,z10]),(0,[z1,z56,z3,z15,z5,z6]),(0,[z1,z2,z3,z764,z5,z6]),(0,[z1,z574,z8,z5,z198,z6])],[(0,[z1,z2,z3,z295,z5,z6]),(0,[z292,z1,z149,z3,z5,z6]),(0,[z1,z3,z422,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z765]),(0,[z2,z3,z8,z4,z5,z90]),(0,[z1,z2,z3,z5,z766,z6])],[(0,[z2,z3,z371,z4,z5,z6]),(0,[z34,z2,z3,z4,z5,z70]),(0,[z600,z2,z3,z4,z5,z6]),(0,[z53,z1,z3,z8,z176,z6]),(0,[z36,z2,z3,z8,z5,z12]),(0,[z1,z2,z516,z8,z5,z16])]],
   [[(0,[z14,z1,z204,z8,z5,z6]),(0,[z1,z115,z50,z398,z5,z6]),(0,[z36,z3,z50,z8,z5,z6])],[(0,[z1,z2,z3,z767,z5,z6]),(0,[z1,z229,z768,z8,z5,z6]),(0,[z1,z2,z769,z8,z5,z6])],[(0,[z1,z2,z770,z8,z5,z6]),(0,[z1,z2,z136,z4,z5,z6]),(0,[z1,z2,z3,z771,z5,z6]),(0,[z372,z1,z2,z3,z8,z71]),(0,[z1,z2,z772,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z773]),(0,[z1,z62,z3,z8,z5,z12]),(0,[z1,z2,z3,z300,z5,z256]),(0,[z160,z1,z3,z8,z358,z71])],[(0,[z78,z2,z79,z4,z5,z6]),(0,[z1,z50,z8,z5,z20,z6]),(0,[z1,z50,z8,z306,z5,z6]),(0,[z774,z1,z3,z8,z5,z6])],[(0,[z1,z3,z50,z352,z5,z6]),(0,[z1,z3,z50,z15,z5,z6]),(0,[z1,z2,z3,z775,z5,z6]),(0,[z1,z315,z50,z8,z20,z6]),(0,[z22,z196,z3,z8,z5,z6]),(0,[z53,z1,z3,z253,z122,z6])],[(0,[z1,z136,z8,z5,z198,z6]),(0,[z74,z2,z3,z8,z41,z6]),(0,[z34,z167,z3,z8,z5,z70]),(0,[z179,z1,z776,z3,z5,z6]),(0,[z777,z1,z3,z8,z5,z6]),(0,[z80,z1,z2,z406,z5,z6])],[(0,[z2,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z778]),(0,[z1,z779,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z225]),(0,[z1,z2,z3,z8,z780,z6])],[(0,[z110,z2,z3,z15,z5,z6]),(0,[z1,z2,z781,z8,z5,z6]),(0,[z1,z2,z3,z782,z5,z6]),(0,[z0,z783,z3,z8,z5,z6]),(0,[z464,z2,z3,z191,z5,z6])],[(0,[z1,z2,z3,z8,z784,z6]),(0,[z1,z2,z3,z15,z5,z112]),(0,[z1,z2,z3,z8,z5,z785]),(0,[z2,z79,z4,z5,z20,z6]),(0,[z1,z2,z4,z5,z6,z786]),(0,[z787,z1,z3,z8,z5,z6]),(0,[z0,z1,z3,z8,z5,z254]),(0,[z788,z2,z3,z8,z5,z6]),(0,[z1,z3,z5,z6,z210,z358])],[(1,[z2,z3,z4,z5,z90]),(0,[z1,z2,z3,z789,z5,z6]),(0,[z0,z119,z1,z15,z5,z6]),(0,[z1,z348,z50,z8,z5,z6]),(0,[z1,z56,z516,z8,z5,z6])],[(0,[z2,z3,z283,z4,z5,z6]),(0,[z0,z1,z50,z15,z5,z6]),(0,[z0,z464,z3,z8,z5,z6])],[(0,[z87,z2,z3,z4,z5,z6]),(0,[z534,z2,z3,z15,z5,z6]),(0,[z3,z50,z8,z5,z790,z6]),(0,[z791,z2,z3,z8,z5,z6]),(0,[z1,z776,z2,z3,z5,z6]),(0,[z1,z792,z3,z8,z5,z6]),(0,[z168,z80,z2,z3,z5,z127])],[(0,[z49,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z793,z5,z6]),(0,[z1,z2,z81,z4,z137,z6]),(0,[z1,z2,z229,z4,z5,z6]),(0,[z1,z2,z3,z794,z5,z6]),(0,[z1,z3,z50,z376,z5,z6]),(0,[z1,z2,z795,z8,z5,z6]),(0,[z1,z3,z796,z8,z5,z6])],[(0,[z34,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z207,z5,z113]),(0,[z0,z1,z3,z797,z5,z6]),(0,[z798,z2,z3,z8,z5,z6]),(0,[z429,z2,z3,z233,z5,z6]),(1,[z799,z2,z3,z5,z6]),(0,[z800,z1,z229,z8,z5,z6]),(0,[z262,z1,z801,z8,z5,z6])],[(0,[z2,z3,z59,z5,z41,z6]),(0,[z0,z1,z3,z8,z172,z6]),(0,[z468,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z15,z5,z802]),(0,[z1,z2,z473,z8,z5,z113]),(0,[z0,z1,z3,z8,z5,z803]),(0,[z0,z1,z3,z253,z5,z6]),(0,[z380,z1,z2,z8,z20,z6]),(0,[z1,z115,z329,z8,z5,z6]),(0,[z1,z2,z115,z8,z5,z804])],[(0,[z1,z2,z3,z48,z5,z6])]],
   [[(0,[z1,z2,z3,z59,z5,z6]),(0,[z1,z296,z3,z8,z5,z6]),(0,[z0,z1,z3,z8,z5,z203]),(0,[z1,z3,z50,z8,z5,z313]),(0,[z1,z13,z3,z219,z5,z6])],[(0,[z1,z2,z805,z8,z5,z6]),(0,[z1,z2,z806,z8,z5,z6])],[(0,[z1,z88,z23,z8,z5,z6]),(0,[z1,z2,z3,z807,z5,z6]),(0,[z753,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z5,z6,z808]),(0,[z1,z2,z801,z8,z5,z6])],[(0,[z93,z3,z360,z8,z5,z6]),(0,[z78,z2,z720,z8,z5,z6]),(0,[z1,z2,z3,z15,z5,z159]),(0,[z1,z2,z3,z809,z5,z6]),(0,[z1,z450,z3,z8,z5,z227]),(0,[z1,z3,z810,z8,z5,z6]),(0,[z1,z3,z50,z398,z5,z6]),(0,[z1,z2,z3,z8,z5,z811]),(0,[z812,z2,z3,z8,z5,z6]),(0,[z160,z1,z56,z3,z8,z71])],[(0,[z34,z2,z3,z8,z5,z344]),(0,[z1,z2,z65,z207,z5,z6]),(0,[z2,z3,z8,z5,z70,z813]),(0,[z1,z81,z50,z8,z5,z6]),(0,[z1,z2,z3,z814,z5,z6]),(0,[z196,z2,z3,z8,z5,z457])],[(0,[z1,z2,z815,z8,z5,z6]),(0,[z0,z1,z3,z461,z5,z6]),(0,[z1,z2,z3,z8,z5,z816]),(0,[z1,z2,z530,z32,z5,z6]),(0,[z1,z379,z3,z8,z5,z256])],[(0,[z1,z2,z273,z4,z5,z6]),(0,[z747,z1,z81,z8,z5,z6]),(0,[z1,z132,z3,z8,z599,z6]),(0,[z1,z2,z817,z8,z5,z6])],[(0,[z1,z2,z3,z818,z5,z6]),(0,[z1,z3,z357,z15,z5,z6]),(0,[z543,z2,z3,z4,z5,z6]),(0,[z819,z3,z50,z8,z5,z6]),(0,[z196,z2,z3,z336,z5,z6]),(0,[z1,z2,z406,z5,z150,z6])],[(0,[z93,z194,z3,z48,z5,z6]),(0,[z1,z204,z50,z8,z5,z6]),(0,[z2,z3,z65,z8,z41,z6]),(0,[z1,z141,z3,z190,z5,z6]),(0,[z259,z1,z3,z8,z5,z326]),(0,[z1,z2,z3,z820,z5,z6]),(0,[z1,z2,z3,z821,z5,z6]),(0,[z196,z3,z8,z5,z122,z6]),(0,[z11,z36,z2,z3,z75,z6]),(0,[z80,z1,z3,z422,z5,z6])],[(0,[z93,z194,z3,z59,z5,z6]),(0,[z540,z2,z3,z4,z5,z6]),(0,[z1,z115,z50,z4,z5,z6]),(0,[z1,z2,z3,z822,z5,z6]),(0,[z1,z2,z823,z8,z5,z6])],[(0,[z301,z2,z3,z8,z5,z10]),(0,[z0,z1,z60,z32,z5,z6]),(0,[z0,z338,z3,z8,z5,z6]),(0,[z824,z2,z3,z8,z5,z6]),(0,[z1,z825,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z826])],[(0,[z1,z3,z193,z15,z5,z6]),(0,[z827,z1,z2,z3,z5,z6]),(0,[z1,z551,z50,z8,z5,z6])],[(0,[z0,z1,z3,z224,z5,z6]),(0,[z1,z3,z50,z8,z5,z90]),(0,[z2,z79,z3,z352,z5,z6]),(0,[z1,z2,z3,z828,z5,z6]),(0,[z1,z151,z3,z350,z5,z6])],[(0,[z1,z180,z3,z207,z5,z6]),(0,[z1,z3,z829,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z830])],[(0,[z1,z2,z831,z8,z5,z6]),(0,[z1,z832,z3,z8,z5,z6]),(0,[z39,z2,z63,z8,z5,z40]),(0,[z19,z1,z2,z4,z20,z6]),(0,[z1,z180,z473,z8,z5,z6]),(0,[z347,z3,z8,z5,z41,z6]),(0,[z262,z1,z3,z8,z5,z70]),(0,[z22,z1,z3,z8,z5,z695]),(0,[z464,z2,z3,z32,z5,z6])]],
   [[(0,[z1,z204,z3,z15,z5,z6]),(0,[z292,z28,z1,z3,z5,z6]),(0,[z1,z2,z3,z833,z5,z6])],[(0,[z2,z3,z4,z5,z10,z153]),(0,[z834,z1,z2,z15,z5,z6]),(0,[z1,z672,z50,z8,z5,z6]),(0,[z1,z3,z329,z8,z5,z6]),(0,[z835,z1,z2,z3,z5,z6]),(0,[z1,z25,z3,z8,z5,z198]),(0,[z163,z151,z3,z8,z5,z6])],[(0,[z39,z2,z63,z8,z5,z6]),(0,[z34,z2,z3,z4,z5,z10]),(0,[z1,z3,z836,z8,z5,z6]),(0,[z1,z2,z3,z837,z5,z6]),(0,[z163,z2,z3,z350,z5,z6]),(0,[z1,z838,z2,z3,z5,z6])],[(0,[z78,z79,z50,z8,z5,z6]),(0,[z839,z1,z473,z8,z5,z6]),(0,[z34,z1,z836,z8,z5,z6]),(0,[z1,z2,z8,z5,z6,z804]),(0,[z1,z3,z478,z398,z5,z6])],[(0,[z1,z56,z3,z4,z5,z6]),(0,[z840,z1,z3,z50,z8,z5]),(0,[z841,z2,z3,z8,z5,z6])],[(0,[z39,z0,z3,z4,z5,z6]),(0,[z1,z357,z8,z5,z20,z6]),(0,[z1,z2,z3,z4,z5,z842]),(0,[z34,z2,z3,z8,z5,z17]),(0,[z1,z2,z406,z8,z5,z256])],[(0,[z843,z1,z2,z8,z5,z6]),(0,[z1,z844,z3,z8,z5,z6])],[(1,[z1,z50,z8,z172,z6]),(0,[z1,z81,z357,z8,z5,z6]),(0,[z68,z2,z3,z305,z41,z6]),(0,[z114,z2,z3,z8,z5,z813]),(0,[z1,z2,z3,z845,z5,z6])],[(0,[z179,z1,z466,z3,z5,z6]),(0,[z1,z2,z3,z350,z5,z6]),(0,[z1,z2,z3,z5,z6,z846])],[(0,[z1,z296,z3,z8,z172,z6]),(0,[z2,z3,z4,z5,z6,z475]),(0,[z658,z1,z2,z3,z75,z6]),(0,[z1,z2,z847,z8,z5,z6]),(0,[z673,z1,z2,z8,z20,z6])],[(0,[z1,z2,z3,z48,z5,z203]),(0,[z109,z1,z3,z8,z5,z6]),(0,[z1,z81,z50,z8,z20,z6]),(0,[z1,z3,z50,z8,z5,z256]),(0,[z0,z285,z1,z8,z5,z6]),(0,[z1,z3,z8,z5,z6,z358]),(0,[z848,z1,z406,z8,z5,z6])],[(0,[z1,z2,z3,z59,z5,z203]),(0,[z1,z2,z3,z8,z5,z849]),(0,[z1,z2,z3,z125,z5,z90]),(0,[z1,z2,z3,z320,z5,z6]),(0,[z1,z2,z850,z8,z5,z6]),(0,[z160,z1,z2,z3,z210,z71])],[(0,[z163,z2,z3,z8,z5,z6]),(0,[z39,z2,z720,z8,z5,z6]),(0,[z1,z2,z3,z851,z5,z6]),(0,[z1,z3,z50,z4,z5,z6]),(0,[z1,z50,z4,z5,z20,z6]),(0,[z1,z2,z3,z8,z5,z852]),(0,[z1,z2,z3,z8,z5,z853]),(0,[z1,z2,z3,z854,z5,z6]),(0,[z11,z0,z1,z3,z75,z6]),(0,[z196,z2,z3,z855,z5,z6]),(1,[z1,z3,z8,z856,z6])],[(0,[z22,z1,z3,z8,z5,z38]),(0,[z0,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z857]),(0,[z858,z2,z3,z8,z5,z6]),(0,[z1,z2,z81,z8,z5,z159]),(0,[z1,z2,z3,z8,z291,z16])],[(0,[z1,z2,z3,z207,z5,z227]),(1,[z2,z3,z8,z859,z6]),(0,[z860,z2,z3,z8,z5,z6])],[(0,[z110,z2,z3,z4,z5,z6]),(0,[z2,z3,z738,z4,z5,z6]),(0,[z1,z2,z473,z8,z5,z227]),(0,[z861,z1,z3,z8,z5,z6]),(0,[z34,z2,z3,z295,z5,z70])]],
   [[(0,[z1,z2,z3,z8,z5,z862]),(0,[z1,z2,z3,z4,z5,z112]),(0,[z381,z2,z3,z4,z5,z6]),(0,[z394,z1,z50,z8,z5,z6]),(0,[z1,z247,z3,z191,z5,z6]),(0,[z1,z2,z3,z276,z5,z150]),(1,[z1,z2,z8,z780,z6]),(0,[z1,z2,z3,z863,z5,z6])],[(0,[z0,z119,z1,z4,z5,z6]),(0,[z1,z2,z3,z864,z5,z6]),(0,[z865,z1,z3,z8,z5,z6])],[(0,[z0,z1,z3,z343,z5,z6]),(0,[z0,z1,z50,z4,z5,z6]),(0,[z1,z434,z3,z191,z5,z6]),(0,[z1,z429,z2,z8,z20,z6])],[(0,[z429,z2,z3,z15,z5,z6]),(0,[z1,z2,z866,z8,z5,z6])],[(0,[z1,z2,z3,z867,z5,z6]),(0,[z34,z2,z3,z512,z5,z6]),(0,[z189,z1,z149,z3,z5,z6]),(0,[z1,z2,z3,z5,z868,z6]),(0,[z119,z869,z1,z8,z5,z6]),(0,[z123,z1,z577,z2,z5,z6]),(0,[z870,z2,z3,z8,z5,z6]),(0,[z1,z3,z422,z300,z5,z6]),(0,[z1,z2,z3,z8,z5,z846])],[(0,[z1,z871,z3,z8,z5,z6]),(0,[z1,z2,z3,z872,z5,z6]),(0,[z873,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z874,z5,z6]),(0,[z875,z2,z3,z8,z5,z6])],[(0,[z78,z79,z357,z8,z5,z6]),(0,[z133,z2,z3,z15,z5,z6]),(0,[z19,z1,z50,z8,z20,z6]),(0,[z0,z1,z3,z8,z5,z876]),(0,[z134,z1,z348,z8,z5,z6]),(0,[z459,z1,z2,z3,z5,z153])],[(0,[z1,z132,z574,z8,z5,z6]),(0,[z1,z132,z3,z8,z5,z436]),(0,[z1,z2,z3,z877,z5,z6]),(0,[z1,z2,z3,z878,z5,z6]),(0,[z1,z879,z3,z8,z5,z6])],[(0,[z2,z3,z880,z8,z5,z6]),(0,[z1,z296,z3,z224,z5,z6]),(0,[z160,z1,z2,z3,z4,z71]),(0,[z1,z347,z3,z295,z5,z6]),(0,[z1,z95,z50,z8,z5,z6]),(0,[z205,z2,z348,z8,z5,z6]),(0,[z429,z341,z3,z8,z5,z6]),(0,[z11,z1,z2,z3,z75,z6]),(0,[z262,z1,z881,z8,z5,z6])],[(0,[z1,z882,z3,z8,z5,z6]),(0,[z128,z1,z2,z4,z5,z153]),(0,[z1,z2,z3,z8,z5,z813]),(0,[z134,z1,z3,z8,z5,z6]),(0,[z1,z43,z50,z8,z5,z6]),(0,[z1,z281,z3,z191,z5,z6]),(0,[z163,z2,z3,z883,z5,z6]),(0,[z1,z2,z8,z780,z20,z6]),(0,[z884,z2,z3,z8,z5,z6])],[(0,[z183,z2,z3,z8,z172,z6]),(0,[z9,z2,z3,z15,z135,z6])],[(0,[z205,z2,z3,z8,z5,z6]),(0,[z39,z2,z63,z8,z172,z6]),(0,[z1,z885,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z159]),(0,[z1,z132,z3,z8,z218,z6]),(0,[z886,z2,z3,z8,z5,z6]),(0,[z1,z2,z887,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z888]),(1,[z889,z2,z3,z5,z6])],[(1,[z39,z50,z4,z5,z6]),(0,[z1,z2,z3,z890,z5,z6]),(0,[z105,z2,z3,z4,z5,z6])],[],[(0,[z22,z2,z3,z4,z5,z10]),(0,[z1,z3,z50,z8,z5,z457]),(0,[z0,z869,z1,z8,z5,z6]),(0,[z891,z2,z3,z8,z5,z6]),(0,[z591,z1,z2,z3,z8,z71]),(0,[z1,z177,z3,z8,z5,z254])],[(0,[z1,z2,z3,z892,z5,z6]),(0,[z1,z3,z357,z4,z5,z6]),(0,[z9,z2,z3,z775,z5,z6]),(0,[z1,z2,z3,z883,z5,z6])]],
   [[(0,[z230,z2,z3,z4,z5,z6]),(0,[z1,z209,z3,z15,z5,z6]),(0,[z1,z2,z3,z893,z5,z6]),(0,[z1,z2,z894,z8,z5,z6]),(0,[z895,z2,z3,z8,z5,z6])],[(0,[z39,z50,z8,z4,z5,z6]),(0,[z1,z2,z896,z8,z5,z6]),(0,[z1,z3,z50,z336,z5,z6]),(0,[z24,z1,z3,z345,z5,z6]),(0,[z479,z1,z108,z8,z5,z6])],[(0,[z22,z1,z3,z8,z5,z143]),(0,[z1,z3,z897,z8,z5,z6]),(0,[z19,z1,z2,z8,z780,z6])],[(0,[z1,z3,z898,z8,z5,z6]),(0,[z1,z2,z81,z233,z5,z6]),(0,[z120,z1,z2,z8,z5,z153])],[(0,[z2,z3,z4,z5,z6,z375]),(0,[z1,z3,z193,z4,z5,z6]),(0,[z899,z1,z3,z8,z5,z6]),(0,[z2,z3,z8,z135,z859,z6]),(0,[z1,z50,z8,z5,z617,z6]),(0,[z0,z1,z680,z8,z5,z6]),(0,[z1,z3,z336,z5,z198,z6])],[(0,[z1,z194,z88,z8,z5,z6]),(0,[z2,z79,z3,z4,z5,z6]),(0,[z196,z2,z3,z4,z5,z6]),(0,[z1,z88,z8,z5,z6,z26]),(0,[z1,z900,z3,z8,z5,z6])],[(0,[z1,z2,z3,z15,z5,z12]),(0,[z53,z1,z574,z8,z122,z6]),(0,[z53,z1,z3,z8,z122,z436])],[(0,[z1,z3,z901,z8,z5,z6])],[(0,[z1,z204,z3,z4,z5,z6]),(0,[z34,z347,z3,z4,z5,z6])],[(0,[z1,z2,z3,z8,z5,z902]),(0,[z1,z2,z3,z8,z444,z40]),(0,[z1,z903,z3,z8,z5,z6]),(0,[z1,z50,z8,z5,z153,z71]),(0,[z1,z3,z191,z5,z469,z6]),(0,[z1,z2,z3,z8,z5,z904]),(0,[z464,z2,z3,z18,z5,z6]),(0,[z160,z459,z1,z2,z3,z71])],[(0,[z39,z204,z3,z4,z5,z6]),(0,[z39,z2,z63,z224,z5,z6]),(0,[z123,z1,z481,z2,z5,z6]),(0,[z1,z3,z50,z5,z6,z210]),(0,[z1,z2,z8,z5,z107,z804]),(0,[z36,z62,z3,z8,z5,z6])],[(0,[z9,z2,z3,z59,z5,z6]),(0,[z36,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z8,z5,z905]),(0,[z1,z3,z906,z8,z5,z6])],[(0,[z1,z2,z3,z8,z444,z6]),(0,[z658,z2,z3,z4,z41,z6]),(0,[z1,z907,z3,z8,z5,z6])],[(0,[z1,z2,z3,z908,z5,z6]),(0,[z241,z2,z3,z4,z5,z6]),(0,[z1,z2,z561,z8,z5,z107]),(0,[z1,z3,z8,z232,z6,z316]),(0,[z1,z2,z229,z8,z5,z256]),(0,[z1,z2,z3,z5,z846,z127])],[(0,[z1,z2,z3,z8,z5,z909]),(0,[z39,z2,z234,z8,z5,z6]),(0,[z1,z2,z3,z305,z5,z6]),(0,[z910,z1,z2,z3,z5,z6]),(0,[z1,z62,z3,z15,z5,z6]),(0,[z68,z2,z3,z8,z41,z6]),(0,[z1,z3,z50,z207,z5,z6]),(0,[z386,z2,z3,z8,z5,z10]),(0,[z1,z13,z3,z8,z5,z6]),(0,[z673,z1,z2,z3,z8,z71])],[(0,[z1,z50,z491,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z227]),(0,[z0,z1,z406,z8,z5,z6]),(0,[z109,z1,z60,z32,z5,z6]),(0,[z2,z3,z8,z5,z6,z911])]],
   [[(0,[z1,z296,z3,z8,z5,z40]),(0,[z1,z912,z3,z8,z5,z6]),(0,[z869,z1,z95,z8,z5,z6]),(0,[z87,z3,z583,z8,z5,z6]),(0,[z128,z1,z50,z8,z5,z153]),(0,[z0,z1,z574,z8,z5,z6]),(0,[z0,z1,z3,z8,z5,z436]),(0,[z1,z2,z3,z913,z5,z6]),(0,[z1,z2,z81,z8,z396,z6]),(0,[z1,z2,z3,z18,z5,z627]),(0,[z338,z2,z3,z914,z5,z6])],[(0,[z1,z2,z3,z8,z5,z915]),(0,[z916,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z75,z256])],[(0,[z338,z2,z3,z8,z5,z6]),(0,[z1,z917,z3,z8,z5,z6]),(0,[z2,z3,z461,z5,z6,z10]),(0,[z1,z3,z50,z8,z5,z918]),(0,[z1,z3,z8,z5,z6,z919]),(0,[z920,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z921,z6]),(0,[z922,z1,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z923]),(0,[z1,z3,z50,z512,z5,z6]),(0,[z1,z132,z3,z212,z5,z6]),(0,[z1,z3,z924,z8,z5,z6])],[(0,[z1,z132,z136,z8,z5,z6]),(0,[z1,z341,z3,z15,z5,z6]),(0,[z160,z0,z1,z3,z8,z71]),(0,[z196,z132,z3,z8,z5,z6]),(0,[z205,z2,z3,z253,z5,z6]),(0,[z1,z2,z3,z925,z5,z6])],[(0,[z1,z3,z926,z8,z5,z6]),(0,[z2,z3,z569,z4,z5,z10]),(0,[z1,z138,z3,z4,z5,z6]),(0,[z669,z2,z3,z8,z5,z10]),(0,[z0,z1,z3,z927,z5,z6])],[(0,[z0,z1,z3,z8,z5,z113]),(0,[z1,z2,z3,z8,z5,z928]),(0,[z929,z2,z3,z8,z5,z6]),(0,[z1,z81,z329,z8,z137,z6]),(0,[z1,z115,z478,z8,z5,z107]),(0,[z930,z164,z2,z3,z5,z6])],[(0,[z39,z2,z3,z807,z5,z6]),(0,[z404,z2,z3,z320,z5,z6]),(0,[z196,z2,z3,z931,z5,z6]),(0,[z932,z2,z3,z8,z5,z6])],[(0,[z0,z1,z3,z8,z5,z112]),(0,[z1,z2,z3,z933,z5,z6]),(0,[z1,z50,z15,z504,z5,z6]),(0,[z123,z1,z31,z177,z5,z6]),(0,[z19,z1,z2,z8,z20,z225]),(0,[z1,z2,z3,z5,z6,z934]),(0,[z479,z1,z164,z3,z5,z6])],[(0,[z1,z2,z115,z15,z5,z107]),(0,[z464,z149,z2,z3,z5,z6]),(0,[z935,z2,z3,z8,z5,z6])],[(0,[z423,z1,z3,z8,z5,z6]),(0,[z2,z3,z4,z5,z585,z6])],[(0,[z0,z405,z3,z4,z5,z6]),(0,[z429,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z15,z5,z313]),(0,[z1,z936,z3,z8,z5,z6]),(0,[z799,z2,z115,z3,z5,z6])],[(0,[z1,z604,z3,z8,z5,z198]),(0,[z1,z2,z516,z15,z5,z6]),(0,[z1,z2,z233,z5,z20,z6]),(0,[z1,z2,z8,z5,z780,z6])],[(0,[z34,z2,z3,z828,z5,z6]),(0,[z0,z1,z65,z8,z5,z6]),(0,[z324,z2,z3,z8,z5,z70]),(0,[z1,z2,z3,z937,z5,z6]),(0,[z1,z2,z3,z5,z451,z127])],[(0,[z1,z2,z3,z8,z5,z938]),(0,[z0,z14,z1,z8,z5,z6]),(0,[z133,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z18,z5,z293])],[(0,[z1,z939,z3,z8,z5,z6]),(0,[z1,z2,z3,z940,z5,z6]),(0,[z1,z2,z51,z452,z5,z6]),(0,[z1,z574,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z941]),(0,[z80,z1,z2,z3,z5,z127]),(0,[z226,z2,z3,z219,z5,z6])]],
   [[(0,[z1,z2,z3,z942,z5,z6]),(0,[z1,z2,z3,z8,z943,z6]),(0,[z1,z2,z50,z8,z5,z90]),(0,[z1,z65,z50,z8,z5,z6]),(0,[z944,z1,z3,z8,z5,z6]),(0,[z1,z2,z516,z186,z5,z6]),(0,[z160,z1,z2,z3,z8,z71])],[(0,[z1,z2,z3,z709,z5,z6]),(0,[z46,z3,z15,z23,z5,z6]),(0,[z1,z31,z2,z3,z5,z313]),(0,[z123,z31,z110,z2,z5,z6])],[(0,[z0,z1,z310,z8,z5,z6]),(0,[z1,z2,z945,z4,z5,z6]),(0,[z1,z286,z3,z8,z5,z6]),(0,[z1,z50,z8,z5,z526,z6]),(0,[z110,z2,z3,z5,z150,z6]),(0,[z459,z1,z3,z5,z6,z358])],[(0,[z34,z0,z3,z4,z5,z6])],[(0,[z1,z25,z3,z8,z5,z562])],[(0,[z481,z2,z79,z4,z5,z6]),(0,[z1,z2,z836,z8,z5,z6]),(0,[z1,z353,z3,z8,z5,z198])],[(0,[z1,z946,z3,z8,z5,z6]),(0,[z183,z2,z3,z738,z5,z6]),(0,[z1,z50,z8,z5,z6,z537]),(0,[z947,z2,z3,z8,z5,z6]),(0,[z128,z1,z2,z8,z5,z804]),(0,[z1,z62,z3,z5,z150,z6]),(0,[z1,z2,z3,z300,z684,z6])],[(0,[z119,z1,z2,z8,z5,z90]),(0,[z9,z3,z50,z4,z5,z6])],[(0,[z1,z136,z50,z8,z5,z6]),(0,[z1,z2,z3,z15,z5,z90]),(0,[z39,z183,z50,z8,z5,z6]),(0,[z1,z209,z3,z4,z5,z6]),(0,[z244,z1,z2,z8,z5,z153]),(0,[z1,z2,z3,z8,z5,z948]),(0,[z1,z2,z115,z398,z5,z107])],[(0,[z1,z3,z949,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z950])],[(0,[z1,z3,z50,z21,z5,z6]),(0,[z87,z3,z50,z4,z5,z6]),(0,[z1,z151,z3,z8,z5,z6]),(0,[z674,z1,z2,z3,z5,z127])],[(0,[z1,z2,z3,z951,z5,z6]),(0,[z1,z952,z3,z8,z5,z6]),(0,[z2,z3,z4,z41,z20,z6]),(0,[z302,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z953,z5,z6])],[(0,[z79,z3,z50,z4,z5,z6]),(0,[z0,z79,z3,z4,z5,z6]),(0,[z2,z81,z79,z4,z5,z6]),(0,[z1,z50,z8,z5,z703,z6]),(0,[z82,z1,z50,z8,z5,z6]),(0,[z0,z1,z3,z212,z5,z6]),(0,[z1,z3,z8,z5,z948,z26])],[(0,[z0,z1,z136,z8,z5,z6]),(0,[z1,z2,z954,z15,z5,z6]),(0,[z168,z2,z3,z295,z5,z6])],[(0,[z1,z2,z3,z4,z5,z12]),(0,[z1,z3,z768,z8,z5,z6]),(0,[z338,z13,z3,z8,z5,z6])],[(0,[z459,z1,z3,z50,z5,z6]),(0,[z955,z2,z3,z8,z5,z6]),(0,[z492,z1,z31,z2,z5,z6])]],
   [[(0,[z2,z3,z4,z5,z486,z6]),(0,[z1,z956,z3,z8,z5,z6]),(0,[z957,z1,z3,z8,z5,z6]),(0,[z1,z3,z958,z8,z5,z6]),(0,[z262,z1,z3,z8,z5,z6])],[(0,[z39,z3,z50,z4,z5,z6]),(0,[z3,z360,z50,z4,z5,z6]),(0,[z0,z1,z3,z18,z5,z150]),(0,[z36,z2,z3,z8,z5,z256])],[(0,[z1,z2,z3,z48,z5,z112]),(0,[z1,z2,z3,z8,z5,z40]),(0,[z2,z3,z4,z5,z41,z6]),(0,[z355,z2,z3,z4,z5,z6]),(0,[z1,z2,z348,z8,z5,z6]),(0,[z959,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z960,z5,z6]),(0,[z80,z1,z2,z3,z5,z102])],[(0,[z1,z2,z3,z59,z5,z112]),(0,[z36,z2,z3,z4,z5,z6]),(0,[z68,z2,z65,z8,z41,z6]),(0,[z1,z961,z3,z50,z5,z6]),(0,[z1,z2,z3,z914,z5,z6])],[(0,[z46,z3,z23,z4,z5,z6]),(0,[z1,z2,z3,z224,z444,z6]),(0,[z1,z164,z115,z50,z5,z6]),(0,[z1,z776,z3,z8,z5,z6]),(0,[z1,z62,z3,z8,z5,z256])],[(0,[z1,z2,z3,z8,z5,z6])],[(0,[z1,z62,z3,z4,z5,z6]),(0,[z1,z605,z3,z211,z5,z6]),(0,[z372,z2,z3,z8,z41,z6]),(0,[z1,z2,z3,z962,z5,z6]),(0,[z1,z3,z963,z8,z5,z6]),(0,[z179,z1,z3,z345,z5,z6])],[(0,[z1,z2,z3,z738,z5,z6]),(0,[z0,z1,z3,z8,z5,z227]),(0,[z964,z1,z3,z8,z5,z6]),(0,[z507,z1,z50,z8,z5,z6]),(0,[z0,z1,z81,z8,z137,z6]),(0,[z0,z1,z229,z8,z5,z6])],[(0,[z39,z0,z63,z8,z5,z6]),(0,[z965,z1,z3,z4,z5,z6]),(0,[z114,z2,z3,z8,z5,z10])],[(0,[z2,z3,z4,z5,z641,z6])],[(0,[z2,z3,z4,z5,z6,z502]),(0,[z1,z2,z966,z8,z5,z6]),(0,[z1,z3,z8,z232,z856,z6])],[(0,[z609,z2,z3,z4,z5,z6]),(0,[z205,z2,z3,z960,z5,z6])],[(0,[z1,z341,z3,z4,z5,z6]),(0,[z701,z2,z3,z4,z5,z6]),(0,[z1,z3,z50,z121,z5,z6]),(0,[z1,z50,z8,z5,z6,z83])],[(0,[z1,z51,z50,z8,z5,z6]),(0,[z652,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z8,z5,z967]),(0,[z1,z2,z3,z968,z5,z6]),(0,[z969,z2,z3,z8,z5,z6])],[(0,[z93,z194,z3,z8,z5,z6]),(0,[z1,z450,z3,z15,z5,z6]),(0,[z970,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z971]),(0,[z1,z2,z3,z5,z6,z972])],[(0,[z1,z2,z3,z973,z5,z6]),(0,[z79,z3,z357,z4,z5,z6]),(0,[z0,z1,z382,z8,z5,z6])]],
   [[(0,[z1,z3,z974,z8,z5,z6]),(0,[z1,z2,z65,z8,z41,z6]),(0,[z1,z3,z50,z8,z5,z975]),(0,[z1,z2,z976,z8,z5,z6]),(0,[z1,z2,z273,z219,z5,z6]),(0,[z1,z2,z881,z8,z5,z6])],[(0,[z1,z2,z115,z4,z5,z107]),(0,[z1,z77,z50,z8,z5,z6]),(0,[z0,z1,z273,z8,z5,z6]),(0,[z1,z2,z3,z977,z5,z6])],[(0,[z1,z2,z3,z978,z5,z6]),(0,[z979,z1,z3,z8,z5,z6]),(0,[z1,z776,z3,z191,z5,z6]),(0,[z1,z31,z2,z185,z5,z6]),(0,[z1,z209,z115,z8,z5,z6])],[(0,[z1,z2,z3,z4,z5,z313]),(0,[z1,z3,z422,z5,z75,z6])],[(0,[z1,z2,z3,z980,z5,z6]),(0,[z1,z2,z516,z4,z5,z6]),(0,[z1,z2,z8,z5,z981,z6]),(0,[z1,z50,z8,z5,z611,z6]),(0,[z1,z3,z50,z8,z5,z711])],[(0,[z1,z2,z3,z982,z5,z6]),(0,[z3,z880,z23,z8,z5,z6]),(0,[z262,z1,z3,z8,z5,z10]),(0,[z22,z1,z3,z8,z5,z948]),(0,[z160,z338,z2,z3,z8,z71]),(0,[z889,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z983]),(0,[z495,z1,z2,z8,z20,z6]),(0,[z1,z450,z473,z8,z5,z6]),(0,[z1,z216,z3,z427,z5,z6]),(0,[z1,z3,z984,z8,z5,z6]),(0,[z128,z1,z138,z8,z5,z153]),(0,[z1,z3,z985,z8,z5,z6])],[(0,[z1,z2,z3,z986,z5,z6]),(0,[z1,z987,z3,z8,z5,z6])],[(0,[z1,z2,z88,z15,z5,z6]),(0,[z1,z988,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z254])],[(0,[z1,z2,z3,z989,z5,z6]),(0,[z1,z2,z3,z15,z5,z457]),(0,[z9,z2,z3,z305,z5,z6]),(0,[z9,z2,z3,z512,z135,z6]),(0,[z1,z115,z50,z8,z5,z107]),(0,[z1,z3,z50,z5,z6,z722])],[(0,[z1,z2,z3,z233,z5,z225]),(0,[z11,z464,z2,z3,z5,z6])],[(0,[z1,z2,z3,z8,z172,z40]),(0,[z1,z2,z3,z990,z5,z6]),(0,[z1,z50,z15,z5,z6,z153]),(0,[z0,z1,z413,z8,z5,z6]),(0,[z1,z2,z348,z253,z5,z6]),(0,[z1,z2,z991,z8,z5,z6]),(0,[z80,z1,z2,z3,z5,z846])],[(0,[z1,z992,z2,z3,z5,z6]),(0,[z1,z2,z3,z993,z5,z6])],[(0,[z1,z2,z3,z994,z5,z6]),(0,[z995,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z797,z5,z6])],[(0,[z1,z2,z3,z8,z172,z6]),(0,[z1,z2,z3,z8,z5,z803]),(0,[z1,z2,z3,z253,z5,z6]),(0,[z92,z1,z3,z8,z5,z6]),(0,[z304,z1,z2,z3,z75,z6]),(0,[z1,z3,z8,z5,z6,z996]),(0,[z1,z56,z3,z219,z5,z6])],[(0,[z2,z3,z4,z5,z548,z6]),(0,[z594,z1,z2,z3,z5,z127]),(0,[z1,z3,z212,z5,z122,z6]),(0,[z1,z997,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z203]),(0,[z1,z2,z3,z4,z5,z90]),(0,[z1,z2,z998,z8,z5,z6]),(0,[z1,z999,z3,z8,z5,z6]),(0,[z1000,z1,z3,z8,z5,z6]),(0,[z429,z2,z81,z8,z5,z6])],[(0,[z1,z3,z50,z47,z5,z6]),(0,[z161,z1,z50,z8,z5,z6]),(0,[z1,z1001,z3,z8,z5,z6])],[(0,[z408,z1,z136,z8,z5,z6]),(0,[z1,z1002,z2,z3,z5,z6]),(0,[z1,z3,z8,z5,z6,z1003])],[(0,[z1,z1004,z3,z8,z5,z6])],[(0,[z0,z420,z1,z8,z5,z6]),(0,[z1,z2,z3,z1005,z5,z6]),(0,[z1,z799,z2,z3,z5,z6])],[(0,[z2,z610,z3,z4,z5,z6]),(0,[z1,z2,z3,z461,z5,z6]),(0,[z536,z1,z2,z8,z20,z6]),(0,[z1006,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z1007,z5,z6]),(0,[z1,z2,z3,z8,z1008,z6]),(0,[z11,z1,z2,z3,z1009,z6]),(0,[z1,z2,z3,z8,z1009,z6])],[(0,[z1,z3,z4,z5,z6,z358]),(0,[z557,z2,z3,z8,z5,z10]),(0,[z1,z3,z50,z219,z5,z6]),(0,[z0,z1,z3,z8,z5,z12]),(0,[z205,z2,z574,z8,z5,z6]),(0,[z205,z2,z3,z8,z5,z436])],[(0,[z1,z2,z3,z4,z5,z1010]),(0,[z1,z2,z735,z8,z5,z6]),(0,[z1,z177,z8,z5,z20,z6])],[(0,[z1,z2,z79,z8,z172,z6]),(0,[z114,z2,z3,z461,z5,z10])],[(0,[z0,z3,z4,z5,z41,z6]),(0,[z424,z1,z50,z8,z5,z6]),(0,[z1,z88,z50,z8,z5,z6]),(0,[z1,z3,z191,z5,z498,z6]),(0,[z1,z1011,z2,z3,z8,z5])],[(0,[z1,z2,z3,z224,z5,z40]),(0,[z1,z2,z473,z15,z5,z6]),(0,[z1,z3,z50,z755,z5,z6]),(0,[z1,z2,z60,z32,z5,z6])],[(0,[z395,z2,z3,z4,z5,z6]),(0,[z464,z3,z50,z8,z5,z6]),(0,[z1,z185,z50,z8,z5,z6]),(0,[z464,z2,z3,z8,z5,z153]),(0,[z160,z1,z2,z273,z8,z71])],[(0,[z1,z3,z1012,z8,z5,z6]),(0,[z479,z1,z3,z8,z5,z6]),(0,[z509,z1,z50,z8,z5,z6]),(0,[z1,z2,z3,z1013,z5,z6]),(0,[z1,z2,z3,z8,z5,z804])],[(0,[z1,z2,z3,z224,z5,z6]),(0,[z39,z204,z63,z8,z5,z6]),(0,[z226,z2,z3,z8,z5,z6]),(0,[z1,z2,z1014,z8,z5,z6]),(0,[z1015,z1,z3,z8,z5,z6]),(0,[z1,z2,z72,z32,z5,z6]),(0,[z1016,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z1017,z5,z6]),(0,[z467,z2,z3,z15,z5,z6]),(0,[z2,z3,z8,z5,z156,z10]),(0,[z1018,z2,z3,z8,z5,z6]),(0,[z1,z3,z1019,z8,z5,z6])],[(0,[z1,z2,z3,z1020,z5,z6]),(0,[z1,z3,z50,z295,z5,z6]),(0,[z1,z2,z3,z1021,z5,z6]),(0,[z1,z2,z3,z8,z6,z1022]),(0,[z889,z2,z3,z5,z6,z71])]],
   [[(0,[z536,z2,z3,z4,z5,z6]),(0,[z1,z1023,z2,z3,z5,z6]),(0,[z86,z2,z3,z8,z5,z10])],[(0,[z404,z2,z3,z8,z5,z6]),(0,[z1,z25,z88,z8,z5,z6])],[(0,[z2,z79,z720,z8,z5,z6]),(0,[z1,z2,z3,z1024,z5,z6])],[(0,[z1,z2,z3,z8,z1025,z6]),(0,[z0,z1,z3,z186,z5,z6]),(0,[z1026,z2,z3,z8,z5,z6]),(0,[z1027,z1,z3,z8,z5,z6]),(0,[z1028,z1,z3,z8,z5,z6])],[(0,[z1,z1029,z3,z8,z5,z6]),(0,[z68,z0,z3,z8,z41,z6]),(0,[z869,z1,z50,z8,z5,z6]),(0,[z223,z3,z360,z8,z5,z6]),(0,[z279,z1,z50,z8,z20,z6]),(0,[z930,z2,z3,z8,z5,z6]),(0,[z1030,z1,z3,z8,z5,z6])],[(0,[z0,z1,z3,z125,z5,z6])],[(0,[z2,z3,z106,z4,z5,z6]),(0,[z1,z450,z3,z4,z5,z6]),(0,[z3,z50,z8,z5,z1031,z6]),(0,[z0,z1,z3,z8,z5,z159]),(0,[z36,z2,z3,z5,z150,z6])],[(0,[z1,z2,z3,z8,z5,z1032]),(0,[z1,z2,z3,z1033,z5,z6]),(0,[z1,z1034,z3,z8,z5,z6]),(0,[z34,z2,z3,z8,z5,z70]),(0,[z1,z3,z8,z5,z198,z948]),(0,[z1,z2,z3,z1035,z5,z6]),(0,[z459,z1,z2,z3,z5,z256])],[(0,[z1,z2,z3,z1036,z5,z6]),(0,[z1,z3,z50,z8,z5,z225]),(0,[z0,z429,z3,z8,z5,z6]),(0,[z1,z2,z3,z1037,z5,z6]),(0,[z1,z2,z3,z1038,z5,z6])],[(0,[z1,z3,z50,z782,z5,z6])],[(0,[z2,z3,z8,z5,z41,z113]),(0,[z1,z2,z3,z5,z6,z1039]),(0,[z1,z229,z50,z8,z5,z6]),(0,[z22,z1,z574,z8,z5,z6]),(0,[z22,z1,z3,z8,z5,z436])],[(0,[z1,z3,z23,z8,z5,z203]),(0,[z78,z2,z79,z8,z5,z6]),(0,[z1,z2,z81,z8,z666,z6])],[(0,[z2,z3,z8,z5,z41,z112]),(0,[z1040,z1,z2,z15,z5,z6]),(0,[z1,z1041,z3,z8,z5,z6]),(0,[z80,z36,z2,z3,z5,z6])],[(0,[z123,z1,z31,z50,z5,z6]),(0,[z791,z3,z50,z8,z5,z6])],[(0,[z49,z3,z50,z4,z5,z6]),(0,[z9,z2,z3,z8,z384,z6])],[(0,[z39,z354,z2,z8,z5,z6]),(0,[z34,z3,z50,z4,z5,z6]),(0,[z1,z2,z3,z305,z5,z113]),(0,[z68,z2,z3,z8,z41,z113])]],
   [[(0,[z1,z347,z3,z8,z5,z6]),(0,[z1,z2,z88,z4,z5,z6]),(0,[z1,z2,z3,z1042,z5,z6])],[(0,[z1,z3,z50,z48,z5,z6]),(0,[z39,z1,z50,z8,z444,z6]),(0,[z220,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z457]),(0,[z1,z2,z1043,z8,z5,z6]),(0,[z123,z110,z2,z3,z5,z6])],[(0,[z46,z3,z23,z21,z5,z6]),(0,[z1,z3,z50,z59,z5,z6]),(0,[z1,z2,z3,z343,z5,z6]),(0,[z1,z1044,z3,z8,z5,z6])],[(0,[z1045,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1046])],[(0,[z39,z2,z50,z4,z5,z6]),(0,[z1,z2,z3,z1047,z5,z6]),(0,[z1,z132,z3,z15,z232,z6]),(0,[z1,z1048,z2,z3,z5,z6])],[(0,[z1,z1049,z3,z8,z5,z6]),(0,[z1050,z1,z3,z8,z5,z6]),(0,[z1051,z1,z3,z15,z5,z6]),(0,[z1,z2,z3,z1052,z5,z6]),(0,[z1,z2,z3,z8,z859,z6]),(0,[z1,z3,z1053,z8,z5,z6]),(0,[z1,z3,z50,z8,z5,z811]),(0,[z91,z1,z2,z3,z5,z127])],[(0,[z1,z2,z3,z8,z5,z1054]),(0,[z1,z2,z3,z224,z172,z6]),(0,[z1,z2,z65,z305,z5,z6]),(0,[z2,z3,z512,z5,z6,z10]),(0,[z1,z3,z50,z814,z5,z6]),(0,[z1,z2,z3,z8,z5,z876]),(0,[z1,z88,z8,z232,z5,z6]),(0,[z123,z1,z31,z2,z5,z6]),(0,[z80,z110,z2,z3,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1055]),(0,[z1,z3,z1056,z8,z5,z6]),(0,[z500,z1,z50,z8,z5,z6]),(0,[z1,z481,z50,z4,z5,z6]),(0,[z80,z464,z2,z3,z5,z127]),(0,[z1,z13,z3,z8,z5,z71])],[(0,[z1,z1057,z2,z3,z5,z6]),(0,[z235,z194,z3,z8,z5,z6]),(0,[z2,z3,z4,z5,z178,z6]),(0,[z1,z2,z3,z15,z5,z256]),(0,[z1,z286,z3,z8,z5,z254])],[(0,[z1,z3,z15,z1058,z5,z6]),(0,[z1059,z1,z3,z8,z5,z6]),(0,[z1,z141,z3,z191,z5,z6]),(0,[z0,z80,z1,z3,z5,z127]),(0,[z226,z13,z3,z8,z5,z6]),(0,[z1060,z459,z2,z3,z5,z6])],[(0,[z1,z1061,z2,z3,z5,z6]),(0,[z363,z194,z3,z8,z5,z6]),(0,[z78,z2,z3,z8,z172,z6]),(0,[z1,z2,z3,z1062,z5,z6]),(0,[z19,z163,z2,z8,z20,z6])],[(0,[z1,z2,z3,z8,z5,z1063]),(0,[z19,z0,z1,z8,z20,z6]),(0,[z1,z2,z3,z8,z5,z1064]),(0,[z22,z1,z3,z8,z5,z474]),(0,[z134,z1,z81,z8,z137,z6]),(0,[z1,z2,z81,z398,z5,z6]),(0,[z1065,z1,z3,z8,z5,z6])],[(0,[z1066,z1,z3,z8,z5,z6]),(0,[z34,z2,z3,z8,z5,z813]),(0,[z80,z1,z50,z8,z5,z153]),(0,[z0,z1,z3,z233,z5,z6]),(0,[z1067,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z1068,z5,z6]),(0,[z1,z1069,z3,z8,z5,z6]),(0,[z19,z1,z2,z350,z20,z6])],[],[(0,[z85,z2,z3,z4,z5,z6]),(0,[z22,z1,z3,z8,z5,z326]),(0,[z1,z379,z3,z8,z5,z6]),(0,[z1070,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z296,z3,z125,z5,z6]),(0,[z1,z1071,z3,z8,z5,z6]),(0,[z1,z167,z3,z15,z5,z6]),(0,[z1,z180,z3,z305,z5,z6]),(0,[z68,z180,z3,z8,z41,z6]),(0,[z1,z366,z50,z8,z5,z6]),(0,[z1,z3,z50,z8,z5,z830]),(0,[z1,z1072,z3,z8,z5,z6])],[(0,[z78,z1,z50,z8,z5,z6]),(0,[z263,z1,z2,z8,z20,z6]),(0,[z531,z2,z3,z4,z5,z6]),(0,[z1,z1073,z3,z4,z5,z6]),(0,[z1,z115,z50,z8,z5,z6]),(0,[z279,z1,z3,z8,z122,z6]),(0,[z1,z421,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z1074]),(0,[z1,z2,z3,z1075,z5,z6]),(0,[z429,z2,z3,z8,z137,z6])],[(0,[z1,z2,z473,z4,z5,z6]),(0,[z1,z3,z1076,z8,z5,z6]),(0,[z1,z3,z8,z5,z198,z237]),(0,[z22,z1,z88,z8,z5,z26]),(1,[z1,z2,z3,z5,z846]),(0,[z1,z889,z2,z3,z5,z6])],[(0,[z1,z2,z1077,z8,z5,z6]),(0,[z2,z3,z4,z5,z6,z90]),(0,[z1,z2,z3,z1078,z5,z6]),(0,[z1,z2,z3,z8,z5,z1079])],[(0,[z1,z2,z3,z1080,z5,z6]),(0,[z53,z205,z3,z8,z122,z6]),(0,[z1,z2,z1081,z8,z5,z6]),(0,[z160,z1,z13,z3,z8,z71])],[],[(0,[z335,z2,z3,z8,z41,z6]),(0,[z1,z598,z50,z8,z5,z6]),(0,[z1,z2,z3,z1082,z5,z6]),(0,[z1,z1083,z3,z4,z5,z6]),(0,[z1,z2,z3,z336,z5,z457]),(0,[z22,z1,z3,z212,z5,z6]),(0,[z1,z1084,z3,z8,z5,z6]),(1,[z1,z801,z8,z5,z6])],[(0,[z22,z1,z136,z8,z5,z6]),(0,[z1,z473,z50,z8,z5,z6]),(0,[z1,z25,z3,z8,z5,z328]),(0,[z1,z2,z3,z8,z463,z16]),(0,[z1,z2,z3,z18,z5,z846])],[(0,[z1,z450,z3,z207,z5,z6]),(0,[z1,z167,z3,z376,z5,z6]),(0,[z1,z1085,z2,z60,z5,z6]),(0,[z1,z2,z3,z1009,z75,z6]),(0,[z1,z1086,z3,z8,z5,z6]),(0,[z1,z2,z3,z1087,z5,z6])],[(0,[z1,z2,z3,z8,z5,z758]),(0,[z1,z50,z8,z5,z126,z6]),(0,[z1,z3,z8,z5,z1088,z6]),(0,[z1,z2,z3,z1089,z5,z6]),(0,[z1,z164,z2,z3,z5,z153])],[(0,[z658,z1,z2,z3,z494,z6]),(0,[z381,z2,z3,z8,z5,z70]),(0,[z1,z3,z50,z350,z5,z6]),(0,[z1,z3,z1090,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1091]),(0,[z1,z2,z1092,z8,z5,z6]),(0,[z1,z1093,z2,z3,z5,z6]),(0,[z262,z1,z3,z8,z5,z436]),(0,[z1,z2,z3,z1094,z5,z6])],[(0,[z2,z3,z4,z5,z239,z6]),(0,[z22,z1,z3,z15,z5,z26]),(0,[z1,z50,z8,z5,z6,z330]),(0,[z1,z3,z8,z5,z198,z436]),(0,[z1,z2,z1095,z8,z5,z6]),(0,[z459,z889,z2,z3,z5,z6])],[(0,[z1096,z1,z2,z8,z5,z6]),(0,[z1,z3,z50,z320,z5,z6]),(0,[z1097,z1,z3,z8,z5,z6]),(0,[z1,z149,z332,z3,z5,z6]),(0,[z1,z2,z348,z8,z5,z436]),(0,[z1,z3,z8,z5,z6,z1098])],[(0,[z87,z3,z23,z8,z5,z6]),(0,[z1,z50,z15,z5,z20,z6]),(0,[z163,z3,z50,z8,z5,z6]),(0,[z1,z516,z958,z8,z5,z6])],[(0,[z1,z3,z50,z8,z5,z857]),(0,[z1,z2,z406,z8,z5,z6]),(0,[z1,z1099,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z1100,z5,z6]),(0,[z1,z2,z3,z305,z5,z227]),(0,[z68,z2,z3,z8,z41,z227]),(0,[z1101,z1,z2,z8,z5,z6]),(0,[z1,z2,z574,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z436]),(0,[z1,z2,z3,z5,z150,z256]),(0,[z1,z2,z3,z5,z150,z257])],[(0,[z183,z2,z3,z125,z5,z6]),(0,[z423,z79,z3,z4,z5,z6]),(0,[z1,z3,z1102,z8,z5,z6])],[(0,[z39,z2,z63,z125,z5,z6]),(0,[z1103,z2,z3,z8,z5,z6])],[(0,[z1,z603,z50,z8,z5,z6])],[(0,[z78,z1,z357,z8,z5,z6]),(0,[z1104,z1,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1105]),(0,[z39,z2,z3,z4,z5,z90]),(0,[z2,z51,z79,z4,z5,z6]),(0,[z1,z50,z8,z5,z173,z6]),(0,[z1,z2,z3,z927,z5,z6])],[(0,[z1,z2,z3,z8,z5,z113]),(0,[z1,z3,z50,z5,z868,z6]),(0,[z1,z151,z8,z5,z20,z6]),(0,[z459,z1,z2,z3,z5,z107])],[(0,[z1,z2,z3,z1106,z5,z6]),(0,[z39,z1,z50,z8,z5,z40]),(0,[z1,z2,z60,z504,z5,z6]),(0,[z429,z2,z3,z8,z5,z225]),(0,[z1,z2,z3,z1107,z5,z6])],[(0,[z1,z2,z3,z8,z5,z112]),(0,[z53,z1,z3,z15,z122,z6]),(0,[z1,z2,z3,z8,z5,z1108]),(0,[z1,z151,z3,z8,z5,z159]),(0,[z1,z1109,z3,z8,z5,z6])],[(0,[z46,z3,z23,z47,z5,z6]),(0,[z1,z2,z3,z350,z5,z159])],[(0,[z39,z1,z50,z8,z5,z6]),(0,[z1,z2,z3,z1110,z5,z6]),(0,[z843,z1,z167,z8,z5,z6]),(0,[z0,z1,z50,z8,z5,z6]),(0,[z1111,z2,z3,z8,z5,z6]),(0,[z1,z13,z273,z8,z5,z6])],[(0,[z1,z2,z1112,z8,z5,z6]),(0,[z1,z25,z3,z212,z5,z198])],[(0,[z93,z194,z3,z8,z5,z203]),(0,[z1,z132,z3,z4,z232,z6]),(0,[z1,z2,z3,z1113,z5,z6]),(0,[z1,z1114,z3,z8,z5,z6])],[(0,[z1,z2,z65,z8,z5,z6]),(0,[z1,z2,z81,z8,z288,z6]),(0,[z1,z2,z3,z15,z5,z740]),(0,[z205,z3,z50,z8,z5,z6]),(0,[z1,z2,z3,z1115,z5,z6]),(0,[z429,z2,z3,z793,z5,z6]),(0,[z163,z2,z3,z8,z5,z159]),(0,[z1116,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z1117,z5,z6]),(0,[z2,z3,z295,z4,z5,z6]),(0,[z1,z2,z3,z1118,z5,z6]),(0,[z338,z2,z273,z8,z5,z6])],[(0,[z0,z78,z79,z8,z5,z6]),(0,[z1,z132,z3,z8,z856,z6]),(0,[z1,z3,z18,z422,z5,z150])]],
   [[(0,[z544,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z256]),(0,[z1,z2,z1119,z8,z5,z6]),(0,[z1,z2,z387,z8,z5,z107])],[(0,[z1,z177,z3,z8,z5,z313]),(0,[z128,z1,z2,z8,z5,z153]),(0,[z1,z2,z1120,z8,z5,z6])],[(0,[z0,z1,z3,z352,z5,z6]),(0,[z0,z1,z3,z15,z5,z6]),(0,[z1,z752,z3,z8,z5,z6]),(0,[z597,z2,z3,z15,z5,z6]),(0,[z34,z347,z3,z8,z5,z70]),(0,[z1,z527,z50,z8,z5,z6]),(0,[z1,z3,z50,z893,z5,z6]),(0,[z1,z1121,z3,z8,z5,z6])],[(0,[z509,z194,z3,z8,z5,z6])],[(0,[z39,z1,z1122,z8,z5,z6]),(0,[z1,z2,z3,z1123,z5,z6]),(0,[z1,z2,z473,z207,z5,z6]),(0,[z557,z1,z50,z8,z5,z6]),(0,[z1,z3,z478,z8,z5,z6])],[(0,[z168,z2,z3,z8,z5,z6])],[(0,[z1,z1124,z3,z8,z5,z6]),(0,[z1,z1125,z3,z4,z5,z6]),(0,[z464,z2,z3,z15,z5,z6]),(0,[z2,z3,z8,z5,z859,z6])],[(0,[z1,z180,z3,z8,z5,z6]),(0,[z1,z2,z1126,z8,z5,z6]),(0,[z1,z216,z3,z211,z5,z6]),(0,[z1,z595,z50,z8,z5,z6]),(0,[z1,z1127,z3,z8,z5,z6])],[(0,[z2,z3,z4,z5,z172,z6]),(0,[z78,z2,z79,z343,z5,z6]),(0,[z1,z2,z3,z1128,z5,z6]),(0,[z1,z167,z3,z4,z5,z6]),(0,[z1,z574,z8,z5,z122,z6]),(0,[z1,z273,z796,z8,z5,z6])],[(0,[z46,z3,z880,z8,z5,z6]),(0,[z179,z1,z88,z8,z5,z6]),(0,[z1,z2,z574,z253,z5,z6]),(0,[z1,z2,z3,z253,z5,z436])],[(0,[z1,z2,z1129,z8,z5,z6]),(0,[z2,z3,z8,z859,z41,z6]),(0,[z1,z3,z1130,z8,z5,z6]),(0,[z0,z1,z3,z376,z5,z6]),(0,[z196,z2,z348,z8,z5,z6])],[(0,[z839,z1,z3,z8,z5,z6]),(0,[z68,z2,z3,z8,z859,z6]),(0,[z9,z347,z3,z8,z5,z6]),(0,[z404,z379,z3,z8,z5,z6]),(0,[z1,z2,z1131,z8,z5,z6])],[(0,[z1132,z1,z2,z3,z5,z6]),(0,[z1,z1133,z3,z8,z5,z6]),(0,[z1,z3,z193,z8,z5,z6]),(0,[z0,z1,z115,z8,z5,z107]),(0,[z1,z2,z3,z212,z5,z6]),(0,[z1,z2,z1134,z8,z5,z6]),(0,[z464,z31,z2,z3,z5,z6]),(0,[z338,z56,z3,z8,z5,z6]),(0,[z1060,z2,z3,z8,z5,z6])],[(0,[z1,z2,z136,z8,z5,z6]),(0,[z196,z2,z3,z8,z5,z6]),(0,[z39,z1,z357,z8,z5,z6]),(0,[z100,z1,z3,z8,z122,z6]),(0,[z1,z1135,z3,z8,z5,z6])],[(0,[z1,z3,z50,z8,z444,z6]),(0,[z0,z1,z3,z8,z5,z313]),(0,[z1,z1085,z2,z3,z5,z6]),(0,[z1,z151,z3,z233,z5,z6])],[(0,[z0,z123,z1,z31,z5,z6]),(0,[z0,z1,z516,z8,z5,z6])]],
   [[(0,[z1,z204,z3,z8,z5,z6]),(0,[z1,z2,z4,z5,z981,z6]),(0,[z1,z3,z50,z305,z5,z6]),(0,[z68,z3,z50,z8,z41,z6]),(0,[z9,z2,z3,z8,z859,z6]),(0,[z1,z3,z50,z8,z5,z909]),(0,[z189,z1,z441,z3,z5,z6]),(0,[z1,z2,z3,z1136,z5,z6]),(0,[z160,z1,z2,z3,z8,z1022])],[(0,[z1,z136,z8,z5,z122,z6]),(0,[z2,z3,z15,z411,z5,z6]),(0,[z1137,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z1138,z5,z6]),(0,[z1,z2,z3,z18,z5,z150])],[(0,[z0,z128,z1,z8,z5,z153])],[(0,[z39,z1,z50,z8,z172,z6]),(0,[z536,z2,z63,z8,z5,z6]),(0,[z1,z2,z1139,z4,z5,z6]),(0,[z2,z3,z15,z738,z5,z6]),(0,[z1,z779,z3,z15,z5,z6]),(0,[z1,z2,z3,z15,z5,z225]),(0,[z2,z3,z8,z5,z790,z6]),(1,[z1,z1085,z2,z5,z6]),(0,[z163,z2,z3,z233,z5,z6]),(0,[z464,z2,z3,z139,z5,z6])],[(0,[z255,z2,z79,z8,z5,z6]),(0,[z22,z1,z3,z4,z5,z26]),(0,[z1140,z1,z3,z8,z5,z6]),(0,[z338,z3,z50,z8,z5,z6]),(0,[z1,z2,z308,z32,z5,z6])],[(0,[z323,z2,z3,z4,z5,z6]),(0,[z1,z579,z50,z8,z5,z6]),(0,[z1,z1141,z3,z8,z5,z6])],[(0,[z93,z194,z136,z8,z5,z6]),(0,[z14,z1,z2,z15,z5,z6]),(0,[z0,z1,z3,z1142,z5,z6])],[(0,[z46,z1,z136,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1143]),(0,[z1,z2,z710,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z227]),(0,[z110,z2,z60,z3,z5,z6]),(0,[z1,z2,z229,z8,z5,z6]),(0,[z1,z2,z81,z8,z137,z6])],[(0,[z1,z2,z3,z1144,z5,z6]),(0,[z1,z341,z3,z8,z5,z225]),(0,[z1,z2,z3,z1145,z5,z6])],[(0,[z3,z23,z8,z5,z342,z6]),(0,[z1,z2,z3,z8,z5,z1146]),(0,[z429,z2,z3,z350,z5,z6]),(0,[z1,z3,z1147,z8,z5,z6]),(0,[z1,z2,z3,z1148,z5,z6])],[(0,[z1,z2,z3,z1149,z5,z6]),(0,[z240,z1,z50,z8,z5,z6]),(0,[z377,z1,z3,z191,z5,z6]),(0,[z123,z1,z1085,z2,z5,z6])],[(0,[z0,z1,z3,z8,z5,z90]),(0,[z1,z1150,z3,z4,z5,z6]),(0,[z553,z2,z3,z4,z5,z6]),(0,[z404,z2,z406,z8,z5,z6])],[(0,[z1,z2,z3,z125,z444,z6]),(0,[z1,z2,z3,z8,z5,z1151]),(0,[z1,z50,z8,z5,z10,z153]),(0,[z1152,z1,z3,z8,z5,z6]),(0,[z1,z50,z290,z8,z5,z6]),(0,[z163,z2,z3,z1153,z5,z6]),(0,[z1,z1154,z2,z3,z5,z6])],[(0,[z1,z1155,z2,z3,z5,z6]),(0,[z34,z0,z3,z8,z5,z70]),(0,[z1,z138,z3,z8,z5,z6]),(0,[z1156,z1,z3,z8,z5,z6])],[(0,[z78,z1,z50,z343,z5,z6]),(0,[z783,z2,z3,z8,z5,z6])],[(0,[z408,z1,z50,z8,z5,z6]),(0,[z1,z1157,z2,z3,z5,z6]),(0,[z0,z712,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z1158,z5,z6]),(0,[z53,z1,z3,z4,z122,z6]),(0,[z1159,z1,z3,z8,z5,z6]),(0,[z1160,z2,z3,z8,z5,z6]),(0,[z338,z2,z3,z186,z5,z6])],[(0,[z39,z50,z63,z8,z5,z6]),(0,[z1,z81,z50,z15,z5,z6]),(0,[z1,z3,z8,z5,z176,z26]),(0,[z1,z2,z273,z8,z5,z6]),(0,[z1161,z2,z3,z8,z5,z6])],[(0,[z39,z1,z50,z224,z5,z6]),(0,[z1,z2,z815,z15,z5,z6]),(0,[z639,z2,z3,z15,z5,z6]),(0,[z1,z164,z3,z50,z5,z6])],[(0,[z9,z2,z3,z320,z135,z6]),(0,[z1,z2,z3,z1162,z5,z6])],[(0,[z1,z2,z3,z8,z1163,z6]),(0,[z1164,z1,z3,z8,z5,z6])],[(0,[z1,z2,z3,z1165,z5,z6]),(0,[z240,z64,z1,z2,z5,z6]),(0,[z1166,z2,z3,z8,z5,z6])],[(0,[z1,z1167,z3,z8,z5,z6]),(0,[z1,z2,z3,z1168,z5,z6]),(0,[z2,z3,z15,z458,z5,z6]),(0,[z840,z1,z2,z3,z8,z5]),(0,[z196,z2,z3,z253,z5,z6]),(0,[z1,z132,z3,z336,z5,z6]),(0,[z429,z2,z3,z872,z5,z6]),(0,[z226,z2,z3,z8,z5,z71]),(0,[z1,z801,z8,z5,z6,z71])],[(0,[z1,z2,z108,z15,z5,z6]),(0,[z1,z2,z32,z5,z228,z6]),(0,[z19,z1,z341,z8,z20,z6])],[(0,[z1,z2,z3,z4,z5,z745]),(0,[z1,z2,z1169,z8,z5,z6])],[(0,[z1,z2,z1170,z15,z5,z6]),(0,[z1,z406,z50,z8,z5,z6]),(1,[z1,z2,z8,z5,z804])],[(0,[z1,z204,z3,z8,z444,z6]),(0,[z0,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z1171,z5,z6]),(0,[z255,z1,z50,z8,z5,z6]),(0,[z19,z1,z2,z8,z20,z6]),(0,[z92,z1,z3,z18,z5,z150])],[(0,[z378,z1,z3,z8,z5,z26]),(0,[z799,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z1172,z5,z6]),(0,[z1,z50,z8,z5,z148,z6]),(0,[z123,z1,z31,z2,z5,z254]),(0,[z226,z2,z3,z1123,z5,z6]),(0,[z1,z2,z3,z1173,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1174]),(0,[z1,z2,z3,z5,z6,z1175]),(0,[z1176,z1,z3,z8,z5,z6]),(0,[z1,z2,z81,z8,z780,z6])],[(0,[z183,z2,z3,z15,z5,z6]),(0,[z464,z2,z3,z4,z5,z6]),(0,[z1,z3,z329,z15,z5,z6])],[(0,[z747,z1,z3,z8,z5,z6]),(0,[z1,z56,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z842]),(0,[z1,z209,z3,z8,z5,z6]),(0,[z1,z1085,z2,z8,z5,z6])],[(0,[z2,z3,z8,z4,z172,z6]),(0,[z594,z2,z3,z4,z5,z10]),(0,[z9,z2,z3,z8,z5,z113]),(0,[z1,z2,z3,z1177,z5,z6]),(0,[z0,z205,z3,z8,z5,z6]),(0,[z1,z2,z3,z1178,z5,z6])],[(0,[z1,z2,z3,z1179,z5,z6]),(0,[z1,z3,z422,z4,z5,z6]),(0,[z53,z1,z3,z8,z122,z457]),(0,[z447,z1,z2,z8,z5,z153])],[(0,[z9,z2,z3,z8,z5,z112]),(0,[z1,z1180,z3,z8,z5,z6]),(0,[z1,z3,z1181,z4,z5,z6]),(0,[z1182,z1,z3,z8,z5,z6])],[(0,[z1183,z1,z2,z8,z5,z6]),(1,[z1,z50,z8,z5,z90]),(0,[z1,z3,z50,z8,z5,z40]),(0,[z1,z50,z504,z8,z5,z6]),(0,[z7,z1,z3,z8,z5,z562]),(0,[z128,z1,z209,z8,z5,z153]),(0,[z1,z2,z3,z1184,z5,z6])],[(0,[z1,z1185,z3,z8,z5,z6]),(0,[z53,z1,z3,z336,z122,z6]),(0,[z1,z3,z8,z856,z122,z6])],[(0,[z1,z296,z3,z8,z5,z90]),(0,[z262,z1,z3,z8,z5,z198]),(0,[z1,z2,z3,z8,z5,z12])],[(0,[z1,z3,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z1186,z6]),(0,[z109,z1,z3,z15,z5,z6])],[(0,[z1,z204,z3,z224,z5,z6]),(0,[z1,z177,z3,z15,z5,z6]),(0,[z9,z2,z65,z8,z5,z6]),(0,[z34,z2,z3,z461,z5,z6]),(0,[z1,z167,z3,z295,z5,z6])],[(0,[z1,z1122,z50,z8,z5,z6]),(0,[z2,z3,z4,z5,z6,z272]),(0,[z1140,z1,z65,z8,z5,z6]),(1,[z1,z836,z8,z5,z6]),(0,[z1,z2,z1187,z8,z5,z6]),(0,[z1,z379,z406,z8,z5,z6])],[(0,[z110,z2,z3,z8,z5,z6]),(0,[z2,z3,z738,z8,z5,z6]),(0,[z114,z3,z50,z8,z5,z10]),(0,[z1,z2,z1188,z8,z5,z6]),(0,[z1,z341,z3,z350,z5,z6])],[(0,[z2,z488,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1189]),(0,[z1,z2,z3,z4,z5,z225]),(0,[z1,z2,z3,z4,z5,z778]),(0,[z0,z1,z88,z8,z5,z6]),(0,[z1190,z1,z3,z8,z5,z6]),(0,[z1,z1191,z3,z8,z5,z6]),(0,[z1192,z1,z3,z8,z5,z6])],[(1,[z2,z3,z4,z172,z6]),(0,[z2,z3,z15,z700,z5,z6]),(0,[z0,z119,z1,z8,z5,z6]),(0,[z0,z1,z3,z8,z5,z457]),(1,[z1,z3,z8,z5,z948]),(0,[z1,z2,z521,z32,z5,z6]),(0,[z11,z1,z2,z3,z75,z12]),(0,[z160,z262,z1,z3,z8,z71])],[(0,[z1,z50,z8,z5,z6,z368])],[(0,[z14,z1,z2,z4,z5,z6]),(0,[z3,z50,z15,z4,z5,z6]),(0,[z1,z50,z8,z135,z20,z6]),(0,[z134,z1,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1193]),(0,[z163,z341,z3,z8,z5,z6])],[(0,[z495,z2,z3,z8,z41,z6]),(0,[z1,z2,z3,z8,z5,z1194]),(0,[z1,z1195,z3,z8,z5,z6]),(0,[z0,z1,z3,z336,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z1196,z6])],[(0,[z1,z3,z1122,z8,z5,z6]),(0,[z351,z1,z99,z3,z5,z6]),(0,[z1,z2,z3,z1197,z5,z6]),(0,[z1,z2,z3,z8,z5,z802]),(0,[z279,z1,z3,z8,z532,z6]),(0,[z1,z2,z3,z1198,z5,z6]),(0,[z1,z13,z3,z8,z5,z16])],[(0,[z1,z2,z3,z125,z5,z40]),(0,[z9,z180,z3,z8,z5,z6]),(0,[z1,z675,z50,z8,z5,z6]),(0,[z1,z3,z664,z8,z5,z198]),(0,[z1,z2,z3,z1199,z5,z6])],[(0,[z78,z2,z360,z8,z5,z6]),(0,[z404,z2,z229,z8,z5,z6]),(0,[z1,z2,z3,z186,z5,z6])],[(0,[z93,z194,z3,z8,z5,z112]),(0,[z1200,z2,z3,z8,z5,z6]),(0,[z1201,z2,z3,z8,z5,z6])],[(0,[z182,z3,z23,z8,z5,z6]),(0,[z1,z2,z3,z8,z1202,z6]),(0,[z1,z2,z3,z125,z5,z6]),(0,[z363,z2,z3,z4,z5,z6]),(0,[z1,z95,z50,z15,z5,z6]),(0,[z1203,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1204]),(0,[z1,z478,z8,z5,z20,z6])],[(0,[z134,z1,z3,z15,z5,z6]),(0,[z1,z2,z3,z8,z5,z1205]),(0,[z1,z2,z3,z8,z5,z159])],[(0,[z183,z2,z3,z8,z5,z90]),(0,[z68,z450,z3,z8,z41,z6]),(0,[z1,z2,z398,z5,z20,z6]),(0,[z459,z1,z2,z3,z5,z127])],[(0,[z39,z2,z63,z8,z5,z90]),(0,[z1,z2,z1206,z8,z5,z6]),(0,[z205,z2,z3,z15,z5,z6]),(0,[z0,z1,z3,z5,z6,z210]),(0,[z1,z2,z3,z1207,z5,z6]),(0,[z304,z1,z2,z3,z8,z71])],[(0,[z1,z81,z50,z4,z5,z6]),(0,[z164,z799,z2,z3,z5,z6]),(0,[z1208,z2,z3,z8,z5,z6]),(0,[z226,z2,z273,z8,z5,z6])],[(0,[z1,z3,z357,z8,z5,z6]),(0,[z1209,z1,z2,z3,z5,z6]),(0,[z1,z3,z50,z8,z5,z254])],[(0,[z1210,z2,z3,z8,z5,z6]),(0,[z1211,z2,z3,z8,z5,z6]),(0,[z1,z2,z574,z8,z5,z436])],[(0,[z0,z1,z3,z207,z5,z6]),(0,[z196,z3,z8,z5,z198,z6]),(0,[z1,z2,z3,z1212,z5,z6]),(0,[z1,z3,z1213,z8,z5,z6])],[(0,[z442,z3,z23,z8,z5,z6]),(0,[z3,z50,z4,z5,z6,z10]),(0,[z1,z3,z8,z5,z1214,z6]),(0,[z0,z1,z473,z8,z5,z6]),(0,[z0,z114,z3,z8,z5,z10]),(0,[z226,z2,z3,z8,z5,z16])],[(0,[z367,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1215,z5,z6]),(0,[z1216,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1217])],[(0,[z1,z2,z3,z1218,z5,z6]),(0,[z1,z2,z108,z4,z5,z6]),(0,[z1,z2,z51,z32,z5,z6]),(0,[z1,z50,z8,z5,z6,z570]),(0,[z0,z55,z1,z8,z5,z6]),(0,[z100,z1,z2,z3,z75,z6])]],
   [[(0,[z1,z204,z3,z8,z5,z40]),(0,[z1,z3,z50,z8,z172,z6]),(0,[z1,z3,z50,z253,z5,z6]),(0,[z1219,z2,z3,z8,z5,z6]),(0,[z1,z3,z336,z5,z122,z6]),(0,[z1,z2,z3,z5,z6,z1220])],[(0,[z1,z2,z3,z8,z1221,z6]),(0,[z2,z528,z3,z4,z5,z6]),(0,[z0,z1,z3,z512,z5,z6]),(0,[z1,z2,z516,z219,z5,z6])],[(0,[z1,z3,z50,z8,z5,z203]),(0,[z1,z1222,z3,z8,z5,z6]),(0,[z1,z177,z81,z8,z5,z6]),(0,[z1,z3,z1223,z8,z5,z6])],[(0,[z0,z404,z3,z8,z5,z6]),(0,[z1,z3,z1224,z8,z5,z6])],[(0,[z834,z1,z2,z8,z5,z6]),(0,[z1,z50,z8,z5,z426,z6]),(0,[z0,z1,z3,z398,z5,z6]),(0,[z1225,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z1226,z5,z6]),(0,[z14,z1,z50,z8,z5,z6]),(0,[z1,z50,z8,z5,z6,z586]),(0,[z1,z3,z8,z5,z1227,z6])],[(0,[z1,z2,z3,z1228,z5,z6]),(0,[z2,z3,z775,z4,z5,z6]),(0,[z1,z3,z329,z4,z5,z6]),(0,[z9,z2,z3,z8,z158,z6]),(0,[z11,z1,z2,z3,z587,z6]),(0,[z1,z1085,z2,z32,z5,z6])],[(0,[z39,z2,z63,z4,z5,z6]),(0,[z658,z2,z3,z8,z41,z6]),(0,[z1,z2,z3,z1229,z5,z6]),(0,[z1,z3,z50,z461,z5,z6]),(0,[z1,z2,z8,z5,z20,z254]),(0,[z1,z164,z3,z478,z5,z6]),(0,[z226,z56,z3,z8,z5,z6])],[(0,[z1,z2,z1230,z8,z5,z6]),(0,[z1,z2,z3,z15,z5,z905]),(0,[z1,z3,z15,z5,z6,z358]),(0,[z1,z2,z3,z1231,z5,z6]),(0,[z160,z1,z2,z3,z186,z71])],[(0,[z1,z37,z50,z8,z5,z6]),(0,[z1,z2,z3,z15,z444,z6]),(0,[z0,z509,z3,z4,z5,z6]),(0,[z1,z907,z3,z15,z5,z6]),(0,[z1232,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z1233,z5,z6]),(0,[z1,z209,z8,z5,z6,z153])],[(0,[z1,z194,z3,z8,z5,z203]),(0,[z1,z2,z3,z8,z5,z1234]),(0,[z1,z2,z3,z8,z5,z1235])],[(0,[z68,z2,z3,z15,z41,z6]),(0,[z1,z65,z744,z8,z5,z6]),(0,[z168,z0,z3,z8,z5,z6]),(0,[z429,z151,z3,z8,z5,z6])],[(0,[z49,z2,z3,z738,z5,z6]),(0,[z1,z473,z1236,z8,z5,z6]),(0,[z0,z9,z3,z8,z135,z6]),(0,[z1237,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z233,z5,z6])],[(0,[z1,z1238,z3,z8,z5,z6]),(0,[z1,z149,z776,z3,z5,z6]),(0,[z1,z25,z3,z8,z5,z704]),(0,[z1,z2,z3,z1239,z5,z6])],[(0,[z1,z2,z3,z125,z172,z6]),(0,[z1,z2,z65,z8,z5,z113]),(0,[z1,z3,z50,z1013,z5,z6]),(0,[z179,z1,z3,z385,z5,z6])],[(0,[z1,z3,z50,z224,z5,z6]),(0,[z109,z1,z3,z4,z5,z6]),(0,[z338,z2,z3,z15,z5,z6]),(0,[z226,z3,z50,z8,z5,z6]),(0,[z0,z1,z3,z8,z5,z1240]),(0,[z1,z13,z3,z186,z5,z6])]],
   [[(0,[z1,z296,z3,z15,z5,z6]),(0,[z1,z2,z3,z8,z5,z1241]),(0,[z1,z2,z3,z4,z5,z849]),(0,[z1,z177,z3,z4,z5,z6]),(0,[z1,z2,z15,z1119,z5,z6]),(0,[z1,z2,z3,z8,z1242,z6])],[(0,[z1,z1243,z3,z8,z5,z6]),(0,[z22,z1,z108,z8,z5,z26]),(0,[z1,z379,z229,z8,z5,z6])],[(0,[z531,z1,z2,z8,z5,z153]),(0,[z1,z2,z3,z1244,z5,z6]),(0,[z1,z2,z3,z1245,z5,z6]),(0,[z338,z2,z3,z1199,z5,z6])],[(0,[z1,z2,z3,z1246,z5,z6]),(0,[z1,z2,z1247,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1248]),(0,[z68,z2,z473,z8,z41,z6]),(0,[z404,z3,z50,z8,z5,z6])],[],[(0,[z155,z1,z50,z8,z5,z6]),(0,[z1,z2,z3,z569,z5,z169]),(0,[z1,z1249,z3,z8,z5,z6]),(0,[z1,z2,z3,z1153,z5,z6]),(0,[z1,z1250,z3,z8,z5,z6]),(0,[z1,z3,z422,z5,z150,z6]),(0,[z1,z1251,z3,z8,z5,z6])],[(0,[z429,z2,z3,z8,z5,z6]),(0,[z80,z1,z2,z3,z5,z502]),(0,[z1,z353,z50,z8,z5,z153]),(0,[z160,z1,z2,z3,z219,z71])],[(0,[z423,z1,z3,z15,z5,z6]),(0,[z1,z2,z1252,z8,z5,z6]),(0,[z1253,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z18,z5,z397])],[(0,[z0,z1,z3,z21,z5,z6]),(0,[z594,z1,z2,z3,z5,z547]),(0,[z1,z180,z3,z8,z5,z113]),(0,[z196,z2,z574,z8,z5,z6]),(0,[z196,z2,z3,z8,z5,z436])],[(0,[z1,z2,z3,z8,z5,z1254]),(0,[z133,z2,z3,z8,z5,z6]),(0,[z236,z2,z3,z4,z5,z6]),(0,[z34,z3,z50,z8,z5,z70]),(0,[z1,z2,z406,z300,z5,z6])],[(0,[z1,z2,z3,z1255,z5,z6]),(0,[z1,z2,z88,z8,z5,z70]),(0,[z1256,z1,z3,z8,z5,z6])],[(0,[z424,z2,z3,z4,z5,z6]),(0,[z1,z50,z8,z5,z6,z326]),(0,[z0,z1,z3,z8,z5,z256]),(0,[z726,z2,z3,z8,z5,z6])],[(0,[z1,z204,z3,z8,z172,z6]),(0,[z1,z81,z50,z8,z137,z6]),(0,[z338,z2,z516,z8,z5,z6])],[(0,[z1,z95,z50,z4,z5,z6]),(0,[z1,z2,z945,z8,z5,z6]),(0,[z9,z2,z3,z8,z135,z6]),(0,[z1,z216,z3,z191,z5,z6])],[(0,[z134,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z1257,z5,z6]),(0,[z1,z1258,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1259]),(0,[z1,z2,z3,z1260,z5,z6]),(0,[z1,z286,z3,z15,z5,z6]),(0,[z1,z180,z65,z8,z5,z6]),(0,[z2,z65,z8,z5,z41,z6])]],
   [[(1,[z3,z880,z8,z5,z6]),(0,[z1,z2,z1261,z8,z5,z6]),(0,[z481,z2,z79,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1262]),(0,[z1,z3,z8,z5,z6,z1263]),(0,[z1,z3,z1264,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1265]),(0,[z1266,z2,z3,z8,z5,z6])],[(0,[z1,z25,z3,z15,z5,z198]),(0,[z7,z1,z88,z8,z5,z6]),(0,[z110,z2,z3,z300,z5,z6]),(0,[z459,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z8,z444,z90])],[(0,[z615,z2,z3,z4,z5,z6]),(0,[z7,z1,z50,z8,z5,z6]),(0,[z1,z1267,z3,z8,z5,z6])],[(0,[z1,z3,z50,z343,z5,z6]),(0,[z1,z2,z3,z1268,z5,z6])],[(0,[z1045,z3,z50,z8,z5,z6]),(0,[z1,z88,z8,z191,z5,z6]),(0,[z1,z2,z406,z5,z75,z6]),(0,[z80,z1,z2,z3,z5,z690])],[(0,[z1,z3,z4,z5,z1214,z6]),(0,[z11,z1,z3,z50,z75,z6]),(0,[z462,z1,z3,z8,z5,z26])],[(0,[z1,z2,z1269,z8,z5,z6]),(0,[z1,z3,z897,z4,z5,z6]),(0,[z1,z151,z3,z15,z5,z6]),(0,[z0,z1,z108,z8,z5,z6]),(0,[z1,z2,z3,z1270,z5,z6])],[(0,[z119,z1,z204,z8,z5,z6]),(0,[z39,z119,z2,z4,z5,z6]),(0,[z1271,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z300,z321,z6]),(0,[z117,z1,z149,z3,z5,z6]),(0,[z1,z2,z3,z1272,z5,z6]),(0,[z1,z1273,z3,z8,z5,z6]),(0,[z80,z1,z2,z3,z5,z539]),(0,[z1,z2,z3,z5,z1009,z6])],[(0,[z0,z226,z3,z8,z5,z6]),(0,[z1,z164,z2,z115,z5,z107])],[(0,[z0,z1,z3,z121,z5,z6]),(0,[z1,z3,z315,z8,z490,z6]),(0,[z1,z1274,z3,z8,z5,z6])],[(0,[z581,z1,z481,z2,z5,z6]),(0,[z1,z286,z3,z8,z5,z313]),(0,[z1275,z2,z3,z8,z5,z6])],[(0,[z163,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z1276,z5,z6])],[(0,[z1,z956,z3,z15,z5,z6]),(0,[z262,z1,z3,z15,z5,z6]),(0,[z53,z196,z3,z8,z122,z6]),(0,[z1,z132,z3,z8,z197,z6])],[(0,[z36,z2,z3,z8,z5,z6])],[(0,[z46,z3,z23,z8,z5,z6]),(0,[z1,z2,z3,z15,z5,z40]),(0,[z1,z2,z348,z15,z5,z6]),(0,[z1,z2,z65,z8,z5,z227]),(0,[z0,z1,z3,z1277,z5,z6])]],
   [[(1,[z2,z720,z8,z5,z6]),(0,[z0,z459,z1,z3,z5,z6]),(0,[z134,z119,z1,z8,z5,z6]),(0,[z1,z3,z212,z5,z198,z6]),(0,[z1,z379,z3,z8,z5,z12]),(0,[z1,z2,z3,z5,z1278,z6]),(0,[z262,z1,z3,z5,z6,z210])],[(0,[z1,z2,z3,z8,z5,z1279]),(0,[z1,z2,z3,z4,z444,z6]),(0,[z1280,z1,z3,z8,z5,z6]),(0,[z1,z214,z50,z8,z5,z6]),(0,[z1,z62,z3,z8,z5,z6]),(0,[z205,z2,z3,z1272,z5,z6]),(0,[z1,z3,z1281,z8,z5,z6])],[(0,[z1,z2,z3,z15,z5,z6]),(0,[z93,z573,z3,z8,z5,z6]),(0,[z1,z2,z3,z352,z5,z6]),(0,[z179,z1,z99,z3,z5,z6]),(0,[z448,z1,z2,z3,z587,z6]),(0,[z244,z1,z3,z8,z5,z250]),(0,[z1,z2,z3,z8,z5,z1282]),(0,[z205,z2,z3,z8,z5,z457]),(0,[z591,z1,z3,z8,z122,z6])],[(0,[z1,z2,z3,z1283,z5,z6]),(0,[z68,z2,z3,z4,z41,z6]),(0,[z965,z1,z3,z8,z5,z6])],[(0,[z183,z0,z3,z15,z5,z6]),(0,[z1284,z1,z3,z8,z5,z6]),(0,[z1,z1285,z3,z8,z5,z6]),(0,[z1,z2,z1286,z8,z5,z6])],[(0,[z405,z2,z3,z4,z5,z6]),(0,[z114,z2,z3,z15,z5,z10]),(0,[z2,z3,z305,z5,z41,z6]),(0,[z1,z2,z1287,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1288]),(0,[z1289,z2,z3,z8,z5,z6]),(0,[z205,z2,z3,z336,z5,z6])],[(0,[z1,z1290,z3,z8,z5,z6])],[(0,[z540,z1,z50,z8,z5,z6]),(0,[z338,z2,z3,z4,z5,z6]),(0,[z1,z341,z3,z8,z5,z6]),(0,[z0,z196,z3,z8,z5,z6]),(0,[z1,z2,z1291,z8,z5,z6])],[(0,[z1,z296,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z1292]),(0,[z1293,z1,z3,z8,z5,z6]),(0,[z9,z2,z3,z4,z41,z6]),(0,[z1,z3,z50,z1082,z5,z6]),(0,[z1,z2,z3,z664,z5,z150])],[(0,[z1,z1073,z3,z8,z5,z6]),(0,[z1,z180,z3,z8,z5,z227]),(0,[z1294,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z1295,z5,z6]),(0,[z1,z1296,z2,z3,z5,z6])],[(0,[z39,z296,z3,z4,z5,z6]),(0,[z1,z2,z3,z376,z5,z6]),(0,[z1,z450,z3,z305,z5,z6]),(0,[z1,z2,z1297,z8,z5,z6]),(0,[z1,z2,z185,z8,z5,z107])],[(0,[z201,z1,z50,z8,z5,z6]),(0,[z93,z194,z3,z15,z5,z6]),(0,[z34,z167,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z471]),(0,[z408,z405,z3,z8,z5,z6]),(0,[z1,z2,z81,z8,z519,z6]),(1,[z1,z776,z3,z5,z6]),(0,[z1,z1298,z3,z8,z5,z6])],[(0,[z2,z63,z8,z41,z20,z6]),(0,[z1,z2,z3,z1299,z5,z6]),(0,[z1,z2,z115,z8,z5,z181]),(0,[z1,z2,z3,z1300,z5,z6]),(0,[z1,z2,z115,z8,z5,z107])],[(0,[z1,z3,z1058,z8,z5,z6]),(0,[z1,z2,z88,z8,z5,z10]),(0,[z1,z2,z1301,z8,z5,z6])],[(0,[z2,z3,z807,z4,z5,z6]),(0,[z145,z2,z3,z15,z5,z6]),(0,[z0,z1,z164,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z313]),(0,[z1,z2,z3,z1302,z5,z6]),(0,[z1,z2,z3,z8,z5,z1022])],[(0,[z0,z1,z3,z47,z5,z6]),(1,[z2,z63,z8,z172,z6]),(0,[z423,z1,z3,z4,z5,z6]),(0,[z1,z2,z516,z8,z5,z6]),(0,[z1,z3,z8,z5,z6,z1303]),(0,[z1,z1304,z3,z8,z5,z6])]],
   [[(0,[z1,z1305,z3,z8,z5,z6]),(0,[z1,z2,z406,z8,z5,z12])],[(0,[z2,z3,z4,z5,z6,z634]),(0,[z2,z520,z3,z4,z5,z6]),(0,[z1,z2,z3,z855,z5,z6]),(0,[z1,z1306,z3,z8,z5,z6]),(0,[z1,z2,z3,z1307,z5,z6]),(0,[z1,z151,z81,z8,z5,z6]),(0,[z1,z2,z3,z1308,z5,z6])],[(0,[z1,z1309,z3,z8,z5,z6]),(0,[z2,z3,z522,z4,z5,z6]),(1,[z869,z1,z8,z5,z6]),(0,[z1,z3,z50,z8,z5,z436]),(0,[z1,z2,z3,z1310,z5,z6]),(0,[z1,z2,z3,z1311,z5,z6]),(0,[z1,z2,z3,z253,z5,z457]),(0,[z1,z2,z3,z683,z5,z150])],[(0,[z1,z2,z50,z8,z172,z6]),(0,[z78,z2,z610,z8,z5,z6])],[(0,[z78,z360,z50,z8,z5,z6]),(0,[z0,z1312,z3,z8,z5,z6]),(0,[z0,z1,z3,z219,z5,z6]),(0,[z1312,z2,z3,z8,z5,z6]),(0,[z1,z2,z1313,z8,z5,z6]),(0,[z1,z2,z3,z1314,z5,z6])],[(0,[z0,z49,z3,z4,z5,z6]),(0,[z160,z1,z2,z3,z15,z71]),(0,[z1,z516,z50,z8,z5,z6]),(0,[z819,z2,z3,z8,z5,z6])],[(0,[z335,z1,z3,z8,z122,z6]),(0,[z1,z2,z3,z8,z1315,z6]),(0,[z9,z2,z3,z8,z560,z6]),(0,[z2,z3,z4,z5,z637,z6]),(0,[z1,z3,z8,z5,z6,z1316]),(0,[z1,z2,z3,z1142,z5,z6])],[(0,[z1,z286,z3,z4,z5,z6]),(0,[z1,z1317,z3,z8,z5,z6])],[(0,[z355,z3,z23,z8,z5,z6]),(0,[z1,z3,z50,z8,z5,z113]),(0,[z869,z1,z2,z8,z5,z6]),(0,[z279,z1,z2,z8,z20,z6]),(0,[z1,z2,z3,z8,z856,z6]),(0,[z19,z1,z2,z8,z20,z159])],[(0,[z93,z3,z880,z8,z5,z6]),(0,[z78,z50,z8,z5,z41,z6]),(0,[z1,z25,z3,z4,z5,z198]),(0,[z22,z1,z3,z336,z5,z6])],[(0,[z1,z3,z50,z8,z5,z112]),(0,[z119,z1,z2,z8,z172,z6]),(0,[z1,z2,z65,z8,z135,z6]),(0,[z1,z2,z8,z5,z6,z1318]),(0,[z1,z2,z3,z1319,z5,z6]),(0,[z1,z2,z3,z1320,z5,z6])],[(0,[z1,z2,z3,z8,z5,z90]),(0,[z1,z2,z3,z15,z172,z6]),(0,[z92,z1,z3,z15,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1321]),(0,[z1040,z1,z2,z8,z5,z6]),(0,[z1,z3,z1322,z8,z5,z6]),(0,[z1323,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z150,z846]),(0,[z979,z1,z516,z8,z5,z6])],[(0,[z1,z999,z3,z15,z5,z6]),(0,[z0,z1,z3,z295,z5,z6]),(0,[z1,z50,z8,z5,z6,z153]),(0,[z80,z1,z3,z50,z5,z127]),(0,[z1,z1324,z3,z8,z5,z6]),(0,[z459,z1,z2,z3,z5,z150])],[(0,[z1,z1325,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1326]),(0,[z1,z13,z3,z15,z5,z6]),(0,[z1,z2,z3,z1327,z5,z6]),(0,[z160,z1,z3,z50,z8,z71]),(0,[z1,z3,z8,z5,z6,z1328]),(0,[z80,z1,z2,z3,z5,z629]),(0,[z464,z2,z3,z8,z5,z107]),(0,[z1329,z1,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1330]),(0,[z1,z151,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z954,z8,z5,z6]),(0,[z1,z952,z3,z4,z5,z6]),(0,[z324,z2,z3,z4,z5,z6]),(0,[z1331,z2,z3,z8,z5,z6]),(0,[z1,z3,z50,z1118,z5,z6]),(0,[z1,z72,z50,z8,z5,z6]),(0,[z1,z416,z50,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1332]),(0,[z464,z2,z3,z5,z6,z127])],[(0,[z2,z3,z15,z493,z5,z6]),(0,[z1,z1333,z3,z8,z5,z6])],[(0,[z1,z2,z1334,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1010]),(0,[z1,z167,z3,z8,z5,z70]),(0,[z1015,z1,z50,z8,z5,z6])],[],[(0,[z163,z2,z3,z4,z5,z6])],[(0,[z262,z1,z3,z4,z5,z6]),(0,[z1,z3,z926,z15,z5,z6]),(0,[z68,z2,z3,z207,z41,z6]),(0,[z1,z3,z50,z8,z5,z159]),(0,[z1,z2,z3,z8,z5,z1335]),(0,[z404,z2,z3,z8,z5,z12]),(0,[z11,z1,z62,z3,z75,z6])],[(0,[z161,z2,z3,z4,z5,z6]),(0,[z1,z2,z473,z305,z5,z6]),(0,[z1,z2,z3,z8,z5,z1336]),(0,[z0,z1,z3,z8,z5,z225]),(0,[z1337,z2,z3,z8,z5,z6])],[(0,[z93,z1,z136,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z40]),(0,[z423,z78,z79,z8,z5,z6]),(0,[z1,z2,z348,z4,z5,z6]),(0,[z168,z3,z50,z8,z5,z6]),(0,[z1,z454,z3,z8,z5,z198]),(0,[z1338,z2,z3,z8,z5,z6]),(0,[z1,z1339,z3,z8,z5,z6])],[(0,[z1,z1340,z3,z8,z5,z6]),(0,[z1,z329,z8,z5,z6,z153]),(0,[z1,z2,z3,z8,z5,z256])],[(0,[z1,z2,z3,z1341,z5,z6]),(0,[z1,z2,z1342,z8,z5,z6]),(0,[z1,z663,z50,z8,z5,z6]),(0,[z1,z50,z8,z41,z20,z6]),(0,[z133,z123,z31,z2,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z39,z1,z50,z125,z5,z6]),(0,[z3,z50,z4,z5,z41,z6]),(0,[z226,z2,z3,z15,z5,z6]),(0,[z1,z3,z1343,z8,z5,z6]),(0,[z1,z1344,z3,z8,z5,z6])],[(0,[z1,z1345,z3,z8,z5,z6]),(0,[z1,z50,z8,z5,z16,z153]),(0,[z1,z3,z8,z5,z856,z6]),(0,[z1,z2,z8,z137,z780,z6]),(0,[z800,z1,z3,z8,z5,z6]),(0,[z1,z13,z516,z8,z5,z6])],[(0,[z1,z3,z1236,z8,z5,z6]),(0,[z1,z2,z3,z1346,z5,z6]),(0,[z1,z2,z961,z3,z5,z6]),(0,[z226,z2,z3,z1197,z5,z6]),(0,[z1,z2,z3,z186,z5,z71])],[(0,[z1,z2,z3,z1347,z5,z6]),(0,[z1,z2,z3,z8,z1348,z6]),(0,[z114,z2,z3,z4,z5,z10]),(0,[z1349,z2,z3,z8,z5,z6]),(0,[z404,z62,z3,z8,z5,z6])],[(0,[z2,z3,z4,z5,z6,z546]),(0,[z404,z2,z3,z15,z5,z6]),(0,[z1,z3,z50,z212,z5,z6]),(0,[z2,z3,z8,z5,z1031,z6]),(0,[z19,z1,z2,z233,z20,z6]),(0,[z36,z2,z3,z371,z5,z6]),(0,[z11,z1,z2,z3,z75,z256]),(0,[z226,z2,z3,z186,z5,z6])],[(0,[z0,z1,z3,z48,z5,z6]),(0,[z25,z2,z3,z4,z5,z10]),(0,[z1,z1350,z3,z8,z5,z6]),(0,[z196,z3,z50,z8,z5,z6])]],
   [[(0,[z0,z1,z3,z59,z5,z6]),(0,[z1,z2,z3,z8,z1351,z6]),(0,[z2,z3,z4,z5,z587,z6]),(0,[z485,z2,z3,z4,z5,z6]),(0,[z1,z3,z1352,z8,z5,z6])],[(0,[z1,z450,z3,z8,z5,z6]),(0,[z509,z2,z3,z4,z5,z6])],[(0,[z2,z602,z3,z4,z5,z6]),(0,[z1,z51,z50,z4,z5,z6]),(0,[z1,z2,z1353,z8,z5,z6]),(0,[z1,z2,z8,z5,z20,z159]),(0,[z1,z2,z8,z5,z152,z153])],[(0,[z93,z194,z3,z4,z5,z6]),(0,[z1354,z1,z3,z8,z5,z6]),(0,[z205,z2,z3,z4,z5,z6]),(0,[z1,z3,z50,z18,z5,z150]),(0,[z479,z1,z115,z8,z5,z107])],[(0,[z1,z2,z3,z8,z172,z90]),(0,[z1,z50,z18,z8,z5,z153]),(0,[z0,z1,z421,z3,z5,z6]),(0,[z1,z2,z3,z32,z5,z313])],[(0,[z36,z2,z3,z300,z5,z6])],[(0,[z1,z1355,z3,z8,z5,z6]),(0,[z468,z2,z3,z8,z135,z6])],[(0,[z194,z3,z880,z8,z5,z6]),(0,[z1,z446,z3,z191,z5,z6]),(0,[z1356,z2,z3,z8,z5,z6]),(0,[z226,z2,z516,z8,z5,z6])],[(0,[z1,z2,z3,z1357,z5,z6]),(0,[z78,z2,z79,z15,z5,z6]),(0,[z0,z1,z3,z820,z5,z6]),(0,[z0,z1,z3,z821,z5,z6]),(0,[z1,z62,z3,z300,z5,z6]),(0,[z1,z2,z229,z8,z5,z12]),(0,[z1,z1358,z3,z8,z5,z6])],[(0,[z1,z2,z896,z4,z5,z6]),(0,[z260,z2,z3,z4,z5,z6]),(0,[z1,z3,z50,z8,z5,z227]),(0,[z0,z824,z3,z8,z5,z6]),(0,[z1,z2,z348,z8,z5,z457]),(0,[z1,z2,z3,z1359,z5,z6]),(0,[z380,z1,z2,z3,z75,z6])],[(0,[z1,z2,z1360,z8,z5,z6]),(0,[z0,z1361,z3,z8,z5,z6])],[(0,[z1,z2,z3,z4,z5,z983]),(0,[z240,z1,z31,z2,z5,z6]),(0,[z1,z3,z50,z233,z5,z6]),(0,[z1,z2,z88,z8,z5,z6]),(0,[z1,z31,z1085,z2,z5,z6]),(0,[z1,z56,z273,z8,z5,z6])],[(0,[z1,z2,z3,z8,z1362,z6]),(0,[z2,z3,z4,z5,z6,z584]),(0,[z1,z2,z3,z931,z5,z6]),(0,[z1363,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z457]),(0,[z1,z2,z348,z336,z5,z6]),(0,[z22,z1,z3,z8,z5,z26]),(0,[z1364,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1365]),(0,[z9,z2,z3,z352,z5,z6]),(0,[z334,z2,z3,z4,z5,z6]),(0,[z1,z347,z3,z15,z5,z6]),(0,[z244,z1,z3,z8,z5,z26]),(0,[z1,z2,z3,z1366,z5,z6]),(0,[z179,z1,z149,z3,z5,z6]),(0,[z1,z2,z3,z8,z1022,z71])],[(0,[z424,z2,z63,z8,z5,z6]),(0,[z1,z1367,z3,z8,z5,z6])],[(0,[z1,z3,z4,z5,z6,z1316]),(0,[z1,z50,z8,z5,z6,z668]),(0,[z1,z108,z50,z8,z5,z6]),(0,[z133,z0,z3,z8,z5,z6]),(0,[z1,z2,z3,z336,z5,z6]),(0,[z429,z2,z3,z8,z20,z6]),(0,[z1182,z1,z273,z8,z5,z6])]],
   [[(0,[z0,z1,z3,z833,z5,z6]),(0,[z1,z2,z1368,z8,z5,z6]),(0,[z110,z2,z3,z5,z75,z6]),(0,[z1,z3,z1369,z8,z5,z6])],[(0,[z1,z2,z3,z8,z1370,z6]),(0,[z2,z3,z4,z137,z41,z6]),(0,[z2,z3,z8,z5,z813,z10]),(0,[z1371,z1,z3,z8,z5,z6])],[(0,[z1,z2,z3,z1372,z5,z6]),(0,[z1,z481,z50,z8,z5,z6]),(0,[z1,z3,z1373,z8,z5,z6])],[(0,[z1,z2,z3,z224,z5,z90]),(0,[z1,z2,z3,z4,z172,z6]),(0,[z1,z1150,z3,z8,z5,z6]),(0,[z1,z2,z3,z106,z5,z293]),(0,[z1,z50,z8,z5,z678,z6]),(0,[z1,z776,z216,z3,z5,z6]),(0,[z1,z3,z30,z191,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1374]),(0,[z1,z2,z3,z1375,z5,z6]),(0,[z1,z1376,z3,z8,z5,z6])],[(0,[z1,z2,z998,z4,z5,z6]),(0,[z9,z2,z3,z376,z5,z6]),(0,[z1,z3,z1377,z8,z5,z6]),(0,[z1,z167,z3,z8,z5,z10]),(0,[z1,z347,z3,z376,z5,z6]),(0,[z0,z163,z3,z8,z5,z6])],[(0,[z2,z63,z8,z5,z172,z6]),(0,[z39,z2,z3,z4,z444,z6]),(0,[z1,z50,z4,z5,z6,z153]),(0,[z1,z13,z3,z4,z5,z6]),(0,[z1,z115,z50,z8,z5,z153])],[(0,[z39,z2,z3,z352,z5,z6]),(0,[z1,z50,z8,z5,z6,z238]),(0,[z1,z2,z3,z1378,z5,z6])],[(0,[z1379,z1,z3,z8,z5,z6]),(0,[z133,z3,z50,z8,z5,z6]),(0,[z0,z1,z3,z350,z5,z6]),(0,[z36,z379,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z210])],[(0,[z183,z2,z3,z295,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1380]),(0,[z199,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z233,z5,z159])],[(0,[z1,z2,z1381,z8,z5,z6]),(0,[z1,z2,z3,z1382,z5,z6]),(0,[z2,z130,z3,z4,z5,z6]),(0,[z536,z1,z50,z8,z5,z6]),(0,[z0,z1,z3,z320,z5,z6]),(0,[z1,z659,z50,z8,z5,z6]),(0,[z1383,z1,z3,z8,z5,z6]),(1,[z429,z2,z8,z20,z6])],[(0,[z9,z2,z3,z8,z349,z6]),(0,[z1,z2,z3,z207,z5,z6]),(0,[z2,z3,z4,z5,z618,z6]),(0,[z1,z379,z3,z15,z5,z6]),(0,[z1,z3,z1384,z8,z5,z6]),(0,[z1,z3,z8,z5,z6,z948]),(0,[z1,z164,z2,z3,z5,z107]),(0,[z1,z3,z8,z5,z6,z1385]),(0,[z1,z2,z3,z8,z5,z1386])],[(0,[z1,z2,z473,z8,z5,z6]),(0,[z11,z1,z379,z3,z75,z6]),(0,[z1,z406,z1387,z8,z5,z6])],[(0,[z78,z1,z50,z352,z5,z6]),(0,[z78,z1,z50,z15,z5,z6]),(0,[z1,z2,z3,z5,z6,z1388]),(0,[z1,z3,z315,z8,z232,z6]),(0,[z217,z1,z3,z8,z148,z6])],[(0,[z1,z2,z1389,z8,z5,z6]),(0,[z123,z1,z31,z2,z5,z313]),(0,[z1,z1390,z3,z8,z5,z6]),(0,[z1,z2,z273,z186,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z918]),(0,[z9,z78,z50,z8,z5,z6]),(0,[z183,z3,z50,z15,z5,z6]),(0,[z1,z2,z3,z1391,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1392]),(0,[z1,z2,z3,z512,z5,z6]),(0,[z1,z1083,z3,z8,z5,z6]),(0,[z1,z25,z3,z8,z5,z948]),(0,[z1,z1393,z3,z8,z5,z6])],[(0,[z1,z2,z3,z1394,z5,z6]),(1,[z2,z3,z8,z5,z813]),(0,[z1,z2,z3,z1395,z5,z6])],[(0,[z1,z1396,z3,z8,z5,z6]),(0,[z1,z3,z50,z1177,z5,z6]),(0,[z1361,z2,z3,z8,z5,z6])],[(0,[z0,z9,z3,z4,z5,z6]),(0,[z1,z2,z3,z398,z5,z6]),(0,[z11,z1,z2,z406,z75,z6]),(0,[z1,z1397,z3,z8,z5,z6])],[(0,[z1,z1398,z3,z8,z5,z6])],[(0,[z404,z2,z3,z4,z5,z6]),(0,[z538,z1,z2,z3,z5,z502]),(0,[z1,z450,z65,z8,z5,z6]),(0,[z53,z1,z88,z8,z5,z6])],[(0,[z1,z60,z50,z32,z5,z6]),(0,[z1,z2,z1399,z8,z5,z6])],[(0,[z1,z2,z3,z15,z5,z254]),(0,[z1,z50,z8,z5,z6,z35]),(0,[z1,z3,z50,z8,z5,z12]),(0,[z1,z430,z3,z191,z5,z6]),(0,[z36,z2,z406,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1400]),(0,[z1,z2,z130,z504,z5,z6]),(0,[z1,z50,z8,z5,z44,z6]),(0,[z1,z2,z3,z350,z5,z225]),(0,[z11,z404,z2,z3,z75,z6])],[(0,[z39,z78,z50,z8,z5,z6]),(0,[z1,z631,z50,z8,z5,z6])],[(0,[z1,z2,z3,z1401,z5,z6]),(0,[z1,z3,z1181,z8,z5,z6]),(0,[z1,z3,z1387,z8,z5,z6]),(0,[z1,z62,z406,z8,z5,z6])],[(0,[z1,z2,z406,z15,z5,z6]),(0,[z110,z3,z50,z8,z5,z6]),(0,[z1402,z2,z3,z8,z5,z6])],[(0,[z39,z296,z63,z8,z5,z6]),(0,[z1,z2,z574,z15,z5,z6]),(0,[z1,z2,z3,z15,z5,z436]),(0,[z262,z1,z3,z8,z5,z26]),(0,[z19,z429,z2,z8,z20,z6]),(0,[z163,z2,z3,z8,z5,z225]),(0,[z19,z1,z151,z8,z20,z6]),(0,[z1,z56,z3,z186,z5,z6])],[(0,[z1,z2,z3,z1403,z5,z6]),(0,[z1,z2,z3,z1404,z5,z6]),(0,[z1405,z1,z3,z8,z5,z6])],[(0,[z1,z3,z1406,z8,z5,z6]),(0,[z1,z2,z672,z8,z137,z6]),(0,[z363,z2,z3,z8,z5,z70]),(0,[z869,z1,z3,z8,z5,z6]),(0,[z1,z3,z1407,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1240]),(0,[z1,z2,z3,z1408,z5,z6])]],
   [[(0,[z1,z2,z3,z15,z5,z203]),(0,[z1,z2,z3,z8,z5,z1409]),(0,[z1410,z1,z3,z8,z5,z6])],[(0,[z1,z3,z1411,z8,z5,z6]),(0,[z1,z2,z3,z1412,z5,z6]),(0,[z1,z1413,z3,z8,z5,z6])],[(0,[z2,z720,z63,z8,z5,z6]),(0,[z2,z3,z720,z8,z5,z6]),(0,[z1414,z1,z3,z8,z5,z6]),(0,[z1415,z2,z3,z8,z5,z6])],[(0,[z1,z50,z8,z5,z172,z6]),(0,[z1,z2,z3,z8,z5,z1189]),(0,[z1,z2,z3,z15,z5,z113]),(0,[z1,z167,z836,z8,z5,z6]),(0,[z479,z119,z1,z8,z5,z6])],[(0,[z479,z1,z50,z8,z5,z6]),(0,[z11,z1,z2,z3,z451,z6]),(0,[z1416,z2,z3,z8,z5,z6]),(0,[z160,z226,z2,z3,z8,z71])],[(0,[z9,z2,z3,z4,z5,z6]),(0,[z1,z347,z3,z4,z5,z6]),(0,[z1,z3,z50,z186,z5,z6]),(0,[z1,z50,z8,z5,z111,z6])],[(0,[z14,z1,z2,z8,z5,z6])],[(0,[z1,z3,z50,z125,z5,z6]),(0,[z39,z1,z50,z15,z5,z6]),(0,[z1,z132,z3,z8,z232,z6])],[(0,[z1,z2,z3,z21,z5,z6]),(0,[z1,z2,z3,z8,z5,z1417]),(0,[z1,z2,z3,z1418,z5,z6]),(0,[z1051,z1,z3,z8,z5,z6]),(0,[z1419,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z1420])],[(0,[z1421,z1,z3,z8,z5,z6]),(0,[z2,z3,z376,z5,z41,z6]),(0,[z1,z2,z1422,z8,z5,z6])],[(0,[z1,z1423,z3,z8,z5,z6]),(0,[z2,z3,z828,z4,z5,z6]),(0,[z1050,z1,z3,z4,z5,z6]),(0,[z1,z2,z65,z15,z5,z6]),(0,[z1,z2,z8,z5,z804,z153]),(0,[z160,z1,z2,z516,z8,z71])],[(0,[z1,z1424,z3,z8,z5,z6]),(0,[z1,z2,z3,z1425,z5,z6])],[(0,[z0,z1,z3,z8,z444,z6]),(0,[z39,z2,z3,z4,z5,z40]),(0,[z1,z1426,z3,z8,z5,z6]),(0,[z479,z1,z3,z15,z5,z6]),(0,[z531,z1,z50,z8,z5,z6]),(0,[z1015,z1,z115,z8,z5,z6]),(0,[z1,z2,z1427,z8,z5,z6]),(0,[z1,z1428,z3,z8,z5,z6])],[(0,[z1,z434,z3,z165,z5,z6]),(0,[z1,z1429,z3,z8,z5,z6]),(0,[z1210,z3,z50,z8,z5,z6]),(0,[z1430,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z1431,z5,z6]),(0,[z128,z1,z2,z15,z5,z153]),(0,[z0,z1,z3,z305,z5,z6]),(0,[z1,z1432,z3,z8,z5,z6]),(0,[z1,z2,z1433,z8,z5,z6]),(0,[z1,z1434,z3,z8,z5,z6])],[(0,[z39,z2,z3,z4,z5,z6]),(0,[z1,z1435,z3,z8,z5,z6]),(0,[z2,z3,z8,z5,z813,z6]),(0,[z414,z1,z3,z427,z5,z6]),(0,[z1,z60,z193,z32,z5,z6]),(0,[z1,z3,z801,z8,z5,z6])]],
   [[(0,[z46,z405,z3,z8,z5,z6]),(0,[z2,z3,z576,z4,z41,z6]),(0,[z1,z1436,z3,z8,z5,z6]),(0,[z1216,z3,z50,z8,z5,z6]),(0,[z848,z1,z3,z8,z5,z6]),(0,[z80,z1,z2,z3,z5,z208])],[(0,[z2,z3,z63,z8,z172,z6]),(0,[z1,z1125,z3,z8,z5,z6]),(0,[z2,z3,z4,z5,z258,z6]),(0,[z1,z3,z478,z15,z5,z6]),(0,[z0,z1,z3,z8,z5,z915]),(0,[z464,z2,z3,z106,z5,z6]),(0,[z338,z2,z3,z219,z5,z6])],[(0,[z2,z3,z4,z5,z6,z10]),(0,[z168,z2,z3,z15,z5,z6]),(0,[z1,z1048,z3,z50,z5,z6]),(0,[z1219,z3,z50,z8,z5,z6]),(0,[z1,z2,z81,z8,z5,z254])],[(0,[z1,z167,z3,z8,z5,z6]),(0,[z1,z418,z50,z8,z5,z6]),(0,[z2,z3,z4,z5,z265,z6]),(0,[z1,z2,z3,z1437,z5,z6])],[(0,[z1,z379,z3,z4,z5,z6]),(0,[z1,z180,z3,z15,z5,z6]),(0,[z180,z3,z8,z5,z41,z6]),(0,[z1,z1438,z3,z8,z5,z6])],[(0,[z0,z36,z3,z8,z5,z6]),(0,[z1,z341,z3,z8,z5,z159]),(0,[z1,z2,z3,z1439,z5,z6])],[(0,[z78,z1,z50,z4,z5,z6]),(0,[z53,z1,z3,z8,z856,z6]),(0,[z1,z2,z3,z1440,z5,z6]),(0,[z1,z1441,z3,z8,z5,z6]),(0,[z80,z1,z62,z3,z5,z6]),(0,[z1,z1442,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1443])],[(0,[z1,z3,z880,z8,z5,z6]),(0,[z692,z3,z23,z8,z5,z6]),(0,[z2,z3,z320,z4,z5,z6]),(0,[z183,z2,z3,z320,z5,z6]),(0,[z34,z2,z3,z15,z5,z70]),(0,[z1,z2,z3,z1444,z5,z6]),(0,[z1,z2,z3,z8,z5,z1445]),(0,[z1,z2,z108,z8,z5,z6]),(0,[z244,z1,z50,z8,z5,z153])],[(0,[z1446,z1,z3,z8,z5,z6]),(0,[z1,z1447,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z1448]),(0,[z1,z2,z516,z8,z5,z71])],[(0,[z39,z2,z79,z4,z5,z6]),(0,[z161,z2,z63,z8,z5,z6]),(0,[z557,z2,z3,z4,z5,z6]),(0,[z1,z2,z1170,z8,z5,z6]),(0,[z424,z2,z3,z8,z41,z6]),(0,[z110,z2,z130,z3,z5,z6])],[(0,[z1,z2,z136,z15,z5,z6]),(0,[z2,z3,z125,z4,z5,z6]),(0,[z1,z2,z3,z121,z5,z6]),(0,[z2,z3,z4,z5,z6,z282]),(0,[z196,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z1449,z5,z6]),(0,[z1,z2,z3,z8,z5,z1450])],[(0,[z78,z2,z79,z352,z5,z6]),(0,[z1,z2,z115,z8,z5,z27]),(0,[z479,z1,z3,z398,z5,z6]),(0,[z262,z459,z1,z3,z5,z6])],[(0,[z1,z2,z3,z1451,z5,z6]),(0,[z0,z1,z612,z8,z5,z6]),(0,[z1,z3,z8,z5,z6,z1452])],[(0,[z2,z3,z352,z5,z41,z6]),(0,[z1,z2,z3,z1453,z5,z6]),(0,[z114,z2,z3,z121,z5,z10])],[(0,[z1,z2,z1139,z8,z5,z6]),(0,[z1137,z1,z3,z15,z5,z6]),(0,[z1,z50,z8,z5,z383,z6]),(0,[z1,z2,z3,z8,z5,z975]),(0,[z1454,z2,z3,z8,z5,z6]),(0,[z417,z1,z2,z8,z5,z153])],[(0,[z1,z2,z3,z1277,z5,z6]),(0,[z1,z2,z8,z5,z6,z786]),(0,[z34,z2,z3,z376,z5,z70]),(0,[z1,z421,z3,z50,z5,z6]),(0,[z0,z110,z3,z8,z5,z6]),(0,[z1455,z2,z3,z8,z5,z6]),(0,[z80,z1,z2,z3,z5,z256])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 479) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 479).take 485) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 964).take 481) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1445).take 55) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1500)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [479, 485, 481, 55] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 76).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 76).take 76).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 152).take 93).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 245).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 336).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 434).take 78).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [76, 76, 93, 91, 98, 78] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

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

end PEqualNP.Outside.L_meta_36240

theorem PEqualNP.Outside.L_meta_36240 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4272618152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4272618152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36240.solve