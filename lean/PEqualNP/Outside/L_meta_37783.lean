import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37783

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

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
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

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
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
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
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
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
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

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
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
  Nat.testBit (4277071598 * 2 ^ 32 + 4209568392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
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
  [(0x50001008810d0950#64 ++ 0x050001008810d095#64 ++ 0xec053499871f1fff#64 ++ 0xfec053499871f1ff#64 : BitVec 256),
   (0x20084122446264a0#64 ++ 0x420084122446264a#64 ++ 0xde1acb6644e3e4fd#64 ++ 0xfde1acb6644e3e4f#64 : BitVec 256),
   (0x41630c7818b4b8c4#64 ++ 0x141630c7818b4b8c#64 ++ 0xb9e30c7878fcf8cf#64 ++ 0xab9e30c7878fcf8c#64 : BitVec 256),
   (0x80bc0f806e00d606#64 ++ 0x980bc0f806e00d60#64 ++ 0x79fc0f807f00ff0b#64 ++ 0x679fc0f807f00ff0#64 : BitVec 256),
   (0x02dff00077db0008#64 ++ 0xe02dff00077db000#64 ++ 0xfbfff0007fff0007#64 ++ 0x1fbfff0007fff000#64 : BitVec 256),
   (0x00f7aed50000000f#64 ++ 0x000f7aed50000000#64 ++ 0xfeffffff80000000#64 ++ 0xffeffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [6, 12]⟩, ⟨.and, [11, 9]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00200ed500000007 0x000200ed50000000 0x04000fff80000000 0xe04000fff8000000

def z1 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff80000000 0xffeffffff8000000

def z2 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff0007fff0007 0x1fbfff0007fff000

def z3 : W := mkw 0x20084122446264a0 0x420084122446264a 0xde1acb6644e3e4fd 0xfde1acb6644e3e4f

def z4 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xb9e30c7878fcf8cf 0xab9e30c7878fcf8c

def z5 : W := mkw 0x50001008810d0950 0x050001008810d095 0xec053499871f1fff 0xfec053499871f1ff

def z6 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x79fc0f807f00ff0b 0x679fc0f807f00ff0

def z7 : W := mkw 0x02fffed577db000f 0xe02fffed577db000 0xffffffffffff0007 0xfffffffffffff000

def z8 : W := mkw 0x00200c5000000004 0x000200c500000000 0x00000c7800000000 0xa00000c780000000

def z9 : W := mkw 0x20084122446264a0 0x420084122446264a 0x0000000044e3e4fd 0x00000000044e3e4f

def z10 : W := mkw 0x90bc1f80ef09d716 0x990bc1f80ef09d71 0x7dfc3f81ff03ff3b 0x77dfc3f81ff03ff3

def z11 : W := mkw 0x206b4d72446264a4 0x4206b4d72446264a 0xfefbcf7e44e3e4fd 0xffefbcf7e44e3e4f

def z12 : W := mkw 0x80b40f802a00d606 0x980b40f802a00d60 0x21e40f803b00ff0a 0x621e40f803b00ff0

def z13 : W := mkw 0x41200c5808049844 0x141200c580804984 0x0000041800001800 0x0000004180000180

def z14 : W := mkw 0x0043000010900000 0x0004300001090000 0xb9e3000078fc0007 0x0b9e3000078fc000

def z15 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x00000c780000f8c8 0xa00000c780000f8c

def z16 : W := mkw 0x0000100001090000 0x0000010000109000 0xe8053000071f0007 0x1e8053000071f000

def z17 : W := mkw 0x5000000880040950 0x0500000088004095 0x0400049980001ff8 0xe0400049980001ff

def z18 : W := mkw 0x20084122446264a0 0x420084122446264a 0xda1acb6644e3e005 0x1da1acb6644e3e00

def z19 : W := mkw 0x009c000066000000 0x8009c00006600000 0x79fc00007f000003 0x079fc00007f00000

def z20 : W := mkw 0x41630c5818949844 0x141630c581894984 0x39e10c18781cf80b 0x239e10c18781cf80

def z21 : W := mkw 0x01630c7018b0b084 0x101630c7018b0b08 0x11e2086078e0e000 0x011e2086078e0e00

def z22 : W := mkw 0x1000100081090110 0x0100010008109011 0x4404308187030730 0x5440430818703073

def z23 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0x461cf38780000000 0x5461cf3878000000

def z24 : W := mkw 0x4100002818b4b8c0 0x14100002818b4b8c 0x0100000078fcf8cf 0x00100000078fcf8c

def z25 : W := mkw 0x41f70ef818b4b8c6 0x141f70ef818b4b8c 0xf9ff0ff878fcf8cf 0xef9ff0ff878fcf8c

def z26 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z27 : W := mkw 0xa0bc4f826e42d626 0xda0bc4f826e42d62 0x7ffccf867f03ff3b 0x77ffccf867f03ff3

def z28 : W := mkw 0x50001008810d0950 0x050001008810d095 0xe8053000071f1fff 0x1e8053000071f1ff

def z29 : W := mkw 0x52085008f7df0950 0xe52085008f7df095 0xed053499ffff1fff 0xfed053499ffff1ff

def z30 : W := mkw 0x22dff12277fb64a8 0xe22dff12277fb64a 0xfbfff0007fffe4ff 0x1fbfff0007fffe4f

def z31 : W := mkw 0x0008400044420000 0x4000840004442000 0xda1ac00044e30005 0x1da1ac00044e3000

def z32 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000000000004f8 0xe04000000000004f

def z33 : W := mkw 0x80ff0f807e90d606 0x980ff0f807e90d60 0xf9ff0f807ffcff0f 0x6f9ff0f807ffcff0

def z34 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffff499ffff0007 0xffffff499ffff000

def z35 : W := mkw 0x80200f800800d606 0x180200f800800d60 0x00000f800000ff08 0x600000f800000ff0

def z36 : W := mkw 0x80b40e802a009206 0x980b40e802a00920 0x39e40c807b00fb0b 0x239e40c807b00fb0

def z37 : W := mkw 0xc1f70ed83a949a46 0x9c1f70ed83a949a4 0x21e504983b1c1b02 0x021e504983b1c1b0

def z38 : W := mkw 0x4143002818b4b8c0 0x14143002818b4b8c 0xb9e3000078fcf8cf 0x0b9e3000078fcf8c

def z39 : W := mkw 0x50201edd810d0957 0x050201edd810d095 0xec053fff871f1fff 0xfec053fff871f1ff

def z40 : W := mkw 0x809c03806e00d602 0x9809c03806e00d60 0x411c03807f00ff0b 0x4411c03807f00ff0

def z41 : W := mkw 0x0000000000000000 0x0000000000000000 0xec05349980000000 0xfec0534998000000

def z42 : W := mkw 0x80bc4f806e42d606 0xd80bc4f806e42d60 0xfbfecf807fe3ff0f 0x7fbfecf807fe3ff0

def z43 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc000000040304fd 0xfcc000000040304f

def z44 : W := mkw 0x2008410244424420 0x4200841024442442 0x5e18cb064403e439 0x75e18cb064403e43

def z45 : W := mkw 0x52dff008f7df0958 0xe52dff008f7df095 0xfbfff0007fff1fff 0x1fbfff0007fff1ff

def z46 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x11f80b007800e000 0x011f80b007800e00

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0x88000000000000cd 0xa88000000000000c

def z48 : W := mkw 0x41630c5818949844 0x141630c581894984 0x21e10418381c1802 0x021e10418381c180

def z49 : W := mkw 0x616b4d7a5cf6fce4 0x5616b4d7a5cf6fce 0xfffbcf7e7cfffcff 0xffffbcf7e7cfffcf

def z50 : W := mkw 0x50001008810d0950 0x050001008810d095 0x84013019801f00f4 0x984013019801f00f

def z51 : W := mkw 0x229cf102674b4428 0xe229cf102674b442 0x461cf30607030430 0x5461cf3060703043

def z52 : W := mkw 0x22dff12277fb64a8 0xe22dff12277fb64a 0xfffffb667fffe4ff 0xffffffb667fffe4f

def z53 : W := mkw 0x229cf122676b64a8 0xe229cf122676b64a 0xde1efb6647e3e4fd 0xfde1efb6647e3e4f

def z54 : W := mkw 0x02f7fed511db000f 0x602f7fed511db000 0xfeffffff80ff0004 0xffeffffff80ff000

def z55 : W := mkw 0x00b40e8000000006 0x000b40e800000000 0x78fc0f8000000000 0x678fc0f800000000

def z56 : W := mkw 0x80ffafd56e00d60f 0x980ffafd56e00d60 0xffffffffff00ff0b 0xfffffffffff00ff0

def z57 : W := mkw 0x4143007810b428c0 0x04143007810b428c 0x8003007800fc00c4 0x88003007800fc00c

def z58 : W := mkw 0xa0bc4fa26e62f6a6 0xda0bc4fa26e62f6a 0xfffecfe67fe3ffff 0xffffecfe67fe3fff

def z59 : W := mkw 0x1000100081090110 0x0100010008109011 0x0400300180030030 0x1040030018003003

def z60 : W := mkw 0xd0bc1f88ef0ddf56 0x9d0bc1f88ef0ddf5 0xfdfd3f99ff1fffff 0xffdfd3f99ff1ffff

def z61 : W := mkw 0x4363fc7819ffb8cc 0x74363fc7819ffb8c 0xbbe3fc7878fff8cf 0xbbbe3fc7878fff8c

def z62 : W := mkw 0x10f7bed58109011f 0x010f7bed58109011 0xfeffffff87030730 0xffeffffff8703073

def z63 : W := mkw 0x00f70ed000000006 0x000f70ed00000000 0xf8ff0ff800000000 0xef8ff0ff80000000

def z64 : W := mkw 0xa0284fa24c62f6a6 0x5a0284fa24c62f6a 0xde1acfe644e3fffd 0xfde1acfe644e3fff

def z65 : W := mkw 0x4143005810940840 0x0414300581094084 0x00010018001c0000 0x000010018001c000

def z66 : W := mkw 0x20084122446264a0 0x420084122446264a 0x121acb6640e0e000 0x0121acb6640e0e00

def z67 : W := mkw 0x20084122446264a0 0x420084122446264a 0x961acb6640e3e0f4 0x9961acb6640e3e0f

def z68 : W := mkw 0x0000100001090000 0x0000010000109000 0x20053000031c0002 0x020053000031c000

def z69 : W := mkw 0x20084122446264a0 0x420084122446264a 0x4618cb660403e4f8 0xf4618cb660403e4f

def z70 : W := mkw 0xa09c43a2666266a2 0xca09c43a2666266a 0xde1ecbe647e3e7fd 0xfde1ecbe647e3e7f

def z71 : W := mkw 0x02dff28577db000b 0xe02dff28577db000 0xfffff387ffff0007 0x5fffff387ffff000

def z72 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x12facb6600000000 0x012facb660000000

def z73 : W := mkw 0x50001008810d0950 0x050001008810d095 0x00000000071f1fff 0x000000000071f1ff

def z74 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xfde30c787cfffcff 0xffde30c787cfffcf

def z75 : W := mkw 0x80b40e802a009206 0x980b40e802a00920 0x69e404803f001f0b 0x669e404803f001f0

def z76 : W := mkw 0x00200c200820b084 0x100200c200820b08 0xb9e20c6078e0f8cf 0xab9e20c6078e0f8c

def z77 : W := mkw 0x82fffe807fdb920e 0xf82fffe807fdb920 0xfbfff4807fff1b07 0x1fbfff4807fff1b0

def z78 : W := mkw 0x41f7aedd1894984f 0x141f7aedd1894984 0x21e53499b81c1802 0x021e53499b81c180

def z79 : W := mkw 0x5100102899bdb9d0 0x15100102899bdb9d 0x010000007fffffff 0x0010000007ffffff

def z80 : W := mkw 0x43fffc787fffb8cc 0xf43fffc787fffb8c 0xfbfffc787ffff8cf 0xbfbfffc787ffff8c

def z81 : W := mkw 0x20004022006220a0 0x420004022006220a 0x8602c06600e300f4 0x98602c06600e300f

def z82 : W := mkw 0x0043a05500000009 0x00043a0550000000 0xde1bfb7f80000000 0xfde1bfb7f8000000

def z83 : W := mkw 0x20084122446264a0 0x420084122446264a 0x561acb6644e3e430 0x5561acb6644e3e43

def z84 : W := mkw 0x00200c0008009004 0x100200c000800900 0x39e00c007800f80b 0x239e00c007800f80

def z85 : W := mkw 0xc1ff0ff87eb4fec6 0x9c1ff0ff87eb4fec 0xf9ff0ff87ffcffcf 0xef9ff0ff87ffcffc

def z86 : W := mkw 0x5143107891bd29d0 0x05143107891bd29d 0x8403307980ff00f4 0x98403307980ff00f

def z87 : W := mkw 0x51631c7899bdb9d4 0x151631c7899bdb9d 0xfde73cf9ffffffff 0xffde73cf9fffffff

def z88 : W := mkw 0x0008000066000000 0x8000800006600000 0x010000007f000003 0x0010000007f00000

def z89 : W := mkw 0x80ffafd56e00d60f 0x980ffafd56e00d60 0x13facb667800e000 0x013facb667800e00

def z90 : W := mkw 0x0043a05500000009 0x00043a0550000000 0x8603f07f80000000 0x98603f07f8000000

def z91 : W := mkw 0x4163ac7d18b4b8cd 0x14163ac7d18b4b8c 0xbfe3fc7ff8fcf8cf 0xbbfe3fc7ff8fcf8c

def z92 : W := mkw 0x0000000000000000 0x0000000000000000 0xa8010000001c0007 0x0a8010000001c000

def z93 : W := mkw 0x0000000000000000 0x0000000000000000 0xde1acb6600000000 0xfde1acb660000000

def z94 : W := mkw 0x20ffeff7446264af 0x420ffeff7446264a 0xfeffffffc4e3e4fd 0xffeffffffc4e3e4f

def z95 : W := mkw 0x00f7aed51090000f 0x000f7aed51090000 0xfffffffff8fc0007 0xffffffffff8fc000

def z96 : W := mkw 0x0008400044420000 0x4000840004442000 0xde1ac00044e304fd 0xfde1ac00044e304f

def z97 : W := mkw 0x0043100011990000 0x0004310001199000 0xf9e730007fff0007 0x1f9e730007fff000

def z98 : W := mkw 0x4100002818b4b8c0 0x14100002818b4b8c 0x9902086078fcf8cf 0xa9902086078fcf8c

def z99 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x13fac0007fff0007 0x013fac0007fff000

def z100 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xfdfd3f99ff00ff0b 0xffdfd3f99ff00ff0

def z101 : W := mkw 0x51631c7899bdb9d4 0x151631c7899bdb9d 0xb9e30c787fffffff 0xab9e30c787ffffff

def z102 : W := mkw 0x20000122002064a0 0x020000122002064a 0x04000b660000e4f8 0xe04000b660000e4f

def z103 : W := mkw 0x00d7a00000000008 0x000d7a0000000000 0xfefffb6600000000 0xffefffb660000000

def z104 : W := mkw 0x0000000000000000 0x0000000000000000 0x6804048007001f0b 0x66804048007001f0

def z105 : W := mkw 0x430850287fffb8c0 0xf430850287fffb8c 0x010000007ffff8cf 0x0010000007ffff8c

def z106 : W := mkw 0x0243f00011db0008 0x60243f00011db000 0xbbe3f00078ff0007 0x1bbe3f00078ff000

def z107 : W := mkw 0x61ffefff5cf6fcef 0x561ffefff5cf6fce 0xfffffffffcfffcff 0xffffffffffcfffcf

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0x4404308180000000 0x5440430818000000

def z109 : W := mkw 0x52085008f7df0950 0xe52085008f7df095 0x010000007fff1fff 0x0010000007fff1ff

def z110 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xf9e70cf87ffcffcf 0xef9e70cf87ffcffc

def z111 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400049980000000 0xe040004998000000

def z112 : W := mkw 0x2008410244424420 0x4200841024442442 0x4618c30604030430 0x54618c3060403043

def z113 : W := mkw 0x82ffff807fdbd60e 0xf82ffff807fdbd60 0xfbffff807fffff0f 0x7fbffff807fffff0

def z114 : W := mkw 0x0000002000202080 0x0000000200020208 0x9802086040e0e0cd 0xa9802086040e0e0c

def z115 : W := mkw 0x800801006e00d600 0x9800801006e00d60 0x010000007f00ff0b 0x0010000007f00ff0

def z116 : W := mkw 0x02dfe00076d20008 0xe02dfe00076d2000 0xbbfbc00078fc0007 0x0bbfbc00078fc000

def z117 : W := mkw 0x02d7b00033990008 0xa02d7b0003399000 0x21e530003b1c0002 0x021e530003b1c000

def z118 : W := mkw 0x809c038066004602 0x8809c03806600460 0x401c038007000700 0x4401c03800700070

def z119 : W := mkw 0x0208500077db0000 0xe0208500077db000 0x010000007fff0007 0x0010000007fff000

def z120 : W := mkw 0x41200efd0824b8c7 0x141200efd0824b8c 0x04000fff8000f8c8 0xe04000fff8000f8c

def z121 : W := mkw 0x41f7aefd18b4b8cf 0x141f7aefd18b4b8c 0xfffffffff8fcf8cf 0xffffffffff8fcf8c

def z122 : W := mkw 0x20bc4fa2446264a6 0x420bc4fa2446264a 0xfefecfe644e3e4fd 0xffefecfe644e3e4f

def z123 : W := mkw 0x0243b00011990008 0x20243b0001199000 0x00013000001c0000 0x000013000001c000

def z124 : W := mkw 0x029cf000674b0008 0xe029cf000674b000 0x421cf00007030000 0x1421cf0000703000

def z125 : W := mkw 0x20085122456b64a0 0x420085122456b64a 0xfe1ffb6647ffe4ff 0xffe1ffb6647ffe4f

def z126 : W := mkw 0x024b500077db0000 0xe024b500077db000 0xb9e300007fff0007 0x0b9e300007fff000

def z127 : W := mkw 0x41f7aefd10b428cf 0x041f7aefd10b428c 0xfeffffff80fc00c4 0xffeffffff80fc00c

def z128 : W := mkw 0x51631c7899bdb9d4 0x151631c7899bdb9d 0xbde33c79f8fff8ff 0xbbde33c79f8fff8f

def z129 : W := mkw 0x20004022006220a0 0x420004022006220a 0xde1acb6600e300f4 0xfde1acb6600e300f

def z130 : W := mkw 0x00085000454b0000 0x400085000454b000 0xfa1ff00047ff0007 0x1fa1ff00047ff000

def z131 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xfffecfe67f00ff0b 0xffffecfe67f00ff0

def z132 : W := mkw 0x02d7f00011db0008 0x602d7f00011db000 0xfafff00000ff0004 0x1fafff00000ff000

def z133 : W := mkw 0x0200f000014b0008 0x60200f000014b000 0x0200f00000030000 0x10200f0000003000

def z134 : W := mkw 0x20004022006220a0 0x420004022006220a 0x0000000000e300f4 0x00000000000e300f

def z135 : W := mkw 0x809ca3856600460b 0x8809ca3856600460 0x461cf38787000700 0x5461cf3878700070

def z136 : W := mkw 0x40200c0808049844 0x140200c080804984 0xb9e10c18781cf8cf 0xab9e10c18781cf8c

def z137 : W := mkw 0x0043000010900000 0x0004300001090000 0x8003000000fc0004 0x08003000000fc000

def z138 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x11e2086078fcf8cf 0x011e2086078fcf8c

def z139 : W := mkw 0x224bf12255fb64a8 0x6224bf12255fb64a 0xde1bfb6644ffe4fd 0xfde1bfb6644ffe4f

def z140 : W := mkw 0x7000112a812d6df0 0x07000112a812d6df 0xec053fff871fffff 0xfec053fff871ffff

def z141 : W := mkw 0x02dff02077fb2088 0xe02dff02077fb208 0xfbfff8607fffe0cf 0xbfbfff8607fffe0c

def z142 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xb8e73cf980000000 0xab8e73cf98000000

def z143 : W := mkw 0x52dff008f7df0958 0xe52dff008f7df095 0xfffff499ffff1fff 0xffffff499ffff1ff

def z144 : W := mkw 0x00d7a00010900008 0x000d7a0001090000 0xfbfff00078fc0007 0x1fbfff00078fc000

def z145 : W := mkw 0x51630c7898b4b9d4 0x151630c7898b4b9d 0xbde30cf9f8fcffff 0xebde30cf9f8fcfff

def z146 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x79fc0b007f00e003 0x079fc0b007f00e00

def z147 : W := mkw 0x1000100081090110 0x0100010008109011 0xcc043081870307fd 0xfcc043081870307f

def z148 : W := mkw 0x0094a00000000008 0x00094a0000000000 0x421cf00000000000 0x1421cf0000000000

def z149 : W := mkw 0x00bc0e8066000006 0x800bc0e806600000 0x79fc0f807f000003 0x679fc0f807f00000

def z150 : W := mkw 0x50f7bedd810d095f 0x050f7bedd810d095 0xfeffffff871f1fff 0xffeffffff871f1ff

def z151 : W := mkw 0x029ce00066420008 0xe029ce0006642000 0x0218c00000000000 0x00218c0000000000

def z152 : W := mkw 0x0243f00011db0008 0x60243f00011db000 0x8203f00000ff0004 0x18203f00000ff000

def z153 : W := mkw 0x50001008810d0950 0x050001008810d095 0x20053499831c1b02 0x020053499831c1b0

def z154 : W := mkw 0x829cf380674b460a 0xe829cf380674b460 0x421cf38007030700 0x5421cf3800703070

def z155 : W := mkw 0x0000000000000000 0x0000000000000000 0xec05349987001f0b 0xfec05349987001f0

def z156 : W := mkw 0xc0bc0f886e04de46 0x9c0bc0f886e04de4 0xf9fd0f987f1cffcf 0xef9fd0f987f1cffc

def z157 : W := mkw 0x20084122446264a0 0x420084122446264a 0xda1ac00044e3e4fd 0x1da1ac00044e3e4f

def z158 : W := mkw 0x80280f804c00d606 0x180280f804c00d60 0x58180f804400ff09 0x658180f804400ff0

def z159 : W := mkw 0x7008512ac56f6df0 0x47008512ac56f6df 0xfe1fffffc7ffffff 0xffe1fffffc7fffff

def z160 : W := mkw 0xd2ffff88ffdfdf5e 0xfd2ffff88ffdfdf5 0xffffff99ffffffff 0xfffffff99fffffff

def z161 : W := mkw 0x0208500077db0000 0xe0208500077db000 0xe90530007fff0007 0x1e90530007fff000

def z162 : W := mkw 0x2008410244424420 0x4200841024442442 0xde1ac30644e30435 0x5de1ac30644e3043

def z163 : W := mkw 0x00200c0008009004 0x100200c000800900 0x21e0040038001802 0x021e004003800180

def z164 : W := mkw 0x4000000800040840 0x0400000080004084 0x80010018001c00c4 0x880010018001c00c

def z165 : W := mkw 0x02fffed577db000f 0xe02fffed577db000 0xfbfff499ffff0007 0x1fbfff499ffff000

def z166 : W := mkw 0x50001008810d0950 0x050001008810d095 0x44043081871f1fff 0x544043081871f1ff

def z167 : W := mkw 0x61200d7a0824fce4 0x161200d7a0824fce 0x04000f7e0000fcf8 0xe04000f7e0000fcf

def z168 : W := mkw 0x00b40e8000000006 0x000b40e800000000 0x78fc0f8007001f0b 0x678fc0f8007001f0

def z169 : W := mkw 0x0000000010900000 0x0000000001090000 0x0100000078fc0007 0x00100000078fc000

def z170 : W := mkw 0x0000002000202080 0x0000000200020208 0xde1acb6640e0e0cd 0xfde1acb6640e0e0c

def z171 : W := mkw 0x80bcaf856e00d60f 0x980bcaf856e00d60 0x7ffcff87ff00ff0b 0x77ffcff87ff00ff0

def z172 : W := mkw 0x0000000008009000 0x1000000000800900 0x010000007800f80b 0x0010000007800f80

def z173 : W := mkw 0x809c038066004602 0x8809c03806600460 0x79fc03807f000703 0x479fc03807f00070

def z174 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x401c0f800700ff08 0x6401c0f800700ff0

def z175 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x66fdf79f80000000 0x566fdf79f8000000

def z176 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x59f80b007c00e409 0x659f80b007c00e40

def z177 : W := mkw 0x80f7aed52a00920f 0x980f7aed52a00920 0x21e53499bb001b02 0x021e53499bb001b0

def z178 : W := mkw 0x02dff05577db0009 0xe02dff05577db000 0xfffff07fffff0007 0x9fffff07fffff000

def z179 : W := mkw 0x0000002000202080 0x0000000200020208 0xdc02086044e3e4fd 0xfdc02086044e3e4f

def z180 : W := mkw 0x00200c0008009004 0x100200c000800900 0x11e008007800e000 0x011e008007800e00

def z181 : W := mkw 0xc1ff0ff87eb4fec6 0x9c1ff0ff87eb4fec 0xb9fb0f7878fcf8cf 0xab9fb0f7878fcf8c

def z182 : W := mkw 0xc3fffff87ffffece 0xfc3fffff87ffffec 0xfbfffff87fffffcf 0xffbfffff87fffffc

def z183 : W := mkw 0x50001008810d0950 0x050001008810d095 0x64053499871f1f32 0x564053499871f1f3

def z184 : W := mkw 0x80200e8008009206 0x180200e800800920 0x0000048000001b00 0x00000048000001b0

def z185 : W := mkw 0x00b4aed50000000f 0x000b4aed50000000 0x461cffff80000000 0xf461cffff8000000

def z186 : W := mkw 0x51631c58999d9954 0x151631c58999d995 0xede53499bf1f1fff 0xfede53499bf1f1ff

def z187 : W := mkw 0x80200f800800d606 0x180200f800800d60 0x00000b000000e000 0x000000b000000e00

def z188 : W := mkw 0x02dfe00076d20008 0xe02dfe00076d2000 0x13fac00078e00000 0x013fac00078e0000

def z189 : W := mkw 0xa0bc4fa26e62f6a6 0xda0bc4fa26e62f6a 0x13facb6678e0e000 0x013facb6678e0e00

def z190 : W := mkw 0x4000000800040840 0x0400000080004084 0x00000000001c18cf 0x000000000001c18c

def z191 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xfde73cf9f8fcf8cf 0xffde73cf9f8fcf8c

def z192 : W := mkw 0x02d7f00033db0008 0xe02d7f00033db000 0xa3e7f0003bff0006 0x1a3e7f0003bff000

def z193 : W := mkw 0x61634c7a18f6b8e4 0x561634c7a18f6b8e 0xbfe3cc7e78fff8ff 0xbbfe3cc7e78fff8f

def z194 : W := mkw 0x7008512ac56f6df0 0x47008512ac56f6df 0xde1bfb7fc4ffe4fd 0xfde1bfb7fc4ffe4f

def z195 : W := mkw 0x50001008810d0950 0x050001008810d095 0xec053499831c1b02 0xfec053499831c1b0

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0x39e0000078000003 0x039e000007800000

def z197 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xfdfc0f807f03ffff 0xffdfc0f807f03fff

def z198 : W := mkw 0x1000100081090110 0x0100010008109011 0xec05349987030730 0xfec0534998703073

def z199 : W := mkw 0x81ff0ff07eb0f686 0x981ff0ff07eb0f68 0x79fe0fe07fe0ff0b 0x679fe0fe07fe0ff0

def z200 : W := mkw 0x50201c08890d9954 0x150201c08890d995 0xfde53c99ff1fffff 0xffde53c99ff1ffff

def z201 : W := mkw 0x436b5c787fffb8c4 0xf436b5c787fffb8c 0xb9e30c787ffff8cf 0xab9e30c787ffff8c

def z202 : W := mkw 0x02ffeed576d2000f 0xe02ffeed576d2000 0xfffffffff8e00000 0xffffffffff8e0000

def z203 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x31e30c7878fcf802 0x031e30c7878fcf80

def z204 : W := mkw 0x20ffeff7446264af 0x420ffeff7446264a 0xdefacb6644e3e4fd 0xfdefacb6644e3e4f

def z205 : W := mkw 0x80b40e802a009206 0x980b40e802a00920 0x01e0000038000000 0x001e000003800000

def z206 : W := mkw 0x00630c0018909004 0x100630c001890900 0xb9e30c0078fcf80f 0x2b9e30c0078fcf80

def z207 : W := mkw 0x00200c0008009004 0x100200c000800900 0x00000c000000f808 0x200000c000000f80

def z208 : W := mkw 0x41631c7819bdb8c4 0x141631c7819bdb8c 0xf9e73c787ffff8cf 0xbf9e73c787ffff8c

def z209 : W := mkw 0x209c4122666264a0 0xc209c4122666264a 0xfffecb667fe3e4ff 0xffffecb667fe3e4f

def z210 : W := mkw 0x50f7bedd810d095f 0x050f7bedd810d095 0xfeffffff801f00f4 0xffeffffff801f00f

def z211 : W := mkw 0x0243f00011db0008 0x60243f00011db000 0xea07f00007ff0007 0x1ea07f00007ff000

def z212 : W := mkw 0x02085000674b0000 0xe02085000674b000 0x0000000007030000 0x0000000000703000

def z213 : W := mkw 0x50001008810d0950 0x050001008810d095 0x68040480071f1fff 0x668040480071f1ff

def z214 : W := mkw 0x00ffafd54400440f 0x000ffafd54400440 0xfeffffffc400e409 0xffeffffffc400e40

def z215 : W := mkw 0x0000000000000000 0x0000000000000000 0x9802086000000000 0xa980208600000000

def z216 : W := mkw 0x20084122446264a0 0x420084122446264a 0x8602c06644e3e4fd 0x98602c06644e3e4f

def z217 : W := mkw 0x20dfe122446264a8 0x420dfe122446264a 0xfefffb6644e3e4fd 0xffefffb6644e3e4f

def z218 : W := mkw 0x00d7a00000000008 0x000d7a0000000000 0x20e5300000000000 0x020e530000000000

def z219 : W := mkw 0x7000502a816f29f0 0x47000502a816f29f 0x8603f07f80ff00f4 0x98603f07f80ff00f

def z220 : W := mkw 0x0043005000000000 0x0004300500000000 0x8003007800000000 0x8800300780000000

def z221 : W := mkw 0x416b4c785cf6b8c4 0x5416b4c785cf6b8c 0xfbfbcc787cfff8cf 0xbfbfbcc787cfff8c

def z222 : W := mkw 0x20000122002064a0 0x020000122002064a 0x00000b660000e000 0x000000b660000e00

def z223 : W := mkw 0x0008010044004400 0x0000801004400440 0x10180b004000e000 0x010180b004000e00

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0x280004000000180b 0x2280004000000180

def z225 : W := mkw 0x00b40e8008009006 0x100b40e800800900 0x79fc0f807800f80b 0x679fc0f807800f80

def z226 : W := mkw 0x22dfe12276f264a8 0xe22dfe12276f264a 0xdffacb667ce3e4fd 0xfdffacb667ce3e4f

def z227 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x32ffffff80000000 0x032ffffff8000000

def z228 : W := mkw 0x50001008810d0950 0x050001008810d095 0x68053499871c1f0b 0x668053499871c1f0

def z229 : W := mkw 0x809c01006e00d600 0x9809c01006e00d60 0x79fc00007f00ff0b 0x079fc00007f00ff0

def z230 : W := mkw 0x00200c0000000004 0x000200c000000000 0x38e00c0000000000 0x238e00c000000000

def z231 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x91e3087878fce0c4 0x891e3087878fce0c

def z232 : W := mkw 0xa2ffffa27ffbf6ae 0xfa2ffffa27ffbf6a 0xffffffe67fffffff 0xfffffffe67ffffff

def z233 : W := mkw 0x0043000010900000 0x0004300001090000 0x11e2000078e00000 0x011e2000078e0000

def z234 : W := mkw 0x41f7aefd0824b8cf 0x141f7aefd0824b8c 0xfeffffff8000f8c8 0xffeffffff8000f8c

def z235 : W := mkw 0x0008010044004400 0x0000801004400440 0x58180b004400e409 0x658180b004400e40

def z236 : W := mkw 0x80b40e802a009206 0x980b40e802a00920 0x21e404803b001b02 0x021e404803b001b0

def z237 : W := mkw 0x4100002818b4b8c0 0x14100002818b4b8c 0xa901041878fcf8cf 0xaa901041878fcf8c

def z238 : W := mkw 0x51201c78892db9d4 0x151201c78892db9d 0xec053cf9871fffff 0xfec053cf9871ffff

def z239 : W := mkw 0x50001008810d0950 0x050001008810d095 0xec053019871f00f7 0x9ec053019871f00f

def z240 : W := mkw 0x7008510ac54f4d70 0x47008510ac54f4d7 0xee1df79f871f1fff 0xfee1df79f871f1ff

def z241 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe1fffff80000000 0xffe1fffff8000000

def z242 : W := mkw 0x20084122446264a0 0x420084122446264a 0xfe1ecfe647e3ffff 0xffe1ecfe647e3fff

def z243 : W := mkw 0x5000000880040950 0x0500000088004095 0xec05349980001ff8 0xfec05349980001ff

def z244 : W := mkw 0x5094b28d810d095b 0x05094b28d810d095 0xee1df79f871f1fff 0xfee1df79f871f1ff

def z245 : W := mkw 0x800801006e00d600 0x9800801006e00d60 0x010000007800e000 0x0010000007800e00

def z246 : W := mkw 0x40f7aedd0004084f 0x040f7aedd0004084 0xfeffffff801c18cf 0xffeffffff801c18c

def z247 : W := mkw 0x2043e077006220a9 0x42043e077006220a 0x8603f07f80e300f4 0x98603f07f80e300f

def z248 : W := mkw 0x00630c5000000004 0x000630c500000000 0xb8e30c7800000000 0xab8e30c780000000

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x180008004000e009 0x2180008004000e00

def z250 : W := mkw 0x0000000000000000 0x0000000000000000 0x6804048000000000 0x6680404800000000

def z251 : W := mkw 0x20084122446264a0 0x420084122446264a 0xcc00000044e3e4fd 0xfcc00000044e3e4f

def z252 : W := mkw 0x20284d224c62f4a4 0x520284d224c62f4a 0xfffacf667ce3fcff 0xffffacf667ce3fcf

def z253 : W := mkw 0x00d7a00000000008 0x000d7a0000000000 0xfafff00000000000 0x1fafff0000000000

def z254 : W := mkw 0x0000000000000000 0x0000000000000000 0x4618c30600000000 0x54618c3060000000

def z255 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000048000001f08 0x60000048000001f0

def z256 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x24e53fff80000000 0xe24e53fff8000000

def z257 : W := mkw 0x20000122002064a0 0x020000122002064a 0xcc000b660403e4fd 0xfcc000b660403e4f

def z258 : W := mkw 0x0000000000000000 0x0000000000000000 0x4400000004030430 0x5440000000403043

def z259 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x33fff0007bfc0002 0x033fff0007bfc000

def z260 : W := mkw 0xa00841226e62f6a0 0xda00841226e62f6a 0x010000007fe3ffff 0x0010000007fe3fff

def z261 : W := mkw 0x4000000800040840 0x0400000080004084 0xa8010418001c18cf 0xaa8010418001c18c

def z262 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xc21ff00007ff0004 0x1c21ff00007ff000

def z263 : W := mkw 0xc10801287eb4fec0 0x9c10801287eb4fec 0x010000007ffcffcf 0x0010000007ffcffc

def z264 : W := mkw 0x61284d7a4c66fce4 0x561284d7a4c66fce 0xde1acf7e44e3fcfd 0xfde1acf7e44e3fcf

def z265 : W := mkw 0x00dfe00044420008 0x400dfe0004442000 0xfafff00044e30005 0x1fafff00044e3000

def z266 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfafff49980000000 0x1fafff4998000000

def z267 : W := mkw 0x004b400054d20000 0x4004b400054d2000 0xfbfbc0007cff0007 0x1fbfbc0007cff000

def z268 : W := mkw 0x20004022006220a0 0x420004022006220a 0xce02c06604e304fd 0xfce02c06604e304f

def z269 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x20e5349980000000 0x020e534998000000

def z270 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800000004030005 0x1c80000000403000

def z271 : W := mkw 0xd0b41e88ab0d9b56 0x9d0b41e88ab0d9b5 0xede53499bf1f1fff 0xfede53499bf1f1ff

def z272 : W := mkw 0x50001008810d0950 0x050001008810d095 0x20053499871f1fff 0x020053499871f1ff

def z273 : W := mkw 0x80200f800800d606 0x180200f800800d60 0x68040f800700ff0b 0x668040f800700ff0

def z274 : W := mkw 0x22dff10277db4428 0xe22dff10277db442 0xfffff3067fff0437 0x5fffff3067fff043

def z275 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x31fc0f807b00fb02 0x031fc0f807b00fb0

def z276 : W := mkw 0xc1200ff80824fec6 0x1c1200ff80824fec 0x00000ff80000ffc8 0xe00000ff80000ffc

def z277 : W := mkw 0x41630c5818949844 0x141630c581894984 0xb9e3041878fc1807 0x0b9e3041878fc180

def z278 : W := mkw 0x52d7b008b39d0958 0xa52d7b008b39d095 0x21e53499bb1c1b02 0x021e53499bb1c1b0

def z279 : W := mkw 0x009c100067090000 0x8009c10006709000 0xf9fd30007f1f0007 0x1f9fd30007f1f000

def z280 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xfffbcf7e78fcf8cf 0xffffbcf7e78fcf8c

def z281 : W := mkw 0x4100000818949840 0x1410000081894984 0x01000000381c1802 0x001000000381c180

def z282 : W := mkw 0x204b412254f264a0 0x4204b412254f264a 0xfffbcb667cffe4ff 0xffffbcb667cffe4f

def z283 : W := mkw 0x80ffaf806e00d60e 0x980ffaf806e00d60 0xfbffff807f00ff0b 0x7fbffff807f00ff0

def z284 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff840304fd 0xffeffffff840304f

def z285 : W := mkw 0x50001008810d0950 0x050001008810d095 0xcc000000071f1fff 0xfcc000000071f1ff

def z286 : W := mkw 0x52d7b008b39d0958 0xa52d7b008b39d095 0xede53499bf1f1fff 0xfede53499bf1f1ff

def z287 : W := mkw 0x02d7b00033990008 0xa02d7b0003399000 0xe9e530003f1f0007 0x1e9e530003f1f000

def z288 : W := mkw 0x01f7aef518b0b08f 0x101f7aef518b0b08 0xfffffffff8e0e000 0xffffffffff8e0e00

def z289 : W := mkw 0x0000002000202080 0x0000000200020208 0x0000000040e0e0cd 0x00000000040e0e0c

def z290 : W := mkw 0x0043000010900000 0x0004300001090000 0x21e10000381c0002 0x021e10000381c000

def z291 : W := mkw 0x009c000066000000 0x8009c00006600000 0x79fc04807f001f0b 0x679fc04807f001f0

def z292 : W := mkw 0x029cf000674b0008 0xe029cf000674b000 0xda1ef00047e30005 0x1da1ef00047e3000

def z293 : W := mkw 0x80b40e802a009206 0x980b40e802a00920 0x79fc0f803b001b02 0x679fc0f803b001b0

def z294 : W := mkw 0x00ffaed56600000f 0x800ffaed56600000 0xffffffffff000003 0xfffffffffff00000

def z295 : W := mkw 0x7000502a816f29f0 0x47000502a816f29f 0xee07f4ff87ff1fff 0xfee07f4ff87ff1ff

def z296 : W := mkw 0x029cf285674b000b 0xe029cf285674b000 0x461cf38787030000 0x5461cf3878703000

def z297 : W := mkw 0x80280d006e00d604 0x980280d006e00d60 0x39e00c007f00ff0b 0x239e00c007f00ff0

def z298 : W := mkw 0x41f7aefd18b4b8cf 0x141f7aefd18b4b8c 0xbbfbcf7e78fcf8cf 0xabbfbcf7e78fcf8c

def z299 : W := mkw 0x50b41e88810d0956 0x050b41e88810d095 0xfcfd3f99871f1fff 0xffcfd3f99871f1ff

def z300 : W := mkw 0x82ffbf807f99d60e 0xb82ffbf807f99d60 0x79fd3f807f1cff0b 0x679fd3f807f1cff0

def z301 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffff0007fff04ff 0xffffff0007fff04f

def z302 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000040304fd 0x000000000040304f

def z303 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x11f80b007f00ff0b 0x011f80b007f00ff0

def z304 : W := mkw 0x1094b2858109011b 0x01094b2858109011 0x461cf38787030730 0x5461cf3878703073

def z305 : W := mkw 0x0000000000000000 0x0000000000000000 0xec04048007031fff 0xfec04048007031ff

def z306 : W := mkw 0x0008000044000000 0x0000800004400000 0x5818000044000001 0x0581800004400000

def z307 : W := mkw 0x716b5d7addfffdf4 0x5716b5d7addfffdf 0xffffffffffffffff 0xffffffffffffffff

def z308 : W := mkw 0x52dff008f7df0958 0xe52dff008f7df095 0xfffff019ffff00f7 0x9fffff019ffff00f

def z309 : W := mkw 0x0000000000000000 0x0000000000000000 0x6804000007000003 0x0680400000700000

def z310 : W := mkw 0x1000100081090110 0x0100010008109011 0x0004308183000300 0x0000430818300030

def z311 : W := mkw 0x0000a00500000009 0x00000a0050000000 0x0600f00780000000 0x10600f0078000000

def z312 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000007001f0b 0x00000000007001f0

def z313 : W := mkw 0x129cf000e74b0118 0xe129cf000e74b011 0x461cf08187030730 0x5461cf0818703073

def z314 : W := mkw 0x7008512ac56f6df0 0x47008512ac56f6df 0x0000000047ffffff 0x00000000047fffff

def z315 : W := mkw 0x50001008810d0950 0x050001008810d095 0xc4053099871f07f4 0xdc4053099871f07f

def z316 : W := mkw 0x800801006e00d600 0x9800801006e00d60 0x690404807f00ff0b 0x6690404807f00ff0

def z317 : W := mkw 0x4000000800040840 0x0400000080004084 0xec010418041f1cff 0xfec010418041f1cf

def z318 : W := mkw 0x2000400200420020 0x4200040020042002 0x0600c00600030030 0x10600c0060003003

def z319 : W := mkw 0x20000122002064a0 0x020000122002064a 0xde1acb660000e4f8 0xfde1acb660000e4f

def z320 : W := mkw 0x20084122446264a0 0x420084122446264a 0x4618c30644e3e4fd 0x54618c30644e3e4f

def z321 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x21e10c78381cf8ca 0xa21e10c78381cf8c

def z322 : W := mkw 0x52fffeddf7df095f 0xe52fffeddf7df095 0xffffffffffff1fff 0xfffffffffffff1ff

def z323 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000b6600000000 0xe04000b660000000

def z324 : W := mkw 0x20000122002064a0 0x020000122002064a 0x000000000000e4f8 0x0000000000000e4f

def z325 : W := mkw 0x02f7bed53399000f 0xa02f7bed53399000 0xffffffffbb1c0002 0xfffffffffbb1c000

def z326 : W := mkw 0x0000000000000000 0x0000000000000000 0xda1ac00000000000 0x1da1ac0000000000

def z327 : W := mkw 0x02f7bed53399000f 0xa02f7bed53399000 0x21e53499bb1c0002 0x021e53499bb1c000

def z328 : W := mkw 0x20004122006264a0 0x420004122006264a 0x8602cb6600e3e4fc 0xf8602cb6600e3e4f

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x4004008007000700 0x4400400800700070

def z330 : W := mkw 0x80f7aed52a00920f 0x980f7aed52a00920 0xffffffffbb001b02 0xfffffffffbb001b0

def z331 : W := mkw 0x50001008810d0950 0x050001008810d095 0xcc013019841f04fd 0xfcc013019841f04f

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0xec053499840304fd 0xfec053499840304f

def z333 : W := mkw 0x809c038066004602 0x8809c03806600460 0x0018030000000000 0x0001803000000000

def z334 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x96fbfb7f80000000 0x996fbfb7f8000000

def z335 : W := mkw 0x0208500077db0000 0xe0208500077db000 0xdb1ac0007fff0007 0x1db1ac0007fff000

def z336 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xa1e3047838fc18c6 0x8a1e3047838fc18c

def z337 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x93fbf00078ff0004 0x193fbf00078ff000

def z338 : W := mkw 0x03ffec707ef2b08c 0xf03ffec707ef2b08 0x13fac86078e0e000 0x013fac86078e0e00

def z339 : W := mkw 0x509c1008e70d0950 0x8509c1008e70d095 0xfdfd3499ff1f1fff 0xffdfd3499ff1f1ff

def z340 : W := mkw 0x00f7bed50109000f 0x000f7bed50109000 0xfeffffff871f0007 0xffeffffff871f000

def z341 : W := mkw 0x02fffc007fdb900c 0xf02fffc007fdb900 0xfbfffc007ffff80f 0x3fbfffc007ffff80

def z342 : W := mkw 0x81ff0ff07eb0f686 0x981ff0ff07eb0f68 0x11fa0b6078e0e000 0x011fa0b6078e0e00

def z343 : W := mkw 0x00280d004c00d404 0x100280d004c00d40 0x79f80f007c00fc0b 0x679f80f007c00fc0

def z344 : W := mkw 0x41630c5818949844 0x141630c581894984 0xa9e10418381c18cf 0xaa9e10418381c18c

def z345 : W := mkw 0x00d7a2d50000000b 0x000d7a2d50000000 0xc61ff3ff80000000 0xdc61ff3ff8000000

def z346 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff4807fff1f0f 0x7fbfff4807fff1f0

def z347 : W := mkw 0xd0bc1f88ef0ddf56 0x9d0bc1f88ef0ddf5 0x79fc0f807f1fffff 0x679fc0f807f1ffff

def z348 : W := mkw 0x82bc5f807fdbd606 0xf82bc5f807fdbd60 0x79fc0f807fffff0f 0x679fc0f807fffff0

def z349 : W := mkw 0x52dff008f7df0958 0xe52dff008f7df095 0xfbfff499ffff1b07 0x1fbfff499ffff1b0

def z350 : W := mkw 0x01630c7018b0b084 0x101630c7018b0b08 0x99e2086078e0e0cd 0xa99e2086078e0e0c

def z351 : W := mkw 0x43dff07877ff28c8 0xe43dff07877ff28c 0xfbfff0787fff00c7 0x9fbfff0787fff00c

def z352 : W := mkw 0x00d7b00001090008 0x000d7b0000109000 0xfafff000071f0007 0x1fafff000071f000

def z353 : W := mkw 0x51631c58999d9954 0x151631c58999d995 0x21e53499bb1c1b02 0x021e53499bb1c1b0

def z354 : W := mkw 0x00b4ae850000000f 0x000b4ae850000000 0x7efcff8780000000 0x77efcff878000000

def z355 : W := mkw 0x0008400044420000 0x4000840004442000 0xde1acb6644e30005 0xfde1acb6644e3000

def z356 : W := mkw 0xd0ffbfddef0ddf5f 0x9d0ffbfddef0ddf5 0xffffffffff1fffff 0xfffffffffff1ffff

def z357 : W := mkw 0x00200ed500000007 0x000200ed50000000 0xde1acfff80000000 0xfde1acfff8000000

def z358 : W := mkw 0x82ffffd57fdbd60f 0xf82ffffd57fdbd60 0xffffffffffffff0f 0xfffffffffffffff0

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0x8401301980000000 0x9840130198000000

def z360 : W := mkw 0x20000022002020a0 0x020000022002020a 0x04000066000000f0 0x804000066000000f

def z361 : W := mkw 0x00f7aed50800900f 0x100f7aed50800900 0xfffffffff800f80b 0xffffffffff800f80

def z362 : W := mkw 0x0294b00023090008 0xa0294b0002309000 0x0004300003000000 0x0000430000300000

def z363 : W := mkw 0x0000100001090000 0x0000010000109000 0xec053000071f04ff 0xfec053000071f04f

def z364 : W := mkw 0xc16b0d787eb4fec4 0x9c16b0d787eb4fec 0xb9e30c787ffcffcf 0xab9e30c787ffcffc

def z365 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x80030c7800fcf8cc 0xa80030c7800fcf8c

def z366 : W := mkw 0x00df000076900000 0x800df00007690000 0xf9ff00007ffc0007 0x0f9ff00007ffc000

def z367 : W := mkw 0x0000000000000000 0x0000000000000000 0xde1acb66040304fd 0xfde1acb66040304f

def z368 : W := mkw 0x410000280824b8c0 0x1410000280824b8c 0x000000000000f8c8 0x0000000000000f8c

def z369 : W := mkw 0x5143107891bd29d0 0x05143107891bd29d 0xec0734f987ff1fff 0xfec0734f987ff1ff

def z370 : W := mkw 0x02dfe00076d20008 0xe02dfe00076d2000 0x7bfec0007fe00003 0x07bfec0007fe0000

def z371 : W := mkw 0x00b40e8000000006 0x000b40e800000000 0x10f80b0000000000 0x010f80b000000000

def z372 : W := mkw 0x0000100001090000 0x0000010000109000 0x00000000071f0007 0x000000000071f000

def z373 : W := mkw 0x01630c7018b0b084 0x101630c7018b0b08 0xb9e30c7878e0e000 0xab9e30c7878e0e00

def z374 : W := mkw 0x029c500077db0000 0xe029c500077db000 0x79fc00007fff0007 0x079fc00007fff000

def z375 : W := mkw 0x01630c7018b0b084 0x101630c7018b0b08 0x39e20c6078e0f80b 0x239e20c6078e0f80

def z376 : W := mkw 0x01630c7018b0b084 0x101630c7018b0b08 0xb9e3086078fce007 0x0b9e3086078fce00

def z377 : W := mkw 0x51200c788824b9d4 0x151200c788824b9d 0x04000cf98000fff8 0xe04000cf98000fff

def z378 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x21e1041878fcf8cf 0x021e1041878fcf8c

def z379 : W := mkw 0x50001008810d0950 0x050001008810d095 0x00000000031c1b02 0x000000000031c1b0

def z380 : W := mkw 0x02dff000674b0008 0xe02dff000674b000 0xfafff00007030000 0x1fafff0000703000

def z381 : W := mkw 0x20084122446264a0 0x420084122446264a 0x121acb6644e3e4fd 0x0121acb6644e3e4f

def z382 : W := mkw 0x20084122446264a0 0x420084122446264a 0xde1acb6640e0e000 0xfde1acb6640e0e00

def z383 : W := mkw 0x50001008810d0950 0x050001008810d095 0xa4053499831f1bf6 0x9a4053499831f1bf

def z384 : W := mkw 0xc1f70ef83ab4bac6 0x9c1f70ef83ab4bac 0xb9e70cf87bfcfbcf 0xab9e70cf87bfcfbc

def z385 : W := mkw 0x03fffc707ffbb08c 0xf03fffc707ffbb08 0xfbfff8607fffe007 0x1fbfff8607fffe00

def z386 : W := mkw 0x0043000000000000 0x0004300000000000 0xb8e3000000000000 0x0b8e300000000000

def z387 : W := mkw 0x0094028000000002 0x0009402800000000 0x401c038000000000 0x4401c03800000000

def z388 : W := mkw 0x20284ff7446264a7 0x420284ff7446264a 0xde1acfffc4e3e4fd 0xfde1acfffc4e3e4f

def z389 : W := mkw 0x7008512ac56f6df0 0x47008512ac56f6df 0xec053499c7ffffff 0xfec053499c7fffff

def z390 : W := mkw 0x20084122446264a0 0x420084122446264a 0x0000000040e0e000 0x00000000040e0e00

def z391 : W := mkw 0x72dff12af7ff6df8 0xe72dff12af7ff6df 0xffffffffffffffff 0xffffffffffffffff

def z392 : W := mkw 0x1000100081090110 0x0100010008109011 0xec053081871f0737 0x5ec053081871f073

def z393 : W := mkw 0xd0201f88890ddf56 0x1d0201f88890ddf5 0xec053f99871fffff 0xfec053f99871ffff

def z394 : W := mkw 0x82dff38077db460a 0xe82dff38077db460 0xfbfff3807fff0707 0x5fbfff3807fff070

def z395 : W := mkw 0x8000038000004602 0x0800003800000460 0x0000038000000700 0x4000003800000070

def z396 : W := mkw 0x809c038066004602 0x8809c03806600460 0x581c0b804700e709 0x6581c0b804700e70

def z397 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x53fef0007fe30000 0x153fef0007fe3000

def z398 : W := mkw 0x216b4d725cf2f4a4 0x5216b4d725cf2f4a 0xdffacb667ce3e4fd 0xfdffacb667ce3e4f

def z399 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff87001f0b 0xffeffffff87001f0

def z400 : W := mkw 0xa00841226e62f6a0 0xda00841226e62f6a 0xdf1acb667fe3ffff 0xfdf1acb667fe3fff

def z401 : W := mkw 0x80280f806e00d606 0x980280f806e00d60 0x01000f807f00ff0b 0x601000f807f00ff0

def z402 : W := mkw 0x20084122446264a0 0x420084122446264a 0xfe1fffffc4e3e4fd 0xffe1fffffc4e3e4f

def z403 : W := mkw 0x809c038066004602 0x8809c03806600460 0x681c078007001f0b 0x6681c078007001f0

def z404 : W := mkw 0x50001008810d0950 0x050001008810d095 0xfe1fffff871f1fff 0xffe1fffff871f1ff

def z405 : W := mkw 0x43dff0287fffb8c8 0xf43dff0287fffb8c 0xfbfff0007ffff8cf 0x1fbfff0007ffff8c

def z406 : W := mkw 0x20004022006220a0 0x420004022006220a 0x0202c06600e00000 0x00202c06600e0000

def z407 : W := mkw 0xd09c1388e70d4f52 0x8d09c1388e70d4f5 0xec1d3799871f1fff 0xfec1d3799871f1ff

def z408 : W := mkw 0x50001008810d0950 0x050001008810d095 0xac013419801f18ff 0xbac013419801f18f

def z409 : W := mkw 0x5243f00891df0958 0x65243f00891df095 0xee07f49987ff1fff 0xfee07f49987ff1ff

def z410 : W := mkw 0x00b40e8000000006 0x000b40e800000000 0xfcfd3f9980000000 0xffcfd3f998000000

def z411 : W := mkw 0x529cf008e74f0958 0xe529cf008e74f095 0xee1df499871f1fff 0xfee1df499871f1ff

def z412 : W := mkw 0x0000100001090000 0x0000010000109000 0xec053499871f0007 0xfec053499871f000

def z413 : W := mkw 0x7008512ac56f6df0 0x47008512ac56f6df 0xde1acb6647ffffff 0xfde1acb6647fffff

def z414 : W := mkw 0xd0bc0f88ee04df56 0x9d0bc0f88ee04df5 0x7dfc0f99ff00fffb 0xe7dfc0f99ff00fff

def z415 : W := mkw 0x12dff000f7db0118 0xe12dff000f7db011 0xfffff081ffff0737 0x5fffff081ffff073

def z416 : W := mkw 0x0200100033990000 0xa020010003399000 0x010000003b1c0002 0x0010000003b1c000

def z417 : W := mkw 0x029cf00077db0008 0xe029cf00077db000 0x431cf0007fff0007 0x1431cf0007fff000

def z418 : W := mkw 0x50001008810d0950 0x050001008810d095 0x00000000001f00f4 0x000000000001f00f

def z419 : W := mkw 0x00630ed500000007 0x000630ed50000000 0xbce30fff80000000 0xebce30fff8000000

def z420 : W := mkw 0x8094028022000202 0x8809402802200020 0x0004008003000300 0x0000400800300030

def z421 : W := mkw 0x0208400076d20000 0xe0208400076d2000 0x0100000078e00000 0x00100000078e0000

def z422 : W := mkw 0x0100002018b0b080 0x10100002018b0b08 0x0100000078e0e000 0x00100000078e0e00

def z423 : W := mkw 0x6108412a5cf6fce0 0x56108412a5cf6fce 0x010000007cfffcff 0x0010000007cfffcf

def z424 : W := mkw 0x02dff10077db4408 0xe02dff10077db440 0xfbfffb007fffe40f 0x7fbfffb007fffe40

def z425 : W := mkw 0xd0200f888804df56 0x1d0200f888804df5 0x04000f998000fff8 0xe04000f998000fff

def z426 : W := mkw 0x80200fd50800d607 0x180200fd50800d60 0x04000fff8000ff08 0xe04000fff8000ff0

def z427 : W := mkw 0x43f7bc783bbdb8cc 0xb43f7bc783bbdb8c 0xb9e73c787bfcf8cf 0xab9e73c787bfcf8c

def z428 : W := mkw 0x00bc0c006e009004 0x900bc0c006e00900 0x79fc0c007f00f80b 0x279fc0c007f00f80

def z429 : W := mkw 0x00f7ae800000000e 0x000f7ae800000000 0xfaffff8000000000 0x7faffff800000000

def z430 : W := mkw 0x50001008810d0950 0x050001008810d095 0xa8053499831c1bcf 0xaa8053499831c1bc

def z431 : W := mkw 0x22dff02277fb20a8 0xe22dff02277fb20a 0xfffff0667fff00f7 0x9fffff0667fff00f

def z432 : W := mkw 0x5000000880040950 0x0500000088004095 0xcc00049984031ffd 0xfcc00049984031ff

def z433 : W := mkw 0x02fffed5674b000f 0xe02fffed5674b000 0xfeffffff87030000 0xffeffffff8703000

def z434 : W := mkw 0x20200ff7002064a7 0x020200ff7002064a 0x04000fff8000e4f8 0xe04000fff8000e4f

def z435 : W := mkw 0x50001008810d0950 0x050001008810d095 0x00013019801c0000 0x000013019801c000

def z436 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x21e404807f00ff0b 0x021e404807f00ff0

def z437 : W := mkw 0x616b4d7a5cf6fce4 0x5616b4d7a5cf6fce 0xb9e30c787cfffcff 0xab9e30c787cfffcf

def z438 : W := mkw 0x41200c2818b4b8c4 0x141200c2818b4b8c 0x39e00c0078fcf8cf 0x239e00c0078fcf8c

def z439 : W := mkw 0xc1bc0ff86e24fec6 0x9c1bc0ff86e24fec 0x79fc0ff87f00ffcb 0xe79fc0ff87f00ffc

def z440 : W := mkw 0x43ffec787ef6b8cc 0xf43ffec787ef6b8c 0xbbfbcc7878fcf8cf 0xabbfbcc7878fcf8c

def z441 : W := mkw 0xa0bc4fa26e62f6a6 0xda0bc4fa26e62f6a 0xdffacb667ce3e4fd 0xfdffacb667ce3e4f

def z442 : W := mkw 0x2008410244424420 0x4200841024442442 0xde1acb6604030430 0xfde1acb660403043

def z443 : W := mkw 0x0043002010b02080 0x00043002010b0208 0xb9e3086078fce0cf 0xab9e3086078fce0c

def z444 : W := mkw 0x0000002000202080 0x0000000200020208 0x8002006000e000c4 0x88002006000e000c

def z445 : W := mkw 0x0008012044206480 0x0000801204420648 0xd81a0b6044e0e4cd 0xed81a0b6044e0e4c

def z446 : W := mkw 0x41630c7810b428c4 0x041630c7810b428c 0xb8e30c7800fc00c4 0xab8e30c7800fc00c

def z447 : W := mkw 0xf0bc5faaef6ffff6 0xdf0bc5faaef6ffff 0xffffffffffffffff 0xffffffffffffffff

def z448 : W := mkw 0x41f7ac7818b4b8cc 0x141f7ac7818b4b8c 0xfbfffc7878fcf8cf 0xbfbfffc7878fcf8c

def z449 : W := mkw 0x41630c780824b8c4 0x141630c780824b8c 0xb8e30c780000f8c8 0xab8e30c780000f8c

def z450 : W := mkw 0x2008410244424420 0x4200841024442442 0x0000000004030430 0x0000000000403043

def z451 : W := mkw 0x43fffefd7fffb8cf 0xf43fffefd7fffb8c 0xfffffffffffff8cf 0xffffffffffffff8c

def z452 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0x0004308180000000 0x0000430818000000

def z453 : W := mkw 0x02fffe8077db000e 0xe02fffe8077db000 0xfbffff807fff0007 0x7fbffff807fff000

def z454 : W := mkw 0x0000010000004400 0x0000001000000440 0x00000b000000e408 0x600000b000000e40

def z455 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfafffb6600000000 0x1fafffb660000000

def z456 : W := mkw 0x5043b05d810d0959 0x05043b05d810d095 0xee07f4ff871f1fff 0xfee07f4ff871f1ff

def z457 : W := mkw 0x82ffef807ed2d60e 0xf82ffef807ed2d60 0x7bfecf807fe0ff0b 0x67bfecf807fe0ff0

def z458 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xbafbcf7e00000000 0xabafbcf7e0000000

def z459 : W := mkw 0x00200ed500000007 0x000200ed50000000 0x0000049980000000 0x0000004998000000

def z460 : W := mkw 0x0008400044420000 0x4000840004442000 0x0000000044e30005 0x00000000044e3000

def z461 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffffb667fff0007 0xffffffb667fff000

def z462 : W := mkw 0x80bc0f8066004606 0x880bc0f806600460 0x78fc0f8007000700 0x678fc0f800700070

def z463 : W := mkw 0x41200c7818b4b8c4 0x141200c7818b4b8c 0x01000c7878fcf8cf 0xa01000c7878fcf8c

def z464 : W := mkw 0x800000002a009200 0x9800000002a00920 0x010000003b001b02 0x0010000003b001b0

def z465 : W := mkw 0x50f7aedd8004095f 0x050f7aedd8004095 0xfeffffff80001ff8 0xffeffffff80001ff

def z466 : W := mkw 0x42dff00877df0848 0xe42dff00877df084 0xfbfff4187fff18cf 0xbfbfff4187fff18c

def z467 : W := mkw 0x00630c5000000004 0x000630c500000000 0x10e2086000000000 0x010e208600000000

def z468 : W := mkw 0x40000028002428c0 0x040000028002428c 0xb8030c7840fcf8cf 0xab8030c7840fcf8c

def z469 : W := mkw 0x00b40e8000000006 0x000b40e800000000 0xfefecfe600000000 0xffefecfe60000000

def z470 : W := mkw 0x53fffc78ffffb9dc 0xf53fffc78ffffb9d 0xfffffcf9ffffffff 0xffffffcf9fffffff

def z471 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xece5349980000000 0xfece534998000000

def z472 : W := mkw 0x204be177446264a9 0x4204be177446264a 0xde1bfb7fc4e3e4fd 0xfde1bfb7fc4e3e4f

def z473 : W := mkw 0x50001008810d0950 0x050001008810d095 0x84013499801f1ffc 0xf84013499801f1ff

def z474 : W := mkw 0x00200c0008009004 0x100200c000800900 0x79e40c807f00ff0b 0x679e40c807f00ff0

def z475 : W := mkw 0x00200ed500000007 0x000200ed50000000 0x00000b6600000000 0x000000b660000000

def z476 : W := mkw 0x51f7befd99bdb9df 0x151f7befd99bdb9d 0xffffffffffffffff 0xffffffffffffffff

def z477 : W := mkw 0xa0bc0fa26e20f6a6 0x9a0bc0fa26e20f6a 0x7dfc0fe67f00fffb 0xe7dfc0fe67f00fff

def z478 : W := mkw 0x50431008919d0950 0x050431008919d095 0xfde73499ffff1fff 0xffde73499ffff1ff

def z479 : W := mkw 0x009c000066000000 0x8009c00006600000 0x11f8000078000000 0x011f800007800000

def z480 : W := mkw 0x0000000000000000 0x0000000000000000 0xe805300000000000 0x1e80530000000000

def z481 : W := mkw 0x4143a07d10b428c9 0x04143a07d10b428c 0x8603f07f80fc00c4 0x98603f07f80fc00c

def z482 : W := mkw 0x0094000022000000 0x8009400002200000 0x21e400003b000002 0x021e400003b00000

def z483 : W := mkw 0x43fffc587fdf984c 0xf43fffc587fdf984 0xfbfff4187fff1807 0x1fbfff4187fff180

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0xa801041800000000 0xaa80104180000000

def z485 : W := mkw 0x0000400000420000 0x4000040000042000 0x8202c00000e30004 0x18202c00000e3000

def z486 : W := mkw 0x80bc0fa06e20f686 0x980bc0fa06e20f68 0xf9fe0fe07fe0ffcf 0xef9fe0fe07fe0ffc

def z487 : W := mkw 0xa0200fa20820f6a6 0x1a0200fa20820f6a 0x04000fe60000fff8 0xe04000fe60000fff

def z488 : W := mkw 0x01f7aef518b0b08f 0x101f7aef518b0b08 0x13facb6678e0e000 0x013facb6678e0e00

def z489 : W := mkw 0x20084122446264a0 0x420084122446264a 0x9802086044e3e4fd 0xa9802086044e3e4f

def z490 : W := mkw 0x30085122c56b65b0 0x430085122c56b65b 0xde1efbe7c7e3e7fd 0xfde1efbe7c7e3e7f

def z491 : W := mkw 0x82f7be803b99920e 0xb82f7be803b99920 0x21e534803b1c1b02 0x021e534803b1c1b0

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0x84000000000300f4 0x984000000000300f

def z493 : W := mkw 0x0008010044004400 0x0000801004400440 0xdc180b004403e4fd 0xfdc180b004403e4f

def z494 : W := mkw 0xc1630ff818b4fec6 0x1c1630ff818b4fec 0xb9e30ff878fcffcf 0xeb9e30ff878fcffc

def z495 : W := mkw 0x50200edd80040957 0x050200edd8004095 0x04000fff80001ff8 0xe04000fff80001ff

def z496 : W := mkw 0xd0bc1f88ef0ddf56 0x9d0bc1f88ef0ddf5 0x79fd3f99ff1cff0b 0x679fd3f99ff1cff0

def z497 : W := mkw 0x43f7bc583b9d984c 0xb43f7bc583b9d984 0x21e534183b1c1802 0x021e534183b1c180

def z498 : W := mkw 0x50081108c50d4d50 0x050081108c50d4d5 0xfc1d3f99c71fffff 0xffc1d3f99c71ffff

def z499 : W := mkw 0x00630c5000000004 0x000630c500000000 0xfce73cf980000000 0xffce73cf98000000

def z500 : W := mkw 0xd0081108ef0ddf50 0x9d0081108ef0ddf5 0xed053499ff1fffff 0xfed053499ff1ffff

def z501 : W := mkw 0x5000000880040950 0x0500000088004095 0xac010499801c1fff 0xeac010499801c1ff

def z502 : W := mkw 0x0008010044004400 0x0000801004400440 0x4018030004000400 0x4401803000400040

def z503 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x21e530007fff0007 0x021e530007fff000

def z504 : W := mkw 0x1000100081090110 0x0100010008109011 0x0000000007030730 0x0000000000703073

def z505 : W := mkw 0x02ffeed576d2000f 0xe02ffeed576d2000 0x13facb6678e00000 0x013facb6678e0000

def z506 : W := mkw 0x50f7bedd810d095f 0x050f7bedd810d095 0x20e53499831c1b02 0x020e53499831c1b0

def z507 : W := mkw 0x00d7a2850000000b 0x000d7a2850000000 0xfefff38780000000 0x5fefff3878000000

def z508 : W := mkw 0x80b40f800800d606 0x180b40f800800d60 0x78fc0f800000ff08 0x678fc0f800000ff0

def z509 : W := mkw 0x50631c58810d0954 0x050631c58810d095 0xfce73cf9871f1fff 0xffce73cf9871f1ff

def z510 : W := mkw 0x4143007818b4b8c0 0x14143007818b4b8c 0x8103007878fcf8cf 0x88103007878fcf8c

def z511 : W := mkw 0x4343f07811ff28c8 0x64343f07811ff28c 0x8203f07800ff00c4 0x98203f07800ff00c

def z512 : W := mkw 0x5243f00891df0958 0x65243f00891df095 0x8603f01980ff00f4 0x98603f01980ff00f

def z513 : W := mkw 0x00200ed500000007 0x000200ed50000000 0xec053fff80000000 0xfec053fff8000000

def z514 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xdefacb6600000000 0xfdefacb660000000

def z515 : W := mkw 0x614b417a54f66ce0 0x4614b417a54f66ce 0xde1bcb7e44ffe4fd 0xfde1bcb7e44ffe4f

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x9802000040e00005 0x09802000040e0000

def z517 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x63fdf0003f1f0002 0x163fdf0003f1f000

def z518 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0xde1efbe780000000 0xfde1efbe78000000

def z519 : W := mkw 0x50001008810d0950 0x050001008810d095 0xa8010418071f1fff 0xaa8010418071f1ff

def z520 : W := mkw 0x82bcff806f4bd60e 0xf82bcff806f4bd60 0x7bfcff807f03ff0b 0x77bfcff807f03ff0

def z521 : W := mkw 0x0000000000000000 0x0000000000000000 0x4800000004000409 0x6480000000400040

def z522 : W := mkw 0x50f7bedd810d095f 0x050f7bedd810d095 0xece53499871f1fff 0xfece53499871f1ff

def z523 : W := mkw 0x00ffeed54442000f 0x400ffeed54442000 0xfeffffffc4e30005 0xffeffffffc4e3000

def z524 : W := mkw 0x0008400044420000 0x4000840004442000 0x121ac00040e00000 0x0121ac00040e0000

def z525 : W := mkw 0x80bc0fd56e00d607 0x980bc0fd56e00d60 0x7dfc0fffff00ff0b 0xe7dfc0fffff00ff0

def z526 : W := mkw 0x5000000880040950 0x0500000088004095 0x0000049980001b00 0x00000049980001b0

def z527 : W := mkw 0x50001008810d0950 0x050001008810d095 0x4404349987031ff8 0xf4404349987031ff

def z528 : W := mkw 0x0000000000000000 0x0000000000000000 0x2004048003001b02 0x02004048003001b0

def z529 : W := mkw 0x41630efd18b4b8c7 0x141630efd18b4b8c 0xbde30ffff8fcf8cf 0xebde30ffff8fcf8c

def z530 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xa6e7f4ff80000000 0x9a6e7f4ff8000000

def z531 : W := mkw 0x6008412a44666ce0 0x46008412a44666ce 0xfe1bcf7e44fffcff 0xffe1bcf7e44fffcf

def z532 : W := mkw 0x20f7eef7006220af 0x420f7eef7006220a 0xfeffffff80e300f4 0xffeffffff80e300f

def z533 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x39e00c787800f8cb 0xa39e00c787800f8c

def z534 : W := mkw 0x6143407a10f628e0 0x46143407a10f628e 0x8603c07e00ff00f4 0x98603c07e00ff00f

def z535 : W := mkw 0x20004022006220a0 0x420004022006220a 0x9e02c86640e3e0fd 0xb9e02c86640e3e0f

def z536 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc00000000000000 0xfcc0000000000000

def z537 : W := mkw 0x209ce3a7446264ab 0x4209ce3a7446264a 0xde1efbe7c4e3e4fd 0xfde1efbe7c4e3e4f

def z538 : W := mkw 0x22dfe12276f264a8 0xe22dfe12276f264a 0x13facb6678e0e000 0x013facb6678e0e00

def z539 : W := mkw 0x0000100001090000 0x0000010000109000 0xe8053480071f1f0f 0x7e8053480071f1f0

def z540 : W := mkw 0x00f7ac500000000c 0x000f7ac500000000 0xfafffc7800000000 0xbfafffc780000000

def z541 : W := mkw 0x029cf000674b0008 0xe029cf000674b000 0x7bfcf0007f030003 0x17bfcf0007f03000

def z542 : W := mkw 0x0043a00000000008 0x00043a0000000000 0x8203f00000000000 0x18203f0000000000

def z543 : W := mkw 0x02fffed577db000f 0xe02fffed577db000 0xfbfffb667fff0007 0x1fbfffb667fff000

def z544 : W := mkw 0x5000000880040950 0x0500000088004095 0x6c04049987001ffb 0xe6c04049987001ff

def z545 : W := mkw 0x50001028812d29d0 0x050001028812d29d 0xfc073cf9c7ffffff 0xffc073cf9c7fffff

def z546 : W := mkw 0x4000000800040840 0x0400000080004084 0x00000418000018c8 0xa00000418000018c

def z547 : W := mkw 0x909c1380e7094712 0x8909c1380e709471 0x441c338187030730 0x5441c33818703073

def z548 : W := mkw 0x00d7a00000000008 0x000d7a0000000000 0x12fac00000000000 0x012fac0000000000

def z549 : W := mkw 0x5043b05d810d0959 0x05043b05d810d095 0x8603f07f801f00f4 0x98603f07f801f00f

def z550 : W := mkw 0x41000078002428c0 0x041000078002428c 0x00000078000000c0 0x800000078000000c

def z551 : W := mkw 0x82ffff807fdbd60e 0xf82ffff807fdbd60 0xfbfffb007fffe007 0x1fbfffb007fffe00

def z552 : W := mkw 0x00bc0f8044004406 0x000bc0f804400440 0x78fc0f804400e409 0x678fc0f804400e40

def z553 : W := mkw 0x00b40e8000000006 0x000b40e800000000 0x20e4048000000000 0x020e404800000000

def z554 : W := mkw 0x7000012a80246df0 0x07000012a80246df 0x04000fff8000fff8 0xe04000fff8000fff

def z555 : W := mkw 0x02fffc5077db000c 0xe02fffc5077db000 0xfbfffc787fff0007 0xbfbfffc787fff000

def z556 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0x0218c30600000000 0x00218c3060000000

def z557 : W := mkw 0x6108412a5cf6fce0 0x56108412a5cf6fce 0xdf1acb667cfffcff 0xfdf1acb667cfffcf

def z558 : W := mkw 0x40630c5800040844 0x040630c580004084 0xb8e30c78001c18cf 0xab8e30c78001c18c

def z559 : W := mkw 0x20ffefd74442442f 0x420ffefd74442442 0xfeffffff84030430 0xffeffffff8403043

def z560 : W := mkw 0x009c000066000000 0x8009c00006600000 0x401c000007000000 0x0401c00000700000

def z561 : W := mkw 0x02d7b00033990008 0xa02d7b0003399000 0xfbfff0003b1c0002 0x1fbfff0003b1c000

def z562 : W := mkw 0x024bf00077db0008 0xe024bf00077db000 0x8303f0007fff0007 0x18303f0007fff000

def z563 : W := mkw 0x2208512277fb64a0 0xe2208512277fb64a 0x010000007fffe4ff 0x0010000007fffe4f

def z564 : W := mkw 0x61630d7a18b4fce4 0x161630d7a18b4fce 0xbde30f7e78fcfcff 0xebde30f7e78fcfcf

def z565 : W := mkw 0x5000000880040950 0x0500000088004095 0x04000019800000f0 0x804000019800000f

def z566 : W := mkw 0x0063aed50000000f 0x00063aed50000000 0x8603ffff80000000 0xf8603ffff8000000

def z567 : W := mkw 0x4143007810b428c0 0x04143007810b428c 0xb9e3007878fc00c7 0x8b9e3007878fc00c

def z568 : W := mkw 0x029cf000674b0008 0xe029cf000674b000 0xea1df000071f0007 0x1ea1df000071f000

def z569 : W := mkw 0x00dfa00066000008 0x800dfa0006600000 0xfbfff0007f000003 0x1fbfff0007f00000

def z570 : W := mkw 0x20084122446264a0 0x420084122446264a 0x58180b0044e3e4fd 0x658180b0044e3e4f

def z571 : W := mkw 0x01200c700820b084 0x101200c700820b08 0x000008600000e000 0x0000008600000e00

def z572 : W := mkw 0x00f7aef50020208f 0x000f7aef50020208 0xfeffffffc0e0e0cd 0xffeffffffc0e0e0c

def z573 : W := mkw 0xd1ff1ff8ffbdffd6 0x9d1ff1ff8ffbdffd 0xfdff3ff9ffffffff 0xffdff3ff9fffffff

def z574 : W := mkw 0x02dfe00076d20008 0xe02dfe00076d2000 0xfbfff00078e00000 0x1fbfff00078e0000

def z575 : W := mkw 0x2243f02211fb20a8 0x62243f02211fb20a 0x8603f06600ff00f4 0x98603f06600ff00f

def z576 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x98020c7840e0f8cd 0xa98020c7840e0f8c

def z577 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x56fefbe780000000 0x556fefbe78000000

def z578 : W := mkw 0xa0bc4fa26e62f6a6 0xda0bc4fa26e62f6a 0x79fc0f807fe3ffff 0x679fc0f807fe3fff

def z579 : W := mkw 0xc1bc0fa87eb4fec6 0x9c1bc0fa87eb4fec 0x79fc0f807ffcffcf 0x679fc0f807ffcffc

def z580 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x16facfff80000000 0xe16facfff8000000

def z581 : W := mkw 0x0000002000202080 0x0000000200020208 0x1002086040e0e000 0x01002086040e0e00

def z582 : W := mkw 0x0000000000000000 0x0000000000000000 0x8602c06600000000 0x98602c0660000000

def z583 : W := mkw 0x0008010044004400 0x0000801004400440 0xde1acb664400e409 0xfde1acb664400e40

def z584 : W := mkw 0x20f7aff7002064af 0x020f7aff7002064a 0xfeffffff8000e4f8 0xffeffffff8000e4f

def z585 : W := mkw 0x00d7a00000000008 0x000d7a0000000000 0xfefff49980000000 0xffefff4998000000

def z586 : W := mkw 0x82ffef807ed2d60e 0xf82ffef807ed2d60 0x13facb0078e0e000 0x013facb0078e0e00

def z587 : W := mkw 0x5000000880040950 0x0500000088004095 0x0000000000001ff8 0x00000000000001ff

def z588 : W := mkw 0x4000000800040840 0x0400000080004084 0xec053499801c18cf 0xfec053499801c18c

def z589 : W := mkw 0x20ffeff7446264af 0x420ffeff7446264a 0xfeffffffc0e0e000 0xffeffffffc0e0e00

def z590 : W := mkw 0x0243f05511db0009 0x60243f05511db000 0x8603f07f80ff0004 0x98603f07f80ff000

def z591 : W := mkw 0x0000000000000000 0x0000000000000000 0x121acb6600000000 0x0121acb660000000

def z592 : W := mkw 0xa0ffeff76e62f6af 0xda0ffeff76e62f6a 0xffffffffffe3ffff 0xfffffffffffe3fff

def z593 : W := mkw 0xc1ffaffd7eb4fecf 0x9c1ffaffd7eb4fec 0xfffffffffffcffcf 0xffffffffffffcffc

def z594 : W := mkw 0x40001008010d0840 0x040001008010d084 0xe8053418071f18cf 0xbe8053418071f18c

def z595 : W := mkw 0x0043a05500000009 0x00043a0550000000 0x0001301980000000 0x0000130198000000

def z596 : W := mkw 0x50001008810d0950 0x050001008810d095 0x24053499831c1ffa 0xe24053499831c1ff

def z597 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0xee1df79f80000000 0xfee1df79f8000000

def z598 : W := mkw 0x80ffafd56e00d60f 0x980ffafd56e00d60 0xfffffffff800e000 0xffffffffff800e00

def z599 : W := mkw 0x2008410244424420 0x4200841024442442 0x0218c30600000000 0x00218c3060000000

def z600 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x00e0000000000000 0x000e000000000000

def z601 : W := mkw 0x800801006e00d600 0x9800801006e00d60 0x59180b007f00ff0b 0x659180b007f00ff0

def z602 : W := mkw 0x0000002000202080 0x0000000200020208 0x000008600000e0c8 0xa000008600000e0c

def z603 : W := mkw 0x4143007810b428c0 0x04143007810b428c 0x9803087840fce0cd 0xa9803087840fce0c

def z604 : W := mkw 0x50001008810d0950 0x050001008810d095 0x04000499871f1fff 0xe04000499871f1ff

def z605 : W := mkw 0x0143007010b02080 0x00143007010b0208 0x0002006000e00000 0x00002006000e0000

def z606 : W := mkw 0x00200e8000000006 0x000200e800000000 0x00000f8000000000 0x600000f800000000

def z607 : W := mkw 0x80ff0fd06e00d606 0x980ff0fd06e00d60 0xf9ff0ff87f00ff0b 0xef9ff0ff87f00ff0

def z608 : W := mkw 0x4000000800040840 0x0400000080004084 0x20010418001c1802 0x020010418001c180

def z609 : W := mkw 0x22fffff777fb64af 0xe22fffff777fb64a 0xffffffffffffe4ff 0xfffffffffffffe4f

def z610 : W := mkw 0x20080122442064a0 0x020080122442064a 0x5c180b664400e4f9 0xe5c180b664400e4f

def z611 : W := mkw 0x2000010200004420 0x0200001020000442 0x0400030600000430 0x4040003060000043

def z612 : W := mkw 0x4043000810940840 0x0404300081094084 0xb9e3041878fc18cf 0xab9e3041878fc18c

def z613 : W := mkw 0x00d7a05500000009 0x000d7a0550000000 0xfefff07f80000000 0x9fefff07f8000000

def z614 : W := mkw 0x02dfe00076d20008 0xe02dfe00076d2000 0xdbfac0007ce30005 0x1dbfac0007ce3000

def z615 : W := mkw 0x70ffffffc56f6dff 0x470ffffffc56f6df 0xfeffffffc7ffffff 0xffeffffffc7fffff

def z616 : W := mkw 0x00630c5000000004 0x000630c500000000 0xfefbcf7e00000000 0xffefbcf7e0000000

def z617 : W := mkw 0x8008010066004600 0x8800801006600460 0x0000000007000700 0x0000000000700070

def z618 : W := mkw 0x1000000080000110 0x0100000008000011 0x0400008180000730 0x4040000818000073

def z619 : W := mkw 0x1000100081090110 0x0100010008109011 0x6c04348187031f3b 0x76c04348187031f3

def z620 : W := mkw 0x20084122446264a0 0x420084122446264a 0x04000b6644e3e4fd 0xe04000b6644e3e4f

def z621 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x51fc0b807f00e700 0x451fc0b807f00e70

def z622 : W := mkw 0x2208512277fb64a0 0xe2208512277fb64a 0xdf1acb667fffe4ff 0xfdf1acb667fffe4f

def z623 : W := mkw 0x0243e00010d20008 0x60243e00010d2000 0x0202c00000e00000 0x00202c00000e0000

def z624 : W := mkw 0x02d7b00033990008 0xa02d7b0003399000 0xb9e730007bfc0007 0x0b9e730007bfc000

def z625 : W := mkw 0x50085008c54f0950 0x450085008c54f095 0xfe1ff499c7ff1fff 0xffe1ff499c7ff1ff

def z626 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x61fc07803f001f02 0x461fc07803f001f0

def z627 : W := mkw 0x30085102c54b4530 0x430085102c54b453 0x461cf38787030730 0x5461cf3878703073

def z628 : W := mkw 0xa09c438266424622 0xca09c43826642462 0x461cc38607030730 0x5461cc3860703073

def z629 : W := mkw 0x2008410244424420 0x4200841024442442 0xce18c306040304fd 0xfce18c306040304f

def z630 : W := mkw 0x0200500011db0000 0x60200500011db000 0x0000000000ff0004 0x00000000000ff000

def z631 : W := mkw 0x80ffafd56e00d60f 0x980ffafd56e00d60 0x7bfecfe67f00ff0b 0x67bfecfe67f00ff0

def z632 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x11f80f807800ff08 0x611f80f807800ff0

def z633 : W := mkw 0x0000005500000001 0x0000000550000000 0x0400007f80000000 0x80400007f8000000

def z634 : W := mkw 0x80bc0e806e009206 0x980bc0e806e00920 0x79fc04807f001b03 0x079fc04807f001b0

def z635 : W := mkw 0x41630c5818949844 0x141630c581894984 0xb9e30c78381c1802 0xab9e30c78381c180

def z636 : W := mkw 0x50001008810d0950 0x050001008810d095 0x84013019871f1fff 0x984013019871f1ff

def z637 : W := mkw 0x0008402044622080 0x4000840204462208 0xda1ac86044e3e0cd 0xbda1ac86044e3e0c

def z638 : W := mkw 0x7008412ac4666df0 0x47008412ac4666df 0xde1acfffc4e3fffd 0xfde1acfffc4e3fff

def z639 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x78fd3f9980000000 0x678fd3f998000000

def z640 : W := mkw 0x009c010066004400 0x8009c01006600440 0x79fc0b007f00e40b 0x679fc0b007f00e40

def z641 : W := mkw 0x4000000800040840 0x0400000080004084 0xe8050498071c1fcf 0xee8050498071c1fc

def z642 : W := mkw 0x20084122446264a0 0x420084122446264a 0x9a1acb6640e0e0cd 0xa9a1acb6640e0e0c

def z643 : W := mkw 0x80ffafd56e00d60f 0x980ffafd56e00d60 0x79fd3f99ff00ff0b 0x679fd3f99ff00ff0

def z644 : W := mkw 0x0008410044424400 0x4000841004442440 0xda1acb0044e3e40d 0x7da1acb0044e3e40

def z645 : W := mkw 0x00630c7000202084 0x000630c700020208 0xb8e30c7840e0e0cd 0xab8e30c7840e0e0c

def z646 : W := mkw 0x63fffd7a7ffffcec 0xf63fffd7a7ffffce 0xffffff7e7ffffcff 0xfffffff7e7ffffcf

def z647 : W := mkw 0x80f7afd50800d60f 0x180f7afd50800d60 0xfeffffff8000ff08 0xffeffffff8000ff0

def z648 : W := mkw 0x01630c5018909004 0x101630c501890900 0x01e0000038000000 0x001e000003800000

def z649 : W := mkw 0x50f7bedd810d095f 0x050f7bedd810d095 0xfeffffff831c1b02 0xffeffffff831c1b0

def z650 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x39f80f007800f80b 0x239f80f007800f80

def z651 : W := mkw 0x0094000000000000 0x0009400000000000 0x78fc000000000000 0x078fc00000000000

def z652 : W := mkw 0x0043a05500000009 0x00043a0550000000 0x0202c06600000000 0x00202c0660000000

def z653 : W := mkw 0x41f7aedd1894984f 0x141f7aedd1894984 0xffffffffb81c1802 0xfffffffffb81c180

def z654 : W := mkw 0x616b4d7a5cf6fce4 0x5616b4d7a5cf6fce 0xbbfbcf7e78fcf8cf 0xabbfbcf7e78fcf8c

def z655 : W := mkw 0x50d7b008810d0958 0x050d7b008810d095 0xfefff499871f1fff 0xffefff499871f1ff

def z656 : W := mkw 0x80bc1f806f09d606 0x980bc1f806f09d60 0xf9fd3f807f1fff0f 0x7f9fd3f807f1fff0

def z657 : W := mkw 0xe1ff4ffa7ef6fee6 0xde1ff4ffa7ef6fee 0xffffcffe7fffffff 0xfffffcffe7ffffff

def z658 : W := mkw 0x20084122446264a0 0x420084122446264a 0xc61ac36604e304f4 0xdc61ac36604e304f

def z659 : W := mkw 0x20084122446264a0 0x420084122446264a 0x5a1acb6644e0e409 0x65a1acb6644e0e40

def z660 : W := mkw 0x4143007810b428c0 0x04143007810b428c 0xa803047800fc18cf 0xaa803047800fc18c

def z661 : W := mkw 0x20000122002064a0 0x020000122002064a 0x9c020b6640e0e4fd 0xe9c020b6640e0e4f

def z662 : W := mkw 0x50001008810d0950 0x050001008810d095 0xe8053499871f1b07 0x1e8053499871f1b0

def z663 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0xa8010c78001cf8cf 0xaa8010c78001cf8c

def z664 : W := mkw 0xd0081108ef0ddf50 0x9d0081108ef0ddf5 0x010000007f1fffff 0x0010000007f1ffff

def z665 : W := mkw 0x800001000800d600 0x1800001000800d60 0x000000000000ff08 0x0000000000000ff0

def z666 : W := mkw 0x820851007fdbd600 0xf820851007fdbd60 0x010000007fffff0f 0x0010000007fffff0

def z667 : W := mkw 0x80ffafd56600460f 0x880ffafd56600460 0xfeffffff87000700 0xffeffffff8700070

def z668 : W := mkw 0x0063ac550000000d 0x00063ac550000000 0xbee3fc7f80000000 0xbbee3fc7f8000000

def z669 : W := mkw 0x209ce3874442442b 0x4209ce3874442442 0x461cf38784030430 0x5461cf3878403043

def z670 : W := mkw 0x20ffeff7446264af 0x420ffeff7446264a 0x12facb6640e0e000 0x012facb6640e0e00

def z671 : W := mkw 0x51631c7899bdb9d4 0x151631c7899bdb9d 0xb9e73cf9fbfcfbcf 0xab9e73cf9fbfcfbc

def z672 : W := mkw 0x20084122446264a0 0x420084122446264a 0x161acb6640e0e4f8 0xe161acb6640e0e4f

def z673 : W := mkw 0x009c400066420000 0xc009c40006642000 0xfbfec0007fe30007 0x1fbfec0007fe3000

def z674 : W := mkw 0xd0b41e88ab0d9b56 0x9d0b41e88ab0d9b5 0x21e53499bb1c1b02 0x021e53499bb1c1b0

def z675 : W := mkw 0x41f7aefd18b4b8cf 0x141f7aefd18b4b8c 0xb9e73cf9f8fcf8cf 0xab9e73cf9f8fcf8c

def z676 : W := mkw 0x0008010044004400 0x0000801004400440 0x000000004400e409 0x0000000004400e40

def z677 : W := mkw 0x00b40ed500000007 0x000b40ed50000000 0x7cfc0fff80000000 0xe7cfc0fff8000000

def z678 : W := mkw 0x416b0d785cb4fcc4 0x1416b0d785cb4fcc 0xf9fb0f787cfcfccf 0xef9fb0f787cfcfcc

def z679 : W := mkw 0x0000100001090000 0x0000010000109000 0x4004300007030000 0x1400430000703000

def z680 : W := mkw 0x0043a05500000009 0x00043a0550000000 0xee07f4ff80000000 0xfee07f4ff8000000

def z681 : W := mkw 0x20084022446220a0 0x420084022446220a 0xde1ac06644e300f5 0x9de1ac06644e300f

def z682 : W := mkw 0x216b4d725cf2f4a4 0x5216b4d725cf2f4a 0x13facb6678e0e000 0x013facb6678e0e00

def z683 : W := mkw 0x0008010044004400 0x0000801004400440 0x781c0f804700ff0b 0x6781c0f804700ff0

def z684 : W := mkw 0x02d7a00032900008 0xa02d7a0003290000 0x01e0000038000000 0x001e000003800000

def z685 : W := mkw 0x0000028500000003 0x0000002850000000 0x0400038780000000 0x4040003878000000

def z686 : W := mkw 0x22dff12277fb64a8 0xe22dff12277fb64a 0xfbfffb667fffe007 0x1fbfffb667fffe00

def z687 : W := mkw 0x02dfb00077990008 0xa02dfb0007799000 0x79fd30007f1c0003 0x079fd30007f1c000

def z688 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x7afecfe600000000 0x67afecfe60000000

def z689 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x11e20c7878e0f8c8 0xa11e20c7878e0f8c

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0x58180b0000000000 0x658180b000000000

def z691 : W := mkw 0x0008400044420000 0x4000840004442000 0x4218c00004030000 0x14218c0000403000

def z692 : W := mkw 0x80200f800800d606 0x180200f800800d60 0x39e00f807800ff0b 0x639e00f807800ff0

def z693 : W := mkw 0x41ff0c787eb4b8c4 0x941ff0c787eb4b8c 0xf9ff0c787ffcf8cf 0xaf9ff0c787ffcf8c

def z694 : W := mkw 0xa0bc4fa26e62f6a6 0xda0bc4fa26e62f6a 0x7bfecfe67fe0ff0b 0x67bfecfe67fe0ff0

def z695 : W := mkw 0x024bf00055db0008 0x6024bf00055db000 0xda1bf00044ff0005 0x1da1bf00044ff000

def z696 : W := mkw 0x4100002810b428c0 0x04100002810b428c 0x0000000000fc00c4 0x00000000000fc00c

def z697 : W := mkw 0x50001008810d0950 0x050001008810d095 0xec053499801f00f4 0xfec053499801f00f

def z698 : W := mkw 0xc1ff0fd87e94de46 0x9c1ff0fd87e94de4 0x79fd0f987f1cff0b 0x679fd0f987f1cff0

def z699 : W := mkw 0x00630c5000000004 0x000630c500000000 0x20e1041800000000 0x020e104180000000

def z700 : W := mkw 0x5100102899bdb9d0 0x15100102899bdb9d 0xed053499ffffffff 0xfed053499fffffff

def z701 : W := mkw 0x0000100001090000 0x0000010000109000 0x80013000001f0004 0x180013000001f000

def z702 : W := mkw 0x00630c5010900004 0x000630c501090000 0xb9e30c7878fc0007 0xab9e30c7878fc000

def z703 : W := mkw 0x0000000000000000 0x0000000000000000 0x2005349980000000 0x0200534998000000

def z704 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x79fc0f807800e000 0x679fc0f807800e00

def z705 : W := mkw 0x00630c5008009004 0x100630c500800900 0xb9e30c787800f80b 0xab9e30c787800f80

def z706 : W := mkw 0x82dff1007fdbd608 0xf82dff1007fdbd60 0xfbfff0007fffff0f 0x1fbfff0007fffff0

def z707 : W := mkw 0x00630c5018909004 0x100630c501890900 0xb9e30c7878fcf80f 0xab9e30c7878fcf80

def z708 : W := mkw 0x0043000010900000 0x0004300001090000 0xb9e3041878fc0007 0xab9e3041878fc000

def z709 : W := mkw 0x02dff10077db4408 0xe02dff10077db440 0xfbfffb007fffe007 0x1fbfffb007fffe00

def z710 : W := mkw 0x00200ed500000007 0x000200ed50000000 0xfe1fffff80000000 0xffe1fffff8000000

def z711 : W := mkw 0x009c5000674b0000 0xc009c5000674b000 0xfbfff0007fff0007 0x1fbfff0007fff000

def z712 : W := mkw 0x616b4d5a5cd6dc64 0x5616b4d5a5cd6dc6 0x67f9c71e3c1f1c32 0x567f9c71e3c1f1c3

def z713 : W := mkw 0x7143507a91ff29f0 0x47143507a91ff29f 0x8603f07f80ff00f4 0x98603f07f80ff00f

def z714 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x11e20c7878fcf8cf 0xa11e20c7878fcf8c

def z715 : W := mkw 0x41630c2818b4b8c4 0x141630c2818b4b8c 0xb9e30c0078fcf8cf 0x2b9e30c0078fcf8c

def z716 : W := mkw 0x00630c5000000004 0x000630c500000000 0xfeffffff80000000 0xffeffffff8000000

def z717 : W := mkw 0x0043400010d20000 0x40043400010d2000 0xbbe3c00078ff0007 0x1bbe3c00078ff000

def z718 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xf9fd3f807f00ff0b 0x7f9fd3f807f00ff0

def z719 : W := mkw 0xa0bc4f826e42d626 0xda0bc4f826e42d62 0xfffecfe67f03ff3b 0xffffecfe67f03ff3

def z720 : W := mkw 0x20084122446264a0 0x420084122446264a 0xde1acfe644e3fffd 0xfde1acfe644e3fff

def z721 : W := mkw 0x0043000010900000 0x0004300001090000 0x91e3000078fc0004 0x091e3000078fc000

def z722 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xbde30cf9f8fcf8cf 0xebde30cf9f8fcf8c

def z723 : W := mkw 0x82dff10077db4608 0xe82dff10077db460 0xfbfff0007fff0707 0x1fbfff0007fff070

def z724 : W := mkw 0xc1630ef818b4bac6 0x1c1630ef818b4bac 0xb9e30cf878fcfbcf 0xab9e30cf878fcfbc

def z725 : W := mkw 0x0243f00011db0008 0x60243f00011db000 0x93e3f00078ff0004 0x193e3f00078ff000

def z726 : W := mkw 0x41200d780824fcc4 0x141200d780824fcc 0x00000f780000fcc8 0xe00000f780000fcc

def z727 : W := mkw 0x4163ac7d18b4b8cd 0x14163ac7d18b4b8c 0xfffbff7ff8fcf8cf 0xffffbff7ff8fcf8c

def z728 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x13fac00078ff0004 0x013fac00078ff000

def z729 : W := mkw 0x20084122446264a0 0x420084122446264a 0xc61acb6604e3e4fc 0xfc61acb6604e3e4f

def z730 : W := mkw 0x0043000010900000 0x0004300001090000 0xf9e7300078fc0007 0x1f9e7300078fc000

def z731 : W := mkw 0xc1200ff80824fec6 0x1c1200ff80824fec 0x00000f780000f8c8 0xa00000f780000f8c

def z732 : W := mkw 0x80f7aed52200020f 0x880f7aed52200020 0xfeffffff83000300 0xffeffffff8300030

def z733 : W := mkw 0x12dff285f7db011b 0xe12dff285f7db011 0xfffff387ffff0737 0x5fffff387ffff073

def z734 : W := mkw 0x02285ed577db0007 0xe02285ed577db000 0x05000fffffff0007 0xe05000fffffff000

def z735 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x33fff0007fff0007 0x033fff0007fff000

def z736 : W := mkw 0x5143107891bd29d0 0x05143107891bd29d 0x8003007800ff00f4 0x88003007800ff00f

def z737 : W := mkw 0x61200c7a0824b8e4 0x161200c7a0824b8e 0x04000c7e0000f8f8 0xa04000c7e0000f8f

def z738 : W := mkw 0x229cf102674b4428 0xe229cf102674b442 0x421cf00007030430 0x1421cf0000703043

def z739 : W := mkw 0x50001008810d0950 0x050001008810d095 0x68053499871f1fff 0x668053499871f1ff

def z740 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfffb007fff0007 0x7fbfffb007fff000

def z741 : W := mkw 0x12dff000f7db0118 0xe12dff000f7db011 0xfffff499ffff0737 0xffffff499ffff073

def z742 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x01e0000078fcf8cf 0x001e0000078fcf8c

def z743 : W := mkw 0x50001008810d0950 0x050001008810d095 0x64053499871f1ffa 0xf64053499871f1ff

def z744 : W := mkw 0x22d7b12233b964a8 0xa22d7b12233b964a 0x25e53b663b1ce4fa 0xe25e53b663b1ce4f

def z745 : W := mkw 0x80b40e802a009206 0x980b40e802a00920 0x79e40c807f00ff0b 0x679e40c807f00ff0

def z746 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x7bfff0007ffc0003 0x07bfff0007ffc000

def z747 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xdbfbf0007cff0005 0x1dbfbf0007cff000

def z748 : W := mkw 0x80280f806e00d606 0x980280f806e00d60 0x39e00f807f00ff0b 0x639e00f807f00ff0

def z749 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x21e1041878fcf802 0x021e1041878fcf80

def z750 : W := mkw 0x43bcfc786f6fb8cc 0xf43bcfc786f6fb8c 0x421cfc780703f8c8 0xb421cfc780703f8c

def z751 : W := mkw 0x11631c7099b9b194 0x111631c7099b9b19 0x55e638e1ffe3e730 0x555e638e1ffe3e73

def z752 : W := mkw 0x50001008810d0950 0x050001008810d095 0xa8053499871f1fff 0xaa8053499871f1ff

def z753 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x96fbffff80000000 0xf96fbffff8000000

def z754 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff801c0007 0xffeffffff801c000

def z755 : W := mkw 0x0000000010900000 0x0000000001090000 0x39e0000078fc0007 0x039e0000078fc000

def z756 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x7ffccf867f00ff0b 0x77ffccf867f00ff0

def z757 : W := mkw 0x51200efd8824b9d7 0x151200efd8824b9d 0x04000fff8000fff8 0xe04000fff8000fff

def z758 : W := mkw 0x22dff10277db4428 0xe22dff10277db442 0xfbfff3067fff0007 0x1fbfff3067fff000

def z759 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfaffffff80000000 0x1faffffff8000000

def z760 : W := mkw 0x7008512ac56f6df0 0x47008512ac56f6df 0x321fffffc3fcfb02 0x0321fffffc3fcfb0

def z761 : W := mkw 0x4163ac7818b4b8cc 0x14163ac7818b4b8c 0xbbe3fc7878fcf8cf 0xbbbe3fc7878fcf8c

def z762 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x21e404807b00fb02 0x021e404807b00fb0

def z763 : W := mkw 0x80bc0f856e00d607 0x980bc0f856e00d60 0x7dfc0f87ff00ff0b 0x67dfc0f87ff00ff0

def z764 : W := mkw 0x51f7bedd999d995f 0x151f7bedd999d995 0x21e53499bb1c1b02 0x021e53499bb1c1b0

def z765 : W := mkw 0x024b500077db0000 0xe024b500077db000 0xf9e730007fff0007 0x1f9e730007fff000

def z766 : W := mkw 0x0043a05510900009 0x00043a0551090000 0xbfe3f07ff8fc0007 0x9bfe3f07ff8fc000

def z767 : W := mkw 0x00df400076d20000 0xc00df400076d2000 0xfbffc0007fff0007 0x1fbffc0007fff000

def z768 : W := mkw 0x80f7aed52a00920f 0x980f7aed52a00920 0xfffffffffb00fb0b 0xffffffffffb00fb0

def z769 : W := mkw 0x41200c2818b4b8c4 0x141200c2818b4b8c 0x11e0080078fcf8cf 0x011e0080078fcf8c

def z770 : W := mkw 0x00d7a2d50000000b 0x000d7a2d50000000 0xfefff3ff80000000 0xdfefff3ff8000000

def z771 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x79fd30007fff0007 0x079fd30007fff000

def z772 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xc61fffff80000000 0xfc61fffff8000000

def z773 : W := mkw 0x0043002010b02080 0x00043002010b0208 0xb9e3000078fce0cf 0x0b9e3000078fce0c

def z774 : W := mkw 0xa0bc4f826e42d626 0xda0bc4f826e42d62 0xfffccf867f03ffff 0xffffccf867f03fff

def z775 : W := mkw 0x809c01006e00d600 0x9809c01006e00d60 0x79fc04807f00ff0b 0x679fc04807f00ff0

def z776 : W := mkw 0x804ba1556e00d609 0x9804ba1556e00d60 0x8703f07fff00ff0b 0x98703f07fff00ff0

def z777 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff87000003 0xffeffffff8700000

def z778 : W := mkw 0x02dfe00076d20008 0xe02dfe00076d2000 0xfbffc0007ffc0007 0x0fbffc0007ffc000

def z779 : W := mkw 0x02dff28577db000b 0xe02dff28577db000 0xfbfff081ffff0007 0x1fbfff081ffff000

def z780 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xdefbfb7f80000000 0xfdefbfb7f8000000

def z781 : W := mkw 0x829cf385674b460b 0xe829cf385674b460 0x461cf38787030700 0x5461cf3878703070

def z782 : W := mkw 0x20084122446264a0 0x420084122446264a 0xfe1ecb6647e3e4ff 0xffe1ecb6647e3e4f

def z783 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff800004f8 0xffeffffff800004f

def z784 : W := mkw 0x40200c280824b8c4 0x140200c280824b8c 0xb9e30c7878fcf8cf 0xab9e30c7878fcf8c

def z785 : W := mkw 0x929cf380e74b471a 0xe929cf380e74b471 0x461cf38187030730 0x5461cf3818703073

def z786 : W := mkw 0x02dfe00076d20008 0xe02dfe00076d2000 0x13fac00078fc0007 0x013fac00078fc000

def z787 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x04000cf98000f8c8 0xe04000cf98000f8c

def z788 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xb9e30c7878fce0c4 0xab9e30c7878fce0c

def z789 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x66fdffff80000000 0xf66fdffff8000000

def z790 : W := mkw 0x0043000010900000 0x0004300001090000 0xfde73499f8fc0007 0xffde73499f8fc000

def z791 : W := mkw 0x00200c0018909004 0x100200c001890900 0x39e00c0078fcf80f 0x239e00c0078fcf80

def z792 : W := mkw 0xc1df03f876b46ec2 0x8c1df03f876b46ec 0xc01f03f807fc07c4 0xcc01f03f807fc07c

def z793 : W := mkw 0x004b400054d20000 0x4004b400054d2000 0xb9e300007cff0007 0x0b9e300007cff000

def z794 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x56feffff80000000 0xf56feffff8000000

def z795 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x01e000007f00ff0b 0x001e000007f00ff0

def z796 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x91e3087878fcf8cf 0x891e3087878fcf8c

def z797 : W := mkw 0x20084122446264a0 0x420084122446264a 0xd61acb6644e3e4f4 0xdd61acb6644e3e4f

def z798 : W := mkw 0x50f7bedd810d095f 0x050f7bedd810d095 0x12facb66071f1fff 0x012facb66071f1ff

def z799 : W := mkw 0x0043000010900000 0x0004300001090000 0x31e3000078fc0002 0x031e3000078fc000

def z800 : W := mkw 0x50001008810d0950 0x050001008810d095 0x64053499871f1fff 0x564053499871f1ff

def z801 : W := mkw 0x4163ac7d18b4b8cd 0x14163ac7d18b4b8c 0xb9e33c79f8fcf8cf 0xab9e33c79f8fcf8c

def z802 : W := mkw 0x80b40e802a009206 0x980b40e802a00920 0x21e40c803b00fb0a 0x221e40c803b00fb0

def z803 : W := mkw 0x22dff10277db4428 0xe22dff10277db442 0xfffffb067fffe43f 0x7fffffb067fffe43

def z804 : W := mkw 0x80bc0fd56e00d607 0x980bc0fd56e00d60 0x79fc0f99ff00ff0b 0x679fc0f99ff00ff0

def z805 : W := mkw 0x4163aefd18b4b8cf 0x14163aefd18b4b8c 0xbfe3fffff8fcf8cf 0xfbfe3fffff8fcf8c

def z806 : W := mkw 0x02d7f00033db0008 0xe02d7f00033db000 0xebe7f0003fff0007 0x1ebe7f0003fff000

def z807 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff0007fff04ff 0x1fbfff0007fff04f

def z808 : W := mkw 0x51200c788824b9d4 0x151200c788824b9d 0x00000c780000fff8 0xa00000c780000fff

def z809 : W := mkw 0x20084122446264a0 0x420084122446264a 0xfe1fffffc7e3ffff 0xffe1fffffc7e3fff

def z810 : W := mkw 0xc1bc0ff86e24fec6 0x9c1bc0ff86e24fec 0x401c0ff80700ffc8 0xe401c0ff80700ffc

def z811 : W := mkw 0xc1200ef80824bac6 0x1c1200ef80824bac 0x00000cf80000fbc8 0xa00000cf80000fbc

def z812 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xdbfac0007fff0007 0x1dbfac0007fff000

def z813 : W := mkw 0x50001008810d0950 0x050001008810d095 0xfc073499c7ff1fff 0xffc073499c7ff1ff

def z814 : W := mkw 0x00f7aed51890900f 0x100f7aed51890900 0xfffffffff8fcf80f 0xffffffffff8fcf80

def z815 : W := mkw 0x0043000010900000 0x0004300001090000 0x21e1000078fc0007 0x021e1000078fc000

def z816 : W := mkw 0x50001008810d0950 0x050001008810d095 0xa4053499871f1fff 0x9a4053499871f1ff

def z817 : W := mkw 0x02dff28077db000a 0xe02dff28077db000 0xfbfff3807fff0007 0x5fbfff3807fff000

def z818 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xa3e7f0007fff0007 0x1a3e7f0007fff000

def z819 : W := mkw 0x20084122446264a0 0x420084122446264a 0xde1acb6644e3e0f5 0x9de1acb6644e3e0f

def z820 : W := mkw 0x7008512ac56f6df0 0x47008512ac56f6df 0x0000000044ffe4fd 0x00000000044ffe4f

def z821 : W := mkw 0x61630c7a18b4b8e4 0x161630c7a18b4b8e 0xbde30c7e78fcf8ff 0xabde30c7e78fcf8f

def z822 : W := mkw 0x00d7a2d50000000b 0x000d7a2d50000000 0xde1ffbff80000000 0xfde1ffbff8000000

def z823 : W := mkw 0x32dff102f7db4538 0xe32dff102f7db453 0xfffff387ffff0737 0x5fffff387ffff073

def z824 : W := mkw 0x0043000010900000 0x0004300001090000 0xb9e3080078fce00f 0x2b9e3080078fce00

def z825 : W := mkw 0x80b40e802a009206 0x980b40e802a00920 0x31e40c807b00fb02 0x031e40c807b00fb0

def z826 : W := mkw 0x029c500077db0000 0xe029c500077db000 0x11f800007fff0007 0x011f800007fff000

def z827 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xbde30c7878fcfcff 0xebde30c7878fcfcf

def z828 : W := mkw 0x00d7000032900000 0x800d700003290000 0xb9e700007bfc0007 0x0b9e700007bfc000

def z829 : W := mkw 0x80b40f802a00d606 0x980b40f802a00d60 0x79fc0f803b00ff0a 0x679fc0f803b00ff0

def z830 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xf9fb0f7878fcf8cf 0xef9fb0f7878fcf8c

def z831 : W := mkw 0x00f7aed50800900f 0x100f7aed50800900 0xfeffffff8000f808 0xffeffffff8000f80

def z832 : W := mkw 0x0143002018b0b080 0x10143002018b0b08 0xb9e3000078fce007 0x0b9e3000078fce00

def z833 : W := mkw 0x009c000076900000 0x8009c00007690000 0x79fc00007ffc0007 0x079fc00007ffc000

def z834 : W := mkw 0x0063aed50000000f 0x00063aed50000000 0xde1bffff80000000 0xfde1bffff8000000

def z835 : W := mkw 0x4100002818b4b8c0 0x14100002818b4b8c 0x39e0000078fcf8cf 0x039e0000078fcf8c

def z836 : W := mkw 0x61200d7a0824fce4 0x161200d7a0824fce 0x00000f7e0000f8c8 0xa00000f7e0000f8c

def z837 : W := mkw 0x20084122446264a0 0x420084122446264a 0x561acb6644e3e4fd 0x5561acb6644e3e4f

def z838 : W := mkw 0x8263ff8019dbd60e 0x78263ff8019dbd60 0x8203ff8000ffff0c 0x78203ff8000ffff0

def z839 : W := mkw 0x00b40e8000000006 0x000b40e800000000 0xfeffffff80000000 0xffeffffff8000000

def z840 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x00000c780000f800 0x000000c780000f80

def z841 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffff0667fff0007 0x9fffff0667fff000

def z842 : W := mkw 0x51630efd98b4b9d7 0x151630efd98b4b9d 0xbde30ffff8fcffff 0xebde30ffff8fcfff

def z843 : W := mkw 0x02dff05577db0009 0xe02dff05577db000 0xfffff4ffffff0007 0xffffff4ffffff000

def z844 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff84030005 0xffeffffff8403000

def z845 : W := mkw 0x00200c0008009004 0x100200c000800900 0x39e40c807b00fb0b 0x239e40c807b00fb0

def z846 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff4007fff180f 0x3fbfff4007fff180

def z847 : W := mkw 0x41630efd18b4b8c7 0x141630efd18b4b8c 0xb9e30cf9f8fcf8cf 0xab9e30cf9f8fcf8c

def z848 : W := mkw 0x80bcafd56e00d60f 0x980bcafd56e00d60 0x7ffcffffff00ff0b 0xf7ffcffffff00ff0

def z849 : W := mkw 0x4194a2ad18b4b8cb 0x14194a2ad18b4b8c 0x471cf387f8fcf8cf 0x5471cf387f8fcf8c

def z850 : W := mkw 0xd0bc1f88ef0ddf56 0x9d0bc1f88ef0ddf5 0x95f93b19f81fe0f4 0x995f93b19f81fe0f

def z851 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xfdfc0f807f00ff0b 0xffdfc0f807f00ff0

def z852 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xe9e530007fff0007 0x1e9e530007fff000

def z853 : W := mkw 0x02dfb00077990008 0xa02dfb0007799000 0xf9ff30007ffc0007 0x0f9ff30007ffc000

def z854 : W := mkw 0x20084122446264a0 0x420084122446264a 0xfe1ecfe644e3e4fd 0xffe1ecfe644e3e4f

def z855 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xf9fe0f807fe0ff0f 0x6f9fe0f807fe0ff0

def z856 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xffffffffffff0007 0xfffffffffffff000

def z857 : W := mkw 0x0243b00011990008 0x20243b0001199000 0xb9e3300078fc0007 0x0b9e3300078fc000

def z858 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x51fc0f807f00ff08 0x651fc0f807f00ff0

def z859 : W := mkw 0x41200c280824b8c4 0x141200c280824b8c 0x00000c000000f8c8 0x200000c000000f8c

def z860 : W := mkw 0x01630c7018b0b084 0x101630c7018b0b08 0xb9e30c6078fcf80f 0x2b9e30c6078fcf80

def z861 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x7affffff80000000 0x67affffff8000000

def z862 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xfbfecf807f00ff0b 0x7fbfecf807f00ff0

def z863 : W := mkw 0x50001008810d0950 0x050001008810d095 0xec053fff871f1fff 0xfec053fff871f1ff

def z864 : W := mkw 0x00b4aed50000000f 0x000b4aed50000000 0xde1effff80000000 0xfde1effff8000000

def z865 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xf9fd0f807f1cff0f 0x6f9fd0f807f1cff0

def z866 : W := mkw 0x20084122446264a0 0x420084122446264a 0xfe1ffb6644e3e4fd 0xffe1ffb6644e3e4f

def z867 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xf9fd0f987f00ff0b 0xef9fd0f987f00ff0

def z868 : W := mkw 0x204b410254d24420 0x4204b410254d2442 0xfffbc3067cff0437 0x5fffbc3067cff043

def z869 : W := mkw 0x0243e00010d20008 0x60243e00010d2000 0xbbe3c00078fc0007 0x0bbe3c00078fc000

def z870 : W := mkw 0x61200d7a0824fce4 0x161200d7a0824fce 0x00000c780000fcf8 0xa00000c780000fcf

def z871 : W := mkw 0x52dfe008f6d60958 0xe52dfe008f6d6095 0x17fac499f8e01ff8 0xe17fac499f8e01ff

def z872 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xb9e30cf878fcffcf 0xeb9e30cf878fcffc

def z873 : W := mkw 0x20084122666264a0 0xc20084122666264a 0xdf1acb667fe3e4ff 0xfdf1acb667fe3e4f

def z874 : W := mkw 0x80bc0e806e009206 0x980bc0e806e00920 0x79fc0c807f00fb0b 0x279fc0c807f00fb0

def z875 : W := mkw 0x02d7b00033990008 0xa02d7b0003399000 0xfbfff0007bfc0007 0x1fbfff0007bfc000

def z876 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x000008780000e0c0 0x8000008780000e0c

def z877 : W := mkw 0x0043a00010900008 0x00043a0001090000 0xbbe3f00078fc0007 0x1bbe3f00078fc000

def z878 : W := mkw 0x7243f02a91ff29f8 0x67243f02a91ff29f 0x8603f07f80ff00f4 0x98603f07f80ff00f

def z879 : W := mkw 0x0094a2d50000000b 0x00094a2d50000000 0x461cf3ff80000000 0xd461cf3ff8000000

def z880 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xb1e30c7878fcf8c6 0x8b1e30c7878fcf8c

def z881 : W := mkw 0x20084122446264a0 0x420084122446264a 0x5a1acb6644e3e4fd 0x65a1acb6644e3e4f

def z882 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffffc0e00005 0xffeffffffc0e0000

def z883 : W := mkw 0x22dff10277db4428 0xe22dff10277db442 0xfffff3067fff04ff 0xffffff3067fff04f

def z884 : W := mkw 0x0243100033990000 0xa024310003399000 0xb9e300007bfc0007 0x0b9e300007bfc000

def z885 : W := mkw 0x024bf00055db0008 0x6024bf00055db000 0xfbfbf0007cff0007 0x1fbfbf0007cff000

def z886 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xb9e3041878fcf8cf 0x0b9e3041878fcf8c

def z887 : W := mkw 0x809c01006e00d600 0x9809c01006e00d60 0x21e400007f00ff0b 0x021e400007f00ff0

def z888 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x39f80f007f00ff0b 0x239f80f007f00ff0

def z889 : W := mkw 0x22dff10277db4428 0xe22dff10277db442 0xfbfff0007fff0437 0x1fbfff0007fff043

def z890 : W := mkw 0x0043000018909000 0x1004300001890900 0xb9e3000078fcf80f 0x0b9e3000078fcf80

def z891 : W := mkw 0x51630c7898b4b9d4 0x151630c7898b4b9d 0xfde30cf9fcffffff 0xffde30cf9fcfffff

def z892 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x39e30c7878fcf80b 0x239e30c7878fcf80

def z893 : W := mkw 0x00b4aed50000000f 0x000b4aed50000000 0x7efcffff80000000 0xf7efcffff8000000

def z894 : W := mkw 0xa0bc4f826e42d626 0xda0bc4f826e42d62 0xfffecf867fe3ff3f 0x7fffecf867fe3ff3

def z895 : W := mkw 0xa0b44ea22a62b2a6 0xda0b44ea22a62b2a 0xa7e6c4e63be31bf6 0x9a7e6c4e63be31bf

def z896 : W := mkw 0x0043000010900000 0x0004300001090000 0xfbfbc00078fc0007 0x1fbfbc00078fc000

def z897 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x000008600000f8c8 0x0000008600000f8c

def z898 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff83001b02 0xffeffffff83001b0

def z899 : W := mkw 0x829cf380674b460a 0xe829cf380674b460 0x421cf30007030000 0x1421cf3000703000

def z900 : W := mkw 0x51630c7898b4b9d4 0x151630c7898b4b9d 0xb9e30c7878fcffff 0xab9e30c7878fcfff

def z901 : W := mkw 0x0063ac550000000d 0x00063ac550000000 0xfefbff7f80000000 0xffefbff7f8000000

def z902 : W := mkw 0x02dff28577db000b 0xe02dff28577db000 0xfffff79fffff0007 0xffffff79fffff000

def z903 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x000004180000f8c8 0x0000004180000f8c

def z904 : W := mkw 0x61200fff0824fce7 0x161200fff0824fce 0x04000fff8000fcf8 0xe04000fff8000fcf

def z905 : W := mkw 0x1043100091990110 0x0104310009199011 0xfde73081ffff0737 0x5fde73081ffff073

def z906 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xfffffffff8fcf8cf 0xffffffffff8fcf8c

def z907 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x53fef0007fff0007 0x153fef0007fff000

def z908 : W := mkw 0x02dff00577db0009 0xe02dff00577db000 0xfffff007ffff0007 0x1fffff007ffff000

def z909 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x39fc0f807b00fb0b 0x239fc0f807b00fb0

def z910 : W := mkw 0x20ffeff7446264af 0x420ffeff7446264a 0x20e53499c4e3e4fd 0x020e53499c4e3e4f

def z911 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xbde33c79f8fcf8cf 0xbbde33c79f8fcf8c

def z912 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xf9fc0f807f03ff0f 0x7f9fc0f807f03ff0

def z913 : W := mkw 0xa0bc4f826e42d626 0xda0bc4f826e42d62 0x7bfccf867f00ff0b 0x67bfccf867f00ff0

def z914 : W := mkw 0x02dff10077db4408 0xe02dff10077db440 0xfbfff0007fffe40f 0x1fbfff0007fffe40

def z915 : W := mkw 0x80bc0fd56e00d607 0x980bc0fd56e00d60 0xfffecfffff00ff0b 0xffffecfffff00ff0

def z916 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x01e000007fff0007 0x001e000007fff000

def z917 : W := mkw 0x4143002818b4b8c0 0x14143002818b4b8c 0x21e1000078fcf8cf 0x021e1000078fcf8c

def z918 : W := mkw 0x024b500077db0000 0xe024b500077db000 0xfbfbc0007fff0007 0x1fbfbc0007fff000

def z919 : W := mkw 0x80df038076904602 0x880df03807690460 0xf9ff03807ffc0707 0x4f9ff03807ffc070

def z920 : W := mkw 0x02dfe00076d20008 0xe02dfe00076d2000 0x33fbc00078fc0002 0x033fbc00078fc000

def z921 : W := mkw 0x01630c7018b0b084 0x101630c7018b0b08 0x11e2086078fce007 0x011e2086078fce00

def z922 : W := mkw 0x029cf100674b4408 0xe029cf100674b440 0x421cf30007030400 0x5421cf3000703040

def z923 : W := mkw 0x00dfa00076900008 0x800dfa0007690000 0xfbfff0007ffc0007 0x1fbfff0007ffc000

def z924 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x12fbfb7f80000000 0x012fbfb7f8000000

def z925 : W := mkw 0x029c500077db0000 0xe029c500077db000 0x21e400007fff0007 0x021e400007fff000

def z926 : W := mkw 0x92dff380f7db471a 0xe92dff380f7db471 0xfffff381ffff0737 0x5fffff381ffff073

def z927 : W := mkw 0x41200efd0824b8c7 0x141200efd0824b8c 0x00000f7e0000f8c8 0xa00000f7e0000f8c

def z928 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x31fc0f807b00ff0a 0x631fc0f807b00ff0

def z929 : W := mkw 0x0043a05500000009 0x00043a0550000000 0xc61bf37f80000000 0xdc61bf37f8000000

def z930 : W := mkw 0xf008512aef6ffff0 0xdf008512aef6ffff 0x010000007fffffff 0x0010000007ffffff

def z931 : W := mkw 0x00f7aed50800900f 0x100f7aed50800900 0xffffffffff00ff0b 0xfffffffffff00ff0

def z932 : W := mkw 0x80b40e802a009206 0x980b40e802a00920 0x21e404807b00fb0b 0x021e404807b00fb0

def z933 : W := mkw 0x00630c2018b0b084 0x100630c2018b0b08 0xb9e30c6078fcf8cf 0xab9e30c6078fcf8c

def z934 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x39e10c1878fcf8cf 0x239e10c1878fcf8c

def z935 : W := mkw 0x50001008810d0950 0x050001008810d095 0xee07f4ff871f1fff 0xfee07f4ff871f1ff

def z936 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x28000c780000f8cb 0xa28000c780000f8c

def z937 : W := mkw 0x12dff000f7db0118 0xe12dff000f7db011 0xfffff081ffff07ff 0xffffff081ffff07f

def z938 : W := mkw 0x024bf00077db0008 0xe024bf00077db000 0xbbe3f0007fff0007 0x1bbe3f0007fff000

def z939 : W := mkw 0x80bc0fd06e00d606 0x980bc0fd06e00d60 0x79fc0ff87f00ff0b 0xe79fc0ff87f00ff0

def z940 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xb9e3087878fce0c7 0x8b9e3087878fce0c

def z941 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff0007fff040f 0x7fbfff0007fff040

def z942 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffff3067fff0007 0x5fffff3067fff000

def z943 : W := mkw 0x12dff000f7db0118 0xe12dff000f7db011 0xfbfff081ffff0307 0x1fbfff081ffff030

def z944 : W := mkw 0x0043a05500000009 0x00043a0550000000 0xfe1fffff80000000 0xffe1fffff8000000

def z945 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xa9e1041878fcf8cf 0xaa9e1041878fcf8c

def z946 : W := mkw 0x4143007818b4b8c0 0x14143007818b4b8c 0xb9e3007878fcf8cf 0x8b9e3007878fcf8c

def z947 : W := mkw 0x02d7f00033db0008 0xe02d7f00033db000 0xfbfff0003bff0006 0x1fbfff0003bff000

def z948 : W := mkw 0x20084122446264a0 0x420084122446264a 0xda1acb6644e3e4fd 0x1da1acb6644e3e4f

def z949 : W := mkw 0x82dff38077db460a 0xe82dff38077db460 0xfbfffb807fffe70f 0x7fbfffb807fffe70

def z950 : W := mkw 0x50001008810d0950 0x050001008810d095 0xe8053499871f1fff 0x1e8053499871f1ff

def z951 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff8007fffe00f 0x3fbfff8007fffe00

def z952 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xb3fff0007bff0006 0x1b3fff0007bff000

def z953 : W := mkw 0x02dff2d577db000b 0xe02dff2d577db000 0xfffff3ffffff0007 0xdfffff3ffffff000

def z954 : W := mkw 0x20084122446264a0 0x420084122446264a 0xec053499c4e3e4fd 0xfec053499c4e3e4f

def z955 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xd6fffbff80000000 0xdd6fffbff8000000

def z956 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff0007bfc0002 0x1fbfff0007bfc000

def z957 : W := mkw 0x004b000054900000 0x0004b00005490000 0xf9fb00007cfc0007 0x0f9fb00007cfc000

def z958 : W := mkw 0x20004022006220a0 0x420004022006220a 0xde1acb6640e3e0fd 0xfde1acb6640e3e0f

def z959 : W := mkw 0x41200c2818b4b8c4 0x141200c2818b4b8c 0xb9e10c1878fcf8cf 0xab9e10c1878fcf8c

def z960 : W := mkw 0x00f7aed51090000f 0x000f7aed51090000 0xfffffffff8e00000 0xffffffffff8e0000

def z961 : W := mkw 0x809c01006e00d600 0x9809c01006e00d60 0x11f800007f00ff0b 0x011f800007f00ff0

def z962 : W := mkw 0x02dff05577db0009 0xe02dff05577db000 0xfffffb7fffff0007 0xffffffb7fffff000

def z963 : W := mkw 0x029c500077db0000 0xe029c500077db000 0xfbfec0007fff0007 0x1fbfec0007fff000

def z964 : W := mkw 0x82dff38077db460a 0xe82dff38077db460 0xfbfff7807fff1f0f 0x7fbfff7807fff1f0

def z965 : W := mkw 0x80b40f802a00d606 0x980b40f802a00d60 0x69e40f803f00ff0b 0x669e40f803f00ff0

def z966 : W := mkw 0x00d7a05500000009 0x000d7a0550000000 0xfefffb7f80000000 0xffefffb7f8000000

def z967 : W := mkw 0x41200c2818b4b8c4 0x141200c2818b4b8c 0x21e0040078fcf8cf 0x021e0040078fcf8c

def z968 : W := mkw 0x80280d006e00d604 0x980280d006e00d60 0x79f80f007f00ff0b 0x679f80f007f00ff0

def z969 : W := mkw 0x20084122446264a0 0x420084122446264a 0x161acb6644e3e4fd 0xe161acb6644e3e4f

def z970 : W := mkw 0x20004122006264a0 0x420004122006264a 0xde1acb6600e3e4fc 0xfde1acb6600e3e4f

def z971 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x11e2086078fcf802 0x011e2086078fcf80

def z972 : W := mkw 0x329cf102e74b4538 0xe329cf102e74b453 0x461cf38787030730 0x5461cf3878703073

def z973 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x76ffffff80000000 0x576ffffff8000000

def z974 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x31fc0f807f00ff0b 0x031fc0f807f00ff0

def z975 : W := mkw 0xe1200ffa0824fee6 0x1e1200ffa0824fee 0x04000ffe0000fff8 0xe04000ffe0000fff

def z976 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xbbfbf00078ff0007 0x1bbfbf00078ff000

def z977 : W := mkw 0x4143007810b428c0 0x04143007810b428c 0xb9e3087878fce0cf 0xab9e3087878fce0c

def z978 : W := mkw 0x829c5380674b4602 0xe829c5380674b460 0x401c038007030700 0x4401c03800703070

def z979 : W := mkw 0x80bc4f806e42d606 0xd80bc4f806e42d60 0x7bfccf807f03ff0b 0x77bfccf807f03ff0

def z980 : W := mkw 0x00630c0018909004 0x100630c001890900 0xb9e3080078fce007 0x0b9e3080078fce00

def z981 : W := mkw 0x4143002818b4b8c0 0x14143002818b4b8c 0x11e2000078fcf8cf 0x011e2000078fcf8c

def z982 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x39e40c807f00ff0b 0x239e40c807f00ff0

def z983 : W := mkw 0x809c03806e00d602 0x9809c03806e00d60 0x79fc03807f00ff0b 0x479fc03807f00ff0

def z984 : W := mkw 0x00f7aed52200000f 0x800f7aed52200000 0xffffffffbb000002 0xfffffffffbb00000

def z985 : W := mkw 0x229cf102674b4428 0xe229cf102674b442 0x421cf30607030000 0x1421cf3060703000

def z986 : W := mkw 0x00bc0c006e009004 0x900bc0c006e00900 0x79fc0c807f00ff0b 0x679fc0c807f00ff0

def z987 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xfde30c7878fcf8cf 0xffde30c7878fcf8c

def z988 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xfde73cf9fffcffcf 0xffde73cf9fffcffc

def z989 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfffffffff8000003 0xffffffffff800000

def z990 : W := mkw 0x41200c2818b4b8c4 0x141200c2818b4b8c 0xb9e20c6078fcf8cf 0xab9e20c6078fcf8c

def z991 : W := mkw 0x80bcaf856e00d60f 0x980bcaf856e00d60 0x79fc3f81ff00ff0b 0x679fc3f81ff00ff0

def z992 : W := mkw 0x024b500077db0000 0xe024b500077db000 0x11e200007fff0007 0x011e200007fff000

def z993 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xb9e73cf9f8fcf8cf 0xab9e73cf9f8fcf8c

def z994 : W := mkw 0x0043a05500000009 0x00043a0550000000 0x961bfb7f80000000 0x9961bfb7f8000000

def z995 : W := mkw 0x00f7aed50800900f 0x100f7aed50800900 0xfffffffff800e000 0xffffffffff800e00

def z996 : W := mkw 0x82dff38577db460b 0xe82dff38577db460 0xfffff387ffff0707 0x5fffff387ffff070

def z997 : W := mkw 0x80f7aed52a00920f 0x980f7aed52a00920 0xffffffffb8000000 0xfffffffffb800000

def z998 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x79fc0b007f00ff0b 0x079fc0b007f00ff0

def z999 : W := mkw 0x0043100011990000 0x0004310001199000 0xb9e300007fff0007 0x0b9e300007fff000

def z1000 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x7dfc0f807f00fffb 0xe7dfc0f807f00fff

def z1001 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x61fc0f803f00ff0a 0x661fc0f803f00ff0

def z1002 : W := mkw 0x41630efd18b4b8c7 0x141630efd18b4b8c 0xfffbcffff8fcf8cf 0xffffbcffff8fcf8c

def z1003 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x18000c784000f8c9 0xa18000c784000f8c

def z1004 : W := mkw 0x0043000010900000 0x0004300001090000 0x11e2000078fc0007 0x011e2000078fc000

def z1005 : W := mkw 0x80f7aed50800920f 0x180f7aed50800920 0xfeffffff80001b00 0xffeffffff80001b0

def z1006 : W := mkw 0x0043000010900000 0x0004300001090000 0xa1e3000038fc0006 0x0a1e3000038fc000

def z1007 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffff4807fff1fff 0xffffff4807fff1ff

def z1008 : W := mkw 0x50001008810d0950 0x050001008810d095 0xfc073cf9871f1fff 0xffc073cf9871f1ff

def z1009 : W := mkw 0x00d7a2d50000000b 0x000d7a2d50000000 0xee1ff7ff80000000 0xfee1ff7ff8000000

def z1010 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff4807fff1b07 0x1fbfff4807fff1b0

def z1011 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffff499ffff1f0f 0xffffff499ffff1f0

def z1012 : W := mkw 0x82dff38077db460a 0xe82dff38077db460 0xfbfff3007fff0007 0x1fbfff3007fff000

def z1013 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x73fff0007fff0002 0x173fff0007fff000

def z1014 : W := mkw 0x02f7aed53290000f 0xa02f7aed53290000 0xffffffffb8000000 0xfffffffffb800000

def z1015 : W := mkw 0xa0bc0f826e00d626 0x9a0bc0f826e00d62 0x7dfc0f867f00ff3b 0x67dfc0f867f00ff3

def z1016 : W := mkw 0x41200c7d0824b8c5 0x141200c7d0824b8c 0x04000c7f8000f8c8 0xa04000c7f8000f8c

def z1017 : W := mkw 0x50001008810d0950 0x050001008810d095 0xfc053c99c71fffff 0xffc053c99c71ffff

def z1018 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xb9e30c787ffcffcf 0xab9e30c787ffcffc

def z1019 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xfbfbcc7878fcf8cf 0xbfbfbcc7878fcf8c

def z1020 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xb9e30c787cfffcff 0xab9e30c787cfffcf

def z1021 : W := mkw 0x80b40f802a00d606 0x980b40f802a00d60 0x21e40f803b00fb02 0x021e40f803b00fb0

def z1022 : W := mkw 0x20084122446264a0 0x420084122446264a 0x961acb6644e3e4fd 0x9961acb6644e3e4f

def z1023 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x39e20c6078fcf8cf 0x239e20c6078fcf8c

def z1024 : W := mkw 0x01630c7018b0b084 0x101630c7018b0b08 0x31e3086078fce002 0x031e3086078fce00

def z1025 : W := mkw 0x20084122446264a0 0x420084122446264a 0xfe1acf6644e3fcff 0xffe1acf6644e3fcf

def z1026 : W := mkw 0x20084122446264a0 0x420084122446264a 0xde1efbe7c4e3e4fd 0xfde1efbe7c4e3e4f

def z1027 : W := mkw 0x02dff28577db000b 0xe02dff28577db000 0xfffffbe7ffff0007 0xffffffbe7ffff000

def z1028 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xffffffffff00ff0b 0xfffffffffff00ff0

def z1029 : W := mkw 0x00b4aed50000000f 0x000b4aed50000000 0xee1dffff80000000 0xfee1dffff8000000

def z1030 : W := mkw 0x01f7aed51890900f 0x101f7aed51890900 0xffffffffb8000000 0xfffffffffb800000

def z1031 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x13fbf00078fc0000 0x013fbf00078fc000

def z1032 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xbefbff7f80000000 0xbbefbff7f8000000

def z1033 : W := mkw 0x7108512addfffdf0 0x57108512addfffdf 0x010000007fffffff 0x0010000007ffffff

def z1034 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x79fc0f807f03ffff 0x679fc0f807f03fff

def z1035 : W := mkw 0xa29cf382674b462a 0xea29cf382674b462 0x461cf38607030730 0x5461cf3860703073

def z1036 : W := mkw 0x12dff000f7db0118 0xe12dff000f7db011 0xfbfff0007fff0737 0x1fbfff0007fff073

def z1037 : W := mkw 0x0094a2850000000b 0x00094a2850000000 0xfe1fffff80000000 0xffe1fffff8000000

def z1038 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xf9e30c787cfcfccf 0xef9e30c787cfcfcc

def z1039 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xbde30c7878fff8ff 0xbbde30c7878fff8f

def z1040 : W := mkw 0xa0bcef876e42d62f 0xda0bcef876e42d62 0x7ffcff87ff03ff3b 0x77ffcff87ff03ff3

def z1041 : W := mkw 0x0043000010900000 0x0004300001090000 0xf9e704807ffc1f0f 0x6f9e704807ffc1f0

def z1042 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x21e40f807f00ff0b 0x621e40f807f00ff0

def z1043 : W := mkw 0x00d7a00000000008 0x000d7a0000000000 0xfeffffff80000000 0xffeffffff8000000

def z1044 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x88000c780000f8cd 0xa88000c780000f8c

def z1045 : W := mkw 0x0243f00011db0008 0x60243f00011db000 0xfbe7f0007fff0007 0x1fbe7f0007fff000

def z1046 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x7bfec0007fff0007 0x07bfec0007fff000

def z1047 : W := mkw 0xc1200d780824fec4 0x1c1200d780824fec 0x00000c780000ffc8 0xa00000c780000ffc

def z1048 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff84030430 0xffeffffff8403043

def z1049 : W := mkw 0x0043000010900000 0x0004300001090000 0xb9e3086078fc0007 0xab9e3086078fc000

def z1050 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xb9e70cf87bfcfbcf 0xab9e70cf87bfcfbc

def z1051 : W := mkw 0x20084122446264a0 0x420084122446264a 0xfe1bcf7e44e3e4fd 0xffe1bcf7e44e3e4f

def z1052 : W := mkw 0x80bc4f806e42d606 0xd80bc4f806e42d60 0xfffecf807fe3ffff 0xffffecf807fe3fff

def z1053 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xbde30f7e78fcf8cf 0xebde30f7e78fcf8c

def z1054 : W := mkw 0x02dff05577db0009 0xe02dff05577db000 0xfbfff0667fff0007 0x1fbfff0667fff000

def z1055 : W := mkw 0x20084122446264a0 0x420084122446264a 0x121acb6640e3e0f4 0x0121acb6640e3e0f

def z1056 : W := mkw 0x00f7aed50800900f 0x100f7aed50800900 0xffffffffb8001802 0xfffffffffb800180

def z1057 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x11e3087878fce000 0x011e3087878fce00

def z1058 : W := mkw 0x80bcaf806e00d60e 0x980bcaf806e00d60 0x7bfcff807f00ff0b 0x77bfcff807f00ff0

def z1059 : W := mkw 0x80280d006e00d604 0x980280d006e00d60 0x79e40c807f00ff0b 0x679e40c807f00ff0

def z1060 : W := mkw 0x009c010066004400 0x8009c01006600440 0x79fc0f807f00ff0b 0x679fc0f807f00ff0

def z1061 : W := mkw 0x00d7a2d50000000b 0x000d7a2d50000000 0x861bf37f80000000 0x9861bf37f8000000

def z1062 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xfde73cf9fcfffcff 0xffde73cf9fcfffcf

def z1063 : W := mkw 0x51200c788824b9d4 0x151200c788824b9d 0x04000c798000f8f8 0xa04000c798000f8f

def z1064 : W := mkw 0x50001008810d0950 0x050001008810d095 0xde1acb66071f1fff 0xfde1acb66071f1ff

def z1065 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffffb667fff04ff 0xffffffb667fff04f

def z1066 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x59f80b007f00ff0b 0x659f80b007f00ff0

def z1067 : W := mkw 0x02d7b00033990008 0xa02d7b0003399000 0x31e730007bfc0002 0x031e730007bfc000

def z1068 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfffb667fff0007 0x1fbfffb667fff000

def z1069 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xf9e70cf878fcf8cf 0xef9e70cf878fcf8c

def z1070 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x63fdf0007fff0007 0x163fdf0007fff000

def z1071 : W := mkw 0x20084122446264a0 0x420084122446264a 0x9a1acb6644e3e4fd 0xa9a1acb6644e3e4f

def z1072 : W := mkw 0x00280d004c00d404 0x100280d004c00d40 0x79fc0f807f00ff0b 0x679fc0f807f00ff0

def z1073 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff84000409 0xffeffffff8400040

def z1074 : W := mkw 0x12dff000f7db0118 0xe12dff000f7db011 0xfffff481ffff1f3f 0x7fffff481ffff1f3

def z1075 : W := mkw 0x80b40f802a00d606 0x980b40f802a00d60 0x21e404803b00ff0a 0x021e404803b00ff0

def z1076 : W := mkw 0x80bcaf856e00d60f 0x980bcaf856e00d60 0xfffeffe7ff00ff0b 0xffffeffe7ff00ff0

def z1077 : W := mkw 0x20084122446264a0 0x420084122446264a 0xde1ecbe647e3e7fd 0xfde1ecbe647e3e7f

def z1078 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffff0007fff00f7 0x9fffff0007fff00f

def z1079 : W := mkw 0x004b400054d20000 0x4004b400054d2000 0xbbfbc00078fc0007 0x0bbfbc00078fc000

def z1080 : W := mkw 0x00d7a00010900008 0x000d7a0001090000 0xb9e7300078fc0007 0x0b9e7300078fc000

def z1081 : W := mkw 0x20084122446264a0 0x420084122446264a 0xde1acb6640e3e0f4 0xfde1acb6640e3e0f

def z1082 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffff019ffff0007 0x9fffff019ffff000

def z1083 : W := mkw 0x02d7f00011db0008 0x602d7f00011db000 0xfbfff00078ff0007 0x1fbfff00078ff000

def z1084 : W := mkw 0x800801006e00d600 0x9800801006e00d60 0x39e000007f00ff0b 0x039e000007f00ff0

def z1085 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x00000478000018c0 0x800000478000018c

def z1086 : W := mkw 0x82dff28077db020a 0xe82dff28077db020 0xfbfff0807fff0307 0x1fbfff0807fff030

def z1087 : W := mkw 0xf0200faa8824fff6 0x1f0200faa8824fff 0x04000fff8000fff8 0xe04000fff8000fff

def z1088 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x7dfc0fe67f00ff0b 0xe7dfc0fe67f00ff0

def z1089 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x04000f7e0000f8c8 0xe04000f7e0000f8c

def z1090 : W := mkw 0xb09c5382e74b4732 0xcb09c5382e74b473 0x461cf38787030730 0x5461cf3878703073

def z1091 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0xde1acf7e0000f8c8 0xfde1acf7e0000f8c

def z1092 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x7dfc3f81ff00ff0b 0x77dfc3f81ff00ff0

def z1093 : W := mkw 0x51201c78892db9d4 0x151201c78892db9d 0x44043cf98703fff8 0xf44043cf98703fff

def z1094 : W := mkw 0x5343f07891ff29d8 0x65343f07891ff29d 0x8603f07980ff00f4 0x98603f07980ff00f

def z1095 : W := mkw 0x02df500077db0000 0xe02df500077db000 0xf9ff00007fff0007 0x0f9ff00007fff000

def z1096 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff0807fff0707 0x5fbfff0807fff070

def z1097 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xbaffffff80000000 0xabaffffff8000000

def z1098 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xb9e3086078fcf8cf 0x0b9e3086078fcf8c

def z1099 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x93fbf0007fff0007 0x193fbf0007fff000

def z1100 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xbbfbcf7e78fcf8cf 0xabbfbcf7e78fcf8c

def z1101 : W := mkw 0x00dfe00054d20008 0x400dfe00054d2000 0xfbfff0007cff0007 0x1fbfff0007cff000

def z1102 : W := mkw 0x80f7aed52a00920f 0x980f7aed52a00920 0xffffffffbf001f0b 0xfffffffffbf001f0

def z1103 : W := mkw 0x02dff28577db000b 0xe02dff28577db000 0xfbfff3067fff0007 0x1fbfff3067fff000

def z1104 : W := mkw 0x22dff38777db442b 0xe22dff38777db442 0xfffff387ffff0437 0x5fffff387ffff043

def z1105 : W := mkw 0x0000002000202080 0x0000000200020208 0xde1acb6644e3e4fd 0xfde1acb6644e3e4f

def z1106 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x79fc0f807b00fb02 0x679fc0f807b00fb0

def z1107 : W := mkw 0x004b010054904400 0x0004b01005490440 0xf9fb0b007cfce40f 0x6f9fb0b007cfce40

def z1108 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffff499ffff04ff 0xffffff499ffff04f

def z1109 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff00078ff0004 0x1fbfff00078ff000

def z1110 : W := mkw 0x004b500055db0000 0x4004b500055db000 0xfbfff0007fff0007 0x1fbfff0007fff000

def z1111 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xb9e730007fff0007 0x0b9e730007fff000

def z1112 : W := mkw 0x02d7b00033990008 0xa02d7b0003399000 0x21e530007bfc0007 0x021e530007bfc000

def z1113 : W := mkw 0x51630c7898b4b9d4 0x151630c7898b4b9d 0xb9e30cf9f8fcfbcf 0xab9e30cf9f8fcfbc

def z1114 : W := mkw 0x51200c788824b9d4 0x151200c788824b9d 0x00000cf98000fbc8 0xa00000cf98000fbc

def z1115 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffff081ffff0007 0x5fffff081ffff000

def z1116 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x11f80f807f00ff0b 0x611f80f807f00ff0

def z1117 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x00000cf80000ffc8 0xe00000cf80000ffc

def z1118 : W := mkw 0x51630c7898b4b9d4 0x151630c7898b4b9d 0xfde73cf9f8fcffff 0xffde73cf9f8fcfff

def z1119 : W := mkw 0x20084122446264a0 0x420084122446264a 0xfffacb667ce3e4ff 0xffffacb667ce3e4f

def z1120 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xfde70cf87fffffff 0xffde70cf87ffffff

def z1121 : W := mkw 0x01630c7018b0b084 0x101630c7018b0b08 0xb9e30c7878fce007 0xab9e30c7878fce00

def z1122 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x21e530007bfc0002 0x021e530007bfc000

def z1123 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xfffecfe67f03ffff 0xffffecfe67f03fff

def z1124 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x04000c780000fcf8 0xe04000c780000fcf

def z1125 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x79fc04807f00ff0b 0x079fc04807f00ff0

def z1126 : W := mkw 0x50001008810d0950 0x050001008810d095 0xfde53499ff1f1fff 0xffde53499ff1f1ff

def z1127 : W := mkw 0x02d7f00033db0008 0xe02d7f00033db000 0xbbe7f0007bff0007 0x1bbe7f0007bff000

def z1128 : W := mkw 0x51630c7898b4b9d4 0x151630c7898b4b9d 0xbde30c79f8fcf8ff 0xabde30c79f8fcf8f

def z1129 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xe6fff7ff80000000 0xde6fff7ff8000000

def z1130 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xfdfd3f99ff03ffff 0xffdfd3f99ff03fff

def z1131 : W := mkw 0x80bc4f806e42d606 0xd80bc4f806e42d60 0x79fc0f807fe3ff0f 0x679fc0f807fe3ff0

def z1132 : W := mkw 0x20084122446264a0 0x420084122446264a 0xfe1bcb6644ffe4ff 0xffe1bcb6644ffe4f

def z1133 : W := mkw 0x02dfe00076d20008 0xe02dfe00076d2000 0x93fbc00078fc0004 0x093fbc00078fc000

def z1134 : W := mkw 0x50001008810d0950 0x050001008810d095 0xee1df79f871f1fff 0xfee1df79f871f1ff

def z1135 : W := mkw 0x02dfe00076d20008 0xe02dfe00076d2000 0xfbfbc0007cff0007 0x1fbfbc0007cff000

def z1136 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x99e2086078fcf8cf 0xa99e2086078fcf8c

def z1137 : W := mkw 0x51630c7898b4b9d4 0x151630c7898b4b9d 0xfde70cf9fffcffff 0xefde70cf9fffcfff

def z1138 : W := mkw 0x71200d7a8824fdf4 0x171200d7a8824fdf 0x04000fff8000fff8 0xe04000fff8000fff

def z1139 : W := mkw 0x12dff000f7db0118 0xe12dff000f7db011 0xfffff001ffff0037 0x1fffff001ffff003

def z1140 : W := mkw 0x5143b07d91bd29d9 0x05143b07d91bd29d 0x8603f07f80ff00f4 0x98603f07f80ff00f

def z1141 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xb9e30c7878fcf802 0xab9e30c7878fcf80

def z1142 : W := mkw 0x02dff10077db4408 0xe02dff10077db440 0xfffffb667fffe40f 0xffffffb667fffe40

def z1143 : W := mkw 0x80bc4f806e42d606 0xd80bc4f806e42d60 0xfffecfe67fe3ff0f 0xffffecfe67fe3ff0

def z1144 : W := mkw 0x4043002810b428c0 0x04043002810b428c 0xb9e30c7878fcf8cf 0xab9e30c7878fcf8c

def z1145 : W := mkw 0x029cf00077db0008 0xe029cf00077db000 0x7bfcf0007fff0007 0x17bfcf0007fff000

def z1146 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x98020c780000f8c8 0xa98020c780000f8c

def z1147 : W := mkw 0x80280d006e00d604 0x980280d006e00d60 0x11e008007f00ff0b 0x011e008007f00ff0

def z1148 : W := mkw 0x4143002818b4b8c0 0x14143002818b4b8c 0xb9e3041878fcf8cf 0xab9e3041878fcf8c

def z1149 : W := mkw 0x024b500077db0000 0xe024b500077db000 0x21e100007fff0007 0x021e100007fff000

def z1150 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xb9e30c7878fcf807 0x0b9e30c7878fcf80

def z1151 : W := mkw 0x22dff00277db0028 0xe22dff00277db002 0xfffff0067fff0037 0x1fffff0067fff003

def z1152 : W := mkw 0x00d7a2851090000b 0x000d7a2851090000 0xfffff387f8fc0007 0x5fffff387f8fc000

def z1153 : W := mkw 0x02dfe00076d20008 0xe02dfe00076d2000 0xfbfff00078fc0007 0x1fbfff00078fc000

def z1154 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff8000180b 0xffeffffff8000180

def z1155 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x79fc0f807f00fb03 0x079fc0f807f00fb0

def z1156 : W := mkw 0x02d7f00033db0008 0xe02d7f00033db000 0x23e7f0003bfc0002 0x023e7f0003bfc000

def z1157 : W := mkw 0x02d7f00033db0008 0xe02d7f00033db000 0x83e3f00038ff0004 0x183e3f00038ff000

def z1158 : W := mkw 0x02dff05077db0008 0xe02dff05077db000 0xfbfff0787fff0007 0x9fbfff0787fff000

def z1159 : W := mkw 0x41b4aefd0824b8cf 0x141b4aefd0824b8c 0x461cffff8000f8c8 0xf461cffff8000f8c

def z1160 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff800000cd 0xffeffffff800000c

def z1161 : W := mkw 0x0043100011990000 0x0004310001199000 0xb9e730007bfc0007 0x0b9e730007bfc000

def z1162 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0x13fac0007bfc0002 0x013fac0007bfc000

def z1163 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffffc000e009 0xffeffffffc000e00

def z1164 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x7dfc0f807f03ff3b 0x77dfc0f807f03ff3

def z1165 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff87031fff 0xffeffffff87031ff

def z1166 : W := mkw 0x00d7000010900000 0x000d700001090000 0xf9ff000078fc0007 0x0f9ff000078fc000

def z1167 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x7bfecfe67f00ff0b 0x67bfecfe67f00ff0

def z1168 : W := mkw 0x0243500011db0000 0x60243500011db000 0xb9e3000078ff0007 0x0b9e3000078ff000

def z1169 : W := mkw 0x80bc4f806e42d606 0xd80bc4f806e42d60 0x7bfecf807fe0ff0b 0x67bfecf807fe0ff0

def z1170 : W := mkw 0x0043000010900000 0x0004300001090000 0xf9e700007ffc0007 0x0f9e700007ffc000

def z1171 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xfffbcf7e7cfffcff 0xffffbcf7e7cfffcf

def z1172 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0xcc000c780403fcfd 0xfcc000c780403fcf

def z1173 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x91e30c7878fcf8cc 0xa91e30c7878fcf8c

def z1174 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff80001f08 0xffeffffff80001f0

def z1175 : W := mkw 0x41200c7818b4b8c4 0x141200c7818b4b8c 0x39e00c7878fcf8cf 0xa39e00c7878fcf8c

def z1176 : W := mkw 0x20084122446264a0 0x420084122446264a 0x561acb6644e3e4f8 0xf561acb6644e3e4f

def z1177 : W := mkw 0x80bc0d006e00d604 0x980bc0d006e00d60 0x79fc0c007f00ff0b 0x279fc0c007f00ff0

def z1178 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x79fd3f99ff00ff0b 0x679fd3f99ff00ff0

def z1179 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xf9e30c787cfff8cf 0xbf9e30c787cfff8c

def z1180 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x71fc0f807f00ff02 0x471fc0f807f00ff0

def z1181 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xf9fe0fe07f00ff0b 0xef9fe0fe07f00ff0

def z1182 : W := mkw 0x02d7f00033db0008 0xe02d7f00033db000 0x21e530003bff0006 0x021e530003bff000

def z1183 : W := mkw 0x82bcef806e42d60e 0xf82bcef806e42d60 0x7bfccf807f00ff0b 0x67bfccf807f00ff0

def z1184 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x31e30c7878fcf8ca 0xa31e30c7878fcf8c

def z1185 : W := mkw 0x00f7aed51090000f 0x000f7aed51090000 0xfeffffff80fc0004 0xffeffffff80fc000

def z1186 : W := mkw 0x41280d784c24fcc4 0x141280d784c24fcc 0x58180f784400fcc9 0xe58180f784400fcc

def z1187 : W := mkw 0x0043100011990000 0x0004310001199000 0xb9e3300078ff0007 0x1b9e3300078ff000

def z1188 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff4187fff0007 0xbfbfff4187fff000

def z1189 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff499ffff0007 0x1fbfff499ffff000

def z1190 : W := mkw 0x02d7a00032900008 0xa02d7a0003290000 0xb9e3000078fc0007 0x0b9e3000078fc000

def z1191 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffff0007fff0007 0xffffff0007fff000

def z1192 : W := mkw 0x80200c002a009204 0x980200c002a00920 0x39e00c007b00fb0b 0x239e00c007b00fb0

def z1193 : W := mkw 0x4163ac7d18b4b8cd 0x14163ac7d18b4b8c 0xffe7fcfff8fcf8cf 0xfffe7fcfff8fcf8c

def z1194 : W := mkw 0x41630ef818b4b8c6 0x141630ef818b4b8c 0xb9e30ff878fcf8cf 0xeb9e30ff878fcf8c

def z1195 : W := mkw 0x0043000010900000 0x0004300001090000 0xf9e300007cff0007 0x1f9e300007cff000

def z1196 : W := mkw 0x00df000076900000 0x800df00007690000 0xb9fb000078fc0007 0x0b9fb000078fc000

def z1197 : W := mkw 0x829cf100674b4608 0xe829cf100674b460 0x421cf00007030700 0x1421cf0000703070

def z1198 : W := mkw 0x004b000076900000 0x8004b00007690000 0xb9e300007ffc0007 0x0b9e300007ffc000

def z1199 : W := mkw 0x41630efd18b4b8c7 0x141630efd18b4b8c 0xfde73ffff8fcf8cf 0xffde73ffff8fcf8c

def z1200 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xbbfff0007bfc0007 0x0bbfff0007bfc000

def z1201 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x11e2086078fce0c4 0x011e2086078fce0c

def z1202 : W := mkw 0x22dff10277db4428 0xe22dff10277db442 0xfffffb667fff0437 0xffffffb667fff043

def z1203 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xb6ffffff80000000 0x9b6ffffff8000000

def z1204 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xa1e3047878fcf8cf 0x8a1e3047878fcf8c

def z1205 : W := mkw 0x00630c7010b02084 0x000630c7010b0208 0xb9e30c7878fce0cf 0xab9e30c7878fce0c

def z1206 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0x68040cf80700ffcb 0xe68040cf80700ffc

def z1207 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x11f80b007b00fb02 0x011f80b007b00fb0

def z1208 : W := mkw 0x50001008810d0950 0x050001008810d095 0xc4053499871f1ffc 0xfc4053499871f1ff

def z1209 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xe3fff0003fff0006 0x1e3fff0003fff000

def z1210 : W := mkw 0x80280d006e00d604 0x980280d006e00d60 0x21e004007f00ff0b 0x021e004007f00ff0

def z1211 : W := mkw 0x0000000000000000 0x0000000000000000 0xde1bfb7f80000000 0xfde1bfb7f8000000

def z1212 : W := mkw 0x50001008810d0950 0x050001008810d095 0x24053499871f1fff 0xe24053499871f1ff

def z1213 : W := mkw 0x0043000010900000 0x0004300001090000 0xfde300007cff04ff 0xffde300007cff04f

def z1214 : W := mkw 0x00b40e8008009006 0x100b40e800800900 0x79fc0f807f00ff0b 0x679fc0f807f00ff0

def z1215 : W := mkw 0x02dff05577db0009 0xe02dff05577db000 0xfbfff019ffff0007 0x1fbfff019ffff000

def z1216 : W := mkw 0x41630c780824b8c4 0x141630c780824b8c 0x80030c780000f8c8 0xa80030c780000f8c

def z1217 : W := mkw 0x50001008810d0950 0x050001008810d095 0xfc1d3f99871f1fff 0xffc1d3f99871f1ff

def z1218 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x7dfc0f99ff00ff0b 0xe7dfc0f99ff00ff0

def z1219 : W := mkw 0x809c01006e00d600 0x9809c01006e00d60 0x79fc0b007f00ff0b 0x679fc0b007f00ff0

def z1220 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff0007fff1f0f 0x1fbfff0007fff1f0

def z1221 : W := mkw 0x50001008810d0950 0x050001008810d095 0xe4053499871f1ff6 0xde4053499871f1ff

def z1222 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff800300f4 0xffeffffff800300f

def z1223 : W := mkw 0x61284d7a4c66fce4 0x561284d7a4c66fce 0x4618cf7e0403fcf8 0xf4618cf7e0403fcf

def z1224 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x51fc0b807f00ff0b 0x451fc0b807f00ff0

def z1225 : W := mkw 0xc1200ffd0824fec7 0x1c1200ffd0824fec 0x04000fff8000ffc8 0xe04000fff8000ffc

def z1226 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xf9e70c787ffcf8cf 0xaf9e70c787ffcf8c

def z1227 : W := mkw 0x20084122446264a0 0x420084122446264a 0xde1bfb7fc4e3e4fd 0xfde1bfb7fc4e3e4f

def z1228 : W := mkw 0x00df100077990000 0x800df10007799000 0xf9ff30007fff0007 0x1f9ff30007fff000

def z1229 : W := mkw 0xd1200ff88824ffd6 0x1d1200ff88824ffd 0x04000ff98000fff8 0xe04000ff98000fff

def z1230 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xf9e73c7878fcf8cf 0xbf9e73c7878fcf8c

def z1231 : W := mkw 0xa0bc4f826e42d626 0xda0bc4f826e42d62 0x79fc0f807f03ff3b 0x679fc0f807f03ff3

def z1232 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfffff0007fff0437 0x5fffff0007fff043

def z1233 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x99e3087878fce0cd 0xa99e3087878fce0c

def z1234 : W := mkw 0x00200c0008009004 0x100200c000800900 0x39e00c007f00ff0b 0x239e00c007f00ff0

def z1235 : W := mkw 0x0043002010b02080 0x00043002010b0208 0xb9e3086078fce007 0x0b9e3086078fce00

def z1236 : W := mkw 0x4163ac7d0824b8cd 0x14163ac7d0824b8c 0x8603fc7f8000f8c8 0xb8603fc7f8000f8c

def z1237 : W := mkw 0x41200ef80824b8c6 0x141200ef80824b8c 0x00000ff80000f8c8 0xe00000ff80000f8c

def z1238 : W := mkw 0x4163ac7d18b4b8cd 0x14163ac7d18b4b8c 0xbbe3cc7e78fcf8cf 0xabbe3cc7e78fcf8c

def z1239 : W := mkw 0x02dff10077db4408 0xe02dff10077db440 0xfbffff807fffff0f 0x7fbffff807fffff0

def z1240 : W := mkw 0x0043000010900000 0x0004300001090000 0xfffbcb6678fc0007 0xffffbcb6678fc000

def z1241 : W := mkw 0xa2dff38277db462a 0xea2dff38277db462 0xfffff3867fff0737 0x5fffff3867fff073

def z1242 : W := mkw 0x0208500077db0000 0xe0208500077db000 0x39e000007fff0007 0x039e000007fff000

def z1243 : W := mkw 0x41630efd18b4b8c7 0x141630efd18b4b8c 0xb9e30f7e78fcf8cf 0xab9e30f7e78fcf8c

def z1244 : W := mkw 0x41630c5818949844 0x141630c581894984 0xb9e30c1878fcf80f 0x2b9e30c1878fcf80

def z1245 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xd3fff0007fff0004 0x1d3fff0007fff000

def z1246 : W := mkw 0x80bcaf856e00d60f 0x980bcaf856e00d60 0x7bfccf867f00ff0b 0x67bfccf867f00ff0

def z1247 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0xec053cf98000f8c8 0xfec053cf98000f8c

def z1248 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x21e10c7878fcf8cf 0xa21e10c7878fcf8c

def z1249 : W := mkw 0x024b400076d20000 0xe024b400076d2000 0xb9e3000078fc0007 0x0b9e3000078fc000

def z1250 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff8607fff0007 0xbfbfff8607fff000

def z1251 : W := mkw 0x41200efd0824b8c7 0x141200efd0824b8c 0x00000cf98000f8c8 0xa00000cf98000f8c

def z1252 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0xbfe3cc7e78fcf8cf 0xbbfe3cc7e78fcf8c

def z1253 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xbbfbc0007fff0007 0x0bbfbc0007fff000

def z1254 : W := mkw 0x20084122446264a0 0x420084122446264a 0xde1acb6647e3ffff 0xfde1acb6647e3fff

def z1255 : W := mkw 0x5143107891bd29d0 0x05143107891bd29d 0x8003307980fc00c4 0x88003307980fc00c

def z1256 : W := mkw 0x00d7a00010900008 0x000d7a0001090000 0xbbfbc00078fc0007 0x0bbfbc00078fc000

def z1257 : W := mkw 0x01630c7018b0b084 0x101630c7018b0b08 0x91e3086078fce004 0x091e3086078fce00

def z1258 : W := mkw 0x0043000010900000 0x0004300001090000 0xb9e3000078fc00cf 0xab9e3000078fc00c

def z1259 : W := mkw 0x02d7b00033990008 0xa02d7b0003399000 0xa1e730003bfc0006 0x0a1e730003bfc000

def z1260 : W := mkw 0xc1200fa80824fec6 0x1c1200fa80824fec 0x00000f800000ffc8 0x600000f800000ffc

def z1261 : W := mkw 0x80bc0fd56e00d607 0x980bc0fd56e00d60 0x79fc0fe67f00ff0b 0x679fc0fe67f00ff0

def z1262 : W := mkw 0x80b40e802a009206 0x980b40e802a00920 0x79fc0f807b00fb0b 0x679fc0f807b00fb0

def z1263 : W := mkw 0x80bcaf856e00d60f 0x980bcaf856e00d60 0xfffdff9fff00ff0b 0xffffdff9fff00ff0

def z1264 : W := mkw 0x40630c0818949844 0x140630c081894984 0xb9e30c1878fcf8cf 0xab9e30c1878fcf8c

def z1265 : W := mkw 0x41630c7818b4b8c4 0x141630c7818b4b8c 0x31e30c7878fcf8cf 0x031e30c7878fcf8c

def z1266 : W := mkw 0xa0084122666266a0 0xca0084122666266a 0xde1acb6647e3e7fd 0xfde1acb6647e3e7f

def z1267 : W := mkw 0x029c500077db0000 0xe029c500077db000 0xf9fd30007fff0007 0x1f9fd30007fff000

def z1268 : W := mkw 0x00f7aed51090000f 0x000f7aed51090000 0xffffffffb81c0002 0xfffffffffb81c000

def z1269 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x61fc07807f00ff0b 0x461fc07807f00ff0

def z1270 : W := mkw 0x41200c780824b8c4 0x141200c780824b8c 0xa8010c780000f8c8 0xaa8010c780000f8c

def z1271 : W := mkw 0x80bc0fd56e00d607 0x980bc0fd56e00d60 0xfdfd3fffff00ff0b 0xffdfd3fffff00ff0

def z1272 : W := mkw 0x50001008810d0950 0x050001008810d095 0xfe1ff499871f1fff 0xffe1ff499871f1ff

def z1273 : W := mkw 0x7208512af7ff6df0 0xe7208512af7ff6df 0x010000007fffffff 0x0010000007ffffff

def z1274 : W := mkw 0x0043000010900000 0x0004300001090000 0xb9e3040078fc180f 0x2b9e3040078fc180

def z1275 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0x69e404807f00ff0b 0x669e404807f00ff0

def z1276 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff0007fff00cf 0xbfbfff0007fff00c

def z1277 : W := mkw 0x0243f00011db0008 0x60243f00011db000 0xa3e3f00038ff0006 0x1a3e3f00038ff000

def z1278 : W := mkw 0x20084122446264a0 0x420084122446264a 0x961acb6640e3e4fc 0xf961acb6640e3e4f

def z1279 : W := mkw 0x00d7b00011990008 0x000d7b0001199000 0xfbfff0007fff0007 0x1fbfff0007fff000

def z1280 : W := mkw 0x41630c7d18b4b8c5 0x141630c7d18b4b8c 0xbde30c7ff8fcf8cf 0xabde30c7ff8fcf8c

def z1281 : W := mkw 0x4143002818b4b8c0 0x14143002818b4b8c 0xb9e3086078fcf8cf 0xab9e3086078fcf8c

def z1282 : W := mkw 0x20084122446264a0 0x420084122446264a 0xde1acfffc4e3e4fd 0xfde1acfffc4e3e4f

def z1283 : W := mkw 0x80b40f802a00d606 0x980b40f802a00d60 0x39e40f807b00ff0b 0x639e40f807b00ff0

def z1284 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0x36ffffff80000000 0xe36ffffff8000000

def z1285 : W := mkw 0x02d7b00033990008 0xa02d7b0003399000 0xf9e730007fff0007 0x1f9e730007fff000

def z1286 : W := mkw 0x02dff10077db4408 0xe02dff10077db440 0xfbfff3007fff0407 0x5fbfff3007fff040

def z1287 : W := mkw 0x80200f800800d606 0x180200f800800d60 0x79e40f807f00ff0b 0x679e40f807f00ff0

def z1288 : W := mkw 0x02dff00077db0008 0xe02dff00077db000 0xfbfff4807fff0007 0x7fbfff4807fff000

def z1289 : W := mkw 0x01630c7018b0b084 0x101630c7018b0b08 0xb9e3086078fce0cf 0xab9e3086078fce0c

def z1290 : W := mkw 0x229cf387674b442b 0xe229cf387674b442 0x461cf38787030430 0x5461cf3878703043

def z1291 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfefffb7f80000000 0x9fefffb7f8000000

def z1292 : W := mkw 0x80bc0f806e00d606 0x980bc0f806e00d60 0xf9fc0f807f00ffcf 0xef9fc0f807f00ffc

def z1293 : W := mkw 0x00f7aed50000000f 0x000f7aed50000000 0xfeffffff87000700 0xffeffffff8700070

def z1294 : W := mkw 0x0043005010900000 0x0004300501090000 0xb9e3007878fc0007 0x8b9e3007878fc000

def z1295 : W := mkw 0x20084122446264a0 0x420084122446264a 0x9e1acb6640e3e0fd 0xb9e1acb6640e3e0f

def z1296 : W := mkw 0x02dff10077db4408 0xe02dff10077db440 0xfffffb007fffe4ff 0xffffffb007fffe4f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z7,z3,z4,z5,z6]),(0,[z1,z2,z7,z3,z4,z5,z6]),(0,[z8,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z9,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z10])],[(0,[z1,z2,z3,z11,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z12,z6]),(0,[z1,z2,z3,z13,z4,z5,z6]),(0,[z14,z1,z3,z15,z4,z5,z6]),(0,[z16,z1,z2,z3,z4,z17,z6]),(0,[z1,z2,z18,z3,z4,z5,z6]),(0,[z19,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z20,z4,z5,z6]),(0,[z1,z21,z2,z22,z3,z4,z6])],[(0,[z23,z1,z2,z3,z24,z5,z6]),(0,[z1,z2,z3,z4,z25,z5,z6]),(0,[z26,z1,z3,z15,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z27])],[(0,[z1,z2,z3,z4,z28,z5,z6]),(0,[z1,z2,z3,z4,z5,z29,z6]),(0,[z1,z2,z3,z30,z4,z5,z6]),(0,[z31,z1,z2,z3,z4,z5,z6]),(0,[z32,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z6,z33])],[(0,[z1,z2,z34,z3,z4,z5,z6]),(0,[z19,z1,z2,z3,z4,z5,z35]),(0,[z1,z2,z3,z4,z5,z36,z6]),(0,[z1,z2,z3,z4,z5,z6,z37])],[(0,[z1,z2,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z39,z6]),(0,[z1,z2,z3,z4,z5,z40,z6]),(0,[z41,z1,z34,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z42]),(0,[z43,z14,z1,z3,z4,z5,z6]),(0,[z1,z2,z44,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z45,z6]),(0,[z14,z1,z3,z4,z5,z46,z6]),(0,[z47,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z48,z4,z5,z49,z6])],[(0,[z14,z1,z3,z4,z50,z5,z6])]],
   [[(0,[z1,z2,z3,z51,z52,z5,z6]),(0,[z1,z2,z3,z53,z4,z5,z6]),(0,[z1,z2,z54,z3,z4,z5,z6])],[(0,[z55,z1,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z57,z4,z5,z58]),(0,[z1,z2,z59,z3,z4,z5,z6])],[(0,[z41,z2,z9,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z56,z60]),(0,[z14,z1,z3,z4,z5,z6,z58]),(0,[z1,z2,z3,z4,z61,z5,z6]),(0,[z1,z2,z62,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z64]),(0,[z1,z2,z3,z65,z4,z5,z6]),(0,[z1,z2,z66,z4,z5,z6,z58]),(0,[z1,z2,z67,z3,z4,z5,z6])],[(0,[z68,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z69,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z70])],[(1,[z1,z71,z3,z4,z5,z6]),(0,[z41,z72,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z73,z5,z6]),(1,[z1,z2,z3,z74,z5,z6]),(0,[z1,z2,z3,z4,z5,z75,z6]),(0,[z76,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z77])],[(0,[z0,z1,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z78,z5,z6]),(0,[z1,z2,z3,z15,z4,z5,z6]),(0,[z8,z1,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z79,z6])],[(0,[z41,z1,z3,z15,z4,z5,z6]),(1,[z14,z1,z3,z80,z5,z6]),(0,[z1,z21,z3,z15,z4,z5,z6]),(0,[z1,z2,z81,z66,z4,z5,z6]),(1,[z82,z2,z3,z4,z5,z6]),(0,[z1,z2,z83,z3,z4,z5,z6]),(0,[z84,z1,z2,z3,z5,z6,z85])]],
   [[(0,[z0,z23,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z33]),(0,[z1,z2,z3,z4,z5,z86,z87])],[(0,[z88,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z89]),(0,[z90,z1,z2,z3,z91,z5,z6]),(0,[z14,z90,z1,z3,z4,z5,z6]),(0,[z92,z14,z1,z3,z4,z5,z6])],[(0,[z93,z2,z3,z94,z4,z5,z6]),(1,[z95,z2,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z4,z5,z6]),(0,[z97,z1,z3,z4,z5,z87,z6])],[(0,[z1,z2,z3,z98,z4,z5,z6]),(0,[z1,z99,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z5,z100]),(0,[z1,z2,z3,z4,z5,z101,z6]),(0,[z31,z1,z2,z102,z4,z5,z6]),(0,[z103,z1,z2,z3,z4,z5,z6]),(0,[z104,z14,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z105,z5,z6]),(0,[z1,z3,z13,z15,z4,z5,z6]),(1,[z1,z106,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z107,z6]),(0,[z108,z1,z2,z3,z4,z5,z6]),(1,[z1,z34,z3,z4,z5,z6]),(0,[z55,z1,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z109,z6]),(0,[z84,z1,z2,z3,z57,z5,z6]),(1,[z1,z2,z3,z110,z5,z6]),(0,[z1,z2,z3,z4,z50,z5,z6])],[(0,[z111,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z87,z6]),(0,[z1,z112,z3,z15,z4,z5,z6]),(0,[z19,z1,z3,z4,z5,z6,z113]),(0,[z114,z1,z2,z112,z4,z5,z6]),(0,[z1,z21,z2,z3,z5,z6,z85])],[(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z46,z56]),(0,[z1,z2,z3,z4,z5,z115,z58]),(0,[z1,z116,z22,z3,z4,z5,z6])],[(1,[z1,z117,z102,z4,z5,z6]),(0,[z1,z66,z3,z15,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z118,z6])]],
   [[(0,[z1,z119,z3,z52,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z6,z85]),(0,[z1,z2,z3,z4,z5,z49,z6])],[(0,[z1,z3,z120,z4,z121,z5,z6]),(0,[z1,z21,z2,z3,z121,z5,z6]),(0,[z1,z2,z3,z122,z4,z5,z6]),(0,[z1,z123,z2,z3,z4,z5,z6]),(0,[z114,z14,z1,z2,z3,z5,z6]),(0,[z1,z124,z2,z3,z80,z5,z6]),(0,[z1,z124,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z125,z4,z5,z6]),(0,[z1,z21,z2,z3,z4,z87,z6])],[(1,[z93,z2,z94,z4,z5,z6]),(1,[z1,z126,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z127,z5,z6]),(0,[z1,z2,z3,z4,z5,z128,z6])],[(0,[z1,z2,z129,z3,z4,z5,z6]),(0,[z130,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z131]),(0,[z1,z3,z15,z4,z121,z5,z6]),(0,[z1,z132,z2,z3,z4,z5,z6]),(0,[z1,z133,z2,z3,z4,z5,z6])],[(0,[z1,z2,z134,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z135,z6]),(0,[z104,z1,z2,z3,z57,z4,z5]),(0,[z104,z1,z2,z3,z4,z6,z60]),(0,[z1,z2,z3,z136,z4,z5,z6]),(0,[z1,z2,z3,z4,z50,z46,z6])],[(0,[z1,z117,z7,z3,z4,z5,z6]),(1,[z1,z3,z15,z4,z5,z6]),(0,[z137,z14,z1,z3,z4,z5,z6])],[(0,[z1,z124,z2,z3,z24,z5,z6]),(0,[z41,z1,z2,z3,z138,z5,z6]),(0,[z1,z2,z3,z139,z4,z5,z6])]],
   [[(0,[z23,z1,z71,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z140,z6]),(0,[z1,z2,z141,z3,z4,z5,z6]),(0,[z142,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z27]),(0,[z1,z2,z3,z57,z4,z5,z6])],[(0,[z84,z14,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z143,z6]),(0,[z1,z2,z112,z3,z4,z5,z27])],[(0,[z144,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z95,z3,z4,z5,z6]),(0,[z1,z2,z3,z17,z5,z145,z6]),(0,[z1,z2,z3,z4,z5,z146,z6]),(0,[z1,z2,z147,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z87,z6])],[(0,[z148,z1,z2,z3,z4,z5,z6]),(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z23,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z150,z6]),(0,[z1,z2,z3,z57,z4,z5,z56]),(0,[z1,z2,z3,z4,z5,z6,z42]),(0,[z1,z151,z2,z3,z4,z5,z6]),(0,[z1,z152,z2,z3,z4,z5,z6])],[(0,[z72,z2,z3,z4,z5,z6,z56]),(1,[z55,z2,z3,z4,z5,z56]),(0,[z14,z1,z3,z4,z5,z6,z56]),(0,[z14,z1,z3,z4,z153,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z154])],[(0,[z155,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z35,z58]),(0,[z1,z2,z3,z4,z5,z6,z156])],[(0,[z1,z2,z157,z3,z4,z5,z6]),(0,[z93,z2,z3,z4,z73,z5,z6]),(0,[z1,z152,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z5,z158,z6]),(0,[z14,z1,z3,z4,z5,z159,z6]),(0,[z1,z2,z3,z4,z5,z6,z160]),(1,[z1,z2,z112,z48,z5,z6])],[(0,[z1,z161,z2,z3,z4,z5,z6]),(0,[z1,z162,z3,z15,z4,z5,z6]),(0,[z163,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z164,z4,z5,z6]),(1,[z1,z2,z3,z57,z5,z118])]],
   [[(0,[z1,z2,z165,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z166,z5,z6]),(0,[z14,z1,z66,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z167,z6]),(0,[z104,z84,z1,z2,z3,z4,z5])],[],[(1,[z0,z119,z3,z4,z5,z6]),(0,[z168,z1,z2,z3,z4,z5,z6])],[(0,[z169,z1,z2,z3,z4,z5,z6]),(0,[z170,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z171]),(0,[z172,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z173,z6])],[(0,[z119,z2,z7,z3,z4,z5,z6]),(0,[z1,z117,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z174,z6]),(0,[z175,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z176,z6]),(0,[z1,z2,z3,z57,z5,z87,z6])],[(0,[z23,z1,z126,z3,z4,z5,z6]),(1,[z72,z2,z3,z4,z73,z6]),(0,[z1,z2,z3,z4,z5,z115,z6]),(0,[z1,z2,z3,z4,z5,z6,z177]),(0,[z1,z2,z178,z3,z4,z5,z6]),(0,[z14,z1,z117,z3,z4,z5,z6]),(0,[z179,z1,z2,z3,z4,z5,z6]),(0,[z180,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z181])],[(1,[z1,z2,z3,z138,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z182]),(0,[z1,z2,z3,z4,z183,z5,z6])],[(0,[z1,z2,z3,z4,z5,z184,z6]),(0,[z185,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z186,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z187,z6]),(0,[z1,z188,z3,z4,z17,z5,z6]),(0,[z1,z188,z3,z4,z5,z6,z113]),(0,[z1,z2,z66,z3,z4,z153,z6]),(0,[z1,z2,z3,z4,z5,z6,z189]),(0,[z84,z1,z2,z3,z4,z5,z118])],[(0,[z23,z1,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z190,z4,z5,z6]),(0,[z1,z2,z3,z4,z191,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z56]),(0,[z1,z152,z3,z15,z4,z5,z6]),(1,[z1,z192,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z193,z6]),(0,[z1,z2,z3,z4,z5,z194,z6])],[(0,[z1,z2,z3,z4,z195,z5,z6]),(0,[z196,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z145,z6]),(0,[z43,z1,z2,z3,z4,z5,z197])],[(0,[z1,z2,z198,z3,z4,z5,z6]),(0,[z1,z2,z22,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z199]),(0,[z1,z2,z3,z4,z5,z200,z6])],[(0,[z1,z2,z3,z4,z201,z5,z6]),(0,[z1,z2,z202,z3,z4,z5,z6]),(1,[z1,z2,z3,z203,z5,z6])],[(0,[z1,z2,z3,z204,z4,z5,z6]),(0,[z1,z117,z2,z52,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z205,z6]),(0,[z1,z2,z3,z57,z4,z50,z5])],[(0,[z206,z1,z2,z3,z4,z5,z6])],[(0,[z84,z1,z2,z3,z4,z5,z115]),(0,[z207,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z208,z5,z6]),(0,[z1,z2,z3,z209,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z210,z6]),(0,[z1,z211,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z212,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z213,z5,z6]),(0,[z1,z2,z102,z3,z4,z5,z6]),(1,[z31,z1,z52,z4,z5,z6]),(1,[z1,z3,z4,z5,z167,z6]),(0,[z1,z214,z2,z3,z4,z5,z6])],[(0,[z215,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z216,z3,z4,z5,z6]),(0,[z1,z22,z3,z15,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z6,z113])],[(0,[z1,z2,z3,z217,z4,z5,z6]),(0,[z218,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z131]),(0,[z1,z2,z3,z4,z5,z219,z6])],[(0,[z220,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z221,z5,z6]),(0,[z31,z1,z2,z3,z4,z5,z42]),(0,[z1,z2,z222,z3,z4,z5,z6])],[(1,[z1,z2,z3,z91,z5,z6]),(0,[z1,z2,z3,z4,z5,z35,z6]),(0,[z223,z1,z2,z3,z4,z5,z6]),(0,[z224,z1,z2,z3,z4,z5,z6])],[(0,[z225,z1,z2,z3,z4,z5,z6]),(1,[z1,z178,z3,z4,z5,z6]),(0,[z1,z2,z3,z226,z4,z5,z6]),(1,[z227,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z228,z5,z6])],[(1,[z1,z2,z3,z4,z5,z229]),(0,[z230,z1,z2,z3,z4,z5,z6]),(0,[z104,z1,z2,z3,z231,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z232]),(0,[z1,z117,z3,z4,z5,z143,z6]),(0,[z233,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z234,z5,z6]),(0,[z1,z2,z112,z48,z4,z5,z6]),(0,[z235,z1,z2,z3,z4,z5,z236]),(0,[z1,z2,z81,z3,z4,z5,z58]),(0,[z1,z2,z22,z3,z5,z87,z6])]],
   [[(0,[z1,z2,z3,z237,z4,z5,z6]),(0,[z55,z2,z3,z4,z5,z6,z56]),(0,[z1,z124,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z238,z6]),(0,[z1,z2,z3,z4,z239,z5,z6]),(0,[z1,z2,z3,z4,z5,z240,z6]),(1,[z241,z2,z3,z4,z5,z6]),(0,[z104,z1,z2,z242,z4,z5,z6])],[(0,[z1,z2,z3,z4,z243,z5,z6]),(0,[z1,z2,z3,z4,z5,z244,z6]),(0,[z1,z2,z3,z4,z5,z245,z6]),(0,[z1,z2,z3,z246,z4,z5,z6])],[(0,[z1,z2,z3,z247,z4,z5,z6]),(0,[z248,z2,z3,z4,z121,z5,z6]),(0,[z14,z1,z69,z3,z4,z5,z6]),(1,[z14,z1,z3,z5,z87,z6]),(0,[z249,z1,z2,z3,z4,z5,z6])],[(0,[z250,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z251,z3,z4,z5,z6]),(0,[z72,z2,z3,z4,z73,z5,z6]),(0,[z14,z1,z3,z4,z73,z5,z6]),(0,[z1,z2,z3,z51,z4,z5,z6]),(0,[z114,z14,z1,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z236,z6,z58]),(0,[z1,z2,z3,z4,z5,z236,z60])],[(0,[z19,z1,z7,z3,z4,z5,z6]),(0,[z1,z2,z3,z252,z4,z5,z6]),(0,[z104,z1,z2,z67,z4,z5,z6])],[(0,[z253,z1,z119,z3,z4,z5,z6]),(0,[z254,z1,z2,z3,z4,z5,z6]),(0,[z235,z1,z3,z15,z4,z5,z6]),(0,[z255,z1,z2,z3,z4,z5,z6])],[(0,[z1,z3,z94,z15,z4,z5,z6]),(0,[z72,z1,z2,z3,z4,z150,z6]),(0,[z256,z1,z2,z3,z4,z5,z6])],[(0,[z19,z1,z2,z3,z4,z5,z56]),(0,[z1,z3,z52,z4,z5,z6,z113]),(0,[z1,z2,z257,z3,z4,z5,z6]),(0,[z258,z1,z2,z3,z4,z5,z6]),(0,[z1,z259,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z260]),(0,[z1,z2,z3,z261,z4,z87,z6]),(0,[z1,z262,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z263])]],
   [[(0,[z1,z2,z3,z4,z5,z264,z6]),(0,[z1,z106,z3,z4,z5,z118,z6])],[(0,[z265,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z171]),(0,[z1,z102,z3,z52,z4,z5,z6]),(0,[z266,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z2,z3,z5,z118,z6]),(1,[z267,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z50,z5,z46]),(0,[z1,z2,z268,z3,z4,z5,z6])],[(0,[z93,z2,z3,z4,z5,z6,z56]),(0,[z269,z2,z3,z4,z5,z150,z6]),(0,[z1,z2,z3,z4,z153,z150,z6]),(0,[z270,z1,z2,z3,z4,z5,z6]),(0,[z43,z1,z259,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z271])],[(1,[z1,z2,z3,z4,z272,z6]),(0,[z93,z1,z2,z3,z4,z272,z6]),(0,[z1,z2,z3,z4,z73,z153,z6]),(0,[z14,z1,z3,z52,z4,z5,z6]),(0,[z14,z1,z21,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z273,z6]),(0,[z1,z2,z3,z274,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z275]),(0,[z43,z1,z2,z4,z5,z159,z6]),(0,[z1,z2,z3,z4,z5,z6,z276])],[(0,[z1,z2,z3,z277,z4,z5,z6]),(0,[z14,z1,z3,z4,z4,z5,z6]),(0,[z1,z124,z2,z3,z5,z87,z6]),(0,[z1,z2,z3,z4,z5,z278,z6]),(0,[z1,z2,z81,z4,z5,z236,z6])],[(1,[z248,z2,z3,z121,z5,z6]),(0,[z279,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z280,z5,z6]),(0,[z93,z1,z2,z3,z280,z5,z6]),(0,[z1,z2,z3,z281,z4,z5,z6]),(0,[z14,z1,z2,z3,z121,z5,z6]),(0,[z1,z2,z3,z24,z5,z87,z6]),(0,[z14,z1,z3,z4,z5,z49,z6]),(0,[z1,z2,z3,z282,z4,z5,z6])],[]],
   [[(0,[z1,z2,z3,z4,z5,z6,z283]),(0,[z43,z284,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z285,z5,z6]),(0,[z1,z2,z3,z4,z5,z286,z6]),(0,[z16,z1,z188,z3,z4,z5,z6]),(0,[z1,z2,z3,z48,z4,z5,z6]),(0,[z1,z287,z2,z3,z4,z5,z6]),(0,[z1,z288,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z231,z4,z5,z6])],[(0,[z289,z1,z2,z3,z4,z5,z6]),(1,[z41,z2,z3,z4,z150,z6]),(0,[z290,z14,z1,z3,z4,z5,z6]),(1,[z14,z1,z3,z15,z5,z6]),(0,[z19,z1,z3,z15,z4,z5,z6]),(0,[z291,z1,z2,z3,z4,z5,z6]),(0,[z1,z292,z2,z3,z4,z5,z6])],[(0,[z267,z1,z3,z4,z5,z49,z6])],[(0,[z1,z2,z3,z4,z5,z293,z6]),(0,[z84,z1,z2,z3,z24,z5,z6]),(0,[z90,z2,z3,z4,z5,z150,z6]),(0,[z31,z1,z3,z15,z4,z5,z6])],[(0,[z90,z1,z178,z3,z4,z5,z6]),(0,[z1,z294,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z295,z6])],[(0,[z1,z7,z3,z15,z4,z5,z6]),(0,[z1,z296,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z297,z6]),(0,[z1,z2,z3,z4,z298,z5,z6]),(0,[z1,z2,z3,z4,z5,z299,z6]),(0,[z1,z2,z3,z4,z5,z6,z300]),(0,[z1,z117,z102,z3,z4,z5,z6]),(0,[z14,z1,z3,z57,z4,z5,z6]),(0,[z43,z1,z301,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z74,z5,z6]),(0,[z1,z2,z81,z3,z4,z5,z6]),(0,[z1,z106,z2,z3,z4,z5,z6])],[(0,[z302,z1,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z5,z303]),(0,[z1,z2,z304,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z143,z6]),(0,[z1,z3,z15,z4,z80,z5,z6]),(0,[z241,z2,z3,z4,z5,z159,z6]),(0,[z305,z1,z2,z3,z4,z5,z6]),(0,[z1,z21,z2,z3,z261,z5,z6])]],
   [[(1,[z14,z1,z3,z24,z5,z6]),(0,[z306,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z52,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z307,z6]),(0,[z235,z1,z192,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z308,z6])],[(0,[z14,z1,z3,z4,z5,z150,z6]),(0,[z309,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z310,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z5,z6])],[],[(0,[z311,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z138,z4,z5,z6]),(0,[z312,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z313,z3,z4,z5,z6]),(1,[z1,z188,z3,z4,z17,z6]),(0,[z2,z3,z4,z5,z314,z159,z6]),(0,[z1,z2,z3,z4,z315,z5,z6])],[(0,[z1,z2,z3,z4,z5,z316,z6]),(1,[z1,z2,z3,z51,z5,z6]),(0,[z14,z14,z1,z3,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z236,z6])],[(0,[z41,z1,z2,z3,z4,z150,z6]),(0,[z31,z1,z2,z52,z4,z5,z6]),(0,[z1,z152,z117,z3,z4,z5,z6]),(0,[z26,z14,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z317,z4,z5,z6]),(0,[z1,z2,z318,z3,z4,z5,z6]),(0,[z1,z2,z3,z48,z5,z87,z6]),(1,[z235,z1,z2,z4,z5,z58]),(0,[z1,z21,z2,z22,z3,z5,z6]),(0,[z1,z21,z2,z3,z57,z5,z6]),(0,[z1,z2,z3,z5,z118,z6,z85]),(0,[z1,z2,z3,z4,z110,z5,z6])],[(0,[z1,z2,z319,z3,z4,z5,z6]),(0,[z1,z2,z320,z3,z4,z5,z6]),(0,[z90,z2,z3,z4,z5,z115,z6]),(0,[z1,z2,z3,z321,z4,z5,z6]),(0,[z1,z2,z66,z3,z4,z159,z6]),(0,[z84,z1,z2,z3,z4,z5,z58])],[(0,[z1,z2,z3,z4,z5,z322,z6]),(0,[z323,z1,z2,z3,z4,z5,z6]),(0,[z90,z2,z3,z4,z121,z5,z6]),(0,[z1,z188,z2,z3,z4,z5,z6]),(0,[z1,z152,z3,z4,z5,z35,z6])]],
   [[(0,[z1,z2,z324,z3,z4,z5,z6]),(0,[z1,z2,z3,z24,z48,z5,z6]),(0,[z1,z2,z325,z3,z4,z5,z6])],[(1,[z1,z2,z3,z231,z5,z6])],[(0,[z326,z1,z2,z3,z4,z5,z6]),(0,[z14,z253,z1,z3,z4,z5,z6]),(0,[z1,z2,z327,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z115,z46]),(0,[z14,z1,z3,z4,z5,z174,z6]),(0,[z16,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z328,z3,z4,z5,z6]),(0,[z329,z1,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z121,z5,z6,z56]),(0,[z14,z1,z3,z4,z5,z115,z6]),(0,[z1,z2,z3,z4,z5,z6,z330]),(0,[z1,z2,z3,z4,z331,z5,z6]),(1,[z1,z2,z242,z4,z5,z6])],[(0,[z332,z1,z2,z3,z4,z5,z6]),(0,[z248,z1,z2,z3,z24,z5,z6]),(0,[z90,z1,z2,z3,z4,z5,z115]),(0,[z1,z2,z3,z4,z5,z333,z6])],[(0,[z92,z1,z2,z3,z4,z5,z6]),(0,[z334,z1,z2,z3,z4,z5,z6])],[(0,[z1,z335,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z303]),(0,[z84,z1,z124,z2,z3,z5,z6]),(0,[z1,z2,z3,z336,z4,z5,z6]),(0,[z1,z337,z2,z3,z4,z5,z6])],[(0,[z1,z2,z338,z3,z4,z5,z6]),(0,[z43,z1,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z339,z6])]],
   [[(0,[z1,z340,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z87,z49,z6]),(0,[z1,z2,z341,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z342])],[(0,[z0,z14,z1,z3,z4,z5,z6]),(0,[z14,z1,z22,z3,z4,z5,z6])],[(0,[z41,z14,z1,z3,z4,z5,z6]),(0,[z343,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z344,z4,z5,z6]),(0,[z345,z1,z2,z3,z4,z5,z6]),(0,[z104,z1,z346,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z347]),(0,[z1,z2,z3,z57,z4,z5,z236])],[(0,[z1,z2,z3,z4,z5,z6,z348]),(0,[z1,z119,z188,z3,z4,z5,z6]),(0,[z1,z21,z124,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z349,z6]),(0,[z1,z350,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z118,z6]),(0,[z1,z2,z3,z4,z351,z5,z6])],[(0,[z352,z1,z2,z3,z4,z5,z6]),(0,[z1,z188,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z353,z6]),(0,[z1,z2,z3,z4,z5,z6,z85]),(0,[z354,z1,z2,z3,z4,z5,z6])],[(0,[z355,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z356]),(0,[z357,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z102,z3,z4,z5,z6])],[(0,[z23,z2,z7,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z358]),(0,[z359,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z360,z3,z4,z5,z6]),(0,[z1,z361,z2,z3,z4,z5,z6])]],
   [[(0,[z41,z2,z3,z4,z5,z150,z6]),(0,[z1,z362,z2,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z6,z60]),(0,[z1,z3,z261,z15,z4,z5,z6]),(0,[z16,z1,z3,z15,z4,z5,z6])],[(0,[z0,z1,z2,z3,z4,z5,z229]),(0,[z2,z3,z24,z4,z121,z5,z6]),(0,[z1,z2,z3,z4,z121,z5,z6]),(0,[z363,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z58,z60]),(1,[z1,z116,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z364]),(0,[z14,z185,z1,z3,z4,z5,z6]),(0,[z137,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z35,z6]),(0,[z1,z2,z3,z365,z4,z5,z6]),(0,[z366,z1,z3,z4,z5,z6,z85])],[(0,[z367,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z368,z15,z4,z5,z6]),(0,[z84,z361,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z369,z6]),(0,[z1,z370,z2,z3,z4,z5,z6])],[(0,[z371,z1,z2,z3,z4,z5,z6])],[(0,[z0,z253,z2,z3,z4,z5,z6]),(0,[z93,z1,z2,z9,z4,z5,z6]),(0,[z14,z1,z21,z3,z4,z5,z6]),(0,[z84,z1,z2,z3,z4,z5,z6])],[(0,[z372,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z9,z66,z4,z5,z6]),(0,[z1,z373,z2,z3,z4,z5,z6]),(0,[z1,z374,z2,z3,z4,z5,z6]),(0,[z1,z3,z15,z15,z4,z5,z6]),(0,[z1,z2,z3,z57,z5,z118,z6]),(0,[z1,z375,z2,z3,z4,z5,z6])],[(0,[z1,z376,z2,z3,z17,z5,z6]),(0,[z1,z3,z4,z5,z377,z87,z6])]],
   [[(1,[z1,z2,z3,z378,z5,z6]),(0,[z93,z1,z2,z3,z378,z5,z6]),(0,[z1,z2,z3,z4,z379,z5,z6]),(0,[z1,z380,z2,z3,z4,z5,z6]),(0,[z14,z1,z3,z24,z4,z5,z6]),(0,[z1,z2,z381,z3,z4,z5,z6]),(0,[z1,z2,z382,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z115,z236]),(0,[z1,z2,z3,z4,z383,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z384]),(0,[z1,z2,z385,z3,z4,z5,z6])],[(0,[z386,z1,z2,z3,z4,z5,z6]),(0,[z93,z14,z1,z3,z4,z5,z6]),(0,[z387,z1,z2,z3,z4,z5,z6]),(0,[z41,z1,z99,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z73,z159,z6]),(1,[z14,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z388,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z389,z6]),(0,[z1,z2,z390,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z391,z6]),(0,[z1,z392,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z393]),(1,[z1,z2,z3,z4,z5,z86])],[(0,[z1,z152,z3,z52,z4,z5,z6]),(0,[z1,z124,z2,z112,z3,z5,z6]),(0,[z1,z3,z15,z4,z5,z46,z6]),(0,[z1,z2,z3,z4,z5,z145,z6]),(0,[z1,z2,z3,z4,z5,z6,z394])],[(0,[z1,z2,z3,z4,z5,z395,z6]),(1,[z19,z1,z3,z4,z5,z113]),(0,[z1,z2,z3,z4,z5,z396,z6]),(1,[z2,z3,z4,z5,z6,z330]),(0,[z1,z397,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z398,z4,z5,z6]),(0,[z104,z399,z2,z3,z4,z5,z6])],[(0,[z1,z119,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z400]),(0,[z1,z2,z346,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z60])],[(0,[z1,z2,z3,z4,z5,z401,z6]),(0,[z2,z3,z94,z4,z5,z150,z6]),(0,[z23,z1,z2,z3,z121,z5,z6]),(1,[z1,z124,z3,z15,z5,z6]),(1,[z206,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z402,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z6,z58]),(0,[z1,z2,z3,z4,z5,z403,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z404,z6]),(0,[z1,z2,z3,z4,z405,z5,z6]),(0,[z31,z1,z117,z3,z4,z5,z6]),(0,[z1,z2,z406,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z407]),(0,[z1,z2,z3,z4,z408,z5,z6])],[(1,[z144,z1,z3,z4,z5,z6]),(0,[z23,z1,z2,z3,z4,z5,z171]),(0,[z14,z1,z3,z4,z17,z5,z6]),(0,[z1,z2,z3,z4,z5,z409,z6]),(1,[z1,z2,z66,z4,z153,z6]),(0,[z410,z1,z2,z3,z4,z5,z6])],[(0,[z41,z1,z2,z402,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z411,z6]),(0,[z43,z1,z2,z3,z4,z159,z6])],[(0,[z412,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z272,z5,z6]),(0,[z269,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z413,z6]),(0,[z1,z2,z3,z4,z5,z6,z414]),(0,[z1,z2,z415,z3,z4,z5,z6])],[(0,[z1,z416,z2,z3,z4,z5,z6]),(0,[z1,z3,z52,z15,z4,z5,z6]),(0,[z14,z1,z3,z282,z4,z5,z6])],[(1,[z253,z7,z3,z4,z5,z6]),(0,[z248,z1,z2,z3,z4,z5,z6]),(0,[z1,z417,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z24,z4,z5,z6]),(0,[z1,z2,z3,z4,z418,z5,z6]),(0,[z55,z1,z2,z3,z4,z5,z115]),(0,[z1,z2,z3,z4,z91,z5,z6]),(0,[z419,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z420,z6]),(0,[z2,z3,z4,z5,z236,z6,z330])],[(0,[z1,z421,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z404,z6]),(0,[z93,z1,z2,z3,z4,z404,z6]),(0,[z1,z422,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z423,z6]),(0,[z1,z2,z424,z3,z4,z5,z6]),(0,[z1,z399,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z425])],[(0,[z1,z2,z3,z24,z5,z49,z6]),(0,[z1,z2,z3,z4,z5,z426,z6]),(0,[z1,z2,z3,z4,z427,z5,z6]),(0,[z14,z1,z3,z48,z4,z5,z6]),(0,[z428,z1,z2,z3,z4,z5,z6]),(0,[z1,z152,z3,z4,z5,z143,z6]),(0,[z429,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z35,z236]),(0,[z1,z2,z3,z4,z430,z5,z6]),(0,[z1,z2,z3,z431,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z378,z4,z5,z6]),(1,[z1,z99,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z432,z5,z6]),(0,[z14,z1,z152,z3,z4,z5,z6]),(0,[z1,z2,z433,z3,z4,z5,z6]),(0,[z114,z1,z124,z2,z3,z5,z6]),(0,[z207,z1,z3,z15,z4,z5,z6]),(1,[z361,z2,z3,z4,z5,z6])],[(0,[z14,z1,z2,z3,z15,z5,z6]),(0,[z14,z1,z2,z3,z80,z5,z6])],[(0,[z1,z2,z3,z434,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z87,z6]),(0,[z1,z2,z3,z4,z435,z5,z6])],[(0,[z1,z2,z3,z4,z5,z436,z6]),(0,[z1,z2,z3,z4,z5,z437,z6]),(0,[z90,z1,z2,z3,z438,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z439]),(0,[z1,z2,z3,z4,z440,z5,z6]),(0,[z1,z2,z3,z4,z5,z314,z6]),(0,[z1,z2,z81,z4,z5,z159,z6]),(0,[z84,z345,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z394]),(0,[z1,z2,z3,z4,z5,z6,z441])],[(0,[z1,z2,z442,z3,z4,z5,z6]),(0,[z443,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z81,z3,z4,z5,z6]),(0,[z444,z1,z2,z3,z4,z5,z6]),(0,[z445,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z446,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z447]),(1,[z1,z346,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z448,z5,z6]),(0,[z1,z2,z3,z449,z4,z5,z6]),(0,[z1,z2,z450,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z17,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z113])],[(0,[z1,z2,z3,z4,z451,z5,z6]),(0,[z2,z9,z3,z94,z4,z5,z6]),(0,[z452,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z2,z3,z24,z5,z6]),(0,[z2,z3,z4,z5,z150,z6,z56]),(0,[z1,z2,z3,z5,z6,z154,z113]),(0,[z1,z2,z3,z4,z5,z275,z6]),(1,[z1,z21,z2,z22,z3,z6]),(0,[z104,z1,z2,z3,z4,z50,z6])]],
   [[(0,[z14,z1,z119,z3,z4,z5,z6]),(0,[z1,z2,z453,z3,z4,z5,z6]),(0,[z454,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z402,z4,z5,z6]),(0,[z1,z124,z3,z15,z4,z5,z6])],[(0,[z1,z2,z4,z153,z5,z159,z6])],[(0,[z248,z1,z3,z15,z4,z5,z6]),(0,[z455,z1,z2,z3,z4,z5,z6]),(1,[z1,z415,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z456,z6]),(0,[z443,z1,z2,z3,z52,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z457]),(0,[z458,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z242,z4,z5,z6])],[(0,[z459,z1,z2,z3,z4,z5,z6]),(0,[z460,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z461,z3,z4,z5,z6]),(0,[z248,z23,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z462,z6]),(1,[z185,z2,z3,z4,z5,z6]),(0,[z1,z112,z3,z274,z4,z5,z6])],[(0,[z1,z2,z3,z463,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z464,z6]),(0,[z1,z124,z2,z3,z5,z118,z6]),(0,[z1,z2,z3,z4,z5,z465,z6]),(1,[z97,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z280,z5,z6]),(0,[z1,z2,z3,z121,z5,z49,z6]),(0,[z1,z2,z3,z4,z5,z236,z113]),(0,[z43,z1,z2,z3,z4,z153,z6]),(0,[z1,z2,z3,z4,z466,z5,z6])]],
   [[(0,[z1,z2,z94,z4,z5,z159,z6]),(0,[z467,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z468,z4,z5,z6]),(0,[z469,z1,z2,z3,z4,z5,z6])],[(0,[z1,z3,z15,z4,z5,z6,z56]),(1,[z1,z2,z3,z4,z5,z12]),(0,[z1,z3,z15,z4,z153,z5,z6]),(0,[z43,z1,z2,z3,z74,z5,z6])],[(0,[z1,z2,z3,z4,z5,z470,z6]),(0,[z471,z1,z2,z3,z4,z5,z6])],[(0,[z1,z124,z2,z3,z121,z5,z6]),(0,[z1,z2,z3,z472,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z159,z6]),(0,[z1,z2,z162,z3,z4,z5,z6]),(0,[z1,z3,z4,z17,z5,z143,z6]),(0,[z1,z2,z3,z4,z473,z5,z6]),(0,[z235,z1,z2,z81,z4,z5,z6]),(0,[z474,z1,z2,z3,z4,z5,z87]),(0,[z1,z2,z3,z4,z5,z86,z6])],[(0,[z475,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z476,z6]),(0,[z1,z2,z3,z4,z5,z6,z477]),(0,[z14,z1,z3,z4,z5,z478,z6]),(0,[z479,z1,z2,z3,z4,z5,z6]),(0,[z104,z1,z337,z3,z4,z5,z6])],[(0,[z480,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z119,z3,z4,z5,z6]),(0,[z1,z2,z3,z481,z4,z5,z6]),(0,[z1,z21,z2,z3,z24,z5,z6]),(0,[z482,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z483,z5,z6]),(1,[z366,z1,z3,z4,z5,z6])],[(0,[z19,z1,z119,z3,z4,z5,z6]),(0,[z484,z1,z2,z3,z4,z5,z6]),(0,[z31,z1,z3,z52,z4,z5,z6]),(1,[z1,z3,z274,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z276])],[(0,[z1,z2,z3,z57,z4,z5,z115]),(0,[z485,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z188,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z486]),(0,[z1,z2,z3,z4,z5,z6,z487])]],
   [[(0,[z1,z488,z2,z3,z4,z5,z6]),(0,[z1,z2,z489,z3,z4,z5,z6]),(0,[z23,z2,z3,z4,z5,z6,z56]),(0,[z235,z14,z1,z3,z4,z5,z6]),(1,[z114,z1,z2,z5,z49,z6]),(0,[z1,z116,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z490,z4,z5,z6])],[(1,[z1,z2,z3,z38,z5,z6]),(0,[z1,z2,z3,z121,z5,z87,z6]),(0,[z1,z2,z3,z4,z5,z6,z491]),(0,[z492,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z81,z3,z4,z5,z236]),(0,[z493,z1,z2,z3,z4,z5,z6])],[(0,[z1,z188,z7,z3,z4,z5,z6]),(0,[z90,z1,z2,z3,z4,z5,z6]),(0,[z1,z152,z2,z3,z4,z5,z115]),(0,[z14,z1,z3,z4,z5,z118,z6]),(0,[z1,z2,z3,z4,z5,z6,z494]),(0,[z1,z192,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z57,z4,z5,z85])],[(0,[z93,z1,z2,z3,z4,z5,z436]),(1,[z114,z14,z1,z3,z5,z6]),(0,[z14,z1,z3,z4,z5,z6,z85])],[(0,[z1,z2,z3,z4,z5,z495,z6]),(0,[z1,z2,z3,z4,z5,z56,z58]),(1,[z2,z3,z4,z5,z314,z6]),(0,[z1,z2,z3,z4,z5,z6,z496])],[(1,[z1,z461,z3,z4,z5,z6]),(0,[z93,z1,z461,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z497,z5,z6]),(0,[z1,z2,z3,z4,z5,z498,z6]),(0,[z499,z1,z2,z3,z4,z5,z6])],[(0,[z41,z1,z2,z381,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z500]),(0,[z290,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z501,z5,z6]),(0,[z1,z3,z4,z5,z167,z49,z6]),(0,[z502,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z197]),(0,[z1,z2,z3,z4,z50,z5,z60])],[(1,[z1,z503,z3,z4,z5,z6]),(0,[z93,z1,z503,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z121,z5,z6]),(0,[z1,z2,z504,z3,z4,z5,z6]),(0,[z72,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z253,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z505,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z506,z6]),(0,[z507,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z508,z6]),(0,[z1,z2,z3,z4,z5,z509,z6]),(0,[z1,z2,z3,z510,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z478,z6]),(0,[z1,z2,z3,z4,z511,z5,z6]),(0,[z1,z2,z3,z4,z5,z512,z6]),(0,[z513,z1,z2,z3,z4,z5,z6]),(0,[z514,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z515,z6])],[(0,[z516,z14,z1,z3,z4,z5,z6]),(1,[z1,z2,z67,z4,z5,z6]),(0,[z104,z1,z2,z3,z4,z5,z6])],[(0,[z1,z517,z2,z3,z4,z5,z6]),(0,[z518,z1,z2,z3,z4,z5,z6]),(0,[z1,z284,z2,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z143,z6]),(0,[z1,z2,z3,z48,z121,z5,z6]),(0,[z1,z2,z3,z4,z519,z5,z6]),(0,[z1,z117,z3,z4,z5,z6,z113]),(0,[z1,z2,z3,z4,z80,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z520]),(0,[z1,z3,z4,z5,z35,z6,z113]),(0,[z521,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z522,z6]),(0,[z1,z523,z2,z3,z4,z5,z6]),(0,[z524,z1,z2,z3,z4,z5,z6]),(0,[z97,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z525]),(0,[z206,z1,z2,z3,z5,z6,z113]),(0,[z1,z22,z415,z3,z4,z5,z6])],[(0,[z31,z14,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z526,z5,z6]),(0,[z1,z2,z3,z4,z527,z5,z6]),(0,[z528,z1,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z529,z5,z6]),(0,[z93,z269,z2,z3,z4,z5,z6]),(0,[z530,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z531,z6])],[(0,[z1,z2,z3,z532,z4,z5,z6])],[(0,[z90,z1,z374,z3,z4,z5,z6]),(0,[z1,z2,z3,z533,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z534,z6]),(0,[z227,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z535,z3,z4,z5,z6])],[(0,[z536,z1,z2,z3,z4,z5,z6]),(0,[z93,z41,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z537,z4,z5,z6]),(0,[z90,z55,z2,z3,z4,z5,z6]),(1,[z90,z2,z3,z4,z5,z115]),(0,[z1,z2,z3,z538,z4,z5,z6]),(0,[z539,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z22,z3,z261,z4,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(1,[z14,z1,z112,z3,z5,z6]),(0,[z540,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z112,z3,z4,z5,z36])],[(0,[z1,z126,z2,z3,z4,z5,z6]),(1,[z1,z2,z381,z4,z5,z6]),(0,[z114,z1,z2,z3,z48,z5,z6]),(0,[z1,z2,z3,z261,z5,z87,z6])],[(0,[z253,z1,z3,z15,z4,z5,z6]),(1,[z1,z2,z3,z438,z5,z6]),(0,[z507,z1,z3,z15,z4,z5,z6]),(0,[z1,z541,z2,z3,z4,z5,z6])],[(0,[z1,z119,z117,z3,z4,z5,z6])]],
   [[(0,[z542,z1,z2,z3,z4,z5,z6]),(0,[z72,z1,z2,z3,z4,z73,z6]),(0,[z1,z3,z15,z4,z73,z5,z6]),(0,[z104,z1,z3,z15,z4,z5,z6]),(0,[z1,z3,z4,z5,z118,z6,z394])],[(0,[z1,z2,z543,z3,z4,z5,z6]),(0,[z1,z188,z2,z3,z4,z143,z6]),(0,[z1,z2,z3,z4,z5,z46,z58])],[(0,[z1,z2,z3,z4,z544,z5,z6]),(0,[z1,z2,z3,z4,z5,z545,z6]),(0,[z1,z2,z301,z3,z4,z5,z6])],[(0,[z14,z55,z1,z3,z4,z5,z6]),(0,[z84,z1,z2,z3,z4,z5,z56]),(0,[z14,z185,z2,z3,z4,z5,z6]),(0,[z1,z3,z546,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z547])],[(0,[z548,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z303,z6]),(0,[z1,z2,z3,z4,z5,z549,z6]),(0,[z1,z102,z3,z15,z4,z5,z6]),(0,[z14,z19,z1,z3,z4,z5,z6]),(0,[z14,z1,z2,z3,z5,z87,z6]),(0,[z1,z2,z3,z550,z4,z5,z6]),(0,[z16,z1,z2,z3,z4,z143,z6]),(1,[z474,z1,z2,z3,z4,z5])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z121,z5,z6]),(0,[z235,z1,z424,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z87,z6,z85]),(0,[z1,z2,z3,z4,z5,z6,z551])],[(0,[z41,z1,z2,z3,z4,z5,z6]),(1,[z1,z259,z3,z4,z5,z6]),(0,[z1,z21,z2,z3,z4,z5,z6])],[(0,[z552,z1,z2,z3,z4,z5,z6]),(0,[z553,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z115,z60]),(1,[z84,z14,z1,z3,z5,z6]),(0,[z1,z3,z15,z4,z50,z5,z6]),(0,[z1,z2,z3,z4,z5,z554,z6]),(1,[z1,z2,z81,z4,z5,z236]),(1,[z1,z337,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z555,z3,z4,z5,z6]),(0,[z556,z1,z2,z3,z4,z5,z6]),(0,[z1,z21,z2,z3,z5,z49,z6]),(0,[z43,z1,z2,z3,z203,z5,z6]),(0,[z84,z1,z2,z3,z4,z5,z236])],[(0,[z1,z2,z3,z4,z5,z557,z6]),(0,[z1,z3,z15,z4,z4,z5,z6]),(1,[z1,z2,z3,z261,z87,z6])],[(0,[z1,z2,z3,z558,z4,z5,z6]),(0,[z1,z2,z3,z559,z4,z5,z6]),(0,[z366,z1,z2,z3,z4,z5,z6])],[(0,[z55,z1,z2,z3,z4,z5,z6]),(0,[z19,z1,z2,z3,z4,z5,z115]),(0,[z560,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z49,z6])],[(0,[z1,z561,z2,z3,z4,z5,z6]),(0,[z1,z9,z3,z15,z4,z5,z6]),(0,[z1,z562,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z563,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z564,z6]),(0,[z14,z1,z3,z4,z5,z6,z113]),(0,[z1,z2,z3,z4,z565,z5,z6]),(0,[z566,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z567,z4,z5,z6]),(1,[z284,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z197]),(0,[z1,z568,z2,z3,z4,z5,z6])],[(0,[z569,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z570,z3,z4,z5,z6]),(0,[z1,z571,z2,z3,z4,z5,z6]),(0,[z1,z572,z2,z3,z4,z5,z6]),(1,[z43,z1,z2,z4,z159,z6]),(0,[z1,z2,z3,z4,z5,z6,z573])],[(0,[z1,z574,z2,z3,z4,z5,z6]),(1,[z443,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z575,z4,z5,z6]),(0,[z1,z2,z3,z576,z4,z5,z6]),(0,[z84,z1,z3,z15,z4,z5,z6]),(0,[z16,z1,z3,z4,z5,z143,z6]),(0,[z1,z152,z2,z3,z4,z5,z113])],[(0,[z1,z7,z3,z4,z5,z35,z6]),(0,[z2,z9,z3,z4,z5,z6,z56]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z112,z3,z48,z5,z6]),(0,[z577,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z93,z1,z2,z94,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z578]),(0,[z1,z2,z3,z4,z5,z6,z579]),(0,[z580,z1,z2,z3,z4,z5,z6]),(0,[z581,z1,z2,z3,z4,z5,z6])],[(0,[z0,z119,z2,z3,z4,z5,z6]),(0,[z582,z1,z2,z3,z4,z5,z6]),(0,[z583,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z584,z4,z5,z6]),(1,[z14,z185,z3,z4,z5,z6]),(0,[z585,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z586]),(0,[z43,z227,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z587,z5,z6]),(0,[z1,z2,z3,z588,z4,z5,z6]),(0,[z1,z117,z188,z3,z4,z5,z6]),(1,[z1,z301,z3,z4,z5,z6]),(0,[z1,z2,z3,z589,z4,z5,z6]),(0,[z235,z1,z2,z4,z5,z6,z58])],[(0,[z1,z590,z2,z3,z4,z5,z6]),(0,[z591,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z592]),(0,[z1,z2,z3,z4,z5,z6,z593]),(0,[z14,z1,z124,z3,z4,z5,z6]),(0,[z16,z14,z1,z3,z4,z5,z6]),(0,[z1,z3,z550,z15,z4,z5,z6]),(0,[z1,z3,z15,z57,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z525]),(0,[z1,z2,z3,z594,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z143,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z595,z1,z2,z3,z4,z5,z6]),(0,[z72,z269,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z596,z5,z6]),(0,[z1,z2,z3,z546,z4,z5,z6]),(0,[z597,z1,z2,z3,z4,z5,z6]),(0,[z84,z1,z2,z3,z4,z50,z5]),(0,[z1,z2,z3,z4,z5,z6,z598])],[(0,[z1,z119,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z120,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z150,z6]),(0,[z1,z3,z4,z5,z143,z6,z113])],[(0,[z14,z248,z1,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z73,z6]),(0,[z31,z1,z2,z3,z4,z5,z12]),(1,[z14,z1,z3,z5,z118,z6]),(0,[z1,z152,z188,z3,z4,z5,z6]),(0,[z1,z2,z599,z3,z4,z5,z6]),(0,[z43,z1,z2,z66,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z276,z85])]],
   [[(0,[z600,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z601,z6]),(0,[z14,z269,z1,z3,z4,z5,z6]),(0,[z84,z1,z2,z3,z121,z5,z6]),(0,[z602,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z603,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z46,z6])],[(0,[z1,z2,z3,z4,z604,z5,z6]),(0,[z1,z605,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z297])],[(0,[z606,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z607]),(0,[z1,z571,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z608,z4,z5,z6])],[(0,[z1,z2,z3,z609,z4,z5,z6]),(0,[z0,z1,z2,z3,z38,z5,z6]),(0,[z1,z503,z2,z3,z4,z5,z6]),(1,[z14,z1,z3,z121,z5,z6]),(0,[z1,z2,z610,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z58])],[(0,[z1,z2,z611,z3,z4,z5,z6]),(0,[z1,z2,z3,z612,z4,z5,z6]),(0,[z613,z1,z2,z3,z4,z5,z6]),(0,[z1,z614,z2,z3,z4,z5,z6])],[(0,[z269,z1,z2,z94,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z615,z6]),(0,[z144,z1,z3,z4,z121,z5,z6]),(0,[z1,z3,z15,z4,z5,z173,z6]),(0,[z616,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z617,z6]),(0,[z169,z14,z1,z3,z4,z5,z6]),(0,[z1,z2,z618,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z5,z275]),(0,[z1,z2,z619,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z620,z3,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z115,z6]),(1,[z1,z2,z3,z4,z5,z36]),(0,[z241,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z159,z6,z58]),(0,[z1,z2,z3,z4,z5,z621,z6])],[(0,[z1,z2,z3,z622,z4,z5,z6]),(0,[z93,z1,z2,z3,z4,z5,z131]),(0,[z41,z1,z2,z3,z191,z5,z6]),(0,[z1,z623,z2,z3,z4,z5,z6]),(0,[z19,z1,z152,z3,z4,z5,z6]),(0,[z1,z624,z112,z3,z4,z5,z6]),(1,[z1,z424,z3,z4,z5,z6]),(0,[z104,z334,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z625,z6]),(0,[z1,z3,z52,z4,z5,z143,z6]),(1,[z1,z376,z2,z3,z5,z6]),(0,[z114,z1,z2,z3,z4,z5,z6])],[(0,[z269,z1,z2,z3,z4,z5,z6]),(0,[z93,z1,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z24,z5,z118,z6]),(0,[z1,z117,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z6,z154]),(0,[z1,z2,z3,z4,z5,z626,z6]),(0,[z1,z2,z3,z627,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z628]),(0,[z1,z2,z629,z3,z4,z5,z6]),(0,[z1,z2,z3,z57,z4,z5,z118])],[(0,[z2,z7,z3,z4,z121,z5,z6]),(0,[z1,z630,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z631]),(0,[z1,z2,z3,z4,z5,z632,z6]),(0,[z114,z1,z2,z3,z5,z49,z6]),(0,[z1,z21,z2,z3,z48,z5,z6])],[(0,[z1,z2,z3,z4,z5,z229,z6]),(1,[z1,z374,z3,z4,z5,z6]),(0,[z235,z1,z2,z3,z4,z5,z58])],[(0,[z633,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z120,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z634,z6]),(0,[z196,z14,z1,z3,z4,z5,z6]),(0,[z602,z1,z3,z15,z4,z5,z6])],[(0,[z1,z2,z3,z635,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z100]),(0,[z1,z2,z3,z4,z636,z5,z6]),(0,[z14,z1,z112,z3,z4,z5,z6]),(0,[z14,z1,z3,z261,z4,z5,z6]),(0,[z637,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z638,z6]),(0,[z639,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z377,z6]),(0,[z104,z1,z2,z3,z4,z5,z46])]],
   [[(0,[z248,z1,z2,z3,z121,z5,z6]),(0,[z640,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z113,z58]),(0,[z1,z2,z3,z641,z4,z5,z6])],[(0,[z0,z1,z2,z3,z4,z5,z525]),(0,[z1,z119,z3,z4,z5,z143,z6]),(0,[z1,z2,z642,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z643]),(0,[z386,z14,z1,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z80,z5,z6]),(0,[z644,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z66,z4,z153,z5,z6]),(1,[z399,z2,z3,z4,z5,z6])],[(0,[z1,z7,z3,z52,z4,z5,z6]),(0,[z0,z1,z2,z3,z529,z5,z6]),(0,[z645,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z73,z5,z150,z6]),(0,[z1,z2,z3,z4,z5,z646,z6]),(0,[z1,z152,z2,z3,z4,z5,z35]),(0,[z1,z2,z3,z4,z5,z6,z647]),(0,[z1,z648,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z649,z6]),(0,[z474,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z650,z6]),(1,[z345,z2,z3,z4,z5,z6])],[(0,[z651,z1,z2,z3,z4,z5,z6]),(0,[z269,z2,z9,z3,z4,z5,z6]),(0,[z652,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z653,z5,z6]),(0,[z1,z2,z3,z4,z5,z654,z6])],[(0,[z1,z2,z3,z4,z5,z655,z6]),(0,[z23,z1,z2,z3,z4,z5,z297]),(0,[z14,z1,z3,z4,z527,z5,z6]),(0,[z1,z3,z15,z4,z5,z6,z60]),(0,[z1,z2,z3,z4,z5,z6,z656]),(0,[z1,z2,z3,z4,z5,z6,z657]),(0,[z1,z2,z658,z3,z4,z5,z6]),(0,[z1,z2,z659,z3,z4,z5,z6]),(0,[z1,z2,z3,z660,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z436]),(0,[z2,z9,z3,z4,z73,z5,z6]),(0,[z82,z2,z3,z4,z5,z236,z6]),(0,[z1,z2,z3,z4,z5,z236,z46])],[(0,[z14,z1,z3,z4,z5,z236,z6]),(0,[z1,z2,z661,z3,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z35,z6]),(0,[z19,z1,z2,z3,z4,z5,z113]),(1,[z1,z2,z3,z4,z50,z46])]],
   [[(1,[z1,z2,z3,z191,z5,z6]),(0,[z90,z1,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z662,z5,z6]),(0,[z114,z1,z3,z15,z4,z5,z6]),(0,[z1,z2,z392,z3,z4,z5,z6])],[(0,[z269,z1,z3,z15,z4,z5,z6]),(0,[z82,z1,z2,z3,z4,z5,z6])],[(0,[z1,z3,z15,z4,z234,z5,z6]),(0,[z1,z2,z3,z663,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z664])],[(0,[z253,z1,z7,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z665,z6]),(0,[z1,z2,z3,z121,z5,z118,z6]),(0,[z1,z3,z24,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z117,z2,z102,z4,z5,z6]),(0,[z233,z14,z1,z3,z4,z5,z6]),(0,[z14,z1,z2,z112,z3,z5,z6]),(0,[z1,z3,z15,z4,z5,z238,z6]),(0,[z1,z2,z3,z4,z5,z6,z666])],[(0,[z72,z2,z3,z94,z4,z5,z6]),(0,[z14,z1,z3,z94,z4,z5,z6]),(1,[z14,z1,z21,z3,z5,z6]),(0,[z1,z2,z112,z3,z4,z5,z6]),(0,[z1,z2,z3,z261,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z667]),(0,[z668,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z66,z94,z4,z5,z6]),(0,[z1,z624,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z669,z4,z5,z6]),(0,[z1,z2,z3,z670,z4,z5,z6]),(0,[z90,z2,z9,z3,z4,z5,z6]),(0,[z1,z2,z112,z3,z5,z49,z6]),(0,[z1,z2,z3,z4,z153,z5,z6]),(0,[z1,z2,z3,z4,z5,z671,z6]),(1,[z104,z1,z2,z3,z4,z60])],[(0,[z1,z2,z672,z3,z4,z5,z6]),(0,[z673,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z377,z6]),(0,[z1,z2,z3,z4,z5,z6,z674]),(0,[z1,z2,z3,z4,z46,z6,z60])]],
   [[(0,[z1,z2,z3,z4,z675,z5,z6]),(0,[z676,z1,z2,z3,z4,z5,z6]),(0,[z677,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z159,z6]),(0,[z1,z2,z3,z4,z678,z5,z6])],[(0,[z93,z90,z2,z3,z4,z5,z6]),(0,[z90,z72,z2,z3,z4,z5,z6]),(1,[z14,z95,z3,z4,z5,z6]),(0,[z679,z1,z2,z3,z4,z5,z6]),(0,[z104,z1,z2,z3,z110,z5,z6]),(0,[z680,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z159,z6]),(0,[z1,z2,z3,z438,z4,z5,z6]),(0,[z1,z2,z681,z3,z4,z5,z6]),(0,[z1,z2,z3,z682,z4,z5,z6]),(0,[z1,z2,z66,z3,z4,z5,z6]),(0,[z683,z1,z2,z3,z4,z5,z6])],[(0,[z14,z1,z7,z3,z4,z5,z6]),(0,[z14,z1,z9,z3,z4,z5,z6]),(0,[z90,z1,z3,z15,z4,z5,z6]),(0,[z1,z684,z2,z3,z4,z5,z6]),(0,[z14,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z264,z6]),(0,[z1,z3,z15,z4,z5,z6,z439])],[(0,[z26,z1,z2,z3,z4,z5,z6]),(0,[z253,z2,z7,z3,z4,z5,z6]),(0,[z685,z1,z2,z3,z4,z5,z6]),(0,[z23,z2,z3,z24,z4,z5,z6]),(0,[z114,z1,z2,z4,z5,z49,z6]),(0,[z235,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z236,z6])],[(0,[z90,z23,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z150,z159,z6]),(0,[z14,z95,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z686,z4,z5,z6])],[(0,[z1,z3,z15,z4,z17,z5,z6]),(0,[z1,z687,z2,z3,z4,z5,z6]),(0,[z688,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z236,z56]),(0,[z84,z14,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z689,z4,z5,z6]),(1,[z16,z1,z3,z4,z143,z6]),(0,[z84,z1,z2,z3,z4,z5,z85])]],
   [[(0,[z690,z1,z2,z3,z4,z5,z6]),(0,[z72,z1,z3,z15,z4,z5,z6]),(0,[z267,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z529,z5,z6]),(0,[z1,z2,z3,z94,z4,z5,z6]),(0,[z14,z72,z1,z3,z4,z5,z6]),(0,[z691,z1,z2,z3,z4,z5,z6]),(0,[z1,z95,z2,z3,z4,z5,z6]),(1,[z1,z624,z3,z4,z5,z6]),(1,[z84,z1,z2,z3,z5,z85]),(0,[z104,z1,z2,z3,z4,z5,z60])],[(0,[z1,z188,z3,z52,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z692,z6]),(0,[z1,z2,z3,z4,z693,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z694]),(0,[z1,z695,z2,z3,z4,z5,z6])],[(0,[z1,z119,z3,z4,z5,z35,z6]),(0,[z1,z2,z3,z696,z4,z5,z6]),(0,[z2,z3,z4,z5,z115,z6,z56]),(0,[z1,z2,z3,z4,z697,z5,z6]),(0,[z1,z3,z15,z48,z4,z5,z6]),(0,[z1,z81,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z698]),(1,[z334,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z368,z4,z5,z6]),(0,[z699,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z71,z3,z4,z5,z6]),(0,[z14,z23,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z700,z6]),(0,[z1,z2,z3,z4,z5,z6,z100]),(0,[z701,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z203,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z516,z1,z2,z3,z4,z5,z6]),(0,[z1,z188,z2,z3,z4,z17,z6])],[(0,[z702,z1,z2,z3,z4,z5,z6]),(0,[z703,z1,z2,z3,z4,z5,z6]),(1,[z23,z2,z3,z24,z5,z6]),(0,[z1,z2,z3,z4,z5,z704,z6]),(0,[z705,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z706]),(0,[z1,z376,z2,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z707,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z131]),(0,[z2,z3,z4,z73,z389,z6]),(0,[z708,z1,z3,z4,z5,z6]),(0,[z1,z709,z3,z4,z5,z6])],[(0,[z14,z7,z3,z121,z5,z6]),(0,[z710,z2,z3,z4,z5,z6]),(0,[z711,z1,z3,z4,z5,z6])],[(0,[z1,z119,z3,z4,z5,z229]),(0,[z1,z3,z438,z15,z5,z6]),(0,[z14,z1,z3,z5,z6,z547]),(0,[z1,z2,z3,z5,z6,z154])],[(0,[z2,z3,z4,z404,z6,z56]),(0,[z1,z126,z3,z4,z5,z297]),(0,[z114,z1,z2,z5,z712,z6]),(0,[z1,z2,z3,z4,z5,z713])],[(0,[z14,z1,z3,z603,z5,z6])],[(0,[z1,z2,z3,z714,z5,z6]),(0,[z1,z2,z3,z715,z5,z6]),(0,[z1,z3,z4,z5,z173,z113]),(0,[z716,z2,z3,z4,z5,z6]),(0,[z717,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z718]),(0,[z2,z3,z4,z73,z404,z6]),(0,[z1,z2,z3,z4,z5,z100]),(0,[z290,z95,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z719]),(0,[z1,z374,z3,z4,z5,z56]),(0,[z469,z2,z3,z4,z5,z56]),(0,[z1,z2,z720,z4,z5,z6]),(0,[z721,z1,z3,z231,z5,z6])],[(0,[z1,z2,z3,z722,z5,z6]),(0,[z14,z1,z3,z378,z5,z6]),(0,[z1,z3,z4,z5,z6,z723]),(0,[z1,z2,z3,z5,z6,z724])],[(0,[z14,z3,z4,z5,z6,z330]),(0,[z1,z725,z3,z4,z5,z6])],[(0,[z14,z1,z3,z368,z5,z6]),(0,[z345,z2,z3,z4,z5,z6]),(0,[z1,z2,z112,z48,z5,z6])],[(0,[z3,z15,z4,z5,z6,z330]),(0,[z1,z3,z726,z4,z5,z6]),(0,[z82,z2,z3,z727,z5,z6])],[(0,[z82,z2,z3,z4,z5,z436]),(0,[z267,z1,z3,z24,z5,z6]),(0,[z1,z728,z3,z4,z5,z6]),(0,[z1,z2,z729,z4,z5,z6]),(0,[z43,z1,z301,z4,z159,z6])],[(0,[z730,z1,z3,z191,z5,z6]),(0,[z1,z3,z15,z4,z5,z36]),(0,[z1,z3,z4,z5,z6,z731])],[(0,[z2,z3,z4,z5,z6,z732]),(0,[z1,z2,z3,z4,z50,z46])],[(0,[z241,z2,z9,z4,z5,z6]),(0,[z284,z2,z3,z203,z5,z6])]],
   [[(0,[z1,z99,z3,z138,z5,z6]),(0,[z1,z733,z3,z4,z5,z6]),(0,[z1,z3,z51,z15,z5,z6]),(0,[z14,z95,z112,z3,z5,z6]),(0,[z305,z1,z2,z3,z4,z60])],[(1,[z734,z3,z4,z5,z6]),(0,[z1,z2,z3,z121,z5,z297]),(0,[z14,z1,z3,z427,z5,z6]),(0,[z196,z95,z3,z4,z5,z6]),(1,[z14,z1,z3,z5,z36])],[(0,[z1,z735,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z736]),(0,[z14,z361,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z737,z6])],[(0,[z1,z3,z261,z15,z87,z6]),(0,[z284,z2,z3,z4,z159,z6])],[(0,[z1,z2,z3,z738,z5,z6])],[(0,[z14,z1,z3,z4,z404,z6]),(0,[z1,z2,z3,z4,z739,z6]),(0,[z84,z95,z2,z3,z5,z6])],[(0,[z1,z740,z3,z4,z5,z6]),(0,[z185,z2,z3,z121,z5,z6]),(0,[z1,z741,z3,z4,z5,z6]),(0,[z1,z2,z3,z742,z5,z6])],[],[(0,[z14,z1,z3,z451,z5,z6]),(0,[z302,z1,z2,z4,z159,z6]),(0,[z1,z2,z3,z4,z743,z6])],[(0,[z14,z227,z3,z4,z5,z6])],[(0,[z1,z3,z15,z4,z5,z436]),(0,[z144,z1,z21,z3,z5,z6]),(0,[z1,z2,z744,z4,z5,z6]),(0,[z602,z443,z1,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z745]),(0,[z1,z746,z3,z4,z5,z6]),(0,[z1,z21,z22,z415,z3,z6])],[(0,[z1,z3,z4,z5,z167,z6]),(0,[z1,z747,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z748]),(0,[z1,z2,z3,z749,z5,z6]),(0,[z249,z14,z1,z3,z5,z6]),(0,[z1,z3,z750,z80,z5,z6]),(0,[z1,z21,z22,z3,z15,z6]),(0,[z1,z21,z2,z751,z3,z6])],[(0,[z1,z2,z3,z4,z752,z6]),(0,[z41,z2,z381,z4,z150,z6]),(0,[z114,z14,z1,z282,z5,z6]),(0,[z753,z2,z3,z4,z5,z6]),(0,[z227,z301,z3,z4,z5,z6])],[]],
   [[(0,[z754,z2,z3,z4,z5,z6]),(0,[z1,z242,z15,z4,z5,z6]),(0,[z84,z1,z2,z3,z5,z85])],[(0,[z227,z2,z3,z4,z5,z6]),(0,[z14,z1,z402,z4,z5,z6]),(0,[z755,z1,z3,z438,z5,z6])],[(0,[z1,z2,z3,z4,z5,z756]),(0,[z443,z1,z3,z5,z143,z6]),(0,[z14,z1,z3,z5,z6,z628]),(0,[z1,z21,z2,z619,z3,z6]),(0,[z84,z366,z1,z3,z5,z85])],[(0,[z1,z3,z4,z5,z757,z6]),(0,[z23,z71,z3,z24,z5,z6]),(0,[z334,z2,z3,z4,z5,z6]),(0,[z84,z14,z185,z3,z5,z6]),(0,[z84,z1,z3,z15,z5,z85]),(0,[z1,z3,z758,z4,z5,z6]),(0,[z1,z2,z629,z48,z5,z6])],[(0,[z759,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z760,z6])],[(0,[z1,z2,z3,z761,z5,z6]),(0,[z412,z1,z3,z4,z143,z6]),(0,[z0,z119,z3,z38,z5,z6]),(0,[z2,z94,z4,z5,z404,z6]),(0,[z1,z2,z3,z4,z5,z762])],[(0,[z1,z2,z3,z4,z5,z763]),(0,[z0,z95,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z764,z6]),(0,[z1,z765,z3,z4,z5,z6]),(0,[z14,z1,z442,z3,z5,z6]),(0,[z14,z206,z1,z3,z5,z6]),(0,[z474,z1,z3,z4,z5,z377])],[(0,[z766,z1,z3,z4,z5,z6]),(0,[z14,z1,z599,z3,z5,z6]),(0,[z43,z1,z2,z4,z159,z275])],[(0,[z1,z2,z4,z760,z159,z6])],[(0,[z170,z1,z2,z5,z49,z6]),(0,[z1,z2,z3,z4,z5,z27]),(0,[z767,z1,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z36,z768]),(0,[z1,z21,z116,z3,z5,z6])],[(0,[z1,z2,z3,z769,z5,z6])],[(0,[z410,z2,z3,z4,z5,z56]),(0,[z14,z95,z3,z5,z118,z6]),(0,[z770,z3,z15,z4,z5,z6])],[(0,[z84,z2,z3,z121,z5,z56]),(0,[z170,z14,z1,z3,z5,z6]),(0,[z84,z14,z361,z3,z5,z6]),(0,[z1,z301,z3,z4,z5,z275])],[(0,[z1,z771,z3,z4,z5,z6]),(0,[z14,z772,z3,z4,z5,z6])],[(0,[z773,z1,z2,z3,z5,z6]),(0,[z180,z14,z1,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z275]),(0,[z1,z2,z3,z641,z87,z6]),(0,[z1,z2,z3,z4,z5,z774])]],
   [[],[(0,[z14,z1,z3,z38,z5,z6]),(0,[z1,z2,z3,z4,z5,z775]),(0,[z248,z2,z3,z121,z5,z6]),(0,[z14,z3,z4,z5,z314,z6]),(0,[z1,z124,z3,z5,z6,z394])],[(0,[z1,z2,z3,z280,z5,z6]),(0,[z1,z2,z381,z4,z5,z303]),(0,[z2,z3,z4,z5,z115,z776]),(0,[z14,z1,z338,z3,z5,z6]),(0,[z777,z2,z3,z4,z5,z6]),(0,[z1,z778,z3,z4,z5,z6])],[(0,[z1,z779,z3,z4,z5,z6]),(0,[z3,z15,z4,z5,z314,z6]),(0,[z1,z2,z5,z712,z49,z6]),(0,[z780,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z5,z6,z781]),(0,[z1,z66,z15,z4,z153,z6]),(0,[z1,z2,z782,z4,z5,z6])],[(0,[z783,z2,z3,z4,z5,z6]),(0,[z14,z1,z3,z5,z671,z6]),(0,[z19,z95,z3,z4,z5,z6])],[(0,[z0,z3,z4,z234,z5,z6]),(0,[z367,z1,z2,z4,z159,z6]),(0,[z14,z1,z3,z80,z5,z6]),(0,[z1,z376,z3,z5,z143,z6]),(0,[z1,z624,z112,z48,z5,z6]),(0,[z1,z2,z3,z784,z5,z6]),(0,[z104,z1,z2,z242,z4,z60])],[(0,[z1,z2,z3,z5,z6,z785])],[(0,[z1,z786,z3,z4,z5,z6]),(0,[z755,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z38,z5,z229]),(0,[z82,z2,z3,z4,z5,z56])],[(0,[z357,z119,z3,z4,z5,z6]),(0,[z1,z3,z787,z191,z5,z6]),(0,[z14,z1,z67,z4,z5,z6])],[(0,[z1,z2,z3,z788,z5,z6]),(0,[z789,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z110,z5,z6])],[(0,[z14,z1,z3,z24,z5,z6]),(0,[z790,z1,z3,z4,z5,z6])],[(0,[z791,z1,z2,z3,z5,z6]),(0,[z2,z3,z4,z5,z776,z6]),(0,[z1,z2,z3,z4,z697,z46])],[(0,[z14,z1,z2,z3,z5,z36]),(1,[z1,z2,z3,z5,z792])],[]],
   [[(0,[z793,z1,z3,z4,z5,z6]),(0,[z14,z794,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z795])],[(0,[z19,z1,z3,z4,z5,z358]),(0,[z23,z2,z3,z24,z5,z171]),(0,[z1,z2,z3,z796,z5,z6]),(0,[z90,z2,z3,z4,z5,z316])],[(0,[z248,z3,z120,z121,z5,z6]),(0,[z516,z1,z282,z4,z5,z6]),(0,[z14,z1,z3,z693,z5,z6])],[(0,[z31,z443,z1,z3,z5,z6]),(0,[z1,z2,z797,z4,z5,z6])],[(0,[z82,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z5,z118,z792])],[],[(0,[z474,z14,z1,z3,z5,z87]),(0,[z305,z1,z2,z4,z159,z6])],[(0,[z41,z2,z3,z4,z798,z6]),(0,[z95,z3,z15,z4,z5,z6]),(0,[z799,z1,z3,z203,z5,z6])],[(0,[z0,z14,z3,z121,z5,z6]),(0,[z1,z2,z3,z4,z800,z6]),(0,[z1,z2,z3,z801,z5,z6]),(0,[z1,z2,z3,z4,z5,z802]),(0,[z1,z346,z3,z231,z5,z6])],[(0,[z253,z734,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z303]),(0,[z1,z3,z803,z4,z5,z6]),(0,[z1,z346,z242,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z804]),(0,[z14,z185,z3,z121,z5,z6]),(0,[z1,z402,z15,z4,z5,z6]),(0,[z155,z2,z3,z4,z150,z6]),(0,[z1,z2,z3,z805,z5,z6]),(0,[z1,z112,z274,z48,z5,z6]),(0,[z1,z806,z3,z4,z5,z6])],[(0,[z95,z2,z3,z5,z118,z6]),(0,[z1,z259,z3,z203,z5,z6]),(0,[z1,z2,z658,z4,z5,z236])],[(0,[z93,z2,z94,z4,z5,z131]),(0,[z1,z807,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z808,z6]),(0,[z1,z2,z809,z4,z5,z6]),(0,[z1,z178,z3,z438,z5,z6]),(0,[z14,z1,z288,z3,z5,z6]),(0,[z1,z3,z4,z5,z6,z810]),(0,[z1,z3,z4,z5,z6,z811])],[(0,[z1,z812,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z813,z6]),(0,[z95,z21,z2,z3,z5,z6]),(0,[z814,z2,z3,z4,z5,z6]),(0,[z1,z346,z67,z4,z5,z6])],[(0,[z815,z1,z3,z378,z5,z6]),(0,[z1,z71,z3,z4,z5,z171]),(0,[z1,z21,z2,z3,z527,z6])]],
   [[(0,[z1,z2,z3,z4,z816,z6]),(0,[z76,z14,z1,z3,z5,z6]),(0,[z399,z2,z3,z110,z5,z6])],[(0,[z1,z817,z3,z4,z5,z6]),(0,[z41,z2,z3,z191,z150,z6])],[(0,[z1,z818,z3,z4,z5,z6]),(0,[z289,z14,z1,z3,z5,z6]),(0,[z1,z106,z3,z121,z5,z6]),(0,[z206,z814,z2,z3,z5,z6])],[(0,[z14,z1,z3,z510,z5,z6]),(0,[z14,z1,z3,z627,z5,z6]),(0,[z1,z2,z819,z4,z5,z6])],[(0,[z1,z99,z381,z4,z5,z6]),(0,[z31,z1,z52,z4,z5,z42]),(0,[z2,z3,z4,z5,z820,z6])],[(0,[z14,z1,z3,z669,z5,z6]),(0,[z31,z1,z282,z4,z5,z6]),(0,[z1,z117,z744,z4,z5,z6]),(0,[z14,z1,z3,z5,z79,z6]),(0,[z1,z624,z3,z4,z5,z27])],[(0,[z1,z2,z3,z5,z821,z6]),(0,[z822,z2,z3,z4,z5,z6]),(0,[z1,z3,z823,z4,z5,z6]),(1,[z824,z1,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z825]),(0,[z1,z826,z3,z4,z5,z6])],[(0,[z14,z1,z3,z5,z86,z87])],[(0,[z93,z2,z3,z4,z5,z100]),(0,[z185,z2,z3,z24,z5,z6]),(0,[z1,z2,z3,z827,z5,z6])],[(0,[z185,z119,z3,z4,z5,z6]),(0,[z1,z126,z3,z121,z5,z6]),(0,[z97,z1,z3,z24,z5,z6]),(0,[z55,z3,z15,z4,z5,z56]),(0,[z14,z1,z21,z3,z527,z6]),(0,[z828,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z829]),(0,[z1,z2,z3,z830,z5,z6]),(0,[z14,z1,z3,z105,z5,z6]),(0,[z831,z3,z15,z4,z5,z6]),(0,[z399,z2,z3,z231,z5,z6])],[(0,[z518,z2,z3,z24,z5,z6]),(0,[z1,z832,z2,z3,z5,z6])],[(0,[z833,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z438,z5,z115]),(0,[z1,z3,z15,z57,z5,z118]),(0,[z399,z2,z242,z4,z5,z6])],[(0,[z668,z2,z3,z121,z5,z6]),(0,[z834,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z835,z5,z6]),(0,[z1,z3,z4,z5,z836,z6])],[(0,[z84,z14,z1,z3,z5,z118])],[(0,[z31,z1,z52,z4,z5,z6])]],
   [[(0,[z1,z3,z15,z4,z5,z171]),(0,[z14,z1,z611,z3,z5,z6]),(0,[z19,z1,z3,z4,z5,z113])],[(0,[z284,z2,z66,z4,z5,z6]),(0,[z227,z2,z3,z74,z5,z6]),(0,[z1,z2,z751,z3,z4,z6])],[(0,[z1,z2,z837,z4,z5,z6]),(0,[z1,z3,z787,z4,z5,z6]),(0,[z72,z3,z15,z4,z73,z6]),(0,[z233,z1,z3,z4,z527,z6])],[(0,[z1,z2,z3,z91,z5,z6]),(0,[z1,z3,z15,z138,z5,z6]),(0,[z1,z2,z3,z750,z5,z6]),(0,[z206,z1,z188,z3,z5,z6]),(0,[z19,z1,z3,z4,z5,z838])],[(0,[z1,z178,z3,z4,z5,z6]),(0,[z14,z1,z3,z5,z135,z6]),(0,[z839,z2,z3,z4,z5,z6])],[(0,[z144,z1,z3,z4,z5,z6]),(0,[z1,z2,z94,z4,z404,z6]),(0,[z345,z2,z3,z121,z5,z6]),(0,[z1,z2,z3,z191,z5,z303]),(0,[z1,z3,z840,z203,z5,z6]),(0,[z104,z334,z2,z3,z4,z60])],[(0,[z1,z841,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z842,z6]),(0,[z1,z117,z3,z4,z5,z42]),(0,[z43,z227,z2,z4,z159,z6]),(0,[z1,z843,z3,z4,z5,z6])],[(0,[z844,z2,z3,z4,z5,z6]),(0,[z1,z3,z15,z5,z145,z6]),(0,[z845,z1,z2,z3,z4,z5]),(0,[z1,z846,z3,z4,z5,z6])],[(0,[z680,z2,z3,z4,z5,z115]),(0,[z14,z1,z3,z4,z5,z36]),(0,[z84,z14,z1,z3,z5,z85]),(0,[z267,z1,z112,z3,z5,z6]),(1,[z1,z2,z4,z760,z6])],[(0,[z1,z2,z3,z847,z5,z6]),(0,[z1,z3,z15,z203,z5,z6])],[(0,[z1,z2,z3,z4,z404,z6]),(0,[z14,z1,z3,z4,z5,z848]),(0,[z334,z2,z3,z110,z5,z6])],[(1,[z2,z3,z849,z5,z6])],[(1,[z1,z2,z3,z4,z850])],[(0,[z1,z2,z3,z4,z5,z851]),(0,[z1,z852,z3,z4,z5,z6]),(0,[z499,z2,z3,z121,z5,z6]),(0,[z1,z853,z3,z4,z5,z6])],[(0,[z591,z2,z94,z4,z5,z6]),(0,[z84,z14,z95,z3,z5,z6]),(0,[z14,z1,z21,z3,z87,z6])],[(0,[z1,z2,z854,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z855]),(0,[z1,z3,z4,z5,z6,z394]),(0,[z1,z2,z3,z74,z5,z275]),(0,[z1,z856,z3,z4,z5,z6])]],
   [[(0,[z96,z1,z52,z4,z5,z6]),(0,[z207,z14,z1,z3,z5,z6]),(0,[z1,z857,z3,z4,z5,z6])],[(0,[z144,z1,z3,z5,z87,z6]),(0,[z14,z1,z3,z4,z5,z858])],[(0,[z1,z2,z3,z4,z272,z6]),(0,[z206,z1,z117,z3,z5,z6]),(0,[z14,z1,z3,z5,z173,z6])],[(0,[z1,z3,z15,z4,z5,z229]),(0,[z1,z284,z2,z4,z159,z6])],[(0,[z1,z3,z859,z438,z5,z6]),(0,[z1,z860,z2,z3,z5,z6]),(0,[z861,z2,z3,z4,z5,z6])],[(0,[z1,z2,z402,z4,z5,z6]),(0,[z95,z3,z4,z5,z35,z6]),(0,[z241,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z5,z712,z6])],[(0,[z1,z2,z3,z4,z5,z862]),(0,[z1,z2,z3,z4,z863,z6]),(0,[z14,z1,z3,z4,z5,z436]),(0,[z14,z864,z3,z4,z5,z6]),(0,[z14,z1,z3,z5,z6,z667])],[(0,[z14,z1,z3,z4,z5,z865]),(0,[z1,z415,z3,z4,z5,z6]),(0,[z1,z3,z5,z377,z145,z6])],[(0,[z1,z2,z866,z4,z5,z6]),(0,[z2,z9,z4,z73,z159,z6]),(0,[z1,z2,z3,z4,z5,z867]),(0,[z1,z3,z868,z4,z5,z6]),(0,[z14,z1,z3,z5,z193,z6]),(0,[z1,z869,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z870,z6]),(0,[z41,z2,z3,z4,z150,z6])],[(0,[z16,z1,z3,z4,z871,z6])],[(0,[z84,z1,z2,z3,z5,z579]),(0,[z196,z1,z3,z4,z5,z33]),(0,[z235,z1,z15,z4,z5,z58]),(0,[z1,z2,z3,z872,z5,z6])],[(0,[z1,z2,z873,z4,z5,z6]),(0,[z93,z2,z94,z4,z272,z6]),(0,[z1,z2,z3,z4,z5,z874]),(0,[z399,z2,z3,z57,z4,z5]),(0,[z1,z2,z242,z4,z5,z46])],[(0,[z1,z875,z3,z4,z5,z6]),(0,[z14,z1,z21,z22,z3,z6])],[(0,[z1,z2,z3,z4,z272,z131]),(0,[z1,z3,z876,z231,z5,z6])],[(0,[z507,z7,z3,z4,z5,z6]),(0,[z93,z2,z94,z280,z5,z6]),(0,[z877,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z878]),(0,[z206,z879,z2,z3,z5,z6])]],
   [[(0,[z90,z2,z3,z438,z5,z115]),(0,[z84,z1,z2,z3,z5,z33])],[(0,[z1,z2,z3,z280,z5,z131]),(0,[z114,z1,z5,z167,z49,z6]),(0,[z284,z2,z3,z4,z5,z197]),(0,[z1,z2,z3,z880,z5,z6])],[(0,[z1,z3,z274,z4,z5,z6]),(0,[z14,z1,z3,z468,z5,z6]),(0,[z1,z124,z3,z274,z5,z6]),(0,[z1,z2,z112,z48,z5,z27])],[(0,[z104,z1,z2,z67,z4,z60])],[(0,[z1,z3,z52,z4,z5,z42]),(0,[z235,z1,z2,z4,z5,z58])],[(0,[z1,z2,z881,z4,z5,z6]),(0,[z14,z1,z341,z3,z5,z6])],[(0,[z14,z3,z24,z121,z5,z6]),(0,[z1,z2,z402,z4,z73,z6]),(0,[z14,z882,z3,z4,z5,z6]),(0,[z14,z185,z3,z80,z5,z6]),(0,[z1,z3,z883,z4,z5,z6]),(0,[z104,z1,z346,z3,z4,z60])],[(0,[z1,z884,z3,z4,z5,z6]),(0,[z14,z1,z3,z5,z700,z6]),(0,[z1,z99,z3,z191,z5,z6]),(0,[z1,z2,z402,z4,z5,z100]),(0,[z14,z1,z3,z5,z238,z6]),(0,[z14,z1,z3,z5,z240,z6]),(0,[z1,z885,z3,z4,z5,z6])],[(0,[z1,z2,z3,z886,z5,z6]),(0,[z2,z3,z4,z5,z314,z6]),(0,[z1,z124,z3,z120,z5,z6]),(0,[z1,z2,z3,z4,z5,z887]),(0,[z482,z1,z3,z4,z5,z113]),(0,[z2,z3,z4,z5,z46,z330]),(0,[z1,z2,z3,z231,z5,z6])],[(0,[z345,z2,z3,z4,z5,z115]),(0,[z235,z14,z1,z4,z5,z58])],[(0,[z1,z2,z3,z4,z5,z888]),(0,[z1,z2,z242,z4,z5,z6]),(0,[z474,z1,z2,z3,z261,z87])],[(0,[z1,z3,z889,z4,z5,z6]),(0,[z41,z2,z3,z4,z150,z100]),(0,[z1,z3,z859,z4,z5,z6]),(0,[z890,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z891,z6]),(0,[z14,z95,z21,z3,z5,z6]),(0,[z1,z2,z3,z892,z5,z6])],[(0,[z14,z185,z3,z24,z5,z6]),(0,[z893,z2,z3,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z894]),(0,[z235,z1,z2,z4,z5,z895])],[(0,[z896,z1,z3,z4,z5,z6]),(0,[z2,z3,z438,z121,z5,z6]),(0,[z1,z3,z897,z138,z5,z6]),(0,[z1,z2,z4,z5,z712,z6]),(0,[z898,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z899])],[(0,[z1,z3,z15,z5,z6,z494]),(0,[z1,z2,z67,z4,z5,z6])],[(0,[z443,z1,z3,z5,z6,z113]),(0,[z1,z188,z3,z4,z432,z6])]],
   [[(0,[z1,z2,z3,z5,z900,z6]),(0,[z185,z2,z3,z38,z5,z6]),(0,[z269,z2,z3,z4,z404,z6]),(0,[z2,z3,z4,z849,z5,z6]),(0,[z1,z2,z402,z191,z5,z6])],[(0,[z1,z734,z3,z4,z5,z6]),(0,[z901,z2,z3,z4,z5,z6]),(0,[z1,z902,z3,z4,z5,z6])],[(0,[z1,z3,z903,z378,z5,z6]),(0,[z1,z3,z4,z5,z904,z6]),(0,[z1,z905,z3,z4,z5,z6])],[(0,[z72,z2,z3,z4,z285,z6]),(0,[z241,z2,z3,z906,z5,z6]),(0,[z1,z2,z3,z261,z86,z87])],[(0,[z1,z907,z3,z4,z5,z6]),(0,[z1,z908,z3,z4,z5,z6]),(0,[z206,z1,z3,z52,z5,z6]),(0,[z233,z95,z3,z4,z5,z6])],[(0,[z1,z2,z3,z24,z5,z297]),(0,[z1,z124,z3,z5,z377,z6]),(0,[z1,z571,z376,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z909])],[(0,[z1,z2,z3,z57,z5,z403])],[(0,[z1,z2,z910,z4,z5,z6]),(0,[z2,z3,z4,z5,z293,z56]),(0,[z1,z2,z3,z911,z5,z6]),(0,[z90,z2,z3,z4,z5,z115])],[(0,[z14,z1,z112,z3,z5,z6]),(0,[z361,z2,z3,z4,z5,z58])],[(0,[z90,z2,z3,z280,z5,z6]),(0,[z84,z144,z1,z3,z5,z6]),(0,[z2,z3,z4,z5,z299,z56]),(0,[z1,z2,z3,z4,z5,z912]),(0,[z1,z2,z3,z4,z5,z913])],[(0,[z1,z914,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z915])],[(0,[z474,z1,z2,z3,z24,z5]),(0,[z241,z916,z3,z4,z5,z6])],[(0,[z1,z34,z3,z138,z5,z6]),(0,[z1,z2,z3,z917,z5,z6])],[(0,[z103,z7,z3,z4,z5,z6]),(0,[z14,z1,z3,z5,z101,z6]),(1,[z474,z14,z1,z3,z5]),(0,[z95,z3,z4,z5,z143,z6]),(0,[z1,z3,z550,z4,z5,z173])],[(0,[z1,z918,z3,z4,z5,z6]),(0,[z1,z3,z5,z118,z6,z919])],[(0,[z1,z2,z3,z378,z5,z6]),(0,[z1,z920,z3,z4,z5,z6]),(0,[z227,z2,z3,z4,z5,z275])]],
   [[(0,[z2,z910,z94,z4,z5,z6]),(0,[z241,z14,z3,z4,z5,z6]),(0,[z474,z1,z2,z3,z4,z5]),(0,[z84,z1,z3,z5,z276,z85]),(0,[z84,z366,z1,z3,z5,z6])],[(0,[z1,z921,z2,z3,z5,z6]),(0,[z514,z2,z3,z4,z73,z6]),(0,[z1,z922,z2,z3,z5,z6])],[(0,[z14,z1,z3,z868,z5,z6]),(0,[z879,z2,z3,z4,z5,z6]),(0,[z824,z1,z2,z3,z5,z6])],[(0,[z2,z3,z4,z5,z6,z330]),(0,[z923,z1,z3,z4,z5,z6]),(0,[z474,z1,z3,z15,z4,z5]),(0,[z924,z2,z3,z4,z5,z6]),(0,[z399,z2,z67,z4,z5,z6])],[(0,[z82,z925,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z926])],[(0,[z23,z3,z24,z15,z5,z6]),(0,[z1,z3,z927,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z928]),(0,[z114,z14,z1,z112,z5,z6]),(0,[z1,z124,z3,z15,z5,z6]),(0,[z284,z301,z3,z4,z5,z6])],[(0,[z703,z2,z3,z4,z150,z6]),(0,[z1,z424,z3,z4,z5,z58])],[(0,[z929,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z930]),(0,[z474,z931,z2,z3,z4,z5])],[(0,[z474,z1,z2,z3,z110,z5])],[(0,[z1,z2,z3,z38,z5,z525]),(0,[z93,z2,z94,z378,z5,z6])],[(0,[z1,z374,z3,z438,z5,z6])],[(0,[z1,z2,z3,z378,z5,z131]),(0,[z443,z1,z188,z3,z5,z6]),(0,[z14,z1,z3,z5,z333,z6])],[(0,[z1,z2,z3,z4,z5,z932]),(0,[z2,z402,z4,z5,z150,z6]),(0,[z1,z2,z3,z57,z5,z135])],[(0,[z933,z1,z2,z3,z5,z6])],[(0,[z144,z7,z3,z4,z5,z6]),(0,[z1,z2,z3,z934,z5,z6]),(0,[z1,z2,z3,z4,z935,z6]),(0,[z14,z95,z3,z15,z5,z6])],[(0,[z1,z99,z3,z4,z5,z6]),(0,[z361,z2,z3,z4,z5,z6]),(0,[z1,z744,z52,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z86]),(0,[z1,z3,z936,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z280,z272,z6]),(0,[z72,z2,z3,z4,z798,z6]),(0,[z677,z2,z3,z4,z5,z56]),(0,[z1,z937,z3,z4,z5,z6])],[(0,[z1,z938,z3,z4,z5,z6]),(0,[z14,z1,z629,z3,z5,z6]),(0,[z1,z3,z15,z4,z5,z939]),(0,[z1,z2,z3,z940,z5,z6]),(0,[z1,z941,z3,z4,z5,z6])],[(0,[z1,z942,z3,z4,z5,z6]),(0,[z1,z2,z3,z57,z110,z5])],[(0,[z14,z1,z3,z5,z118,z6]),(0,[z1,z943,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z330,z60])],[(0,[z14,z1,z535,z3,z5,z6]),(0,[z43,z2,z4,z314,z159,z6]),(0,[z944,z2,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z945,z5,z6]),(0,[z1,z21,z2,z22,z3,z6])],[(0,[z1,z2,z3,z946,z5,z6]),(0,[z93,z2,z94,z4,z404,z6]),(0,[z1,z947,z3,z4,z5,z6]),(0,[z23,z178,z3,z4,z5,z6]),(0,[z14,z1,z3,z57,z5,z118]),(0,[z1,z3,z274,z4,z5,z27]),(0,[z334,z2,z3,z231,z5,z6])],[(0,[z602,z14,z1,z3,z5,z6])],[(0,[z1,z2,z3,z4,z404,z131]),(0,[z1,z102,z4,z5,z264,z6]),(0,[z235,z1,z192,z4,z5,z58]),(0,[z334,z2,z242,z4,z5,z6])],[],[(0,[z1,z2,z948,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z171]),(0,[z1,z3,z4,z5,z6,z949])],[(0,[z1,z2,z3,z4,z950,z6]),(0,[z1,z2,z3,z4,z5,z36])],[(0,[z1,z424,z3,z4,z5,z6]),(0,[z1,z2,z751,z3,z5,z6]),(0,[z334,z2,z67,z4,z5,z6])],[(0,[z443,z1,z7,z3,z5,z6]),(0,[z0,z126,z3,z4,z5,z6]),(0,[z14,z1,z3,z138,z5,z6]),(0,[z1,z951,z3,z4,z5,z6]),(0,[z1,z259,z3,z4,z5,z197]),(0,[z1,z952,z3,z4,z5,z6])],[(0,[z14,z1,z3,z5,z6,z384]),(0,[z1,z376,z188,z3,z5,z6])]],
   [[],[(0,[z1,z99,z3,z4,z5,z100]),(0,[z1,z953,z3,z4,z5,z6])],[(0,[z0,z119,z3,z4,z5,z229]),(0,[z2,z3,z954,z4,z5,z6]),(0,[z14,z1,z3,z5,z145,z6]),(0,[z14,z1,z3,z5,z6,z394]),(0,[z1,z3,z15,z567,z5,z6])],[(0,[z241,z2,z3,z4,z150,z6]),(0,[z1,z3,z4,z5,z377,z86])],[(0,[z14,z185,z3,z38,z5,z6]),(0,[z502,z14,z1,z3,z5,z6]),(0,[z14,z1,z3,z203,z5,z6])],[(0,[z2,z9,z4,z5,z413,z6]),(0,[z14,z248,z3,z121,z5,z6]),(0,[z1,z2,z3,z4,z5,z858]),(0,[z955,z2,z3,z4,z5,z6])],[(0,[z1,z117,z610,z4,z5,z6]),(0,[z14,z1,z3,z5,z403,z6])],[(0,[z93,z2,z402,z4,z5,z6]),(0,[z1,z956,z3,z4,z5,z6]),(0,[z14,z1,z3,z5,z6,z407])],[(0,[z1,z2,z3,z38,z5,z6]),(0,[z84,z14,z1,z3,z5,z33]),(0,[z1,z2,z3,z5,z118,z520]),(0,[z957,z1,z3,z4,z5,z6]),(0,[z1,z2,z44,z4,z5,z58])],[(0,[z1,z2,z958,z4,z5,z6]),(0,[z1,z2,z3,z959,z5,z6]),(0,[z185,z2,z3,z4,z5,z848]),(0,[z1,z2,z3,z727,z5,z6])],[(0,[z1,z2,z3,z4,z5,z436]),(0,[z185,z3,z15,z4,z5,z6]),(0,[z960,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z961]),(0,[z1,z962,z3,z4,z5,z6])],[(0,[z1,z963,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z865]),(0,[z1,z3,z4,z5,z6,z964])],[(0,[z1,z461,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z965]),(0,[z824,z1,z3,z4,z5,z6])],[(0,[z966,z2,z3,z4,z5,z6]),(0,[z14,z1,z112,z3,z5,z27]),(0,[z82,z2,z3,z967,z5,z6]),(0,[z104,z1,z337,z3,z4,z60])],[(0,[z1,z503,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z229]),(0,[z14,z1,z450,z3,z5,z6]),(0,[z1,z3,z15,z4,z5,z12])],[(0,[z41,z2,z3,z4,z150,z303]),(0,[z84,z14,z1,z3,z5,z58])]],
   [[(0,[z1,z2,z3,z4,z5,z968]),(0,[z1,z2,z3,z57,z5,z792])],[(0,[z90,z2,z3,z4,z404,z6]),(0,[z1,z2,z66,z4,z760,z6]),(0,[z1,z2,z242,z110,z5,z6])],[(0,[z1,z2,z969,z4,z5,z6]),(1,[z14,z361,z3,z5,z6]),(0,[z104,z1,z2,z3,z4,z60])],[(0,[z1,z2,z970,z4,z5,z6]),(0,[z1,z2,z3,z971,z5,z6]),(0,[z1,z178,z3,z91,z5,z6]),(0,[z1,z2,z3,z972,z5,z6]),(0,[z206,z19,z1,z3,z5,z113]),(0,[z973,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z974]),(0,[z1,z3,z4,z5,z6,z975]),(0,[z1,z976,z3,z4,z5,z6])],[(0,[z1,z2,z3,z977,z5,z6]),(0,[z14,z95,z3,z4,z5,z6]),(0,[z104,z1,z3,z15,z4,z60]),(0,[z1,z2,z67,z110,z5,z6])],[(0,[z1,z2,z3,z5,z6,z978]),(0,[z616,z2,z3,z121,z5,z6]),(0,[z1,z106,z3,z24,z5,z6]),(0,[z84,z361,z2,z3,z5,z85]),(0,[z84,z1,z2,z242,z4,z5])],[(0,[z1,z2,z3,z4,z5,z979]),(0,[z14,z789,z3,z4,z5,z6]),(0,[z345,z953,z3,z4,z5,z6]),(0,[z980,z1,z2,z3,z5,z6])],[(0,[z23,z2,z3,z38,z5,z6]),(0,[z1,z461,z3,z4,z5,z131]),(0,[z93,z503,z94,z4,z5,z6]),(0,[z2,z3,z57,z4,z5,z330])],[(0,[z1,z2,z3,z981,z5,z6]),(0,[z1,z2,z3,z5,z792,z85])],[(0,[z1,z503,z3,z4,z5,z131]),(0,[z1,z2,z3,z4,z5,z982]),(0,[z1,z3,z15,z4,z5,z983]),(0,[z770,z2,z3,z4,z5,z6])],[(0,[z253,z95,z3,z4,z5,z6]),(0,[z14,z1,z3,z237,z5,z6]),(0,[z1,z3,z15,z4,z5,z197]),(0,[z1,z2,z4,z5,z236,z895])],[(0,[z14,z1,z3,z5,z462,z6]),(0,[z984,z2,z3,z4,z5,z6]),(0,[z1,z188,z3,z4,z871,z6]),(0,[z1,z2,z3,z985,z5,z6])],[(0,[z1,z126,z3,z24,z5,z6]),(0,[z986,z1,z2,z3,z4,z5]),(0,[z284,z2,z4,z5,z159,z6])],[(0,[z1,z2,z3,z987,z5,z6]),(0,[z1,z2,z3,z988,z5,z6]),(0,[z14,z443,z1,z3,z5,z6]),(0,[z14,z989,z3,z4,z5,z6]),(0,[z683,z1,z2,z4,z5,z58])],[]],
   [[(0,[z1,z2,z3,z990,z5,z6]),(0,[z1,z34,z381,z4,z5,z6]),(0,[z1,z2,z3,z438,z5,z56])],[(0,[z1,z2,z3,z4,z5,z991]),(1,[z2,z3,z4,z798,z6]),(0,[z14,z95,z3,z5,z87,z6]),(0,[z772,z2,z3,z4,z5,z6]),(0,[z1,z992,z3,z4,z5,z6])],[(0,[z1,z2,z3,z993,z5,z6]),(0,[z14,z72,z3,z4,z73,z6]),(0,[z19,z1,z3,z4,z5,z33])],[(0,[z1,z3,z15,z4,z5,z525]),(0,[z23,z2,z3,z24,z5,z6]),(0,[z14,z284,z3,z4,z5,z6]),(0,[z267,z1,z21,z3,z5,z6]),(0,[z994,z2,z3,z4,z5,z6]),(0,[z995,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z996]),(0,[z443,z1,z102,z3,z5,z6]),(0,[z2,z3,z4,z5,z6,z997])],[(0,[z1,z3,z15,z529,z5,z6]),(0,[z1,z2,z3,z4,z5,z998]),(0,[z999,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z813,z6]),(0,[z1,z259,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1000]),(0,[z1,z3,z612,z15,z5,z6]),(0,[z82,z2,z81,z4,z5,z236])],[(0,[z644,z1,z52,z4,z5,z6]),(0,[z84,z14,z1,z3,z5,z6]),(0,[z1,z337,z3,z4,z5,z6]),(0,[z284,z2,z3,z4,z153,z6])],[(0,[z640,z1,z3,z4,z5,z113]),(0,[z14,z1,z571,z3,z5,z6])],[(0,[z23,z2,z3,z24,z5,z297]),(0,[z14,z185,z112,z3,z5,z6]),(0,[z474,z14,z1,z3,z4,z5]),(0,[z1,z624,z3,z4,z5,z36]),(0,[z284,z2,z3,z74,z5,z6]),(0,[z84,z1,z2,z3,z5,z384])],[(0,[z93,z2,z910,z4,z5,z6]),(0,[z345,z2,z3,z24,z5,z6]),(0,[z14,z1,z3,z4,z5,z1001])],[(0,[z1,z2,z3,z1002,z5,z6]),(0,[z1,z3,z1003,z4,z5,z6])],[(0,[z1,z2,z3,z280,z404,z6]),(0,[z284,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z849,z5,z6]),(0,[z185,z95,z3,z4,z5,z6])],[(0,[z705,z2,z3,z121,z5,z6]),(0,[z1004,z1,z3,z138,z5,z6]),(0,[z14,z1,z3,z51,z5,z6])],[(0,[z206,z19,z1,z3,z5,z6])],[(0,[z702,z1,z3,z15,z5,z6]),(0,[z90,z2,z3,z4,z5,z436]),(0,[z877,z1,z3,z91,z5,z6]),(0,[z84,z14,z1,z3,z5,z236]),(0,[z1,z2,z3,z4,z5,z792])],[(0,[z2,z3,z4,z5,z6,z1005])]],
   [[(0,[z1006,z1,z3,z4,z5,z6]),(0,[z14,z334,z3,z4,z5,z6])],[(0,[z1,z71,z3,z4,z5,z6]),(0,[z41,z99,z3,z4,z150,z6]),(0,[z1,z3,z4,z5,z6,z919]),(0,[z1,z2,z3,z203,z5,z197])],[],[],[(0,[z1,z1007,z3,z4,z5,z6])],[(0,[z367,z2,z94,z4,z5,z6]),(0,[z14,z754,z3,z4,z5,z6])],[(0,[z95,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1008,z6]),(0,[z1,z71,z3,z4,z5,z297]),(1,[z2,z3,z4,z5,z776]),(0,[z1009,z2,z3,z4,z5,z6])],[(0,[z1,z2,z129,z4,z5,z236]),(0,[z1,z1010,z3,z4,z5,z6])],[(0,[z1,z34,z3,z4,z5,z6]),(0,[z2,z3,z280,z5,z6,z56]),(0,[z223,z1,z2,z4,z5,z58]),(0,[z931,z2,z3,z4,z5,z6])],[(0,[z1,z1011,z3,z4,z5,z6])],[(0,[z41,z2,z402,z4,z150,z6]),(0,[z1,z2,z381,z138,z5,z6]),(0,[z14,z345,z3,z4,z5,z6]),(0,[z361,z2,z3,z4,z5,z236]),(0,[z1,z3,z4,z5,z6,z1012]),(0,[z84,z1,z2,z3,z5,z263])],[(0,[z1,z117,z102,z4,z5,z6]),(0,[z1,z1013,z3,z4,z5,z6]),(0,[z399,z337,z3,z4,z5,z6])],[(0,[z93,z94,z15,z4,z5,z6]),(0,[z172,z14,z1,z3,z5,z6])],[(0,[z2,z3,z4,z73,z798,z6]),(0,[z14,z185,z3,z4,z5,z848]),(0,[z1,z2,z242,z57,z4,z5])],[(0,[z1,z117,z319,z4,z5,z6]),(0,[z1,z3,z840,z4,z5,z6])],[]],
   [[],[(0,[z2,z1014,z3,z4,z5,z6]),(0,[z14,z1,z3,z5,z545,z6]),(0,[z14,z1,z3,z5,z6,z919]),(0,[z1,z2,z3,z4,z5,z848])],[(0,[z1,z3,z15,z4,z5,z6]),(0,[z95,z2,z3,z5,z87,z6]),(0,[z104,z1,z2,z3,z231,z60])],[(0,[z1,z2,z3,z4,z5,z1015]),(0,[z474,z1,z124,z2,z3,z5])],[(0,[z1,z374,z3,z4,z5,z6]),(0,[z1,z2,z66,z4,z228,z6]),(0,[z2,z81,z4,z5,z236,z330])],[(0,[z1,z99,z3,z4,z5,z303]),(0,[z1,z3,z1016,z4,z5,z6]),(0,[z1,z2,z3,z4,z1017,z6])],[(0,[z1,z2,z3,z1018,z5,z6]),(0,[z90,z2,z3,z91,z5,z115]),(0,[z1,z2,z3,z4,z5,z855]),(0,[z1,z2,z751,z3,z261,z6])],[(0,[z1,z2,z3,z1019,z5,z6]),(0,[z1,z2,z3,z1020,z5,z6]),(0,[z1,z3,z15,z4,z5,z297]),(0,[z90,z178,z3,z4,z5,z115]),(0,[z114,z14,z185,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z1021]),(0,[z104,z1,z2,z3,z4,z850])],[(0,[z1,z2,z1022,z4,z5,z6]),(0,[z1,z2,z3,z1023,z5,z6]),(0,[z55,z2,z3,z4,z5,z56]),(0,[z1,z1024,z2,z3,z5,z6]),(0,[z1,z424,z3,z4,z5,z236]),(0,[z1,z2,z1025,z4,z5,z6])],[(0,[z1,z503,z3,z4,z272,z6]),(0,[z1,z2,z1026,z4,z5,z6]),(0,[z14,z1,z3,z576,z5,z6]),(0,[z831,z2,z3,z4,z5,z6]),(0,[z1,z2,z268,z4,z5,z236])],[(0,[z14,z1,z3,z405,z5,z6]),(0,[z882,z2,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z86])],[(0,[z1,z7,z3,z38,z5,z6]),(0,[z1,z1027,z3,z4,z5,z6]),(0,[z1,z2,z3,z57,z5,z118])],[(0,[z1,z503,z3,z280,z5,z6]),(0,[z241,z2,z3,z4,z5,z1028])],[(0,[z332,z1,z2,z4,z159,z6]),(0,[z345,z2,z3,z4,z5,z56]),(0,[z14,z1029,z3,z4,z5,z6]),(0,[z1030,z2,z3,z4,z5,z6]),(0,[z1,z1031,z3,z4,z5,z6])],[(0,[z896,z1,z3,z280,z5,z6]),(0,[z1,z2,z402,z4,z5,z303]),(0,[z104,z84,z14,z1,z3,z5]),(0,[z1,z112,z15,z48,z5,z6])],[(0,[z31,z1,z51,z52,z5,z6]),(0,[z1032,z2,z3,z4,z5,z6])]],
   [[(0,[z248,z2,z3,z849,z5,z6]),(0,[z1,z3,z15,z5,z6,z154]),(0,[z2,z3,z4,z5,z1033,z6]),(0,[z2,z3,z4,z5,z6,z768]),(0,[z43,z1,z2,z203,z159,z6])],[(0,[z1,z2,z3,z4,z5,z1034]),(0,[z72,z2,z3,z4,z73,z6]),(0,[z1,z2,z3,z5,z6,z1035])],[],[(0,[z1,z188,z3,z4,z243,z6]),(0,[z1,z1036,z3,z4,z5,z6]),(0,[z1,z34,z3,z191,z5,z6]),(0,[z14,z1,z21,z3,z5,z6]),(0,[z14,z1,z3,z274,z5,z6]),(0,[z1037,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1038,z5,z6])],[(0,[z1,z3,z15,z4,z5,z100])],[(0,[z1,z2,z3,z378,z404,z6]),(0,[z1,z2,z112,z48,z5,z36]),(0,[z1,z301,z3,z203,z5,z6]),(0,[z1,z2,z3,z1039,z5,z6]),(0,[z1,z2,z4,z5,z6,z895]),(0,[z334,z337,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1040]),(0,[z1041,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z377,z6])],[(0,[z1,z2,z3,z4,z5,z1042]),(0,[z93,z2,z94,z4,z5,z436]),(0,[z1043,z2,z3,z4,z5,z6]),(0,[z399,z3,z15,z4,z5,z6]),(0,[z1,z3,z1044,z4,z5,z6]),(0,[z1,z1045,z3,z4,z5,z6])],[(0,[z345,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z203,z5,z6])],[(0,[z93,z461,z94,z4,z5,z6]),(0,[z14,z1,z3,z120,z5,z6]),(0,[z1,z2,z3,z4,z850,z60])],[(0,[z1,z1046,z3,z4,z5,z6]),(0,[z104,z14,z1,z3,z4,z60]),(0,[z366,z1,z3,z5,z118,z6])],[(0,[z2,z3,z402,z4,z150,z6]),(0,[z1,z3,z4,z5,z6,z1047]),(0,[z207,z206,z1,z3,z5,z6]),(0,[z1048,z2,z3,z4,z5,z6])],[(0,[z1049,z1,z3,z4,z5,z6]),(0,[z581,z14,z1,z3,z5,z6]),(0,[z1,z3,z15,z4,z50,z46]),(0,[z1,z2,z3,z1050,z5,z6])],[(0,[z1,z2,z3,z378,z272,z6]),(0,[z1,z2,z1051,z4,z5,z6]),(0,[z1,z3,z15,z191,z5,z6]),(0,[z168,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z5,z1052]),(0,[z104,z1,z2,z3,z110,z60])],[(0,[z14,z1,z3,z5,z617,z6]),(0,[z1,z2,z242,z231,z5,z6])],[(0,[z1,z2,z3,z1053,z5,z6]),(0,[z1,z1054,z3,z4,z5,z6]),(0,[z1,z2,z1055,z4,z5,z6]),(0,[z14,z82,z3,z4,z5,z6]),(0,[z1056,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1057,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1058]),(0,[z1,z2,z3,z4,z5,z1059]),(0,[z1060,z1,z2,z3,z4,z5]),(0,[z14,z893,z3,z4,z5,z6]),(0,[z8,z3,z4,z234,z5,z6]),(0,[z1,z2,z3,z906,z5,z6])],[(0,[z474,z1,z2,z3,z57,z5]),(0,[z474,z1061,z2,z3,z4,z5]),(0,[z1,z2,z22,z751,z3,z6])],[(0,[z1,z2,z3,z1062,z5,z6]),(0,[z1,z117,z257,z4,z5,z6]),(0,[z14,z1,z3,z5,z626,z6]),(0,[z1,z3,z4,z5,z838,z113]),(0,[z1,z2,z67,z231,z5,z6]),(0,[z1,z3,z4,z5,z1063,z6])],[(0,[z2,z3,z4,z1064,z5,z6]),(0,[z799,z1,z3,z4,z5,z6])],[(1,[z1,z3,z4,z871,z6])],[(0,[z1,z1065,z3,z4,z5,z6]),(0,[z1,z112,z3,z868,z5,z6]),(0,[z1,z259,z3,z74,z5,z6]),(0,[z1,z2,z81,z4,z5,z75]),(0,[z1061,z2,z3,z4,z5,z6])],[(0,[z14,z1,z3,z5,z377,z6]),(0,[z284,z2,z3,z4,z5,z275])],[(0,[z1,z2,z3,z4,z5,z1066]),(0,[z97,z1,z3,z4,z5,z86]),(0,[z1,z1067,z3,z4,z5,z6])],[(0,[z1,z1068,z3,z4,z5,z6]),(0,[z1,z916,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1069,z5,z6]),(0,[z14,z1,z3,z4,z5,z12])],[(0,[z1,z2,z66,z4,z195,z6])],[(0,[z14,z1,z3,z449,z5,z6]),(0,[z1,z1070,z3,z4,z5,z6]),(0,[z1,z2,z1071,z4,z5,z6])],[(0,[z1,z3,z897,z4,z5,z6]),(0,[z31,z1,z744,z4,z5,z6]),(0,[z1,z162,z52,z4,z5,z6]),(0,[z443,z1,z152,z3,z5,z6]),(0,[z14,z1,z350,z3,z5,z6])],[(0,[z332,z2,z3,z4,z150,z6]),(0,[z1072,z1,z2,z3,z4,z5]),(0,[z1073,z2,z3,z4,z5,z6]),(0,[z1,z1074,z3,z4,z5,z6]),(0,[z1,z337,z3,z110,z5,z6])],[(0,[z14,z1,z3,z136,z5,z6])],[(0,[z43,z284,z2,z4,z159,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1075]),(0,[z14,z95,z3,z121,z5,z6]),(0,[z23,z126,z3,z24,z5,z6]),(0,[z1,z99,z402,z4,z5,z6]),(0,[z14,z1,z572,z3,z5,z6]),(0,[z721,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1076])],[(0,[z334,z3,z15,z4,z5,z6])],[(0,[z0,z119,z3,z4,z5,z525]),(0,[z14,z1,z376,z3,z5,z6])],[(0,[z1,z117,z69,z4,z5,z6]),(0,[z1,z2,z1077,z4,z5,z6]),(0,[z104,z399,z2,z3,z4,z60])],[(0,[z0,z119,z3,z529,z5,z6]),(0,[z354,z2,z3,z4,z5,z56]),(0,[z1,z1078,z3,z4,z5,z6]),(0,[z1079,z1,z3,z4,z5,z6])],[(0,[z1080,z1,z3,z4,z5,z6]),(0,[z241,z2,z3,z4,z73,z6]),(1,[z1,z2,z4,z5,z895])],[(0,[z1,z503,z3,z378,z5,z6]),(0,[z82,z2,z3,z4,z5,z6]),(0,[z14,z1,z3,z15,z5,z6]),(0,[z14,z1,z3,z4,z5,z197]),(0,[z84,z14,z345,z3,z5,z6])],[(0,[z371,z2,z3,z4,z5,z56]),(0,[z1,z2,z1081,z4,z5,z6])],[(0,[z126,z7,z3,z4,z5,z6])],[(0,[z1,z1082,z3,z4,z5,z6]),(0,[z267,z1,z3,z5,z87,z6])],[(0,[z1,z1083,z3,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z42]),(0,[z14,z1,z3,z4,z5,z1084]),(0,[z1,z3,z1085,z4,z5,z6]),(0,[z1,z3,z546,z4,z238,z6]),(0,[z1,z3,z4,z5,z6,z1086]),(0,[z1,z3,z4,z5,z6,z1087])],[(0,[z1,z2,z3,z4,z5,z1088]),(0,[z1,z124,z3,z750,z5,z6]),(0,[z1,z2,z3,z4,z5,z894])],[(0,[z1,z3,z1089,z4,z5,z6])],[(0,[z14,z1,z422,z3,z5,z6])],[(0,[z14,z1,z3,z4,z5,z525]),(0,[z19,z1,z3,z4,z5,z348]),(0,[z23,z2,z3,z849,z5,z6]),(0,[z1,z2,z3,z5,z6,z1090])],[(0,[z1,z3,z1091,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1092]),(0,[z1,z3,z5,z1093,z87,z6]),(0,[z1,z2,z3,z4,z5,z1094])]],
   [[(0,[z14,z1,z3,z529,z5,z6]),(0,[z72,z2,z3,z4,z213,z6]),(0,[z2,z3,z4,z5,z776,z56]),(0,[z583,z1,z2,z4,z5,z58]),(0,[z1,z2,z3,z51,z5,z6]),(0,[z14,z1,z3,z20,z5,z6]),(0,[z14,z1,z141,z3,z5,z6])],[(0,[z1,z1095,z3,z4,z5,z6]),(0,[z1,z1096,z3,z4,z5,z6])],[(0,[z1,z3,z15,z74,z5,z6]),(0,[z1097,z2,z3,z4,z5,z6])],[(0,[z14,z55,z3,z4,z5,z56]),(0,[z1,z2,z66,z4,z5,z197])],[(0,[z1,z2,z3,z1098,z5,z6]),(0,[z1,z503,z3,z4,z404,z6])],[(0,[z14,z1,z381,z4,z5,z6]),(0,[z14,z1,z3,z689,z5,z6])],[(0,[z1,z1099,z3,z4,z5,z6]),(0,[z14,z1,z3,z438,z5,z6]),(0,[z14,z185,z3,z5,z118,z6]),(0,[z92,z1,z3,z4,z478,z6]),(0,[z84,z2,z3,z4,z5,z330])],[(0,[z419,z2,z3,z121,z5,z6])],[(0,[z734,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z529,z5,z229]),(0,[z1,z2,z3,z1100,z5,z6]),(0,[z1,z2,z3,z4,z272,z436]),(0,[z1101,z1,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1102])],[(0,[z14,z1,z3,z25,z5,z6])],[(0,[z1,z461,z3,z4,z272,z6]),(0,[z1,z1103,z3,z4,z5,z6]),(0,[z1,z3,z274,z4,z5,z36]),(0,[z43,z241,z2,z4,z159,z6])],[(0,[z1,z2,z3,z280,z5,z436]),(0,[z1,z3,z1104,z4,z5,z6]),(0,[z31,z443,z1,z52,z5,z6]),(0,[z14,z1,z3,z5,z36,z6]),(0,[z644,z1,z2,z4,z5,z58]),(0,[z206,z1,z2,z3,z5,z58]),(0,[z1,z2,z4,z153,z760,z6])],[],[(0,[z1,z461,z3,z280,z5,z6]),(0,[z1,z34,z3,z4,z5,z100])],[(0,[z1105,z1,z2,z4,z5,z6]),(0,[z14,z1,z3,z663,z5,z6]),(0,[z474,z1,z2,z3,z5,z85])],[(0,[z1,z2,z3,z4,z5,z1106]),(0,[z14,z225,z1,z3,z5,z6]),(0,[z1107,z1,z3,z4,z5,z6]),(0,[z14,z1,z81,z4,z5,z236]),(0,[z1,z21,z2,z147,z3,z6])]],
   [[(0,[z355,z1,z52,z4,z5,z6])],[(0,[z0,z119,z3,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z131]),(0,[z1,z1108,z3,z4,z5,z6]),(1,[z2,z402,z4,z150,z6]),(0,[z1,z1109,z3,z4,z5,z6]),(0,[z14,z1,z3,z261,z87,z6]),(0,[z14,z1,z3,z61,z5,z6]),(0,[z1110,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z50,z369]),(0,[z1,z106,z3,z57,z5,z118])],[(0,[z2,z9,z3,z4,z5,z100]),(0,[z1,z2,z3,z4,z5,z171]),(0,[z114,z14,z95,z3,z5,z6]),(0,[z1,z67,z15,z4,z5,z6])],[(0,[z474,z14,z1,z2,z3,z5])],[(0,[z613,z7,z3,z4,z5,z6]),(0,[z1,z1111,z3,z4,z5,z6]),(0,[z14,z1,z66,z4,z153,z6])],[(0,[z1,z2,z9,z4,z404,z6]),(0,[z1,z2,z3,z138,z5,z6]),(0,[z1,z21,z2,z198,z3,z6]),(0,[z72,z2,z3,z4,z5,z100]),(0,[z1,z116,z3,z4,z5,z6]),(0,[z227,z259,z3,z4,z5,z6]),(0,[z235,z1,z424,z4,z5,z58])],[(0,[z14,z3,z121,z5,z6,z56]),(0,[z185,z2,z3,z4,z5,z1084])],[(0,[z1,z1112,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z1113,z6]),(0,[z14,z1,z3,z533,z5,z6]),(0,[z989,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1114,z6])],[(0,[z1,z1115,z3,z4,z5,z6]),(0,[z1,z192,z3,z4,z5,z6]),(0,[z399,z2,z3,z4,z5,z60])],[(0,[z1,z2,z3,z4,z5,z1116]),(0,[z178,z3,z4,z121,z5,z6]),(0,[z1,z2,z3,z5,z145,z6])],[],[(0,[z1,z2,z3,z4,z760,z6]),(0,[z1,z3,z1117,z4,z5,z6])],[(0,[z1,z2,z3,z5,z1118,z6]),(0,[z1,z3,z744,z4,z5,z6]),(0,[z14,z1,z1119,z4,z5,z6]),(0,[z1,z2,z3,z1120,z5,z6])],[(0,[z14,z1,z3,z4,z5,z6]),(0,[z361,z124,z2,z3,z5,z6]),(0,[z179,z1,z2,z5,z49,z6]),(0,[z1,z2,z3,z4,z50,z850])],[(0,[z1,z1121,z2,z3,z5,z6]),(0,[z1,z1122,z3,z4,z5,z6]),(0,[z1,z376,z188,z3,z17,z6])],[]],
   [[(0,[z248,z144,z3,z121,z5,z6]),(0,[z1,z2,z3,z4,z5,z1123]),(0,[z14,z1,z112,z3,z5,z36])],[(0,[z1,z2,z3,z4,z798,z6]),(0,[z14,z1,z3,z5,z128,z6]),(0,[z1,z3,z1124,z4,z5,z6]),(0,[z1,z116,z3,z5,z87,z6])],[(0,[z241,z2,z94,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z297]),(0,[z206,z1,z2,z3,z5,z6]),(0,[z1,z925,z3,z4,z5,z6])],[(0,[z14,z185,z21,z3,z5,z6]),(0,[z16,z1,z3,z4,z478,z6]),(0,[z1,z259,z3,z4,z5,z275])],[(0,[z1,z2,z3,z4,z5,z1125]),(0,[z14,z1,z3,z4,z1126,z6]),(0,[z1,z1127,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z229]),(0,[z1,z7,z3,z4,z5,z229]),(0,[z1,z119,z3,z38,z5,z6]),(0,[z84,z14,z1,z3,z5,z115]),(0,[z95,z3,z4,z5,z174,z6]),(0,[z1,z571,z392,z3,z4,z6]),(0,[z206,z1,z3,z15,z5,z6]),(0,[z1,z2,z3,z5,z1128,z6]),(0,[z1129,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1130])],[(0,[z1,z2,z3,z4,z5,z1131]),(0,[z241,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z138,z5,z100]),(0,[z14,z1,z1132,z4,z5,z6]),(0,[z1,z1133,z3,z4,z5,z6])],[(0,[z14,z1,z3,z463,z5,z6]),(0,[z1,z2,z3,z4,z1134,z6])],[(0,[z14,z1,z3,z5,z87,z6]),(0,[z14,z428,z1,z3,z5,z6])],[(0,[z1,z124,z2,z3,z5,z36]),(0,[z539,z1,z3,z4,z143,z6]),(0,[z673,z1,z3,z4,z5,z113]),(0,[z1,z2,z3,z4,z331,z46])],[(0,[z443,z1,z119,z3,z5,z6]),(0,[z14,z1,z3,z5,z6,z154]),(0,[z1,z313,z3,z15,z5,z6]),(0,[z1,z1135,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1136,z5,z6])],[(0,[z1,z2,z3,z5,z1137,z6]),(0,[z1,z3,z4,z5,z1138,z6]),(0,[z1,z1139,z3,z4,z5,z6])],[(0,[z1,z2,z681,z4,z5,z236]),(0,[z97,z1,z3,z261,z87,z6])],[]],
   [[(0,[z267,z1,z3,z4,z5,z6]),(0,[z1,z3,z5,z6,z154,z394])],[(0,[z1,z2,z3,z4,z5,z1140]),(0,[z1,z3,z15,z91,z5,z6]),(0,[z1,z3,z15,z750,z5,z6])],[(0,[z1,z2,z3,z1141,z5,z6]),(0,[z1,z1142,z3,z4,z5,z6]),(0,[z227,z3,z15,z4,z5,z6]),(0,[z1,z922,z424,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1143]),(0,[z1,z374,z3,z91,z5,z6]),(0,[z1,z2,z3,z1144,z5,z6]),(0,[z95,z117,z3,z4,z5,z6]),(0,[z824,z1,z424,z3,z5,z6])],[(0,[z1,z1145,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z798,z6]),(0,[z1,z3,z1016,z91,z5,z6]),(0,[z14,z1,z385,z3,z5,z6])],[(0,[z1,z3,z1146,z4,z5,z6]),(0,[z1,z2,z3,z378,z5,z436]),(0,[z2,z3,z4,z5,z150,z100]),(0,[z864,z2,z3,z4,z5,z6]),(0,[z14,z1,z729,z4,z5,z6])],[(0,[z702,z2,z3,z121,z5,z6]),(0,[z14,z1,z3,z559,z5,z6]),(0,[z1,z2,z3,z4,z5,z1147])],[(0,[z1,z461,z3,z378,z5,z6]),(0,[z14,z1,z3,z4,z50,z46])],[(0,[z1,z2,z3,z1148,z5,z6]),(0,[z14,z1,z3,z191,z5,z6]),(0,[z1,z1149,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z850])],[(0,[z1,z2,z3,z1150,z5,z6]),(0,[z1,z392,z3,z4,z143,z6]),(0,[z1,z3,z1151,z4,z5,z6])],[(0,[z1,z3,z1089,z280,z5,z6]),(0,[z93,z14,z94,z4,z5,z6]),(0,[z14,z1,z3,z675,z5,z6]),(0,[z566,z2,z3,z4,z5,z115]),(0,[z1,z3,z4,z5,z1093,z6]),(0,[z97,z1,z3,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z27]),(0,[z366,z1,z21,z3,z5,z6]),(0,[z84,z345,z2,z3,z5,z85]),(0,[z1,z337,z3,z231,z5,z6])],[(0,[z1152,z1,z3,z4,z5,z6])],[(0,[z507,z3,z368,z4,z5,z6]),(0,[z1,z337,z242,z4,z5,z6])],[(0,[z1,z1153,z3,z4,z5,z6]),(0,[z41,z34,z3,z4,z150,z6]),(0,[z1,z2,z3,z4,z5,z12]),(0,[z1154,z2,z3,z4,z5,z6])],[(0,[z84,z1,z2,z3,z5,z593]),(0,[z1,z2,z3,z4,z5,z1155])],[(0,[z14,z1,z3,z365,z5,z6]),(0,[z493,z1,z2,z4,z5,z58]),(0,[z1,z1156,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z15,z4,z272,z6]),(0,[z1,z2,z3,z4,z5,z1001]),(0,[z14,z960,z3,z4,z5,z6]),(0,[z1,z3,z15,z4,z5,z275]),(0,[z1,z1157,z3,z4,z5,z6]),(0,[z1,z337,z67,z4,z5,z6])],[(0,[z1,z1158,z3,z4,z5,z6]),(0,[z1,z3,z4,z1159,z5,z6]),(0,[z1160,z2,z3,z4,z5,z6]),(0,[z1161,z1,z3,z4,z5,z6])],[(0,[z1,z1162,z3,z4,z5,z6]),(0,[z248,z3,z15,z121,z5,z6]),(0,[z14,z1,z3,z221,z5,z6]),(0,[z14,z95,z3,z368,z5,z6]),(0,[z14,z1,z361,z3,z5,z6]),(0,[z1,z3,z4,z5,z6,z276]),(0,[z1,z188,z3,z4,z17,z6]),(1,[z1,z2,z5,z712,z6]),(0,[z43,z1,z2,z4,z159,z197])],[(0,[z1,z3,z15,z280,z5,z6]),(0,[z1,z2,z3,z4,z404,z436]),(0,[z1,z374,z3,z4,z5,z115]),(0,[z1,z2,z3,z57,z5,z628])],[(0,[z114,z1,z2,z5,z49,z6]),(0,[z1163,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1164]),(0,[z1,z2,z4,z5,z498,z58]),(0,[z1,z2,z4,z5,z895,z58]),(0,[z1165,z2,z3,z4,z5,z6])],[(0,[z1,z461,z3,z4,z404,z6]),(0,[z1,z2,z3,z57,z5,z128])],[(0,[z1166,z1,z3,z4,z5,z6]),(0,[z14,z185,z3,z15,z5,z6]),(0,[z14,z1,z3,z234,z5,z6]),(0,[z399,z346,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1167]),(0,[z41,z3,z15,z4,z150,z6]),(0,[z1,z1168,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1169]),(0,[z95,z3,z282,z4,z5,z6]),(0,[z1,z301,z3,z4,z5,z197]),(0,[z474,z97,z1,z3,z4,z5]),(0,[z1170,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1171,z5,z6]),(0,[z1,z3,z1172,z4,z5,z6]),(0,[z1,z2,z3,z1173,z5,z6]),(0,[z1174,z2,z3,z4,z5,z6]),(0,[z227,z2,z3,z203,z5,z6])],[(0,[z1,z2,z3,z1175,z5,z6]),(0,[z14,z23,z3,z24,z5,z6])],[(0,[z14,z185,z3,z4,z5,z1084]),(0,[z1,z2,z3,z4,z5,z197]),(0,[z241,z2,z3,z742,z5,z6])],[(0,[z734,z7,z3,z4,z5,z6]),(0,[z1004,z1,z3,z4,z5,z6]),(0,[z14,z1,z1176,z4,z5,z6]),(0,[z1,z2,z3,z967,z5,z6])],[(0,[z1,z3,z15,z110,z5,z6]),(0,[z1,z2,z81,z4,z5,z895])],[(0,[z1,z2,z3,z4,z5,z1177]),(0,[z1,z2,z3,z4,z5,z1178]),(0,[z1,z2,z3,z1179,z5,z6]),(0,[z366,z1,z3,z5,z87,z6])],[(0,[z1,z2,z3,z4,z5,z1084]),(0,[z1029,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1180])],[(0,[z1,z2,z3,z4,z5,z1181])]],
   [[],[(0,[z14,z1,z3,z98,z5,z6]),(0,[z14,z1,z3,z1159,z5,z6]),(0,[z1,z34,z3,z4,z5,z303]),(0,[z1,z1182,z3,z4,z5,z6]),(0,[z95,z3,z52,z4,z5,z6]),(0,[z1,z188,z3,z4,z544,z6])],[(0,[z2,z3,z4,z121,z5,z525]),(0,[z1,z2,z3,z4,z5,z1183])],[(0,[z41,z2,z3,z4,z404,z6]),(0,[z1,z2,z3,z1184,z5,z6]),(0,[z290,z1,z69,z4,z5,z6]),(0,[z14,z1,z162,z3,z5,z6]),(0,[z1185,z2,z3,z4,z5,z6]),(0,[z1,z3,z1186,z4,z5,z6]),(0,[z1,z21,z116,z22,z3,z6]),(0,[z1187,z1,z3,z4,z5,z6])],[(0,[z0,z734,z3,z4,z5,z6]),(0,[z1,z1188,z3,z4,z5,z6])],[(0,[z14,z1,z3,z4,z5,z42]),(1,[z1,z744,z4,z5,z6])],[(0,[z1,z102,z744,z4,z5,z6]),(0,[z1,z3,z15,z231,z5,z6]),(0,[z1,z2,z3,z203,z5,z275])],[(0,[z1,z1189,z3,z4,z5,z6]),(0,[z14,z1185,z3,z4,z5,z6]),(0,[z1,z1190,z3,z4,z5,z6])],[(0,[z566,z119,z3,z4,z5,z6]),(0,[z1,z1191,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1192]),(0,[z1,z2,z442,z48,z5,z6]),(0,[z1,z2,z3,z1193,z5,z6])],[(0,[z1,z2,z3,z1194,z5,z6]),(0,[z1,z2,z381,z4,z5,z6]),(0,[z2,z3,z4,z5,z297,z56]),(0,[z1,z3,z15,z4,z5,z802]),(0,[z1195,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1028])],[(0,[z2,z94,z4,z150,z159,z6]),(0,[z1,z2,z3,z438,z5,z6]),(1,[z1,z3,z750,z5,z6]),(0,[z637,z14,z1,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z838]),(0,[z1196,z1,z3,z4,z5,z6])],[(0,[z597,z2,z3,z24,z5,z6]),(0,[z1,z3,z15,z4,z5,z303]),(0,[z1,z2,z3,z5,z6,z1197]),(0,[z1198,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z1199,z5,z6]),(0,[z1,z1200,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1201,z5,z6]),(0,[z1,z2,z3,z501,z87,z6]),(0,[z1,z2,z3,z4,z6,z850])],[(0,[z119,z734,z3,z4,z5,z6]),(0,[z1,z3,z1202,z4,z5,z6]),(0,[z14,z1,z3,z74,z5,z6])],[(0,[z114,z267,z1,z3,z5,z6])],[(0,[z2,z3,z849,z121,z5,z6]),(0,[z1,z126,z3,z4,z5,z171])]],
   [[(0,[z2,z3,z38,z121,z5,z6]),(0,[z1,z2,z112,z53,z5,z6]),(0,[z114,z267,z1,z5,z49,z6])],[(0,[z1,z3,z1124,z74,z5,z6]),(0,[z1203,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z86])],[(0,[z1,z296,z3,z15,z5,z6]),(0,[z1,z461,z3,z4,z5,z436]),(0,[z1,z2,z3,z1204,z5,z6])],[(0,[z1205,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z939]),(0,[z179,z14,z1,z3,z5,z6]),(0,[z1,z3,z1206,z4,z5,z6]),(0,[z1,z3,z4,z871,z143,z6]),(0,[z1,z2,z81,z4,z5,z236])],[(0,[z815,z1,z3,z4,z5,z6]),(0,[z1,z503,z3,z4,z5,z436])],[(0,[z1,z3,z120,z529,z5,z6]),(0,[z1,z2,z3,z4,z5,z1207]),(0,[z14,z1,z3,z4,z1208,z6]),(0,[z1,z1209,z3,z4,z5,z6]),(0,[z1,z2,z3,z261,z87,z6])],[(0,[z1,z2,z3,z4,z5,z1210]),(0,[z1211,z2,z3,z4,z5,z6])],[(0,[z90,z374,z3,z4,z5,z115]),(0,[z1,z3,z876,z4,z5,z6])],[(0,[z1,z2,z66,z4,z153,z6])],[(0,[z43,z1,z2,z4,z159,z6])],[(0,[z1,z2,z3,z4,z1212,z6]),(0,[z1213,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z138,z5,z303])],[(0,[z253,z7,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z131])],[(0,[z1,z3,z15,z378,z5,z6]),(0,[z1214,z1,z2,z3,z4,z5]),(0,[z14,z1,z658,z3,z5,z6]),(0,[z206,z1,z2,z3,z5,z236]),(0,[z235,z824,z1,z3,z5,z6])],[(0,[z2,z3,z4,z798,z150,z6]),(0,[z1,z301,z3,z4,z5,z6]),(0,[z14,z95,z3,z80,z5,z6])],[(0,[z2,z3,z94,z4,z404,z6]),(0,[z1,z1215,z3,z4,z5,z6]),(0,[z1,z3,z1216,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z1217,z6]),(0,[z1,z3,z15,z5,z564,z6]),(0,[z1,z2,z1119,z4,z5,z6]),(0,[z1,z2,z112,z5,z712,z6]),(0,[z104,z1,z2,z3,z4,z200])],[(0,[z1,z2,z3,z4,z5,z1218])],[(0,[z1,z2,z3,z4,z5,z1219]),(0,[z14,z1,z3,z4,z5,z100]),(0,[z41,z14,z3,z4,z150,z6]),(0,[z1,z1220,z3,z4,z5,z6]),(0,[z206,z1,z3,z5,z35,z6]),(0,[z1,z2,z3,z4,z1221,z6]),(0,[z929,z2,z3,z4,z5,z36]),(0,[z1222,z2,z3,z4,z5,z6])],[(0,[z585,z7,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1223,z6]),(0,[z241,z2,z3,z4,z5,z795])],[(0,[z1,z2,z3,z4,z5,z1224]),(0,[z14,z1,z488,z3,z5,z6]),(0,[z1,z3,z4,z5,z6,z1225]),(0,[z14,z95,z3,z24,z5,z6]),(0,[z1,z2,z381,z191,z5,z6]),(0,[z84,z14,z1,z3,z5,z174]),(0,[z1,z2,z3,z1226,z5,z6]),(0,[z1,z346,z3,z4,z5,z6])],[(0,[z14,z90,z3,z121,z5,z6]),(0,[z82,z2,z3,z4,z5,z115])],[(0,[z1,z2,z3,z4,z5,z297]),(0,[z14,z1,z112,z48,z5,z6])],[(0,[z1,z2,z1227,z4,z5,z6]),(0,[z1228,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1229])],[(0,[z1,z2,z3,z1230,z5,z6]),(0,[z1,z2,z3,z529,z5,z525]),(0,[z513,z119,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1231]),(0,[z14,z1,z3,z121,z5,z6]),(0,[z169,z185,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1126,z6]),(0,[z1,z1232,z3,z4,z5,z6]),(0,[z1,z2,z3,z1233,z5,z6])],[(0,[z1,z2,z3,z4,z5,z776]),(0,[z14,z185,z3,z5,z87,z6])],[],[(0,[z1,z3,z15,z4,z404,z6]),(0,[z14,z645,z1,z3,z5,z6]),(0,[z144,z1,z3,z5,z118,z6]),(0,[z1234,z1,z2,z3,z4,z5])],[(0,[z185,z2,z3,z4,z5,z6]),(0,[z185,z7,z3,z4,z5,z6]),(0,[z2,z3,z24,z849,z5,z6]),(0,[z1,z34,z402,z4,z5,z6]),(0,[z14,z705,z1,z3,z5,z6]),(0,[z1,z3,z4,z750,z5,z6]),(0,[z1235,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z481,z5,z118]),(0,[z1,z3,z4,z1236,z5,z6]),(0,[z14,z1,z3,z5,z200,z6]),(0,[z361,z3,z15,z4,z5,z6]),(0,[z19,z1,z3,z4,z5,z666]),(0,[z84,z1,z2,z3,z110,z5])],[(0,[z14,z1,z3,z201,z5,z6]),(0,[z14,z399,z3,z4,z5,z6]),(0,[z1,z376,z2,z3,z5,z6]),(0,[z114,z1,z15,z5,z49,z6]),(0,[z1,z3,z4,z17,z871,z6])],[(0,[z1,z381,z15,z4,z5,z6]),(0,[z1,z3,z1237,z4,z5,z6]),(0,[z1,z2,z4,z5,z159,z197])]],
   [[(0,[z1,z2,z3,z588,z87,z6]),(0,[z1,z2,z3,z1238,z5,z6]),(0,[z1,z2,z382,z4,z153,z6]),(0,[z1,z1239,z3,z4,z5,z6])],[(0,[z1240,z1,z3,z4,z5,z6]),(0,[z2,z9,z402,z4,z5,z6]),(0,[z14,z1,z3,z208,z5,z6]),(0,[z1,z376,z3,z15,z5,z6]),(0,[z1,z3,z4,z5,z6,z1241]),(0,[z1,z1242,z3,z4,z5,z6])],[(0,[z1,z3,z120,z4,z5,z6])],[(0,[z1,z2,z3,z1243,z5,z6]),(0,[z225,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z1244,z5,z6]),(0,[z14,z1,z3,z5,z395,z6]),(0,[z1,z1245,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z792])],[(0,[z1,z2,z3,z4,z5,z1246]),(0,[z72,z2,z402,z4,z5,z6]),(0,[z366,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z46,z850])],[(0,[z1,z3,z368,z38,z5,z6]),(0,[z1,z3,z1247,z4,z5,z6]),(0,[z14,z1,z3,z4,z743,z6]),(0,[z43,z1,z259,z4,z159,z6])],[(0,[z185,z126,z3,z4,z5,z6]),(0,[z399,z2,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z1248,z5,z6]),(0,[z1,z3,z4,z5,z6,z838]),(0,[z1,z2,z48,z5,z712,z6]),(0,[z1,z3,z261,z377,z87,z6])],[(0,[z82,z962,z3,z4,z5,z6])],[(0,[z1,z1249,z3,z4,z5,z6]),(0,[z55,z2,z3,z4,z5,z776]),(0,[z114,z14,z1,z3,z5,z6]),(0,[z1,z2,z3,z74,z5,z197])],[(0,[z1,z1250,z3,z4,z5,z6]),(0,[z1,z3,z1251,z4,z5,z6]),(0,[z267,z1,z3,z121,z5,z6])],[(0,[z1,z2,z3,z4,z5,z983]),(0,[z1,z2,z3,z1252,z5,z6]),(0,[z1,z2,z3,z191,z5,z6]),(0,[z1,z1253,z3,z4,z5,z6]),(0,[z345,z2,z3,z4,z5,z297]),(0,[z1,z2,z1254,z4,z5,z6]),(0,[z14,z1,z3,z91,z5,z6]),(0,[z114,z14,z1,z5,z49,z6]),(0,[z14,z1,z3,z750,z5,z6]),(0,[z1,z188,z3,z17,z145,z6])],[(0,[z14,z1,z3,z321,z5,z6]),(0,[z14,z1,z3,z5,z1093,z6])],[(0,[z2,z3,z4,z5,z436,z56]),(0,[z14,z1,z373,z3,z5,z6]),(0,[z1,z3,z209,z4,z5,z113]),(0,[z1,z2,z3,z4,z5,z1255]),(0,[z1170,z1,z3,z110,z5,z6])],[]],
   [[(0,[z1256,z1,z3,z4,z5,z6]),(0,[z1,z1257,z2,z3,z5,z6])],[(0,[z1,z2,z402,z4,z150,z6]),(0,[z19,z1,z3,z4,z5,z706]),(0,[z474,z14,z1,z3,z5,z6]),(0,[z1258,z1,z3,z4,z5,z6]),(0,[z1,z1259,z3,z4,z5,z6])],[(0,[z14,z1,z3,z440,z5,z6]),(1,[z1,z2,z751,z3,z6])],[(0,[z1,z3,z4,z5,z6,z1260]),(0,[z386,z95,z3,z4,z5,z6]),(0,[z84,z399,z2,z3,z4,z5])],[],[(0,[z1,z2,z3,z4,z5,z525]),(0,[z14,z1,z3,z448,z5,z6]),(0,[z1,z2,z3,z4,z5,z1261]),(0,[z97,z1,z3,z121,z5,z6]),(0,[z14,z1,z3,z4,z5,z27]),(0,[z1,z162,z13,z4,z5,z6]),(0,[z1,z2,z751,z3,z87,z6])],[(0,[z1,z3,z15,z38,z5,z6]),(0,[z1,z2,z3,z4,z5,z1262]),(0,[z1,z2,z402,z138,z5,z6]),(0,[z114,z1,z2,z282,z5,z6]),(0,[z1,z2,z3,z4,z5,z1263])],[(0,[z1,z2,z3,z529,z5,z6]),(0,[z345,z1242,z3,z4,z5,z6])],[(0,[z14,z1,z375,z3,z5,z6])],[(0,[z14,z90,z3,z4,z5,z115]),(0,[z1195,z1,z3,z74,z5,z6]),(0,[z1,z2,z242,z4,z5,z60])],[(0,[z90,z2,z3,z4,z5,z297]),(0,[z41,z2,z3,z138,z150,z6]),(0,[z206,z1,z3,z5,z143,z6])],[(0,[z14,z1,z3,z4,z272,z6]),(0,[z14,z1,z3,z4,z5,z275]),(0,[z16,z1,z3,z4,z143,z6]),(0,[z84,z1,z2,z3,z5,z792])],[(0,[z1,z3,z1159,z121,z5,z6]),(0,[z1,z2,z3,z1264,z5,z6]),(0,[z284,z259,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1265,z5,z6]),(0,[z241,z2,z3,z4,z404,z6]),(0,[z144,z95,z3,z4,z5,z6]),(0,[z90,z2,z3,z4,z5,z776]),(0,[z1,z624,z3,z4,z5,z6])],[(0,[z14,z1,z3,z280,z5,z6]),(0,[z1,z2,z4,z5,z6,z1266]),(0,[z1,z2,z3,z191,z5,z100]),(0,[z1,z1267,z3,z4,z5,z6])],[(0,[z794,z2,z3,z4,z5,z6]),(0,[z1,z2,z1176,z4,z5,z6])]],
   [[(0,[z14,z1,z3,z298,z5,z6]),(0,[z1268,z2,z3,z4,z5,z6])],[(0,[z2,z3,z910,z4,z5,z6]),(0,[z14,z1,z3,z5,z470,z6])],[(0,[z84,z1,z2,z3,z5,z364]),(0,[z95,z3,z4,z5,z478,z6]),(0,[z241,z856,z3,z4,z5,z6])],[(0,[z0,z144,z3,z4,z5,z6]),(0,[z93,z2,z472,z4,z5,z6]),(0,[z14,z1,z3,z5,z476,z6]),(0,[z43,z1,z15,z4,z159,z6]),(0,[z334,z346,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1269]),(0,[z602,z1,z4,z5,z264,z6])],[(0,[z23,z2,z3,z4,z5,z525]),(1,[z2,z94,z4,z404,z6]),(0,[z95,z188,z3,z4,z5,z6]),(0,[z19,z1,z3,z5,z154,z113]),(0,[z1,z2,z3,z317,z87,z6]),(0,[z1,z2,z3,z4,z5,z895]),(0,[z1,z3,z1117,z110,z5,z6])],[(0,[z474,z1,z2,z3,z121,z5]),(0,[z1,z188,z3,z4,z527,z6])],[(0,[z1,z3,z903,z4,z5,z6]),(0,[z1,z3,z1270,z4,z5,z6]),(0,[z14,z1,z3,z110,z5,z6]),(0,[z1,z2,z3,z4,z5,z1271]),(0,[z43,z1,z2,z4,z760,z6])],[(0,[z1,z2,z3,z4,z1272,z6]),(0,[z241,z2,z402,z4,z5,z6]),(0,[z90,z3,z15,z4,z5,z115]),(0,[z31,z1,z52,z4,z5,z12]),(0,[z2,z3,z4,z5,z1273,z6]),(0,[z1,z81,z15,z4,z5,z236]),(0,[z1274,z1,z3,z4,z5,z6])],[(0,[z84,z14,z1,z3,z5,z56]),(0,[z1,z2,z3,z4,z5,z42]),(0,[z14,z361,z2,z3,z5,z6]),(0,[z43,z1,z2,z74,z159,z6])],[(0,[z1,z2,z3,z4,z5,z1275]),(0,[z1,z1276,z3,z4,z5,z6])],[(0,[z1,z1277,z3,z4,z5,z6])],[(0,[z363,z1,z3,z4,z143,z6]),(0,[z1,z2,z1278,z4,z5,z6])],[(0,[z1279,z1,z3,z4,z5,z6]),(0,[z23,z2,z3,z438,z5,z6]),(0,[z443,z1,z2,z3,z5,z6]),(0,[z1,z3,z51,z274,z5,z6]),(0,[z1,z2,z3,z4,z871,z6])],[(0,[z1,z2,z381,z4,z5,z100]),(0,[z1,z301,z3,z74,z5,z6])],[(0,[z1,z2,z3,z1280,z5,z6]),(0,[z14,z1268,z3,z4,z5,z6]),(0,[z291,z1,z3,z4,z5,z113])]],
   [[(0,[z443,z1,z3,z15,z5,z6]),(0,[z14,z185,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1281,z5,z6]),(0,[z1,z2,z1282,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1283]),(0,[z1284,z2,z3,z4,z5,z6]),(0,[z43,z14,z1,z4,z159,z6]),(0,[z14,z1,z3,z231,z5,z6]),(0,[z1,z2,z3,z74,z5,z6])],[(0,[z730,z1,z3,z4,z5,z6])],[(0,[z345,z2,z3,z438,z5,z6]),(0,[z1,z3,z15,z277,z5,z6]),(0,[z14,z1,z242,z4,z5,z6]),(0,[z1,z1285,z3,z4,z5,z6]),(0,[z1,z1286,z3,z4,z5,z6]),(1,[z284,z2,z4,z159,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1287])],[(0,[z155,z1,z2,z3,z4,z60]),(0,[z14,z1,z21,z3,z478,z6])],[(0,[z1,z1288,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z303])],[(0,[z1,z1289,z2,z3,z5,z6]),(0,[z114,z14,z1,z69,z5,z6]),(0,[z1,z106,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z871,z6])],[(0,[z1,z2,z3,z1290,z5,z6])],[(0,[z1,z2,z3,z4,z1208,z6]),(0,[z284,z3,z15,z4,z5,z6]),(0,[z1291,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1292]),(0,[z227,z2,z3,z4,z5,z197]),(0,[z1293,z2,z3,z4,z5,z6]),(0,[z1,z3,z57,z5,z118,z394])],[(0,[z1294,z1,z3,z4,z5,z6]),(0,[z84,z14,z1,z3,z50,z5]),(0,[z1,z3,z4,z17,z238,z6]),(0,[z399,z2,z3,z4,z5,z46]),(0,[z1,z346,z3,z110,z5,z6])],[(0,[z1,z2,z1295,z4,z5,z6])],[(0,[z1,z1296,z3,z4,z5,z6])],[(0,[z1,z126,z3,z4,z5,z6]),(0,[z93,z2,z94,z4,z5,z6]),(0,[z1,z2,z1132,z4,z5,z6])],[]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 502) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 502).take 509) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1011).take 297) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1308)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [502, 509, 297] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 144).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 144).take 144).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 288).take 148).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 436).take 76).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [144, 144, 148, 76] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
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

end PEqualNP.Outside.L_meta_37783

theorem PEqualNP.Outside.L_meta_37783 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071598 * 2 ^ 32 + 4209568392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071598 * 2 ^ 32 + 4209568392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37783.solve