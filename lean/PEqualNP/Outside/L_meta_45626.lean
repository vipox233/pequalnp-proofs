import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45626

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
  Nat.testBit (4008241376 * 2 ^ 32 + 4001949824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x030d8b8621ac36c0#64 ++ 0x080c362e1886b0db#64 ++ 0x471f9f8e63fc7fde#64 ++ 0xfd1c7e7e398ff1ff#64 : BitVec 256),
   (0x1862a5b08c558b41#64 ++ 0x00618a96c231562d#64 ++ 0xb8e3e7f19c7f8fef#64 ++ 0xfee38f9fc671fe3f#64 : BitVec 256),
   (0xc0b4505be062d182#64 ++ 0x3302d1416f818b46#64 ++ 0xc0fc78ffe063f1f7#64 ++ 0x7b03f1e3ff818fc7#64 : BitVec 256),
   (0xed007e0156836c10#64 ++ 0x87b401f8055a0db0#64 ++ 0xff007f01ff83fe3b#64 ++ 0xbffc01fc07fe0ff8#64 : BitVec 256),
   (0xf6ff0001fb780008#64 ++ 0x57dbfc0007ede000#64 ++ 0xffff8001fffc0003#64 ++ 0xd7fffe0007fff000#64 : BitVec 256),
   (0xffdbffec00000004#64 ++ 0xe3ff6fffb0000000#64 ++ 0xfffffffe00000003#64 ++ 0xe3fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.and, [6, 3]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x030d8b8621ac36c0 0x080c362e1886b0db 0x471f9f8e63fc7fde 0xfd1c7e7e398ff1ff

def z1 : W := mkw 0x09002e0004812c00 0x002400b8001204b0 0xff007f01ff83fe3b 0xbffc01fc07fe0ff8

def z2 : W := mkw 0x1862a5b08c558b41 0x00618a96c231562d 0xb8e3e7f19c7f8fef 0xfee38f9fc671fe3f

def z3 : W := mkw 0x1b4bafa40d9d2e41 0x086d2ebe903674b9 0x3f0387001f9c0e08 0x84fc0e1c007e7038

def z4 : W := mkw 0xf6ff0001fb780008 0x57dbfc0007ede000 0xffff8001fffc0003 0xd7fffe0007fff000

def z5 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0xfffffffe00000003 0xe3fffffff8000000

def z6 : W := mkw 0x1a4ba5a400000000 0x00692e9690000000 0xb8ffe7fe00000003 0xe2e3ff9ff8000000

def z7 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z8 : W := mkw 0xed007e0156836c10 0x87b401f8055a0db0 0xff007f01ff83fe3b 0xbffc01fc07fe0ff8

def z9 : W := mkw 0x374b8b841b9c2648 0x4cdd2e2e106e7099 0x3f0387001f9c0e08 0x84fc0e1c007e7038

def z10 : W := mkw 0xf6ff505bfb7ad18a 0x77dbfd416fedeb46 0xfffff8fffffff1f7 0xffffffe3ffffffc7

def z11 : W := mkw 0x000000001b180008 0x04000000006c6000 0x000000001f9c0000 0x04000000007e7000

def z12 : W := mkw 0xc990ffec00000004 0xa32643ffb0000000 0xc0fc7ffe00000003 0x6303f1fff8000000

def z13 : W := mkw 0x00240013e062d182 0x100090004f818b46 0x00000001e003f030 0x0000000007800fc0

def z14 : W := mkw 0x1b4bafa400000000 0x006d2ebe90000000 0xfffffffe00000003 0xe3fffffff8000000

def z15 : W := mkw 0x36fb00009b580008 0x54dbec00026d6000 0x3fe380001f9c0000 0x84ff8e00007e7000

def z16 : W := mkw 0x1062000088500000 0x0041880002214000 0xb8e380019c7c0003 0xd6e38e000671f000

def z17 : W := mkw 0xfeffa5b1ff7d8b49 0x57fbfe96c7fdf62d 0xffffe7f1ffff8fef 0xffffff9fc7fffe3f

def z18 : W := mkw 0x364b00001b180008 0x44d92c00006c6000 0x3f0380001f9c0000 0x84fc0e00007e7000

def z19 : W := mkw 0xc090504800000000 0x2302414120000000 0xc0fc78fe00000003 0x6303f1e3f8000000

def z20 : W := mkw 0xed907e4956836c10 0xa7b641f9255a0db0 0xfffc7fffff83fe3b 0xfffff1fffffe0ff8

def z21 : W := mkw 0xffdb7e6d56836c14 0xe7ff6df9b55a0db0 0xfffc7f7fff83fe3b 0xbffff1fdfffe0ff8

def z22 : W := mkw 0x124b81a400000000 0x00492e0690000000 0x00ff80fe00000000 0x4003fe03f8000000

def z23 : W := mkw 0x126f81b6a97c93c1 0x0849be06daa5f24f 0x00ff80fe007c01c4 0x4003fe03f801f007

def z24 : W := mkw 0x01000a0000802400 0x0004002800020090 0x47001f0063807e1a 0xbd1c007c018e01f8

def z25 : W := mkw 0x12db81ec00000004 0x604b6e07b0000000 0x00ff80fe00000000 0x4003fe03f8000000

def z26 : W := mkw 0xef0dff8777af7ed0 0x8fbc37fe1ddebdfb 0xff1fff8fffffffff 0xfffc7ffe3fffffff

def z27 : W := mkw 0x020d8186212c12c0 0x080836061884b04b 0x001f808e007c01c4 0x40007e023801f007

def z28 : W := mkw 0x00240013fa72d18a 0x140090004fe9cb46 0x00000001fc63f1f4 0x1800000007f18fc7

def z29 : W := mkw 0x2d002e0016812c10 0x84b400b8005a04b0 0x3f0007001f800e08 0x84fc001c007e0038

def z30 : W := mkw 0xedb47e5bf6e3fd92 0xb7b6d1f96fdb8ff6 0xfffc7fffffe3ffff 0xfffff1ffffff8fff

def z31 : W := mkw 0xffdbffed56836c14 0xe7ff6fffb55a0db0 0xffffffffff83fe3b 0xfffffffffffe0ff8

def z32 : W := mkw 0xc3b9dbddc1cee742 0x3b0ee76f77073b9d 0x87e3e771839f8e29 0x861f8f9dc60e7e38

def z33 : W := mkw 0x1adba5ec00000004 0x606b6e97b0000000 0x38ff87fe00000000 0xc0e3fe1ff8000000

def z34 : W := mkw 0x00240013e872d182 0x100090004fa1cb46 0x00000001fc7ff1f4 0x1c00000007f1ffc7

def z35 : W := mkw 0xffdbffec1b9c264c 0xefff6fffb06e7099 0xfffffffe1f9c0e0b 0xe7fffffff87e7038

def z36 : W := mkw 0xc190dbcc00000000 0x2306436f30000000 0xc0fc7ffe00000003 0x6303f1fff8000000

def z37 : W := mkw 0x00240013e062d182 0x100090004f818b46 0x00000001e063f1f4 0x1800000007818fc7

def z38 : W := mkw 0xf6ff005bfb78918a 0x77dbfc016fede246 0xffff80fffffc01c7 0xd7fffe03fffff007

def z39 : W := mkw 0x00b4005aa0609182 0x3002d0016a818246 0x00fc00fe006001c4 0x4003f003f8018007

def z40 : W := mkw 0x366f0001fb780008 0x54d9bc0007ede000 0x3f038001fffc0000 0x94fc0e0007fff000

def z41 : W := mkw 0x2d242e13f6e3fd92 0x94b490b84fdb8ff6 0x3f000701ffe3fffc 0x9cfc001c07ff8fff

def z42 : W := mkw 0x00240012a0609180 0x000090004a818246 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z43 : W := mkw 0xed907e0156836c18 0xd7b641f8055a0db0 0xff007f01ff83fe3b 0xbffc01fc07fe0ff8

def z44 : W := mkw 0x364f00003b380008 0x44d93c0000ece000 0x7f1f80007ffc0002 0xd5fc7e0001fff000

def z45 : W := mkw 0x366b00009b580008 0x44d9ac00026d6000 0x3fe380001ffc0000 0xc4ff8e00007ff000

def z46 : W := mkw 0x0000505a0002d182 0x2000014168000b46 0x000078fe0003f1f4 0x280001e3f8000fc7

def z47 : W := mkw 0xed90ffed56836c14 0xa7b643ffb55a0db0 0xfffc7fffff83fe3b 0xfffff1fffffe0ff8

def z48 : W := mkw 0xf562dbb1dad6e751 0x87d58b6ec76b5b9d 0x47e398f063fc71d4 0x411f8e63c18ff1c7

def z49 : W := mkw 0xf6ff505be062d182 0x73dbfd416f818b46 0xfffff8ffe063f1f7 0xfbffffe3ff818fc7

def z50 : W := mkw 0x366f0001fb780008 0x54d9bc0007ede000 0xbfe38001fffc0003 0xd6ff8e0007fff000

def z51 : W := mkw 0x00240013ffffffd1 0x0c0090004fffffff 0x00000001fffffffc 0x1c00000007ffffff

def z52 : W := mkw 0x13db8bec018c2644 0x684f6e2fb0063099 0x07ff87fe039c0e08 0xc41ffe1ff80e7038

def z53 : W := mkw 0xed907e4956836c10 0xa7b641f9255a0db0 0xffe07f71ff83fe3b 0xbfff81fdc7fe0ff8

def z54 : W := mkw 0xf6dbd1ec00000004 0xe3db6f47b0000000 0x00ff80fe00000000 0x4003fe03f8000000

def z55 : W := mkw 0xc0205011c042c100 0x0300814047010b04 0xc0e078f1e063f1f7 0x7b0381e3c7818fc7

def z56 : W := mkw 0xf6ff004dfb78000c 0x77dbfc0137ede000 0xffff800ffffc0003 0xd7fffe003ffff000

def z57 : W := mkw 0xf6ff5001fb7a4008 0x57dbfd4007ede900 0xfffff801fffff033 0xffffffe007ffffc0

def z58 : W := mkw 0xfedbf5e800000000 0x63fb6fd7a0000000 0xfffffffe00000003 0xe3fffffff8000000

def z59 : W := mkw 0x0024505be062d182 0x300091416f818b46 0x000078ffe063f1f4 0x380001e3ff818fc7

def z60 : W := mkw 0x0090004800000000 0x2002400120000000 0x00fc00fe00000000 0x4003f003f8000000

def z61 : W := mkw 0xec00740156034810 0x87b001d005580d20 0xb80060019c038021 0x02e0018006700e00

def z62 : W := mkw 0xf6db000000000000 0x43db6c0000000000 0xffff800000000003 0xc3fffe0000000000

def z63 : W := mkw 0xffdbffec1b18000c 0xe7ff6fffb06c6000 0xfffffffe1f9c0003 0xe7fffffff87e7000

def z64 : W := mkw 0x2d007e0156836c10 0x84b401f8055a0db0 0x3f007f01ff83fe38 0xbcfc01fc07fe0ff8

def z65 : W := mkw 0x0900afb60485bfc1 0x082402bed81216ff 0x00007ffe0003fffc 0x280001fff8000fff

def z66 : W := mkw 0x1b4bafa40d9d2e41 0x086d2ebe903674b9 0xfffffffe1f9c0e0b 0xe7fffffff87e7038

def z67 : W := mkw 0xfedbf5ed56034814 0xe7fb6fd7b5580d20 0xb8ffe0ff9c038021 0x42e3ff83fe700e00

def z68 : W := mkw 0x124f000029380000 0x00493c0000a4e000 0x7f1f80007ffc0002 0xd5fc7e0001fff000

def z69 : W := mkw 0x002000108c558b41 0x000080004231562d 0x000000019c7f8fec 0x1c0000000671fe3f

def z70 : W := mkw 0x00240012ac759bc3 0x100090004ab1d66f 0x000000019c7f8fec 0x1c0000000671fe3f

def z71 : W := mkw 0xf64b00015b180008 0x47d92c00056c6000 0xff038001ff9c0003 0x97fc0e0007fe7000

def z72 : W := mkw 0x0000000156836c10 0x04000000055a0db0 0x00000001ff83fe38 0x1c00000007fe0ff8

def z73 : W := mkw 0x37db8bec00000004 0xe0df6e2fb0000000 0x07ff80fe00000000 0x401ffe03f8000000

def z74 : W := mkw 0xc0245013e062d182 0x130091404f818b46 0xc0007801e063f1f7 0x3b0001e007818fc7

def z75 : W := mkw 0xe4b4505bf262d182 0x3792d1416fc98b46 0xfffc78ffffe3f1f7 0xfffff1e3ffff8fc7

def z76 : W := mkw 0xffff7e01fffb6c18 0xd7fffdf807ffedb0 0xffffff01fffffe3b 0xfffffffc07fffff8

def z77 : W := mkw 0x00240013e4e3fd92 0x100090004f938ff6 0x00000001e063fffc 0x1800000007818fff

def z78 : W := mkw 0x0800240004010800 0x0020009000100420 0xb80067019c038e2b 0xbee0019c06700e38

def z79 : W := mkw 0x1962afb08cd5af41 0x00658abec23356bd 0xffe3fff1ffffffff 0xffff8fffc7ffffff

def z80 : W := mkw 0xc094505a2022d182 0x2302514168808b46 0xc0fc78fe6063f1f7 0x7b03f1e3f9818fc7

def z81 : W := mkw 0x0020001080408100 0x0000800042010204 0x80e060f1806381e7 0x7a038183c6018e07

def z82 : W := mkw 0xd8f6f5fbec77dbc3 0x3363dbd7efb1df6f 0xf8fffffffc7fffff 0xffe3fffffff1ffff

def z83 : W := mkw 0x1062819088548340 0x00418a064221520d 0xb8e3e7f19c7f8fef 0xfee38f9fc671fe3f

def z84 : W := mkw 0x366f0013fb7ad18a 0x54d9bc004fedeb46 0x3f038001fffff1f4 0x9cfc0e0007ffffc7

def z85 : W := mkw 0x00240013fb7ad18a 0x140090004fedeb46 0x00000001fffff1f4 0x1c00000007ffffc7

def z86 : W := mkw 0x3f4bafa400000004 0xc0fd2ebe90000000 0x3f03870000000000 0x80fc0e1c00000000

def z87 : W := mkw 0x00b4505aa062d182 0x3002d1416a818b46 0x00fc78fe0063f1f4 0x6803f1e3f8018fc7

def z88 : W := mkw 0xf6db00001b180008 0x47db6c00006c6000 0xffff80001f9c0003 0xc7fffe00007e7000

def z89 : W := mkw 0x10d2006800000004 0x60434801a0000000 0x00fc00fe00000000 0x4003f003f8000000

def z90 : W := mkw 0x3fdbafec00000004 0xe0ff6ebfb0000000 0x3fff87fe00000000 0xc0fffe1ff8000000

def z91 : W := mkw 0x0000000140024000 0x0000000005000900 0x00000001e003f030 0x1800000007800fc0

def z92 : W := mkw 0xed247e13f6e3fd92 0x97b491f84fdb8ff6 0xff007f01ffe3ffff 0xbffc01fc07ff8fff

def z93 : W := mkw 0xffdbffed52000004 0xe7ff6fffb5480000 0xffffffffff800003 0xf7fffffffffe0000

def z94 : W := mkw 0x1bdbffec00000004 0xe06f6fffb0000000 0x00fffffe00000000 0x6003fffff8000000

def z95 : W := mkw 0xc090d1c800040240 0x2302434720001009 0xc0fffffe007c0fcf 0xff03fffff801f03f

def z96 : W := mkw 0xed907e4956836c14 0xe7b641f9255a0db0 0xff007f01ff83fe3b 0xbffc01fc07fe0ff8

def z97 : W := mkw 0x00240013e1eef7c2 0x180090004f87bbdf 0x00000001e3fffffc 0x1c000000078fffff

def z98 : W := mkw 0xf6df00003b380008 0x47db7c0000ece000 0xffff80007ffc0003 0xd7fffe0001fff000

def z99 : W := mkw 0x00240013edffffc3 0x180090004fb7ffff 0x00000001fffffffc 0x1c00000007ffffff

def z100 : W := mkw 0x00240012ad7d9bc1 0x080090004ab5f66f 0x000000019c7f8fec 0x1c0000000671fe3f

def z101 : W := mkw 0x364b00001b180008 0x44d92c00006c6000 0x7f1f80001f9c0002 0xc5fc7e00007e7000

def z102 : W := mkw 0xf6ff0003fb781088 0x57dbfc000fede042 0xffff988ffffc71d7 0xfffffe623ffff1c7

def z103 : W := mkw 0xf6ff005bfb78918a 0x77dbfc016fede246 0xffff98fffffc71d7 0xfffffe63fffff1c7

def z104 : W := mkw 0xc000500140024000 0x0300014005000900 0xc0007801e003f033 0x3b0001e007800fc0

def z105 : W := mkw 0xf6fb0001db580008 0x57dbec00076d6000 0xbfe380019f9c0001 0x86ff8e00067e7000

def z106 : W := mkw 0xf66b0001db580008 0x47d9ac00076d6000 0xffe38001fffc0003 0xd7ff8e0007fff000

def z107 : W := mkw 0x09007e0004836c10 0x802401f800120db0 0x00007f000003fe38 0x280001fc00000ff8

def z108 : W := mkw 0x12ff0000a9780008 0x504bfc0002a5e000 0x00ff8000007c0000 0x4003fe000001f000

def z109 : W := mkw 0xffdbffec018c2644 0xebff6fffb0063099 0xfffffffe039c0e0b 0xe7fffffff80e7038

def z110 : W := mkw 0xee0df587772f5ad0 0x8fb837d61ddcbd6b 0xb81fe08f9c7f81e5 0x42e07f823e71fe07

def z111 : W := mkw 0x0900ff8604877ed0 0x882403fe18121dfb 0x00007f8e0003fffc 0x280001fe38000fff

def z112 : W := mkw 0xc890746800000004 0xa32241d1a0000000 0xc0fc78fe00000003 0x6303f1e3f8000000

def z113 : W := mkw 0x00240013ff7fdbcb 0x140090004ffdff6f 0x00000001fffffffc 0x1c00000007ffffff

def z114 : W := mkw 0x1842a5a000000000 0x00610a9680000000 0xb8e3e7f000000003 0xe2e38f9fc0000000

def z115 : W := mkw 0xfffbfffc8c558b45 0xe3ffeffff231562d 0xffffffff9c7f8fef 0xfffffffffe71fe3f

def z116 : W := mkw 0x2d002e0156836c10 0x84b400b8055a0db0 0x3f000701ff83fe38 0x9cfc001c07fe0ff8

def z117 : W := mkw 0xd2dbd1ed40024004 0x634b6f47b5000900 0xc0fff8ffe003f033 0x7b03ffe3ff800fc0

def z118 : W := mkw 0xe7995a4d52826414 0xe79e6569354a0990 0xc7fc78ffe383f033 0x7b1ff1e3ff8e0fc0

def z119 : W := mkw 0xf6ff0001fb780008 0x57dbfc0007ede000 0xffffe0f1fffc0003 0xf7ffff83c7fff000

def z120 : W := mkw 0x00240012a0609182 0x100090004a818246 0x00000000006001c4 0x0000000000018007

def z121 : W := mkw 0x0900fffc0487ef55 0xa02403fff0121fbd 0x00007ffe0003fffc 0x280001fff8000fff

def z122 : W := mkw 0x106281b088548341 0x00418a06c221520d 0x00e380f0007c01c4 0x40038e03c001f007

def z123 : W := mkw 0xe5005a0152826410 0x87940168054a0990 0x4700180063807010 0x011c0060018e01c0

def z124 : W := mkw 0xfcf27479de53c915 0xe7f3c9d1e7794f24 0xb8e060719c038021 0x02e38181c6700e00

def z125 : W := mkw 0xffdbffed56876e54 0xe7ff6fffb55a1db9 0xffffffffffffffff 0xffffffffffffffff

def z126 : W := mkw 0xfedba5ec00000004 0x63fb6e97b0000000 0xffffe7fe00000003 0xe3ffff9ff8000000

def z127 : W := mkw 0xf64b00001b180008 0x47d92c00006c6000 0xff0380001f9c0003 0x87fc0e00007e7000

def z128 : W := mkw 0x00240012a1ecb7c0 0x080090004a87b2df 0x00000001e3fffffc 0x1c000000078fffff

def z129 : W := mkw 0xed907e4800000000 0xa3b641f920000000 0xfffc7ffe00000003 0xe3fff1fff8000000

def z130 : W := mkw 0xffdbffec12000004 0xe7ff6fffb0480000 0xfffffffe1f800003 0xe7fffffff87e0000

def z131 : W := mkw 0xf6ff0013fb7ad18a 0x57dbfc004fedeb46 0xffff8001fffff1f7 0xdffffe0007ffffc7

def z132 : W := mkw 0xffdbffec018c2644 0xebff6fffb0063099 0xfffffffe03fc0fcf 0xfffffffff80ff03f

def z133 : W := mkw 0xed907e4816812c10 0xa7b641f9205a04b0 0xfffc7ffe1f800e0b 0xe7fff1fff87e0038

def z134 : W := mkw 0xf6db004800000000 0x63db6c0120000000 0xffff80fe00000003 0xc3fffe03f8000000

def z135 : W := mkw 0x0209818400000000 0x0008260610000000 0x001f808e00000000 0x40007e0238000000

def z136 : W := mkw 0x13df8bee21ac36c4 0x684f7e2fb886b0db 0x47ff9ffe63fc7fde 0xfd1ffe7ff98ff1ff

def z137 : W := mkw 0x00240013ec73d983 0x100090004fb1cf66 0x00000001fc63f1f4 0x1800000007f18fc7

def z138 : W := mkw 0xfedbf5ec00000004 0xe3fb6fd7b0000000 0xb8ffe0fe00000001 0x42e3ff83f8000000

def z139 : W := mkw 0x0900afb00485af51 0x802402bec01216bd 0x000067f000038fec 0x2800019fc0000e3f

def z140 : W := mkw 0xc090504800000000 0x2302414120000000 0x40fc18fe00000000 0x4103f063f8000000

def z141 : W := mkw 0x364b00001b180008 0x44d92c00006c6000 0xbfe380001f9c0003 0xc6ff8e00007e7000

def z142 : W := mkw 0xc090505a0002d182 0x2302414168000b46 0xc0fc78fe0003f1f7 0x6b03f1e3f8000fc7

def z143 : W := mkw 0xe79d5a4b73aa749a 0xf79e75692dcea9d2 0x471c180e63807010 0x011c7060398e01c0

def z144 : W := mkw 0xdbdbffec00000004 0xe36f6fffb0000000 0xc0fffffe00000003 0x6303fffff8000000

def z145 : W := mkw 0xffdbffed44836c14 0xe3ff6fffb5120db0 0xffffffffe003fe3b 0xfbffffffff800ff8

def z146 : W := mkw 0xc0b40001e0600000 0x1302d00007818000 0xc0fc0001e0600003 0x5303f00007818000

def z147 : W := mkw 0x01000a0000802400 0x0004002800020090 0x471c1f8e63807e1a 0xfd1c707e398e01f8

def z148 : W := mkw 0x00b4505aa062d182 0x3002d1416a818b46 0x80fc78ff8063f1f7 0x7a03f1e3fe018fc7

def z149 : W := mkw 0xc090504940024000 0x2302414125000900 0xc0fc78ffe003f033 0x7b03f1e3ff800fc0

def z150 : W := mkw 0xed007e0156836c10 0x87b401f8055a0db0 0xff007f01ff83fe39 0x2bfc01fc07fe0ff8

def z151 : W := mkw 0xec247413f663d992 0x97b091d04fd98f66 0xb8006001fc63f1f5 0x1ae0018007f18fc7

def z152 : W := mkw 0x03098b8400040240 0x000c262e10001009 0x471f9f8e007c0fce 0xfd1c7e7e3801f03f

def z153 : W := mkw 0xffdfffee21ac36c4 0xebff7fffb886b0db 0xfffffffe63fc7fdf 0xfffffffff98ff1ff

def z154 : W := mkw 0xd8d2f5e800000000 0x23634bd7a0000000 0xf8fffffe00000003 0xe3e3fffff8000000

def z155 : W := mkw 0x0000000000000000 0x0000000000000000 0x80e060f000000003 0x62038183c0000000

def z156 : W := mkw 0xc090504956836c10 0x27024141255a0db0 0xc0fc78ffff83fe3b 0x7f03f1e3fffe0ff8

def z157 : W := mkw 0x1842a5a004050a40 0x00610a9680101429 0xb8e3e7f19c7f8fef 0xfee38f9fc671fe3f

def z158 : W := mkw 0x36db00001b180008 0x44db6c00006c6000 0x3fff80001f9c0000 0xc4fffe00007e7000

def z159 : W := mkw 0x0900afb40485af41 0x082402bed01216bd 0x000067f000038fec 0x2800019fc0000e3f

def z160 : W := mkw 0xc094504b60225082 0x330251412d808942 0x401c180e60007010 0x01007060398001c0

def z161 : W := mkw 0x3d42afa01e952e51 0x84f50abe807a54b9 0x3f0387001f9c0e08 0x84fc0e1c007e7038

def z162 : W := mkw 0x00240012a0609180 0x000090004a818246 0x00000001e063f1f4 0x1800000007818fc7

def z163 : W := mkw 0x03098b8400000000 0x000c262e10000000 0x471f9f8e00000002 0xe11c7e7e38000000

def z164 : W := mkw 0xc39ddbce21ac36c0 0x2b0e776f3886b0db 0xc7fffffe63fc7fdf 0xff1ffffff98ff1ff

def z165 : W := mkw 0xed007e0000000000 0x83b401f800000000 0xff007f0000000003 0xa3fc01fc00000000

def z166 : W := mkw 0xc0b4505bfb7ad18a 0x3702d1416fedeb46 0xc0fc78fffffff1f7 0x7f03f1e3ffffffc7

def z167 : W := mkw 0xe69d000173280008 0x579a740005cca000 0x471c000063800000 0x011c7000018e0000

def z168 : W := mkw 0xee9da5b1772d8b49 0x57ba7696c5dcb62d 0x471c67f063838fec 0x291c719fc18e0e3f

def z169 : W := mkw 0x00240012a16c93c2 0x180090004a85b24f 0x00000000007c01c4 0x000000000001f007

def z170 : W := mkw 0xf66f0001fb780008 0x57d9bc0007ede000 0xff038001fffc0003 0x97fc0e0007fff000

def z171 : W := mkw 0xffff7e5bfffbfd9a 0xf7fffdf96fffeff6 0xffffffffffffffff 0xffffffffffffffff

def z172 : W := mkw 0x0900fffe0485bfc5 0xa82403fff81216ff 0x00007ffe0003fffc 0x280001fff8000fff

def z173 : W := mkw 0x0900ffee04877ed4 0xa82403ffb8121dfb 0x00007ffe0003fffc 0x280001fff8000fff

def z174 : W := mkw 0x00240013e876d3c3 0x100090004fa1db4f 0x00000001e07ff1f4 0x180000000781ffc7

def z175 : W := mkw 0xf6ff5049fb780008 0x77dbfd4127ede000 0xffffe071fffc0003 0xd7ffff81c7fff000

def z176 : W := mkw 0xf6db81ec00000004 0x63db6e07b0000000 0xb8ff80fe00000001 0x42e3fe03f8000000

def z177 : W := mkw 0xed247e13f7efffd2 0x9fb491f84fdfbfff 0xff007f01ffffffff 0xbffc01fc07ffffff

def z178 : W := mkw 0xf6ff505bfb7ad18a 0x77dbfd416fedeb46 0xffffe071fffff1f7 0xdfffff81c7ffffc7

def z179 : W := mkw 0xe79d5a4f73aa748a 0x7f9e75693dcea9d2 0x471c180e63807010 0x011c7060398e01c0

def z180 : W := mkw 0x000081ec00000004 0x20000207b0000000 0x000000fe00000000 0x00000003f8000000

def z181 : W := mkw 0xe4240001fb780008 0x1790900007ede000 0xff000001fffc0003 0x97fc000007fff000

def z182 : W := mkw 0x09007e0004836c10 0x802401f800120db0 0xff007f01ff83fe3b 0xbffc01fc07fe0ff8

def z183 : W := mkw 0xffdbffec1308000c 0xe7ff6fffb04c2000 0xfffffffe03800003 0xe3fffffff80e0000

def z184 : W := mkw 0x1adba5ec00000004 0x606b6e97b0000000 0xb8ffe7fe00000003 0xe2e3ff9ff8000000

def z185 : W := mkw 0xe400000152000000 0x0790000005480000 0xff000001ff800003 0x97fc000007fe0000

def z186 : W := mkw 0xfd627e01ded36c10 0x87f589f8077b4db0 0xffe3ff01fffffe3b 0xffff8ffc07fffff8

def z187 : W := mkw 0xffffffedfb78000c 0xf7ffffffb7ede000 0xfffffffffffc0003 0xf7fffffffffff000

def z188 : W := mkw 0x12ff81eca978000c 0x704bfe07b2a5e000 0x00ff80fe007c0000 0x4003fe03f801f000

def z189 : W := mkw 0x126f0000a9780000 0x0049bc0002a5e000 0xffff8001fffc0003 0xd7fffe0007fff000

def z190 : W := mkw 0x13db8bec00802404 0x604f6e2fb0020090 0x47ff9ffe63807e1a 0xfd1ffe7ff98e01f8

def z191 : W := mkw 0x0004000221ac36c0 0x080010000886b0db 0x0000000063fc7fdc 0x1c000000018ff1ff

def z192 : W := mkw 0xfcd2746800000004 0xe3f349d1a0000000 0xb8e0607000000001 0x02e38181c0000000

def z193 : W := mkw 0xf4620001da500000 0x07d1880007694000 0xffe38001fffc0003 0xd7ff8e0007fff000

def z194 : W := mkw 0xf6ff5001fb780008 0x57dbfd4007ede000 0xfffff801fffc0003 0xf7ffffe007fff000

def z195 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z196 : W := mkw 0x13db8bec00000004 0x604f6e2fb0000000 0x07ff87fe00000000 0xc01ffe1ff8000000

def z197 : W := mkw 0xffdbffec00802404 0xe3ff6fffb0020090 0xfffffffe63807e1b 0xfffffffff98e01f8

def z198 : W := mkw 0xffdbffed40000004 0xe3ff6fffb5000000 0xffffffffe0000003 0xf3ffffffff800000

def z199 : W := mkw 0xf6ff504bfb781088 0x77dbfd412fede042 0xfffff8fffffc71d7 0xffffffe3fffff1c7

def z200 : W := mkw 0xffdbffed56034814 0xe7ff6fffb5580d20 0xffffffff9c038023 0xe3fffffffe700e00

def z201 : W := mkw 0xffdbffed40024004 0xe3ff6fffb5000900 0xffffffffe003f033 0xfbffffffff800fc0

def z202 : W := mkw 0x1b6fafb6adfdbfc1 0x086dbebedab7f6ff 0x3f038701fffffffc 0x9cfc0e1c07ffffff

def z203 : W := mkw 0xffdbffec01080004 0xe3ff6fffb0042000 0xfffffffe039c0003 0xe7fffffff80e7000

def z204 : W := mkw 0x00240001fb780008 0x1400900007ede000 0x00000001fffc0000 0x1400000007fff000

def z205 : W := mkw 0xf6ff5049fb780008 0x77dbfd4127ede000 0xfffff8fffffc0003 0xf7ffffe3fffff000

def z206 : W := mkw 0xffffffffe062d186 0xf3ffffffff818b46 0xffffffffe063f1f7 0xfbffffffff818fc7

def z207 : W := mkw 0xed007e0016812c10 0x87b401f8005a04b0 0xff007f001f800e0b 0xa7fc01fc007e0038

def z208 : W := mkw 0xffdbffed52826414 0xe7ff6fffb54a0990 0xfffffffe63807013 0xe3fffffff98e01c0

def z209 : W := mkw 0x36ff005abb78918a 0x74dbfc016aede246 0x3fff80fe1ffc01c4 0xc4fffe03f87ff007

def z210 : W := mkw 0xe79d5a4f73aa7492 0xbf9e75693dcea9d2 0x471c180e63807010 0x011c7060398e01c0

def z211 : W := mkw 0xffdbffed56034814 0xe7ff6fffb5580d20 0xffffffffff838023 0xf7fffffffffe0e00

def z212 : W := mkw 0x0900afa400000004 0x802402be90000000 0x0000070000000000 0x0000001c00000000

def z213 : W := mkw 0xf6ff5049fb7a4008 0x77dbfd4127ede900 0xfffff8fffffff033 0xffffffe3ffffffc0

def z214 : W := mkw 0x0900ffec04836c14 0xa02403ffb0120db0 0x00007ffe0003fe38 0x280001fff8000ff8

def z215 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0x47fffffe00000000 0x611ffffff8000000

def z216 : W := mkw 0xe490504800000000 0x2392414120000000 0xfffc78fe00000003 0xe3fff1e3f8000000

def z217 : W := mkw 0x0000818000040240 0x0000020600001009 0x00038780007c0fce 0xfc000e1e0001f03f

def z218 : W := mkw 0x1b6fafb6adfdbfc1 0x086dbebedab7f6ff 0xffffffffffffffff 0xffffffffffffffff

def z219 : W := mkw 0xf6df000173280000 0x47db7c0005cca000 0xffff8001fffc0003 0xd7fffe0007fff000

def z220 : W := mkw 0xf7dbdbec00000004 0xe3df6f6fb0000000 0x47ff98fe00000000 0x411ffe63f8000000

def z221 : W := mkw 0xed007e0156836c10 0x87b401f8055a0db0 0xbf006701ff83fe39 0x9efc019c07fe0ff8

def z222 : W := mkw 0xfd62ffb1ded7ef51 0x87f58bfec77b5fbd 0xffe3fff1ffffffff 0xffff8fffc7ffffff

def z223 : W := mkw 0xffdbffec04812c04 0xe3ff6fffb01204b0 0xffffffffff83fe3b 0xfffffffffffe0ff8

def z224 : W := mkw 0xec90744956034810 0xa7b241d125580d20 0xf8fc78ff9c038023 0x63e3f1e3fe700e00

def z225 : W := mkw 0xf6df00017b380008 0x57db7c0005ece000 0x7f1f80007f9c0000 0x85fc7e0001fe7000

def z226 : W := mkw 0x2d007e0016836c10 0x84b401f8005a0db0 0x3f007f001f83fe38 0xacfc01fc007e0ff8

def z227 : W := mkw 0x00240012adfdbfc1 0x080090004ab7f6ff 0x00000001fffffffc 0x1c00000007ffffff

def z228 : W := mkw 0xffdbffed56034814 0xe7ff6fffb5580d20 0xffffffff9c038e2b 0xfffffffffe700e38

def z229 : W := mkw 0xe7995a4c00000004 0xe39e656930000000 0xc7fc78fe00000003 0x631ff1e3f8000000

def z230 : W := mkw 0x1862a5b08c558b41 0x00618a96c231562d 0x380387019c7f8fec 0x9ce00e1c0671fe3f

def z231 : W := mkw 0xffdb7e6c00000004 0xe3ff6df9b0000000 0xfffc787e00000001 0x03fff1e1f8000000

def z232 : W := mkw 0x1842a5a00c150a41 0x00610a9680305429 0x380387001c1c0e08 0x84e00e1c00707038

def z233 : W := mkw 0x1b6bafb48dddaf41 0x086daebed23776bd 0xbfe3e7f19fff8fef 0xfeff8f9fc67ffe3f

def z234 : W := mkw 0xedb07e59d6c3ed12 0xb7b6c1f9675b0fb4 0xffe07f71ff83fe3b 0xbfff81fdc7fe0ff8

def z235 : W := mkw 0x020d000221281080 0x000834000884a042 0x471f988e63fc71d6 0xfd1c7e62398ff1c7

def z236 : W := mkw 0xf7ff8b87fbfc36c8 0x5fdffe2e1feff0db 0xffff9f8ffffc7fdf 0xfffffe7e3ffff1ff

def z237 : W := mkw 0xe400500152024000 0x0790014005480900 0xff007801ff83f033 0xbffc01e007fe0fc0

def z238 : W := mkw 0xc090000000000000 0x0302400000000000 0xc0fc000000000003 0x4303f00000000000

def z239 : W := mkw 0x00240012a062d182 0x100090004a818b46 0x000000000063f1f4 0x0800000000018fc7

def z240 : W := mkw 0xf6ff0013fb78918a 0x57dbfc004fede246 0xffff8001fffc01c7 0xd7fffe0007fff007

def z241 : W := mkw 0xf6ff505bfb7ad18a 0x77dbfd416fedeb46 0xffffe0ffffff81e7 0xd7ffff83fffffe07

def z242 : W := mkw 0xed007e0156034810 0x87b401f805580d20 0xff007f019c038023 0xa3fc01fc06700e00

def z243 : W := mkw 0xe7995a4c00000004 0xe39e656930000000 0x471c180e00000000 0x011c706038000000

def z244 : W := mkw 0xffdbffec00024004 0xe3ff6fffb0000900 0xfffffffe0003f033 0xebfffffff8000fc0

def z245 : W := mkw 0x12ff005aa978918a 0x704bfc016aa5e246 0x00ff80fe007c01c4 0x4003fe03f801f007

def z246 : W := mkw 0x0000000000000000 0x0000000000000000 0x401c188e00000002 0x6100706238000000

def z247 : W := mkw 0xffdbffec00040244 0xe3ff6fffb0001009 0xfffffffe007c0fcf 0xfffffffff801f03f

def z248 : W := mkw 0xe699504800000000 0x639a654120000000 0xc7fc78fe00000003 0x631ff1e3f8000000

def z249 : W := mkw 0x36ff0001fb780008 0x54dbfc0007ede000 0x3fff8001fffc0000 0xd4fffe0007fff000

def z250 : W := mkw 0xc9b4ffffe4e7ffc3 0x3b26d3ffff939fff 0xc0fc7fffe063ffff 0x7b03f1ffff818fff

def z251 : W := mkw 0x00240013fffbfd9a 0x140090004fffeff6 0x00000001fffffffc 0x1c00000007ffffff

def z252 : W := mkw 0x3f4bafa416812c14 0xc4fd2ebe905a04b0 0x3f0387001f800e08 0x84fc0e1c007e0038

def z253 : W := mkw 0xe5905a4800000000 0xa396416920000000 0xc7fc78fe00000003 0x631ff1e3f8000000

def z254 : W := mkw 0x0900ffec00000004 0xa02403ffb0000000 0x00007ffe00000000 0x200001fff8000000

def z255 : W := mkw 0x00240013fef7ffd3 0x140090004ffbdfff 0x00000001fffffffc 0x1c00000007ffffff

def z256 : W := mkw 0xf6ff0003fb7a508a 0x57dbfc000fede942 0xffff8001fffc7013 0xd7fffe0007fff1c0

def z257 : W := mkw 0x03098b8400802400 0x000c262e10020090 0x471f9f8e63807e1a 0xfd1c7e7e398e01f8

def z258 : W := mkw 0xffdfffef77af7ed4 0xefff7fffbddebdfb 0xffffffffffffffff 0xffffffffffffffff

def z259 : W := mkw 0xfdd2ffe800000000 0xa3f74bffa0000000 0xfffffffe00000003 0xe3fffffff8000000

def z260 : W := mkw 0xe7bd5a5fe062d186 0xf39ef5697f818b46 0xc7fc78ffe063f1f7 0x7b1ff1e3ff818fc7

def z261 : W := mkw 0xffdbffed5b18000c 0xe7ff6fffb56c6000 0xffffffffff9c0003 0xf7fffffffffe7000

def z262 : W := mkw 0x12ff81b6a97c93c9 0x584bfe06daa5f24f 0x00ff80fe007c01c4 0x4003fe03f801f007

def z263 : W := mkw 0x020d000021280000 0x000834000084a000 0x471f800063fc0002 0xd51c7e00018ff000

def z264 : W := mkw 0xc094504b60225082 0x330251412d808942 0xc0fc78fe60007013 0x6303f1e3f98001c0

def z265 : W := mkw 0x364b000000000000 0x40d92c0000000000 0x3f03800000000000 0x80fc0e0000000000

def z266 : W := mkw 0x0924ffedfb78000c 0xb42493ffb7ede000 0x00007ffffffc0000 0x340001fffffff000

def z267 : W := mkw 0xf6ff0011fb788108 0x57dbfc0047ede204 0xffff80f1fffc01c7 0xd7fffe03c7fff007

def z268 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0xffffffff9c000003 0xf7fffffffe700000

def z269 : W := mkw 0x0800a5a004050a41 0x0020029680101429 0x0000070000000e08 0x0000001c00000038

def z270 : W := mkw 0xff4b7e015f9b6c18 0xc7fd2df8057e6db0 0xff03ff01ff9ffe3b 0xbffc0ffc07fe7ff8

def z271 : W := mkw 0xfcf27459de53c91a 0xf7f3c9d167794f24 0xb8e060719c038021 0x02e38181c6700e00

def z272 : W := mkw 0xffdbffec00842644 0xebff6fffb0021099 0xfffffffe00000e0b 0xe3fffffff8000038

def z273 : W := mkw 0xecb4745bf663d992 0xb7b2d1d16fd98f66 0xf8fc78fffc63f1f7 0x7be3f1e3fff18fc7

def z274 : W := mkw 0xc890744800000000 0x232241d120000000 0xf8fc7ffe00000003 0xe3e3f1fff8000000

def z275 : W := mkw 0xffdbffed52000004 0xe7ff6fffb5480000 0xfffffffe63800003 0xe3fffffff98e0000

def z276 : W := mkw 0x126f0000a9780008 0x5049bc0002a5e000 0x00038000007c0000 0x00000e000001f000

def z277 : W := mkw 0xffdbffec1f992c1c 0xe7ff6fffb07e64b0 0xfffffffe1f9c0e0b 0xe7fffffff87e7038

def z278 : W := mkw 0xffdbffec16812c14 0xe7ff6fffb05a04b0 0xfffffffe1f800e0b 0xe7fffffff87e0038

def z279 : W := mkw 0xe4245013fb7ad18a 0x179091404fedeb46 0xff007801fffff1f7 0xbffc01e007ffffc7

def z280 : W := mkw 0xffdb7e6c00000004 0xe3ff6df9b0000000 0xfffc78fe00000003 0x63fff1e3f8000000

def z281 : W := mkw 0xe4b4505bf262d18a 0x7792d1416fc98b46 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z282 : W := mkw 0xec00740156034800 0x07b001d005580d20 0xff007f01ff83fe3b 0xbffc01fc07fe0ff8

def z283 : W := mkw 0xffdbffec1a10000c 0xe7ff6fffb0684000 0xfffffffe1c000003 0xe3fffffff8700000

def z284 : W := mkw 0x01040a0221ac36c0 0x080410280886b0db 0x47001f0063fc7fde 0xbd1c007c018ff1ff

def z285 : W := mkw 0x10d2006800000004 0x60434801a0000000 0x00e0007000000000 0x00038001c0000000

def z286 : W := mkw 0xed007e0156836c10 0x87b401f8055a0db0 0xbf0067019f838e29 0x86fc019c067e0e38

def z287 : W := mkw 0xc094504a20201080 0x2302514128808042 0xc0fc78fe606071d7 0x7b03f1e3f98181c7

def z288 : W := mkw 0xd8f6f5fbe062d182 0x3363dbd7ef818b46 0xf8ffffffe063f1f7 0xfbe3ffffff818fc7

def z289 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0xc0fc7fffe063ffff 0xff03f1ffff818fff

def z290 : W := mkw 0x1062000088500000 0x0041880002214000 0xffe38001fffc0003 0xd7ff8e0007fff000

def z291 : W := mkw 0xfcd2746800000004 0xe3f349d1a0000000 0xf8fc78fe00000003 0x63e3f1e3f8000000

def z292 : W := mkw 0xc9b47e5be4e3fd92 0xb326d1f96f938ff6 0xc0fc7fffe063ffff 0x7b03f1ffff818fff

def z293 : W := mkw 0x1862a5b08c558b41 0x00618a96c231562d 0xf8ffffff9c7f8fef 0xffe3fffffe71fe3f

def z294 : W := mkw 0x106281b088548341 0x00418a06c221520d 0x00038000007c01c4 0x00000e000001f007

def z295 : W := mkw 0x0090504800000000 0x2002414120000000 0x00fc78fe00000000 0x6003f1e3f8000000

def z296 : W := mkw 0xc1b4dbdfe0e6f7c2 0x3b06d36f7f839bdf 0xc0fc7fffe063ffff 0x7b03f1ffff818fff

def z297 : W := mkw 0x00240013ec77dbc3 0x100090004fb1df6f 0x00000001fc7ffffc 0x1c00000007f1ffff

def z298 : W := mkw 0xffdbffec0c150a45 0xe3ff6fffb0305429 0xfffffffe1c1c0e0b 0xe7fffffff8707038

def z299 : W := mkw 0xc0b0505bc042d182 0x3302c1416f010b46 0x80e078ff8003f1f5 0x2a0381e3fe000fc7

def z300 : W := mkw 0x364f00003b380008 0x44d93c0000ece000 0x3f0380007ffc0000 0x94fc0e0001fff000

def z301 : W := mkw 0x0820a5b084458b41 0x00208296c211162d 0x80e067f180638fef 0x7a03819fc6018e3f

def z302 : W := mkw 0x2609000013080008 0x44982400004c2000 0x0700000003800000 0x001c0000000e0000

def z303 : W := mkw 0x12db004800000000 0x604b6c0120000000 0x00ff80fe00000000 0x4003fe03f8000000

def z304 : W := mkw 0x2d002e0016812c10 0x84b400b8005a04b0 0x7f001f007f807e1a 0xbdfc007c01fe01f8

def z305 : W := mkw 0xd2dbd1ec00000004 0x634b6f47b0000000 0x40ff98fe00000000 0x4103fe63f8000000

def z306 : W := mkw 0x2d002e0156836c10 0x84b400b8055a0db0 0xbf006701ff83fe3b 0xbefc019c07fe0ff8

def z307 : W := mkw 0xffdbffec04050a44 0xe3ff6fffb0101429 0xffffffff9c7f8fef 0xfffffffffe71fe3f

def z308 : W := mkw 0xc0b45001e0624000 0x1302d14007818900 0xc0fc7801e063f033 0x7b03f1e007818fc0

def z309 : W := mkw 0x0000504800000000 0x2000014120000000 0x000078fe00000000 0x200001e3f8000000

def z310 : W := mkw 0xffdbffec04010804 0xe3ff6fffb0100420 0xffffffff9c038e2b 0xfffffffffe700e38

def z311 : W := mkw 0xf6ff0049fb780008 0x77dbfc0127ede000 0xffff80fffffc0003 0xd7fffe03fffff000

def z312 : W := mkw 0x1b4bafa404812c00 0x006d2ebe901204b0 0xffffffffff83fe3b 0xfffffffffffe0ff8

def z313 : W := mkw 0xed907e4956836c10 0xa7b641f9255a0db0 0xff1c7f0fff83fe3b 0xbffc71fc3ffe0ff8

def z314 : W := mkw 0xc9007e0144836c00 0x032401f805120db0 0xff007f01ff83fe3b 0xbffc01fc07fe0ff8

def z315 : W := mkw 0xfcd6746a21ac36c4 0xebf359d1a886b0db 0xb8e0607063fc7fdd 0x1ee38181c18ff1ff

def z316 : W := mkw 0xed207e11d6c3ed10 0x87b481f8475b0fb4 0xffe07ff1ffe3ffff 0xffff81ffc7ff8fff

def z317 : W := mkw 0xffdbffec08140245 0xe3ff6fffb0205009 0xfffffffe001c0003 0xe3fffffff8007000

def z318 : W := mkw 0xffdb7e4800000000 0xe3ff6df920000000 0xfffffffe00000003 0xe3fffffff8000000

def z319 : W := mkw 0x01008b8400842640 0x0804022e10021099 0x0000070000000e08 0x0000001c00000038

def z320 : W := mkw 0xf4f25059da52c10a 0x77d3c94167694b04 0xb8e060719c038021 0x02e38181c6700e00

def z321 : W := mkw 0xc9b4ffdfe4e7ffd2 0xbb26d3ff7f939fff 0xc0fc7fffe063ffff 0x7b03f1ffff818fff

def z322 : W := mkw 0xf6ff005bfb78918a 0x77dbfc016fede246 0xffffe0ffffff81e7 0xffffff83fffffe07

def z323 : W := mkw 0xc299504800000000 0x230a654120000000 0xc7fff8fe00000003 0xe31fffe3f8000000

def z324 : W := mkw 0x00200011c042c102 0x1000800047010b04 0x0000000180038020 0x0000000006000e00

def z325 : W := mkw 0x03098b84018c2640 0x080c262e10063099 0x471f9f8e039c0e0a 0xe51c7e7e380e7038

def z326 : W := mkw 0x0900ffb00487ef51 0x802403fec0121fbd 0x00007ff00003fffc 0x280001ffc0000fff

def z327 : W := mkw 0x2db42e5ab6e1bd92 0xb4b6d0b96adb86f6 0x3ffc07fe1fe00fcc 0xc4fff01ff87f803f

def z328 : W := mkw 0x3f4bafa4178d2e54 0xccfd2ebe905e34b9 0x3f0387001f9c0e08 0x84fc0e1c007e7038

def z329 : W := mkw 0xd8d6f5eb6c375ac3 0x33635bd7adb0dd6b 0x781f9f0e7c1c7e18 0x85e07e7c39f071f8

def z330 : W := mkw 0xc399dbcc00000000 0x230e676f30000000 0xc7fffffe00000003 0xe31ffffff8000000

def z331 : W := mkw 0x364b505a1b1ad18a 0x64d92d41686c6b46 0x3f03f8fe1f9ff1f4 0xacfc0fe3f87e7fc7

def z332 : W := mkw 0x3f6fafb7e062d186 0xd0fdbebedf818b46 0x3f038701e063f1f4 0x98fc0e1c07818fc7

def z333 : W := mkw 0xc090d1ec00000004 0x23024347b0000000 0xc0fc78fe00000003 0x6303f1e3f8000000

def z334 : W := mkw 0x0820a59084458b40 0x002082964211162d 0xb8e3e7f19c7f8fef 0xfee38f9fc671fe3f

def z335 : W := mkw 0x366b00009b580008 0x44d9ac00026d6000 0xbfe380019ffc0003 0xd6ff8e00067ff000

def z336 : W := mkw 0xe5245a13f2e2f592 0x979491684fcb8bd6 0x47001801e3e3f1f4 0x191c0060078f8fc7

def z337 : W := mkw 0xc0b0505a8042d182 0x2302c1416a010b46 0xc0fc78ff8063f1f7 0x7b03f1e3fe018fc7

def z338 : W := mkw 0xf6db50481b180008 0x67db6d41206c6000 0xfffff8fe1f9c0003 0xe7ffffe3f87e7000

def z339 : W := mkw 0xe4b4505be062d186 0xf392d1416f818b46 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z340 : W := mkw 0x12db81ec00000004 0x604b6e07b0000000 0x00ff87fe00000002 0xe003fe1ff8000000

def z341 : W := mkw 0xc1b45a5be0e2f582 0x3306d1696f838bd6 0xc7fc7fffe3e3ffff 0xff1ff1ffff8f8fff

def z342 : W := mkw 0xed007e0156836c10 0x87b401f8055a0db0 0xffe07ff1ff83fe3b 0xffff81ffc7fe0ff8

def z343 : W := mkw 0xf6db504800000000 0x63db6d4120000000 0xfffff8fe00000003 0xe3ffffe3f8000000

def z344 : W := mkw 0xf64b50015b1a4008 0x47d92d40056c6900 0xff03f801ff9ff033 0xbffc0fe007fe7fc0

def z345 : W := mkw 0x186224108c518900 0x0061889042314624 0xb8e3e7f19c7f8fef 0xfee38f9fc671fe3f

def z346 : W := mkw 0x00240012a978918a 0x100090004aa5e246 0x00000000007c01c4 0x000000000001f007

def z347 : W := mkw 0x01048b8620a436c0 0x0804122e188290db 0x401c1f8e60607fde 0x7900707e398181ff

def z348 : W := mkw 0xf4f20001da500008 0x57d3c80007694000 0xb8e000019c000001 0x02e3800006700000

def z349 : W := mkw 0x124b000009180008 0x40492c0000246000 0x00038000001c0000 0x00000e0000007000

def z350 : W := mkw 0xc9007e0144836c10 0x832401f805120db0 0xc0007f01e003fe3b 0x3b0001fc07800ff8

def z351 : W := mkw 0xc0b4505bec77dbc3 0x3302d1416fb1df6f 0xc0fc78fffc7fffff 0x7f03f1e3fff1ffff

def z352 : W := mkw 0x12df81ee212c12c4 0x684b7e07b884b04b 0x00ff80fe007c01c4 0x4003fe03f801f007

def z353 : W := mkw 0x0900afa004852e51 0x802402be801214b9 0x0000070000000e08 0x0000001c00000038

def z354 : W := mkw 0xc090504800000000 0x2302414120000000 0x401c180e00000000 0x0100706038000000

def z355 : W := mkw 0xf6ff5049fb7a400a 0x77dbfd4127ede900 0xffff8001fffc0003 0xd7fffe0007fff000

def z356 : W := mkw 0xfedb746800000004 0xe3fb6dd1a0000000 0xfffff8fe00000003 0xe3ffffe3f8000000

def z357 : W := mkw 0xf7ffdbdffbfef7ca 0x7fdfff6f7feffbdf 0xffffffffffffffff 0xffffffffffffffff

def z358 : W := mkw 0xc090004800000000 0x2302400120000000 0xc0fc00fe00000003 0x4303f003f8000000

def z359 : W := mkw 0xc3bddbdfe1eef7c2 0x3b0ef76f7f87bbdf 0xc7ffffffe3ffffff 0xff1fffffff8fffff

def z360 : W := mkw 0xffdbffec00802404 0xe3ff6fffb0020090 0xfffffffe03800e0b 0xe7fffffff80e0038

def z361 : W := mkw 0xe79d5a4f73aa7494 0xef9e75693dcea9d2 0x471c180e63807010 0x011c7060398e01c0

def z362 : W := mkw 0xf6ff0011fb788108 0x57dbfc0047ede204 0xffffe0f1ffff81e7 0xffffff83c7fffe07

def z363 : W := mkw 0xf6df504b7b3a508a 0x77db7d412dece942 0x7f1f980e7f9c7010 0x85fc7e6039fe71c0

def z364 : W := mkw 0xc0b4505bf6e3fd92 0x3702d1416fdb8ff6 0xc0fc78ffffe3ffff 0x7f03f1e3ffff8fff

def z365 : W := mkw 0xfcf27479de53c90b 0x77f3c9d1e7794f24 0xb8e060719c038021 0x02e38181c6700e00

def z366 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0xc7fc78ffe3e3f1f7 0xff1ff1e3ff8f8fc7

def z367 : W := mkw 0x030d8b8621ac36c0 0x080c362e1886b0db 0x471f9f8e63fc7fdc 0xc51c7e7e398ff1ff

def z368 : W := mkw 0x1866a5b3ec77dbc3 0x10619a96cfb1df6f 0xb8e3e7f1fc7fffff 0xfee38f9fc7f1ffff

def z369 : W := mkw 0xe69d504b732a508a 0x779a75412dcca942 0x471c180e63807010 0x011c7060398e01c0

def z370 : W := mkw 0x0004000360225082 0x100010000d808942 0x0000000060007010 0x00000000018001c0

def z371 : W := mkw 0x1842a5a00c150a41 0x00610a9680305429 0xb8e3e7f01c1c0e0b 0xe6e38f9fc0707038

def z372 : W := mkw 0x030d0a0621a83480 0x080c34281886a0d2 0x471c180e63807010 0x011c7060398e01c0

def z373 : W := mkw 0x124b000009180000 0x00492c0000246000 0x3f0380001f9c0000 0x84fc0e00007e7000

def z374 : W := mkw 0x0900afa404852e41 0x082402be901214b9 0x0000070000000e08 0x0000001c00000038

def z375 : W := mkw 0x0900ffb60487ffd1 0x882403fed8121fff 0x00007ffe0003fffc 0x280001fff8000fff

def z376 : W := mkw 0x00240012a97c93c1 0x080090004aa5f24f 0x00000000007c01c4 0x000000000001f007

def z377 : W := mkw 0x186224308c518901 0x00618890c2314624 0xb8e060719c038021 0x02e38181c6700e00

def z378 : W := mkw 0xf6db000152000000 0x47db6c0005480000 0xffff8001ff800003 0xd7fffe0007fe0000

def z379 : W := mkw 0x0900afb00485af41 0x002402bec01216bd 0x00007ff00003fffc 0x280001ffc0000fff

def z380 : W := mkw 0xf6fb0001da500000 0x47dbec0007694000 0xffff8001fffc0003 0xd7fffe0007fff000

def z381 : W := mkw 0xed007e0152000000 0x87b401f805480000 0xff007f01ff800003 0xb7fc01fc07fe0000

def z382 : W := mkw 0x03098b84018c2640 0x080c262e10063099 0x07038700039c0e08 0x841c0e1c000e7038

def z383 : W := mkw 0x1bdbafec00000004 0x606f6ebfb0000000 0xfffffffe00000003 0xe3fffffff8000000

def z384 : W := mkw 0x0020001088548341 0x000080004221520d 0x00000000007c01c4 0x000000000001f007

def z385 : W := mkw 0xe7995a4d52826414 0xe79e6569354a0990 0x471c180e63807010 0x011c7060398e01c0

def z386 : W := mkw 0x0900ff8004876e50 0x802403fe00121db9 0x00007f800003fffc 0x280001fe00000fff

def z387 : W := mkw 0x13db8bec00000004 0x604f6e2fb0000000 0x47ff98fe00000000 0x411ffe63f8000000

def z388 : W := mkw 0xc0b4505bfa72d18a 0x3702d1416fe9cb46 0xc0fc78fffc63f1f7 0x7b03f1e3fff18fc7

def z389 : W := mkw 0xe5905a4952826410 0xa7964169254a0990 0xc7fc78fe63807013 0x631ff1e3f98e01c0

def z390 : W := mkw 0x0800a5b004058b41 0x00200296c010162d 0x000067f000038fec 0x2800019fc0000e3f

def z391 : W := mkw 0x1962ffb08cd7ef51 0x80658bfec2335fbd 0xb8e3fff19c7fffff 0xfee38fffc671ffff

def z392 : W := mkw 0xffdbffed52024004 0xe7ff6fffb5480900 0xffffffffff83f033 0xfffffffffffe0fc0

def z393 : W := mkw 0x030d8b8621ac36c0 0x080c362e1886b0db 0x0703870063fc7fdc 0x9c1c0e1c018ff1ff

def z394 : W := mkw 0xc090504800000000 0x2302414120000000 0x80e0607000000001 0x02038181c0000000

def z395 : W := mkw 0xffdb7e6c00000004 0xe3ff6df9b0000000 0xfffff87e00000003 0xc3ffffe1f8000000

def z396 : W := mkw 0xc090504940024000 0x2302414125000900 0xc0fc78ff80038023 0x6303f1e3fe000e00

def z397 : W := mkw 0xed247e13fef7ffd3 0x97b491f84ffbdfff 0xff007f01ffffffff 0xbffc01fc07ffffff

def z398 : W := mkw 0xf6ff0003fb781088 0x57dbfc000fede042 0xffff8001fffc71d7 0xdffffe0007fff1c7

def z399 : W := mkw 0xc2bd505be16ad182 0x330af5416f85ab46 0xc7fff8ffe3fff1f7 0xff1fffe3ff8fffc7

def z400 : W := mkw 0xf5f28b87dad436c8 0x5fd7ca2e1f6b50db 0xb8e01f8f9c007fdd 0x2ae3807e3e7001ff

def z401 : W := mkw 0xffdbffec04010804 0xe3ff6fffb0100420 0xfffffffe1c000e0b 0xe7fffffff8700038

def z402 : W := mkw 0xf6df00017b380008 0x57db7c0005ece000 0x7f1f80007ffc0002 0xd5fc7e0001fff000

def z403 : W := mkw 0xf6ff0001fb780008 0x57dbfc0007ede000 0xbfff80019ffc0001 0xc6fffe00067ff000

def z404 : W := mkw 0xe5005a0152826400 0x07940168054a0990 0xff007f01ff83fe3b 0xbffc01fc07fe0ff8

def z405 : W := mkw 0xcb99ffec00000004 0xa32e67ffb0000000 0xc7fffffe00000003 0xe31ffffff8000000

def z406 : W := mkw 0x00240013f6e3fd92 0x140090004fdb8ff6 0x00000001ffe3fffc 0x1c00000007ff8fff

def z407 : W := mkw 0xc0b4505aa062d182 0x3302d1416a818b46 0xc0fc78fe0063f1f7 0x6b03f1e3f8018fc7

def z408 : W := mkw 0x1b6f2e36adf9bd81 0x086dbcb8dab7e6f6 0xfffc787fff83f031 0x03fff1e1fffe0fc0

def z409 : W := mkw 0xed007e4956836c10 0xa7b401f9255a0db0 0xff007fffff83fe3b 0xbffc01fffffe0ff8

def z410 : W := mkw 0xffdbffec12802414 0xe7ff6fffb04a0090 0xfffffffe03800003 0xe3fffffff80e0000

def z411 : W := mkw 0xf6ff505bfb7ad18a 0x77dbfd416fedeb46 0xffff980ffffff1f7 0xdffffe603fffffc7

def z412 : W := mkw 0xc000500156836c10 0x07000140055a0db0 0xc0007801ff83fe3b 0x3f0001e007fe0ff8

def z413 : W := mkw 0xf6db81ec00000004 0x63db6e07b0000000 0x47ff80fe00000000 0x411ffe03f8000000

def z414 : W := mkw 0x12ff81dea97c93ca 0x784bfe077aa5f24f 0x00ff80fe007c01c4 0x4003fe03f801f007

def z415 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0x80fc78ff8063f1f5 0x6a03f1e3fe018fc7

def z416 : W := mkw 0x3f4bafa40c150a45 0xc0fd2ebe90305429 0x3f0387001c1c0e08 0x84fc0e1c00707038

def z417 : W := mkw 0xffdbffed56836c14 0xe7ff6fffb55a0db0 0xffffffff9f838e2b 0xe7fffffffe7e0e38

def z418 : W := mkw 0xffdbffed40826404 0xe3ff6fffb5020990 0xffffffffe383fe3b 0xffffffffff8e0ff8

def z419 : W := mkw 0xe60d000173280000 0x0798340005cca000 0xff1f8001fffc0003 0xd7fc7e0007fff000

def z420 : W := mkw 0xf6ff5059fb7ac10a 0x77dbfd4167edeb04 0xfffff871fffff033 0xffffffe1c7ffffc0

def z421 : W := mkw 0xfffffffffb7ad18e 0xf7ffffffffedeb46 0xfffffffffffff1f7 0xffffffffffffffc7

def z422 : W := mkw 0x136f8b86a9fc36c0 0x084dbe2e1aa7f0db 0xffff9f8ffffc7fdf 0xfffffe7e3ffff1ff

def z423 : W := mkw 0x3f4bafa41e952e55 0xc4fd2ebe907a54b9 0x3f0387001f9c0e08 0x84fc0e1c007e7038

def z424 : W := mkw 0x0004000220201080 0x0000100008808042 0x401c188e606071d6 0x79007062398181c7

def z425 : W := mkw 0xed007e6956836c14 0xa7b401f9a55a0db0 0xff007f71ff83fe3b 0xbffc01fdc7fe0ff8

def z426 : W := mkw 0x1bdbafec00000004 0xe06f6ebfb0000000 0x00ff87fe00000000 0x4003fe1ff8000000

def z427 : W := mkw 0xf6db81ec00000004 0x63db6e07b0000000 0xffff80fe00000003 0xc3fffe03f8000000

def z428 : W := mkw 0xf6ff0001fb780008 0x57dbfc0007ede000 0xffff8001fffc0001 0x43fffe0007fff000

def z429 : W := mkw 0xc9907e4800000000 0xa32641f920000000 0xc0fc7ffe00000003 0x6303f1fff8000000

def z430 : W := mkw 0x032d8b96a1ecb7c0 0x080cb62e5a87b2df 0xc7ffffffe3ffffff 0xff1fffffff8fffff

def z431 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0xfffffffe60007013 0xfbfffffff98001c0

def z432 : W := mkw 0xf6ff0003fb781088 0x57dbfc000fede042 0xffff808ffffc01c7 0xd7fffe023ffff007

def z433 : W := mkw 0xffdbffec16010814 0xe7ff6fffb0580420 0xfffffffe1c000003 0xe3fffffff8700000

def z434 : W := mkw 0xc094504b60225080 0x230251412d808942 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z435 : W := mkw 0xe490504800000004 0xe392414120000000 0xc0fc78fe00000003 0x6303f1e3f8000000

def z436 : W := mkw 0xc004500360225080 0x030011400d808942 0xc01c788fe063f1f7 0x7b0071e23f818fc7

def z437 : W := mkw 0x030d0a0221a83480 0x000c34280886a0d2 0x471f9f8e63fc7fde 0xfd1c7e7e398ff1ff

def z438 : W := mkw 0x01008b86008436c0 0x0804022e180210db 0x00001f8e00007fdc 0x2800007e380001ff

def z439 : W := mkw 0x00240013fbfef7ca 0x1c0090004feffbdf 0x00000001fffffffc 0x1c00000007ffffff

def z440 : W := mkw 0xc0b4505aa0609182 0x3302d1416a818246 0xc0fc78fe006001c7 0x6303f1e3f8018007

def z441 : W := mkw 0x2f09af84178d2e50 0x8cbc26be105e34b9 0x3f0387001f9c0e08 0x84fc0e1c007e7038

def z442 : W := mkw 0xffdbffed44034804 0xe3ff6fffb5100d20 0xfffffffffc03fe3b 0xfffffffffff00ff8

def z443 : W := mkw 0x1adba5ec0c150a45 0x606b6e97b0305429 0x38ff87fe1c1c0e08 0xc4e3fe1ff8707038

def z444 : W := mkw 0x020d000021280000 0x000834000084a000 0xff1f8001fffc0003 0xd7fc7e0007fff000

def z445 : W := mkw 0x1862a5b08c558b41 0x00618a96c231562d 0xffe3e7f1ffff8fef 0xffff8f9fc7fffe3f

def z446 : W := mkw 0x01000a0156836c10 0x04040028055a0db0 0x47001f01ff83fe3a 0xbd1c007c07fe0ff8

def z447 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0xc0fc78ffe003f1f5 0x2b03f1e3ff800fc7

def z448 : W := mkw 0xf6ff5059fb7ac10a 0x77dbfd4167edeb04 0xffffe071ffff8023 0xd7ffff81c7fffe00

def z449 : W := mkw 0xd8f2f5f88c558b41 0x2363cbd7e231562d 0xf8ffffff9c7f8fef 0xffe3fffffe71fe3f

def z450 : W := mkw 0xf6ff5059fb7ac10a 0x77dbfd4167edeb04 0xfffff8ffffff8023 0xf7ffffe3fffffe00

def z451 : W := mkw 0x00240012a1ecb7c2 0x180090004a87b2df 0x0000000063fc7fdc 0x1c000000018ff1ff

def z452 : W := mkw 0xedb47e01f6e36c10 0x97b6d1f807db8db0 0xfffc7f01ffe3fe3b 0xfffff1fc07ff8ff8

def z453 : W := mkw 0xe4b4505bfb7ad18a 0x3792d1416fedeb46 0xfffc78fffffff1f7 0xfffff1e3ffffffc7

def z454 : W := mkw 0x1862a5b08c558b41 0x00618a96c231562d 0xf8e3fff1fc7fffff 0xffe38fffc7f1ffff

def z455 : W := mkw 0x000000120002d182 0x0000000048000b46 0x000000000003f1f4 0x0800000000000fc7

def z456 : W := mkw 0xf4625011da52c100 0x07d1894047694b04 0xffe3f8f1fffff1f7 0xffff8fe3c7ffffc7

def z457 : W := mkw 0xf4660001fb780008 0x17d1980007ede000 0xffe38001fffc0003 0xd7ff8e0007fff000

def z458 : W := mkw 0xd2dbd1ec00000004 0x634b6f47b0000000 0xc0fff8fe00000003 0x6303ffe3f8000000

def z459 : W := mkw 0xffdbffec04836c14 0xe3ff6fffb0120db0 0xfffffffe0003fe3b 0xebfffffff8000ff8

def z460 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0xfffc7ffe00000001 0x23fff1fff8000000

def z461 : W := mkw 0x12db000000000000 0x404b6c0000000000 0x00ff800000000000 0x4003fe0000000000

def z462 : W := mkw 0xf6ff81edfb78000c 0x77dbfe07b7ede000 0xffff80fffffc0003 0xd7fffe03fffff000

def z463 : W := mkw 0x1bff7e00adfb6c18 0xd06ffdf802b7edb0 0x00ffff00007ffe38 0x6803fffc0001fff8

def z464 : W := mkw 0xffdbffec04836c14 0xe3ff6fffb0120db0 0xfffffffe6383fe3b 0xfffffffff98e0ff8

def z465 : W := mkw 0x0900af8604853ec0 0x082402be181214fb 0x00007f8e0003fffc 0x280001fe38000fff

def z466 : W := mkw 0x09247e13e4e3fd92 0x902491f84f938ff6 0x00007f01e063fffc 0x380001fc07818fff

def z467 : W := mkw 0x00240012a0609182 0x100090004a818246 0x00000000606071d4 0x18000000018181c7

def z468 : W := mkw 0xff4bffa400000004 0xc3fd2ffe90000000 0xff03ff0000000003 0xa3fc0ffc00000000

def z469 : W := mkw 0xc399dbcd40826400 0x230e676f35020990 0xc7ffffffe383fe3b 0xff1fffffff8e0ff8

def z470 : W := mkw 0x01240a13e0e2f582 0x100490284f838bd6 0x47001f01e3e3fffe 0xbd1c007c078f8fff

def z471 : W := mkw 0xf6df00017b380008 0x57db7c0005ece000 0xff1f8001ff9c0003 0x97fc7e0007fe7000

def z472 : W := mkw 0x00240013e0e6f7c2 0x180090004f839bdf 0x00000001e063fffc 0x1800000007818fff

def z473 : W := mkw 0xed007e5b5683fd92 0xa7b401f96d5a0ff6 0xff007fffff83ffff 0xbffc01fffffe0fff

def z474 : W := mkw 0xf6ff504bfb7a508a 0x77dbfd412fede942 0xffff980ffffc7013 0xd7fffe603ffff1c0

def z475 : W := mkw 0xe7b95a5c8c558b45 0xe39ee5697231562d 0x471c180f9c7f8fec 0x1d1c70603e71fe3f

def z476 : W := mkw 0xf6ff0013fb789188 0x57dbfc004fede246 0xfffff8fffffff1f7 0xffffffe3ffffffc7

def z477 : W := mkw 0xed007e0156836c10 0x87b401f8055a0db0 0x7f001f01ff83fe38 0x9dfc007c07fe0ff8

def z478 : W := mkw 0xf7db5a4c00000004 0xe3df6d6930000000 0xfffff8fe00000003 0xe3ffffe3f8000000

def z479 : W := mkw 0xe6bd0001f3680000 0x179af40007cda000 0xffff8001fffc0003 0xd7fffe0007fff000

def z480 : W := mkw 0x0900fffe0002d186 0xa02403fff8000b46 0x00007ffe0003f1f4 0x280001fff8000fc7

def z481 : W := mkw 0x1842a5a004010800 0x00610a9680100420 0xb8e3e7f19c038e2b 0xfee38f9fc6700e38

def z482 : W := mkw 0xfffbfffdded7ef55 0xe7ffeffff77b5fbd 0xffffffffffffffff 0xffffffffffffffff

def z483 : W := mkw 0xed907e0156836c10 0x87b641f8055a0db0 0xfffc7f01ff83fe3b 0xfffff1fc07fe0ff8

def z484 : W := mkw 0x366b00009b580008 0x44d9ac00026d6000 0x3f0380019ffc0000 0x94fc0e00067ff000

def z485 : W := mkw 0xffdbffed5f9b6c1c 0xe7ff6fffb57e6db0 0xffffffffff9ffe3b 0xfffffffffffe7ff8

def z486 : W := mkw 0xe400000156836c10 0x07900000055a0db0 0xff000001ff83fe3b 0x9ffc000007fe0ff8

def z487 : W := mkw 0xff4bffa556836c14 0xc7fd2ffe955a0db0 0xff03ff01ff83fe3b 0xbffc0ffc07fe0ff8

def z488 : W := mkw 0x030d8b8621ac36c0 0x080c362e1886b0db 0xc7fffffe63fc7fdf 0xff1ffffff98ff1ff

def z489 : W := mkw 0x032d8b96adfdbfc1 0x080cb62e5ab7f6ff 0x471f9f8ffffffffe 0xfd1c7e7e3fffffff

def z490 : W := mkw 0xfcf27479de53c913 0xb7f3c9d1e7794f24 0xb8e060719c038021 0x02e38181c6700e00

def z491 : W := mkw 0xc0245013e062d182 0x130091404f818b46 0x40001801e063f1f4 0x1900006007818fc7

def z492 : W := mkw 0xf6fb00009b580008 0x47dbec00026d6000 0xffff80019ffc0003 0xd7fffe00067ff000

def z493 : W := mkw 0xef99ffec00000004 0xe3be67ffb0000000 0xc7fc7ffe00000003 0x631ff1fff8000000

def z494 : W := mkw 0xc9b4fffbe4e7ffd3 0xb326d3ffef939fff 0xc0fc7fffe063ffff 0x7b03f1ffff818fff

def z495 : W := mkw 0xffdbffec1f1d0a4d 0xe7ff6fffb07c7429 0xfffffffe1f9c0e0b 0xe7fffffff87e7038

def z496 : W := mkw 0xc0b4505be1eef7c2 0x3b02d1416f87bbdf 0xc0fc78ffe3ffffff 0x7f03f1e3ff8fffff

def z497 : W := mkw 0xfc62a5b1de558b41 0x07f18a96c779562d 0xffe3e7f1ffff8fef 0xffff8f9fc7fffe3f

def z498 : W := mkw 0xc890f5e800000000 0x232243d7a0000000 0xc0fc7ffe00000003 0x6303f1fff8000000

def z499 : W := mkw 0x00040002212c12c0 0x080010000884b04b 0x00000000007c01c4 0x000000000001f007

def z500 : W := mkw 0xfcd2746956034814 0xe7f349d1a5580d20 0xb8e060719c038021 0x02e38181c6700e00

def z501 : W := mkw 0x00240012a87493c3 0x100090004aa1d24f 0x00000000007c01c4 0x000000000001f007

def z502 : W := mkw 0x020d8186212c12c0 0x080836061884b04b 0x00038000007c01c4 0x00000e000001f007

def z503 : W := mkw 0xfcd2746800000004 0xe3f349d1a0000000 0xf8fc787e00000001 0x03e3f1e1f8000000

def z504 : W := mkw 0xe6bd505bf36ad18a 0x779af5416fcdab46 0xc7fc78ffe3e3f1f7 0x7b1ff1e3ff8f8fc7

def z505 : W := mkw 0xf6ff5001fb7a4008 0x57dbfd4007ede900 0xffff9801fffc7013 0xd7fffe6007fff1c0

def z506 : W := mkw 0xf6ff5001fb7a4018 0xd7dbfd4007ede900 0xffff8001fffc0003 0xd7fffe0007fff000

def z507 : W := mkw 0x00b4005aa0609182 0x3002d0016a818246 0x40fc18fe606071d6 0x7903f063f98181c7

def z508 : W := mkw 0xc9b4ffffe062d186 0xb326d3ffff818b46 0xc0fc7fffe063f1f7 0x7b03f1ffff818fc7

def z509 : W := mkw 0xc3bddbdfe062d182 0x330ef76f7f818b46 0xc7ffffffe063f1f7 0xfb1fffffff818fc7

def z510 : W := mkw 0x36db81ec00000004 0x60db6e07b0000000 0x3fff80fe00000000 0xc0fffe03f8000000

def z511 : W := mkw 0x3fdbafec00000004 0xe0ff6ebfb0000000 0x7fff9ffe00000002 0xe1fffe7ff8000000

def z512 : W := mkw 0x36ff0000bb780008 0x54dbfc0002ede000 0x3fff80001ffc0000 0xc4fffe00007ff000

def z513 : W := mkw 0xf6dbd1ec00000004 0x63db6f47b0000000 0xfffff8fe00000003 0xe3ffffe3f8000000

def z514 : W := mkw 0x030d8b8621ac36c0 0x080c362e1886b0db 0x471f9f0e63fc7fdc 0x9d1c7e7c398ff1ff

def z515 : W := mkw 0xed007e0140024000 0x83b401f805000900 0xff007f01e003f033 0xbbfc01fc07800fc0

def z516 : W := mkw 0xe4b4505bf262d182 0x3792d1416fc98b46 0xf8fc78fffc63f1f7 0x7be3f1e3fff18fc7

def z517 : W := mkw 0xf6ff0011fb7ac10a 0x57dbfc0047edeb04 0xffff8001ffff8023 0xd7fffe0007fffe00

def z518 : W := mkw 0x12db81ec00000004 0x604b6e07b0000000 0xb8ff80fe00000003 0xc2e3fe03f8000000

def z519 : W := mkw 0xed00ffb15687ef51 0x87b403fec55a1fbd 0xff007ff1ff83ffff 0xbffc01ffc7fe0fff

def z520 : W := mkw 0xffdbffed52000004 0xe7ff6fffb5480000 0xffffffff9c000003 0xe3fffffffe700000

def z521 : W := mkw 0x0900af8604853ed0 0x882402be181214fb 0x00001f8e00007fdc 0x2800007e380001ff

def z522 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0xc0fc78ffe063f1f5 0x4303f1e3ff818fc7

def z523 : W := mkw 0x0800240156836c10 0x04200090055a0db0 0xb8006701ff83fe3b 0xbee0019c07fe0ff8

def z524 : W := mkw 0xe4240013f262d182 0x179090004fc98b46 0xff000001ffe3f1f7 0x9ffc000007ff8fc7

def z525 : W := mkw 0x0209000001080000 0x0008240000042000 0x07038000039c0000 0x841c0e00000e7000

def z526 : W := mkw 0x374f8b863bbc36c8 0x4cdd3e2e18eef0db 0x7f1f9f8e7ffc7fde 0xfdfc7e7e39fff1ff

def z527 : W := mkw 0xf6ff0069fb78000c 0x77dbfc01a7ede000 0xffff8071fffc0003 0xd7fffe01c7fff000

def z528 : W := mkw 0xf6db504952024000 0x67db6d4125480900 0xfffff8ffff83f033 0xffffffe3fffe0fc0

def z529 : W := mkw 0x032d8b97e1eef7c2 0x180cb62e5f87bbdf 0x471f9f8fe3fffffe 0xfd1c7e7e3f8fffff

def z530 : W := mkw 0xf6df00017b380008 0x57db7c0005ece000 0xffff80007f9c0003 0xc7fffe0001fe7000

def z531 : W := mkw 0x00240013f262d182 0x140090004fc98b46 0x00000001ffe3f1f4 0x1c00000007ff8fc7

def z532 : W := mkw 0xc0b4505be97ad18a 0x3302d1416fa5eb46 0xc0fc78ffe07ff1f7 0x7b03f1e3ff81ffc7

def z533 : W := mkw 0x00240013e062d182 0x100090004f818b46 0x40001801e063f1f6 0x3900006007818fc7

def z534 : W := mkw 0xc890744804010800 0x232241d120100420 0xf8fc7fff9c038e2b 0xffe3f1fffe700e38

def z535 : W := mkw 0xc0b40011e0608100 0x1302d00047818204 0xc0fc60f1e06381e7 0x7b03f183c7818e07

def z536 : W := mkw 0xffdbffec04836c14 0xe3ff6fffb0120db0 0xffffffff9c03fe3b 0xfffffffffe700ff8

def z537 : W := mkw 0x366f0000bb780008 0x54d9bc0002ede000 0x3f0380001ffc0000 0x84fc0e00007ff000

def z538 : W := mkw 0xf6ff0000bb780008 0x57dbfc0002ede000 0xffff80001ffc0003 0xc7fffe00007ff000

def z539 : W := mkw 0xedb47e5be062d182 0xb3b6d1f96f818b46 0xfffc7fffe063f1f7 0xfbfff1ffff818fc7

def z540 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0xffffff7e00000001 0x83fffffdf8000000

def z541 : W := mkw 0x0090004800000000 0x2002400120000000 0x80fc60fe00000003 0x6203f183f8000000

def z542 : W := mkw 0x00240013e467dbc3 0x100090004f919f6f 0x00000001e063fffc 0x1800000007818fff

def z543 : W := mkw 0xed002e0156812c00 0x07b400b8055a04b0 0xff007f01ff83fe3b 0xbffc01fc07fe0ff8

def z544 : W := mkw 0x364b00001b180008 0x44d92c00006c6000 0xbf0380019f9c0003 0x96fc0e00067e7000

def z545 : W := mkw 0x12db81ed56836c14 0x644b6e07b55a0db0 0x00ff80ffff83fe38 0x5c03fe03fffe0ff8

def z546 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0xc0fc787fe003f031 0x0303f1e1ff800fc0

def z547 : W := mkw 0xe4b4505bf262d192 0xb792d1416fc98b46 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z548 : W := mkw 0x2d002e0016812c10 0x84b400b8005a04b0 0xbf0067019f838e2b 0xbefc019c067e0e38

def z549 : W := mkw 0xf6ff504bfb7a508a 0x77dbfd412fede942 0xfffff80ffffff033 0xffffffe03fffffc0

def z550 : W := mkw 0x0004000220201080 0x0000100008808042 0x00000000606071d4 0x18000000018181c7

def z551 : W := mkw 0xf7dbdbec00000004 0xe3df6f6fb0000000 0xffff98fe00000003 0xc3fffe63f8000000

def z552 : W := mkw 0xc0b40013e062d182 0x1302d0004f818b46 0xc0fc0001e063f1f7 0x5b03f00007818fc7

def z553 : W := mkw 0x1b4fafa62dbd3ec1 0x086d3ebe98b6f4fb 0x7f1f9f8e7ffc7fde 0xfdfc7e7e39fff1ff

def z554 : W := mkw 0xf6ff5059fb788108 0x77dbfd4167ede204 0xfffff8ffffff81e7 0xffffffe3fffffe07

def z555 : W := mkw 0x1062001088508100 0x0041880042214204 0xb8e3e0f19c7f81e7 0xfee38f83c671fe07

def z556 : W := mkw 0x346200009a500000 0x04d1880002694000 0xbfe380019ffc0003 0xd6ff8e00067ff000

def z557 : W := mkw 0xc0b4505aa0609180 0x2302d1416a818246 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z558 : W := mkw 0x00248193e066d3c2 0x100092064f819b4f 0x00038781e07ffffe 0xfc000e1e0781ffff

def z559 : W := mkw 0x344200001a100000 0x04d1080000684000 0x3f0380001f9c0000 0x84fc0e00007e7000

def z560 : W := mkw 0x344200001a100008 0x44d1080000684000 0x380000001c000000 0x00e0000000700000

def z561 : W := mkw 0xf6ff0001fb780008 0x57dbfc0007ede000 0xffff9801fffc7013 0xfffffe6007fff1c0

def z562 : W := mkw 0x13db8bec00000004 0x604f6e2fb0000000 0x47ff9ffe00000002 0xe11ffe7ff8000000

def z563 : W := mkw 0xffdbffed56812c14 0xe7ff6fffb55a04b0 0xffffffffff800e0b 0xf7fffffffffe0038

def z564 : W := mkw 0xd8d2746800000000 0x236349d1a0000000 0xf8fc78fe00000003 0x63e3f1e3f8000000

def z565 : W := mkw 0xf6fb0001db580008 0x57dbec00076d6000 0xffe38001ff9c0003 0x97ff8e0007fe7000

def z566 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0x401c180fe063f1f4 0x190070603f818fc7

def z567 : W := mkw 0xf6db00015b180008 0x47db6c00056c6000 0xffff8001ff9c0003 0xd7fffe0007fe7000

def z568 : W := mkw 0xfcd2746956034814 0xe7f349d1a5580d20 0xf8fc78fffc03f033 0x7be3f1e3fff00fc0

def z569 : W := mkw 0x0900ffa004876e51 0x802403fe80121db9 0x00007f000003fe38 0x280001fc00000ff8

def z570 : W := mkw 0x09002e0004812c10 0x802400b8001204b0 0x0000070000000e08 0x0000001c00000038

def z571 : W := mkw 0xfffffffff6e3fd96 0xf7ffffffffdb8ff6 0xffffffffffe3ffff 0xffffffffffff8fff

def z572 : W := mkw 0xffdbffed52024014 0xe7ff6fffb5480900 0xfffffffe00000003 0xe3fffffff8000000

def z573 : W := mkw 0xec00240156010800 0x07b0009005580420 0xff006701ff838e2b 0xbffc019c07fe0e38

def z574 : W := mkw 0xf6db00001b180008 0x47db6c00006c6000 0x7f1f80001f9c0000 0x85fc7e00007e7000

def z575 : W := mkw 0x03098b8400842640 0x000c262e10021099 0x471f9f8e63fc7fde 0xfd1c7e7e398ff1ff

def z576 : W := mkw 0x00240012a0609182 0x100090004a818246 0x00000001806381e4 0x1800000006018e07

def z577 : W := mkw 0xed907e4956836c12 0xb7b641f9255a0db0 0xff007f01ff83fe3b 0xbffc01fc07fe0ff8

def z578 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0x40fc78fe6063f1f4 0x6903f1e3f9818fc7

def z579 : W := mkw 0xd2ffd1ffe062d186 0x734bff47ff818b46 0xc0fff8ffe063f1f7 0x7b03ffe3ff818fc7

def z580 : W := mkw 0xf64b00015b180008 0x47d92c00056c6000 0xbf0380019f9c0001 0x86fc0e00067e7000

def z581 : W := mkw 0xf6ff0001fb7a4008 0x57dbfc0007ede900 0xffff8001fffff033 0xdffffe0007ffffc0

def z582 : W := mkw 0xffdbffec0d9d2e45 0xebff6fffb03674b9 0xfffffffe1f9c0e0b 0xe7fffffff87e7038

def z583 : W := mkw 0xc0b45059e062c102 0x3302d14167818b04 0xc0fc6071e0638023 0x5303f181c7818e00

def z584 : W := mkw 0xffdbffed52826414 0xe7ff6fffb54a0990 0xffffffffe383f033 0xfbffffffff8e0fc0

def z585 : W := mkw 0xed007e0156836c10 0x87b401f8055a0db0 0xff1c7f8fff83fe3b 0xfffc71fe3ffe0ff8

def z586 : W := mkw 0x1862a5b08c558b41 0x00618a96c231562d 0xb8e3e7f19c7f8fed 0xc6e38f9fc671fe3f

def z587 : W := mkw 0xf4f6505bfa72d18a 0x77d3d9416fe9cb46 0xf8fc78fffc63f1f7 0x7be3f1e3fff18fc7

def z588 : W := mkw 0x00240012a9fcb7c1 0x080090004aa7f2df 0x0000000063fc7fdc 0x1c000000018ff1ff

def z589 : W := mkw 0xffdbffec04812c14 0xe3ff6fffb01204b0 0xfffffffe00000e0b 0xe3fffffff8000038

def z590 : W := mkw 0xc090505b4002d182 0x230241416d000b46 0xc0fc78ffe003f1f7 0x7b03f1e3ff800fc7

def z591 : W := mkw 0x1866a5b3ec77dbc3 0x10619a96cfb1df6f 0x38038701fc7ffffc 0x9ce00e1c07f1ffff

def z592 : W := mkw 0x00240013e463d982 0x100090004f918f66 0x00000001fc63fffc 0x1c00000007f18fff

def z593 : W := mkw 0xffdbffec16836c14 0xe7ff6fffb05a0db0 0xfffffffe1f83fe3b 0xeffffffff87e0ff8

def z594 : W := mkw 0xed247e13fffbfd9a 0x97b491f84fffeff6 0xff007f01ffffffff 0xbffc01fc07ffffff

def z595 : W := mkw 0x104281a000000000 0x00410a0680000000 0x00e380f000000000 0x40038e03c0000000

def z596 : W := mkw 0x1afba5fc8c558b45 0x606bee97f231562d 0xb8ffe7ff9c7f8fef 0xfee3ff9ffe71fe3f

def z597 : W := mkw 0x00240013e1eaf582 0x180090004f87abd6 0x00000001e3e3f1f4 0x18000000078f8fc7

def z598 : W := mkw 0xf6ff005bfb7ad18a 0x77dbfc016fedeb46 0xffff80fffffff1f7 0xdffffe03ffffffc7

def z599 : W := mkw 0x0024505aa062d182 0x200091416a818b46 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z600 : W := mkw 0x3e4ba5a01f1d0a49 0x44f92e96807c7429 0x3f0387001f9c0e08 0x84fc0e1c007e7038

def z601 : W := mkw 0xed00ffed56836c14 0xa7b403ffb55a0db0 0xff007fffff83fe3b 0xbffc01fffffe0ff8

def z602 : W := mkw 0xf6ff0001fb780008 0x57dbfc0007ede000 0xffff988ffffc0003 0xf7fffe623ffff000

def z603 : W := mkw 0x00b4005be062d182 0x3002d0016f818b46 0x00fc00ffe063f1f4 0x5803f003ff818fc7

def z604 : W := mkw 0xf6ff0001fb780008 0x57dbfc0007ede000 0x7f1f8001fffc0000 0x95fc7e0007fff000

def z605 : W := mkw 0x00240013f36ad18a 0x140090004fcdab46 0x00000001e3e3f1f4 0x18000000078f8fc7

def z606 : W := mkw 0x00240013e16ad182 0x100090004f85ab46 0x00000001e3fff1f4 0x1c000000078fffc7

def z607 : W := mkw 0xc090504800000000 0x2302414120000000 0xc0fc78fe006001c7 0x7b03f1e3f8018007

def z608 : W := mkw 0xc0b40013e0609180 0x1302d0004f818246 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z609 : W := mkw 0xc090504800000000 0x2302414120000000 0xc0fc78ff80038023 0x7b03f1e3fe000e00

def z610 : W := mkw 0xffdbffed56034814 0xe7ff6fffb5580d20 0xfffffffffc03f033 0xfbfffffffff00fc0

def z611 : W := mkw 0xc090504800024000 0x2302414120000900 0xc0fc78fe0003f033 0x6b03f1e3f8000fc0

def z612 : W := mkw 0x00240013e066d3c2 0x100090004f819b4f 0x00000001e07ffffc 0x1c0000000781ffff

def z613 : W := mkw 0xf7dbdbcc00000000 0x63df6f6f30000000 0xfffffffe00000003 0xe3fffffff8000000

def z614 : W := mkw 0xc0b0505880408100 0x2302c14162010204 0xc0fc78ff806381e7 0x7b03f1e3fe018e07

def z615 : W := mkw 0x1a6fa5b0ad7d8b41 0x0069be96c2b5f62d 0xffffe7f1ffff8fef 0xffffff9fc7fffe3f

def z616 : W := mkw 0x36db81ec1b18000c 0x64db6e07b06c6000 0x3fff80fe1f9c0000 0xc4fffe03f87e7000

def z617 : W := mkw 0xfedbf5ec00000004 0xe3fb6fd7b0000000 0xb8ffe7fe00000003 0xe2e3ff9ff8000000

def z618 : W := mkw 0x1bdbffec00000004 0xe06f6fffb0000000 0x47fffffe00000002 0xe11ffffff8000000

def z619 : W := mkw 0xe4b40001f2600000 0x1792d00007c98000 0xfffc0001ffe00003 0xd7fff00007ff8000

def z620 : W := mkw 0x029981cc00000000 0x200a660730000000 0x00ff80fe00000000 0x4003fe03f8000000

def z621 : W := mkw 0x01048b8220a436c0 0x0004122e088290db 0x471f9f8e63fc7fde 0xfd1c7e7e398ff1ff

def z622 : W := mkw 0xdbdbffec00000000 0x236f6fffb0000000 0xfffffffe00000003 0xe3fffffff8000000

def z623 : W := mkw 0x00240000a9780008 0x1000900002a5e000 0x00000000007c0000 0x000000000001f000

def z624 : W := mkw 0xe799dbcc00000004 0xe39e676f30000000 0xc7fffffe00000003 0xe31ffffff8000000

def z625 : W := mkw 0xc8b4f5fbe467dbc3 0x3322d3d7ef919f6f 0xc0fc7fffe063ffff 0x7b03f1ffff818fff

def z626 : W := mkw 0xf4f60001fa700000 0x17d3d80007e9c000 0xffff8001fffc0003 0xd7fffe0007fff000

def z627 : W := mkw 0xffdbffec0918000c 0xe3ff6fffb0246000 0xfffffffe001c0003 0xe3fffffff8007000

def z628 : W := mkw 0x12db81ec00000004 0x604b6e07b0000000 0x40ff98fe00000002 0x6103fe63f8000000

def z629 : W := mkw 0x030d8b8621ac36c0 0x080c362e1886b0db 0xc71fff8fe3ffffff 0xff1c7ffe3f8fffff

def z630 : W := mkw 0x3f4bafa41b18000c 0xc4fd2ebe906c6000 0x3f0387001f9c0000 0x84fc0e1c007e7000

def z631 : W := mkw 0x1866a5b2ac759bc1 0x00619a96cab1d66f 0xf8fffffffc7fffff 0xffe3fffffff1ffff

def z632 : W := mkw 0xffdbffec04050a45 0xe3ff6fffb0101429 0xfffffffe00000e0b 0xe3fffffff8000038

def z633 : W := mkw 0xc0b05059c042c100 0x2302c14167010b04 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z634 : W := mkw 0xc094505b6022d182 0x330251416d808b46 0xc0fc78fe6003f1f7 0x6b03f1e3f9800fc7

def z635 : W := mkw 0xed007e0156836c10 0x87b401f8055a0db0 0xff007f81ffe3ffff 0xfffc01fe07ff8fff

def z636 : W := mkw 0xfd42ffa156836c10 0x87f50bfe855a0db0 0xffe3fff1ff83fe3b 0xffff8fffc7fe0ff8

def z637 : W := mkw 0x09007e4804836c10 0xa02401f920120db0 0x00007ffe0003fe38 0x280001fff8000ff8

def z638 : W := mkw 0xc0240013e062d182 0x130090004f818b46 0xc0000001e063f1f7 0x1b00000007818fc7

def z639 : W := mkw 0xf6ff5001fb7a4008 0x57dbfd4007ede900 0xffffe001ffff8023 0xd7ffff8007fffe00

def z640 : W := mkw 0xe5905a4952826410 0xa7964169254a0990 0x471c180e63807010 0x011c7060398e01c0

def z641 : W := mkw 0xc990ffed44836c14 0xa32643ffb5120db0 0xc0fc7fffe003fe3b 0x7b03f1ffff800ff8

def z642 : W := mkw 0xffdbffec1e952e55 0xe7ff6fffb07a54b9 0xfffffffe1f9c0e0b 0xe7fffffff87e7038

def z643 : W := mkw 0xc0b05059c042c102 0x3302c14167010b04 0xc0fc78ff80038023 0x6303f1e3fe000e00

def z644 : W := mkw 0xc090504940024002 0x3302414125000900 0xc0fc78fe00000003 0x6303f1e3f8000000

def z645 : W := mkw 0xffdbffec0c110805 0xe3ff6fffb0304420 0xfffffffe1c000003 0xe3fffffff8700000

def z646 : W := mkw 0xc1905a4800802400 0x2306416920020090 0xc7fc7ffe63807e1b 0xff1ff1fff98e01f8

def z647 : W := mkw 0xf6ff0000a9780000 0x43dbfc0002a5e000 0xffff8001fffc0003 0xd7fffe0007fff000

def z648 : W := mkw 0xfdd27e6956836c14 0xe7f749f9a55a0db0 0xffe07f71ff83fe3b 0xbfff81fdc7fe0ff8

def z649 : W := mkw 0xf7dbdbec00000004 0xe3df6f6fb0000000 0x47ff9ffe00000002 0xe11ffe7ff8000000

def z650 : W := mkw 0xc0b4504be0625082 0x3302d1412f818942 0xc0fc180fe0607013 0x5303f0603f8181c0

def z651 : W := mkw 0xe490504952000000 0x2792414125480000 0xfffc78ffff800003 0xf7fff1e3fffe0000

def z652 : W := mkw 0xfdd27e6800000004 0xe3f749f9a0000000 0xfffc7ffe00000003 0xe3fff1fff8000000

def z653 : W := mkw 0x364b00001b180008 0x44d92c00006c6000 0x3f0380001ffc0002 0xd4fc0e00007ff000

def z654 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0xc0fff8ffe07ff1f7 0xff03ffe3ff81ffc7

def z655 : W := mkw 0xff4bffa400000000 0x83fd2ffe90000000 0xfffffffe00000003 0xe3fffffff8000000

def z656 : W := mkw 0x3e6ba5b09f5d8b49 0x44f9ae96c27d762d 0xbfe3e7f19fff8fef 0xfeff8f9fc67ffe3f

def z657 : W := mkw 0xd2ff505be97ad18a 0x734bfd416fa5eb46 0xc0fff8ffe07ff1f7 0x7b03ffe3ff81ffc7

def z658 : W := mkw 0x0b0dff8625af7ed0 0x882c37fe1896bdfb 0x471fff8e63fffffe 0xfd1c7ffe398fffff

def z659 : W := mkw 0x00240013f2e2f592 0x140090004fcb8bd6 0x00000001e3e3f1f4 0x18000000078f8fc7

def z660 : W := mkw 0xffdbffed56836c14 0xe7ff6fffb55a0db0 0xfffffffe6383fe3b 0xebfffffff98e0ff8

def z661 : W := mkw 0xc299d1cc00000000 0x230a674730000000 0xc0fff8fe00000003 0x6303ffe3f8000000

def z662 : W := mkw 0xc090504940024000 0x2302414125000900 0xc0fc78fe60007013 0x6303f1e3f98001c0

def z663 : W := mkw 0x03998bcc00000000 0x200e662f30000000 0x47ff9ffe00000002 0xe11ffe7ff8000000

def z664 : W := mkw 0xef9dffcf77af7ed0 0xafbe77ff3ddebdfb 0xffffffffffffffff 0xffffffffffffffff

def z665 : W := mkw 0xed00ff8756877ed0 0x8fb403fe1d5a1dfb 0xff007f8fff83ffff 0xbffc01fe3ffe0fff

def z666 : W := mkw 0xffdbffed52802404 0xe7ff6fffb54a0090 0xffffffffff807e1b 0xfffffffffffe01f8

def z667 : W := mkw 0xf6ff0011fb788108 0x57dbfc0047ede204 0xffff8001ffff81e7 0xdffffe0007fffe07

def z668 : W := mkw 0x36ff0000bb780008 0x54dbfc0002ede000 0xbfff80019ffc0003 0xd6fffe00067ff000

def z669 : W := mkw 0x3f4bffec00000004 0xe0fd2fffb0000000 0x3f03fffe00000000 0xa0fc0ffff8000000

def z670 : W := mkw 0xe400000152000000 0x0790000005480000 0xff038001fffc0003 0xd7fc0e0007fff000

def z671 : W := mkw 0x364f00023b381088 0x44d93c0008ece042 0x7f1f988e7ffc71d6 0xfdfc7e6239fff1c7

def z672 : W := mkw 0xffdbfffe0002d186 0xe3ff6ffff8000b46 0xfffffffe0003f1f7 0xebfffffff8000fc7

def z673 : W := mkw 0xc090d1c800000000 0x2302434720000000 0xc0fffffe00000003 0xe303fffff8000000

def z674 : W := mkw 0x36df00003b380008 0x54db7c0000ece000 0x3f1f80001f9c0000 0x84fc7e00007e7000

def z675 : W := mkw 0xed007e4d56836c14 0xa7b401f9355a0db0 0xff007f0fff83fe3b 0xbffc01fc3ffe0ff8

def z676 : W := mkw 0xffdb7e6c00000004 0xe3ff6df9b0000000 0xfffc7f7e00000003 0xa3fff1fdf8000000

def z677 : W := mkw 0x3f4bafa40d9d2e45 0xc8fd2ebe903674b9 0x3f0387001f9c0e08 0x84fc0e1c007e7038

def z678 : W := mkw 0xffdbffec00802404 0xe3ff6fffb0020090 0xfffffffe63807013 0xe3fffffff98e01c0

def z679 : W := mkw 0x0004505a2022d182 0x2000114168808b46 0x401c78fe6063f1f6 0x790071e3f9818fc7

def z680 : W := mkw 0x364b00001b180008 0x44d92c00006c6000 0x7f0380007f9c0002 0x95fc0e0001fe7000

def z681 : W := mkw 0xc0b4d1dbe066d3c2 0x3302d3476f819b4f 0xc0ffffffe07fffff 0xff03ffffff81ffff

def z682 : W := mkw 0x364f00003b380008 0x44d93c0000ece000 0x3f1f80001ffc0000 0xc4fc7e00007ff000

def z683 : W := mkw 0xfdd2ffec00000004 0xe3f74bffb0000000 0xf8fc7ffe00000003 0x63e3f1fff8000000

def z684 : W := mkw 0xffdbafa400000000 0x43ff6ebe90000000 0xfffffffe00000003 0xe3fffffff8000000

def z685 : W := mkw 0xffdbffec00802404 0xe3ff6fffb0020090 0xfffffffe00007e1b 0xebfffffff80001f8

def z686 : W := mkw 0xd0d2504800000000 0x2343494120000000 0xf8fff8fe00000003 0xe3e3ffe3f8000000

def z687 : W := mkw 0xc1905a4800000000 0x2306416920000000 0xc7fc7ffe00000003 0xe31ff1fff8000000

def z688 : W := mkw 0xe5b45a5bf2e2f592 0xb796d1696fcb8bd6 0xc7fc78ffe3e3f1f7 0x7b1ff1e3ff8f8fc7

def z689 : W := mkw 0x12ff81fea97c93c3 0x384bfe07faa5f24f 0x00ff80fe007c01c4 0x4003fe03f801f007

def z690 : W := mkw 0xc000505b4002d182 0x230001416d000b46 0xc00078ffe003f1f7 0x3b0001e3ff800fc7

def z691 : W := mkw 0x364b00015b180008 0x44d92c00056c6000 0x3f038001ff9c0000 0x94fc0e0007fe7000

def z692 : W := mkw 0x1b6bafb48c558b41 0x006daebed231562d 0xffffffff9c7f8fef 0xfffffffffe71fe3f

def z693 : W := mkw 0xc0b4505bf36ad18a 0x3702d1416fcdab46 0xc0fc78ffe3e3f1f7 0x7b03f1e3ff8f8fc7

def z694 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0xfffffffe007c0003 0xf7fffffff801f000

def z695 : W := mkw 0xc0b4505be872d182 0x3302d1416fa1cb46 0xc0fc78fffc7ff1f7 0x7f03f1e3fff1ffc7

def z696 : W := mkw 0x124b81a400000004 0x40492e0690000000 0x0003800000000000 0x00000e0000000000

def z697 : W := mkw 0xffdbffec08100004 0xe3ff6fffb0204000 0xfffffffe1c1c0003 0xe7fffffff8707000

def z698 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0x00000001e063f1f4 0x1800000007818fc7

def z699 : W := mkw 0xc090504800000000 0x2302414120000000 0x80fc60fe00000001 0x4203f183f8000000

def z700 : W := mkw 0xfcf6747be062d186 0xf3f3d9d1ef818b46 0xf8fc78ffe063f1f7 0x7be3f1e3ff818fc7

def z701 : W := mkw 0xffdbffec010c0244 0xebff6fffb0043009 0xfffffffe001c0003 0xe3fffffff8007000

def z702 : W := mkw 0xf6ff004bfb78108a 0x77dbfc012fede042 0xffff800ffffc0003 0xd7fffe003ffff000

def z703 : W := mkw 0x00240013fb78918a 0x140090004fede246 0x00000001fffc01c4 0x1400000007fff007

def z704 : W := mkw 0x1862a5b08c558b41 0x00618a96c231562d 0xb8e3e7719c7f8fed 0x9ee38f9dc671fe3f

def z705 : W := mkw 0xf6ff504bfb7a508a 0x77dbfd412fede942 0xffff988ffffc71d7 0xfffffe623ffff1c7

def z706 : W := mkw 0xf6ff0059fb78810a 0x77dbfc0167ede204 0xffff8071fffc0003 0xd7fffe01c7fff000

def z707 : W := mkw 0x1a6fa5b6ad7d9bc1 0x0869be96dab5f66f 0xb8ffe7ff9c7f8fef 0xfee3ff9ffe71fe3f

def z708 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0x40fc18fe606071d4 0x4103f063f98181c7

def z709 : W := mkw 0xf6ff5013fb7ad18a 0x57dbfd404fedeb46 0xfffff801fffff1f7 0xffffffe007ffffc7

def z710 : W := mkw 0xf6ff0031fb788109 0x57dbfc00c7ede204 0xffff8071fffc0003 0xd7fffe01c7fff000

def z711 : W := mkw 0xffdbffec16812c14 0xe7ff6fffb05a04b0 0xfffffffe7f807e1b 0xfffffffff9fe01f8

def z712 : W := mkw 0x366f0001fb780008 0x54d9bc0007ede000 0x7f1f8001fffc0002 0xd5fc7e0007fff000

def z713 : W := mkw 0x0004818221ac36c0 0x080012060886b0db 0x0003878063fc7fde 0xfc000e1e018ff1ff

def z714 : W := mkw 0xed247e13e062d182 0x93b491f84f818b46 0xff007f01e063f1f7 0xbbfc01fc07818fc7

def z715 : W := mkw 0xc000500000000000 0x0300014000000000 0xc000780000000003 0x230001e000000000

def z716 : W := mkw 0xf4d2504800000000 0x63d3494120000000 0xf8fc78fe00000003 0x63e3f1e3f8000000

def z717 : W := mkw 0x12fb81fc88548345 0x604bee07f221520d 0x00ff80fe007c01c4 0x4003fe03f801f007

def z718 : W := mkw 0x082024108c558b41 0x002080904231562d 0xb80067019c7f8fef 0xbee0019c0671fe3f

def z719 : W := mkw 0xe7995a4c00000004 0xe39e656930000000 0x47fc18fe00000000 0x411ff063f8000000

def z720 : W := mkw 0xffdbffed56836c14 0xe7ff6fffb55a0db0 0xffffffffff83f033 0xe3fffffffffe0fc0

def z721 : W := mkw 0xd2ff505be97ad182 0x334bfd416fa5eb46 0xfffff8fffffff1f7 0xffffffe3ffffffc7

def z722 : W := mkw 0x12ff81b0a97c8349 0x504bfe06c2a5f20d 0x00ff80f0007c01c4 0x4003fe03c001f007

def z723 : W := mkw 0xffdb7e0156836c10 0xc7ff6df8055a0db0 0xffffff01ff83fe3b 0xfffffffc07fe0ff8

def z724 : W := mkw 0xf6db81ed52000004 0x67db6e07b5480000 0xffff80ffff800003 0xd7fffe03fffe0000

def z725 : W := mkw 0xfefff5fbff7fdbcb 0x77fbffd7effdff6f 0xffffffffffffffff 0xffffffffffffffff

def z726 : W := mkw 0xffffffedfffb6c1c 0xf7ffffffb7ffedb0 0xfffffffffffffe3b 0xfffffffffffffff8

def z727 : W := mkw 0xed007e0004836c10 0x83b401f800120db0 0xff007f000003fe3b 0xabfc01fc00000ff8

def z728 : W := mkw 0x12ff81fea0609186 0x704bfe07fa818246 0x00ff80fe006001c4 0x4003fe03f8018007

def z729 : W := mkw 0xc3995a4c00000000 0x230e656930000000 0xc7fc78fe00000003 0x631ff1e3f8000000

def z730 : W := mkw 0x0900af8404852e50 0x882402be101214b9 0x0000070000000e08 0x0000001c00000038

def z731 : W := mkw 0xffdbffed56836c14 0xe7ff6fffb55a0db0 0xffffffff9c03fe3b 0xebfffffffe700ff8

def z732 : W := mkw 0xc0b40003e0601080 0x1302d0000f818042 0xc0fc188fe06071d7 0x7b03f0623f8181c7

def z733 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0x7fff9ffe00000000 0xc1fffe7ff8000000

def z734 : W := mkw 0xffdbffec00040244 0xe3ff6fffb0001009 0xfffffffe007c01c7 0xe3fffffff801f007

def z735 : W := mkw 0xf4f20001da500008 0x57d3c80007694000 0xffe38001fffc0003 0xd7ff8e0007fff000

def z736 : W := mkw 0xc299504c00000004 0x630a654130000000 0xc0fc78fe00000003 0x6303f1e3f8000000

def z737 : W := mkw 0x0090505a0002d182 0x2002414168000b46 0x00fc78fe0003f1f4 0x6803f1e3f8000fc7

def z738 : W := mkw 0xdadbf5ec00000004 0x636b6fd7b0000000 0xf8fffffe00000003 0xe3e3fffff8000000

def z739 : W := mkw 0x0020001080408100 0x0000800042010204 0x00000001806381e4 0x1800000006018e07

def z740 : W := mkw 0x1b4fafa621ac36c0 0x086d3ebe9886b0db 0xfffffffe63fc7fdf 0xfffffffff98ff1ff

def z741 : W := mkw 0xd8d2f5e944034800 0x23634bd7a5100d20 0xf8fffffffc03fe3b 0xffe3fffffff00ff8

def z742 : W := mkw 0x00240013e062d182 0x100090004f818b46 0x00000000606071d4 0x00000000018181c7

def z743 : W := mkw 0x364f00017b380008 0x54d93c0005ece000 0x3f0380007f9c0000 0x84fc0e0001fe7000

def z744 : W := mkw 0xed007e0156836c10 0x87b401f8055a0db0 0xff007f01ff83fe39 0x87fc01fc07fe0ff8

def z745 : W := mkw 0xd2db81ec00000004 0x634b6e07b0000000 0xc0ff80fe00000003 0x4303fe03f8000000

def z746 : W := mkw 0xc0245013e062d180 0x030091404f818b46 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z747 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0xfffffffe006001c7 0xfbfffffff8018007

def z748 : W := mkw 0xffdbffed5200000c 0xf7ff6fffb5480000 0xfffffffe00000003 0xe3fffffff8000000

def z749 : W := mkw 0xffdbffed40024006 0xf3ff6fffb5000900 0xfffffffe00000003 0xe3fffffff8000000

def z750 : W := mkw 0xfedbf5ec00000004 0xe3fb6fd7b0000000 0xffffe0fe00000003 0xc3ffff83f8000000

def z751 : W := mkw 0x3f4bafa400000004 0xc0fd2ebe90000000 0xfffffffe00000003 0xe3fffffff8000000

def z752 : W := mkw 0xfdd2ffe956836c10 0xa7f74bffa55a0db0 0xffffffffff83fe3b 0xfffffffffffe0ff8

def z753 : W := mkw 0x00b4505aa062d182 0x3002d1416a818b46 0x40fc78fe6063f1f6 0x7903f1e3f9818fc7

def z754 : W := mkw 0xc1245a13e1eef7c2 0x1b0491684f87bbdf 0xc7007f01e3ffffff 0xbf1c01fc078fffff

def z755 : W := mkw 0x136f8bb6a9fcb7c1 0x084dbe2edaa7f2df 0x47ff9ffe63fc7fde 0xfd1ffe7ff98ff1ff

def z756 : W := mkw 0x0900fffa0487ffd3 0xa02403ffe8121fff 0x00007ffe0003fffc 0x280001fff8000fff

def z757 : W := mkw 0xc0b4505bf262d182 0x3702d1416fc98b46 0xc0fc78ffffe3f1f7 0x7f03f1e3ffff8fc7

def z758 : W := mkw 0xed007e0156836c10 0x87b401f8055a0db0 0xff03ff01fffffe3b 0xfffc0ffc07fffff8

def z759 : W := mkw 0x2400000012000000 0x0490000000480000 0x3f0000001f800000 0x84fc0000007e0000

def z760 : W := mkw 0xc0b45049e0600000 0x3302d14127818000 0xc0fc78ffe0600003 0x7303f1e3ff818000

def z761 : W := mkw 0xf6ff505bfb78918a 0x77dbfd416fede246 0xfffff8fffffc01c7 0xf7ffffe3fffff007

def z762 : W := mkw 0x032d8b97e1eef7c2 0x180cb62e5f87bbdf 0x07038701e3fffffc 0x9c1c0e1c078fffff

def z763 : W := mkw 0x1bdbffec04836c14 0xe06f6fffb0120db0 0x00fffffe0003fe38 0x6803fffff8000ff8

def z764 : W := mkw 0x0900fffe0487ffc3 0x282403fff8121fff 0x00007ffe0003fffc 0x280001fff8000fff

def z765 : W := mkw 0xc0b0505bc042d182 0x3302c1416f010b46 0xc0fc78ff8003f1f7 0x6b03f1e3fe000fc7

def z766 : W := mkw 0x366b00109b588108 0x44d9ac00426d6204 0xbfe3e0f19fff81e7 0xfeff8f83c67ffe07

def z767 : W := mkw 0x020d8182212c12c0 0x000836060884b04b 0x471f9f8e63fc7fde 0xfd1c7e7e398ff1ff

def z768 : W := mkw 0x3f4bafa41f9d2e49 0x4cfd2ebe907e74b9 0x3f0387001f9c0e08 0x84fc0e1c007e7038

def z769 : W := mkw 0xe5005a0156836c10 0x87940168055a0db0 0x47001801ff83fe38 0x1d1c006007fe0ff8

def z770 : W := mkw 0x0800240004010800 0x0020009000100420 0xb8e067f19c038e2b 0xfee3819fc6700e38

def z771 : W := mkw 0x00245013e062d182 0x100091404f818b46 0x00007801e063f1f4 0x380001e007818fc7

def z772 : W := mkw 0x0b0dafb625adbfc1 0x082c36bed896b6ff 0x471ffffe63fffffe 0xfd1c7ffff98fffff

def z773 : W := mkw 0xf44200015a100000 0x07d1080005684000 0xff038001ff9c0003 0x97fc0e0007fe7000

def z774 : W := mkw 0xc090504940000000 0x2302414125000000 0xc0fc78ffe0000003 0x7303f1e3ff800000

def z775 : W := mkw 0xfedbf5ec00000004 0xe3fb6fd7b0000000 0xf8fff8fe00000003 0x63e3ffe3f8000000

def z776 : W := mkw 0xc399dbcc018c2640 0x2b0e676f30063099 0xc7fffffe039c0e0b 0xe71ffffff80e7038

def z777 : W := mkw 0x12db81ec00000004 0x604b6e07b0000000 0x47ff80fe00000002 0xc11ffe03f8000000

def z778 : W := mkw 0xe5000a0152802400 0x07940028054a0090 0xff001f01ff807e1b 0xbffc007c07fe01f8

def z779 : W := mkw 0xed002e0156812c10 0x87b400b8055a04b0 0xff000701ff800e0b 0x97fc001c07fe0038

def z780 : W := mkw 0xed247e01fffb6c18 0x97b491f807ffedb0 0xff007f01fffffe3b 0xbffc01fc07fffff8

def z781 : W := mkw 0x12dbd1ec00000004 0x604b6f47b0000000 0x00fff8fe00000000 0x6003ffe3f8000000

def z782 : W := mkw 0x1bdbffec00000004 0xe06f6fffb0000000 0xb8fffffe00000003 0xe2e3fffff8000000

def z783 : W := mkw 0xffdbffed5e976e55 0xe7ff6fffb57a5db9 0xffffffffff9ffe3b 0xfffffffffffe7ff8

def z784 : W := mkw 0xffdb7e4956836c10 0xe7ff6df9255a0db0 0xffffffffff83fe3b 0xfffffffffffe0ff8

def z785 : W := mkw 0x1adba5ec04010804 0x606b6e97b0100420 0xb8ffe7ff9c038e2b 0xfee3ff9ffe700e38

def z786 : W := mkw 0x12ff8186a97c12c8 0x584bfe061aa5f04b 0x00ff808e007c01c4 0x4003fe023801f007

def z787 : W := mkw 0xd2db504800000000 0x634b6d4120000000 0xc0fff8fe00000003 0x6303ffe3f8000000

def z788 : W := mkw 0xc0b05059c042c102 0x3302c14167010b04 0x80e0607180038021 0x02038181c6000e00

def z789 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0xffffffff80038023 0xfbfffffffe000e00

def z790 : W := mkw 0x12ff81faa97c93cb 0x704bfe07eaa5f24f 0x00ff80fe007c01c4 0x4003fe03f801f007

def z791 : W := mkw 0x030d8b8621ac36c0 0x080c362e1886b0db 0xff1f9f8ffffc7fdf 0xfffc7e7e3ffff1ff

def z792 : W := mkw 0xf7dbdbed52826414 0xe7df6f6fb54a0990 0x47ff98fe63807010 0x411ffe63f98e01c0

def z793 : W := mkw 0xf6ff0001fb780008 0x57dbfc0007ede000 0xffffe001ffff8023 0xffffff8007fffe00

def z794 : W := mkw 0xf6ff0001fb780008 0x57dbfc0007ede000 0xffff8701fffc0e0b 0xfffffe1c07fff038

def z795 : W := mkw 0x00240013e97ad18a 0x100090004fa5eb46 0x00000001e07ff1f4 0x180000000781ffc7

def z796 : W := mkw 0xe609000153080000 0x07982400054c2000 0xff038001ff9c0003 0x97fc0e0007fe7000

def z797 : W := mkw 0x08242413e463d982 0x102090904f918f66 0xb8006701fc63ffff 0xbee0019c07f18fff

def z798 : W := mkw 0xed207e11ded7ef51 0x87b481f8477b5fbd 0xff007f01ffffffff 0xbffc01fc07ffffff

def z799 : W := mkw 0x00240013e062d182 0x100090004f818b46 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z800 : W := mkw 0xed90ffec00000004 0xa3b643ffb0000000 0xfffc7ffe00000003 0xe3fff1fff8000000

def z801 : W := mkw 0xf6ff505bfb7ad18a 0x77dbfd416fedeb46 0xfffff87ffffff033 0xd7ffffe1ffffffc0

def z802 : W := mkw 0x1842a5a000000000 0x00610a9680000000 0xf8fffffe00000003 0xe3e3fffff8000000

def z803 : W := mkw 0x0b0daf8625ad3ec0 0x082c36be1896b4fb 0xff1fff8fffffffff 0xfffc7ffe3fffffff

def z804 : W := mkw 0xed007e0000802400 0x83b401f800020090 0xff007f0063807e1b 0xbffc01fc018e01f8

def z805 : W := mkw 0xe70d8b8773ac36c0 0x0f9c362e1dceb0db 0xff1f9f8ffffc7fdf 0xfffc7e7e3ffff1ff

def z806 : W := mkw 0xed007e0156836c10 0x87b401f8055a0db0 0x7f001f007f807e18 0x85fc007c01fe01f8

def z807 : W := mkw 0xc920ffb1c4c7ef51 0x832483fec7131fbd 0xc0e07ff1e063ffff 0x7b0381ffc7818fff

def z808 : W := mkw 0x36ff0000bb780008 0x54dbfc0002ede000 0x7fff80007ffc0002 0xd5fffe0001fff000

def z809 : W := mkw 0xf6ff0003fb781088 0x57dbfc000fede042 0xffff980ffffc7013 0xd7fffe603ffff1c0

def z810 : W := mkw 0x1842a5a000040240 0x00610a9680001009 0xb8e3e7f0007c0fcf 0xfee38f9fc001f03f

def z811 : W := mkw 0x00240001e0600000 0x1000900007818000 0x00000001e0600000 0x1000000007818000

def z812 : W := mkw 0x126f0001fb780008 0x1449bc0007ede000 0xffff8001fffc0003 0xd7fffe0007fff000

def z813 : W := mkw 0xffdbffed40024004 0xe3ff6fffb5000900 0xfffffffe60007013 0xe3fffffff98001c0

def z814 : W := mkw 0x3fdbffec00000004 0xe0ff6fffb0000000 0x3ffffffe00000000 0xe0fffffff8000000

def z815 : W := mkw 0xf6db00015b180008 0x57db6c00056c6000 0x3f0380001f9c0000 0x84fc0e00007e7000

def z816 : W := mkw 0x366f0000bb780008 0x44d9bc0002ede000 0xffff8001fffc0003 0xd7fffe0007fff000

def z817 : W := mkw 0x10d281e800000000 0x20434a07a0000000 0x00ff80fe00000000 0x4003fe03f8000000

def z818 : W := mkw 0x00240013e062d182 0x100090004f818b46 0x00000001806381e4 0x0000000006018e07

def z819 : W := mkw 0xe69d000173280008 0x579a740005cca000 0xff1f8001fffc0003 0xd7fc7e0007fff000

def z820 : W := mkw 0x1846a5a221ac36c0 0x08611a968886b0db 0xb8e3e7f063fc7fdf 0xfee38f9fc18ff1ff

def z821 : W := mkw 0x364f00003b380008 0x44d93c0000ece000 0x7f1f80007f9c0000 0x85fc7e0001fe7000

def z822 : W := mkw 0xffdbffed52826414 0xe7ff6fffb54a0990 0xfffffffe63807e1b 0xfffffffff98e01f8

def z823 : W := mkw 0xf6fb0001db580008 0x57dbec00076d6000 0xffff80019f9c0003 0xc7fffe00067e7000

def z824 : W := mkw 0xd9d2ffec00000004 0xa3674bffb0000000 0xf8fffffe00000003 0xe3e3fffff8000000

def z825 : W := mkw 0x3fdbafec00000004 0xe0ff6ebfb0000000 0xbfffe7fe00000003 0xe2ffff9ff8000000

def z826 : W := mkw 0x00b4505be062d182 0x3002d1416f818b46 0x00fc78ffe063f1f4 0x7803f1e3ff818fc7

def z827 : W := mkw 0xffdbffec01882404 0xebff6fffb0062090 0xfffffffe03800003 0xe3fffffff80e0000

def z828 : W := mkw 0xef0d7e0177ab6c10 0x87bc35f805deadb0 0xff1fff01fffffe3b 0xfffc7ffc07fffff8

def z829 : W := mkw 0xed947e4b76a37c92 0xb7b651f92dda8df2 0xff1c7f0fff83fe3b 0xbffc71fc3ffe0ff8

def z830 : W := mkw 0x12db81ec0918000c 0x604b6e07b0246000 0x00ff80fe001c0000 0x4003fe03f8007000

def z831 : W := mkw 0xc090504800000000 0x2302414120000000 0xc0fc78fe60007013 0x7b03f1e3f98001c0

def z832 : W := mkw 0xffff7e49fffb6c18 0xf7fffdf927ffedb0 0xfffffffffffffe3b 0xfffffffffffffff8

def z833 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0fc78fe00000003 0x6303f1e3f8000000

def z834 : W := mkw 0x12ff81fea97c93c5 0x684bfe07faa5f24f 0x00ff80fe007c01c4 0x4003fe03f801f007

def z835 : W := mkw 0x1b4bffec00000004 0xa06d2fffb0000000 0xfffffffe00000003 0xe3fffffff8000000

def z836 : W := mkw 0x0299004c00000004 0x600a640130000000 0x00fc00fe00000000 0x4003f003f8000000

def z837 : W := mkw 0xd0d2d1e800000000 0x23434b47a0000000 0xc0fff8fe00000003 0x6303ffe3f8000000

def z838 : W := mkw 0x13dbdbec00000004 0xe04f6f6fb0000000 0x00ff98fe00000000 0x4003fe63f8000000

def z839 : W := mkw 0x126b000089580000 0x0049ac0002256000 0xbfe380019ffc0003 0xd6ff8e00067ff000

def z840 : W := mkw 0xc1905a4c00000004 0xa306416930000000 0xc0fc78fe00000003 0x6303f1e3f8000000

def z841 : W := mkw 0xffdbffec018c2644 0xebff6fffb0063099 0xfffffffe639c7e1b 0xfffffffff98e71f8

def z842 : W := mkw 0xf6ff0007fb781088 0x5fdbfc001fede042 0xffff800ffffc0003 0xd7fffe003ffff000

def z843 : W := mkw 0x2d002e0000000000 0x80b400b800000000 0x3f00070000000000 0x80fc001c00000000

def z844 : W := mkw 0x09007e0156836c10 0x842401f8055a0db0 0x00007f01ff83fe38 0x3c0001fc07fe0ff8

def z845 : W := mkw 0x00240013e062d182 0x100090004f818b46 0x80e060f1e063f1f7 0x7a038183c7818fc7

def z846 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0xf8fc78fffc63f1f7 0xffe3f1e3fff18fc7

def z847 : W := mkw 0x00b4005aa0609182 0x3002d0016a818246 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z848 : W := mkw 0xc0b4505be16ad182 0x3302d1416f85ab46 0xc0fc78ffe3fff1f7 0x7f03f1e3ff8fffc7

def z849 : W := mkw 0xed002e0156836c10 0x87b400b8055a0db0 0xff000701ff83fe3b 0x9ffc001c07fe0ff8

def z850 : W := mkw 0x12ff0000a9780008 0x504bfc0002a5e000 0xffff8001fffc0003 0xd7fffe0007fff000

def z851 : W := mkw 0x12db81ec00040244 0x604b6e07b0001009 0x00ff80fe007c01c4 0x4003fe03f801f007

def z852 : W := mkw 0x0020505a8042d182 0x200081416a010b46 0x80e078ff8063f1f7 0x7a0381e3fe018fc7

def z853 : W := mkw 0x1962afb68cd5bfc1 0x08658abeda3356ff 0xb8e3ffff9c7fffff 0xfee38ffffe71ffff

def z854 : W := mkw 0x0990ffec00000004 0xa02643ffb0000000 0x00fc7ffe00000000 0x6003f1fff8000000

def z855 : W := mkw 0x366b0001db580008 0x54d9ac00076d6000 0x3f0380019f9c0000 0x84fc0e00067e7000

def z856 : W := mkw 0xffdbffec04010804 0xe3ff6fffb0100420 0xfffffffe00038e2b 0xebfffffff8000e38

def z857 : W := mkw 0xf6ff0013fb7ad18a 0x57dbfc004fedeb46 0xffffe0f1fffff1f7 0xffffff83c7ffffc7

def z858 : W := mkw 0x260d000033280000 0x0498340000cca000 0x7f1f80007ffc0002 0xd5fc7e0001fff000

def z859 : W := mkw 0x1862a5b08c558b41 0x00618a96c231562d 0xb8e3e7f19c7f8fed 0x6ae38f9fc671fe3f

def z860 : W := mkw 0xf6ff5049fb780008 0x77dbfd4127ede000 0xffff980ffffc0003 0xd7fffe603ffff000

def z861 : W := mkw 0xef997e4d56836c14 0xe7be65f9355a0db0 0xff1c7f0fff83fe3b 0xbffc71fc3ffe0ff8

def z862 : W := mkw 0x009081ec00000004 0x20024207b0000000 0x00fc00fe00000000 0x4003f003f8000000

def z863 : W := mkw 0xec90744956034810 0xa7b241d125580d20 0xb8e060719c038021 0x02e38181c6700e00

def z864 : W := mkw 0xfcd2746800000004 0xe3f349d1a0000000 0xb8fc60fe00000001 0x42e3f183f8000000

def z865 : W := mkw 0x1866a5b2adfdbfc1 0x08619a96cab7f6ff 0xb8e3e7f1ffffffff 0xfee38f9fc7ffffff

def z866 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0x80fc60ff806381e5 0x4203f183fe018e07

def z867 : W := mkw 0xef997e4c00000004 0xe3be65f930000000 0xfffc7ffe00000003 0xe3fff1fff8000000

def z868 : W := mkw 0x2d002e0156836c10 0x84b400b8055a0db0 0x7f001f01ff83fe3a 0xbdfc007c07fe0ff8

def z869 : W := mkw 0xf6ff0001fb780008 0x57dbfc0007ede000 0x7fff80007ffc0000 0xc5fffe0001fff000

def z870 : W := mkw 0xf7dbdbec00000004 0xe3df6f6fb0000000 0xc7fff8fe00000003 0x631fffe3f8000000

def z871 : W := mkw 0x0900ff8404876e50 0x882403fe10121db9 0x00007f000003fe38 0x280001fc00000ff8

def z872 : W := mkw 0x1adba5ec00000004 0x606b6e97b0000000 0x00ffe7fe00000000 0x6003ff9ff8000000

def z873 : W := mkw 0x09002e0156836c10 0x042400b8055a0db0 0xff007f01ff83fe3b 0xbffc01fc07fe0ff8

def z874 : W := mkw 0xec00240156836c10 0x07b00090055a0db0 0xff006701ff83fe3b 0xbffc019c07fe0ff8

def z875 : W := mkw 0x030d8b8621ac36c0 0x080c362e1886b0db 0x471f9f8e63fc7fdc 0x691c7e7e398ff1ff

def z876 : W := mkw 0x00b4005aa0609182 0x3002d0016a818246 0x80fc60ff806381e7 0x7a03f183fe018e07

def z877 : W := mkw 0xffdbffec00826414 0xe3ff6fffb0020990 0xfffffffe00007013 0xe3fffffff80001c0

def z878 : W := mkw 0xf6ff0001fb780008 0x57dbfc0007ede000 0xbfe38001fffc0001 0x96ff8e0007fff000

def z879 : W := mkw 0x126f0012a9789180 0x0049bc004aa5e246 0xfffff8fffffff1f7 0xffffffe3ffffffc7

def z880 : W := mkw 0x0924afb6a4e5bfc1 0x082492beda9396ff 0xc0fc7fffe063ffff 0x7b03f1ffff818fff

def z881 : W := mkw 0x03298b948c558b41 0x000ca62e5231562d 0x471f9f8f9c7f8fee 0xfd1c7e7e3e71fe3f

def z882 : W := mkw 0xf6fb0001db580008 0x57dbec00076d6000 0xbfe380019ffc0003 0xd6ff8e00067ff000

def z883 : W := mkw 0xc8b4745be463d982 0x3322d1d16f918f66 0xf8fc7ffffc63ffff 0xffe3f1fffff18fff

def z884 : W := mkw 0xef997e4d56836c14 0xe7be65f9355a0db0 0xfffc7fffff83fe3b 0xfffff1fffffe0ff8

def z885 : W := mkw 0xfedb746c00000004 0xe3fb6dd1b0000000 0xb8fc607e00000001 0x02e3f181f8000000

def z886 : W := mkw 0xf4f6505bfa72d182 0x37d3d9416fe9cb46 0xfffff8fffffff1f7 0xffffffe3ffffffc7

def z887 : W := mkw 0xd0d2506800000004 0x63434941a0000000 0xc0fc78fe00000003 0x6303f1e3f8000000

def z888 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0xbfffe7fe00000001 0xc2ffff9ff8000000

def z889 : W := mkw 0x3f4bafa4018c2644 0xc8fd2ebe90063099 0x3f038700039c0e08 0x84fc0e1c000e7038

def z890 : W := mkw 0x3edba5ec00000004 0xe0fb6e97b0000000 0x38ff80fe00000000 0x40e3fe03f8000000

def z891 : W := mkw 0x12db81ec08140245 0x604b6e07b0205009 0x00ff80fe001c0000 0x4003fe03f8007000

def z892 : W := mkw 0xe62d0001fb780008 0x1798b40007ede000 0xff1f8001fffc0003 0xd7fc7e0007fff000

def z893 : W := mkw 0xffdbffec04010804 0xe3ff6fffb0100420 0xffffffff9c038023 0xe3fffffffe700e00

def z894 : W := mkw 0x00240013e062d182 0x100090004f818b46 0x00000081e063f1f6 0x7800000207818fc7

def z895 : W := mkw 0xc0245013e062d182 0x130091404f818b46 0x80006001e063f1f5 0x1a00018007818fc7

def z896 : W := mkw 0x1adba5ec00000004 0x606b6e97b0000000 0xb8ffe0fe00000001 0x42e3ff83f8000000

def z897 : W := mkw 0xe4b4505bf262d182 0x3792d1416fc98b46 0xc7fc78ffe3e3f1f7 0x7b1ff1e3ff8f8fc7

def z898 : W := mkw 0x0299004c00000004 0x600a640130000000 0x001c000e00000000 0x0000700038000000

def z899 : W := mkw 0xc0b4005be0609182 0x3302d0016f818246 0xc0fc00ffe06001c7 0x5303f003ff818007

def z900 : W := mkw 0x2d002e0016812c10 0x84b400b8005a04b0 0xff007f01ff83fe3b 0xbffc01fc07fe0ff8

def z901 : W := mkw 0xf6ff5059fb7ac10a 0x77dbfd4167edeb04 0xffffe0f1ffff81e7 0xffffff83c7fffe07

def z902 : W := mkw 0x00240012ac759bc1 0x000090004ab1d66f 0x00000001fc7ffffc 0x1c00000007f1ffff

def z903 : W := mkw 0x12db81ec00040244 0x604b6e07b0001009 0x00ff87fe007c0fce 0xfc03fe1ff801f03f

def z904 : W := mkw 0xffdbffec0c150a45 0xe3ff6fffb0305429 0xfffffffe1c7c0fcf 0xfffffffff871f03f

def z905 : W := mkw 0xf7db8bec00000004 0x63df6e2fb0000000 0xffff9ffe00000003 0xe3fffe7ff8000000

def z906 : W := mkw 0x00240013e16ed3c2 0x180090004f85bb4f 0x00000001e07ff1f4 0x180000000781ffc7

def z907 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0xb8fffffe00000001 0x62e3fffff8000000

def z908 : W := mkw 0x00240013e062d182 0x100090004f818b46 0x80006001e063f1f7 0x3a00018007818fc7

def z909 : W := mkw 0xed007e0152826410 0x87b401f8054a0990 0xff007f0063807013 0xa3fc01fc018e01c0

def z910 : W := mkw 0xf6ff0001fb780008 0x57dbfc0007ede000 0xffff8081fffc01c7 0xfffffe0207fff007

def z911 : W := mkw 0xf6ff0001fb780008 0x57dbfc0007ede000 0xffff8001ff9c0001 0x87fffe0007fe7000

def z912 : W := mkw 0xff4bffa556836c10 0x87fd2ffe955a0db0 0xffffffffff83fe3b 0xfffffffffffe0ff8

def z913 : W := mkw 0xf7db5a6c00000004 0xe3df6d69b0000000 0x47fc187e00000000 0x011ff061f8000000

def z914 : W := mkw 0xc8247413ec77dbc3 0x132091d04fb1df6f 0xf8007f01fc7fffff 0xbfe001fc07f1ffff

def z915 : W := mkw 0x3f4bafa41f9d2e51 0x8cfd2ebe907e74b9 0x3f0387001f9c0e08 0x84fc0e1c007e7038

def z916 : W := mkw 0xef99ffcc00000000 0xa3be67ff30000000 0xfffffffe00000003 0xe3fffffff8000000

def z917 : W := mkw 0xf6ff505bfb7ad18a 0x77dbfd416fedeb46 0xffff98fffffc71d7 0xd7fffe63fffff1c7

def z918 : W := mkw 0xffdbffec178d2e54 0xefff6fffb05e34b9 0xfffffffe1f9c0e0b 0xe7fffffff87e7038

def z919 : W := mkw 0xc0b40001fb780008 0x1702d00007ede000 0xc0fc0001fffc0003 0x5703f00007fff000

def z920 : W := mkw 0xec90744800000000 0xa3b241d120000000 0xf8fc78fe00000003 0x63e3f1e3f8000000

def z921 : W := mkw 0xffdbffed56010804 0xe7ff6fffb5580420 0xffffffffff838e2b 0xfffffffffffe0e38

def z922 : W := mkw 0xf6ff5049fb78000c 0xf7dbfd4127ede000 0xffff8001fffc0003 0xd7fffe0007fff000

def z923 : W := mkw 0xef99ffcd56836c10 0xa7be67ff355a0db0 0xffffffffff83fe3b 0xfffffffffffe0ff8

def z924 : W := mkw 0x12db006c00000004 0x604b6c01b0000000 0x00fc007e00000000 0x0003f001f8000000

def z925 : W := mkw 0xc090504800000000 0x2302414120000000 0xc0fc787e00000001 0x0303f1e1f8000000

def z926 : W := mkw 0x366b00009b580008 0x44d9ac00026d6000 0xbfe380019f9c0001 0x86ff8e00067e7000

def z927 : W := mkw 0x00240013e0609182 0x100090004f818246 0x00000001e06001c4 0x1000000007818007

def z928 : W := mkw 0x00240013f7efffd2 0x1c0090004fdfbfff 0x00000001fffffffc 0x1c00000007ffffff

def z929 : W := mkw 0xffdbffec00842644 0xe3ff6fffb0021099 0xfffffffe63fc7fdf 0xfffffffff98ff1ff

def z930 : W := mkw 0xffdbffec0c150a45 0xe3ff6fffb0305429 0xffffffff9c1f8e2b 0xfffffffffe707e38

def z931 : W := mkw 0xed047e0376a37c90 0x87b411f80dda8df2 0xff1c7f8fffe3ffff 0xfffc71fe3fff8fff

def z932 : W := mkw 0xffdbffed52826414 0xe7ff6fffb54a0990 0xffffffffff807013 0xf7fffffffffe01c0

def z933 : W := mkw 0x00240013e0e2f582 0x100090004f838bd6 0x00000001e3e3fffc 0x1c000000078f8fff

def z934 : W := mkw 0x0090004800000000 0x2002400120000000 0x40fc18fe00000002 0x6103f063f8000000

def z935 : W := mkw 0xffdbffed578f6e54 0xefff6fffb55e3db9 0xffffffffff9ffe3b 0xfffffffffffe7ff8

def z936 : W := mkw 0xe7995a4c00000004 0xe39e656930000000 0xc7fc787e00000001 0x031ff1e1f8000000

def z937 : W := mkw 0x002081908c558b41 0x000082064231562d 0x000387819c7f8fee 0xfc000e1e0671fe3f

def z938 : W := mkw 0x3fdbafec16812c14 0xe4ff6ebfb05a04b0 0x3fff87fe1f800e08 0xc4fffe1ff87e0038

def z939 : W := mkw 0xf6fb5059db5ac10a 0x77dbed41676d6b04 0xbfe3e0719f9f8021 0x86ff8f81c67e7e00

def z940 : W := mkw 0x00240013f663d992 0x140090004fd98f66 0x00000001fc63f1f4 0x1800000007f18fc7

def z941 : W := mkw 0xf6ff0013fb7ad18a 0x57dbfc004fedeb46 0xffff988ffffff1f7 0xfffffe623fffffc7

def z942 : W := mkw 0xd2ff0001e9780000 0x134bfc0007a5e000 0xffff8001fffc0003 0xd7fffe0007fff000

def z943 : W := mkw 0xf6db00001b180008 0x47db6c00006c6000 0xbfe380001f9c0001 0x86ff8e00007e7000

def z944 : W := mkw 0xed007e0004812c00 0x83b401f8001204b0 0xff007f01ff83fe3b 0xbffc01fc07fe0ff8

def z945 : W := mkw 0xc094505b6022d182 0x330251416d808b46 0x401c78fe6003f1f4 0x290071e3f9800fc7

def z946 : W := mkw 0x1adbf5ec00000004 0xe06b6fd7b0000000 0x00ffe0fe00000000 0x4003ff83f8000000

def z947 : W := mkw 0x00240013e062d182 0x100090004f818b46 0x401c188fe063f1f6 0x790070623f818fc7

def z948 : W := mkw 0x13db8bec00000004 0x604f6e2fb0000000 0x00ff9ffe00000000 0x6003fe7ff8000000

def z949 : W := mkw 0xd0f6505be872d182 0x3343d9416fa1cb46 0xf8fff8fffc7ff1f7 0xffe3ffe3fff1ffc7

def z950 : W := mkw 0xf66f0001fb780000 0x07d9bc0007ede000 0xffff8001fffc0003 0xd7fffe0007fff000

def z951 : W := mkw 0xec00740156836c10 0x87b001d0055a0db0 0xb8006001ff83fe39 0x1ee0018007fe0ff8

def z952 : W := mkw 0xffdb7e6d56836c14 0xe7ff6df9b55a0db0 0xfffc787fff83f031 0x03fff1e1fffe0fc0

def z953 : W := mkw 0xe60d5003732a5080 0x079835400dcca942 0xff1ff88ffffff1f7 0xfffc7fe23fffffc7

def z954 : W := mkw 0xffdbffec00040244 0xe3ff6fffb0001009 0xfffffffe001c0e0b 0xe7fffffff8007038

def z955 : W := mkw 0xed247e13ffffffd1 0x8fb491f84fffffff 0xff007f01ffffffff 0xbffc01fc07ffffff

def z956 : W := mkw 0x12db81ec00000004 0x604b6e07b0000000 0x80ffe0fe00000003 0x6203ff83f8000000

def z957 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0xfffffffe63800003 0xf7fffffff98e0000

def z958 : W := mkw 0xfdf2fff9ded7ef51 0xa7f7cbffe77b5fbd 0xffffffffffffffff 0xffffffffffffffff

def z959 : W := mkw 0x2609000013080000 0x04982400004c2000 0x3f0380001f9c0000 0x84fc0e00007e7000

def z960 : W := mkw 0xc0b4505be062d182 0x3302d1416f818b46 0x80e06071e063f1f5 0x1a038181c7818fc7

def z961 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0xfffffffe00000e0b 0xfffffffff8000038

def z962 : W := mkw 0x09242e12adfdbfc1 0x082490b84ab7f6ff 0xff007f01ffffffff 0xbffc01fc07ffffff

def z963 : W := mkw 0x00b40000a0600000 0x1002d00002818000 0x00fc000000600000 0x4003f00000018000

def z964 : W := mkw 0xf64b00015b180008 0x47d92c00056c6000 0x7f0380007f9c0000 0x85fc0e0001fe7000

def z965 : W := mkw 0x12db81ec010c0244 0x684b6e07b0043009 0x00ff80fe001c0000 0x4003fe03f8007000

def z966 : W := mkw 0xffdbffed40024004 0xe3ff6fffb5000900 0xffffffff80038023 0xe3fffffffe000e00

def z967 : W := mkw 0xf64f00017b380008 0x47d93c0005ece000 0xff1f8001fffc0003 0xd7fc7e0007fff000

def z968 : W := mkw 0xe4b4505be062d182 0x3392d1416f818b46 0xfffc78ffe063f1f7 0xfbfff1e3ff818fc7

def z969 : W := mkw 0xef09ff8556836c10 0x87bc27fe155a0db0 0xff1fff8fff83fe3b 0xfffc7ffe3ffe0ff8

def z970 : W := mkw 0xffdbffec16812c14 0xe7ff6fffb05a04b0 0xffffffff9f838e2b 0xfffffffffe7e0e38

def z971 : W := mkw 0xf6ff0011fb788108 0x57dbfc0047ede204 0xffffe071ffff8023 0xd7ffff81c7fffe00

def z972 : W := mkw 0xf6ff5003fb7a5088 0x57dbfd400fede942 0xfffff88ffffff1f7 0xffffffe23fffffc7

def z973 : W := mkw 0x03098b8400000000 0x000c262e10000000 0xc7fffffe00000003 0xe31ffffff8000000

def z974 : W := mkw 0x134b8ba400000000 0x004d2e2e90000000 0x47ff9ffe00000002 0xe11ffe7ff8000000

def z975 : W := mkw 0xd8d2f5e80c150a41 0x23634bd7a0305429 0xf8fffffe1c1c0e0b 0xe7e3fffff8707038

def z976 : W := mkw 0xf6ff5011fb7ac108 0x57dbfd4047edeb04 0xfffff8f1fffff1f7 0xffffffe3c7ffffc7

def z977 : W := mkw 0xed007e0004010800 0x83b401f800100420 0xff007f019c038e2b 0xbffc01fc06700e38

def z978 : W := mkw 0xffdbafec00000004 0xe3ff6ebfb0000000 0xffff87fe00000003 0xc3fffe1ff8000000

def z979 : W := mkw 0xd2dbd1ec00000004 0x634b6f47b0000000 0x80ffe0fe00000001 0x4203ff83f8000000

def z980 : W := mkw 0xc9907e4804836c10 0xa32641f920120db0 0xc0fc7ffe0003fe3b 0x6b03f1fff8000ff8

def z981 : W := mkw 0xed047e0377af7ed0 0x8fb411f80ddebdfb 0xff007f01ffffffff 0xbffc01fc07ffffff

def z982 : W := mkw 0xfdd27e6956836c14 0xe7f749f9a55a0db0 0xfffc7fffff83fe3b 0xfffff1fffffe0ff8

def z983 : W := mkw 0x00240013fffdbfc9 0x1c0090004ffff6ff 0x00000001fffffffc 0x1c00000007ffffff

def z984 : W := mkw 0x18d2a5e800000000 0x20634a97a0000000 0xb8ffe7fe00000003 0xe2e3ff9ff8000000

def z985 : W := mkw 0xffdbffec00040244 0xe3ff6fffb0001009 0xfffffffe00000fcf 0xebfffffff800003f

def z986 : W := mkw 0xe5000a0156836c10 0x07940028055a0db0 0xff001f01ff83fe3b 0xbffc007c07fe0ff8

def z987 : W := mkw 0xe6bd505bf36ad182 0x379af5416fcdab46 0xfffff8fffffff1f7 0xffffffe3ffffffc7

def z988 : W := mkw 0x0900ffde0487ffd2 0xa82403ff78121fff 0x00007ffe0003fffc 0x280001fff8000fff

def z989 : W := mkw 0xfcd2f5e800000004 0xe3f34bd7a0000000 0xf8fffffe00000003 0xe3e3fffff8000000

def z990 : W := mkw 0x0900afa604853ec1 0x082402be981214fb 0x00001f8e00007fdc 0x2800007e380001ff

def z991 : W := mkw 0xc904ff8764a77ed0 0x8b2413fe1d929dfb 0xc01c7f8fe063ffff 0x7b0071fe3f818fff

def z992 : W := mkw 0xd3dbdbec00000004 0x634f6f6fb0000000 0xc7fffffe00000003 0xe31ffffff8000000

def z993 : W := mkw 0xe490000152000000 0x0792400005480000 0xfffc0001ff800003 0xd7fff00007fe0000

def z994 : W := mkw 0xffdbffec00000004 0xe3ff6fffb0000000 0xfffff8fe00000001 0x43ffffe3f8000000

def z995 : W := mkw 0xffdbffed56836c14 0xe7ff6fffb55a0db0 0xfffffffe7f807e1b 0xe7fffffff9fe01f8

def z996 : W := mkw 0xf6ff504bfb7a508a 0x77dbfd412fede942 0xfffff8fffffc7013 0xf7ffffe3fffff1c0

def z997 : W := mkw 0x1042000008100000 0x0041080000204000 0x380380001c1c0000 0x84e00e0000707000

def z998 : W := mkw 0xffdbffec04034814 0xe3ff6fffb0100d20 0xfffffffe00038023 0xe3fffffff8000e00

def z999 : W := mkw 0x3f4b2e001f992c18 0xc4fd2cb8007e64b0 0x3f0387001f9c0e08 0x84fc0e1c007e7038

def z1000 : W := mkw 0xed907e4956836c10 0xa7b641f9255a0db0 0xfffc7fffffe3ffff 0xfffff1ffffff8fff

def z1001 : W := mkw 0x3f6fafb7fb7ad18e 0xd4fdbebedfedeb46 0x3f038701fffff1f4 0x9cfc0e1c07ffffc7

def z1002 : W := mkw 0xe42481edfb78000c 0x37909207b7ede000 0xff0000fffffc0003 0x97fc0003fffff000

def z1003 : W := mkw 0xed907e4956836c12 0xb7b641f9255a0db0 0xfffc7fffff83fe3b 0xfffff1fffffe0ff8

def z1004 : W := mkw 0xf6db00495b180008 0x67db6c01256c6000 0xffff80ffff9c0003 0xd7fffe03fffe7000

def z1005 : W := mkw 0x0800a58004050a40 0x0020029600101429 0xb8e3e7f19c7f8fef 0xfee38f9fc671fe3f

def z1006 : W := mkw 0xed247e12b6e1bd92 0x97b491f84adb86f6 0xff007f001fe00fcf 0xa7fc01fc007f803f

def z1007 : W := mkw 0x2d242e12b6e1bd92 0x94b490b84adb86f6 0x3f0007001fe00fcc 0x84fc001c007f803f

def z1008 : W := mkw 0x3f6f2e13fffbfd9a 0xd4fdbcb84fffeff6 0x3f038701fffffffc 0x9cfc0e1c07ffffff

def z1009 : W := mkw 0xed907e4956836c14 0xe7b641f9255a0db0 0xfffc7fffff83fe3b 0xfffff1fffffe0ff8

def z1010 : W := mkw 0xc9907e4804812c00 0x232641f9201204b0 0xfffc7fffff83fe3b 0xfffff1fffffe0ff8

def z1011 : W := mkw 0xf6ff505bfb7ad18a 0x77dbfd416fedeb46 0xbfe3e071fffff1f5 0x9eff8f81c7ffffc7

def z1012 : W := mkw 0x2d902e4816812c10 0xa4b640b9205a04b0 0x3ffc07fe1f800e08 0xc4fff01ff87e0038

def z1013 : W := mkw 0x366f0013fb78918a 0x54d9bc004fede246 0x3f038001fffc01c4 0x94fc0e0007fff007

def z1014 : W := mkw 0xfcd6746b772f5ad4 0xeff359d1addcbd6b 0xb8e060719c7f81e5 0x02e38181c671fe07

def z1015 : W := mkw 0xf66f5013fb7ad18a 0x57d9bd404fedeb46 0xff03f801fffff1f7 0xbffc0fe007ffffc7

def z1016 : W := mkw 0xf6db50495b1a4008 0x67db6d41256c6900 0xfffff8ffff9ff033 0xffffffe3fffe7fc0

def z1017 : W := mkw 0xf6ff505bfb7ad18a 0x77dbfd416fedeb46 0x7f1f980ffffff1f4 0x9dfc7e603fffffc7

def z1018 : W := mkw 0x0900ffce04877ed0 0xa82403ff38121dfb 0x00007ffe0003fffc 0x280001fff8000fff

def z1019 : W := mkw 0x01008b8000842640 0x0004022e00021099 0x471f9f8e63fc7fde 0xfd1c7e7e398ff1ff

def z1020 : W := mkw 0xf66f0013fb78918a 0x57d9bc004fede246 0xff038001fffc01c7 0x97fc0e0007fff007

def z1021 : W := mkw 0x2d902e4956836c10 0xa4b640b9255a0db0 0x3ffc07ffff83fe38 0xdcfff01ffffe0ff8

def z1022 : W := mkw 0x35468b863ab436c8 0x4cd51a2e18ead0db 0x781c1f8e7c607fde 0x79e0707e39f181ff

def z1023 : W := mkw 0x03298b95c1cee742 0x180ca62e57073b9d 0x471f9f8f839f8e2a 0xe51c7e7e3e0e7e38

def z1024 : W := mkw 0xfcf27479de53c911 0xa7f3c9d1e7794f24 0xb8e060719c038021 0x02e38181c6700e00

def z1025 : W := mkw 0x0990afec00000004 0xa02642bfb0000000 0x00fc07fe00000000 0x4003f01ff8000000

def z1026 : W := mkw 0x3e6fa5b3ff7fdbcb 0x54f9be96cffdff6f 0x3f038701fffffffc 0x9cfc0e1c07ffffff

def z1027 : W := mkw 0xc190dbcc00842640 0x2b06436f30021099 0xc0fc7ffe00000e0b 0x6303f1fff8000038

def z1028 : W := mkw 0x366f5049fb780008 0x74d9bd4127ede000 0x3f03f8fffffc0000 0xb4fc0fe3fffff000

def z1029 : W := mkw 0x126f0012a978918a 0x5049bc004aa5e246 0x00038000007c01c4 0x00000e000001f007

def z1030 : W := mkw 0xf66f0013fb7ad18a 0x57d9bc004fedeb46 0xff038001fffff1f7 0x9ffc0e0007ffffc7

def z1031 : W := mkw 0xe69d000173280000 0x079a740005cca000 0xffff8001fffc0003 0xd7fffe0007fff000

def z1032 : W := mkw 0x2d902e4800000000 0xa0b640b920000000 0x3ffc07fe00000000 0xc0fff01ff8000000

def z1033 : W := mkw 0x126f81b6a97c93c1 0x0849be06daa5f24f 0x00038000007c01c4 0x00000e000001f007

def z1034 : W := mkw 0x126f0013fb7ad18a 0x5449bc004fedeb46 0x00038001fffff1f4 0x1c000e0007ffffc7

def z1035 : W := mkw 0x0900fff80487ef51 0xa02403ffe0121fbd 0x00007ffe0003fffc 0x280001fff8000fff

def z1036 : W := mkw 0x36ff005bfb7ad18a 0x74dbfc016fedeb46 0x3fff80fffffff1f4 0xdcfffe03ffffffc7

def z1037 : W := mkw 0x0924afb7fb7ad18e 0x942492bedfedeb46 0x00000701fffff1f4 0x1c00001c07ffffc7

def z1038 : W := mkw 0xf4f20001da500000 0x07d3c80007694000 0xffff8001fffc0003 0xd7fffe0007fff000

def z1039 : W := mkw 0xd26fd1b7e062d186 0x5349bf46df818b46 0xc003f801e063f1f7 0x3b000fe007818fc7

def z1040 : W := mkw 0xd8f2f5f88c558b41 0x2363cbd7e231562d 0x781f9f0f9c7f8fec 0x9de07e7c3e71fe3f

def z1041 : W := mkw 0xed907e4956836c10 0xa7b641f9255a0db0 0xfffc7f7fff83fe3b 0xbffff1fdfffe0ff8

def z1042 : W := mkw 0xed907e4804812c10 0xa3b641f9201204b0 0xfffc7ffe00000e0b 0xe3fff1fff8000038

def z1043 : W := mkw 0xc9907e4804812c10 0xa32641f9201204b0 0xc0fc7ffe00000e0b 0x6303f1fff8000038

def z1044 : W := mkw 0x3f6fafb6b6e1bd96 0xd4fdbebedadb86f6 0x3f0387001fe00fcc 0x84fc0e1c007f803f

def z1045 : W := mkw 0xf6db50495b180008 0x67db6d41256c6000 0xfffff8ffff9c0003 0xf7ffffe3fffe7000

def z1046 : W := mkw 0x366f0012bb78918a 0x54d9bc004aede246 0x3f0380001ffc01c4 0x84fc0e00007ff007

def z1047 : W := mkw 0xc39ddbce21ac36c0 0x2b0e776f3886b0db 0x87e3e77063fc7fdd 0x9e1f8f9dc18ff1ff

def z1048 : W := mkw 0x0ab9245c8c558b45 0x602ae4917231562d 0xb81c670f9c7f8fef 0xbee0719c3e71fe3f

def z1049 : W := mkw 0xf6db00121b1ad18a 0x47db6c00486c6b46 0xffff80001f9ff1f7 0xcffffe00007e7fc7

def z1050 : W := mkw 0x0024505aa062d182 0x300091416a818b46 0x000078fe0063f1f4 0x280001e3f8018fc7

def z1051 : W := mkw 0x0924ffecadfb6c1c 0xb02493ffb2b7edb0 0x00007ffe007ffe38 0x280001fff801fff8

def z1052 : W := mkw 0xe490504952024000 0x2792414125480900 0xfffc78ffff83f033 0xfffff1e3fffe0fc0

def z1053 : W := mkw 0xee9df5eb772f5acb 0x77ba77d7addcbd6b 0x471c1f0e63807e18 0x011c707c398e01f8

def z1054 : W := mkw 0xf64b505b5b1ad18a 0x67d92d416d6c6b46 0xff03f8ffff9ff1f7 0xbffc0fe3fffe7fc7

def z1055 : W := mkw 0xed907e4d56836c14 0xa7b641f9355a0db0 0xfffc7fffff83fe3b 0xfffff1fffffe0ff8

def z1056 : W := mkw 0x1bff2e5aadf9bd9a 0xf06ffcb96ab7e6f6 0x00ff87fe007c0fcc 0x4003fe1ff801f03f

def z1057 : W := mkw 0xc890f5e804050a41 0x232243d7a0101429 0xc0fc7ffe00000e0b 0x6303f1fff8000038

def z1058 : W := mkw 0xe79d5a4f73aa7490 0xaf9e75693dcea9d2 0x471c180e63807010 0x011c7060398e01c0

def z1059 : W := mkw 0x1846a5a36c375ac3 0x10611a968db0dd6b 0xb8e3e7f07c1c7e1b 0xe6e38f9fc1f071f8

def z1060 : W := mkw 0x09002e0004812c00 0x002400b8001204b0 0xfffc7fffff83fe3b 0xfffff1fffffe0ff8

def z1061 : W := mkw 0x366f505bfb7ad18a 0x74d9bd416fedeb46 0x3f03f8fffffff1f4 0xbcfc0fe3ffffffc7

def z1062 : W := mkw 0x11d60a6a21ac36c4 0x68475829a886b0db 0x47e01f7063fc7fde 0xbd1f807dc18ff1ff

def z1063 : W := mkw 0xc090504940024000 0x2302414125000900 0xc0fc78ffe063f1f7 0x7b03f1e3ff818fc7

def z1064 : W := mkw 0x366f0013fb7ad18a 0x54d9bc004fedeb46 0x7f1f988ffffff1f6 0xfdfc7e623fffffc7

def z1065 : W := mkw 0xdb4b7e014d9b6c18 0xc36d2df805366db0 0xc003ff01e01ffe3b 0x3b000ffc07807ff8

def z1066 : W := mkw 0x376f8b97fbfef7ca 0x5cddbe2e5feffbdf 0x3f038701fffffffc 0x9cfc0e1c07ffffff

def z1067 : W := mkw 0xc990ffec1b18000c 0xa72643ffb06c6000 0xc0fc7ffe1f9c0003 0x6703f1fff87e7000

def z1068 : W := mkw 0x2e29a5b0974d8b49 0x44b8a696c25d362d 0x87e067f183e38fef 0x7a1f819fc60f8e3f

def z1069 : W := mkw 0xe4b4505bf262d182 0x3792d1416fc98b46 0xfffff8fffffff1f7 0xffffffe3ffffffc7

def z1070 : W := mkw 0xed007e0156836c10 0x87b401f8055a0db0 0xfffc7fffff83fe3b 0xfffff1fffffe0ff8

def z1071 : W := mkw 0xd2dbd1ed56836c14 0x674b6f47b55a0db0 0xc0fff8ffff83fe3b 0x7f03ffe3fffe0ff8

def z1072 : W := mkw 0xff6f7e13fffbfd9a 0xd7fdbdf84fffeff6 0xff03ff01ffffffff 0xbffc0ffc07ffffff

def z1073 : W := mkw 0x00240012b6e1bd92 0x140090004adb86f6 0x000000001fe00fcc 0x04000000007f803f

def z1074 : W := mkw 0xf5f2dbdddad6e74a 0x7fd7cb6f776b5b9d 0xb8e067719c038e29 0x02e3819dc6700e38

def z1075 : W := mkw 0xed907e6956836c14 0xa7b641f9a55a0db0 0xfffc7fffff83fe3b 0xfffff1fffffe0ff8

def z1076 : W := mkw 0xe7b95a5ddad6e755 0xe79ee569776b5b9d 0x471c180e63fc71d4 0x011c7060398ff1c7

def z1077 : W := mkw 0x366f0013fb7ad18a 0x54d9bc004fedeb46 0xbfe3e0f1fffff1f7 0xfeff8f83c7ffffc7

def z1078 : W := mkw 0x36db00481b180008 0x64db6c01206c6000 0x3fff80fe1f9c0000 0xc4fffe03f87e7000

def z1079 : W := mkw 0xf6db00481b180008 0x67db6c01206c6000 0xffff80fe1f9c0003 0xc7fffe03f87e7000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z2,z6,z7,z8,z4]),(0,[z0,z2,z9,z8,z10,z5]),(0,[z11,z0,z2,z7,z12,z8])],[(0,[z13,z0,z2,z7,z8,z4]),(0,[z0,z2,z14,z7,z8,z4]),(0,[z0,z2,z15,z7,z8,z5]),(0,[z0,z16,z7,z8,z17,z5]),(0,[z0,z2,z18,z19,z7,z20])],[(0,[z0,z2,z7,z8,z4,z21]),(0,[z0,z22,z23,z2,z7,z4]),(0,[z24,z25,z2,z7,z26,z4]),(0,[z27,z0,z2,z7,z20,z4]),(0,[z28,z0,z2,z7,z8,z4]),(0,[z0,z2,z29,z30,z4,z31])],[(0,[z2,z7,z32,z8,z4,z5]),(0,[z0,z2,z33,z7,z8,z4]),(0,[z34,z0,z2,z7,z8,z4]),(1,[z0,z2,z18,z7,z20])],[(0,[z0,z2,z7,z8,z4,z35]),(0,[z0,z2,z7,z36,z8,z4]),(0,[z37,z0,z2,z7,z8,z38]),(0,[z39,z0,z25,z2,z29,z4]),(0,[z0,z2,z40,z7,z12,z8])],[(0,[z0,z2,z41,z7,z8,z4])],[(0,[z42,z37,z0,z2,z8,z4]),(0,[z0,z2,z7,z43,z4,z5]),(0,[z0,z2,z44,z7,z8,z5]),(0,[z0,z2,z45,z7,z8,z5]),(0,[z39,z0,z2,z8,z10,z31])],[(0,[z0,z2,z29,z7,z4,z31]),(0,[z0,z2,z19,z8,z30,z10]),(0,[z0,z2,z18,z7,z30,z31]),(0,[z0,z2,z8,z20,z10,z5]),(0,[z46,z0,z2,z19,z20,z4]),(0,[z0,z2,z18,z7,z8,z47])],[(0,[z0,z2,z7,z48,z4,z5]),(0,[z0,z2,z18,z8,z49,z5])],[(0,[z0,z2,z50,z19,z7,z8])],[(0,[z51,z0,z2,z7,z8,z4]),(0,[z0,z52,z2,z7,z8,z4]),(0,[z0,z2,z19,z7,z53,z4])],[(0,[z0,z23,z2,z3,z4,z5]),(0,[z0,z2,z7,z8,z54,z4]),(0,[z0,z2,z55,z19,z8,z4]),(0,[z0,z2,z7,z8,z56,z5]),(0,[z39,z0,z2,z8,z57,z5]),(0,[z0,z2,z7,z8,z10,z58]),(0,[z59,z0,z2,z18,z8,z5])],[(0,[z0,z2,z30,z4,z10,z31]),(0,[z60,z39,z0,z2,z29,z4])],[(0,[z27,z2,z7,z61,z4,z5]),(0,[z0,z2,z19,z8,z62,z10]),(0,[z0,z2,z7,z12,z8,z63]),(0,[z0,z2,z64,z19,z7,z4]),(0,[z0,z25,z2,z7,z20,z4])],[(0,[z0,z65,z2,z14,z7,z8]),(0,[z0,z2,z66,z7,z8,z4]),(0,[z0,z2,z7,z8,z4,z67]),(0,[z0,z68,z2,z7,z8,z5]),(0,[z69,z0,z2,z19,z8,z10]),(0,[z70,z0,z2,z7,z8,z4]),(0,[z39,z0,z2,z29,z71,z5]),(0,[z72,z0,z2,z19,z8,z10])],[]],
   [[(0,[z0,z25,z2,z7,z8,z4]),(0,[z0,z2,z73,z7,z8,z4]),(0,[z60,z0,z2,z74,z8,z4]),(0,[z0,z2,z75,z8,z5,z76]),(0,[z77,z0,z2,z7,z8,z4])],[(0,[z0,z78,z79,z7,z4,z5]),(0,[z0,z2,z80,z8,z4,z5]),(0,[z81,z0,z82,z8,z4,z31]),(0,[z81,z0,z82,z8,z10,z5])],[(0,[z0,z83,z7,z8,z4,z5]),(0,[z0,z2,z84,z7,z8,z5]),(0,[z85,z0,z2,z86,z8,z4]),(0,[z0,z2,z86,z7,z20,z4]),(0,[z37,z87,z0,z2,z8,z4]),(0,[z0,z2,z7,z8,z88,z31])],[(0,[z0,z89,z2,z7,z8,z4]),(0,[z37,z0,z2,z7,z8,z57]),(0,[z0,z2,z90,z7,z8,z10]),(0,[z91,z0,z2,z7,z92,z4])],[(0,[z0,z2,z7,z8,z10,z93])],[(0,[z87,z0,z2,z94,z8,z4])],[(0,[z0,z2,z95,z7,z8,z4]),(0,[z42,z0,z2,z18,z8,z5]),(0,[z0,z2,z7,z96,z4,z5]),(0,[z97,z0,z2,z18,z7,z8]),(0,[z0,z2,z7,z20,z4,z17]),(0,[z37,z0,z2,z7,z8,z98])],[(0,[z99,z0,z2,z7,z8,z4]),(0,[z0,z1,z2,z18,z7,z5]),(0,[z100,z0,z2,z7,z8,z4]),(0,[z0,z2,z101,z7,z8,z5])],[(0,[z0,z25,z2,z7,z8,z102]),(0,[z0,z2,z7,z8,z103,z5]),(0,[z0,z2,z104,z30,z4,z31])],[(0,[z0,z2,z7,z8,z105,z5]),(0,[z0,z2,z7,z8,z106,z5]),(0,[z37,z0,z107,z108,z2,z7])],[(0,[z0,z2,z7,z8,z4,z109]),(0,[z0,z2,z7,z110,z4,z5]),(0,[z37,z0,z111,z2,z7,z8]),(0,[z0,z2,z7,z112,z8,z4]),(0,[z113,z0,z2,z7,z8,z4]),(0,[z0,z114,z7,z8,z4,z115]),(0,[z0,z2,z116,z7,z4,z5])],[(0,[z0,z2,z7,z117,z8,z4])],[(0,[z0,z2,z7,z118,z8,z4]),(0,[z0,z2,z19,z7,z8,z119]),(0,[z120,z0,z2,z7,z8,z88])],[(0,[z0,z121,z2,z7,z8,z5]),(0,[z0,z122,z18,z7,z123,z5]),(0,[z0,z2,z7,z12,z8,z4]),(0,[z87,z0,z2,z8,z4,z93]),(0,[z2,z7,z8,z4,z124,z31])],[(0,[z0,z2,z7,z8,z4,z125]),(0,[z0,z2,z7,z8,z4,z126]),(0,[z60,z0,z2,z8,z4,z10]),(0,[z0,z2,z7,z8,z127,z5])],[(0,[z0,z2,z7,z8,z4,z31]),(0,[z0,z2,z3,z8,z4,z5]),(0,[z128,z0,z2,z7,z8,z4]),(0,[z0,z16,z2,z75,z8,z5]),(0,[z0,z2,z7,z8,z129,z4]),(0,[z0,z2,z7,z8,z4,z130]),(0,[z0,z2,z19,z7,z8,z131])]],
   [[(0,[z0,z2,z7,z8,z4,z132]),(0,[z0,z2,z7,z8,z133,z4]),(0,[z0,z2,z7,z8,z134,z38]),(0,[z37,z0,z2,z18,z7,z8]),(0,[z135,z136,z2,z7,z8,z4])],[(0,[z137,z0,z2,z7,z8,z4]),(0,[z24,z2,z7,z26,z4,z138]),(0,[z0,z139,z2,z7,z8,z5])],[(0,[z0,z23,z2,z18,z7,z5]),(0,[z0,z2,z140,z7,z8,z4]),(0,[z0,z2,z141,z7,z8,z5]),(0,[z0,z2,z142,z8,z4,z5]),(0,[z0,z7,z143,z8,z10,z5]),(0,[z0,z2,z7,z8,z131,z5]),(0,[z0,z2,z18,z7,z144,z8]),(0,[z0,z2,z18,z7,z8,z145])],[(0,[z0,z2,z146,z8,z10,z5]),(0,[z147,z0,z2,z7,z20,z4])],[(0,[z148,z0,z2,z8,z4,z5]),(0,[z0,z2,z90,z104,z30,z4]),(0,[z0,z2,z149,z8,z10,z31]),(0,[z0,z2,z19,z8,z4,z49])],[(0,[z0,z2,z7,z150,z4,z5]),(0,[z0,z2,z7,z151,z8,z4]),(0,[z120,z0,z2,z7,z8,z71])],[(0,[z0,z2,z7,z8,z102,z5]),(0,[z152,z2,z7,z8,z4,z153]),(0,[z81,z0,z154,z82,z8,z4]),(0,[z0,z2,z7,z82,z20,z4]),(0,[z155,z0,z2,z19,z8,z10]),(0,[z0,z2,z156,z7,z8,z4]),(0,[z0,z157,z7,z8,z4,z31]),(0,[z0,z25,z2,z158,z7,z8])],[(0,[z0,z159,z2,z7,z8,z5]),(0,[z0,z2,z19,z160,z8,z10]),(0,[z0,z25,z2,z142,z8,z4])],[(0,[z0,z2,z161,z19,z8,z4]),(0,[z0,z2,z104,z7,z20,z4]),(0,[z0,z108,z2,z7,z20,z4])],[(0,[z162,z0,z2,z7,z8,z4]),(0,[z163,z2,z7,z164,z8,z4]),(0,[z0,z78,z2,z19,z8,z10]),(0,[z0,z2,z7,z165,z10,z31]),(0,[z0,z2,z149,z7,z8,z10]),(0,[z85,z0,z2,z166,z8,z10]),(0,[z0,z2,z116,z19,z7,z4])],[(0,[z81,z0,z2,z7,z20,z4]),(0,[z0,z7,z167,z8,z168,z5]),(0,[z0,z2,z7,z8,z20,z4]),(0,[z0,z2,z75,z8,z4,z93])],[(0,[z169,z0,z2,z7,z8,z4]),(0,[z163,z0,z2,z19,z8,z10]),(0,[z0,z2,z7,z8,z170,z5]),(0,[z0,z2,z19,z8,z10,z171])],[(0,[z0,z172,z2,z7,z8,z5]),(0,[z0,z2,z84,z7,z8,z10])],[(0,[z0,z173,z2,z7,z8,z5]),(0,[z174,z0,z2,z7,z8,z4]),(0,[z0,z2,z19,z7,z8,z175])],[(0,[z0,z2,z7,z8,z176,z4])],[(0,[z0,z2,z7,z8,z177,z4]),(0,[z0,z2,z7,z8,z178,z5]),(0,[z0,z2,z19,z8,z10,z153]),(0,[z0,z7,z179,z8,z10,z5]),(0,[z0,z2,z19,z8,z10,z5]),(0,[z180,z0,z2,z7,z181,z8])]],
   [[(0,[z0,z182,z2,z7,z4,z5]),(0,[z37,z27,z2,z7,z61,z4]),(0,[z0,z2,z7,z8,z4,z183]),(0,[z0,z2,z184,z7,z8,z4]),(0,[z0,z2,z7,z185,z186,z5]),(0,[z0,z2,z7,z12,z8,z187]),(0,[z0,z25,z2,z7,z8,z88]),(0,[z0,z188,z2,z7,z4,z31])],[(0,[z0,z189,z2,z7,z8,z31]),(0,[z0,z190,z2,z7,z8,z4]),(0,[z191,z2,z18,z7,z8,z192]),(0,[z37,z0,z2,z7,z8,z193]),(0,[z0,z2,z7,z8,z194,z5]),(0,[z195,z0,z2,z19,z8,z10]),(0,[z0,z2,z84,z19,z8,z10])],[(0,[z0,z196,z2,z7,z8,z4]),(0,[z24,z2,z7,z26,z4,z197]),(0,[z0,z2,z7,z8,z4,z198])],[(0,[z0,z2,z7,z8,z199,z5]),(1,[z0,z2,z19,z8,z131])],[(0,[z0,z2,z7,z8,z10,z200]),(0,[z163,z2,z7,z8,z10,z153]),(0,[z0,z2,z7,z8,z10,z201]),(0,[z87,z0,z25,z2,z8,z4])],[(0,[z0,z2,z202,z7,z8,z4]),(0,[z46,z0,z2,z30,z4,z31]),(0,[z0,z2,z18,z7,z8,z203]),(0,[z204,z0,z2,z7,z8,z205]),(0,[z0,z2,z149,z8,z4,z206]),(0,[z120,z0,z2,z7,z207,z4])],[(0,[z0,z122,z7,z123,z4,z208]),(0,[z0,z2,z209,z7,z8,z5]),(1,[z0,z2,z116,z19,z10])],[(0,[z0,z7,z210,z8,z4,z5]),(0,[z0,z2,z7,z8,z4,z211]),(0,[z85,z0,z212,z2,z7,z8]),(0,[z0,z2,z7,z8,z213,z31]),(0,[z204,z0,z214,z2,z7,z8])],[(0,[z0,z2,z7,z8,z4,z215]),(0,[z0,z2,z216,z75,z8,z4])],[(0,[z217,z218,z7,z8,z10,z5]),(0,[z0,z2,z7,z8,z219,z5]),(0,[z0,z2,z7,z8,z10,z220]),(0,[z0,z25,z2,z7,z8,z71]),(0,[z0,z2,z116,z19,z4,z10])],[(0,[z0,z2,z7,z221,z4,z5]),(0,[z0,z78,z7,z4,z222,z31])],[(0,[z0,z2,z7,z8,z4,z223]),(0,[z0,z2,z7,z224,z8,z4]),(0,[z0,z25,z2,z7,z8,z225]),(0,[z0,z2,z226,z7,z4,z31]),(0,[z204,z0,z2,z7,z12,z8])],[(0,[z227,z0,z2,z3,z8,z4]),(0,[z0,z2,z7,z8,z4,z228]),(0,[z0,z2,z18,z7,z229,z8]),(0,[z46,z0,z2,z20,z4,z5]),(0,[z0,z230,z2,z7,z20,z4])],[(0,[z217,z218,z7,z8,z4,z231]),(0,[z0,z232,z233,z8,z4,z5]),(0,[z0,z2,z7,z234,z4,z31]),(0,[z235,z2,z7,z8,z236,z5]),(0,[z0,z2,z7,z237,z5,z76]),(0,[z0,z2,z7,z8,z47,z4]),(0,[z0,z2,z238,z7,z8,z205]),(0,[z239,z0,z2,z7,z8,z4]),(0,[z0,z107,z108,z2,z7,z5])],[(0,[z37,z0,z2,z7,z8,z240])],[(0,[z217,z189,z218,z7,z8,z5]),(0,[z0,z2,z7,z8,z241,z5]),(0,[z0,z2,z7,z61,z20,z4]),(0,[z0,z2,z7,z242,z4,z31]),(0,[z69,z0,z18,z7,z243,z8]),(0,[z120,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z4,z244]),(0,[z0,z245,z2,z30,z10,z5]),(0,[z246,z0,z2,z19,z8,z10]),(0,[z0,z2,z40,z19,z142,z8])]],
   [[(0,[z217,z218,z7,z8,z4,z247]),(0,[z0,z232,z2,z149,z8,z4]),(0,[z0,z2,z7,z248,z8,z4]),(0,[z0,z2,z146,z7,z20,z4]),(0,[z0,z2,z249,z19,z7,z8]),(0,[z0,z2,z40,z7,z8,z20])],[(0,[z0,z2,z7,z250,z8,z5]),(0,[z24,z2,z19,z7,z26,z4]),(0,[z37,z39,z0,z2,z8,z10]),(0,[z0,z2,z64,z7,z4,z5]),(0,[z251,z0,z2,z7,z8,z10])],[(0,[z0,z2,z252,z8,z10,z5])],[(0,[z227,z0,z189,z2,z7,z8]),(0,[z0,z2,z7,z253,z8,z4]),(0,[z0,z254,z2,z7,z181,z8])],[(0,[z255,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z256,z5]),(0,[z37,z0,z2,z86,z8,z131]),(0,[z257,z2,z7,z8,z4,z258])],[(0,[z0,z2,z7,z8,z4,z259]),(0,[z0,z2,z19,z260,z8,z4]),(0,[z0,z2,z7,z8,z71,z261]),(0,[z46,z0,z2,z7,z20,z4]),(0,[z59,z0,z2,z19,z8,z4])],[(0,[z0,z262,z2,z7,z4,z5]),(0,[z263,z0,z2,z19,z8,z10]),(0,[z37,z0,z2,z264,z8,z4]),(0,[z0,z2,z265,z7,z8,z63]),(0,[z0,z25,z2,z7,z185,z76]),(0,[z204,z0,z266,z2,z7,z8])],[(0,[z24,z2,z7,z26,z10,z5]),(0,[z24,z2,z7,z26,z4,z31]),(0,[z0,z2,z7,z8,z267,z5]),(0,[z0,z2,z7,z229,z8,z10]),(0,[z0,z2,z7,z8,z4,z268]),(0,[z0,z2,z149,z7,z30,z4]),(0,[z0,z269,z2,z19,z8,z10]),(0,[z0,z2,z8,z10,z270,z5]),(0,[z0,z2,z19,z237,z8,z10]),(0,[z2,z7,z8,z10,z271,z5])],[],[(0,[z0,z122,z2,z7,z20,z4]),(0,[z0,z2,z19,z8,z10,z10])],[(0,[z0,z2,z7,z8,z4,z272]),(0,[z0,z122,z19,z7,z123,z4])],[(0,[z0,z2,z273,z8,z10,z5]),(0,[z0,z122,z25,z7,z123,z4])],[(0,[z0,z2,z7,z274,z8,z4]),(0,[z0,z2,z19,z7,z20,z4]),(0,[z0,z2,z40,z19,z7,z8]),(0,[z37,z0,z2,z40,z7,z8]),(0,[z0,z2,z7,z216,z8,z4])],[(0,[z0,z23,z2,z7,z4,z5]),(0,[z0,z2,z7,z8,z4,z275]),(0,[z46,z0,z2,z19,z8,z4]),(0,[z0,z2,z7,z20,z4,z10]),(0,[z0,z276,z2,z7,z20,z4]),(0,[z0,z2,z7,z8,z4,z277]),(0,[z0,z25,z2,z7,z8,z56])],[(0,[z39,z0,z2,z29,z4,z278]),(0,[z0,z2,z7,z279,z8,z10])],[(0,[z0,z2,z7,z8,z4,z280]),(0,[z0,z2,z281,z8,z4,z5]),(0,[z0,z2,z19,z123,z8,z10]),(0,[z0,z2,z252,z30,z4,z31]),(0,[z0,z2,z149,z30,z4,z5]),(0,[z0,z2,z7,z282,z10,z5]),(0,[z0,z2,z18,z7,z8,z283]),(0,[z284,z285,z2,z7,z8,z4])]],
   [[(0,[z42,z0,z2,z19,z8,z4]),(0,[z0,z2,z7,z286,z4,z31]),(0,[z37,z0,z2,z287,z8,z4]),(0,[z0,z2,z19,z288,z8,z4])],[(0,[z0,z2,z289,z8,z4,z5]),(0,[z0,z1,z2,z19,z7,z4]),(0,[z0,z290,z2,z7,z8,z5])],[(0,[z0,z2,z18,z7,z8,z291]),(0,[z0,z2,z292,z8,z10,z5]),(0,[z72,z0,z25,z2,z7,z10]),(0,[z0,z293,z19,z7,z8,z4]),(0,[z0,z294,z2,z7,z20,z4]),(0,[z295,z0,z2,z7,z8,z4])],[(0,[z0,z2,z296,z8,z10,z5]),(0,[z81,z297,z0,z82,z8,z4]),(0,[z0,z232,z160,z8,z4,z298]),(0,[z0,z254,z2,z166,z8,z5])],[(0,[z0,z2,z18,z299,z8,z5]),(0,[z0,z2,z300,z7,z8,z5]),(0,[z0,z2,z7,z8,z10,z298]),(0,[z0,z301,z302,z7,z8,z5])],[(0,[z0,z2,z19,z8,z10,z17]),(0,[z0,z2,z29,z7,z20,z4]),(0,[z0,z303,z2,z7,z8,z4])],[(0,[z0,z189,z23,z2,z7,z5]),(0,[z0,z2,z304,z7,z4,z31]),(0,[z0,z2,z7,z305,z8,z4]),(0,[z0,z2,z306,z19,z7,z4])],[(0,[z24,z2,z18,z7,z26,z5]),(0,[z0,z2,z7,z8,z4,z307]),(0,[z0,z2,z308,z8,z10,z5]),(0,[z309,z0,z2,z7,z20,z4])],[(0,[z0,z2,z7,z8,z4,z310]),(0,[z0,z2,z19,z7,z8,z311])],[(0,[z0,z2,z312,z7,z8,z4]),(0,[z0,z2,z19,z7,z313,z4]),(0,[z0,z2,z158,z7,z8,z5])],[(0,[z0,z2,z7,z314,z4,z5]),(1,[z2,z7,z8,z4,z315]),(0,[z0,z2,z7,z316,z4,z31]),(0,[z37,z0,z2,z19,z8,z10])],[(0,[z0,z2,z7,z8,z4,z317]),(0,[z0,z2,z7,z8,z4,z318]),(0,[z0,z2,z29,z149,z7,z4]),(0,[z319,z2,z7,z8,z320,z5])],[(0,[z0,z23,z2,z19,z7,z4]),(0,[z0,z2,z7,z321,z8,z5])],[(0,[z0,z2,z7,z8,z322,z5])],[(0,[z0,z189,z2,z19,z7,z8]),(0,[z0,z2,z7,z323,z8,z4]),(0,[z37,z0,z78,z7,z4,z222]),(0,[z37,z0,z2,z84,z7,z8]),(0,[z324,z325,z2,z7,z8,z4])],[(0,[z217,z0,z2,z7,z20,z4]),(0,[z0,z326,z2,z7,z8,z5]),(0,[z0,z2,z29,z327,z4,z5]),(0,[z295,z87,z0,z2,z8,z4]),(0,[z120,z0,z2,z252,z8,z4])]],
   [[(0,[z0,z2,z328,z8,z4,z5]),(0,[z0,z2,z329,z8,z4,z5]),(0,[z87,z0,z2,z185,z5,z76])],[(0,[z0,z2,z7,z330,z8,z4]),(0,[z0,z232,z160,z229,z8,z4]),(0,[z0,z2,z331,z7,z8,z5]),(0,[z0,z2,z332,z8,z4,z206]),(0,[z0,z2,z333,z7,z8,z4])],[(0,[z0,z334,z7,z8,z4,z5]),(0,[z0,z2,z335,z7,z8,z5]),(0,[z0,z2,z7,z336,z8,z4]),(0,[z0,z2,z337,z8,z4,z5]),(0,[z0,z2,z7,z8,z338,z4]),(0,[z0,z2,z18,z7,z20,z5]),(0,[z72,z0,z25,z2,z18,z7]),(0,[z0,z2,z40,z7,z8,z31])],[(0,[z0,z2,z339,z8,z4,z5]),(0,[z39,z0,z2,z29,z10,z5]),(0,[z39,z0,z2,z29,z4,z31]),(0,[z46,z0,z2,z18,z12,z8])],[(0,[z0,z340,z2,z7,z8,z4]),(0,[z0,z2,z341,z8,z10,z5]),(0,[z0,z2,z7,z8,z10,z138]),(0,[z0,z2,z7,z342,z4,z5]),(0,[z0,z2,z8,z30,z343,z10]),(0,[z39,z0,z2,z8,z344,z5]),(0,[z0,z345,z7,z8,z10,z5]),(0,[z346,z0,z2,z7,z8,z10])],[(0,[z0,z2,z18,z7,z8,z5]),(0,[z27,z2,z7,z61,z4,z200]),(0,[z347,z2,z7,z8,z348,z5])],[(0,[z0,z7,z329,z8,z4,z5]),(0,[z0,z2,z19,z142,z8,z4]),(0,[z0,z349,z2,z7,z350,z5]),(0,[z0,z266,z2,z7,z8,z4])],[(0,[z0,z2,z351,z8,z10,z5])],[],[(0,[z0,z352,z2,z7,z4,z31]),(0,[z46,z0,z2,z12,z8,z4])],[(0,[z0,z353,z2,z7,z8,z5]),(0,[z0,z2,z86,z19,z8,z10]),(0,[z0,z2,z354,z7,z20,z4])],[(0,[z0,z2,z7,z8,z355,z5]),(0,[z0,z2,z7,z8,z4,z356]),(0,[z46,z0,z2,z8,z129,z4]),(0,[z0,z2,z19,z8,z10,z357]),(0,[z0,z2,z358,z7,z8,z4])],[(0,[z0,z2,z19,z359,z8,z10]),(0,[z0,z2,z7,z8,z4,z360]),(0,[z0,z7,z361,z8,z4,z5]),(0,[z263,z2,z7,z8,z236,z31]),(0,[z0,z2,z7,z8,z362,z5]),(0,[z0,z2,z7,z8,z363,z5]),(0,[z0,z2,z364,z8,z10,z5])],[(0,[z2,z7,z8,z4,z365,z5]),(0,[z0,z25,z2,z7,z10,z31]),(0,[z72,z0,z2,z7,z92,z4]),(0,[z0,z2,z158,z74,z7,z8])],[(0,[z42,z0,z2,z8,z4,z31]),(0,[z42,z0,z2,z8,z10,z5]),(0,[z0,z2,z366,z8,z4,z5]),(0,[z367,z2,z7,z8,z4,z5]),(0,[z69,z0,z368,z7,z8,z4]),(0,[z0,z2,z19,z369,z8,z10]),(0,[z370,z0,z371,z7,z8,z4])],[(0,[z372,z0,z2,z7,z20,z4]),(0,[z0,z122,z7,z123,z4,z5]),(0,[z0,z2,z7,z167,z20,z4]),(0,[z39,z0,z2,z7,z92,z4]),(1,[z0,z2,z149,z8,z10]),(0,[z0,z2,z19,z7,z8,z88])]],
   [[(0,[z0,z373,z2,z7,z8,z5]),(0,[z0,z374,z2,z7,z8,z5]),(0,[z0,z375,z2,z7,z8,z5]),(0,[z376,z0,z2,z7,z8,z4]),(0,[z0,z377,z2,z19,z8,z10]),(0,[z39,z0,z2,z149,z8,z4]),(0,[z0,z2,z7,z8,z378,z187])],[(0,[z0,z379,z2,z7,z8,z5]),(0,[z0,z2,z7,z8,z380,z5]),(0,[z0,z2,z7,z381,z4,z31])],[(0,[z0,z2,z20,z4,z10,z5]),(0,[z0,z2,z7,z8,z240,z31])],[(0,[z382,z0,z2,z149,z8,z4]),(0,[z39,z0,z2,z74,z8,z4])],[(0,[z0,z2,z383,z7,z8,z4]),(0,[z37,z0,z2,z44,z7,z8]),(0,[z0,z16,z2,z7,z20,z4]),(0,[z384,z0,z7,z385,z8,z4])],[(0,[z0,z2,z3,z18,z8,z5]),(0,[z0,z2,z7,z8,z10,z197]),(0,[z0,z2,z7,z8,z10,z278]),(0,[z0,z2,z19,z8,z131,z5])],[(0,[z0,z386,z2,z7,z8,z5]),(0,[z37,z0,z16,z7,z8,z17]),(0,[z46,z0,z2,z8,z20,z4]),(0,[z0,z2,z18,z149,z7,z8])],[(0,[z0,z387,z2,z7,z8,z4]),(0,[z0,z2,z388,z8,z4,z5]),(0,[z0,z2,z7,z389,z8,z4]),(0,[z0,z390,z391,z7,z8,z5]),(0,[z0,z2,z7,z8,z4,z392]),(0,[z393,z2,z394,z7,z8,z4])],[(0,[z0,z2,z7,z8,z4,z395]),(0,[z0,z2,z7,z53,z4,z5]),(0,[z0,z2,z396,z7,z8,z4]),(0,[z0,z2,z7,z8,z397,z4]),(0,[z37,z0,z122,z7,z123,z4]),(0,[z0,z2,z149,z8,z30,z4]),(0,[z0,z2,z19,z7,z8,z71]),(0,[z0,z2,z7,z8,z71,z31]),(0,[z0,z2,z7,z8,z88,z131]),(0,[z0,z254,z266,z2,z7,z8])],[(0,[z0,z2,z7,z8,z398,z5]),(0,[z24,z111,z2,z7,z26,z5]),(0,[z0,z2,z18,z399,z8,z5]),(1,[z2,z7,z8,z400,z5]),(0,[z0,z2,z7,z8,z4,z401]),(0,[z0,z2,z18,z74,z7,z8]),(0,[z0,z266,z2,z7,z8,z187])],[(0,[z0,z2,z7,z8,z402,z5]),(0,[z0,z2,z7,z8,z403,z5]),(0,[z0,z2,z7,z404,z4,z5]),(0,[z0,z2,z7,z405,z8,z4]),(0,[z0,z2,z19,z7,z8,z225]),(0,[z69,z0,z7,z243,z8,z10]),(0,[z406,z0,z2,z18,z7,z8]),(0,[z0,z2,z18,z8,z10,z31]),(0,[z0,z2,z407,z8,z4,z5])],[(0,[z0,z408,z7,z8,z4,z5]),(0,[z0,z25,z232,z160,z8,z4]),(0,[z0,z2,z7,z8,z38,z5]),(0,[z0,z2,z7,z409,z4,z5])],[(0,[z217,z218,z7,z8,z4,z31]),(0,[z0,z2,z7,z8,z4,z410]),(0,[z0,z2,z7,z8,z411,z5]),(0,[z0,z2,z18,z142,z8,z5]),(0,[z0,z2,z116,z40,z19,z7]),(0,[z0,z25,z2,z412,z7,z4])],[(0,[z0,z16,z7,z8,z168,z5]),(0,[z0,z2,z7,z8,z413,z4]),(0,[z0,z414,z2,z7,z10,z5]),(0,[z0,z2,z7,z20,z4,z205])],[(0,[z227,z0,z2,z7,z8,z4]),(0,[z87,z0,z2,z18,z8,z5])],[(0,[z0,z25,z2,z7,z8,z193]),(1,[z0,z2,z84,z19,z8]),(0,[z0,z2,z7,z237,z5,z171])]],
   [[(0,[z0,z2,z415,z8,z4,z5]),(0,[z0,z2,z416,z8,z10,z5]),(0,[z0,z2,z7,z129,z4,z31]),(0,[z246,z2,z7,z164,z8,z4])],[(0,[z0,z2,z7,z8,z4,z417]),(0,[z0,z2,z7,z8,z4,z418]),(0,[z24,z2,z7,z419,z26,z5]),(0,[z0,z2,z7,z8,z420,z5]),(0,[z0,z2,z19,z299,z8,z4]),(0,[z120,z0,z2,z7,z8,z38]),(0,[z87,z0,z2,z8,z71,z5]),(1,[z0,z2,z84,z8,z10]),(0,[z0,z2,z7,z8,z343,z421]),(0,[z37,z0,z2,z116,z19,z4])],[(0,[z0,z65,z2,z7,z8,z5]),(0,[z263,z422,z2,z7,z8,z5]),(0,[z81,z0,z2,z19,z8,z10]),(0,[z0,z2,z394,z7,z20,z4]),(0,[z0,z2,z423,z8,z4,z31])],[(0,[z424,z97,z2,z359,z8,z4]),(0,[z0,z2,z7,z425,z4,z5]),(0,[z0,z2,z426,z7,z8,z4])],[(0,[z0,z2,z18,z19,z8,z10]),(0,[z0,z2,z7,z8,z427,z10])],[(0,[z0,z1,z2,z7,z4,z5]),(0,[z0,z2,z19,z7,z342,z4]),(0,[z0,z2,z19,z7,z185,z76])],[(0,[z0,z2,z7,z8,z428,z5]),(0,[z0,z2,z18,z7,z8,z129]),(0,[z120,z0,z2,z29,z7,z4]),(0,[z0,z2,z7,z429,z8,z4])],[(0,[z0,z111,z2,z7,z8,z5]),(0,[z0,z2,z7,z185,z20,z4])],[(0,[z424,z430,z2,z8,z4,z5]),(0,[z0,z2,z104,z30,z57,z5]),(0,[z0,z2,z18,z84,z7,z8])],[(0,[z0,z2,z7,z8,z4,z431]),(0,[z0,z2,z7,z8,z432,z5]),(0,[z0,z2,z7,z8,z4,z433]),(0,[z0,z2,z434,z8,z4,z5]),(0,[z81,z0,z329,z8,z4,z5]),(0,[z0,z232,z160,z8,z10,z5]),(0,[z85,z0,z2,z7,z8,z343]),(0,[z0,z25,z2,z166,z8,z4])],[(0,[z0,z2,z7,z435,z8,z4]),(0,[z424,z2,z359,z8,z4,z5]),(0,[z0,z2,z436,z19,z8,z4]),(0,[z0,z2,z306,z7,z4,z5]),(0,[z437,z2,z7,z8,z4,z5]),(0,[z37,z0,z2,z19,z8,z205])],[(0,[z438,z0,z2,z75,z8,z5]),(0,[z0,z2,z7,z129,z20,z4]),(0,[z439,z0,z2,z7,z8,z10])],[(0,[z37,z0,z2,z440,z8,z4])],[(0,[z0,z2,z441,z19,z8,z4]),(1,[z0,z2,z149,z30,z4]),(0,[z239,z87,z0,z2,z8,z4])],[(0,[z0,z2,z7,z8,z10,z231]),(0,[z97,z0,z2,z7,z8,z10]),(0,[z0,z2,z7,z8,z119,z5]),(0,[z0,z2,z7,z8,z4,z442]),(0,[z0,z2,z443,z7,z8,z4]),(0,[z444,z0,z2,z7,z8,z5])],[(0,[z37,z0,z2,z7,z8,z105]),(0,[z0,z445,z7,z8,z4,z5]),(0,[z0,z2,z7,z419,z8,z5]),(0,[z446,z0,z25,z2,z7,z4]),(0,[z0,z2,z7,z8,z57,z5])]],
   [[(0,[z0,z2,z447,z8,z4,z5]),(0,[z37,z0,z2,z7,z8,z448]),(0,[z0,z390,z7,z167,z8,z5]),(0,[z0,z2,z19,z449,z8,z10])],[(0,[z0,z2,z7,z8,z10,z247]),(0,[z0,z2,z7,z8,z450,z5]),(0,[z451,z0,z2,z7,z8,z4]),(0,[z0,z2,z8,z452,z10,z5]),(0,[z0,z25,z2,z453,z8,z4])],[(0,[z0,z2,z19,z7,z8,z4]),(0,[z0,z454,z7,z8,z4,z5]),(0,[z60,z0,z2,z116,z7,z4]),(0,[z455,z0,z2,z19,z8,z205])],[(0,[z0,z2,z7,z8,z456,z5]),(0,[z0,z2,z7,z8,z457,z5]),(0,[z0,z122,z7,z48,z4,z5]),(0,[z87,z0,z2,z8,z10,z5]),(0,[z0,z2,z116,z18,z19,z7])],[(0,[z424,z0,z2,z149,z8,z4]),(0,[z0,z2,z7,z458,z4,z31]),(0,[z37,z0,z2,z86,z8,z88])],[(0,[z37,z0,z23,z2,z7,z4]),(0,[z0,z2,z7,z154,z8,z10]),(0,[z37,z0,z390,z7,z167,z8]),(0,[z0,z25,z2,z7,z8,z38]),(0,[z0,z2,z40,z8,z10,z5]),(0,[z0,z2,z7,z8,z10,z459]),(0,[z0,z2,z19,z8,z4,z131])],[(0,[z0,z2,z7,z8,z4,z460]),(0,[z0,z461,z2,z7,z8,z462])],[(0,[z0,z2,z7,z30,z10,z31]),(0,[z0,z107,z2,z7,z20,z4]),(0,[z0,z2,z463,z7,z8,z5])],[(0,[z0,z2,z7,z8,z4,z464]),(0,[z60,z0,z2,z7,z8,z311]),(0,[z37,z0,z2,z7,z8,z10])],[(0,[z0,z465,z2,z7,z8,z5]),(0,[z0,z2,z237,z30,z10,z5])],[(0,[z0,z2,z19,z7,z8,z102]),(0,[z0,z25,z2,z40,z7,z8]),(0,[z0,z466,z2,z7,z8,z4]),(0,[z0,z2,z463,z7,z185,z5])],[(0,[z467,z0,z2,z7,z8,z4]),(0,[z0,z2,z8,z10,z468,z5]),(0,[z204,z0,z2,z7,z8,z343]),(0,[z0,z2,z18,z166,z8,z5])],[(0,[z0,z2,z7,z469,z8,z4]),(0,[z470,z0,z2,z7,z8,z4]),(0,[z2,z7,z8,z348,z400,z5]),(0,[z0,z2,z7,z8,z471,z5])],[(0,[z27,z0,z2,z19,z8,z10]),(0,[z472,z0,z2,z7,z8,z4]),(0,[z0,z7,z48,z4,z222,z5]),(0,[z120,z0,z2,z18,z7,z8]),(0,[z0,z2,z7,z473,z4,z31]),(0,[z0,z2,z18,z7,z8,z93]),(0,[z0,z2,z94,z7,z185,z76])],[(0,[z42,z0,z65,z2,z8,z5]),(0,[z0,z2,z7,z8,z474,z5]),(0,[z0,z78,z7,z10,z222,z5]),(0,[z0,z7,z475,z8,z4,z5]),(1,[z0,z2,z7,z20,z4]),(0,[z85,z0,z2,z146,z8,z10]),(0,[z0,z2,z7,z20,z10,z5]),(0,[z0,z2,z7,z8,z343,z4])],[(0,[z0,z2,z7,z8,z476,z5]),(0,[z0,z1,z65,z2,z7,z5]),(0,[z0,z2,z7,z477,z4,z5]),(0,[z0,z2,z149,z8,z4,z10]),(0,[z0,z349,z2,z75,z8,z5])]],
   [[(0,[z0,z2,z75,z8,z10,z5]),(0,[z0,z2,z7,z8,z10,z478]),(0,[z0,z2,z18,z12,z8,z10]),(0,[z0,z2,z19,z20,z4,z10])],[(0,[z27,z2,z7,z110,z4,z5]),(0,[z81,z0,z82,z8,z362,z5]),(0,[z0,z78,z7,z4,z220,z222])],[(0,[z0,z2,z14,z18,z7,z8]),(0,[z0,z2,z7,z479,z8,z5]),(0,[z0,z480,z2,z19,z8,z4]),(0,[z37,z0,z2,z7,z8,z398]),(0,[z0,z481,z7,z8,z4,z482])],[(0,[z393,z2,z7,z8,z4,z192]),(0,[z0,z2,z116,z7,z458,z4]),(0,[z0,z2,z7,z483,z4,z5]),(0,[z0,z2,z86,z8,z10,z31])],[(0,[z0,z25,z2,z7,z8,z57])],[(0,[z0,z2,z484,z7,z8,z5]),(0,[z0,z2,z7,z8,z4,z63]),(0,[z85,z0,z2,z86,z8,z10]),(0,[z0,z2,z7,z8,z4,z485]),(0,[z0,z25,z2,z7,z486,z4])],[(0,[z0,z2,z19,z399,z8,z4]),(0,[z0,z2,z8,z10,z487,z5]),(0,[z488,z2,z19,z7,z8,z4])],[(0,[z191,z489,z2,z7,z8,z4]),(0,[z2,z7,z8,z4,z490,z5]),(0,[z0,z2,z491,z7,z8,z4]),(0,[z37,z0,z2,z7,z8,z492])],[(0,[z37,z0,z65,z2,z7,z8]),(0,[z2,z7,z8,z400,z236,z5]),(0,[z0,z2,z7,z8,z493,z4]),(0,[z0,z232,z335,z160,z8,z5]),(0,[z0,z2,z7,z494,z8,z5]),(0,[z0,z2,z7,z8,z4,z495]),(0,[z0,z25,z2,z19,z8,z10]),(0,[z0,z2,z19,z8,z4,z421])],[(0,[z2,z7,z61,z110,z4,z5]),(0,[z37,z0,z2,z496,z8,z4]),(0,[z0,z16,z7,z8,z497,z5]),(0,[z0,z2,z7,z498,z8,z4]),(0,[z37,z0,z2,z104,z30,z4]),(0,[z499,z2,z7,z8,z4,z500])],[(0,[z501,z0,z2,z7,z8,z4]),(0,[z0,z212,z2,z19,z8,z10]),(0,[z85,z0,z2,z7,z8,z131]),(0,[z0,z2,z94,z7,z8,z4])],[(0,[z424,z37,z2,z359,z8,z4]),(0,[z0,z232,z18,z160,z8,z5]),(0,[z502,z0,z2,z7,z20,z4])],[(0,[z0,z2,z7,z8,z4,z503]),(0,[z0,z2,z18,z504,z8,z5])],[(0,[z263,z25,z2,z7,z8,z236]),(0,[z0,z2,z7,z8,z505,z5]),(0,[z39,z0,z2,z8,z343,z10])],[(0,[z408,z218,z7,z8,z4,z5]),(0,[z0,z2,z7,z8,z506,z5]),(0,[z507,z0,z2,z8,z10,z5]),(0,[z0,z2,z19,z508,z8,z4])],[(0,[z0,z2,z3,z19,z8,z4]),(0,[z0,z2,z19,z509,z8,z4]),(0,[z0,z16,z7,z8,z17,z31]),(0,[z406,z0,z2,z7,z8,z10])]],
   [[(0,[z0,z230,z7,z243,z8,z4]),(0,[z0,z2,z7,z12,z8,z10]),(0,[z0,z2,z18,z510,z7,z8])],[(0,[z0,z2,z511,z7,z8,z4]),(0,[z0,z2,z512,z7,z8,z5]),(0,[z0,z2,z7,z8,z513,z4]),(0,[z0,z25,z2,z18,z7,z8]),(0,[z0,z2,z7,z8,z343,z187]),(0,[z514,z2,z19,z7,z8,z4]),(0,[z0,z2,z332,z8,z4,z5]),(0,[z0,z2,z7,z515,z4,z31])],[(0,[z0,z2,z516,z8,z4,z5]),(0,[z0,z2,z7,z8,z4,z208]),(0,[z0,z2,z7,z8,z129,z10]),(0,[z60,z0,z2,z8,z10,z5]),(0,[z37,z0,z2,z7,z8,z517])],[(0,[z0,z518,z2,z7,z8,z4])],[(0,[z0,z2,z44,z7,z8,z31]),(0,[z37,z0,z2,z7,z419,z8]),(0,[z0,z107,z2,z7,z519,z5]),(0,[z0,z2,z18,z7,z405,z8]),(0,[z0,z2,z7,z8,z62,z131])],[(0,[z2,z408,z7,z8,z4,z5]),(0,[z0,z2,z7,z8,z4,z520]),(0,[z0,z521,z2,z7,z8,z5]),(0,[z0,z2,z29,z7,z10,z31])],[(0,[z0,z2,z522,z8,z4,z5]),(0,[z0,z78,z7,z4,z222,z310]),(0,[z0,z326,z25,z2,z7,z8]),(0,[z0,z523,z25,z2,z7,z4]),(0,[z0,z2,z7,z524,z8,z4])],[(0,[z525,z2,z526,z7,z8,z5]),(0,[z37,z0,z2,z86,z8,z4]),(0,[z0,z25,z2,z7,z8,z527])],[(0,[z0,z78,z326,z7,z222,z5]),(0,[z0,z2,z7,z8,z528,z4]),(0,[z87,z0,z2,z19,z8,z4])],[(0,[z191,z529,z2,z7,z8,z4]),(0,[z37,z39,z0,z2,z29,z4])],[(1,[z0,z7,z475,z8,z4]),(0,[z37,z0,z2,z7,z8,z530]),(0,[z37,z0,z2,z149,z8,z4]),(0,[z531,z0,z2,z75,z8,z4]),(0,[z0,z2,z532,z8,z4,z5])],[(0,[z27,z2,z7,z61,z10,z5]),(0,[z438,z2,z7,z8,z400,z5]),(0,[z81,z0,z18,z82,z8,z5]),(0,[z120,z0,z2,z7,z8,z240]),(0,[z0,z2,z7,z8,z88,z187])],[(0,[z533,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z534,z8,z4]),(0,[z0,z2,z116,z19,z7,z10]),(0,[z204,z0,z2,z7,z8,z131])],[(0,[z0,z2,z18,z7,z8,z200]),(0,[z163,z2,z18,z7,z8,z153]),(0,[z0,z2,z535,z8,z10,z5]),(0,[z0,z2,z7,z8,z4,z536]),(0,[z0,z2,z18,z7,z8,z201]),(0,[z39,z0,z2,z29,z18,z5]),(0,[z72,z0,z2,z7,z458,z4]),(0,[z0,z2,z537,z7,z8,z5])],[(0,[z120,z39,z0,z2,z8,z10]),(0,[z39,z0,z2,z29,z19,z4]),(0,[z37,z0,z2,z7,z8,z538]),(0,[z0,z2,z7,z539,z4,z31])],[(0,[z0,z2,z7,z8,z4,z540]),(0,[z541,z0,z2,z7,z8,z4]),(0,[z542,z0,z2,z7,z8,z4]),(0,[z39,z0,z2,z29,z38,z5]),(0,[z85,z0,z2,z18,z8,z10])]],
   [[(0,[z0,z78,z18,z7,z222,z5]),(0,[z406,z0,z2,z104,z30,z4]),(0,[z0,z83,z7,z8,z10,z5])],[(0,[z0,z2,z7,z543,z4,z5]),(0,[z0,z2,z544,z7,z8,z5]),(0,[z46,z0,z2,z18,z8,z31]),(0,[z0,z108,z2,z463,z7,z5]),(1,[z0,z545,z2,z7,z4])],[(0,[z0,z2,z546,z8,z10,z5]),(0,[z217,z218,z18,z7,z8,z5]),(0,[z0,z2,z547,z8,z4,z5]),(0,[z0,z25,z2,z44,z7,z8])],[(0,[z217,z14,z218,z7,z8,z4]),(0,[z0,z2,z548,z7,z4,z31]),(0,[z0,z2,z7,z8,z549,z5]),(0,[z0,z2,z104,z19,z8,z10]),(0,[z0,z108,z2,z19,z8,z10]),(0,[z550,z529,z2,z7,z8,z4])],[(0,[z0,z2,z7,z8,z4,z551]),(0,[z0,z2,z166,z8,z4,z5]),(0,[z0,z2,z552,z8,z10,z5])],[(0,[z382,z2,z553,z8,z4,z5])],[(0,[z0,z2,z7,z8,z554,z5]),(0,[z0,z555,z2,z19,z8,z10]),(0,[z0,z2,z185,z75,z5,z76])],[(0,[z0,z2,z7,z8,z193,z31]),(0,[z0,z2,z556,z7,z8,z5])],[(0,[z0,z2,z7,z8,z10,z109]),(0,[z0,z114,z7,z8,z10,z115]),(0,[z0,z2,z116,z7,z10,z5]),(0,[z0,z2,z18,z7,z8,z493]),(0,[z37,z0,z2,z7,z8,z205]),(0,[z0,z2,z19,z166,z8,z4])],[(0,[z0,z2,z557,z8,z4,z5]),(0,[z46,z60,z0,z2,z8,z4]),(0,[z0,z2,z18,z331,z8,z5])],[(0,[z558,z0,z2,z7,z8,z4]),(0,[z0,z2,z559,z7,z8,z5]),(0,[z347,z2,z560,z7,z8,z5])],[(0,[z0,z2,z7,z8,z561,z5]),(0,[z0,z562,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z4,z563])],[(0,[z217,z25,z218,z7,z8,z4]),(0,[z0,z2,z7,z564,z8,z4]),(0,[z24,z0,z2,z7,z20,z4]),(0,[z0,z232,z160,z8,z4,z31]),(0,[z0,z266,z2,z7,z8,z62])],[(0,[z0,z2,z3,z8,z4,z31]),(0,[z0,z2,z3,z8,z10,z5]),(0,[z0,z2,z7,z8,z565,z5]),(0,[z0,z2,z19,z566,z8,z4]),(0,[z0,z2,z7,z8,z567,z5]),(0,[z0,z2,z7,z8,z10,z31]),(0,[z0,z2,z116,z19,z10,z5])],[(0,[z0,z2,z7,z8,z4,z568]),(0,[z2,z7,z8,z400,z4,z5]),(0,[z0,z569,z2,z7,z8,z5]),(0,[z0,z570,z2,z19,z8,z10]),(0,[z0,z2,z537,z149,z7,z8]),(0,[z0,z2,z149,z8,z4,z571])],[(0,[z37,z0,z1,z2,z7,z4]),(0,[z0,z2,z7,z8,z4,z572]),(0,[z0,z2,z7,z573,z4,z31]),(0,[z0,z2,z7,z8,z574,z5]),(0,[z60,z0,z2,z7,z20,z4])]],
   [[(0,[z575,z2,z7,z8,z4,z5]),(0,[z576,z0,z2,z7,z8,z4]),(0,[z0,z2,z142,z8,z10,z5])],[(0,[z0,z2,z184,z18,z7,z8]),(0,[z0,z2,z146,z8,z10,z31])],[(0,[z0,z2,z7,z577,z4,z5]),(0,[z0,z2,z578,z8,z4,z5]),(0,[z60,z0,z2,z7,z8,z4]),(0,[z120,z0,z2,z7,z8,z10]),(0,[z0,z2,z7,z579,z4,z31])],[(0,[z0,z2,z7,z8,z580,z5]),(0,[z0,z2,z19,z7,z477,z4]),(0,[z37,z0,z2,z7,z8,z581])],[(0,[z0,z2,z3,z8,z4,z582]),(0,[z0,z2,z7,z8,z102,z31]),(0,[z0,z2,z583,z8,z10,z5]),(0,[z0,z2,z7,z8,z4,z584]),(0,[z0,z2,z74,z7,z8,z4]),(0,[z0,z2,z19,z7,z8,z38]),(0,[z0,z2,z19,z7,z585,z4])],[(0,[z0,z2,z7,z8,z4,z283]),(0,[z85,z0,z2,z8,z30,z10]),(0,[z0,z2,z8,z344,z10,z5])],[(0,[z0,z586,z7,z8,z4,z5]),(0,[z0,z2,z19,z8,z587,z4]),(0,[z588,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z4,z589]),(0,[z87,z0,z2,z8,z4,z31]),(0,[z0,z2,z590,z8,z4,z5])],[(0,[z0,z2,z14,z7,z8,z10]),(0,[z0,z2,z7,z8,z517,z5]),(0,[z0,z2,z591,z7,z8,z4]),(0,[z0,z349,z2,z8,z10,z5]),(0,[z0,z2,z331,z8,z4,z5]),(0,[z0,z230,z2,z19,z8,z10])],[(0,[z0,z232,z19,z160,z8,z4]),(0,[z592,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z4,z593]),(0,[z0,z2,z440,z8,z10,z5]),(0,[z0,z2,z7,z8,z594,z4]),(0,[z0,z595,z596,z7,z8,z4])],[(0,[z0,z65,z25,z2,z7,z8]),(0,[z597,z0,z2,z7,z8,z4]),(0,[z0,z2,z19,z504,z8,z4]),(0,[z0,z2,z74,z19,z8,z4]),(0,[z0,z2,z7,z8,z598,z5])],[(0,[z599,z0,z2,z8,z4,z5]),(0,[z438,z2,z7,z8,z320,z5]),(0,[z0,z2,z600,z8,z10,z5]),(0,[z0,z25,z2,z7,z601,z4])],[(0,[z0,z2,z7,z8,z602,z5]),(0,[z0,z2,z7,z8,z338,z5]),(0,[z603,z0,z2,z8,z10,z5]),(0,[z0,z2,z7,z8,z88,z63]),(0,[z0,z173,z2,z7,z8,z31])],[(0,[z37,z438,z2,z7,z8,z348]),(0,[z0,z2,z7,z8,z604,z5]),(0,[z605,z0,z2,z7,z8,z4]),(0,[z0,z2,z463,z7,z4,z5])],[(0,[z606,z0,z2,z7,z8,z4]),(0,[z0,z2,z18,z7,z8,z298])],[(0,[z0,z2,z607,z7,z8,z4]),(0,[z0,z2,z608,z8,z4,z5]),(0,[z0,z25,z2,z7,z8,z448]),(0,[z0,z111,z25,z2,z7,z8]),(0,[z0,z2,z609,z7,z8,z4])],[(0,[z37,z24,z2,z7,z26,z4]),(0,[z37,z0,z2,z335,z7,z8]),(0,[z85,z0,z2,z19,z8,z4]),(0,[z0,z266,z2,z7,z8,z5])]],
   [[(0,[z438,z0,z2,z7,z20,z4]),(0,[z46,z0,z2,z19,z8,z10])],[(0,[z0,z2,z7,z8,z4,z610]),(0,[z0,z2,z44,z19,z7,z8]),(0,[z438,z2,z7,z8,z348,z5]),(0,[z0,z2,z104,z19,z30,z4]),(0,[z0,z2,z7,z20,z4,z31])],[(0,[z0,z2,z611,z7,z8,z4])],[(0,[z37,z0,z2,z416,z8,z4]),(0,[z0,z2,z19,z7,z8,z57]),(0,[z0,z2,z40,z19,z8,z206]),(0,[z0,z2,z75,z8,z4,z31])],[(0,[z612,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z448,z5]),(0,[z0,z2,z7,z8,z4,z613]),(0,[z0,z122,z2,z19,z8,z10]),(0,[z0,z2,z614,z8,z10,z5]),(0,[z309,z0,z2,z40,z7,z8]),(0,[z0,z2,z7,z92,z4,z31])],[(0,[z0,z16,z615,z7,z8,z5]),(0,[z0,z2,z7,z458,z8,z4]),(0,[z0,z2,z84,z8,z4,z10])],[(0,[z0,z25,z2,z7,z8,z10]),(0,[z60,z0,z25,z2,z8,z10]),(0,[z0,z2,z18,z616,z7,z8]),(0,[z37,z0,z2,z7,z8,z567])],[(0,[z0,z2,z7,z8,z4,z617]),(0,[z0,z2,z7,z8,z98,z5]),(0,[z0,z2,z618,z7,z8,z4]),(0,[z0,z78,z19,z7,z4,z222]),(0,[z0,z2,z7,z8,z57,z201]),(0,[z0,z2,z619,z8,z10,z5]),(0,[z0,z2,z19,z19,z8,z10]),(0,[z0,z2,z7,z8,z219,z31])],[(0,[z620,z0,z2,z7,z8,z4]),(0,[z81,z0,z19,z82,z8,z4]),(0,[z621,z2,z7,z8,z4,z5]),(0,[z37,z0,z2,z7,z8,z338]),(0,[z0,z303,z2,z7,z8,z10]),(0,[z0,z2,z7,z8,z205,z5])],[(0,[z0,z2,z7,z622,z8,z4]),(0,[z0,z2,z7,z585,z4,z5]),(0,[z0,z2,z7,z207,z4,z31]),(0,[z623,z0,z214,z2,z7,z8])],[(0,[z0,z2,z7,z624,z8,z4]),(1,[z0,z7,z8,z168,z5]),(0,[z0,z2,z625,z8,z10,z5])],[(0,[z2,z7,z8,z4,z315,z153]),(0,[z2,z7,z8,z4,z315,z5]),(0,[z0,z2,z7,z8,z626,z5]),(1,[z0,z2,z327,z4,z5]),(0,[z0,z2,z18,z7,z8,z627]),(0,[z0,z2,z7,z8,z4,z145]),(0,[z0,z2,z18,z7,z8,z427]),(0,[z0,z230,z354,z7,z8,z4]),(0,[z0,z2,z19,z8,z205,z206])],[(0,[z217,z42,z218,z8,z4,z5]),(0,[z0,z628,z2,z7,z8,z4]),(0,[z0,z2,z18,z8,z587,z5]),(0,[z629,z2,z7,z8,z4,z5])],[(0,[z0,z2,z18,z7,z8,z138]),(0,[z0,z2,z84,z19,z7,z8]),(0,[z37,z0,z2,z364,z8,z4]),(0,[z37,z0,z2,z630,z8,z4])],[(0,[z81,z0,z631,z8,z4,z5]),(0,[z0,z293,z7,z8,z4,z5]),(0,[z0,z2,z7,z8,z4,z632]),(0,[z0,z2,z633,z8,z4,z5]),(0,[z0,z2,z634,z8,z4,z5])],[(0,[z0,z2,z7,z635,z4,z5]),(0,[z217,z218,z19,z7,z8,z4]),(0,[z0,z25,z2,z7,z4,z636]),(0,[z0,z637,z2,z7,z20,z4])]],
   [[(0,[z163,z136,z2,z7,z8,z4]),(0,[z0,z78,z7,z193,z222,z5]),(0,[z120,z0,z2,z7,z30,z4]),(0,[z0,z2,z29,z19,z8,z10]),(0,[z113,z0,z2,z7,z8,z10]),(0,[z0,z2,z638,z7,z8,z4])],[(0,[z37,z0,z2,z75,z8,z4]),(0,[z0,z545,z2,z7,z4,z5])],[(0,[z0,z2,z7,z8,z639,z5]),(0,[z2,z7,z8,z4,z271,z5]),(1,[z0,z2,z20,z4,z10]),(0,[z309,z0,z2,z19,z8,z10]),(0,[z0,z2,z7,z640,z20,z4])],[(0,[z120,z0,z2,z7,z92,z4]),(2,[z0,z2,z20,z10]),(0,[z0,z2,z18,z7,z641,z8])],[(0,[z0,z2,z7,z330,z8,z10]),(0,[z0,z2,z7,z8,z4,z315]),(0,[z2,z7,z8,z4,z192,z315]),(0,[z0,z2,z7,z8,z4,z642]),(0,[z0,z2,z7,z8,z92,z131])],[(0,[z37,z0,z2,z7,z8,z474]),(0,[z0,z2,z19,z165,z8,z10]),(0,[z0,z2,z40,z7,z20,z4]),(0,[z37,z0,z2,z332,z8,z4])],[(0,[z37,z0,z2,z643,z8,z4]),(0,[z0,z107,z108,z2,z7,z459])],[(0,[z0,z2,z644,z7,z8,z4]),(0,[z0,z2,z7,z8,z4,z645]),(0,[z0,z25,z2,z104,z30,z4]),(0,[z0,z2,z7,z8,z62,z187])],[(0,[z0,z2,z7,z646,z8,z4]),(0,[z0,z2,z18,z7,z12,z8]),(0,[z0,z2,z7,z8,z10,z272])],[(0,[z424,z2,z330,z359,z8,z4])],[(0,[z217,z0,z2,z19,z8,z10]),(0,[z0,z2,z7,z8,z647,z5]),(0,[z191,z2,z7,z8,z4,z192]),(0,[z191,z2,z7,z8,z4,z315]),(0,[z0,z2,z19,z164,z8,z10]),(0,[z0,z2,z463,z7,z5,z76])],[(0,[z0,z23,z2,z7,z10,z5]),(0,[z60,z0,z2,z7,z8,z71])],[(0,[z0,z2,z7,z8,z225,z5]),(0,[z319,z0,z2,z19,z8,z10])],[(0,[z0,z2,z643,z8,z10,z5]),(0,[z0,z25,z2,z7,z4,z648]),(0,[z0,z2,z7,z313,z4,z5])],[(0,[z0,z189,z2,z3,z8,z5]),(0,[z0,z2,z7,z8,z4,z203]),(0,[z0,z2,z18,z7,z8,z197]),(0,[z27,z2,z7,z61,z4,z31]),(0,[z0,z2,z18,z7,z8,z278]),(0,[z0,z25,z2,z7,z4,z487])],[(0,[z0,z2,z7,z8,z4,z649]),(0,[z0,z2,z650,z8,z10,z5]),(0,[z0,z2,z7,z651,z8,z4])]],
   [[(0,[z0,z7,z123,z48,z4,z5]),(0,[z37,z0,z2,z614,z8,z4]),(0,[z0,z2,z7,z8,z20,z10]),(0,[z603,z0,z2,z19,z8,z4])],[(0,[z0,z2,z7,z8,z492,z5]),(0,[z0,z2,z19,z7,z8,z193])],[(0,[z0,z1,z2,z14,z7,z4]),(0,[z0,z2,z7,z8,z4,z652]),(0,[z0,z25,z2,z7,z419,z8]),(0,[z0,z232,z2,z7,z20,z4])],[(0,[z0,z2,z653,z7,z8,z5]),(0,[z0,z2,z654,z8,z4,z5]),(0,[z0,z2,z7,z8,z4,z655]),(0,[z0,z16,z656,z7,z8,z5])],[(0,[z0,z2,z18,z657,z8,z5])],[(0,[z438,z658,z2,z7,z8,z5]),(0,[z0,z2,z18,z7,z8,z220]),(0,[z0,z2,z354,z19,z8,z10]),(0,[z0,z2,z86,z332,z8,z4]),(0,[z0,z2,z265,z166,z8,z5])],[(0,[z0,z2,z7,z8,z10,z310]),(0,[z659,z0,z2,z7,z8,z4]),(0,[z0,z2,z184,z7,z8,z10]),(0,[z0,z2,z7,z8,z4,z660]),(0,[z0,z107,z108,z2,z7,z427])],[(0,[z0,z2,z7,z661,z8,z4]),(0,[z0,z2,z662,z7,z8,z4]),(0,[z0,z663,z2,z7,z8,z4]),(0,[z46,z0,z2,z116,z19,z4])],[(0,[z235,z0,z2,z19,z8,z10]),(0,[z0,z2,z94,z18,z7,z8]),(0,[z0,z2,z7,z20,z664,z4])],[(0,[z217,z23,z218,z7,z4,z5]),(0,[z0,z107,z2,z7,z665,z5]),(0,[z0,z2,z512,z7,z8,z201]),(0,[z0,z2,z7,z8,z10,z318])],[(0,[z372,z0,z2,z19,z8,z10]),(0,[z0,z2,z7,z8,z105,z31])],[(0,[z0,z2,z7,z8,z4,z666]),(0,[z0,z2,z116,z7,z4,z31]),(0,[z0,z2,z40,z7,z8,z187])],[(0,[z0,z2,z7,z8,z667,z5]),(0,[z0,z2,z331,z146,z8,z5])],[(0,[z0,z23,z2,z14,z7,z4]),(0,[z0,z2,z668,z7,z8,z5]),(0,[z0,z2,z669,z8,z10,z5]),(0,[z0,z2,z40,z19,z7,z20])],[(0,[z0,z2,z7,z670,z8,z5]),(0,[z0,z2,z671,z7,z8,z5]),(0,[z0,z2,z287,z8,z10,z5]),(0,[z0,z390,z2,z75,z8,z5]),(0,[z0,z2,z19,z8,z4,z672]),(0,[z0,z121,z2,z7,z8,z31])],[(0,[z0,z189,z2,z14,z7,z8]),(0,[z0,z16,z2,z19,z8,z10]),(0,[z0,z2,z8,z30,z10,z5])]],
   [[(0,[z0,z2,z673,z7,z8,z4]),(0,[z0,z2,z335,z7,z8,z31]),(0,[z0,z2,z674,z7,z8,z5]),(0,[z0,z2,z7,z675,z4,z5]),(0,[z0,z2,z86,z74,z8,z4])],[(0,[z0,z2,z7,z8,z4,z676]),(0,[z0,z2,z677,z8,z4,z5]),(0,[z0,z2,z7,z8,z4,z678]),(0,[z679,z0,z2,z18,z8,z5])],[(0,[z0,z2,z8,z129,z4,z10]),(0,[z0,z2,z18,z7,z8,z338])],[(0,[z0,z2,z680,z7,z8,z5]),(0,[z0,z2,z7,z8,z400,z5]),(0,[z0,z2,z7,z8,z131,z31]),(0,[z0,z2,z142,z8,z4,z31])],[(0,[z0,z2,z681,z8,z10,z5])],[(0,[z0,z2,z682,z7,z8,z5]),(0,[z39,z0,z2,z8,z10,z5]),(0,[z0,z2,z18,z7,z8,z683]),(0,[z0,z25,z2,z7,z8,z170])],[(0,[z0,z2,z7,z8,z4,z684]),(0,[z0,z2,z7,z8,z4,z685]),(0,[z0,z25,z2,z7,z8,z205])],[(0,[z0,z2,z18,z7,z8,z231]),(0,[z0,z2,z7,z686,z8,z4]),(0,[z0,z2,z30,z10,z5,z31]),(0,[z0,z2,z238,z8,z10,z5]),(0,[z0,z2,z7,z8,z62,z63])],[(0,[z0,z2,z7,z687,z8,z4]),(0,[z0,z2,z688,z8,z10,z5]),(0,[z0,z2,z19,z243,z8,z10]),(0,[z0,z2,z327,z8,z4,z5])],[(0,[z0,z689,z2,z7,z4,z5]),(0,[z0,z2,z7,z8,z10,z356]),(0,[z0,z2,z18,z690,z8,z5]),(0,[z0,z2,z691,z7,z8,z5])],[(0,[z0,z2,z18,z7,z8,z247]),(0,[z0,z114,z692,z7,z8,z4]),(0,[z0,z2,z693,z8,z4,z5])],[(0,[z0,z2,z7,z8,z4,z694]),(0,[z0,z2,z7,z8,z4,z291]),(0,[z0,z2,z695,z8,z4,z5]),(0,[z0,z696,z2,z74,z8,z4])],[],[(0,[z0,z2,z19,z7,z8,z448]),(0,[z0,z2,z327,z104,z4,z5]),(0,[z0,z2,z394,z19,z8,z10]),(0,[z85,z0,z2,z7,z8,z4]),(0,[z0,z2,z18,z7,z8,z697])],[(0,[z0,z2,z698,z7,z8,z4]),(0,[z0,z2,z699,z7,z8,z4]),(0,[z2,z7,z110,z26,z4,z5]),(0,[z0,z2,z19,z8,z4,z700]),(0,[z0,z481,z7,z8,z4,z115]),(0,[z0,z2,z18,z7,z8,z459])],[(0,[z0,z1,z2,z7,z54,z4]),(0,[z227,z0,z2,z18,z7,z8]),(0,[z0,z2,z7,z8,z4,z701]),(0,[z0,z2,z7,z8,z702,z5]),(0,[z703,z0,z2,z7,z8,z4]),(0,[z0,z704,z19,z7,z8,z4]),(0,[z0,z2,z7,z8,z380,z31])]],
   [[(0,[z0,z2,z7,z8,z705,z5]),(0,[z0,z25,z2,z7,z8,z105]),(0,[z0,z2,z7,z8,z706,z5]),(0,[z0,z122,z707,z7,z4,z5]),(0,[z0,z2,z708,z8,z10,z5]),(0,[z72,z0,z2,z30,z10,z5]),(0,[z0,z2,z19,z8,z10,z31]),(0,[z0,z25,z2,z7,z8,z709])],[(0,[z0,z2,z7,z8,z710,z5]),(0,[z0,z2,z7,z8,z88,z5]),(0,[z0,z2,z18,z8,z343,z10])],[(0,[z0,z2,z7,z8,z4,z711]),(0,[z37,z0,z2,z7,z8,z362]),(0,[z0,z2,z104,z7,z92,z4]),(0,[z39,z0,z2,z30,z10,z5]),(0,[z0,z2,z19,z7,z20,z10]),(0,[z0,z2,z7,z185,z93,z76])],[(0,[z0,z2,z712,z7,z8,z5]),(0,[z713,z2,z7,z8,z4,z192]),(0,[z81,z37,z0,z82,z8,z4]),(0,[z0,z2,z7,z123,z20,z4]),(0,[z0,z2,z7,z8,z714,z4])],[(0,[z0,z2,z7,z8,z92,z4]),(0,[z0,z2,z715,z7,z20,z4]),(0,[z0,z107,z108,z2,z19,z7])],[(0,[z0,z2,z7,z8,z716,z4]),(0,[z81,z0,z2,z149,z8,z4]),(0,[z0,z717,z2,z7,z4,z31]),(0,[z0,z718,z7,z243,z8,z4]),(0,[z0,z2,z327,z30,z4,z5]),(0,[z72,z0,z2,z7,z129,z4]),(0,[z0,z2,z7,z719,z8,z4]),(0,[z0,z2,z19,z7,z8,z10]),(0,[z0,z2,z7,z8,z10,z392]),(0,[z46,z0,z2,z331,z8,z5]),(0,[z0,z2,z7,z8,z709,z5]),(0,[z204,z0,z254,z2,z166,z8])],[(0,[z0,z2,z7,z8,z4,z720]),(0,[z0,z2,z7,z721,z8,z5]),(0,[z27,z25,z2,z7,z61,z4]),(0,[z0,z722,z2,z7,z4,z31]),(0,[z0,z2,z616,z7,z8,z4]),(0,[z0,z25,z2,z7,z4,z723])],[(0,[z0,z2,z264,z8,z10,z5]),(0,[z0,z2,z104,z30,z4,z5]),(0,[z0,z2,z7,z8,z724,z4])],[(0,[z0,z2,z7,z404,z10,z5]),(0,[z0,z555,z7,z8,z725,z5])],[(0,[z0,z562,z2,z18,z7,z8]),(0,[z0,z2,z7,z8,z38,z31]),(0,[z0,z2,z7,z8,z378,z726]),(0,[z0,z2,z7,z727,z4,z31])],[(0,[z0,z2,z327,z7,z4,z5]),(0,[z393,z0,z2,z7,z20,z4]),(0,[z0,z728,z2,z7,z4,z31])],[(0,[z0,z2,z7,z729,z8,z4]),(0,[z0,z730,z2,z7,z8,z5]),(0,[z0,z2,z7,z8,z4,z731]),(0,[z0,z2,z732,z8,z10,z5]),(0,[z0,z2,z7,z8,z4,z733]),(1,[z0,z7,z48,z4,z5]),(0,[z0,z78,z25,z7,z4,z222]),(0,[z0,z2,z7,z8,z344,z5])],[(0,[z81,z0,z25,z82,z8,z4]),(0,[z204,z0,z2,z7,z20,z4])],[(0,[z0,z2,z7,z8,z4,z734]),(0,[z0,z2,z7,z8,z735,z5]),(0,[z0,z25,z2,z335,z7,z8]),(0,[z0,z245,z2,z19,z8,z10])],[(0,[z0,z2,z7,z8,z4,z5]),(0,[z0,z2,z50,z7,z8,z5]),(0,[z0,z107,z108,z2,z7,z31])],[(0,[z0,z22,z2,z7,z8,z4]),(0,[z263,z2,z19,z7,z8,z236]),(0,[z0,z2,z7,z736,z8,z4]),(0,[z0,z2,z7,z20,z20,z4]),(0,[z0,z2,z116,z19,z7,z205]),(0,[z737,z0,z2,z8,z4,z5])]],
   [[(0,[z0,z2,z7,z738,z8,z4]),(0,[z0,z2,z7,z8,z20,z205]),(0,[z739,z0,z368,z7,z8,z4]),(0,[z0,z107,z2,z463,z7,z5])],[(0,[z42,z0,z2,z8,z476,z5]),(0,[z163,z2,z740,z7,z8,z4]),(0,[z81,z0,z82,z8,z225,z5]),(0,[z0,z2,z7,z741,z8,z4]),(0,[z742,z0,z2,z7,z8,z4]),(0,[z0,z2,z743,z7,z8,z5]),(0,[z0,z2,z19,z657,z8,z4]),(0,[z0,z2,z19,z8,z4,z206])],[(0,[z0,z2,z7,z744,z4,z5]),(0,[z0,z2,z7,z745,z8,z4]),(0,[z0,z107,z2,z19,z8,z10])],[(0,[z0,z1,z2,z7,z10,z5]),(0,[z0,z1,z2,z7,z4,z31]),(0,[z0,z2,z746,z8,z4,z5]),(0,[z0,z2,z252,z8,z10,z31]),(0,[z0,z2,z149,z8,z10,z5])],[(0,[z0,z2,z7,z8,z4,z747]),(0,[z0,z2,z7,z8,z4,z748]),(0,[z0,z2,z19,z20,z10,z5]),(0,[z0,z2,z18,z7,z8,z20]),(0,[z155,z0,z7,z449,z8,z4]),(0,[z0,z2,z238,z7,z20,z4])],[(0,[z0,z2,z7,z8,z4,z749]),(0,[z382,z0,z2,z7,z20,z4]),(0,[z0,z2,z7,z8,z4,z750]),(0,[z0,z157,z7,z8,z4,z5]),(0,[z0,z2,z18,z90,z7,z8])],[(0,[z0,z2,z751,z7,z8,z4]),(0,[z0,z2,z7,z8,z4,z752]),(0,[z120,z39,z0,z2,z29,z4]),(1,[z0,z2,z19,z20,z10]),(0,[z0,z2,z84,z8,z10,z5]),(0,[z0,z2,z166,z8,z62,z5])],[(0,[z753,z0,z2,z8,z4,z5]),(0,[z120,z0,z2,z149,z8,z4]),(1,[z0,z2,z463,z7,z5]),(0,[z0,z2,z434,z8,z4,z31])],[(0,[z424,z2,z359,z8,z4,z31]),(0,[z424,z2,z359,z8,z10,z5]),(0,[z0,z2,z7,z754,z8,z4]),(0,[z27,z755,z2,z7,z4,z5]),(0,[z0,z756,z2,z7,z8,z5]),(0,[z0,z2,z7,z8,z338,z10]),(0,[z437,z2,z7,z8,z10,z5]),(0,[z0,z2,z757,z8,z4,z5])],[(0,[z0,z2,z7,z758,z4,z5]),(1,[z0,z2,z19,z8,z10]),(0,[z0,z2,z759,z7,z270,z5])],[(0,[z0,z326,z2,z19,z7,z8])],[(0,[z0,z2,z7,z8,z175,z5]),(0,[z0,z2,z760,z8,z10,z5]),(0,[z0,z2,z7,z8,z761,z5])],[(1,[z0,z2,z30,z10,z31])],[(0,[z37,z0,z2,z3,z8,z4]),(0,[z0,z762,z2,z7,z8,z4]),(0,[z0,z2,z335,z19,z7,z8]),(0,[z0,z2,z90,z7,z8,z4]),(0,[z0,z2,z94,z7,z8,z10]),(0,[z0,z2,z763,z7,z8,z4])],[(0,[z217,z65,z218,z7,z8,z5]),(0,[z0,z764,z2,z7,z8,z5]),(0,[z0,z23,z2,z7,z4,z31]),(0,[z191,z0,z2,z7,z20,z4]),(0,[z0,z390,z7,z167,z8,z31])],[(0,[z424,z2,z359,z8,z102,z5]),(0,[z0,z2,z765,z8,z4,z5]),(0,[z0,z2,z766,z7,z8,z5]),(0,[z767,z2,z7,z8,z4,z5]),(0,[z37,z0,z2,z116,z7,z4]),(0,[z0,z25,z2,z75,z8,z4])]],
   [[(0,[z0,z2,z768,z8,z4,z5]),(0,[z0,z2,z7,z359,z20,z4]),(1,[z0,z329,z8,z4,z5]),(0,[z0,z25,z2,z7,z769,z4]),(0,[z0,z114,z7,z449,z8,z4]),(0,[z0,z2,z149,z30,z4,z31]),(0,[z0,z2,z18,z19,z7,z8])],[(0,[z217,z1,z218,z7,z4,z5]),(0,[z0,z2,z19,z7,z419,z8])],[(0,[z0,z770,z2,z7,z20,z4]),(0,[z771,z0,z2,z7,z8,z4])],[(0,[z376,z0,z23,z2,z7,z4]),(0,[z438,z772,z2,z7,z8,z5]),(0,[z297,z0,z2,z7,z8,z4]),(0,[z0,z25,z2,z7,z8,z474]),(0,[z37,z0,z2,z146,z8,z10]),(0,[z0,z2,z18,z8,z10,z63])],[(0,[z42,z0,z2,z14,z8,z4]),(0,[z0,z2,z7,z8,z773,z5]),(0,[z0,z2,z7,z8,z513,z10]),(0,[z0,z2,z7,z8,z92,z88])],[],[(0,[z0,z2,z7,z20,z4,z115]),(0,[z0,z2,z774,z7,z8,z4])],[(0,[z0,z2,z7,z8,z4,z775]),(0,[z46,z0,z2,z18,z8,z63])],[(0,[z0,z2,z7,z776,z8,z4]),(0,[z0,z777,z2,z7,z8,z4]),(0,[z0,z2,z7,z778,z4,z31]),(0,[z0,z2,z7,z779,z4,z31]),(0,[z0,z2,z7,z780,z4,z31])],[(0,[z0,z78,z7,z4,z222,z5]),(0,[z0,z114,z596,z7,z8,z4]),(0,[z39,z0,z25,z2,z8,z10]),(0,[z0,z2,z19,z7,z409,z4])],[(0,[z0,z371,z7,z8,z4,z115]),(0,[z37,z0,z2,z86,z8,z10]),(0,[z0,z2,z86,z8,z343,z10]),(0,[z0,z781,z2,z7,z8,z4])],[(0,[z0,z232,z160,z8,z474,z5]),(0,[z0,z2,z782,z7,z8,z4]),(0,[z0,z2,z18,z7,z165,z31]),(0,[z37,z0,z2,z40,z19,z8])],[(0,[z163,z2,z7,z8,z4,z315]),(0,[z0,z2,z7,z8,z4,z783]),(0,[z69,z0,z7,z475,z8,z4]),(0,[z0,z2,z18,z104,z30,z5]),(0,[z0,z2,z7,z8,z4,z784])],[(0,[z0,z2,z7,z20,z26,z4]),(0,[z0,z2,z785,z7,z8,z4]),(0,[z0,z2,z510,z7,z8,z4])],[(0,[z42,z0,z1,z2,z4,z5]),(0,[z0,z786,z2,z7,z4,z31]),(0,[z0,z2,z7,z8,z530,z5]),(0,[z0,z2,z7,z787,z8,z4])],[(0,[z85,z0,z254,z2,z7,z8]),(0,[z0,z2,z19,z552,z8,z4])]],
   [[(0,[z0,z2,z788,z7,z20,z4]),(0,[z0,z2,z7,z8,z4,z789]),(0,[z0,z326,z2,z7,z8,z31]),(0,[z0,z2,z7,z30,z4,z201]),(0,[z0,z2,z149,z7,z20,z4])],[(0,[z0,z2,z18,z7,z8,z109]),(0,[z0,z790,z2,z7,z4,z5]),(0,[z0,z114,z18,z7,z8,z115]),(0,[z0,z2,z328,z8,z4,z31])],[(0,[z191,z2,z7,z8,z4,z500]),(0,[z0,z2,z19,z82,z8,z10]),(0,[z791,z2,z7,z8,z4,z5]),(0,[z0,z2,z7,z8,z4,z792]),(0,[z0,z301,z7,z167,z8,z5]),(0,[z0,z2,z19,z7,z20,z205])],[(0,[z0,z2,z218,z7,z20,z4]),(0,[z0,z2,z7,z8,z793,z5]),(0,[z0,z2,z7,z8,z10,z63]),(0,[z0,z2,z19,z8,z20,z10]),(0,[z85,z0,z2,z166,z8,z4]),(0,[z46,z0,z2,z19,z8,z205]),(0,[z72,z0,z545,z2,z7,z4])],[(0,[z0,z2,z7,z8,z794,z5]),(0,[z227,z0,z2,z7,z8,z10]),(0,[z37,z0,z2,z19,z8,z131]),(0,[z0,z2,z19,z7,z8,z170]),(0,[z795,z0,z2,z7,z8,z4])],[(0,[z0,z2,z19,z8,z205,z10])],[(0,[z424,z0,z2,z7,z20,z4]),(0,[z0,z2,z7,z796,z8,z5]),(0,[z263,z0,z2,z75,z8,z5]),(0,[z0,z2,z18,z7,z8,z31]),(0,[z0,z2,z19,z8,z10,z421]),(0,[z0,z2,z18,z7,z8,z130])],[(0,[z42,z0,z23,z2,z4,z5]),(0,[z0,z797,z2,z7,z8,z4]),(0,[z0,z2,z7,z798,z4,z31]),(1,[z0,z2,z8,z129,z10]),(0,[z60,z0,z2,z7,z8,z38])],[(0,[z0,z2,z18,z7,z8,z343])],[(0,[z799,z0,z2,z8,z4,z5]),(0,[z0,z2,z426,z7,z8,z10]),(0,[z0,z2,z18,z7,z8,z800]),(0,[z0,z2,z116,z7,z20,z4])],[(0,[z0,z2,z7,z8,z801,z5]),(0,[z0,z802,z2,z7,z8,z4]),(0,[z24,z803,z2,z7,z4,z5])],[(0,[z0,z2,z7,z804,z4,z31]),(0,[z0,z2,z84,z19,z8,z4])],[(0,[z263,z2,z7,z805,z8,z5]),(0,[z0,z2,z7,z806,z4,z31]),(0,[z0,z2,z7,z807,z8,z5]),(0,[z37,z0,z2,z18,z86,z8]),(0,[z60,z0,z2,z40,z7,z8])],[(0,[z0,z65,z2,z19,z7,z8]),(0,[z0,z2,z7,z8,z362,z31]),(0,[z0,z2,z18,z7,z154,z8]),(0,[z0,z2,z7,z8,z4,z58]),(0,[z0,z7,z361,z8,z4,z31])],[(0,[z0,z254,z2,z7,z20,z4])],[(0,[z0,z2,z19,z7,z8,z105]),(0,[z0,z2,z808,z7,z8,z5])]],
   [[(0,[z37,z263,z2,z7,z8,z236]),(0,[z0,z122,z7,z123,z10,z5]),(0,[z0,z122,z7,z123,z4,z31]),(0,[z0,z2,z7,z8,z10,z208])],[(0,[z0,z2,z7,z8,z809,z5]),(0,[z0,z810,z7,z8,z4,z115]),(0,[z703,z0,z2,z7,z8,z38]),(0,[z811,z0,z2,z7,z8,z131]),(0,[z204,z0,z254,z2,z7,z8])],[(0,[z37,z382,z2,z788,z8,z4]),(0,[z0,z111,z2,z19,z7,z8]),(0,[z0,z2,z160,z7,z20,z4]),(0,[z37,z0,z2,z18,z19,z8])],[(0,[z81,z0,z82,z8,z4,z5]),(0,[z0,z390,z7,z369,z8,z5]),(0,[z0,z390,z2,z7,z20,z4]),(0,[z120,z0,z2,z7,z8,z567])],[(0,[z227,z0,z65,z2,z7,z8]),(0,[z0,z812,z2,z7,z8,z5]),(0,[z0,z2,z7,z8,z4,z813]),(0,[z0,z2,z814,z7,z8,z4]),(0,[z37,z0,z2,z18,z8,z10]),(0,[z0,z2,z7,z449,z20,z4])],[(0,[z0,z2,z7,z8,z815,z5]),(0,[z0,z2,z816,z7,z8,z5]),(0,[z0,z817,z2,z7,z8,z4]),(0,[z0,z2,z249,z7,z8,z5])],[(0,[z818,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z4,z93]),(0,[z0,z2,z7,z185,z5,z76])],[(0,[z0,z2,z7,z819,z8,z5]),(0,[z24,z0,z2,z19,z8,z10]),(0,[z0,z2,z7,z8,z527,z5]),(0,[z0,z820,z2,z7,z8,z4]),(0,[z0,z2,z18,z7,z8,z183])],[(0,[z0,z2,z821,z7,z8,z5]),(0,[z0,z2,z7,z8,z4,z822]),(0,[z0,z2,z7,z8,z823,z5])],[(0,[z0,z2,z18,z7,z824,z8])],[(0,[z0,z2,z825,z7,z8,z4]),(0,[z0,z2,z7,z144,z8,z4]),(0,[z60,z0,z2,z19,z8,z10]),(0,[z826,z0,z2,z8,z4,z5])],[(0,[z0,z2,z7,z8,z4,z827]),(0,[z0,z2,z19,z61,z8,z10]),(0,[z0,z2,z7,z185,z828,z5]),(0,[z0,z2,z7,z829,z4,z31]),(0,[z251,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z452,z4,z31]),(0,[z0,z830,z2,z7,z8,z4])],[(0,[z0,z390,z7,z8,z168,z5])],[(0,[z0,z2,z831,z7,z8,z4])],[(0,[z0,z2,z29,z7,z4,z201]),(0,[z0,z2,z40,z7,z20,z5])],[(0,[z2,z7,z8,z4,z124,z5])]],
   [[(0,[z0,z114,z7,z475,z8,z4]),(0,[z0,z2,z19,z185,z8,z10]),(0,[z0,z2,z7,z20,z4,z832])],[(0,[z833,z42,z0,z2,z8,z4]),(0,[z0,z834,z2,z7,z4,z5]),(0,[z0,z2,z19,z8,z26,z10]),(0,[z0,z2,z40,z7,z8,z5]),(0,[z0,z2,z7,z185,z31,z76])],[(0,[z0,z2,z166,z8,z10,z5])],[(0,[z0,z65,z2,z7,z8,z31]),(0,[z0,z2,z835,z7,z8,z4]),(0,[z382,z2,z788,z8,z10,z5]),(0,[z69,z0,z2,z7,z20,z4]),(0,[z60,z0,z2,z18,z7,z8]),(0,[z0,z2,z8,z20,z4,z10]),(0,[z72,z0,z2,z7,z20,z4]),(0,[z0,z2,z19,z8,z539,z4])],[(0,[z836,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z837,z8,z4]),(0,[z0,z838,z2,z7,z8,z4]),(0,[z0,z7,z143,z8,z4,z5]),(0,[z0,z2,z7,z8,z343,z10]),(1,[z0,z2,z7,z20,z10])],[(0,[z424,z2,z359,z8,z105,z5]),(0,[z0,z839,z2,z7,z8,z5]),(0,[z0,z555,z7,z8,z17,z5]),(0,[z0,z2,z7,z840,z8,z4]),(0,[z0,z2,z7,z8,z4,z841]),(0,[z39,z0,z2,z7,z20,z4]),(0,[z0,z2,z19,z7,z8,z338])],[(0,[z0,z2,z7,z8,z842,z5]),(0,[z0,z2,z7,z824,z8,z4]),(0,[z0,z2,z19,z579,z8,z4])],[(0,[z0,z7,z8,z48,z4,z5]),(0,[z0,z2,z843,z7,z4,z31]),(0,[z0,z2,z18,z7,z458,z8]),(0,[z0,z844,z25,z2,z7,z4])],[(0,[z0,z111,z2,z7,z8,z31]),(0,[z0,z2,z7,z458,z8,z10]),(0,[z0,z2,z146,z8,z343,z10])],[(0,[z845,z0,z2,z19,z8,z4])],[(0,[z0,z2,z846,z8,z4,z5]),(0,[z37,z0,z2,z8,z30,z10])],[(0,[z0,z2,z3,z435,z8,z4]),(0,[z847,z0,z2,z8,z4,z5]),(0,[z2,z32,z359,z8,z4,z5]),(0,[z27,z2,z18,z7,z61,z5]),(0,[z263,z2,z7,z8,z236,z5]),(0,[z0,z2,z848,z8,z4,z5]),(0,[z438,z0,z2,z19,z8,z10]),(0,[z85,z0,z2,z18,z7,z8]),(0,[z0,z2,z7,z849,z4,z5]),(0,[z0,z2,z7,z165,z4,z31]),(0,[z0,z2,z7,z8,z567,z31])],[(0,[z0,z2,z14,z3,z8,z4]),(0,[z0,z850,z2,z7,z8,z5]),(0,[z325,z2,z7,z8,z4,z153])],[(0,[z0,z851,z2,z7,z8,z4]),(0,[z42,z0,z189,z2,z8,z5]),(0,[z0,z25,z2,z7,z8,z457])],[(0,[z0,z1,z189,z2,z7,z5]),(0,[z852,z0,z2,z18,z8,z5]),(0,[z0,z2,z8,z129,z30,z10]),(1,[z0,z2,z331,z8,z5]),(0,[z0,z2,z19,z75,z8,z4]),(0,[z575,z2,z7,z8,z4,z31]),(0,[z737,z0,z25,z2,z8,z4]),(0,[z0,z2,z453,z8,z4,z5])],[(0,[z0,z390,z853,z7,z8,z5]),(0,[z0,z390,z19,z7,z167,z8]),(0,[z0,z2,z104,z30,z4,z201]),(0,[z0,z854,z2,z7,z8,z4]),(0,[z39,z0,z2,z327,z4,z5])]],
   [[(0,[z0,z2,z32,z8,z4,z5]),(1,[z2,z7,z110,z4,z5]),(0,[z2,z7,z8,z110,z4,z5]),(0,[z0,z2,z7,z419,z8,z31]),(0,[z0,z2,z7,z8,z57,z31]),(1,[z0,z2,z84,z7,z8])],[(0,[z0,z7,z179,z8,z4,z5]),(0,[z0,z2,z512,z90,z7,z8]),(0,[z0,z2,z7,z8,z240,z5]),(0,[z37,z0,z2,z19,z20,z4]),(0,[z0,z254,z2,z7,z8,z88])],[(0,[z0,z2,z7,z20,z348,z4]),(0,[z0,z2,z855,z7,z8,z5]),(0,[z0,z2,z7,z8,z4,z856]),(0,[z0,z2,z7,z8,z857,z5]),(0,[z393,z0,z2,z19,z8,z10]),(0,[z0,z2,z19,z7,z8,z604])],[(0,[z0,z189,z2,z7,z8,z5]),(0,[z0,z2,z858,z7,z8,z5]),(0,[z85,z0,z2,z7,z8,z62]),(0,[z46,z0,z2,z149,z8,z4])],[(0,[z0,z2,z7,z8,z10,z589]),(0,[z37,z0,z2,z19,z8,z4]),(0,[z0,z2,z332,z19,z8,z4])],[(0,[z488,z2,z7,z8,z4,z5]),(0,[z0,z2,z19,z8,z10,z115]),(0,[z0,z2,z331,z8,z10,z5])],[(0,[z0,z2,z7,z8,z4,z200]),(0,[z0,z859,z7,z8,z4,z5]),(0,[z163,z2,z7,z8,z4,z153]),(0,[z0,z2,z7,z8,z4,z201]),(1,[z0,z2,z20,z10,z5])],[(0,[z37,z0,z189,z2,z7,z8]),(0,[z0,z2,z7,z8,z71,z5])],[(0,[z0,z2,z7,z8,z860,z5]),(0,[z0,z25,z2,z7,z861,z4]),(0,[z0,z2,z19,z8,z10,z725]),(0,[z862,z0,z2,z7,z8,z4]),(0,[z0,z2,z40,z142,z8,z5])],[(0,[z0,z2,z7,z863,z20,z4]),(0,[z0,z2,z7,z8,z213,z5])],[(0,[z0,z2,z7,z8,z4,z864]),(0,[z0,z2,z7,z20,z4,z187])],[(0,[z217,z218,z7,z8,z4,z5]),(0,[z227,z0,z1,z2,z7,z4]),(0,[z69,z0,z865,z7,z8,z4]),(0,[z0,z2,z7,z8,z4,z220]),(0,[z0,z2,z265,z8,z343,z10]),(0,[z0,z2,z630,z8,z10,z5]),(0,[z155,z0,z2,z7,z20,z4]),(0,[z531,z0,z2,z7,z8,z4])],[(0,[z0,z2,z512,z19,z7,z8]),(0,[z0,z696,z2,z7,z4,z31]),(0,[z455,z0,z2,z19,z8,z4]),(0,[z0,z2,z116,z19,z4,z206])],[(0,[z0,z2,z866,z8,z10,z5]),(0,[z0,z2,z7,z8,z867,z4])],[(0,[z0,z2,z868,z7,z4,z5]),(0,[z679,z0,z2,z19,z8,z4]),(0,[z0,z2,z7,z8,z869,z5]),(0,[z0,z2,z7,z8,z4,z870]),(0,[z0,z78,z2,z7,z20,z4]),(0,[z0,z2,z90,z7,z8,z57]),(0,[z0,z2,z7,z8,z528,z10]),(0,[z37,z0,z2,z7,z8,z823])],[(0,[z0,z871,z2,z7,z8,z5]),(0,[z0,z2,z7,z8,z474,z31]),(0,[z0,z2,z872,z7,z8,z4]),(0,[z0,z2,z19,z7,z849,z4])]],
   [[(0,[z163,z0,z2,z7,z20,z4]),(0,[z514,z2,z7,z8,z4,z5]),(0,[z39,z0,z2,z779,z4,z5]),(0,[z0,z2,z40,z19,z8,z10])],[(0,[z406,z0,z2,z8,z30,z10]),(0,[z0,z25,z2,z146,z8,z10])],[(0,[z0,z1,z2,z7,z4,z223]),(0,[z0,z873,z2,z7,z4,z5]),(0,[z0,z2,z7,z874,z4,z5]),(0,[z0,z2,z7,z8,z10,z613]),(0,[z37,z0,z2,z7,z8,z131])],[(0,[z875,z2,z7,z8,z4,z5]),(0,[z876,z0,z2,z8,z10,z5]),(0,[z0,z2,z7,z8,z4,z877]),(0,[z0,z2,z19,z7,z8,z878])],[(0,[z227,z0,z23,z2,z7,z4]),(0,[z60,z39,z0,z2,z8,z10]),(0,[z46,z37,z0,z2,z18,z8]),(0,[z0,z2,z18,z75,z8,z5]),(0,[z0,z25,z2,z18,z7,z31]),(0,[z0,z254,z2,z7,z8,z63])],[(0,[z0,z879,z2,z7,z8,z5]),(0,[z0,z880,z2,z7,z8,z5]),(0,[z0,z881,z2,z7,z8,z4]),(0,[z0,z2,z19,z7,z483,z4])],[(0,[z0,z2,z149,z7,z8,z4]),(0,[z195,z0,z2,z7,z20,z4]),(0,[z0,z2,z94,z75,z8,z4])],[(0,[z0,z2,z7,z8,z882,z5]),(0,[z0,z2,z883,z8,z10,z5]),(0,[z0,z2,z7,z475,z8,z4]),(0,[z0,z114,z2,z7,z20,z4]),(0,[z204,z0,z254,z2,z142,z8])],[(0,[z0,z65,z23,z2,z7,z5]),(0,[z0,z2,z7,z8,z884,z4]),(0,[z0,z2,z512,z104,z30,z5]),(1,[z0,z2,z12,z8,z10]),(0,[z0,z2,z19,z7,z8,z205]),(0,[z37,z0,z2,z7,z8,z667])],[(0,[z24,z2,z7,z26,z4,z5]),(0,[z0,z2,z7,z8,z4,z885]),(0,[z0,z2,z7,z8,z886,z5]),(0,[z0,z2,z29,z18,z7,z31]),(0,[z0,z2,z84,z7,z8,z4])],[(0,[z0,z108,z2,z7,z350,z5])],[(0,[z0,z2,z19,z167,z8,z10]),(0,[z0,z2,z508,z8,z10,z5]),(0,[z0,z2,z19,z8,z4,z10])],[(0,[z162,z42,z0,z2,z8,z4]),(0,[z0,z2,z7,z887,z8,z4]),(0,[z85,z39,z0,z2,z8,z10]),(0,[z0,z2,z633,z8,z4,z31])],[(0,[z0,z2,z7,z8,z4,z888]),(0,[z0,z2,z19,z8,z10,z236]),(0,[z0,z232,z2,z19,z8,z10]),(0,[z0,z2,z12,z8,z4,z10]),(0,[z46,z0,z25,z2,z18,z8]),(0,[z0,z2,z868,z19,z7,z4])],[(0,[z37,z0,z2,z889,z8,z4]),(0,[z455,z0,z2,z142,z8,z4])],[(0,[z0,z2,z890,z7,z8,z4]),(0,[z0,z2,z19,z8,z320,z10]),(0,[z0,z545,z2,z7,z4,z31])]],
   [[(0,[z0,z891,z2,z7,z8,z4]),(0,[z37,z0,z326,z2,z7,z8]),(0,[z0,z2,z7,z20,z4,z206])],[(0,[z0,z2,z7,z892,z8,z5]),(0,[z0,z562,z2,z7,z8,z10]),(0,[z0,z2,z7,z20,z4,z236]),(0,[z297,z0,z2,z18,z7,z8]),(0,[z0,z2,z7,z282,z4,z5]),(0,[z0,z7,z8,z168,z17,z5]),(0,[z0,z570,z245,z2,z7,z5]),(0,[z0,z2,z8,z539,z10,z5])],[(0,[z217,z408,z7,z8,z4,z5]),(0,[z0,z2,z7,z8,z4,z893]),(0,[z0,z2,z512,z7,z8,z31])],[(0,[z894,z0,z2,z7,z8,z4]),(0,[z0,z2,z895,z7,z8,z4])],[(0,[z0,z232,z329,z8,z4,z5]),(0,[z0,z16,z19,z7,z8,z17]),(0,[z0,z2,z7,z8,z343,z205]),(0,[z246,z0,z2,z7,z20,z4]),(0,[z37,z0,z2,z19,z8,z88]),(1,[z0,z2,z7,z20,z205])],[(0,[z0,z2,z896,z7,z8,z4]),(1,[z0,z2,z8,z20,z10])],[(0,[z0,z2,z7,z8,z4,z298]),(0,[z0,z2,z897,z8,z4,z5]),(0,[z0,z2,z8,z129,z10,z5]),(0,[z898,z0,z718,z7,z8,z4])],[(0,[z455,z0,z2,z7,z8,z88])],[(0,[z27,z2,z19,z7,z61,z4]),(0,[z438,z25,z2,z7,z8,z348]),(0,[z191,z2,z7,z8,z10,z192]),(0,[z0,z854,z2,z7,z8,z71]),(0,[z60,z0,z2,z7,z8,z10]),(0,[z0,z2,z899,z8,z10,z5])],[(0,[z0,z2,z900,z7,z4,z5]),(0,[z0,z2,z7,z8,z901,z5]),(0,[z0,z2,z29,z7,z117,z4])],[(0,[z902,z0,z2,z7,z8,z4]),(0,[z0,z2,z74,z7,z8,z10]),(0,[z0,z2,z7,z20,z4,z76]),(0,[z0,z2,z7,z20,z205,z5])],[(0,[z0,z903,z2,z7,z8,z4]),(0,[z0,z2,z889,z8,z10,z5]),(0,[z0,z2,z532,z8,z4,z31])],[(0,[z0,z2,z7,z8,z4,z904]),(0,[z0,z269,z7,z369,z8,z5])],[(0,[z0,z2,z7,z8,z4,z905]),(0,[z0,z2,z149,z7,z8,z213])],[(0,[z24,z2,z7,z110,z4,z5]),(0,[z906,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z594,z10]),(0,[z0,z2,z7,z8,z427,z4]),(0,[z0,z2,z537,z7,z8,z31])],[(0,[z0,z2,z7,z8,z4,z907]),(0,[z908,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z909,z4,z31]),(0,[z37,z0,z2,z512,z7,z8])]],
   [[(0,[z0,z2,z7,z8,z910,z5]),(0,[z0,z2,z7,z8,z911,z5]),(0,[z0,z329,z82,z8,z4,z5]),(0,[z85,z0,z2,z7,z8,z10]),(0,[z37,z0,z2,z760,z8,z4])],[(0,[z0,z2,z7,z8,z4,z912]),(0,[z0,z2,z7,z8,z4,z913]),(0,[z0,z2,z7,z914,z8,z4]),(0,[z0,z2,z104,z129,z30,z4])],[(0,[z0,z2,z86,z8,z10,z5]),(0,[z0,z25,z2,z18,z8,z10])],[(0,[z0,z2,z915,z8,z4,z5]),(0,[z0,z25,z2,z7,z8,z362])],[(0,[z42,z0,z2,z8,z815,z5]),(0,[z0,z2,z7,z229,z8,z4]),(0,[z0,z2,z7,z8,z4,z627])],[(0,[z39,z0,z2,z29,z4,z5]),(0,[z85,z0,z2,z19,z8,z10]),(0,[z0,z2,z690,z19,z8,z4]),(0,[z0,z2,z166,z8,z4,z31])],[(0,[z0,z2,z7,z8,z916,z4]),(0,[z0,z2,z7,z8,z4,z138]),(0,[z0,z2,z7,z20,z4,z192]),(0,[z0,z345,z7,z8,z4,z5]),(0,[z60,z0,z2,z579,z8,z4])],[(0,[z0,z2,z7,z8,z917,z5])],[(0,[z424,z25,z2,z359,z8,z4]),(0,[z97,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z4,z918]),(0,[z852,z0,z2,z19,z8,z4]),(1,[z0,z266,z2,z7,z8])],[(0,[z0,z2,z919,z8,z10,z5]),(0,[z46,z0,z2,z40,z8,z5])],[(0,[z0,z2,z7,z920,z8,z4]),(0,[z0,z2,z7,z8,z4,z921]),(1,[z46,z0,z2,z20,z4]),(0,[z0,z2,z19,z7,z8,z602])],[(0,[z0,z2,z7,z8,z922,z5]),(0,[z0,z704,z7,z8,z4,z5]),(0,[z0,z2,z7,z279,z8,z4]),(0,[z0,z2,z712,z19,z7,z8]),(0,[z0,z254,z2,z142,z8,z4])],[(0,[z37,z0,z2,z7,z8,z256]),(0,[z0,z2,z142,z8,z4,z187])],[(0,[z0,z2,z8,z30,z10,z31]),(0,[z0,z696,z2,z8,z10,z5])],[],[(0,[z217,z37,z218,z7,z8,z4]),(0,[z0,z2,z7,z154,z8,z4]),(0,[z0,z2,z715,z19,z8,z10]),(0,[z37,z0,z2,z7,z20,z4]),(0,[z72,z0,z25,z2,z7,z4]),(0,[z0,z25,z2,z7,z4,z31])]],
   [[(0,[z217,z3,z218,z8,z4,z5]),(0,[z42,z0,z2,z8,z4,z5]),(0,[z0,z2,z7,z8,z62,z462])],[(0,[z0,z2,z7,z8,z923,z4])],[(0,[z37,z0,z2,z7,z8,z4]),(0,[z0,z924,z2,z7,z8,z4]),(0,[z0,z2,z8,z30,z57,z5]),(0,[z2,z7,z8,z10,z365,z5]),(0,[z0,z107,z245,z2,z7,z5]),(0,[z0,z2,z332,z7,z8,z4])],[(0,[z0,z390,z25,z7,z167,z8])],[(0,[z0,z2,z925,z7,z8,z4]),(0,[z0,z2,z926,z7,z8,z5]),(0,[z927,z0,z2,z7,z8,z4])],[(0,[z928,z0,z2,z7,z8,z4]),(0,[z0,z2,z19,z7,z8,z474]),(0,[z0,z2,z7,z8,z538,z5])],[(0,[z0,z2,z7,z8,z4,z929])],[(0,[z0,z2,z7,z8,z4,z197]),(0,[z0,z2,z7,z8,z168,z5]),(0,[z0,z7,z8,z168,z4,z5]),(0,[z0,z7,z243,z475,z8,z4]),(0,[z0,z2,z7,z8,z4,z278]),(0,[z0,z2,z19,z8,z343,z10]),(1,[z0,z2,z7,z8,z338]),(0,[z204,z0,z2,z19,z8,z10]),(0,[z0,z2,z590,z8,z4,z31])],[(0,[z217,z227,z218,z7,z8,z4]),(0,[z0,z25,z2,z8,z30,z10]),(0,[z0,z2,z7,z8,z4,z930])],[(0,[z0,z2,z7,z8,z10,z291]),(0,[z263,z2,z7,z8,z400,z5]),(0,[z0,z2,z19,z8,z10,z187]),(0,[z0,z830,z2,z18,z7,z8]),(0,[z0,z2,z7,z165,z20,z4])],[(0,[z37,z0,z2,z7,z8,z102]),(0,[z424,z2,z18,z359,z8,z5]),(0,[z284,z2,z7,z8,z4,z192]),(0,[z0,z2,z7,z117,z4,z31])],[(0,[z0,z2,z7,z931,z4,z31]),(0,[z0,z2,z7,z8,z4,z932]),(0,[z0,z2,z18,z7,z8,z92]),(0,[z0,z2,z19,z7,z8,z860])],[(0,[z42,z0,z25,z2,z8,z4]),(0,[z42,z227,z0,z2,z8,z4]),(0,[z933,z0,z2,z7,z8,z4]),(0,[z934,z0,z2,z7,z8,z4]),(0,[z0,z2,z18,z8,z10,z5]),(0,[z120,z0,z2,z7,z8,z131])],[(0,[z0,z1,z25,z2,z7,z4]),(0,[z0,z2,z7,z8,z4,z935]),(0,[z0,z2,z7,z936,z8,z4]),(0,[z937,z0,z7,z243,z8,z4]),(0,[z0,z2,z938,z7,z8,z4]),(0,[z39,z0,z2,z19,z8,z10])],[(0,[z0,z25,z2,z3,z8,z4]),(0,[z0,z2,z7,z164,z20,z4])],[(0,[z0,z2,z7,z8,z939,z5]),(0,[z0,z414,z2,z7,z4,z5]),(0,[z940,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z941,z5]),(0,[z0,z2,z7,z8,z581,z5]),(0,[z0,z2,z238,z19,z8,z10])]],
   [[(0,[z382,z0,z2,z19,z8,z10]),(0,[z46,z0,z2,z18,z8,z5]),(0,[z0,z2,z19,z146,z8,z10]),(0,[z0,z25,z2,z116,z7,z4])],[(0,[z0,z2,z7,z942,z8,z5]),(0,[z346,z0,z2,z7,z8,z4]),(0,[z46,z0,z2,z40,z19,z8])],[(0,[z438,z2,z7,z8,z348,z31]),(0,[z0,z2,z7,z8,z943,z5]),(0,[z0,z2,z18,z7,z8,z310]),(0,[z0,z2,z19,z7,z8,z194])],[(0,[z0,z2,z7,z944,z4,z5]),(0,[z0,z2,z19,z945,z8,z4]),(0,[z46,z0,z2,z8,z71,z5]),(0,[z0,z108,z2,z75,z8,z5])],[(0,[z0,z2,z423,z8,z4,z5]),(0,[z0,z2,z84,z19,z8,z5]),(0,[z0,z2,z116,z7,z205,z5]),(1,[z0,z2,z332,z8,z4])],[(0,[z0,z377,z2,z7,z20,z4]),(0,[z0,z2,z7,z8,z448,z31]),(0,[z0,z2,z946,z7,z8,z4]),(0,[z0,z2,z496,z8,z10,z5]),(0,[z947,z0,z2,z19,z8,z4]),(0,[z0,z2,z104,z30,z10,z5])],[(0,[z0,z2,z18,z7,z330,z8]),(0,[z0,z948,z2,z7,z8,z4]),(0,[z297,z0,z2,z7,z8,z10]),(0,[z0,z2,z7,z8,z193,z5]),(0,[z0,z2,z19,z949,z8,z4]),(0,[z0,z25,z2,z7,z8,z311])],[(0,[z0,z2,z7,z8,z950,z5]),(0,[z0,z25,z2,z7,z951,z4]),(0,[z60,z0,z2,z7,z8,z170]),(0,[z0,z2,z18,z19,z8,z206])],[(0,[z0,z2,z7,z8,z4,z952]),(0,[z0,z23,z25,z2,z7,z4]),(0,[z0,z78,z7,z48,z4,z5]),(0,[z69,z0,z7,z385,z8,z4]),(0,[z0,z2,z19,z7,z221,z4]),(0,[z60,z0,z2,z7,z8,z205]),(0,[z0,z2,z116,z40,z7,z5])],[(0,[z0,z2,z7,z953,z8,z5]),(0,[z191,z0,z2,z19,z8,z10]),(0,[z406,z0,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z205,z31]),(0,[z37,z0,z2,z142,z8,z4])],[(0,[z0,z189,z25,z2,z7,z8]),(0,[z0,z696,z2,z7,z20,z4])],[(0,[z0,z232,z160,z8,z4,z5]),(0,[z0,z25,z2,z86,z8,z10])],[(0,[z0,z2,z7,z8,z10,z5]),(0,[z0,z2,z18,z7,z8,z63]),(0,[z0,z2,z18,z7,z8,z485])],[(0,[z0,z2,z7,z8,z4,z954]),(0,[z0,z2,z7,z8,z955,z4]),(0,[z0,z2,z7,z641,z8,z4])],[(0,[z0,z2,z7,z8,z4,z683]),(0,[z0,z956,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z134,z4])],[(0,[z0,z2,z7,z8,z878,z5]),(0,[z0,z2,z7,z8,z4,z957]),(0,[z0,z2,z7,z8,z10,z632]),(0,[z0,z2,z19,z8,z10,z206])]],
   [[(0,[z0,z2,z7,z8,z4,z231]),(0,[z0,z2,z29,z440,z4,z5]),(0,[z0,z25,z2,z7,z8,z131])],[(0,[z424,z2,z32,z8,z4,z5]),(0,[z27,z562,z2,z7,z61,z4]),(0,[z0,z2,z7,z185,z270,z5]),(0,[z0,z2,z7,z20,z4,z958])],[(0,[z0,z2,z959,z7,z8,z5]),(0,[z37,z0,z2,z7,z8,z88]),(0,[z37,z0,z2,z252,z8,z4])],[(0,[z0,z2,z7,z8,z4,z247]),(0,[z0,z2,z7,z8,z4,z582]),(0,[z0,z2,z19,z960,z8,z4]),(0,[z0,z2,z7,z20,z30,z4])],[(0,[z0,z2,z7,z8,z4,z961]),(0,[z0,z962,z2,z7,z8,z4]),(0,[z963,z0,z2,z8,z10,z5]),(0,[z0,z2,z74,z7,z8,z709])],[(0,[z87,z0,z2,z8,z4,z5]),(0,[z0,z2,z7,z8,z311,z5]),(0,[z0,z545,z2,z7,z165,z4])],[(0,[z0,z2,z7,z8,z4,z697]),(0,[z862,z0,z2,z18,z7,z8])],[(0,[z438,z2,z19,z7,z8,z348]),(0,[z0,z2,z7,z8,z964,z5]),(0,[z69,z0,z7,z243,z8,z4]),(0,[z0,z2,z7,z8,z4,z459])],[(0,[z0,z965,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z4,z966]),(0,[z0,z2,z7,z8,z967,z5]),(0,[z0,z122,z184,z7,z123,z4]),(0,[z0,z16,z25,z7,z8,z17]),(0,[z46,z0,z2,z18,z19,z8]),(0,[z0,z2,z968,z8,z4,z5])],[(0,[z0,z2,z19,z8,z348,z10]),(0,[z0,z25,z2,z7,z969,z4]),(0,[z0,z2,z7,z8,z4,z970]),(0,[z0,z2,z18,z7,z8,z208]),(0,[z0,z2,z18,z945,z8,z5]),(0,[z0,z2,z7,z30,z4,z31]),(0,[z0,z2,z19,z8,z10,z76]),(0,[z0,z2,z18,z7,z20,z4]),(0,[z0,z2,z7,z20,z62,z4])],[(0,[z0,z2,z7,z8,z971,z5]),(0,[z0,z2,z7,z8,z972,z5]),(0,[z973,z0,z2,z7,z8,z4]),(0,[z37,z0,z232,z160,z8,z4]),(0,[z0,z974,z2,z7,z8,z4]),(0,[z0,z2,z7,z8,z62,z205])],[(0,[z0,z373,z2,z3,z8,z5]),(0,[z0,z374,z2,z3,z8,z5]),(0,[z0,z2,z7,z975,z8,z4]),(0,[z0,z2,z7,z8,z976,z5]),(0,[z0,z2,z7,z977,z4,z31]),(0,[z0,z2,z237,z30,z4,z5]),(0,[z37,z0,z2,z7,z8,z71]),(0,[z0,z254,z2,z40,z7,z8])],[(0,[z257,z2,z7,z8,z4,z153]),(0,[z0,z2,z18,z949,z8,z5]),(0,[z0,z2,z7,z243,z20,z4]),(0,[z0,z2,z7,z8,z4,z261]),(1,[z0,z2,z40,z7,z20])],[(0,[z0,z2,z19,z788,z8,z10]),(0,[z37,z0,z2,z7,z8,z225]),(0,[z0,z2,z7,z8,z225,z31]),(0,[z0,z160,z329,z8,z4,z5]),(0,[z767,z2,z7,z8,z10,z5]),(0,[z0,z25,z545,z2,z7,z4])],[(0,[z0,z2,z218,z19,z8,z10]),(0,[z263,z0,z2,z7,z20,z4]),(0,[z37,z0,z2,z351,z8,z4]),(0,[z0,z2,z7,z8,z4,z978]),(0,[z0,z2,z12,z8,z10,z5])],[(0,[z0,z114,z2,z19,z8,z10]),(0,[z0,z2,z7,z8,z800,z4]),(0,[z0,z2,z116,z18,z7,z5])]],
   [[(0,[z0,z2,z7,z20,z4,z153]),(0,[z0,z2,z7,z20,z4,z5]),(0,[z0,z545,z2,z7,z8,z4])],[(0,[z424,z0,z2,z19,z8,z10]),(0,[z0,z2,z7,z979,z8,z4]),(0,[z0,z696,z25,z2,z8,z10]),(0,[z0,z2,z7,z980,z8,z4])],[(0,[z0,z2,z7,z981,z4,z31]),(0,[z0,z2,z19,z7,z8,z362]),(0,[z0,z2,z7,z8,z4,z478]),(0,[z0,z2,z75,z8,z4,z5])],[(0,[z0,z2,z7,z8,z4,z982]),(0,[z235,z2,z7,z8,z357,z5]),(0,[z0,z2,z265,z8,z10,z5]),(0,[z0,z2,z19,z20,z4,z206])],[(0,[z983,z0,z2,z7,z8,z4]),(0,[z0,z7,z475,z8,z4,z115]),(0,[z0,z2,z984,z7,z8,z4]),(0,[z0,z2,z116,z19,z8,z10])],[(0,[z0,z2,z19,z8,z10,z192])],[(0,[z0,z2,z7,z8,z4,z985]),(0,[z0,z2,z7,z986,z4,z5]),(0,[z0,z2,z19,z8,z10,z222])],[(0,[z424,z2,z19,z359,z8,z4]),(0,[z0,z2,z7,z987,z8,z5]),(0,[z0,z25,z2,z7,z892,z8])],[(0,[z439,z0,z2,z7,z8,z4]),(0,[z263,z2,z526,z7,z8,z5]),(1,[z60,z0,z2,z8,z10]),(0,[z37,z0,z2,z7,z185,z76]),(0,[z0,z2,z86,z8,z131,z5]),(0,[z37,z0,z2,z166,z8,z4])],[(0,[z0,z988,z2,z7,z8,z5]),(0,[z0,z2,z74,z8,z30,z4]),(0,[z0,z254,z2,z19,z8,z10]),(0,[z0,z2,z7,z7,z20,z4]),(0,[z120,z0,z2,z7,z20,z4])],[(0,[z0,z2,z7,z8,z4,z989]),(0,[z0,z990,z2,z7,z8,z5]),(0,[z0,z2,z7,z20,z4,z222]),(0,[z0,z2,z7,z8,z92,z10]),(0,[z0,z2,z7,z8,z10,z784])],[(0,[z0,z2,z7,z991,z8,z5]),(0,[z39,z0,z2,z29,z458,z4])],[(0,[z0,z2,z7,z992,z8,z4]),(0,[z0,z2,z7,z993,z20,z4])],[(0,[z0,z2,z7,z8,z4,z994]),(0,[z0,z65,z2,z3,z8,z5]),(0,[z0,z2,z7,z8,z4,z995]),(0,[z0,z25,z2,z512,z7,z8])],[(0,[z833,z0,z2,z7,z8,z4]),(0,[z0,z390,z2,z19,z8,z10]),(0,[z0,z2,z7,z8,z996,z5]),(0,[z0,z2,z8,z71,z10,z5]),(0,[z0,z997,z656,z7,z8,z5]),(0,[z0,z2,z40,z7,z8,z205])],[(0,[z0,z2,z7,z8,z4,z998]),(0,[z0,z790,z2,z7,z10,z5]),(0,[z0,z2,z999,z8,z10,z5]),(0,[z0,z107,z25,z108,z2,z7])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z2,z7,z110,z4,z138]),(0,[z2,z7,z8,z10,z315]),(0,[z0,z7,z48,z4,z220]),(0,[z437,z2,z7,z237,z5]),(0,[z0,z2,z94,z463,z7])],[(0,[z0,z2,z7,z1000,z4]),(0,[z0,z2,z20,z10,z192])],[(0,[z0,z2,z20,z10,z222]),(0,[z0,z555,z7,z282,z5]),(0,[z0,z2,z1001,z8,z4]),(0,[z0,z2,z75,z20,z4]),(0,[z0,z2,z7,z1002,z8])],[(0,[z0,z65,z2,z7,z20]),(0,[z0,z2,z7,z1003,z4]),(0,[z438,z0,z2,z20,z10]),(0,[z0,z184,z7,z48,z4]),(0,[z0,z2,z7,z8,z1004])]],
   [[(0,[z2,z19,z7,z8,z400]),(0,[z0,z2,z611,z8,z38]),(0,[z0,z269,z19,z369,z8]),(0,[z0,z1005,z7,z20,z4])],[(0,[z0,z2,z299,z20,z4]),(0,[z0,z2,z7,z20,z193]),(0,[z0,z2,z149,z30,z4]),(0,[z60,z0,z2,z116,z10]),(0,[z257,z157,z7,z8,z4])],[(0,[z0,z377,z2,z20,z10]),(0,[z0,z329,z8,z225,z5]),(0,[z0,z83,z19,z8,z10]),(0,[z0,z2,z7,z20,z604]),(0,[z0,z2,z7,z1006,z4]),(0,[z87,z0,z2,z463,z5])],[(0,[z0,z2,z607,z8,z10]),(0,[z0,z2,z55,z20,z4]),(0,[z0,z16,z7,z20,z17]),(0,[z39,z0,z2,z1007,z4]),(0,[z0,z555,z2,z20,z10])]],
   [[(0,[z0,z353,z2,z19,z8]),(0,[z0,z2,z149,z92,z4]),(0,[z0,z2,z1008,z8,z10])],[(0,[z42,z0,z2,z20,z4]),(0,[z0,z2,z3,z1009,z4]),(0,[z0,z879,z2,z19,z8]),(0,[z0,z2,z19,z953,z8]),(0,[z934,z0,z2,z8,z10]),(0,[z0,z2,z19,z8,z178]),(0,[z2,z18,z7,z8,z315]),(0,[z0,z414,z2,z19,z10]),(0,[z309,z0,z2,z20,z10]),(0,[z0,z2,z331,z12,z8])],[(0,[z0,z2,z7,z1010,z4]),(0,[z0,z2,z19,z8,z1011]),(0,[z0,z230,z354,z8,z10]),(0,[z0,z2,z116,z84,z19]),(0,[z0,z570,z245,z2,z19]),(0,[z46,z0,z2,z84,z8])],[(0,[z833,z0,z2,z8,z476]),(0,[z97,z2,z32,z8,z4]),(0,[z37,z2,z7,z110,z4]),(0,[z0,z704,z7,z20,z4]),(0,[z147,z2,z7,z664,z4])]],
   [[(0,[z2,z32,z8,z10,z5]),(0,[z0,z2,z44,z7,z20]),(0,[z0,z2,z396,z8,z10]),(0,[z0,z2,z30,z10,z392]),(0,[z0,z696,z2,z10,z31]),(0,[z0,z254,z2,z20,z10]),(0,[z0,z2,z7,z651,z76])],[(0,[z2,z7,z110,z4,z200]),(0,[z679,z0,z2,z20,z4]),(0,[z39,z0,z2,z1012,z4]),(0,[z0,z2,z641,z8,z10]),(0,[z46,z0,z2,z18,z20])],[(0,[z408,z7,z8,z4,z247]),(0,[z0,z2,z7,z1009,z4]),(0,[z0,z7,z48,z10,z5]),(0,[z0,z2,z331,z19,z8]),(0,[z0,z2,z237,z20,z10])],[(0,[z111,z2,z7,z110,z5]),(0,[z39,z0,z2,z92,z10])]],
   [[(0,[z217,z218,z19,z8,z10]),(0,[z0,z7,z8,z168,z31])],[(0,[z0,z2,z3,z20,z4]),(0,[z2,z7,z110,z4,z197]),(0,[z37,z0,z329,z8,z4]),(0,[z0,z2,z20,z10,z115]),(0,[z0,z2,z327,z129,z4]),(0,[z0,z2,z327,z4,z31]),(0,[z0,z2,z1013,z7,z8]),(0,[z2,z7,z8,z4,z1014])],[(0,[z0,z2,z30,z344,z5]),(0,[z0,z345,z19,z8,z10]),(0,[z0,z2,z156,z8,z10]),(0,[z0,z2,z7,z20,z860]),(0,[z0,z2,z7,z20,z240])],[(0,[z0,z2,z20,z30,z10]),(0,[z37,z0,z2,z331,z8])]],
   [[(0,[z0,z154,z329,z8,z4]),(0,[z0,z2,z20,z10,z725]),(0,[z0,z2,z449,z20,z10]),(0,[z0,z770,z7,z4,z958])],[(0,[z0,z374,z2,z19,z8]),(0,[z39,z0,z2,z20,z10]),(0,[z246,z2,z164,z8,z10]),(0,[z0,z2,z1001,z8,z10])],[(0,[z0,z2,z7,z20,z4]),(0,[z0,z2,z149,z8,z38]),(0,[z0,z2,z8,z1015,z10]),(0,[z0,z2,z463,z19,z7]),(0,[z37,z0,z2,z463,z7])],[(0,[z2,z7,z419,z110,z5]),(0,[z0,z2,z7,z8,z1016]),(0,[z0,z2,z146,z20,z10]),(0,[z0,z2,z19,z8,z1017]),(0,[z0,z2,z7,z20,z878]),(0,[z0,z1018,z2,z7,z20])]],
   [[(0,[z25,z2,z7,z110,z4]),(0,[z24,z0,z2,z20,z10]),(0,[z0,z2,z149,z30,z10]),(0,[z0,z2,z20,z10,z10]),(0,[z1019,z2,z7,z20,z4]),(0,[z0,z2,z7,z993,z832])],[(0,[z0,z2,z149,z8,z102]),(0,[z60,z0,z2,z327,z4]),(0,[z0,z2,z20,z62,z10])],[(0,[z0,z25,z329,z8,z4]),(0,[z37,z0,z7,z8,z168]),(0,[z0,z2,z7,z8,z1020]),(0,[z0,z345,z7,z237,z5]),(0,[z0,z2,z40,z142,z20])],[(0,[z0,z2,z19,z8,z886]),(0,[z0,z2,z30,z10,z201]),(0,[z0,z2,z7,z20,z170]),(0,[z0,z2,z1021,z7,z4])]],
   [[(0,[z0,z2,z243,z20,z10]),(0,[z0,z2,z149,z30,z213]),(0,[z0,z25,z2,z331,z8]),(0,[z0,z107,z2,z20,z10]),(0,[z2,z1022,z7,z8,z5]),(0,[z0,z2,z7,z20,z205]),(0,[z1023,z2,z7,z8,z4])],[(0,[z0,z2,z949,z20,z4]),(0,[z0,z2,z40,z332,z8]),(0,[z0,z2,z75,z93,z76])],[(0,[z0,z2,z7,z20,z102]),(0,[z81,z0,z82,z20,z4]),(0,[z0,z122,z2,z20,z10]),(0,[z69,z0,z2,z20,z10]),(0,[z0,z2,z30,z213,z31]),(0,[z502,z0,z2,z20,z10]),(0,[z0,z2,z86,z20,z10]),(0,[z0,z2,z64,z19,z10]),(0,[z2,z7,z20,z4,z1024])],[(0,[z424,z0,z2,z20,z10]),(0,[z0,z7,z8,z168,z5]),(0,[z0,z2,z167,z20,z10]),(0,[z0,z2,z30,z528,z4]),(0,[z0,z1025,z2,z8,z10]),(0,[z0,z2,z19,z404,z10]),(0,[z0,z555,z19,z8,z725]),(0,[z0,z2,z1026,z8,z10]),(0,[z0,z2,z75,z270,z5]),(0,[z0,z25,z2,z463,z7])]],
   [[(0,[z0,z390,z2,z20,z10]),(0,[z0,z2,z327,z4,z5]),(0,[z0,z2,z7,z20,z119]),(0,[z0,z2,z463,z7,z31])],[(0,[z0,z2,z7,z20,z448]),(0,[z0,z2,z1027,z8,z10]),(0,[z37,z0,z2,z20,z10]),(0,[z0,z2,z40,z20,z10]),(0,[z0,z2,z980,z8,z10])],[(0,[z0,z2,z140,z8,z10]),(0,[z0,z19,z7,z48,z4]),(0,[z0,z2,z640,z20,z10])],[(0,[z424,z2,z359,z20,z4]),(0,[z514,z2,z7,z20,z4]),(0,[z0,z2,z7,z20,z131]),(0,[z87,z0,z2,z20,z4]),(0,[z0,z2,z1028,z7,z8])]],
   [[(0,[z189,z408,z7,z8,z5]),(0,[z0,z2,z331,z8,z31]),(0,[z0,z2,z19,z342,z10]),(0,[z0,z294,z7,z640,z4]),(0,[z0,z108,z2,z7,z980])],[(0,[z0,z7,z193,z48,z5]),(0,[z0,z78,z19,z10,z222]),(0,[z0,z2,z840,z8,z10]),(0,[z0,z1029,z2,z20,z10]),(0,[z488,z2,z7,z20,z4])],[(0,[z1,z408,z7,z4,z5]),(0,[z2,z7,z110,z10,z5]),(0,[z2,z7,z110,z4,z31]),(0,[z0,z335,z329,z8,z5]),(0,[z0,z704,z19,z8,z10]),(0,[z455,z0,z2,z20,z205])],[(0,[z0,z2,z389,z8,z10])]],
   [[(0,[z0,z2,z646,z8,z10]),(0,[z0,z329,z8,z474,z5]),(0,[z0,z2,z29,z20,z10]),(0,[z0,z1029,z2,z8,z10]),(0,[z0,z2,z19,z20,z131]),(0,[z502,z2,z7,z863,z4])],[(0,[z0,z2,z7,z20,z10]),(0,[z0,z2,z715,z20,z10]),(0,[z0,z2,z332,z8,z88])],[(0,[z218,z95,z7,z8,z4]),(0,[z0,z2,z399,z20,z4]),(0,[z0,z16,z2,z20,z10]),(0,[z60,z0,z2,z8,z709]),(0,[z60,z0,z2,z20,z10]),(0,[z85,z0,z2,z331,z8]),(0,[z246,z0,z2,z20,z10]),(0,[z0,z25,z2,z20,z10])],[(0,[z0,z2,z160,z20,z10]),(0,[z0,z2,z7,z8,z1030]),(0,[z0,z2,z20,z320,z10]),(0,[z862,z0,z2,z8,z10]),(0,[z0,z2,z19,z8,z131])]],
   [[(0,[z0,z78,z2,z20,z10]),(0,[z0,z2,z20,z10,z31]),(0,[z0,z2,z20,z10,z958]),(0,[z0,z2,z993,z20,z10])],[(0,[z372,z0,z2,z20,z10]),(0,[z0,z2,z142,z20,z4]),(0,[z0,z2,z7,z1031,z20]),(0,[z0,z2,z7,z20,z213])],[(0,[z0,z18,z7,z475,z8]),(0,[z0,z2,z1032,z327,z4]),(0,[z0,z2,z19,z20,z10]),(0,[z0,z2,z19,z849,z10])],[(0,[z0,z2,z19,z282,z10]),(0,[z0,z2,z116,z84,z10]),(0,[z0,z2,z651,z8,z10]),(0,[z0,z637,z276,z2,z7]),(0,[z0,z2,z75,z31,z76]),(0,[z0,z2,z463,z7,z5])]],
   [[(0,[z0,z329,z8,z4,z298]),(0,[z0,z2,z20,z4,z49]),(0,[z0,z266,z2,z7,z8])],[(0,[z0,z2,z19,z8,z10]),(0,[z382,z0,z2,z20,z10]),(0,[z406,z0,z2,z327,z4])],[(0,[z0,z111,z2,z7,z20]),(0,[z0,z2,z61,z20,z10]),(0,[z46,z0,z2,z20,z4]),(0,[z147,z0,z2,z20,z10]),(0,[z293,z7,z164,z8,z4])],[(0,[z0,z1033,z2,z7,z4]),(0,[z81,z0,z2,z20,z10]),(0,[z0,z2,z662,z8,z10]),(0,[z0,z230,z2,z20,z10])]],
   [[(0,[z263,z2,z7,z20,z236]),(0,[z0,z2,z36,z8,z10]),(0,[z0,z2,z149,z8,z362]),(0,[z0,z2,z30,z10,z31]),(0,[z0,z2,z1007,z149,z4]),(0,[z0,z2,z19,z237,z171]),(0,[z0,z2,z19,z483,z10]),(0,[z0,z2,z18,z332,z8])],[(0,[z0,z2,z19,z8,z857]),(1,[z0,z2,z20,z10]),(0,[z0,z2,z84,z7,z8]),(0,[z0,z2,z657,z20,z4]),(0,[z0,z2,z463,z7,z427])],[(0,[z0,z2,z253,z8,z10]),(0,[z0,z1034,z2,z8,z10]),(0,[z0,z2,z452,z10,z31]),(0,[z0,z2,z429,z8,z10]),(0,[z0,z2,z142,z8,z205]),(0,[z0,z2,z7,z20,z88])],[(0,[z0,z2,z20,z10,z171]),(0,[z0,z2,z185,z20,z10])]],
   [[(0,[z0,z1,z2,z19,z10]),(0,[z27,z0,z2,z20,z10]),(0,[z37,z2,z7,z8,z400]),(0,[z0,z329,z8,z4,z5]),(0,[z0,z2,z18,z20,z10]),(0,[z0,z2,z20,z664,z10]),(0,[z0,z2,z84,z19,z20]),(0,[z85,z0,z2,z20,z10]),(0,[z46,z0,z2,z20,z205]),(0,[z0,z1035,z2,z7,z20])],[(0,[z0,z2,z327,z4,z278]),(0,[z0,z2,z1036,z19,z8]),(0,[z0,z2,z863,z20,z10]),(0,[z0,z2,z84,z7,z20]),(0,[z0,z212,z2,z84,z8]),(0,[z0,z1037,z2,z7,z8]),(0,[z204,z0,z2,z20,z10]),(0,[z575,z481,z7,z8,z4])],[(0,[z0,z2,z435,z8,z10]),(0,[z0,z2,z116,z84,z7]),(0,[z0,z2,z7,z20,z1038]),(0,[z0,z2,z7,z20,z567])],[(0,[z24,z2,z7,z953,z5]),(0,[z0,z2,z20,z10,z153]),(0,[z0,z2,z20,z10,z5]),(0,[z0,z2,z129,z20,z10]),(0,[z0,z2,z20,z10,z832]),(0,[z0,z2,z1039,z8,z4])]],
   [[(0,[z0,z2,z327,z71,z5]),(0,[z767,z555,z7,z8,z5]),(0,[z0,z790,z2,z19,z10]),(0,[z0,z2,z7,z20,z338]),(0,[z0,z2,z116,z7,z338])],[(0,[z0,z2,z19,z8,z476]),(0,[z0,z2,z699,z8,z10]),(0,[z0,z7,z1040,z8,z4]),(0,[z0,z2,z142,z8,z131])],[(0,[z0,z329,z229,z8,z4]),(0,[z0,z232,z160,z20,z4]),(0,[z514,z2,z19,z8,z10]),(0,[z0,z2,z7,z20,z602])],[(0,[z0,z2,z7,z20,z71]),(0,[z0,z2,z29,z149,z10]),(0,[z0,z2,z7,z8,z338]),(0,[z0,z696,z2,z20,z10]),(0,[z0,z2,z590,z20,z4])]],
   [[(0,[z0,z2,z7,z1041,z4]),(0,[z0,z2,z8,z1042,z10]),(0,[z39,z0,z2,z8,z1016]),(0,[z488,z2,z19,z8,z10]),(0,[z0,z2,z1043,z8,z10])],[(0,[z0,z23,z2,z19,z10]),(0,[z0,z2,z19,z987,z8]),(0,[z0,z2,z7,z20,z225]),(0,[z297,z0,z329,z8,z4]),(0,[z235,z2,z7,z404,z5]),(0,[z0,z2,z1044,z8,z4])],[],[(0,[z0,z2,z7,z8,z1045]),(0,[z0,z269,z2,z20,z10]),(0,[z0,z2,z1046,z8,z10]),(0,[z0,z2,z774,z8,z10]),(0,[z2,z7,z1047,z8,z4])]],
   [[(0,[z191,z0,z2,z20,z10]),(0,[z0,z2,z327,z57,z5]),(0,[z0,z2,z712,z7,z20])],[(0,[z25,z2,z7,z8,z400]),(0,[z0,z7,z475,z8,z10]),(0,[z46,z0,z2,z20,z10]),(0,[z0,z1048,z7,z8,z4])],[(0,[z0,z854,z2,z8,z10]),(0,[z0,z2,z539,z10,z31]),(0,[z0,z2,z7,z8,z1049])],[(0,[z0,z2,z512,z7,z20])]],
   [[(0,[z0,z2,z687,z8,z10]),(0,[z0,z2,z333,z8,z10]),(0,[z0,z108,z2,z20,z10]),(0,[z1050,z0,z2,z20,z4]),(0,[z0,z1051,z2,z7,z8])],[(0,[z0,z2,z831,z8,z10]),(0,[z163,z0,z2,z20,z10]),(0,[z0,z2,z7,z20,z474]),(0,[z0,z2,z332,z20,z4])],[(0,[z0,z2,z925,z8,z10]),(0,[z0,z2,z112,z8,z10]),(0,[z2,z19,z8,z10,z271]),(0,[z0,z2,z690,z20,z4])],[(0,[z0,z2,z19,z721,z8]),(0,[z0,z2,z129,z10,z31]),(0,[z0,z2,z1046,z149,z8])]],
   [[(0,[z0,z2,z7,z419,z20]),(0,[z72,z0,z2,z129,z10]),(0,[z0,z545,z2,z7,z10]),(0,[z0,z2,z332,z8,z4]),(0,[z0,z2,z166,z20,z4])],[(0,[z0,z2,z149,z931,z4]),(0,[z263,z0,z2,z20,z10]),(0,[z0,z7,z48,z4,z310]),(0,[z37,z0,z2,z327,z4]),(0,[z0,z2,z12,z8,z10]),(0,[z0,z245,z2,z20,z10])],[(0,[z24,z2,z19,z26,z10]),(0,[z0,z2,z30,z57,z201]),(0,[z0,z2,z327,z10,z5]),(0,[z309,z0,z2,z84,z8]),(0,[z488,z7,z449,z8,z4])],[(0,[z217,z879,z7,z8,z5]),(0,[z0,z2,z327,z512,z5]),(0,[z0,z2,z8,z129,z10]),(0,[z393,z2,z394,z8,z10])]],
   [[(0,[z0,z2,z8,z133,z10]),(0,[z0,z2,z149,z8,z240]),(0,[z0,z2,z1052,z20,z10]),(0,[z0,z637,z2,z20,z10])],[(0,[z0,z7,z48,z4,z31]),(0,[z0,z2,z1007,z30,z4]),(0,[z120,z0,z2,z327,z4]),(0,[z235,z2,z19,z8,z357]),(0,[z0,z7,z8,z1053,z5]),(0,[z37,z0,z2,z20,z205])],[(0,[z2,z7,z8,z4,z315]),(0,[z0,z2,z8,z1054,z5]),(0,[z0,z2,z84,z8,z343]),(0,[z0,z2,z537,z7,z20]),(0,[z0,z2,z332,z8,z205])],[(0,[z562,z2,z7,z110,z4]),(0,[z0,z2,z19,z8,z941]),(0,[z0,z78,z7,z456,z5]),(0,[z0,z2,z123,z20,z10]),(0,[z0,z2,z1052,z8,z10]),(0,[z0,z19,z143,z8,z10]),(0,[z0,z2,z20,z343,z10]),(0,[z0,z2,z116,z332,z4])]],
   [[(0,[z0,z2,z7,z1055,z4]),(0,[z0,z2,z74,z20,z4]),(0,[z0,z276,z2,z20,z10])],[(0,[z0,z730,z2,z19,z8]),(0,[z0,z2,z19,z8,z456]),(0,[z0,z114,z2,z20,z10]),(0,[z0,z2,z20,z10,z187]),(0,[z0,z2,z611,z8,z10]),(0,[z0,z293,z7,z20,z4])],[(0,[z2,z32,z8,z102,z5]),(0,[z0,z19,z329,z8,z4]),(0,[z0,z2,z82,z20,z10]),(0,[z0,z25,z2,z327,z4]),(0,[z2,z19,z8,z10,z365]),(0,[z0,z2,z1056,z7,z5]),(0,[z0,z2,z7,z20,z194]),(0,[z0,z2,z633,z20,z4])],[(0,[z2,z19,z7,z110,z4]),(0,[z0,z2,z945,z20,z4]),(0,[z39,z0,z2,z8,z1015]),(0,[z235,z0,z2,z20,z10]),(0,[z0,z2,z1057,z8,z10]),(0,[z72,z0,z2,z20,z10]),(0,[z46,z0,z2,z40,z20]),(0,[z0,z7,z1058,z20,z4])]],
   [[(0,[z0,z2,z7,z20,z38])],[(0,[z0,z2,z498,z8,z10]),(0,[z120,z0,z2,z30,z10]),(0,[z0,z2,z249,z7,z20]),(0,[z0,z2,z332,z8,z131])],[(0,[z0,z2,z8,z20,z10])],[(0,[z0,z2,z166,z12,z8])]],
   [[(0,[z0,z2,z202,z8,z10]),(0,[z27,z2,z19,z61,z10]),(0,[z0,z2,z18,z149,z30]),(0,[z0,z2,z7,z20,z311]),(0,[z0,z545,z2,z18,z7]),(0,[z0,z1059,z7,z8,z4])],[(0,[z37,z0,z7,z48,z4]),(0,[z0,z2,z504,z20,z4]),(0,[z59,z0,z2,z20,z4])],[(0,[z0,z2,z116,z20,z10]),(0,[z0,z2,z149,z473,z4])],[(0,[z0,z1060,z2,z7,z4]),(0,[z0,z19,z7,z8,z168]),(0,[z0,z2,z104,z20,z10]),(0,[z0,z2,z1061,z8,z5]),(0,[z0,z2,z868,z19,z10]),(0,[z0,z2,z20,z20,z10]),(0,[z0,z2,z332,z8,z10]),(0,[z1062,z2,z7,z8,z4])]],
   [[(0,[z217,z0,z2,z20,z10]),(0,[z0,z2,z218,z20,z10]),(0,[z0,z7,z48,z4,z5]),(0,[z0,z25,z7,z8,z168])],[(0,[z0,z2,z20,z10,z17]),(0,[z0,z2,z30,z10,z784]),(0,[z0,z770,z2,z20,z10]),(0,[z0,z2,z20,z205,z10]),(0,[z0,z2,z149,z8,z131])],[(0,[z0,z2,z1063,z8,z4]),(0,[z0,z189,z2,z7,z20]),(0,[z2,z7,z8,z400,z31]),(0,[z0,z2,z20,z587,z4]),(0,[z0,z2,z8,z800,z10]),(0,[z120,z0,z2,z20,z10]),(0,[z0,z2,z20,z10,z421])],[(0,[z0,z2,z7,z20,z105]),(0,[z0,z2,z327,z90,z4]),(0,[z393,z0,z2,z20,z10]),(0,[z0,z2,z1064,z19,z8])]],
   [[(0,[z0,z7,z48,z4,z208]),(0,[z0,z2,z19,z8,z411]),(0,[z0,z2,z149,z20,z10]),(0,[z0,z2,z40,z7,z20])],[(0,[z217,z42,z1,z4,z5]),(0,[z0,z2,z609,z8,z10]),(0,[z235,z83,z7,z8,z5]),(0,[z0,z2,z116,z19,z131]),(0,[z0,z2,z7,z483,z205])],[(0,[z0,z329,z8,z4,z31]),(0,[z0,z329,z8,z10,z5]),(0,[z0,z25,z7,z48,z4]),(0,[z0,z2,z19,z8,z976]),(0,[z0,z2,z327,z458,z4]),(0,[z0,z2,z7,z1065,z5]),(0,[z0,z266,z2,z142,z8])],[(0,[z0,z2,z673,z8,z10]),(0,[z0,z122,z19,z123,z10]),(0,[z0,z2,z30,z57,z31]),(0,[z0,z2,z7,z20,z57]),(0,[z0,z2,z149,z8,z10]),(0,[z295,z0,z2,z8,z10]),(0,[z0,z2,z463,z7,z93])]],
   [[(0,[z0,z2,z1007,z7,z4]),(0,[z0,z570,z2,z20,z10]),(0,[z0,z2,z19,z409,z10]),(0,[z0,z2,z463,z7,z459])],[(0,[z0,z2,z117,z30,z4]),(0,[z0,z2,z331,z8,z343]),(0,[z0,z2,z1066,z8,z10]),(0,[z767,z2,z19,z8,z10]),(0,[z0,z2,z354,z20,z10]),(0,[z0,z294,z2,z20,z10]),(0,[z0,z2,z7,z1067,z8]),(0,[z0,z2,z40,z7,z409])],[(0,[z0,z2,z920,z8,z10]),(0,[z0,z2,z20,z4,z10]),(0,[z0,z1068,z7,z8,z5])],[(0,[z0,z2,z1069,z8,z5]),(0,[z42,z0,z2,z1070,z4]),(0,[z0,z2,z224,z8,z10]),(0,[z0,z2,z327,z18,z5]),(0,[z0,z2,z7,z8,z1015]),(0,[z0,z2,z7,z1071,z4]),(0,[z0,z2,z116,z19,z10]),(0,[z0,z2,z20,z10,z206]),(0,[z0,z2,z238,z20,z10]),(0,[z0,z2,z19,z8,z709])]],
   [[(0,[z0,z2,z20,z10,z236]),(0,[z0,z18,z329,z8,z5]),(0,[z0,z2,z534,z8,z10]),(0,[z0,z2,z327,z19,z4]),(0,[z60,z0,z2,z8,z1015]),(0,[z0,z19,z179,z8,z10]),(0,[z0,z2,z19,z53,z10]),(0,[z0,z2,z84,z8,z205])],[(0,[z2,z18,z7,z110,z5]),(0,[z438,z2,z7,z20,z348]),(0,[z0,z326,z7,z48,z5]),(0,[z0,z2,z327,z38,z5]),(0,[z0,z2,z8,z47,z10]),(0,[z0,z2,z331,z8,z63])],[(0,[z0,z2,z483,z10,z5])],[(0,[z0,z7,z475,z8,z4])]],
   [[(0,[z227,z408,z7,z8,z4]),(0,[z37,z2,z32,z8,z4]),(0,[z0,z2,z359,z20,z10]),(0,[z0,z390,z7,z167,z20]),(0,[z60,z0,z2,z8,z10]),(0,[z0,z293,z19,z8,z10]),(0,[z0,z2,z19,z8,z1015]),(0,[z0,z2,z50,z7,z20])],[(0,[z0,z2,z788,z20,z10]),(0,[z2,z7,z8,z400,z5]),(0,[z346,z0,z2,z30,z10]),(0,[z0,z2,z8,z10,z1072]),(0,[z0,z2,z84,z86,z8]),(0,[z0,z2,z19,z8,z598])],[(0,[z1073,z0,z2,z327,z4]),(0,[z2,z7,z8,z1074,z5]),(0,[z0,z2,z369,z20,z10]),(0,[z0,z2,z19,z477,z10])],[(0,[z0,z2,z19,z585,z10]),(0,[z0,z25,z2,z10,z487])]],
   [[(0,[z852,z0,z2,z20,z4]),(0,[z0,z212,z2,z20,z10]),(0,[z0,z2,z7,z20,z175]),(0,[z0,z266,z2,z166,z8])],[(0,[z217,z218,z7,z20,z4]),(0,[z0,z2,z7,z1075,z4]),(0,[z0,z2,z20,z348,z10]),(0,[z0,z18,z7,z48,z5]),(0,[z0,z2,z30,z528,z10]),(0,[z0,z2,z20,z10,z76])],[(0,[z0,z374,z2,z435,z8]),(0,[z0,z2,z7,z20,z362]),(0,[z0,z329,z8,z362,z5]),(0,[z0,z2,z537,z149,z30]),(0,[z0,z2,z331,z8,z5]),(0,[z0,z2,z84,z20,z10]),(0,[z0,z545,z2,z7,z4]),(0,[z0,z7,z1076,z8,z4])],[(0,[z217,z1,z14,z7,z4]),(0,[z0,z2,z335,z7,z20]),(0,[z0,z2,z20,z10,z357]),(0,[z0,z2,z84,z19,z8]),(0,[z195,z0,z2,z20,z10]),(0,[z0,z2,z19,z221,z10]),(0,[z0,z2,z1061,z19,z8]),(0,[z0,z2,z20,z205,z206])]],
   [[(0,[z0,z2,z7,z1070,z4]),(0,[z2,z7,z110,z4,z5]),(0,[z0,z2,z436,z20,z4]),(0,[z0,z2,z161,z20,z4]),(0,[z0,z2,z327,z4,z201]),(0,[z0,z2,z19,z313,z10]),(0,[z437,z2,z19,z8,z10])],[(0,[z319,z0,z2,z20,z10]),(0,[z0,z2,z84,z8,z10]),(0,[z155,z0,z2,z20,z10]),(0,[z0,z2,z1077,z19,z8]),(0,[z0,z2,z165,z20,z10])],[(0,[z0,z2,z19,z8,z972]),(0,[z0,z2,z306,z19,z10]),(0,[z0,z2,z579,z20,z4])],[(0,[z217,z312,z7,z8,z4]),(0,[z0,z326,z2,z7,z20]),(0,[z541,z0,z2,z8,z10]),(0,[z0,z2,z18,z7,z20]),(0,[z155,z0,z449,z8,z10])]],
   [[(0,[z0,z2,z274,z8,z10]),(0,[z0,z2,z216,z8,z10]),(0,[z0,z2,z1078,z7,z8]),(0,[z0,z2,z463,z75,z5])],[(0,[z217,z42,z189,z8,z5]),(0,[z0,z2,z644,z8,z10]),(0,[z0,z2,z441,z20,z4]),(0,[z0,z2,z20,z26,z10])],[(0,[z0,z2,z95,z8,z10]),(0,[z0,z232,z2,z20,z10]),(0,[z0,z2,z164,z20,z10]),(0,[z0,z2,z166,z8,z343]),(0,[z0,z2,z358,z8,z10])],[(0,[z833,z0,z2,z8,z10]),(0,[z0,z2,z149,z316,z4]),(0,[z0,z2,z7,z8,z1079]),(0,[z0,z2,z1046,z7,z8]),(0,[z0,z2,z394,z20,z10]),(0,[z0,z2,z434,z20,z4])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 4 128 bkB c

def parents : List (ℕ × List W) := expandN 1 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 1 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 10) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa1 : chunkB SA 2 ((parents.drop 10).take 11) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa2 : chunkB SA 2 ((parents.drop 21).take 10) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa3 : chunkB SA 2 ((parents.drop 31).take 10) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa4 : chunkB SA 2 ((parents.drop 41).take 6) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa5 : chunkB SA 2 ((parents.drop 47).take 8) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa6 : chunkB SA 2 ((parents.drop 55).take 9) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa7 : chunkB SA 2 ((parents.drop 64).take 2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 66)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [10, 11, 10, 10, 6, 8, 9, 2] = true :=
  windowsG_cons pa0 (windowsG_cons pa1 (windowsG_cons pa2 (windowsG_cons pa3 (windowsG_cons pa4 (windowsG_cons pa5 (windowsG_cons pa6 (windowsG_cons pa7 (windowsG_nil paend))))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 632) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 632).take 638) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1270).take 630) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1900).take 200) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 2100)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [632, 638, 630, 200] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 4 ((bkB.flatten.drop 0).take 67).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 4 ((bkB.flatten.drop 67).take 61).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 4 bkB.flatten 0 [67, 61] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 1) (J := 4) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 4) (nb2 := 128) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_45626

theorem PEqualNP.Outside.L_meta_45626 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241376 * 2 ^ 32 + 4001949824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241376 * 2 ^ 32 + 4001949824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45626.solve