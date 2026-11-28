import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45668

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
  Nat.testBit (4008241824 * 2 ^ 32 + 3940592128) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00042e056c170d54#64 ++ 0x00010b815b05c355#64 ++ 0xfd0c7e1ffc7f1ffd#64 ++ 0xff431f87ff1fc7ff#64 : BitVec 256),
   (0x0c7196ece1b36331#64 ++ 0x031c65bb386cd8cc#64 ++ 0x7ef39fece3b3e332#64 ++ 0xdfbce7fb38ecf8cc#64 : BitVec 256),
   (0x1302c170b6c1b7c0#64 ++ 0x84c0b05c2db06df0#64 ++ 0x5f03e1f0ffc3ffc3#64 ++ 0x97c0f87c3ff0fff0#64 : BitVec 256),
   (0x23b801ba03e802a8#64 ++ 0x08ee006e80fa00aa#64 ++ 0xeffc01ff03fc03fc#64 ++ 0xfbff007fc0ff00ff#64 : BitVec 256),
   (0x57df7a00037ed800#64 ++ 0x55f7de8000dfb600#64 ++ 0x77fffe0003fffc03#64 ++ 0x1dffff8000ffff00#64 : BitVec 256),
   (0xebeffddfd8000000#64 ++ 0x3afbff77f6000000#64 ++ 0x7bfffffffc000000#64 ++ 0x1effffffff000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [6, 5]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000004040c44 0x0000000001010311 0x80000000004c1ccd 0x2000000000130733

def z1 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0xfd0c7e1ffc7f1ffd 0xff431f87ff1fc7ff

def z2 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x7ef39fece3b3e332 0xdfbce7fb38ecf8cc

def z3 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z4 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z5 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x77fffe0003fffc03 0x1dffff8000ffff00

def z6 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x7bfffffffc000000 0x1effffffff000000

def z7 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0x02f001e003800000 0x00bc007800e00000

def z8 : W := mkw 0x23bc2fbf6fff0ffc 0x08ef0befdbffc3ff 0xfffc7fffffff1ffd 0xffff1fffffffc7ff

def z9 : W := mkw 0xebffffffffff0ffc 0x3affffffffffc3ff 0xffffffffffff1ffd 0xffffffffffffc7ff

def z10 : W := mkw 0x00042c0548000000 0x00010b0152000000 0x790c7e1ffc000000 0x1e431f87ff000000

def z11 : W := mkw 0xebefffdffc170d54 0x3afbfff7ff05c355 0xfffffffffc7f1ffd 0xffffffffff1fc7ff

def z12 : W := mkw 0xcc47fe45f8136111 0x3311ff917e04d844 0x1003fe00fc03e002 0x0400ff803f00f800

def z13 : W := mkw 0x0300011000000000 0x00c0004400000000 0x4b0001f000000000 0x12c0007c00000000

def z14 : W := mkw 0x538a400002489000 0x54e2900000922400 0x0000000000000000 0x0000000000000000

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0x84000000007c03fc 0xe1000000001f00ff

def z16 : W := mkw 0x23a801ba02c802a8 0x08ea006e80b200aa 0x890c01ff004c03fc 0xe243007fc01300ff

def z17 : W := mkw 0x0000060460130110 0x000001811804c044 0x7c001e0ce0330330 0xdf000783380cc0cc

def z18 : W := mkw 0x0c75beededb76f75 0x031d6fbb7b6ddbdd 0xffffffffffffffff 0xffffffffffffffff

def z19 : W := mkw 0x0451120001324000 0x01144480004c9000 0x76f39e0003b3e002 0x1dbce78000ecf800

def z20 : W := mkw 0x73be69ba03ec9aa8 0x5cef9a6e80fb26aa 0xeffc61ff03fc1ffd 0xfbff187fc0ff07ff

def z21 : W := mkw 0x1b63d5fcf6c1b7c0 0x86d8f57f3db06df0 0x7ff3fffcffc3ffc3 0x9ffcffff3ff0fff0

def z22 : W := mkw 0x0c7196ece3fb63b9 0x031c65bb38fed8ee 0xfef39fece3ffe3fe 0xffbce7fb38fff8ff

def z23 : W := mkw 0x0004280108040804 0x00010a0042010201 0x800c0003000c000c 0x20030000c0030003

def z24 : W := mkw 0xebebd1da90000000 0x3afaf476a4000000 0x02f381e000000000 0x00bce07800000000

def z25 : W := mkw 0x003000a801a00220 0x000c002a00680088 0x6ef001ec03b00330 0xdbbc007b00ec00cc

def z26 : W := mkw 0x0c419644e0136111 0x031065913804d844 0x10039e00e003e002 0x0400e7803800f800

def z27 : W := mkw 0x2be995dec0000000 0x0afa6577b0000000 0x7bff9fffe0000000 0x1effe7fff8000000

def z28 : W := mkw 0x082084ece0812331 0x0208213b382048cc 0x080001ece0000330 0xc200007b380000cc

def z29 : W := mkw 0x538e6800024c9800 0x54e39a0000932600 0x010c6000004c1c01 0x0043180000130700

def z30 : W := mkw 0xebfbd1fa93e802a8 0x3afef47ea4fa00aa 0x02f381e003800000 0x00bce07800e00000

def z31 : W := mkw 0x0410022025b76f75 0x01040088096ddbdd 0x8400000003ffffff 0xe100000000ffffff

def z32 : W := mkw 0x082084ccc0000000 0x0208213330000000 0x080001ece0000000 0x0200007b38000000

def z33 : W := mkw 0x1302400002409000 0x04c0900000902400 0x5703e00003c3fc03 0x15c0f80000f0ff00

def z34 : W := mkw 0x57dffb70b7ffffc0 0xd5f7fedc2dfffff0 0x7ffffff0ffffffc3 0x9ffffffc3ffffff0

def z35 : W := mkw 0x1302c370b6d7bfd4 0x84c0b0dc2db5eff5 0xdf03e1f0ffffffff 0xf7c0f87c3fffffff

def z36 : W := mkw 0x003080e8a1a12320 0x000c203a286848c8 0x7ef381ece3b3e332 0xdfbce07b38ecf8cc

def z37 : W := mkw 0x04519260a1b36300 0x01146498286cd8c0 0x7ef39fe0e3b3e302 0x9fbce7f838ecf8c0

def z38 : W := mkw 0x00042e0548160800 0x00010b8152058200 0x7d0c7e1ffc7f1c01 0x1f431f87ff1fc700

def z39 : W := mkw 0x0865bccdc8000000 0x02196f3372000000 0x7bfffffffc000000 0x1effffffff000000

def z40 : W := mkw 0x00042e0548160814 0x00010b8152058205 0xa00c1e0f003c003c 0x68030783c00f000f

def z41 : W := mkw 0x0302c150b4010540 0x00c0b0542d004150 0x5f03e1f0fc431fc1 0x97c0f87c3f10c7f0

def z42 : W := mkw 0x00000110140004c0 0x8000004405000130 0x000000101c0000c0 0x0000000407000030

def z43 : W := mkw 0x003000a803e802a8 0x000c002a00fa00aa 0xeef001ec03fc03fc 0xfbbc007b00ff00ff

def z44 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x22ff9fef00000000 0x08bfe7fbc0000000

def z45 : W := mkw 0xe867fddfd8000000 0x3a19ff77f6000000 0x1803fffffc000000 0x0600ffffff000000

def z46 : W := mkw 0x54577a00037ed800 0x5515de8000dfb600 0x1403fe0003fffc03 0x0500ff8000ffff00

def z47 : W := mkw 0x20b8008a01280028 0x082e0022804a000a 0xedfc001f007c03fc 0xfb7f0007c01f00ff

def z48 : W := mkw 0x1302c17092c0b280 0x84c0b05c24b02ca0 0x5703e1e003c3fc03 0x15c0f87800f0ff00

def z49 : W := mkw 0x0c71168c41324031 0x031c45a3104c900c 0x20f01e0c00300030 0x483c0783000c000c

def z50 : W := mkw 0x00008060a0812300 0x00002018282048c0 0x5e0381e0e383e302 0x9780e07838e0f8c0

def z51 : W := mkw 0x1f73d7fcf7f3f7f1 0x87dcf5ff3dfcfdfc 0x7ff3fffcfff3fff3 0xdffcffff3ffcfffc

def z52 : W := mkw 0xeffffffffbfb63b9 0x3bfffffffefed8ee 0xffffffffffffe3fe 0xfffffffffffff8ff

def z53 : W := mkw 0x04142e256db76f75 0x01050b895b6ddbdd 0xfd0c7e1fffffffff 0xff431f87ffffffff

def z54 : W := mkw 0x1002c040b401b540 0x8400b0102d006d50 0x1003e000fc03fc03 0x0400f8003f00ff00

def z55 : W := mkw 0x0000020024170d54 0x000000800905c355 0x84000000007f1ffd 0xe1000000001fc7ff

def z56 : W := mkw 0x2ff991fa83e862a9 0x0bfe647ea0fa18aa 0xefff81ff03fce3fe 0xfbffe07fc0ff38ff

def z57 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0x10007e00fc031c01 0x04001f803f00c700

def z58 : W := mkw 0x1410022027ffffc0 0xc504008809fffff0 0x0400000003ffffc3 0x8100000000fffff0

def z59 : W := mkw 0x0c75beece1b76b31 0x031d6fbb386ddacc 0x7fffffece3ffff33 0xdffffffb38ffffcc

def z60 : W := mkw 0xebeff9da90000000 0x3afbfe76a4000000 0x73ffffe000000000 0x1cfffff800000000

def z61 : W := mkw 0x000004056c010554 0x000001015b004155 0x8800001ffc0003fc 0xe2000007ff0000ff

def z62 : W := mkw 0x175352000372d000 0x05d4d48000dcb400 0x77f3fe0003f3fc03 0x1dfcff8000fcff00

def z63 : W := mkw 0x1002c060b481b740 0x8400b0182d206dd0 0x5e03e1e0ff83ff03 0x9780f8783fe0ffc0

def z64 : W := mkw 0xe8edbddfd8000000 0x3a3b6f77f6000000 0x28fc1ffffc000000 0x0a3f07ffff000000

def z65 : W := mkw 0xa82085ffd88002a8 0x2a08217ff62000aa 0x880001fffc0003fc 0xe200007fff0000ff

def z66 : W := mkw 0xebebd5ded0000000 0x3afaf577b4000000 0x7af39fece0000000 0x1ebce7fb38000000

def z67 : W := mkw 0x13024110164094c0 0x84c0904405902530 0x010060101c401cc1 0x0040180407100730

def z68 : W := mkw 0xe38e691318000000 0x38e39a44c6000000 0x010c60131c000000 0x00431804c7000000

def z69 : W := mkw 0x086194ccc0000000 0x0218653330000000 0x7af39fece0000000 0x1ebce7fb38000000

def z70 : W := mkw 0xa82085dfd8000000 0x2a082177f6000000 0x080001fffc000000 0x0200007fff000000

def z71 : W := mkw 0x0300000002400000 0x00c0000000900000 0x4700000003c00000 0x11c0000000f00000

def z72 : W := mkw 0xfbfffdffffe9b7e8 0xbeffff7ffffa6dfa 0xffffffffffffffff 0xffffffffffffffff

def z73 : W := mkw 0xffff7e8f4b7ed800 0x7fffdfa3d2dfb600 0x77fffe0f03fffc03 0x1dffff83c0ffff00

def z74 : W := mkw 0x43cf780000000000 0x10f3de0000000000 0x73fffe0000000000 0x1cffff8000000000

def z75 : W := mkw 0xffffffdfdb7ed800 0x7ffffff7f6dfb600 0x7ffffffffffffc03 0x1fffffffffffff00

def z76 : W := mkw 0x00042a0024170d54 0x00010a800905c355 0xf50c7e00007f1ffd 0xfd431f80001fc7ff

def z77 : W := mkw 0x57dffb7093fefa80 0xd5f7fedc24ffbea0 0x77ffffe003fffc03 0x1dfffff800ffff00

def z78 : W := mkw 0x0451160461334110 0x01144581184cd044 0x7ef39e0ce3b3e332 0xdfbce78338ecf8cc

def z79 : W := mkw 0x54477e056c17dd54 0x5511df815b05f755 0x1003fe00fc03fc03 0x0400ff803f00ff00

def z80 : W := mkw 0xe3be69bb1be802a8 0x38ef9a6ec6fa00aa 0xeffc61ff1ffc03fc 0xfbff187fc7ff00ff

def z81 : W := mkw 0x64fd3a8a013e4828 0x593f4ea2804f920a 0xa0fc1e0f003c003c 0x683f0783c00f000f

def z82 : W := mkw 0xa82085fff8812331 0x2a08217ffe2048cc 0x080001fffc000330 0xc200007fff0000cc

def z83 : W := mkw 0xfbeffdfffec1b7c0 0xbefbff7fffb06df0 0x7fffffffffc3ffc3 0x9ffffffffff0fff0

def z84 : W := mkw 0x57df7a2003fedaa8 0x55f7de8800ffb6aa 0xf7fffe0003ffffff 0xfdffff8000ffffff

def z85 : W := mkw 0x63ff79ba03e802a8 0x18ffde6e80fa00aa 0xffffffff03fc03fc 0xffffffffc0ff00ff

def z86 : W := mkw 0x0000000024010540 0x0000000009004150 0x5d006010fc431fc1 0x974018043f10c7f0

def z87 : W := mkw 0x1306ef75fed7bfd4 0x84c1bbdd7fb5eff5 0xff0fffffffffffff 0xffc3ffffffffffff

def z88 : W := mkw 0x57db50000368d000 0x55f6d40000da3400 0x02f380000380e002 0x00bce00000e03800

def z89 : W := mkw 0x0000020000160800 0x0000008000058200 0x04000000007f1c01 0x01000000001fc700

def z90 : W := mkw 0x1b22c5fcf6c1b7f1 0x86c8b17f3db06dfc 0x5f03e1fcffc3fff3 0xd7c0f87f3ff0fffc

def z91 : W := mkw 0xa824addfd8000000 0x2a092b77f6000000 0x790c7ffffc000000 0x1e431fffff000000

def z92 : W := mkw 0x20b8008a01280028 0x082e0022804a000a 0xa0fc000f003c003c 0x683f0003c00f000f

def z93 : W := mkw 0x1f73d6ece3f3f331 0x07dcf5bb38fcfccc 0x7ff3ffece3f3ff33 0xdffcfffb38fcffcc

def z94 : W := mkw 0x1002c060b6c1b7c0 0x8400b0182db06df0 0x1403e000ffc3ffc3 0x8500f8003ff0fff0

def z95 : W := mkw 0x1302c15092409000 0x04c0b05424902400 0x5f03e1f0ffc3fc03 0x17c0f87c3ff0ff00

def z96 : W := mkw 0x43cf7c0548000000 0x10f3df0152000000 0x7bfffe1ffc000000 0x1effff87ff000000

def z97 : W := mkw 0x00008170b48127c0 0x8000205c2d2049f0 0x080001f0fc0003c0 0x8200007c3f0000f0

def z98 : W := mkw 0x57df7a2023fffb31 0x55f7de8808fffecc 0x77fffe0003ffff33 0xddffff8000ffffcc

def z99 : W := mkw 0x33bac1fab7e9b7e8 0x8ceeb07eadfa6dfa 0xffffe1ffffffffff 0xfffff87fffffffff

def z100 : W := mkw 0x04553a0001364800 0x01154e80004d9200 0x77fffe0003fffc03 0x1dffff8000ffff00

def z101 : W := mkw 0x00042a0000160800 0x00010a8000058200 0x750c7e00007f1c01 0x1d431f80001fc700

def z102 : W := mkw 0x23a8019a00000000 0x08ea006680000000 0xeffc01ff007c03fc 0xfbff007fc01f00ff

def z103 : W := mkw 0x2388011202480088 0x08e2004480920022 0x810c0013004c00cc 0x20430004c0130033

def z104 : W := mkw 0x00008060a4812740 0x00002018292049d0 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z105 : W := mkw 0x0c7190e881a06221 0x031c643a20681888 0x02f381e00380e002 0x00bce07800e03800

def z106 : W := mkw 0x0c7196ededb36775 0x031c65bb7b6cd9dd 0xfef39fffffb3e3fe 0xffbce7ffffecf8ff

def z107 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0x6bfc01ff03800000 0x1aff007fc0e00000

def z108 : W := mkw 0x0302c15090000000 0x00c0b05424000000 0x5b03e1f0fc000000 0x16c0f87c3f000000

def z109 : W := mkw 0x57cf7a000016d800 0x55f3de800005b600 0x73fffe000003fc03 0x1cffff800000ff00

def z110 : W := mkw 0x408c2800000c0800 0x50230a0000030200 0x000c0000000c0000 0x0003000000030000

def z111 : W := mkw 0x1000002026c1b7c0 0x8400000809b06df0 0x0400000003c3ffc3 0x8100000000f0fff0

def z112 : W := mkw 0x1c7196ece7f3f7f1 0x871c65bb39fcfdfc 0x7ef39fece3f3fff3 0xdfbce7fb38fcfffc

def z113 : W := mkw 0x5ffffae883fefa21 0x57fffeba20ffbe88 0x77ffffe003fffc03 0x1dfffff800ffff00

def z114 : W := mkw 0x5ffbd0e883e8f221 0x57fef43a20fa3c88 0x02f381e00380e002 0x00bce07800e03800

def z115 : W := mkw 0x0c7197fcf5b367f1 0x831c65ff3d6cd9fc 0x7ef39ffcffb3e3f2 0xdfbce7ff3fecf8fc

def z116 : W := mkw 0x14100200037ed800 0x4504008000dfb600 0x0400000003fffc03 0x0100000000ffff00

def z117 : W := mkw 0x238c29130e4c0ccc 0x08e30a44c3930333 0x810c60131c4c1ccd 0x20431804c7130733

def z118 : W := mkw 0x2ff997fee3fb63b9 0x0bfe65ffb8fed8ee 0xffff9fffe3ffe3fe 0xffffe7fff8fff8ff

def z119 : W := mkw 0x44dd3a00013e4800 0x51374e80004f9200 0x20fc1e00003c0000 0x083f0780000f0000

def z120 : W := mkw 0x0010002003e802a8 0x0004000800fa00aa 0x8400000003fc03fc 0xe100000000ff00ff

def z121 : W := mkw 0xc847fc45d8000000 0x3211ff1176000000 0x1003fe00fc000000 0x0400ff803f000000

def z122 : W := mkw 0x0410022023fb63b9 0x0104008808fed8ee 0x8400000003ffe3fe 0xe100000000fff8ff

def z123 : W := mkw 0x57df7b10177edcc0 0xd5f7dec405dfb730 0x77fffe101ffffcc3 0x1dffff8407ffff30

def z124 : W := mkw 0xc867fccdd8000000 0x3219ff3376000000 0x7af3ffecfc000000 0x1ebcfffb3f000000

def z125 : W := mkw 0x003000a801a00220 0x000c002a00680088 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z126 : W := mkw 0x0410022021b36331 0x01040088086cd8cc 0x0400000003b3e332 0xc100000000ecf8cc

def z127 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0xb00c7e0ffc3f1c3d 0x6c031f83ff0fc70f

def z128 : W := mkw 0x77ff7a8a037ed828 0x5dffdea280dfb60a 0xf7fffe0f03fffc3f 0x7dffff83c0ffff0f

def z129 : W := mkw 0x0000000000000000 0x0000000000000000 0x4d000010004003c0 0x93400004001000f0

def z130 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x060381e003c3ffc3 0x8180e07800f0fff0

def z131 : W := mkw 0x0398000003680000 0x00e6000000da0000 0x67fc000003fc0000 0x19ff000000ff0000

def z132 : W := mkw 0x77ff7bba03fedaa8 0x5dffdeee80ffb6aa 0xffffffff03ffffff 0xffffffffc0ffffff

def z133 : W := mkw 0x0000806080802200 0x0000201820200880 0x020381e00380e002 0x0080e07800e03800

def z134 : W := mkw 0x43cb500000000000 0x10f2d40000000000 0x02f3800000000000 0x00bce00000000000

def z135 : W := mkw 0xc847fe45fc170d54 0x3211ff917f05c355 0x1003fe00fc031c01 0x0400ff803f00c700

def z136 : W := mkw 0x0000002000800200 0x0000000800200080 0x4e0001e003800300 0x9380007800e000c0

def z137 : W := mkw 0x1302400002409000 0x04c0900000902400 0x0100600000401c01 0x0040180000100700

def z138 : W := mkw 0x2cf9168e413a4039 0x0b3e45a3904e900e 0xa0fc1e0f003c003c 0x683f0783c00f000f

def z139 : W := mkw 0x57dbd17093e8f280 0xd5f6f45c24fa3ca0 0x02f381e00380e002 0x00bce07800e03800

def z140 : W := mkw 0x538e6a00025e9800 0x54e39a800097a600 0x750c7e00007f1c01 0x1d431f80001fc700

def z141 : W := mkw 0x086190c880000000 0x0218643220000000 0x02f381e000000000 0x00bce07800000000

def z142 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0xfffffe1f03ffffff 0xffffff87c0ffffff

def z143 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x12f3fe000383fc03 0x04bcff8000e0ff00

def z144 : W := mkw 0x57dffa60a3fffb00 0x55f7fe9828fffec0 0x7fffffe0e3ffff03 0x9ffffff838ffffc0

def z145 : W := mkw 0x0c41904080006001 0x0310641020001800 0x000380000000e002 0x0000e00000003800

def z146 : W := mkw 0x538e6910164c9cc0 0xd4e39a4405932730 0x010c60101c4c1cc1 0x0043180407130730

def z147 : W := mkw 0x04108260a1b36331 0x01042098286cd8cc 0x5e0381e0e3b3e332 0xd780e07838ecf8cc

def z148 : W := mkw 0xcc77feedf9b36331 0x331dffbb7e6cd8cc 0x7ef3ffecffb3e332 0xdfbcfffb3fecf8cc

def z149 : W := mkw 0x0000815090000000 0x0000205424000000 0x080001f0fc000000 0x0200007c3f000000

def z150 : W := mkw 0x1300013026c1b7c0 0x84c0004c09b06df0 0x4f0001f003c3ffc3 0x93c0007c00f0fff0

def z151 : W := mkw 0xeffffffffdb76f75 0x3bffffffff6ddbdd 0xffffffffffffffff 0xffffffffffffffff

def z152 : W := mkw 0x14142a00037ed800 0x45050a8000dfb600 0x750c7e0003fffc03 0x1d431f8000ffff00

def z153 : W := mkw 0x33b801ba27e9b7e8 0x8cee006e89fa6dfa 0xeffc01ff03ffffff 0xfbff007fc0ffffff

def z154 : W := mkw 0x33aac1fab6c1b7c0 0x8ceab07eadb06df0 0x7fffe1ffffc3ffc3 0x9ffff87ffff0fff0

def z155 : W := mkw 0x538e6800024c9800 0x54e39a0000932600 0x570fe00003cffc03 0x15c3f80000f3ff00

def z156 : W := mkw 0x23a8019a00000000 0x08ea006680000000 0x6bfc01ff00000000 0x1aff007fc0000000

def z157 : W := mkw 0x57df7e056f7fdd54 0x55f7df815bdff755 0xfffffe1fffffffff 0xffffff87ffffffff

def z158 : W := mkw 0x54477a000016d800 0x5511de800005b600 0x1003fe000003fc03 0x0400ff800000ff00

def z159 : W := mkw 0x0398000003680000 0x00e6000000da0000 0xeffc001f03fc03fc 0xfbff0007c0ff00ff

def z160 : W := mkw 0x0010002003e802a8 0x0004000800fa00aa 0xed0c001f03fc03fc 0xfb430007c0ff00ff

def z161 : W := mkw 0xeffbd1fa91a06221 0x3bfef47ea4681888 0x02f381e00380e002 0x00bce07800e03800

def z162 : W := mkw 0xfffffffffbfffb31 0x7ffffffffefffecc 0x7fffffffffffff33 0xdfffffffffffffcc

def z163 : W := mkw 0xc8453c0548000000 0x32114f0152000000 0x00001e0000000000 0x0000078000000000

def z164 : W := mkw 0x3322c1fab6c1b7e8 0x8cc8b07eadb06dfa 0xdf03e1ffffc3ffff 0xf7c0f87ffff0ffff

def z165 : W := mkw 0x00042c056c010554 0x00010b015b004155 0xf90c7e1ffc0003fc 0xfe431f87ff0000ff

def z166 : W := mkw 0x1302c17092c0b280 0x84c0b05c24b02ca0 0x020381e00380e002 0x0080e07800e03800

def z167 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x12f39fe0e383e002 0x04bce7f838e0f800

def z168 : W := mkw 0x0865becdec170d54 0x02196fb37b05c355 0xfffffffffc7f1ffd 0xffffffffff1fc7ff

def z169 : W := mkw 0x13024110364195c0 0x84c090440d906570 0x5d006010fc431fc1 0x974018043f10c7f0

def z170 : W := mkw 0x0c7196ece5b36771 0x031c65bb396cd9dc 0x7ff3fffcfff3fff3 0xdffcffff3ffcfffc

def z171 : W := mkw 0x0c45be45ec176d55 0x03116f917b05db55 0xfd0ffe1ffc7fffff 0xff43ff87ff1fffff

def z172 : W := mkw 0x1f43d774f6d3f7d1 0x87d0f5dd3db4fdf4 0x5f03fff0ffc3ffc3 0x97c0fffc3ff0fff0

def z173 : W := mkw 0xeffffffff9b36331 0x3bfffffffe6cd8cc 0x7fffffffffb3e332 0xdfffffffffecf8cc

def z174 : W := mkw 0x086194ece0812331 0x0218653b382048cc 0x7af39fece0000330 0xdebce7fb380000cc

def z175 : W := mkw 0x57df7a010f7edc44 0x55f7de8043dfb711 0xf7fffe131ffffccf 0x3dffff84c7ffff33

def z176 : W := mkw 0x33bac1fab7e9b7e8 0x8ceeb07eadfa6dfa 0x5ff3e1f0ffc3ffc3 0x97fcf87c3ff0fff0

def z177 : W := mkw 0x0000000020010100 0x0000000008004040 0x5c000000e0030300 0x970000003800c0c0

def z178 : W := mkw 0x0302c15090000000 0x00c0b05424000000 0x020381e000000000 0x0080e07800000000

def z179 : W := mkw 0x23aac1da90000000 0x08eab076a4000000 0x7bffe1fffc000000 0x1efff87fff000000

def z180 : W := mkw 0x17124200037ed800 0x45c4908000dfb600 0x5703e00003fffc03 0x15c0f80000ffff00

def z181 : W := mkw 0x2020019a00000000 0x0808006680000000 0x080001ff00000000 0x0200007fc0000000

def z182 : W := mkw 0x0c3086ece1b36331 0x030c21bb386cd8cc 0x0c0001ece3b3e332 0xc300007b38ecf8cc

def z183 : W := mkw 0xf38e69131a4c9800 0x7ce39a44c6932600 0x010c60131c4c1c01 0x00431804c7130700

def z184 : W := mkw 0x0004ae65ec972f54 0x00012b997b25cbd5 0xff0fffffffffffff 0xffc3ffffffffffff

def z185 : W := mkw 0xffffffffdbfedaa8 0x7ffffffff6ffb6aa 0xffffffffffffffff 0xffffffffffffffff

def z186 : W := mkw 0x57df7800036cd800 0x55f7de0000db3600 0x03ffe00003ccfc03 0x00fff80000f33f00

def z187 : W := mkw 0x2388011202480088 0x08e2004480920022 0xed0c001f007c03fc 0xfb430007c01f00ff

def z188 : W := mkw 0x538e68010e4c9c44 0x54e39a0043932711 0x810c60131c4c1ccd 0x20431804c7130733

def z189 : W := mkw 0x03008170a2c12380 0x00c0205c28b048e0 0x5f0381f0e3c3e3c2 0x97c0e07c38f0f8f0

def z190 : W := mkw 0x0000013000800280 0x0000004c002000a0 0x080001f0000003c0 0x8200007c000000f0

def z191 : W := mkw 0xebfffddfd9280028 0x3affff77f64a000a 0xfbfffffffc3c003c 0x7effffffff0f000f

def z192 : W := mkw 0x087194ecc1a00220 0x021c653b30680088 0x7ef39fece3b00330 0xdfbce7fb38ec00cc

def z193 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0x8af001ff038003fc 0xe2bc007fc0e000ff

def z194 : W := mkw 0x0300013002c00280 0x00c0004c00b000a0 0x4f0001f003c003c0 0x93c0007c00f000f0

def z195 : W := mkw 0x10042e256ed7bfd4 0x84010b895bb5eff5 0xfd0c7e1fffffffff 0xff431f87ffffffff

def z196 : W := mkw 0x43df780003680000 0x10f7de0000da0000 0x77fffe0003fc0000 0x1dffff8000ff0000

def z197 : W := mkw 0x203001ba03e802a8 0x080c006e80fa00aa 0x8c0001ff03fc03fc 0xe300007fc0ff00ff

def z198 : W := mkw 0x1410022023fffb31 0x4504008808fffecc 0x0400000003ffff33 0xc100000000ffffcc

def z199 : W := mkw 0x1302c17092c0b280 0x84c0b05c24b02ca0 0x5b03e1f0ff80e002 0x16c0f87c3fe03800

def z200 : W := mkw 0xebfffdffd9a00220 0x3affff7ff6680088 0x7fffffffffb00330 0xdfffffffffec00cc

def z201 : W := mkw 0xebfd3dbf4be802a8 0x3aff4f6fd2fa00aa 0xeffc1fff03fc03fc 0xfbff07ffc0ff00ff

def z202 : W := mkw 0x0000000000000000 0x0000000000000000 0xed0c001f007c03fc 0xfb430007c01f00ff

def z203 : W := mkw 0x0000000024010554 0x0000000009004155 0x80000000000003fc 0xe0000000000000ff

def z204 : W := mkw 0x27f913ba03fa42a8 0x09fe44ee80fe90aa 0xffff9fff03ffe3fe 0xffffe7ffc0fff8ff

def z205 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800001f000003fc 0xe2000007c00000ff

def z206 : W := mkw 0x1302c170b2c1b380 0x84c0b05c2cb06ce0 0x5e0381e0e383e302 0x9780e07838e0f8c0

def z207 : W := mkw 0x0000060464130550 0x000001811904c154 0x7d007e1cfc731ff1 0xdf401f873f1cc7fc

def z208 : W := mkw 0x44d9100001284000 0x51364400004a1000 0x00f0000000000000 0x003c000000000000

def z209 : W := mkw 0x57db5200037ed800 0x55f6d48000dfb600 0x06f3800003fffc03 0x01bce00000ffff00

def z210 : W := mkw 0x33bac1fa93e8b2a8 0x8ceeb07ea4fa2caa 0x02f381e00380e002 0x00bce07800e03800

def z211 : W := mkw 0x2ff997fee1b36331 0x0bfe65ffb86cd8cc 0x7fff9fffe3b3e332 0xdfffe7fff8ecf8cc

def z212 : W := mkw 0x0c7196ecc1b26231 0x031c65bb306c988c 0x22f39fec03b0e032 0x48bce7fb00ec380c

def z213 : W := mkw 0x5fdffe44e37ff911 0x57f7ff9138dffe44 0x77fffe00e3fffc03 0x1dffff8038ffff00

def z214 : W := mkw 0x1302c150964094c0 0x84c0b05425902530 0x5b03e1f0fc401cc1 0x16c0f87c3f100730

def z215 : W := mkw 0x0c419664e0936311 0x031065993824d8c4 0x5e039fe0e383e302 0x9780e7f838e0f8c0

def z216 : W := mkw 0x0306ef55fc170d54 0x00c1bbd57f05c355 0xff0ffffffc7f1ffd 0xffc3ffffff1fc7ff

def z217 : W := mkw 0xe38e6d1758000000 0x38e39b45d6000000 0x790c7e1ffc000000 0x1e431f87ff000000

def z218 : W := mkw 0x0000002020812300 0x00000008082048c0 0x040000000383e302 0x8100000000e0f8c0

def z219 : W := mkw 0xa820048f48000000 0x2a080123d2000000 0x0000000f00000000 0x00000003c0000000

def z220 : W := mkw 0x54477e056c17dd54 0x5511df815b05f755 0xfd0ffe1ffc7fffff 0xff43ff87ff1fffff

def z221 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0x790c7e1ffc031c01 0x1e431f87ff00c700

def z222 : W := mkw 0x00042e0568130110 0x00010b815a04c044 0x7d0c7e1ffc330330 0xdf431f87ff0cc0cc

def z223 : W := mkw 0x20bc2e8f6d3f0d7c 0x082f0ba3db4fc35f 0xfdfc7e1ffc7f1ffd 0xff7f1f87ff1fc7ff

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z225 : W := mkw 0x2ffdbfffefff6ffd 0x0bff6ffffbffdbff 0xffffffffffffffff 0xffffffffffffffff

def z226 : W := mkw 0xebeffddffc010540 0x3afbff77ff004150 0x7ffffffffc431fc1 0x9fffffffff10c7f0

def z227 : W := mkw 0x0c71108801204021 0x031c442200481008 0x00f0000000000000 0x003c000000000000

def z228 : W := mkw 0x0c7196ece5b76f75 0x031c65bb396ddbdd 0xfef39fece3ffffff 0xffbce7fb38ffffff

def z229 : W := mkw 0xc006680118000000 0x30019a0046000000 0x000060001c000000 0x0000180007000000

def z230 : W := mkw 0x43cf7a0000160800 0x10f3de8000058200 0x77fffe00007f1c01 0x1dffff80001fc700

def z231 : W := mkw 0x0000060440120010 0x0000018110048004 0x20001e0c00300030 0x48000783000c000c

def z232 : W := mkw 0x0c7194ecc1a06221 0x031c653b30681888 0x7af39fece380e002 0x1ebce7fb38e03800

def z233 : W := mkw 0x000428012c050d44 0x00010a004b014351 0xdd0c6013fc4f1fcd 0xb7431804ff13c7f3

def z234 : W := mkw 0x003000a801a00220 0x000c002a00680088 0x02f001e003800000 0x00bc007800e00000

def z235 : W := mkw 0x0004280000000000 0x00010a0000000000 0x710c7e0000000000 0x1c431f8000000000

def z236 : W := mkw 0x23b803ba27ff0ffc 0x08ee00ee89ffc3ff 0xeffc01ff03ff1ffd 0xfbff007fc0ffc7ff

def z237 : W := mkw 0x0000060460130110 0x000001811804c044 0x10001e00e0030000 0x040007803800c000

def z238 : W := mkw 0x0410002001a06221 0x0104000800681888 0x000000000380e002 0x0000000000e03800

def z239 : W := mkw 0x1f73d7fcf3f3f3b1 0x87dcf5ff3cfcfcec 0x7ef39fece3b3e332 0xdfbce7fb38ecf8cc

def z240 : W := mkw 0xebfffdffdbe802a8 0x3affff7ff6fa00aa 0xfffffffffffc03fc 0xffffffffffff00ff

def z241 : W := mkw 0x082084edec812775 0x0208213b7b2049dd 0x880001fffc0003fc 0xe200007fff0000ff

def z242 : W := mkw 0x1306e971bec5bfc4 0x84c1ba5c6fb16ff1 0xdf0fe1f3ffcfffcf 0xb7c3f87cfff3fff3

def z243 : W := mkw 0x20b801ba01a802a8 0x082e006e806a00aa 0xa8fc01ff003c03fc 0xea3f007fc00f00ff

def z244 : W := mkw 0x086194ece0812300 0x0218653b382048c0 0x7ef39fece383e302 0x9fbce7fb38e0f8c0

def z245 : W := mkw 0x04100200013e4800 0x41040080004f9200 0x00000000003c0000 0x00000000000f0000

def z246 : W := mkw 0x202001ba008002a8 0x0808006e802000aa 0x880001ff000003fc 0xe200007fc00000ff

def z247 : W := mkw 0x23b8019a03680000 0x08ee006680da0000 0x6ffc01ff03fc0000 0x1bff007fc0ff0000

def z248 : W := mkw 0x23ac2d9f48000000 0x08eb0b67d2000000 0x7bfc7ffffc000000 0x1eff1fffff000000

def z249 : W := mkw 0x23a8019a00000000 0x08ea006680000000 0x02f001e000000000 0x00bc007800000000

def z250 : W := mkw 0x00042e0548160814 0x00010b8152058205 0xf90c7e1ffc3c003c 0x7e431f87ff0f000f

def z251 : W := mkw 0x0c519664e1b36331 0x03146599386cd8cc 0x14039e00e3b3e332 0xc500e78038ecf8cc

def z252 : W := mkw 0x0000020024170d54 0x000000800905c355 0x0000000000031c01 0x000000000000c700

def z253 : W := mkw 0x0000020020130110 0x000000800804c044 0x0400000000330330 0xc1000000000cc0cc

def z254 : W := mkw 0x0451120001324000 0x01144480004c9000 0x20f01e0000300000 0x083c0780000c0000

def z255 : W := mkw 0xd847fc45fc01b540 0xb611ff117f006d50 0x1003fe00fc03fc03 0x0400ff803f00ff00

def z256 : W := mkw 0x0c753e8d49364835 0x031d4fa3524d920d 0xa0fc1e0f003c003c 0x683f0783c00f000f

def z257 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0xfffffffffc7c03fc 0xffffffffff1f00ff

def z258 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x12f3ffe0fc000000 0x04bcfff83f000000

def z259 : W := mkw 0xebeffdfff8812300 0x3afbff7ffe2048c0 0x7fffffffff83e302 0x9fffffffffe0f8c0

def z260 : W := mkw 0x0002c04090000000 0x0000b01024000000 0x1003e000fc000000 0x0400f8003f000000

def z261 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0x750c7e00fc7f1c01 0x1d431f803f1fc700

def z262 : W := mkw 0x0c7192e8a1b36331 0x031c64ba286cd8cc 0x06f381e003b3e332 0xc1bce07800ecf8cc

def z263 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0x86f001e003fc03fc 0xe1bc007800ff00ff

def z264 : W := mkw 0xfffffbda937ed800 0x7ffffef6a4dfb600 0x77ffffe003fffc03 0x1dfffff800ffff00

def z265 : W := mkw 0x77df7b12037ed888 0x5df7dec480dfb622 0xf7fffe1303fffccf 0x3dffff84c0ffff33

def z266 : W := mkw 0x0c7196cce1336131 0x031c65b3384cd84c 0x30f39e0ce033e032 0x4c3ce783380cf80c

def z267 : W := mkw 0x0000020024170d54 0x000000800905c355 0xdd006010fc7f1ffd 0xf74018043f1fc7ff

def z268 : W := mkw 0x14511200037ed800 0x4514448000dfb600 0x76f39e0003fffc03 0x1dbce78000ffff00

def z269 : W := mkw 0x0302c17092c00280 0x00c0b05c24b000a0 0x5f03e1f0ffc003c0 0x97c0f87c3ff000f0

def z270 : W := mkw 0x1002c0409000b000 0x8400b01024002c00 0x000380000000e002 0x0000e00000003800

def z271 : W := mkw 0x00342ead6db70f74 0x000d0bab5b6dc3dd 0xfffc7fffffff1ffd 0xffff1fffffffc7ff

def z272 : W := mkw 0xdc47fe45d816d800 0x7711ff917605b600 0x1003fe00fc03fc03 0x0400ff803f00ff00

def z273 : W := mkw 0xa82081da90000000 0x2a082076a4000000 0x000001e000000000 0x0000007800000000

def z274 : W := mkw 0x000428010c040c44 0x00010a0043010311 0x810c60131c4c1ccd 0x20431804c7130733

def z275 : W := mkw 0xebeff9db98000000 0x3afbfe76e6000000 0x03ffe1f31c000000 0x00fff87cc7000000

def z276 : W := mkw 0x1410022027f3f7f1 0x8504008809fcfdfc 0x0400000003f3fff3 0xc100000000fcfffc

def z277 : W := mkw 0x0010000001200000 0x0004000000480000 0x66f0000003b00000 0x19bc000000ec0000

def z278 : W := mkw 0x1f73d1f8b7e1f7e1 0x87dcf47e2df87df8 0x5ff3e1f0ffc3ffc3 0x97fcf87c3ff0fff0

def z279 : W := mkw 0xebebd5dfd8000000 0x3afaf577f6000000 0x0af381fffc000000 0x02bce07fff000000

def z280 : W := mkw 0x57df78000368d000 0x55f7de0000da3400 0x73fffe000380e002 0x1cffff8000e03800

def z281 : W := mkw 0x03b800a803e80220 0x00ee002a00fa0088 0x6ffc01ec03fc0330 0xdbff007b00ff00cc

def z282 : W := mkw 0x00008040b4012540 0x800020102d004950 0x00000000fc000000 0x000000003f000000

def z283 : W := mkw 0x2088000200080008 0x0822000080020002 0x800c0003000c000c 0x20030000c0030003

def z284 : W := mkw 0x338ac172b6c9b7c8 0x8ce2b05cadb26df2 0xdf0fe1f3ffcfffcf 0xb7c3f87cfff3fff3

def z285 : W := mkw 0x00042e054c160c54 0x00010b8153058315 0xa10c7e1f1c7c1cfd 0x68431f87c71f073f

def z286 : W := mkw 0x23b8019a036800a8 0x08ee006680da002a 0xa1fc001f007c00fc 0x687f0007c01f003f

def z287 : W := mkw 0xfbeffddfda4c9800 0x7efbff77f6932600 0x7bfffffffc4c1c01 0x1effffffff130700

def z288 : W := mkw 0x0c7196ccc1324031 0x031c65b3304c900c 0x7af39fece0300030 0x5ebce7fb380c000c

def z289 : W := mkw 0xebefffdff8130110 0x3afbfff7fe04c044 0x7ffffffffc330330 0xdfffffffff0cc0cc

def z290 : W := mkw 0x0000020000160814 0x0000008000058205 0x80000000003c003c 0x60000000000f000f

def z291 : W := mkw 0x1302413036c1b7c0 0x84c0904c0db06df0 0x050060101fc3ffc3 0x8140180407f0fff0

def z292 : W := mkw 0x1000000002409000 0x0400000000902400 0x0400000003c3fc03 0x0100000000f0ff00

def z293 : W := mkw 0x0ff996ece3fb6331 0x03fe65bb38fed8cc 0x7fff9fece3ffe332 0xdfffe7fb38fff8cc

def z294 : W := mkw 0x0c6196ece0936331 0x031865bb3824d8cc 0x18039fece003e332 0xc600e7fb3800f8cc

def z295 : W := mkw 0x0000000024010540 0x0000000009004150 0x10006000fc031c01 0x040018003f00c700

def z296 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0x910c7e13fc4f1ccd 0x24431f84ff13c733

def z297 : W := mkw 0x44453a0000164800 0x51114e8000059200 0x00001e0000000000 0x0000078000000000

def z298 : W := mkw 0x0c45be45ec176d55 0x03116f917b05db55 0x1003fe00fc03fc03 0x0400ff803f00ff00

def z299 : W := mkw 0x5ffffffcf7fffff1 0xd7ffffff3dfffffc 0x7ffffffcfffffff3 0xdfffffff3ffffffc

def z300 : W := mkw 0x539e6800036c9800 0x54e79a0000db2600 0x67fc600003fc1c01 0x19ff180000ff0700

def z301 : W := mkw 0x57db5200037ad000 0x55f6d48000deb400 0x76f39e0003b3e002 0x1dbce78000ecf800

def z302 : W := mkw 0x57df7e054b7ed800 0x55f7df8152dfb600 0x7ffffe1ffffffc03 0x1fffff87ffffff00

def z303 : W := mkw 0x0824aeedec972f75 0x02092bbb7b25cbdd 0xfd0c7ffffc7f1ffd 0xff431fffff1fc7ff

def z304 : W := mkw 0xa824afdffc170d54 0x2a092bf7ff05c355 0xfd0c7ffffc7f1ffd 0xff431fffff1fc7ff

def z305 : W := mkw 0x44dd3a00013e4800 0x51374e80004f9200 0x75fc7e00007f1c01 0x1d7f1f80001fc700

def z306 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0xffff9fffe3ffe3fe 0xffffe7fff8fff8ff

def z307 : W := mkw 0xebebd1da90000000 0x3afaf476a4000000 0x6bff81ff00000000 0x1affe07fc0000000

def z308 : W := mkw 0x57dbd170b7e9f7c0 0xd5f6f45c2dfa7df0 0x5ff3e1f0ffc3ffc3 0x97fcf87c3ff0fff0

def z309 : W := mkw 0x10008170b6c1b7c0 0x8400205c2db06df0 0x0c0001f0ffc3ffc3 0x8300007c3ff0fff0

def z310 : W := mkw 0x082085fcf48127f1 0x8208217f3d2049fc 0x080001fcfc0003f0 0xc200007f3f0000fc

def z311 : W := mkw 0x00042a012c170d54 0x00010a804b05c355 0x850c60131c7f1ffd 0xe1431804c71fc7ff

def z312 : W := mkw 0x37b803ba03fedaa8 0x4dee00ee80ffb6aa 0xeffc01ff03ffffff 0xfbff007fc0ffffff

def z313 : W := mkw 0x0020008800000000 0x0008002200000000 0x6af001ec00000000 0x1abc007b00000000

def z314 : W := mkw 0xaba885dfd8000000 0x2aea2177f6000000 0x6bfc01fffc000000 0x1aff007fff000000

def z315 : W := mkw 0x202001ba008002a8 0x0808006e802000aa 0x000001e000000000 0x0000007800000000

def z316 : W := mkw 0x538e6e056e5f9d54 0x54e39b815b97e755 0xfd0c7e1ffc7f1ffd 0xff431f87ff1fc7ff

def z317 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0xff0fe1ffffffffff 0xffc3f87fffffffff

def z318 : W := mkw 0xecfd3e8f49324031 0x3b3f4fa3d24c900c 0x20fc1e0f00300030 0x483f0783c00c000c

def z319 : W := mkw 0x00000020248127c0 0x80000008092049f0 0x00000000000003c0 0x80000000000000f0

def z320 : W := mkw 0x57dfff75ffffffd4 0xd5f7ffdd7ffffff5 0xffffffffffffffff 0xffffffffffffffff

def z321 : W := mkw 0xebefffdfd8160800 0x3afbfff7f6058200 0x7ffffffffc7f1c01 0x1fffffffff1fc700

def z322 : W := mkw 0x086196cce0130110 0x021865b33804c044 0x7ef39fece0330330 0xdfbce7fb380cc0cc

def z323 : W := mkw 0x0b63d5dcd0000000 0x02d8f57734000000 0x7bf3fffcfc000000 0x1efcffff3f000000

def z324 : W := mkw 0x1002400014009440 0x8400900005002510 0x000060001c001c01 0x0000180007000700

def z325 : W := mkw 0x0000002002c00280 0x0000000800b000a0 0x0400000003c003c0 0x8100000000f000f0

def z326 : W := mkw 0x53cff970b6c1b7c0 0x94f3fe5c2db06df0 0x7ffffff0ffc3ffc3 0x9ffffffc3ff0fff0

def z327 : W := mkw 0x1302c17096c0b6c0 0x84c0b05c25b02db0 0x0303e1f01fc0fcc3 0x00c0f87c07f03f30

def z328 : W := mkw 0x0300013026c107c0 0x00c0004c09b041f0 0x5f0061f0ffc31fc1 0x97c0187c3ff0c7f0

def z329 : W := mkw 0x0c419644e0136111 0x031065913804d844 0x7c039e0ce033e332 0xdf00e783380cf8cc

def z330 : W := mkw 0xebeffddfdc040c44 0x3afbff77f7010311 0xfbfffffffc4c1ccd 0x3effffffff130733

def z331 : W := mkw 0x77fb51ba03e8d2a8 0x5dfed46e80fa34aa 0xefff81ff03fce3fe 0xfbffe07fc0ff38ff

def z332 : W := mkw 0x23bc2dbf4be802a8 0x08ef0b6fd2fa00aa 0xfffc7ffffffc03fc 0xffff1fffffff00ff

def z333 : W := mkw 0x08419444c0000000 0x0210651130000000 0x10039e00e0000000 0x0400e78038000000

def z334 : W := mkw 0x23b881fab7e927e8 0x88ee207eadfa49fa 0xeffc01fffffc03fc 0xfbff007fffff00ff

def z335 : W := mkw 0x033001b803e002a0 0x00cc006e00f800a8 0x6ff001fc03f003f0 0xdbfc007f00fc00fc

def z336 : W := mkw 0x33bac1fa93e8b2a8 0x8ceeb07ea4fa2caa 0xefff81ff03fce3fe 0xfbffe07fc0ff38ff

def z337 : W := mkw 0x238c2f176e5f0ddc 0x08e30bc5db97c377 0xfd0c7e1ffc7f1ffd 0xff431f87ff1fc7ff

def z338 : W := mkw 0x141000000368d000 0x4504000000da3400 0x000000000380e002 0x0000000000e03800

def z339 : W := mkw 0x20b800aa01a80228 0x082e002a806a008a 0xeefc01ef03bc033c 0xfbbf007bc0ef00cf

def z340 : W := mkw 0x0000060460130110 0x000001811804c044 0xfd0c1e1fe07f03fc 0xff430787f81fc0ff

def z341 : W := mkw 0x0030008801200020 0x000c002200480008 0x20f0000c00300030 0x483c0003000c000c

def z342 : W := mkw 0x13024110164094c0 0x84c0904405902530 0x5703e0101fc3fcc3 0x15c0f80407f0ff30

def z343 : W := mkw 0x5ffffeedefffff75 0x57ffffbb7bffffdd 0xffffffffffffffff 0xffffffffffffffff

def z344 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x1203e1e0ff83fc03 0x0480f8783fe0ff00

def z345 : W := mkw 0x57db50000368d000 0x55f6d40000da3400 0x67ff800003fce002 0x19ffe00000ff3800

def z346 : W := mkw 0x13066a0002569800 0x04c19a800095a600 0x770ffe0003fffc03 0x1dc3ff8000ffff00

def z347 : W := mkw 0x23bc2bba03fe0aa8 0x08ef0aee80ff82aa 0xfffc7fff03ff1ffd 0xffff1fffc0ffc7ff

def z348 : W := mkw 0x54577a000136d800 0x5515de80004db600 0x76f3fe0003b3fc03 0x1dbcff8000ecff00

def z349 : W := mkw 0x57dffb50937ed800 0x55f7fed424dfb600 0x7ffffff0fffffc03 0x1ffffffc3fffff00

def z350 : W := mkw 0x0000020024170d54 0x000000800905c355 0xed0c001f007f1ffd 0xfb430007c01fc7ff

def z351 : W := mkw 0x202001ba008002a8 0x0808006e802000aa 0xed0c01ff007c03fc 0xfb43007fc01f00ff

def z352 : W := mkw 0x5ffffeece3fffb31 0x57ffffbb38fffecc 0x7fffffece3ffff33 0xdffffffb38ffffcc

def z353 : W := mkw 0x23a801ba008002a8 0x08ea006e802000aa 0xebfc01ff000003fc 0xfaff007fc00000ff

def z354 : W := mkw 0x00042e0460170910 0x00010b811805c244 0x7d0c7e0ce07f1f31 0xdf431f83381fc7cc

def z355 : W := mkw 0xf7df7b131b7ed800 0x7df7dec4c6dfb600 0x77fffe131ffffc03 0x1dffff84c7ffff00

def z356 : W := mkw 0x57dffa40b77ffd40 0xd5f7fe902ddfff50 0x77fffe00fffffc03 0x1dffff803fffff00

def z357 : W := mkw 0x44dd3a00013e4800 0x51374e80004f9200 0x76ff9e0003bfe002 0x1dbfe78000eff800

def z358 : W := mkw 0x0400020020136111 0x010000800804d844 0x000000000003e002 0x000000000000f800

def z359 : W := mkw 0x000004056c010554 0x000001015b004155 0x00000000fc000000 0x000000003f000000

def z360 : W := mkw 0x53cf780002409000 0x14f3de0000902400 0x77fffe0003c3fc03 0x1dffff8000f0ff00

def z361 : W := mkw 0x03008170b6c127c0 0x80c0205c2db049f0 0x4f0001f0ffc003c0 0x93c0007c3ff000f0

def z362 : W := mkw 0x0010022027ff0ffc 0x0004008809ffc3ff 0x8400000003ff1ffd 0xe100000000ffc7ff

def z363 : W := mkw 0x0000040548000000 0x0000010152000000 0x0800001ffc000000 0x02000007ff000000

def z364 : W := mkw 0x0010000001280028 0x00040000004a000a 0x80000000003c003c 0x60000000000f000f

def z365 : W := mkw 0xe8ed3c8f48000000 0x3a3b4f23d2000000 0x79fc7e1ffc000000 0x1e7f1f87ff000000

def z366 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0x67fc01e003fc0000 0x19ff007800ff0000

def z367 : W := mkw 0x0302c170b0812300 0x00c0b05c2c2048c0 0x5f03e1f0ff83e302 0x97c0f87c3fe0f8c0

def z368 : W := mkw 0x5747fb70b6d7ffc0 0xd5d1fedc2db5fff0 0x5f03fff0ffc3ffc3 0x97c0fffc3ff0fff0

def z369 : W := mkw 0x0410020001324000 0x01040080004c9000 0x0400000003b3e002 0x0100000000ecf800

def z370 : W := mkw 0xe38a411210000000 0x38e2904484000000 0x0000000000000000 0x0000000000000000

def z371 : W := mkw 0xebfffdffdbe802a8 0x3affff7ff6fa00aa 0x7bffffffff800000 0x1effffffffe00000

def z372 : W := mkw 0x27b803ba23fb63b9 0x09ee00ee88fed8ee 0xeffc01ff03ffe3fe 0xfbff007fc0fff8ff

def z373 : W := mkw 0x43cff95090000000 0x10f3fe5424000000 0x7bfffff0fc000000 0x1efffffc3f000000

def z374 : W := mkw 0xe8ed3c8f48000000 0x3a3b4f23d2000000 0x20fc1e0f00000000 0x083f0783c0000000

def z375 : W := mkw 0x0000000024010540 0x0000000009004150 0xfd0c601ffc7f1ffd 0xff431807ff1fc7ff

def z376 : W := mkw 0x07d91200037a4000 0x01f6448000de9000 0x77ff9e0003ffe002 0x1dffe78000fff800

def z377 : W := mkw 0xf38e69131e4094c0 0xbce39a44c7902530 0x010c60131c401cc1 0x00431804c7100730

def z378 : W := mkw 0xe8fd3c8f49280028 0x3a3f4f23d24a000a 0xa0fc1e0f003c003c 0x683f0783c00f000f

def z379 : W := mkw 0x10000000064094c0 0x8400000001902530 0x0000000000401cc1 0x0000000000100730

def z380 : W := mkw 0x00008060a0812300 0x00002018282048c0 0x080001e0e0000300 0x82000078380000c0

def z381 : W := mkw 0xebeffdfffc8127c0 0xbafbff7fff2049f0 0x7bfffffffc0003c0 0x9effffffff0000f0

def z382 : W := mkw 0xecfdbeefe9b36331 0x3b3f6fbbfa6cd8cc 0x7eff9fefe3b3e332 0xdfbfe7fbf8ecf8cc

def z383 : W := mkw 0x1302c150b401b540 0x84c0b0542d006d50 0x5b03e1f0fc03fc03 0x16c0f87c3f00ff00

def z384 : W := mkw 0x43cf7e056c170d54 0x10f3df815b05c355 0xfffffe1ffc7f1ffd 0xffffff87ff1fc7ff

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0x59006010fc000000 0x164018043f000000

def z386 : W := mkw 0x0c71168c61334131 0x031c45a3184cd04c 0x7cf01e0ce0330330 0xdf3c0783380cc0cc

def z387 : W := mkw 0x438e680000000000 0x10e39a0000000000 0x010c600000000000 0x0043180000000000

def z388 : W := mkw 0x53cf7800024c9800 0x54f3de0000932600 0x73fffe00004c1c01 0x1cffff8000130700

def z389 : W := mkw 0x23b805bf6fe907fc 0x08ee016fdbfa41ff 0xeffc01fffffc03fc 0xfbff007fffff00ff

def z390 : W := mkw 0x282085fee08123b9 0x0a08217fb82048ee 0x880001ffe00003fc 0xe200007ff80000ff

def z391 : W := mkw 0x0388000002480000 0x00e2000000920000 0x010c0000004c0000 0x0043000000130000

def z392 : W := mkw 0x338a4112164894c8 0x8ce2904485922532 0x810c60131c4c1ccd 0x20431804c7130733

def z393 : W := mkw 0x1f77fffdfff7fff5 0x87ddffff7ffdfffd 0xffffffffffffffff 0xffffffffffffffff

def z394 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00c000f003c003c 0x68030003c00f000f

def z395 : W := mkw 0x003006ac61b30330 0x000c01ab186cc0cc 0x7ef01fece3b30330 0xdfbc07fb38ecc0cc

def z396 : W := mkw 0x0398000003680000 0x00e6000000da0000 0x02f0000003800000 0x00bc000000e00000

def z397 : W := mkw 0x0861148c40000000 0x0218452310000000 0x20f01e0c00000000 0x083c078300000000

def z398 : W := mkw 0xe38e6f177c170d54 0x38e39bc5df05c355 0xfd0c7e1ffc7f1ffd 0xff431f87ff1fc7ff

def z399 : W := mkw 0x54df7a00013ed800 0x5537de80004fb600 0x30fffe00003ffc03 0x0c3fff80000fff00

def z400 : W := mkw 0x139ac170b7e9b7c0 0x84e6b05c2dfa6df0 0x7fffe1f0ffffffc3 0x9ffff87c3ffffff0

def z401 : W := mkw 0x0410062461b36331 0x01040189186cd8cc 0x7c001e0ce3b3e332 0xdf00078338ecf8cc

def z402 : W := mkw 0xfffffffffff3f7f1 0xbffffffffffcfdfc 0x7ffffffffff3fff3 0xdffffffffffcfffc

def z403 : W := mkw 0x1302c150b641b5c0 0x84c0b0542d906d70 0x1103e010fc43fcc3 0x0440f8043f10ff30

def z404 : W := mkw 0x0f73d7fcf1b36331 0x03dcf5ff3c6cd8cc 0x7ff3fffcffb3e332 0xdffcffff3fecf8cc

def z405 : W := mkw 0x738e6912024c9888 0x5ce39a4480932622 0x810c6013004c1ccd 0x20431804c0130733

def z406 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0xa80c1e1ffc3c03fc 0xea030787ff0f00ff

def z407 : W := mkw 0x0302400000000000 0x00c0900000000000 0x5303e00000000000 0x14c0f80000000000

def z408 : W := mkw 0x40cd380000000000 0x10334e0000000000 0x20fc1e0000000000 0x083f078000000000

def z409 : W := mkw 0xebfffddfdb680000 0x3affff77f6da0000 0x7ffffffffffc0000 0x1fffffffffff0000

def z410 : W := mkw 0x7ffffffee3fffbb9 0x5fffffffb8fffeee 0xffffffffe3ffffff 0xfffffffff8ffffff

def z411 : W := mkw 0x000006056c130554 0x000001815b04c155 0xfc001e1ffc3303fc 0xff000787ff0cc0ff

def z412 : W := mkw 0x043002a821b36331 0x010c00aa086cd8cc 0x6ef001ec03b3e332 0xdbbc007b00ecf8cc

def z413 : W := mkw 0x0000000004000440 0x0000000001000110 0x010060101c401cc1 0x0040180407100730

def z414 : W := mkw 0x0300013002c00280 0x00c0004c00b000a0 0x020001e003800000 0x0080007800e00000

def z415 : W := mkw 0x00042e0548160814 0x00010b8152058205 0xf50c7e0f007f1c3d 0x7d431f83c01fc70f

def z416 : W := mkw 0x1302400002409000 0x04c0900000902400 0x020380000380e002 0x0080e00000e03800

def z417 : W := mkw 0x23ac2f9f6c170d54 0x08eb0be7db05c355 0xfffc7ffffc7f1ffd 0xffff1fffff1fc7ff

def z418 : W := mkw 0x1312c170b7e9b7e8 0x84c4b05c2dfa6dfa 0xdf03e1f0ffffffff 0xf7c0f87c3fffffff

def z419 : W := mkw 0xebeffddfda480088 0x3afbff77f6920022 0xfbfffffffc4c00cc 0x3effffffff130033

def z420 : W := mkw 0x5ffffeccc37ed800 0x57ffffb330dfb600 0x7fffffece3fffc03 0x1ffffffb38ffff00

def z421 : W := mkw 0x047112a801b24220 0x011c44aa006c9088 0x7ef39fec03b3e332 0xdfbce7fb00ecf8cc

def z422 : W := mkw 0x57db50000368d000 0x55f6d40000da3400 0x57f3e00003c3fc03 0x15fcf80000f0ff00

def z423 : W := mkw 0x1306ef75fed7bfd4 0x84c1bbdd7fb5eff5 0x5f03fff0ffc3ffc3 0x97c0fffc3ff0fff0

def z424 : W := mkw 0x0c7192e881b26221 0x031c64ba206c9888 0x76f39fe003b3e002 0x1dbce7f800ecf800

def z425 : W := mkw 0x039c2e056f7f0d54 0x00e70b815bdfc355 0xfffc7e1fffff1ffd 0xffff1f87ffffc7ff

def z426 : W := mkw 0x0004280108000000 0x00010a0042000000 0x010c60131c000000 0x00431804c7000000

def z427 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0x7c007e0cfc331f31 0xdf001f833f0cc7cc

def z428 : W := mkw 0x1002400000009000 0x0400900000002400 0x1003e0000003fc03 0x0400f8000000ff00

def z429 : W := mkw 0xfbeffddfda409000 0x3efbff77f6902400 0x7fffffffffc3fc03 0x1ffffffffff0ff00

def z430 : W := mkw 0x0306ed55d8000000 0x00c1bb5576000000 0x7b0ffffffc000000 0x1ec3ffffff000000

def z431 : W := mkw 0xc847fc45d8000000 0x3211ff1176000000 0x790ffe1ffc000000 0x1e43ff87ff000000

def z432 : W := mkw 0xebeffdffdac00280 0x3afbff7ff6b000a0 0x7fffffffffc003c0 0x9ffffffffff000f0

def z433 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x0a0381f0ff80e3c2 0x8280e07c3fe038f0

def z434 : W := mkw 0x1302c060a2c1b300 0x04c0b01828b06cc0 0x5f03e1e0e3c3ff03 0x97c0f87838f0ffc0

def z435 : W := mkw 0x20a8008a00000000 0x082a002280000000 0x20fc000f00000000 0x083f0003c0000000

def z436 : W := mkw 0x082080e880802221 0x0208203a20200888 0x000001e000000000 0x0000007800000000

def z437 : W := mkw 0x57df7b3003feda80 0x55f7decc00ffb6a0 0x7ffffff003ffffc3 0x9ffffffc00fffff0

def z438 : W := mkw 0x1010002027e9b7e8 0x8404000809fa6dfa 0x8400000003ffffff 0xe100000000ffffff

def z439 : W := mkw 0xecfd3e8f493e4800 0x7b3f4fa3d24f9200 0x20fc1e0f003c0000 0x083f0783c00f0000

def z440 : W := mkw 0x0c7194ece1a16331 0x031c653b386858cc 0x0af381ece380e332 0xc2bce07b38e038cc

def z441 : W := mkw 0x0300011002400080 0x00c0004400900020 0x01000010004000c0 0x0040000400100030

def z442 : W := mkw 0x1002c170b481b7c0 0x8400b05c2d206df0 0x1803e1f0fc03ffc3 0x8600f87c3f00fff0

def z443 : W := mkw 0xfffbd1da9368d000 0x7ffef476a4da3400 0x02f381e00380e002 0x00bce07800e03800

def z444 : W := mkw 0x03042f356ed70fd4 0x00c10bcd5bb5c3f5 0xff0c7fffffff1ffd 0xffc31fffffffc7ff

def z445 : W := mkw 0x00042a0024170d40 0x00010a800905c350 0x7d0c7e10fc7f1fc1 0x9f431f843f1fc7f0

def z446 : W := mkw 0x0000040460010110 0x0000010118004044 0x0800000ce0000330 0xc2000003380000cc

def z447 : W := mkw 0x2388013202c80288 0x08e2004c80b200a2 0xcf0c01f303cc03cc 0xb3c3007cc0f300f3

def z448 : W := mkw 0xa86195dfd8000000 0x2a186577f6000000 0x7af39ffffc000000 0x1ebce7ffff000000

def z449 : W := mkw 0x20b800aa03e802a8 0x082e002a80fa00aa 0xa4fc000f03fc03fc 0xe93f0003c0ff00ff

def z450 : W := mkw 0x000004056c010554 0x000001015b004155 0xed0c001ffc7c03fc 0xfb430007ff1f00ff

def z451 : W := mkw 0x0398002003e802a8 0x00e6000800fa00aa 0xe7fc000003fc03fc 0xf9ff000000ff00ff

def z452 : W := mkw 0x33beefffffffbffc 0x8cefbbffffffefff 0xffffffffffffffff 0xffffffffffffffff

def z453 : W := mkw 0x33ba41ba03e892a8 0x0cee906e80fa24aa 0xffffe1ff03ffffff 0xfffff87fc0ffffff

def z454 : W := mkw 0x44dd3e056d3f4d54 0x51374f815b4fd355 0xfdfc7e1ffc7f1ffd 0xff7f1f87ff1fc7ff

def z455 : W := mkw 0xdfdffe45db7ed800 0x77f7ff9176dfb600 0x77fffe00fffffc03 0x1dffff803fffff00

def z456 : W := mkw 0x579e6a00037ed800 0x55e79a8000dfb600 0x050c600003fffc03 0x0143180000ffff00

def z457 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0x98007e1ffc031ffd 0xe6001f87ff00c7ff

def z458 : W := mkw 0xfbeffffffed7bfd4 0xbefbffffffb5eff5 0xffffffffffffffff 0xffffffffffffffff

def z459 : W := mkw 0xebeffddffc010554 0x3afbff77ff004155 0xfbfffffffc0003fc 0xfeffffffff0000ff

def z460 : W := mkw 0x0c75beede9b36331 0x031d6fbb7a6cd8cc 0x7fffffffffb3e332 0xdfffffffffecf8cc

def z461 : W := mkw 0x2020008a00000028 0x080800228000000a 0x8000000f0000003c 0x60000003c000000f

def z462 : W := mkw 0x67fd3bba03fe4aa8 0x59ff4eee80ff92aa 0xeffc1fff03fc03fc 0xfbff07ffc0ff00ff

def z463 : W := mkw 0xeffffdffd9a06221 0x3bffff7ff6681888 0x7bffffffff80e002 0x1effffffffe03800

def z464 : W := mkw 0xebebd1da90000000 0x3afaf476a4000000 0x5bf3e1f0fc000000 0x16fcf87c3f000000

def z465 : W := mkw 0x4cfdbeece1bf6b31 0x533f6fbb386fdacc 0x7eff9fece3bfe332 0xdfbfe7fb38eff8cc

def z466 : W := mkw 0x00042a0000160800 0x00010a8000058200 0x200c1e00003c0000 0x08030780000f0000

def z467 : W := mkw 0x0f7197fce3f363b1 0x03dc65ff38fcd8ec 0x7ff39ffce3f3e3f2 0xdffce7ff38fcf8fc

def z468 : W := mkw 0xabb885ffdbe802a8 0x2aee217ff6fa00aa 0xeffc01fffffc03fc 0xfbff007fffff00ff

def z469 : W := mkw 0x0000020000120000 0x0000008000048000 0x74001e0000330000 0x1d000780000cc000

def z470 : W := mkw 0xa82085dffc010554 0x2a082177ff004155 0x880001fffc0003fc 0xe200007fff0000ff

def z471 : W := mkw 0x00008170b48127c0 0x8000205c2d2049f0 0x5e0381f0ff83e3c2 0x9780e07c3fe0f8f0

def z472 : W := mkw 0xfbebd1fa92c0b280 0xbefaf47ea4b02ca0 0x02f381e00380e002 0x00bce07800e03800

def z473 : W := mkw 0x0451122021b36331 0x01144488086cd8cc 0x76f39e0003b3e332 0xddbce78000ecf8cc

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0x690c001f00000000 0x1a430007c0000000

def z475 : W := mkw 0x082084ece0812331 0x0208213b382048cc 0x5e0381ece383e332 0xd780e07b38e0f8cc

def z476 : W := mkw 0x54dd3a00037ed800 0x55374e8000dfb600 0x24fc1e0003fffc03 0x093f078000ffff00

def z477 : W := mkw 0x77ff7b9a037ed800 0x5dffdee680dfb600 0x7fffffff03fffc03 0x1fffffffc0ffff00

def z478 : W := mkw 0x23b881faa3e923a8 0x08ee207ea8fa48ea 0xffff81ffe3ffe3fe 0xffffe07ff8fff8ff

def z479 : W := mkw 0xe8edbccfc8000000 0x3a3b6f33f2000000 0x7aff9fefe0000000 0x1ebfe7fbf8000000

def z480 : W := mkw 0x203001ba01a002a8 0x080c006e806800aa 0xeef001ff03b003fc 0xfbbc007fc0ec00ff

def z481 : W := mkw 0x57df7a00277fdd54 0x55f7de8009dff755 0xf7fffe0003ffffff 0xfdffff8000ffffff

def z482 : W := mkw 0x2ff917be43fa42b9 0x0bfe45ef90fe90ae 0xeffc1fff03fc03fc 0xfbff07ffc0ff00ff

def z483 : W := mkw 0x20242fbf6c970ffc 0x08090befdb25c3ff 0xfd0c7ffffc7f1ffd 0xff431fffff1fc7ff

def z484 : W := mkw 0x44dd3e05493e4814 0x51374f81524f9205 0xa0fc1e0f003c003c 0x683f0783c00f000f

def z485 : W := mkw 0xeffbd7fef1b36331 0x3bfef5ffbc6cd8cc 0x7ef39fece3b3e332 0xdfbce7fb38ecf8cc

def z486 : W := mkw 0xefffffdfd9324031 0x3bfffff7f64c900c 0x7bfffffffc300030 0x5effffffff0c000c

def z487 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0x94007e00fc7f1ffd 0xe5001f803f1fc7ff

def z488 : W := mkw 0x1302c774f6d3b7d0 0x84c0b1dd3db4edf4 0x7f03fffcfff3fff3 0xdfc0ffff3ffcfffc

def z489 : W := mkw 0x00042c056c050d54 0x00010b015b014355 0x890c601ffc4c1ffd 0xe2431807ff1307ff

def z490 : W := mkw 0x0000002020812331 0x00000008082048cc 0x0000000000000330 0xc0000000000000cc

def z491 : W := mkw 0x57477a000256d800 0x55d1de800095b600 0x5703fe0003c3fc03 0x15c0ff8000f0ff00

def z492 : W := mkw 0x20bc2e8f493e083c 0x082f0ba3d24f820f 0xa0fc1e0f003c003c 0x683f0783c00f000f

def z493 : W := mkw 0x1306eb70b6d7bfc0 0x84c1badc2db5eff0 0x7f0ffff0ffffffc3 0x9fc3fffc3ffffff0

def z494 : W := mkw 0x0010002001a00220 0x0004000800680088 0x0400000003b00330 0xc100000000ec00cc

def z495 : W := mkw 0x14142e056f7fdd54 0x45050b815bdff755 0xfd0c7e1fffffffff 0xff431f87ffffffff

def z496 : W := mkw 0x57ff7aa803feda20 0x55ffdeaa00ffb688 0x7fffffec03ffff33 0xdffffffb00ffffcc

def z497 : W := mkw 0x0c7116ac61b36331 0x031c45ab186cd8cc 0x24f01e0c03b3e332 0xc93c078300ecf8cc

def z498 : W := mkw 0x10000000024c9800 0x4400000000932600 0x00000000004c1c01 0x0000000000130700

def z499 : W := mkw 0x0000000000000000 0x0000000000000000 0x650c0000007c0000 0x19430000001f0000

def z500 : W := mkw 0xe38ee95398000000 0x38e3ba54e6000000 0x5b0fe1f3fc000000 0x16c3f87cff000000

def z501 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0xa2fc01ef03bc003c 0x68bf007bc0ef000f

def z502 : W := mkw 0xe8e9108a00000000 0x3a3a442280000000 0x00f0000000000000 0x003c000000000000

def z503 : W := mkw 0x00042a0000160800 0x00010a8000058200 0x10007e0000031c01 0x04001f800000c700

def z504 : W := mkw 0xebaeeddfd8000000 0x3aebbb77f6000000 0x090c61fffc000000 0x0243187fff000000

def z505 : W := mkw 0x00042a010c160c44 0x00010a8043058311 0xf50c7e131c7f1ccd 0x3d431f84c71fc733

def z506 : W := mkw 0x00000020008002a8 0x00000008002000aa 0x80000000000003fc 0xe0000000000000ff

def z507 : W := mkw 0x0c7196ccc1324000 0x031c65b3304c9000 0x7ef39fece3b3e002 0x1fbce7fb38ecf800

def z508 : W := mkw 0x0000040548000014 0x0000010152000005 0x8000000f0000003c 0x60000003c000000f

def z509 : W := mkw 0xebefffdffc170d54 0x3afbfff7ff05c355 0x7bfffffffc031c01 0x1effffffff00c700

def z510 : W := mkw 0x23b8008a03680028 0x08ee002280da000a 0xe7fc000f03fc003c 0x79ff0003c0ff000f

def z511 : W := mkw 0x4047780000000000 0x1011de0000000000 0x1003fe0000000000 0x0400ff8000000000

def z512 : W := mkw 0x0c7116ac41b24231 0x031c45ab106c908c 0x6ef01fec03b00330 0xdbbc07fb00ec00cc

def z513 : W := mkw 0x1712c370b7ffffc0 0xc5c4b0dc2dfffff0 0x5f03e1f0ffffffc3 0x97c0f87c3ffffff0

def z514 : W := mkw 0x1002c040b401b540 0x8400b0102d006d50 0x5d03e010fc43ffc3 0x9740f8043f10fff0

def z515 : W := mkw 0x0310013003e802a8 0x00c4004c00fa00aa 0xcf0001f003fc03fc 0xf3c0007c00ff00ff

def z516 : W := mkw 0xa82085fffc8127c0 0xaa08217fff2049f0 0x080001fffc0003c0 0x8200007fff0000f0

def z517 : W := mkw 0x002000a800800220 0x0008002a00200088 0x080001ec00000330 0xc200007b000000cc

def z518 : W := mkw 0xffffffffffffffc0 0xfffffffffffffff0 0x7fffffffffffffc3 0x9ffffffffffffff0

def z519 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0x83fc01f303cc00cc 0x20ff007cc0f30033

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0x810c0013004c00cc 0x20430004c0130033

def z521 : W := mkw 0x00008575fc8127d4 0x8000215d7f2049f5 0x880001fffc0003fc 0xe200007fff0000ff

def z522 : W := mkw 0x77ff7bba03fedaa8 0x5dffdeee80ffb6aa 0x77ffffe003fffc03 0x1dfffff800ffff00

def z523 : W := mkw 0x23b801ba01a00220 0x08ee006e80680088 0x6ffc01ff03b00330 0xdbff007fc0ec00cc

def z524 : W := mkw 0x0000060464170d54 0x000001811905c355 0xfc001e0ce07f1ffd 0xff000783381fc7ff

def z525 : W := mkw 0x77fb51ba03e8d2a8 0x5dfed46e80fa34aa 0x02f381e00380e002 0x00bce07800e03800

def z526 : W := mkw 0x1000022026d7bfd4 0x8400008809b5eff5 0x8400000003ffffff 0xe100000000ffffff

def z527 : W := mkw 0x0041100000000000 0x0010440000000000 0x72f39e0000000000 0x1cbce78000000000

def z528 : W := mkw 0x140002000016d800 0x450000800005b600 0x000000000003fc03 0x000000000000ff00

def z529 : W := mkw 0xefefffdff8136111 0x3bfbfff7fe04d844 0x7bfffffffc03e002 0x1effffffff00f800

def z530 : W := mkw 0x77fffbfab7ffffe8 0xddfffefeadfffffa 0xffffffffffffffff 0xffffffffffffffff

def z531 : W := mkw 0x130669111e449cc4 0x84c19a4447912731 0x810c60131c4c1ccd 0x20431804c7130733

def z532 : W := mkw 0x1000002002c0b280 0x8400000800b02ca0 0x000000000380e002 0x0000000000e03800

def z533 : W := mkw 0x0000000024010540 0x0000000009004150 0x08000010fc0003c0 0x820000043f0000f0

def z534 : W := mkw 0x57df7e056f7fdd54 0x55f7df815bdff755 0x77fffe00fffffc03 0x1dffff803fffff00

def z535 : W := mkw 0x00042e0568170914 0x00010b815a05c245 0xfc0c1e0fe03f033c 0xff030783f80fc0cf

def z536 : W := mkw 0xebcffd57d8000000 0x3af3ff55f6000000 0x110ffe13fc000000 0x0443ff84ff000000

def z537 : W := mkw 0x0398013003e80280 0x00e6004c00fa00a0 0x6ffc01f003fc03c0 0x9bff007c00ff00f0

def z538 : W := mkw 0x20b8008a01280028 0x082e0022804a000a 0x00f0000000000000 0x003c000000000000

def z539 : W := mkw 0xebefffdfd8160814 0x3afbfff7f6058205 0xfbfffffffc3c003c 0x7effffffff0f000f

def z540 : W := mkw 0x1302c17092c0b280 0x84c0b05c24b02ca0 0x4f0381f003c0e3c2 0x93c0e07c00f038f0

def z541 : W := mkw 0x100000002401b540 0x8400000009006d50 0x000000000003fc03 0x000000000000ff00

def z542 : W := mkw 0x57cf7a00025ed800 0x55f3de800097b600 0x110ffe00004ffc03 0x0443ff800013ff00

def z543 : W := mkw 0x0004280000040800 0x00010a0000010200 0x010c6000004c1c01 0x0043180000130700

def z544 : W := mkw 0x33ba41ba17e896e8 0x8cee906e85fa25ba 0xeffc61ff1ffc1ffd 0xfbff187fc7ff07ff

def z545 : W := mkw 0xfbeffddfde4094c0 0xbefbff77f7902530 0x7bfffffffc401cc1 0x1effffffff100730

def z546 : W := mkw 0x23a8019a02480088 0x08ea006680920022 0xebfc01ff004c00cc 0x3aff007fc0130033

def z547 : W := mkw 0xfbeffddffc01b540 0xbefbff77ff006d50 0x7bfffffffc03fc03 0x1effffffff00ff00

def z548 : W := mkw 0x0098000001280000 0x00260000004a0000 0x20fc0000003c0000 0x083f0000000f0000

def z549 : W := mkw 0x47df7a00013e4800 0x51f7de80004f9200 0x73fffe00003c0000 0x1cffff80000f0000

def z550 : W := mkw 0x1c7196ece3fffb31 0x471c65bb38fffecc 0x7ef39fece3ffff33 0xdfbce7fb38ffffcc

def z551 : W := mkw 0xe8ed3e8f48160814 0x3a3b4fa3d2058205 0xa0fc1e0f003c003c 0x683f0783c00f000f

def z552 : W := mkw 0xe8effccfd8000000 0x3a3bff33f6000000 0x30fffe0ffc000000 0x0c3fff83ff000000

def z553 : W := mkw 0xebed3d9f48000000 0x3afb4f67d2000000 0x6bfc1fff00000000 0x1aff07ffc0000000

def z554 : W := mkw 0xac7197fff9b36331 0x2b1c65fffe6cd8cc 0x7ef39fffffb3e332 0xdfbce7ffffecf8cc

def z555 : W := mkw 0x5fff7e8c437ed831 0x57ffdfa310dfb60c 0x77fffe0c03fffc33 0x5dffff8300ffff0c

def z556 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0x5d007e10fc431fc1 0x97401f843f10c7f0

def z557 : W := mkw 0x0c75beededb76f75 0x031d6fbb7b6ddbdd 0x7ef3ffecffb3ff33 0xdfbcfffb3fecffcc

def z558 : W := mkw 0x2bb885fee3e923b9 0x0aee217fb8fa48ee 0xeffc01ffe3fc03fc 0xfbff007ff8ff00ff

def z559 : W := mkw 0x039c2a00037e0800 0x00e70a8000df8200 0x77fc7e0003ff1c01 0x1dff1f8000ffc700

def z560 : W := mkw 0x0010002003e802a8 0x0004000800fa00aa 0x0000000003800000 0x0000000000e00000

def z561 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x28f01fece0300330 0xca3c07fb380c00cc

def z562 : W := mkw 0x00008170b48127c0 0x8000205c2d2049f0 0x5d0061f0fc431fc1 0x9740187c3f10c7f0

def z563 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0xa40c1e0f007f1ffd 0xe9030783c01fc7ff

def z564 : W := mkw 0xc843d04090000000 0x3210f41024000000 0x0003800000000000 0x0000e00000000000

def z565 : W := mkw 0x0410020001324031 0x01040080004c900c 0x0000000000300030 0x40000000000c000c

def z566 : W := mkw 0x1332c1f8b7e1b7e0 0x84ccb07e2df86df8 0x7ff3e1fcfff3fff3 0xdffcf87f3ffcfffc

def z567 : W := mkw 0x4cfd3e8c413e4831 0x533f4fa3104f920c 0x20fc1e0c003c0030 0x483f0783000f000c

def z568 : W := mkw 0x2bf995fec3e802a8 0x0afe657fb0fa00aa 0xffff9fffe3fc03fc 0xffffe7fff8ff00ff

def z569 : W := mkw 0x57df7e04637fd910 0x55f7df8118dff644 0x7ffffe0ce3ffff33 0xdfffff8338ffffcc

def z570 : W := mkw 0xfbeffdffdac0b280 0xbefbff7ff6b02ca0 0x7bffffffff80e002 0x1effffffffe03800

def z571 : W := mkw 0x4beffcccc0000000 0x12fbff3330000000 0x7bffffece0000000 0x1efffffb38000000

def z572 : W := mkw 0x88008445d8000000 0x2200211176000000 0x00000000fc000000 0x000000003f000000

def z573 : W := mkw 0x00042e0548160814 0x00010b8152058205 0x00001e0000000000 0x0000078000000000

def z574 : W := mkw 0x57df7e054b7ed814 0x55f7df8152dfb605 0xf7fffe0f03fffc3f 0x7dffff83c0ffff0f

def z575 : W := mkw 0x083084ece1a12331 0x020c213b386848cc 0x6ef001ece3b00330 0xdbbc007b38ec00cc

def z576 : W := mkw 0x1006ee45fc17bd54 0x8401bb917f05ef55 0xfd0ffe1ffc7fffff 0xff43ff87ff1fffff

def z577 : W := mkw 0x1302411012409080 0x84c0904404902420 0x0000000000000000 0x0000000000000000

def z578 : W := mkw 0x0000817090802280 0x8000205c242008a0 0x000001e000000000 0x0000007800000000

def z579 : W := mkw 0x1302413016c096c0 0x84c0904c05b025b0 0x4f0061f01fc01fc1 0x93c0187c07f007f0

def z580 : W := mkw 0x17980200037ed800 0x45e6008000dfb600 0x67fc000003fffc03 0x19ff000000ffff00

def z581 : W := mkw 0x2ff997fee3fb63b9 0x0bfe65ffb8fed8ee 0x7ef39fece3b3e332 0xdfbce7fb38ecf8cc

def z582 : W := mkw 0x2000011200000088 0x0800004480000022 0x80000013000000cc 0x20000004c0000033

def z583 : W := mkw 0xcbcffc45d8000000 0x32f3ff1176000000 0x73fffe00fc000000 0x1cffff803f000000

def z584 : W := mkw 0x082086ece0932331 0x020821bb3824c8cc 0x7c001fece0330330 0xdf0007fb380cc0cc

def z585 : W := mkw 0x00142e256fff0ffc 0x00050b895bffc3ff 0xfd0c7e1fffff1ffd 0xff431f87ffffc7ff

def z586 : W := mkw 0xebfbd1fa93e802a8 0x3afef47ea4fa00aa 0xefff81ff03fc03fc 0xfbffe07fc0ff00ff

def z587 : W := mkw 0x00042a0000160800 0x00010a8000058200 0xfd0c7e1f007f1ffd 0xff431f87c01fc7ff

def z588 : W := mkw 0xc847fe45fc170d54 0x3211ff917f05c355 0xfd0ffe1ffc7f1ffd 0xff43ff87ff1fc7ff

def z589 : W := mkw 0xdb47fd75fec1b7c0 0xb6d1ff5d7fb06df0 0x5f03fff0ffc3ffc3 0x97c0fffc3ff0fff0

def z590 : W := mkw 0xffffffdfff7fdd54 0x7ffffff7ffdff755 0xffffffffffffffff 0xffffffffffffffff

def z591 : W := mkw 0xfbebd1fab6c1b7c0 0xbefaf47eadb06df0 0x5ff3e1f0ffc3ffc3 0x97fcf87c3ff0fff0

def z592 : W := mkw 0x5006680000049800 0x54019a0000012600 0x0000600000001c01 0x0000180000000700

def z593 : W := mkw 0x47df7a0001324000 0x11f7de80004c9000 0x77fffe0003b3e002 0x1dffff8000ecf800

def z594 : W := mkw 0x23a801ba02c00280 0x08ea006e80b000a0 0x6ffc01ff03c003c0 0x9bff007fc0f000f0

def z595 : W := mkw 0x000000010c000444 0x0000000043000111 0x800000131c0000cc 0x20000004c7000033

def z596 : W := mkw 0x0000804080000000 0x0000201020000000 0x5a0381e0e0000000 0x1680e07838000000

def z597 : W := mkw 0x0302411010000000 0x00c0904404000000 0x010060101c000000 0x0040180407000000

def z598 : W := mkw 0x00008664e0932310 0x000021993824c8c4 0x7e039fece3b3e332 0xdf80e7fb38ecf8cc

def z599 : W := mkw 0xe3ae699b18000000 0x38eb9a66c6000000 0x6bfc61ff1c000000 0x1aff187fc7000000

def z600 : W := mkw 0x2c7197fee1b363b9 0x0b1c65ffb86cd8ee 0xfef39fffe3b3e3fe 0xffbce7fff8ecf8ff

def z601 : W := mkw 0x5c77feece1b7fb31 0x571dffbb386dfecc 0x7ef3ffece3b3ff33 0xdfbcfffb38ecffcc

def z602 : W := mkw 0x00042c0548000000 0x00010b0152000000 0x10007e00fc000000 0x04001f803f000000

def z603 : W := mkw 0x202081fab48127e8 0x8808207ead2049fa 0x880001fffc0003fc 0xe200007fff0000ff

def z604 : W := mkw 0x0004af75fc972fd4 0x80012bdd7f25cbf5 0xfd0c7ffffc7f1ffd 0xff431fffff1fc7ff

def z605 : W := mkw 0xefffffdfd93e4800 0x7bfffff7f64f9200 0x7bfffffffc3c0000 0x1effffffff0f0000

def z606 : W := mkw 0x63ef799a00000000 0x18fbde6680000000 0x7bffffff00000000 0x1effffffc0000000

def z607 : W := mkw 0x0451100001204000 0x0114440000481000 0x02f380000380e002 0x00bce00000e03800

def z608 : W := mkw 0xcb47fd55d8000000 0x32d1ff5576000000 0x5b03fff0fc000000 0x16c0fffc3f000000

def z609 : W := mkw 0x57df7a2027ffffc0 0xd5f7de8809fffff0 0x77fffe0003ffffc3 0x9dffff8000fffff0

def z610 : W := mkw 0x1000002026c1b7c0 0x8400000809b06df0 0x5d006010ffc3ffc3 0x974018043ff0fff0

def z611 : W := mkw 0x0000000000000000 0x0000000000000000 0x560380000383e002 0x1580e00000e0f800

def z612 : W := mkw 0x000428010c040c44 0x00010a0043010311 0x000060001c001c01 0x0000180007000700

def z613 : W := mkw 0x0441120000124000 0x0110448000049000 0x10039e000003e002 0x0400e7800000f800

def z614 : W := mkw 0xa000011318000000 0x28000044c6000000 0x000000131c000000 0x00000004c7000000

def z615 : W := mkw 0x47dd3a00037e4800 0x51f74e8000df9200 0x67fc1e0003fc0000 0x19ff078000ff0000

def z616 : W := mkw 0x232001ba02c002a8 0x08c8006e80b000aa 0xcf0001ff03c003fc 0xf3c0007fc0f000ff

def z617 : W := mkw 0xffefffdfd816d800 0x7ffbfff7f605b600 0x7bfffffffc03fc03 0x1effffffff00ff00

def z618 : W := mkw 0x202005bf6c8107fc 0x0808016fdb2041ff 0x880001fffc0003fc 0xe200007fff0000ff

def z619 : W := mkw 0x0c41160440124011 0x0310458110049004 0x00001e0000000000 0x0000078000000000

def z620 : W := mkw 0xe3cf791318000000 0x38f3de44c6000000 0x73fffe131c000000 0x1cffff84c7000000

def z621 : W := mkw 0x2388011202480088 0x08e2004480920022 0x0000000000000000 0x0000000000000000

def z622 : W := mkw 0x0c7190e8a1a16321 0x031c643a286858c8 0x5ef381e0e383e302 0x97bce07838e0f8c0

def z623 : W := mkw 0x1306ed75fec1b7c0 0x84c1bb5d7fb06df0 0x7f0fffffffc3ffc3 0x9fc3fffffff0fff0

def z624 : W := mkw 0xebef7d9f58000000 0x3afbdf67d6000000 0x21fc7e1f1c000000 0x087f1f87c7000000

def z625 : W := mkw 0x04553e056d374d54 0x01154f815b4dd355 0xfffffe1fffffffff 0xffffff87ffffffff

def z626 : W := mkw 0x1753d370b7f3f7c0 0x85d4f4dc2dfcfdf0 0x7ff3fff0fff3ffc3 0x9ffcfffc3ffcfff0

def z627 : W := mkw 0xbb22c5fffec1b7c0 0xaec8b17fffb06df0 0x5f03e1ffffc3ffc3 0x97c0f87ffff0fff0

def z628 : W := mkw 0x1006ee45fc17bd54 0x8401bb917f05ef55 0x1003fe00fc03fc03 0x0400ff803f00ff00

def z629 : W := mkw 0x0000000002480088 0x0000000000920022 0x80000000004c00cc 0x2000000000130033

def z630 : W := mkw 0x23b8019a01280028 0x08ee0066804a000a 0xebfc01ff003c003c 0x7aff007fc00f000f

def z631 : W := mkw 0x1302402026c1b7c0 0x84c0900809b06df0 0x5703e00003c3ffc3 0x95c0f80000f0fff0

def z632 : W := mkw 0x544350000000d000 0x5510d40000003400 0x000380000000e002 0x0000e00000003800

def z633 : W := mkw 0x2398011203680088 0x08e6004480da0022 0xe7fc001303fc00cc 0x39ff0004c0ff0033

def z634 : W := mkw 0x0302c170b48127c0 0x80c0b05c2d2049f0 0x5b03e1f0fc0003c0 0x96c0f87c3f0000f0

def z635 : W := mkw 0x2388011200000000 0x08e2004480000000 0x010c001300000000 0x00430004c0000000

def z636 : W := mkw 0x2ff991fa83e862a9 0x0bfe647ea0fa18aa 0x02f381e00380e002 0x00bce07800e03800

def z637 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x090061f0fc401fc1 0x8240187c3f1007f0

def z638 : W := mkw 0x0000040440000000 0x0000010110000000 0x78001e0ce0000000 0x1e00078338000000

def z639 : W := mkw 0x0388000000000000 0x00e2000000000000 0x63fc000000000000 0x18ff000000000000

def z640 : W := mkw 0xab22c5dfd8000000 0x2ac8b177f6000000 0x5b03e1fffc000000 0x16c0f87fff000000

def z641 : W := mkw 0x2398013203e802a8 0x08e6004c80fa00aa 0x850c001303fc03fc 0xe1430004c0ff00ff

def z642 : W := mkw 0x10008060a6c1b7c0 0x8400201829b06df0 0x5e0381e0e3c3ffc3 0x9780e07838f0fff0

def z643 : W := mkw 0x000004056c010554 0x000001015b004155 0xdd00601ffc431ffd 0xf7401807ff10c7ff

def z644 : W := mkw 0x0010000003680000 0x0004000000da0000 0x0400000003fc0000 0x0100000000ff0000

def z645 : W := mkw 0x13066e056e579d54 0x04c19b815b95e755 0xff0ffe1fffffffff 0xffc3ff87ffffffff

def z646 : W := mkw 0x23b807be63fb03b8 0x08ee01ef98fec0ee 0xfffc1fffe3ff03fc 0xffff07fff8ffc0ff

def z647 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x21fc7e00007c1c01 0x087f1f80001f0700

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x6c00000c00300330 0xdb000003000c00cc

def z649 : W := mkw 0x57df7a00277fdd40 0x55f7de8009dff750 0x7ffffe10ffffffc3 0x9fffff843ffffff0

def z650 : W := mkw 0x1302400026419540 0x04c0900009906550 0x5f03e010ffc3ffc3 0x97c0f8043ff0fff0

def z651 : W := mkw 0x5ffbd6ece3fbf331 0x57fef5bb38fefccc 0x7ef39fece3b3e332 0xdfbce7fb38ecf8cc

def z652 : W := mkw 0x00042e0548160814 0x00010b8152058205 0xed0c1e1f007c03fc 0xfb430787c01f00ff

def z653 : W := mkw 0x1c43d644f413f551 0x8710f5913d04fd54 0x1003fe00fc03fc03 0x0400ff803f00ff00

def z654 : W := mkw 0x00042c056c010540 0x00010b015b004150 0x7d0c7e1ffc431fc1 0x9f431f87ff10c7f0

def z655 : W := mkw 0x00008040a0012100 0x0000201028004840 0x10038000e003e002 0x0400e0003800f800

def z656 : W := mkw 0x0300013002c00280 0x00c0004c00b000a0 0xef0c01ff03fc03fc 0xfbc3007fc0ff00ff

def z657 : W := mkw 0x14100200277fdd54 0x4504008009dff755 0x8400000003ffffff 0xe100000000ffffff

def z658 : W := mkw 0x23bac1fa93e802a8 0x08eeb07ea4fa00aa 0xffffe1fffffc03fc 0xfffff87fffff00ff

def z659 : W := mkw 0x0c753e8d6d374d75 0x031d4fa35b4dd35d 0xfdfc7e1ffc7f1ffd 0xff7f1f87ff1fc7ff

def z660 : W := mkw 0x1712c370b7f3f7f1 0x85c4b0dc2dfcfdfc 0x5f03e1f0fff3fff3 0xd7c0f87c3ffcfffc

def z661 : W := mkw 0x0c519644e1336111 0x03146591384cd844 0x76f39e00e3b3e002 0x1dbce78038ecf800

def z662 : W := mkw 0xe38e69131a480088 0x38e39a44c6920022 0x810c60131c4c00cc 0x20431804c7130033

def z663 : W := mkw 0x23bc2fbf4bfe0abc 0x08ef0befd2ff82af 0xeffc1fff03fc03fc 0xfbff07ffc0ff00ff

def z664 : W := mkw 0xe38e69131c040c44 0x38e39a44c7010311 0x810c60131c4c1ccd 0x20431804c7130733

def z665 : W := mkw 0xebeffdfff8812331 0x3afbff7ffe2048cc 0x7bfffffffc000330 0xdeffffffff0000cc

def z666 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0x6ef001ec03b00330 0xdbbc007b00ec00cc

def z667 : W := mkw 0x23b801ba27e907e8 0x08ee006e89fa41fa 0xfffc61ffffff1ffd 0xffff187fffffc7ff

def z668 : W := mkw 0x00042c0548000000 0x00010b0152000000 0x200c1e0f00000000 0x08030783c0000000

def z669 : W := mkw 0x5c47fe44e017f911 0x5711ff913805fe44 0x1003fe00e003fc03 0x0400ff803800ff00

def z670 : W := mkw 0xf38ee973bec1b7c0 0xbce3ba5cefb06df0 0x5f0fe1f3ffc3ffc3 0x97c3f87cfff0fff0

def z671 : W := mkw 0x2cf996eee1bb6339 0x0b3e65bbb86ed8ce 0xfeff9fefe3bfe33e 0xffbfe7fbf8eff8cf

def z672 : W := mkw 0x0c7190e881a06221 0x031c643a20681888 0x6ef381ec03b0e332 0xdbbce07b00ec38cc

def z673 : W := mkw 0x0c71168c41324031 0x031c45a3104c900c 0x76f39e0c03b3e032 0x5dbce78300ecf80c

def z674 : W := mkw 0x08008444e0012111 0x0200211138004844 0x00000000e0000000 0x0000000038000000

def z675 : W := mkw 0x538ee970b6cdbfc0 0xd4e3ba5c2db36ff0 0x5f0fe1f0ffcfffc3 0x97c3f87c3ff3fff0

def z676 : W := mkw 0x00042c054c040c44 0x00010b0153010311 0xf90c7e1ffc4c1ccd 0x3e431f87ff130733

def z677 : W := mkw 0x5447fa40b417fd40 0xd511fe902d05ff50 0x1003fe00fc03fc03 0x0400ff803f00ff00

def z678 : W := mkw 0x1302413002c09280 0x04c0904c00b024a0 0x5f03e1f003c3ffc3 0x97c0f87c00f0fff0

def z679 : W := mkw 0x00042c0548000000 0x00010b0152000000 0xfd0c7e1ffc7c03fc 0xff431f87ff1f00ff

def z680 : W := mkw 0x0000000024010540 0x0000000009004150 0x0400000000431fc1 0x810000000010c7f0

def z681 : W := mkw 0xefffffdfd9324000 0x3bfffff7f64c9000 0x7fffffffffb3e002 0x1fffffffffecf800

def z682 : W := mkw 0xe8ed3e8f6c170d54 0x3a3b4fa3db05c355 0xfdfc7e1ffc7f1ffd 0xff7f1f87ff1fc7ff

def z683 : W := mkw 0xebeffdffd88002a8 0x3afbff7ff62000aa 0xfbfffffffc0003fc 0xfeffffffff0000ff

def z684 : W := mkw 0x0c75beede9b76b35 0x031d6fbb7a6ddacd 0xfeff9fefe3bfe33e 0xffbfe7fbf8eff8cf

def z685 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0x4ff001f003c003c0 0x93fc007c00f000f0

def z686 : W := mkw 0x1f73d1f893e0f2a1 0x87dcf47e24f83ca8 0x02f381e00380e002 0x00bce07800e03800

def z687 : W := mkw 0x0820048c40000031 0x020801231000000c 0x0000000c00000030 0x400000030000000c

def z688 : W := mkw 0x4ffffeece1b36331 0x13ffffbb386cd8cc 0x7fffffece3b3e332 0xdffffffb38ecf8cc

def z689 : W := mkw 0x23bc29bb0fec0eec 0x08ef0a6ec3fb03bb 0xeffc61ff1ffc1ffd 0xfbff187fc7ff07ff

def z690 : W := mkw 0x000428010c040c44 0x00010a0043010311 0xed0c601f1c7c1ffd 0xfb431807c71f07ff

def z691 : W := mkw 0x1410022003fedaa8 0x4504008800ffb6aa 0x8400000003ffffff 0xe100000000ffffff

def z692 : W := mkw 0x0c6196cce0136111 0x031865b33804d844 0x7af39fece003e002 0x1ebce7fb3800f800

def z693 : W := mkw 0x3ffbd7fef7fbf7f9 0x8ffef5ffbdfefdfe 0xffffffffffffffff 0xffffffffffffffff

def z694 : W := mkw 0x000006056c170d54 0x000001815b05c355 0x8c00001ffc7f1ffd 0xe3000007ff1fc7ff

def z695 : W := mkw 0xebef7c8f48000000 0x3afbdf23d2000000 0x73fffe0f00000000 0x1cffff83c0000000

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0x5500600000431c01 0x154018000010c700

def z697 : W := mkw 0x13066f157e579dd4 0x84c19bc55f95e775 0xfd0c7e1ffc7f1ffd 0xff431f87ff1fc7ff

def z698 : W := mkw 0x1302c040b641b540 0x84c0b0102d906d50 0x5703e000ffc3fc03 0x15c0f8003ff0ff00

def z699 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x22ff9e0003bce002 0x08bfe78000ef3800

def z700 : W := mkw 0x1302c575fec1b7d4 0x84c0b15d7fb06df5 0xdf03e1ffffc3ffff 0xf7c0f87ffff0ffff

def z701 : W := mkw 0xfffffddfdb68d000 0x7fffff77f6da3400 0x7bffffffff80e002 0x1effffffffe03800

def z702 : W := mkw 0x139a400003689000 0x04e6900000da2400 0x77ffe00003fffc03 0x1dfff80000ffff00

def z703 : W := mkw 0x1c73d6ecf5b3f771 0x871cf5bb3d6cfddc 0x7ef3ffecffb3ff33 0xdfbcfffb3fecffcc

def z704 : W := mkw 0x77ff7fbf6fffdffc 0x5dffdfefdbfff7ff 0xffffffffffffffff 0xffffffffffffffff

def z705 : W := mkw 0x54477a000016d800 0x5511de800005b600 0x750ffe00007ffc03 0x1d43ff80001fff00

def z706 : W := mkw 0xe08c280308000000 0x38230a00c2000000 0x000c000300000000 0x00030000c0000000

def z707 : W := mkw 0x0302c170b4812740 0x00c0b05c2d2049d0 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z708 : W := mkw 0x30bac0cab529b568 0x8c2eb032ad4a6d5a 0xb0ffe00ffc3ffc3f 0x6c3ff803ff0fff0f

def z709 : W := mkw 0xecfd3e8f493e4828 0x7b3f4fa3d24f920a 0xa0fc1e0f003c003c 0x683f0783c00f000f

def z710 : W := mkw 0x5baeecece2cdbb31 0x56ebbb3b38b36ecc 0x090c61ece04c1f31 0xc243187b381307cc

def z711 : W := mkw 0xbc3087dfdb7ed800 0x6f0c21f7f6dfb600 0x0c0001fffffffc03 0x0300007fffffff00

def z712 : W := mkw 0xf38e69131a409080 0xbce39a44c6902420 0x010c60131c000000 0x00431804c7000000

def z713 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0xfbfffffffc0003fc 0xfeffffffff0000ff

def z714 : W := mkw 0xebeffddfd8040804 0x3afbff77f6010201 0xfbfffffffc0c000c 0x3effffffff030003

def z715 : W := mkw 0x57db54056f69d554 0x55f6d5015bda7555 0x8af3801fff80e3fe 0xe2bce007ffe038ff

def z716 : W := mkw 0xf38e69131a409000 0x3ce39a44c6902400 0x010c60131c401c01 0x00431804c7100700

def z717 : W := mkw 0x57df7b10137ed880 0xd5f7dec404dfb620 0x77fffe0003fffc03 0x1dffff8000ffff00

def z718 : W := mkw 0x57df78000368d000 0x55f7de0000da3400 0x77fffe0003c3fc03 0x1dffff8000f0ff00

def z719 : W := mkw 0x04519260a1b36331 0x01146498286cd8cc 0x7ef39fe0e3b3e332 0xdfbce7f838ecf8cc

def z720 : W := mkw 0x138ac170b6c1b7c0 0x84e2b05c2db06df0 0x7fffe1f0ffc3ffc3 0x9ffff87c3ff0fff0

def z721 : W := mkw 0x538ac170b6c9b7c0 0xd4e2b05c2db26df0 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z722 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x7af39fece383e002 0x1ebce7fb38e0f800

def z723 : W := mkw 0x17535200037ed800 0x45d4d48000dfb600 0x77f3fe0003fffc03 0x1dfcff8000ffff00

def z724 : W := mkw 0x00042c054c040c44 0x00010b0153010311 0xfd0c7e1ffc7c1ffd 0xff431f87ff1f07ff

def z725 : W := mkw 0xfbeffddfda4c9888 0x7efbff77f6932622 0xfbfffffffc4c1ccd 0x3effffffff130733

def z726 : W := mkw 0x1002c060b6c1b7c0 0x8400b0182db06df0 0x5e03e1e0ffc3ffc3 0x9780f8783ff0fff0

def z727 : W := mkw 0xe8effddfd8000000 0x3a3bff77f6000000 0x38fffffffc000000 0x0e3fffffff000000

def z728 : W := mkw 0xebebd3dab4170d54 0x3afaf4f6ad05c355 0x86f381e0007f1ffd 0xe1bce078001fc7ff

def z729 : W := mkw 0x0865bccdc8000000 0x02196f3372000000 0x7af3ffecfc000000 0x1ebcfffb3f000000

def z730 : W := mkw 0xa82085fffc8127e8 0xaa08217fff2049fa 0x880001fffc0003fc 0xe200007fff0000ff

def z731 : W := mkw 0xebeffddfd8040800 0x3afbff77f6010200 0x7bfffffffc4c1c01 0x1effffffff130700

def z732 : W := mkw 0x20b801ba01a802a8 0x082e006e806a00aa 0xeefc01ff03bc03fc 0xfbbf007fc0ef00ff

def z733 : W := mkw 0x04553a0001364800 0x01154e80004d9200 0x76f3fe0003b3fc03 0x1dbcff8000ecff00

def z734 : W := mkw 0x738e6912024c9888 0x5ce39a4480932622 0x010c6000004c1c01 0x0043180000130700

def z735 : W := mkw 0xcbcffd55d8000000 0x32f3ff5576000000 0x7bfffff0fc000000 0x1efffffc3f000000

def z736 : W := mkw 0x1302c170b6c1b7e8 0x84c0b05c2db06dfa 0xdf03e1f0ffc3ffff 0xf7c0f87c3ff0ffff

def z737 : W := mkw 0x4beffccdc8000000 0x12fbff3372000000 0x7bfffffffc000000 0x1effffffff000000

def z738 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x7ff3fffcffb3e332 0xdffcffff3fecf8cc

def z739 : W := mkw 0x23a8039a24170d54 0x08ea00e68905c355 0xeffc01ff007f1ffd 0xfbff007fc01fc7ff

def z740 : W := mkw 0xcc47fe45fc176d55 0x3311ff917f05db55 0x1003fe00fc03fc03 0x0400ff803f00ff00

def z741 : W := mkw 0x1010022027ffbffc 0x8404008809ffefff 0x8400000003ffffff 0xe100000000ffffff

def z742 : W := mkw 0x086194ecc0802200 0x0218653b30200880 0x7af39fece380e002 0x1ebce7fb38e03800

def z743 : W := mkw 0x77df7b12037ed800 0x5df7dec480dfb600 0x77fffe1303fffc03 0x1dffff84c0ffff00

def z744 : W := mkw 0x23b801ba01a00220 0x08ee006e80680088 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z745 : W := mkw 0x1306ef75dad6ba94 0x84c1bbdd76b5aea5 0xa20f9fef03bce03e 0x6883e7fbc0ef380f

def z746 : W := mkw 0x00042c056c010540 0x00010b015b004150 0xfd0c7e1ffc7f1ffd 0xff431f87ff1fc7ff

def z747 : W := mkw 0x0c7190e881a06221 0x031c643a20681888 0x72f39fe00380e002 0x1cbce7f800e03800

def z748 : W := mkw 0x20b801ba01a802a8 0x082e006e806a00aa 0xedfc01ff007c03fc 0xfb7f007fc01f00ff

def z749 : W := mkw 0x53cf7800024c9800 0x54f3de0000932600 0x77fffe0003cffc03 0x1dffff8000f3ff00

def z750 : W := mkw 0x282085ffec8127fd 0x0a08217ffb2049ff 0x880001fffc0003fc 0xe200007fff0000ff

def z751 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0xa6fc01ef03fc03fc 0xe9bf007bc0ff00ff

def z752 : W := mkw 0xabacaddfd8000000 0x2aeb2b77f6000000 0x7bfc7ffffc000000 0x1eff1fffff000000

def z753 : W := mkw 0x2fc99756e25b6199 0x0bf265d5b896d866 0x910f9e13e04fe0ce 0x2443e784f813f833

def z754 : W := mkw 0x57df7a010b7ed804 0x55f7de8042dfb601 0xf7fffe0303fffc0f 0x3dffff80c0ffff03

def z755 : W := mkw 0x0c519664e1b36311 0x03146599386cd8c4 0x7ef39fe0e3b3e302 0x9fbce7f838ecf8c0

def z756 : W := mkw 0x74677bba0096daa8 0x5d19deee8025b6aa 0x9803ffff0003ffff 0xe600ffffc000ffff

def z757 : W := mkw 0x0c75b8e98da46e65 0x031d6e3a63691b99 0x83ffe1f31fccfccf 0x20fff87cc7f33f33

def z758 : W := mkw 0x1410022027ffdffc 0x4504008809fff7ff 0x8400000003ffffff 0xe100000000ffffff

def z759 : W := mkw 0xf8ed3caf6ec1b7c0 0xbe3b4f2bdbb06df0 0x24fc1e0f03c3ffc3 0x893f0783c0f0fff0

def z760 : W := mkw 0x0c7194ecc1a06221 0x031c653b30681888 0x22f39fec0380e002 0x08bce7fb00e03800

def z761 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x13fffe0003cffc03 0x04ffff8000f3ff00

def z762 : W := mkw 0x1302c060b6c1b740 0x84c0b0182db06dd0 0x5f03e1e0ffc3ff03 0x97c0f8783ff0ffc0

def z763 : W := mkw 0xebeffddfda480088 0x3afbff77f6920022 0x7bfffffffc000000 0x1effffffff000000

def z764 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x7fff9fffe3b3e332 0xdfffe7fff8ecf8cc

def z765 : W := mkw 0x886194cdd8000000 0x2218653376000000 0x7af39fecfc000000 0x1ebce7fb3f000000

def z766 : W := mkw 0xe79e6b3339b36331 0x39e79accce6cd8cc 0x050c60131fb3e332 0xc1431804c7ecf8cc

def z767 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x2af39fece3b0e332 0xcabce7fb38ec38cc

def z768 : W := mkw 0x0c7196ecc1b26221 0x031c65bb306c9888 0x7ef39fece3b3e002 0x1fbce7fb38ecf800

def z769 : W := mkw 0x1302c170b6c9b7c8 0x84c0b05c2db26df2 0xdf03e1f0ffcfffcf 0xb7c0f87c3ff3fff3

def z770 : W := mkw 0x538e6910124c9800 0x54e39a4404932600 0x010c60101c4c1c01 0x0043180407130700

def z771 : W := mkw 0x138ac170b6c9b7c0 0x84e2b05c2db26df0 0x5f0fe1f0ffcfffc3 0x97c3f87c3ff3fff0

def z772 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x7f03e1fcfff3fff3 0xdfc0f87f3ffcfffc

def z773 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0xfffc61ff03ff1ffd 0xffff187fc0ffc7ff

def z774 : W := mkw 0xebed3d9f48000000 0x3afb4f67d2000000 0x7bfc7ffffc000000 0x1eff1fffff000000

def z775 : W := mkw 0xfbeffddfda4c9800 0x7efbff77f6932600 0x7fffffffffcffc03 0x1ffffffffff3ff00

def z776 : W := mkw 0x1302c060a6c1b740 0x04c0b01829b06dd0 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z777 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x7ffffe1f03fffc03 0x1fffff87c0ffff00

def z778 : W := mkw 0x57df7a000136d800 0x55f7de80004db600 0x77fffe0003b3fc03 0x1dffff8000ecff00

def z779 : W := mkw 0x0c7196ece1bf6b31 0x431c65bb386fdacc 0x7ef39fece3bfe332 0xdfbce7fb38eff8cc

def z780 : W := mkw 0x1302c150964094c0 0x84c0b05425902530 0x5f03e1f0ffc3fcc3 0x17c0f87c3ff0ff30

def z781 : W := mkw 0x0410022025b36771 0x01040088096cd9dc 0x0400000003f3fff3 0xc100000000fcfffc

def z782 : W := mkw 0x1302c170b2c1b300 0x04c0b05c2cb06cc0 0x5f03e1f0ffc3ff03 0x97c0f87c3ff0ffc0

def z783 : W := mkw 0x5c47fe45ec17fd55 0x5711ff917b05ff55 0x1003fe00fc03fc03 0x0400ff803f00ff00

def z784 : W := mkw 0x43cffd55d8000000 0x10f3ff5576000000 0x7bfffffffc000000 0x1effffffff000000

def z785 : W := mkw 0x538e6910024c9880 0x54e39a4400932620 0x010c6010004c1cc1 0x0043180400130730

def z786 : W := mkw 0x0451120001324000 0x01144480004c9000 0x77f3fe0003f3fc03 0x1dfcff8000fcff00

def z787 : W := mkw 0x0c7192e8a1b36331 0x031c64ba286cd8cc 0x76f39fe003b3e332 0xddbce7f800ecf8cc

def z788 : W := mkw 0xebeffddfd8000028 0x3afbff77f600000a 0xfbfffffffc00003c 0x7effffffff00000f

def z789 : W := mkw 0x0c7196ece5b36771 0x031c65bb396cd9dc 0x7ef39fece3f3fff3 0xdfbce7fb38fcfffc

def z790 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x5ef39fe0e383e302 0x97bce7f838e0f8c0

def z791 : W := mkw 0x0c7196ece1bb6339 0x031c65bb386ed8ce 0xfef39fece3bfe33e 0xffbce7fb38eff8cf

def z792 : W := mkw 0xc867fccdd8000000 0x3219ff3376000000 0x12f3ffe0fc000000 0x04bcfff83f000000

def z793 : W := mkw 0x0c7196ece1b76b35 0x031c65bb386ddacd 0xfef39fece3bfe33e 0xffbce7fb38eff8cf

def z794 : W := mkw 0x086194cdc8000000 0x0218653372000000 0x7af39ffffc000000 0x1ebce7ffff000000

def z795 : W := mkw 0xecfd3e8f493e4831 0x7b3f4fa3d24f920c 0x20fc1e0f003c0030 0x483f0783c00f000c

def z796 : W := mkw 0x738e6912024c9800 0x5ce39a4480932600 0x010c6013004c1c01 0x00431804c0130700

def z797 : W := mkw 0xebeffddfda480088 0x3afbff77f6920022 0xfffffffffc7c03fc 0xffffffffff1f00ff

def z798 : W := mkw 0x0410022025b36775 0x01040088096cd9dd 0x8400000003b3e3fe 0xe100000000ecf8ff

def z799 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x26f39fec03b3e332 0xc9bce7fb00ecf8cc

def z800 : W := mkw 0x37b801ba03e8d2a8 0x4dee006e80fa34aa 0xeffc01ff03fce3fe 0xfbff007fc0ff38ff

def z801 : W := mkw 0x047192e8a1b36320 0x011c64ba286cd8c8 0x7ef39fece3b3e332 0xdfbce7fb38ecf8cc

def z802 : W := mkw 0x44ddbb70b5bf6fc0 0xd1376edc2d6fdbf0 0x28fc1ff0fc3c03c0 0x8a3f07fc3f0f00f0

def z803 : W := mkw 0xfbeffddfd800b000 0xbefbff77f6002c00 0x7bfffffffc00e002 0x1effffffff003800

def z804 : W := mkw 0x20b800aa03e802a8 0x082e002a80fa00aa 0xeefc01ef03fc03fc 0xfbbf007bc0ff00ff

def z805 : W := mkw 0x57df7a000372d000 0x15f7de8000dcb400 0x77fffe0003f3fc03 0x1dffff8000fcff00

def z806 : W := mkw 0x282085fef48127f9 0x8a08217fbd2049fe 0x880001fffc0003fc 0xe200007fff0000ff

def z807 : W := mkw 0xa865bddfd8000000 0x2a196f77f6000000 0x7bfffffffc000000 0x1effffffff000000

def z808 : W := mkw 0xebebd5dfd8000000 0x3afaf577f6000000 0x7af39ffffc000000 0x1ebce7ffff000000

def z809 : W := mkw 0x1f73579c5772d4f1 0x87dcd5e715dcb53c 0x21f07e1c1c701cf1 0x487c1f87071c073c

def z810 : W := mkw 0xfbeffddfda409000 0x3efbff77f6902400 0x7bffffffff80e002 0x1effffffffe03800

def z811 : W := mkw 0x082084edec812775 0x0208213b7b2049dd 0x080001ecfc000330 0xc200007b3f0000cc

def z812 : W := mkw 0x047112a801b24220 0x011c44aa006c9088 0x76f39fe003b3e002 0x1dbce7f800ecf800

def z813 : W := mkw 0x00242c8d48000000 0x00090b2352000000 0x7bfc7ffffc000000 0x1eff1fffff000000

def z814 : W := mkw 0xfbfbd1fa93e8b2a8 0xbefef47ea4fa2caa 0x02f381e00380e002 0x00bce07800e03800

def z815 : W := mkw 0x20b801ba03e802a8 0x082e006e80fa00aa 0xacfc01ff03fc03fc 0xeb3f007fc0ff00ff

def z816 : W := mkw 0xc857fc65dbe802a8 0x3215ff1976fa00aa 0x9403fe00fffc03fc 0xe500ff803fff00ff

def z817 : W := mkw 0x10008060a6c1b7c0 0x8400201829b06df0 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z818 : W := mkw 0x003000a803e802a8 0x000c002a00fa00aa 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z819 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x1303e1f0ffc3fcc3 0x04c0f87c3ff0ff30

def z820 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x16f3fe0003fffc03 0x05bcff8000ffff00

def z821 : W := mkw 0xe8edbccfc8000000 0x3a3b6f33f2000000 0x7bfffffffc000000 0x1effffffff000000

def z822 : W := mkw 0x23bc2fbf6fff0ffc 0x08ef0befdbffc3ff 0x12f07fe0ff831c01 0x04bc1ff83fe0c700

def z823 : W := mkw 0x00142c254be802a8 0x00050b0952fa00aa 0xfd0c7e1ffffc03fc 0xff431f87ffff00ff

def z824 : W := mkw 0xefeffddfd8006001 0x3bfbff77f6001800 0x7bfffffffc00e002 0x1effffffff003800

def z825 : W := mkw 0x1302413026c197c0 0x04c0904c09b065f0 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z826 : W := mkw 0x77fbd1fa93e8f2a8 0xddfef47ea4fa3caa 0x02f381e00380e002 0x00bce07800e03800

def z827 : W := mkw 0xf38e6912124c9800 0x7ce39a4484932600 0x010c6000004c1c01 0x0043180000130700

def z828 : W := mkw 0x0c7196ece1b36300 0x031c65bb386cd8c0 0x7ef39fece3b3e302 0x9fbce7fb38ecf8c0

def z829 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0xffff81ff03ffe3fe 0xffffe07fc0fff8ff

def z830 : W := mkw 0x0845be45ec170d54 0x02116f917b05c355 0x1003fe00fc031c01 0x0400ff803f00c700

def z831 : W := mkw 0x1712c350937ed800 0x45c4b0d424dfb600 0x5f03e1f0fffffc03 0x17c0f87c3fffff00

def z832 : W := mkw 0x57df7b10137ed800 0x55f7dec404dfb600 0x77fffe101ffffc03 0x1dffff8407ffff00

def z833 : W := mkw 0x1410022027f3f7c0 0x8504008809fcfdf0 0x0400000003f3ffc3 0x8100000000fcfff0

def z834 : W := mkw 0x33b801ba03e892a8 0x0cee006e80fa24aa 0xeffc01ff03ffffff 0xfbff007fc0ffffff

def z835 : W := mkw 0x0c7196ece5b76f75 0x031c65bb396ddbdd 0xffff9fffe3ffffff 0xffffe7fff8ffffff

def z836 : W := mkw 0x1002c060b481b740 0x8400b0182d206dd0 0x1203e1e0ff83fc03 0x0480f8783fe0ff00

def z837 : W := mkw 0x53cf7a0002569800 0x14f3de800095a600 0x77fffe0003fffc03 0x1dffff8000ffff00

def z838 : W := mkw 0x0c7196ece5b76f75 0x031c65bb396ddbdd 0x7ef39fece3b3ff33 0xdfbce7fb38ecffcc

def z839 : W := mkw 0x0451122001b24200 0x01144488006c9080 0x7ef39fe003b3e302 0x9fbce7f800ecf8c0

def z840 : W := mkw 0x2cfd3e8f493e483d 0x0b3f4fa3d24f920f 0xa0fc1e0f003c003c 0x683f0783c00f000f

def z841 : W := mkw 0x0451926081b26200 0x01146498206c9880 0x76f39fe003b3e002 0x1dbce7f800ecf800

def z842 : W := mkw 0xac7196efe9b36331 0x2b1c65bbfa6cd8cc 0x7ef39fefe3b3e332 0xdfbce7fbf8ecf8cc

def z843 : W := mkw 0x5447fe45fc17fd54 0xd511ff917f05ff55 0x1003fe00fc03fc03 0x0400ff803f00ff00

def z844 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x57f3fe0003c3fc03 0x15fcff8000f0ff00

def z845 : W := mkw 0xffeffddfd800d000 0x7ffbff77f6003400 0x7bfffffffc00e002 0x1effffffff003800

def z846 : W := mkw 0x0410022025b76f75 0x01040088096ddbdd 0x0400000003b3ff33 0xc100000000ecffcc

def z847 : W := mkw 0x087194ece1a12320 0x021c653b386848c8 0x7ef39fece3b3e332 0xdfbce7fb38ecf8cc

def z848 : W := mkw 0x1410022027ffff75 0x4504008809ffffdd 0x8400000003ffffff 0xe100000000ffffff

def z849 : W := mkw 0x0c7196ecc1b26231 0x031c65bb306c988c 0x02f39fe00380e002 0x00bce7f800e03800

def z850 : W := mkw 0xd847fe45fc17bd54 0xb611ff917f05ef55 0x1003fe00fc03fc03 0x0400ff803f00ff00

def z851 : W := mkw 0x57577a000376d800 0x55d5de8000ddb600 0x77f3fe0003f3fc03 0x1dfcff8000fcff00

def z852 : W := mkw 0xfffbd1fa93e8d2a8 0x7ffef47ea4fa34aa 0x02f381e00380e002 0x00bce07800e03800

def z853 : W := mkw 0x145112000136d800 0x45144480004db600 0x76f39e0003b3fc03 0x1dbce78000ecff00

def z854 : W := mkw 0x538e69111e4c9cc4 0xd4e39a4447932731 0x810c60131c4c1ccd 0x20431804c7130733

def z855 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x5703e1e0ffc3fc03 0x15c0f8783ff0ff00

def z856 : W := mkw 0xfbeffddfd8009000 0x3efbff77f6002400 0x7bfffffffc03fc03 0x1effffffff00ff00

def z857 : W := mkw 0x53cf782026c1b7c0 0x94f3de0809b06df0 0x77fffe0003c3ffc3 0x9dffff8000f0fff0

def z858 : W := mkw 0x0c7196ece1b363b9 0x031c65bb386cd8ee 0xfef39fece3b3e3fe 0xffbce7fb38ecf8ff

def z859 : W := mkw 0x1302c17092c09280 0x04c0b05c24b024a0 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z860 : W := mkw 0x0451924081324000 0x01146490204c9000 0x7ef39fe0e3b3e002 0x1fbce7f838ecf800

def z861 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x7af3ffecfc000000 0x1ebcfffb3f000000

def z862 : W := mkw 0x047112a821b36331 0x011c44aa086cd8cc 0x7ef39fec03b3e332 0xdfbce7fb00ecf8cc

def z863 : W := mkw 0x0c7192e881b26221 0x031c64ba206c9888 0x12f39fe00383e002 0x04bce7f800e0f800

def z864 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0xfef39fece3ffe3fe 0xffbce7fb38fff8ff

def z865 : W := mkw 0x1410022027fbf7f9 0x8504008809fefdfe 0x8400000003ffffff 0xe100000000ffffff

def z866 : W := mkw 0xebeffddfd8000031 0x3afbff77f600000c 0x7bfffffffc000030 0x5effffffff00000c

def z867 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0xf7fffe0003ffffff 0xfdffff8000ffffff

def z868 : W := mkw 0x17d91200037ed800 0x45f6448000dfb600 0x77ff9e0003fffc03 0x1dffe78000ffff00

def z869 : W := mkw 0x1c47fe45fc17fd55 0x8711ff917f05ff55 0x1003fe00fc03fc03 0x0400ff803f00ff00

def z870 : W := mkw 0xebeffddfd8000088 0x3afbff77f6000022 0xfbfffffffc0000cc 0x3effffffff000033

def z871 : W := mkw 0x0c7196ededb76f75 0x031c65bb7b6ddbdd 0xfef39fffffffffff 0xffbce7ffffffffff

def z872 : W := mkw 0xfbeffddfda409080 0xbefbff77f6902420 0x7bfffffffc000000 0x1effffffff000000

def z873 : W := mkw 0x57df7a00037ed831 0x55f7de8000dfb60c 0x77fffe0003fffc33 0x5dffff8000ffff0c

def z874 : W := mkw 0xfbeffddfda409000 0x3efbff77f6902400 0x7bfffffffc401c01 0x1effffffff100700

def z875 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x32f39fece3b3e032 0x4cbce7fb38ecf80c

def z876 : W := mkw 0xab63d5dfd8000000 0x2ad8f577f6000000 0x7bf3fffffc000000 0x1efcffffff000000

def z877 : W := mkw 0x17577a000376d800 0x05d5de8000ddb600 0x77fffe0003fffc03 0x1dffff8000ffff00

def z878 : W := mkw 0x047116ac61b34330 0x011c45ab186cd0cc 0x7ef39fece3b3e332 0xdfbce7fb38ecf8cc

def z879 : W := mkw 0x54577a000136d800 0x5515de80004db600 0x77fffe0003fffc03 0x1dffff8000ffff00

def z880 : W := mkw 0x23aeeddfd8000000 0x08ebbb77f6000000 0x7bfffffffc000000 0x1effffffff000000

def z881 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0xff0ffe1fffffffff 0xffc3ff87ffffffff

def z882 : W := mkw 0xf7df7a030b7ed800 0x7df7de80c2dfb600 0x77fffe0303fffc03 0x1dffff80c0ffff00

def z883 : W := mkw 0x1002c170b481b7c0 0x8400b05c2d206df0 0x5e03e1f0ff83ffc3 0x9780f87c3fe0fff0

def z884 : W := mkw 0x0c7196ededb36775 0x031c65bb7b6cd9dd 0xffff9fffffffe3fe 0xffffe7fffffff8ff

def z885 : W := mkw 0x0c7196ededb36775 0x031c65bb7b6cd9dd 0x7ef39fecffb3e332 0xdfbce7fb3fecf8cc

def z886 : W := mkw 0x03008170a6c127c0 0x00c0205c29b049f0 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z887 : W := mkw 0x1410022027fffff1 0xc504008809fffffc 0x0400000003fffff3 0xc100000000fffffc

def z888 : W := mkw 0x57df7a00037ed828 0x55f7de8000dfb60a 0xf7fffe0003fffc3f 0x7dffff8000ffff0f

def z889 : W := mkw 0x086196ece0932310 0x021865bb3824c8c4 0x7ef39fece3b3e332 0xdfbce7fb38ecf8cc

def z890 : W := mkw 0x0c7194ecc1a06221 0x031c653b30681888 0x12f39fe0e380e002 0x04bce7f838e03800

def z891 : W := mkw 0xebeffddfda480000 0x3afbff77f6920000 0x7bfffffffc4c0000 0x1effffffff130000

def z892 : W := mkw 0x03b800a803e80220 0x00ee002a00fa0088 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z893 : W := mkw 0x00419060a0812300 0x00106418282048c0 0x7ef39fe0e383e302 0x9fbce7f838e0f8c0

def z894 : W := mkw 0x0b67fdddd8000000 0x02d9ff7776000000 0x7bfffffffc000000 0x1effffffff000000

def z895 : W := mkw 0x203001ba01a002a8 0x080c006e806800aa 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z896 : W := mkw 0x54df7a00037ed800 0x5537de8000dfb600 0x34fffe0003fffc03 0x0d3fff8000ffff00

def z897 : W := mkw 0xf38e69131e449cc4 0xbce39a44c7912731 0x810c60131c4c1ccd 0x20431804c7130733

def z898 : W := mkw 0x2bedbddfc8000000 0x0afb6f77f2000000 0x7bfffffffc000000 0x1effffffff000000

def z899 : W := mkw 0x082084ece4812771 0x0208213b392049dc 0x080001fcfc0003f0 0xc200007f3f0000fc

def z900 : W := mkw 0x0010022025b70f74 0x00040088096dc3dd 0x8400000003ff1ffd 0xe100000000ffc7ff

def z901 : W := mkw 0xcbeffccdd8000000 0x32fbff3376000000 0x7bffffecfc000000 0x1efffffb3f000000

def z902 : W := mkw 0x63eff9da90000000 0x18fbfe76a4000000 0x7bfffffffc000000 0x1effffffff000000

def z903 : W := mkw 0xcb67fdddd8000000 0x32d9ff7776000000 0x7bf3fffcfc000000 0x1efcffff3f000000

def z904 : W := mkw 0x1302c17092c0b280 0x84c0b05c24b02ca0 0x5f03e1f0ffc3fc03 0x17c0f87c3ff0ff00

def z905 : W := mkw 0x1302c170b6c1b7f1 0x84c0b05c2db06dfc 0x5f03e1f0ffc3fff3 0xd7c0f87c3ff0fffc

def z906 : W := mkw 0xf38e69131a4c9888 0x7ce39a44c6932622 0x810c60131c4c1ccd 0x20431804c7130733

def z907 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x5bf3fff0fc000000 0x16fcfffc3f000000

def z908 : W := mkw 0x202085fffc8127fc 0x8808217fff2049ff 0x880001fffc0003fc 0xe200007fff0000ff

def z909 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x1a03e1f0ff83ffc3 0x8680f87c3fe0fff0

def z910 : W := mkw 0x0c7196ede9b36331 0x031c65bb7a6cd8cc 0x7ef39fffffb3e332 0xdfbce7ffffecf8cc

def z911 : W := mkw 0x086194ccc0000000 0x0218653330000000 0x7ef39fece383e002 0x1fbce7fb38e0f800

def z912 : W := mkw 0x00042e0548160800 0x00010b8152058200 0xfd0c7e1ffc7f1ffd 0xff431f87ff1fc7ff

def z913 : W := mkw 0x0398013003e80280 0x00e6004c00fa00a0 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z914 : W := mkw 0xdc47fe45fc17dd54 0x7711ff917f05f755 0x1003fe00fc03fc03 0x0400ff803f00ff00

def z915 : W := mkw 0xa86195dfd8000000 0x2a186577f6000000 0x28f01ffffc000000 0x0a3c07ffff000000

def z916 : W := mkw 0x8c7196edf9b36331 0x231c65bb7e6cd8cc 0x7ef39fecffb3e332 0xdfbce7fb3fecf8cc

def z917 : W := mkw 0xe3ae6d9f58000000 0x38eb9b67d6000000 0x7bfc7ffffc000000 0x1eff1fffff000000

def z918 : W := mkw 0x0c7196ecc1b26231 0x031c65bb306c988c 0x6ef39fec03b0e332 0xdbbce7fb00ec38cc

def z919 : W := mkw 0x338ac172b6c9b7c8 0x8ce2b05cadb26df2 0xff0fe1ffffffffff 0xffc3f87fffffffff

def z920 : W := mkw 0x1410022027ffffd4 0xc504008809fffff5 0x8400000003ffffff 0xe100000000ffffff

def z921 : W := mkw 0x0c7196ede9b36335 0x031c65bb7a6cd8cd 0xfef39fefe3b3e33e 0xffbce7fbf8ecf8cf

def z922 : W := mkw 0x57df7a00037ed814 0x55f7de8000dfb605 0xf7fffe0003fffc3f 0x7dffff8000ffff0f

def z923 : W := mkw 0x0c7196ece5b36771 0x031c65bb396cd9dc 0xffffffffffffffff 0xffffffffffffffff

def z924 : W := mkw 0x0c7196ece5b36771 0x031c65bb396cd9dc 0x7ef3ffecffb3ff33 0xdfbcfffb3fecffcc

def z925 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0xdf03e1ffffc3ffff 0xf7c0f87ffff0ffff

def z926 : W := mkw 0x0c7196cce1336111 0x031c65b3384cd844 0x7ef39fece3b3e002 0x1fbce7fb38ecf800

def z927 : W := mkw 0x23b8019a03680000 0x08ee006680da0000 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z928 : W := mkw 0x00042e056c170d54 0x00010b815b05c355 0xa90c7e1ffc7c1ffd 0xea431f87ff1f07ff

def z929 : W := mkw 0xfbeffddfd8049800 0x7efbff77f6012600 0x7bfffffffc001c01 0x1effffffff000700

def z930 : W := mkw 0x57cf7a000256d800 0x55f3de800095b600 0x77fffe0003c3fc03 0x1dffff8000f0ff00

def z931 : W := mkw 0x04042e056c176d55 0x01010b815b05db55 0xfd0c7e1ffc7fffff 0xff431f87ff1fffff

def z932 : W := mkw 0x54577a000136d800 0x5515de80004db600 0x12f3fe000383fc03 0x04bcff8000e0ff00

def z933 : W := mkw 0x0c7194ece1a16331 0x031c653b386858cc 0x7af39fece380e332 0xdebce7fb38e038cc

def z934 : W := mkw 0x20b800aa01a80228 0x082e002a806a008a 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z935 : W := mkw 0x082085fcf48127c0 0x8208217f3d2049f0 0x080001fcfc0003c0 0x8200007f3f0000f0

def z936 : W := mkw 0xebeffddfda400080 0x3afbff77f6900020 0x7bfffffffc4000c0 0x1effffffff100030

def z937 : W := mkw 0xf38e69131a489000 0x7ce39a44c6922400 0x010c60131c000000 0x00431804c7000000

def z938 : W := mkw 0x1410022027ffffe8 0xc504008809fffffa 0x8400000003ffffff 0xe100000000ffffff

def z939 : W := mkw 0x0451120001364800 0x01144480004d9200 0x76f39e0003fffc03 0x1dbce78000ffff00

def z940 : W := mkw 0x086194ccc0000000 0x0218653330000000 0x7bf3fffcfc000000 0x1efcffff3f000000

def z941 : W := mkw 0x0c7192e881b26221 0x031c64ba206c9888 0x7ef39fec03b3e332 0xdfbce7fb00ecf8cc

def z942 : W := mkw 0xe867fddfd8000000 0x3a19ff77f6000000 0x7af3fffffc000000 0x1ebcffffff000000

def z943 : W := mkw 0x44dd3a00013e4800 0x51374e80004f9200 0x77fffe0003fffc03 0x1dffff8000ffff00

def z944 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x16f39fe0e3b3e332 0xc5bce7f838ecf8cc

def z945 : W := mkw 0x23b8019a01280028 0x08ee0066804a000a 0xeffc01ff007c03fc 0xfbff007fc01f00ff

def z946 : W := mkw 0xe3cff95398000000 0x38f3fe54e6000000 0x7bfffff3fc000000 0x1efffffcff000000

def z947 : W := mkw 0x14553a00037ed800 0x45154e8000dfb600 0x77fffe0003fffc03 0x1dffff8000ffff00

def z948 : W := mkw 0x23b801ba01a802a8 0x08ee006e806a00aa 0xebfc01ff003c03fc 0xfaff007fc00f00ff

def z949 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x32fffe0003bffc03 0x0cbfff8000efff00

def z950 : W := mkw 0xebeffddfd8080008 0x3afbff77f6020002 0xfbfffffffc0c000c 0x3effffffff030003

def z951 : W := mkw 0xebeffddfd80c0800 0x7afbff77f6030200 0x7bfffffffc0c0000 0x1effffffff030000

def z952 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x5e03e1e0ff83ff03 0x9780f8783fe0ffc0

def z953 : W := mkw 0x0863d4ccd0000000 0x0218f53334000000 0x7af3ffecfc000000 0x1ebcfffb3f000000

def z954 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x32ffffeffc000000 0x0cbffffbff000000

def z955 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x7ff3ffece3f3ff33 0xdffcfffb38fcffcc

def z956 : W := mkw 0x082084ecf4812771 0x8208213b3d2049dc 0x080001ecfc000330 0xc200007b3f0000cc

def z957 : W := mkw 0x54df7a00013ed800 0x5537de80004fb600 0x76fffe0003bffc03 0x1dbfff8000efff00

def z958 : W := mkw 0x0c7196ecc1b24220 0x031c65bb306c9088 0x7ef39fece3b3e332 0xdfbce7fb38ecf8cc

def z959 : W := mkw 0x27b801ba03e862a9 0x09ee006e80fa18aa 0xeffc01ff03fce3fe 0xfbff007fc0ff38ff

def z960 : W := mkw 0x0c7192e8a1b36321 0x031c64ba286cd8c8 0x7ef39fe0e3b3e302 0x9fbce7f838ecf8c0

def z961 : W := mkw 0x47df7a0001364800 0x11f7de80004d9200 0x77fffe0003fffc03 0x1dffff8000ffff00

def z962 : W := mkw 0xf7df7b131b7ed888 0x7df7dec4c6dfb622 0xf7fffe131ffffccf 0x3dffff84c7ffff33

def z963 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x73fffe000383fc03 0x1cffff8000e0ff00

def z964 : W := mkw 0x0c7194ecc1a06221 0x031c653b30681888 0x7ef39fece3b0e332 0xdfbce7fb38ec38cc

def z965 : W := mkw 0x57df7a010b7ed800 0x55f7de8042dfb600 0x77fffe131ffffc03 0x1dffff84c7ffff00

def z966 : W := mkw 0xf38ac172b6c1b7c0 0xbce2b05cadb06df0 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z967 : W := mkw 0x0343d15090000000 0x00d0f45424000000 0x7bf3fff0fc000000 0x1efcfffc3f000000

def z968 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x7f0fe1f0ffffffc3 0x9fc3f87c3ffffff0

def z969 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x7ffffe0c03ffff33 0xdfffff8300ffffcc

def z970 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0xfffc61fffffc03fc 0xffff187fffff00ff

def z971 : W := mkw 0x4cfd3e8d493e4835 0x533f4fa3524f920d 0xa0fc1e0f003c003c 0x683f0783c00f000f

def z972 : W := mkw 0x0000060464130550 0x000001811904c154 0xfd0c7e1ffc7f1ffd 0xff431f87ff1fc7ff

def z973 : W := mkw 0x0410022027ff6ffd 0x0104008809ffdbff 0x8400000003ffffff 0xe100000000ffffff

def z974 : W := mkw 0xf7df7b12137ed800 0x7df7dec484dfb600 0x77fffe0003fffc03 0x1dffff8000ffff00

def z975 : W := mkw 0xecfd3e8f49364835 0x3b3f4fa3d24d920d 0xa0fc1e0f003c003c 0x683f0783c00f000f

def z976 : W := mkw 0xebebd5ded0000000 0x3afaf577b4000000 0x7bf3fffcfc000000 0x1efcffff3f000000

def z977 : W := mkw 0x2bebd5ded0000000 0x0afaf577b4000000 0x7bfffffffc000000 0x1effffffff000000

def z978 : W := mkw 0xabe995dfd8000000 0x2afa6577f6000000 0x7bff9ffffc000000 0x1effe7ffff000000

def z979 : W := mkw 0x1343500002409000 0x04d0d40000902400 0x77f3fe0003c3fc03 0x1dfcff8000f0ff00

def z980 : W := mkw 0x0c7196ecc1b26231 0x031c65bb306c988c 0x7af39fece3b0e032 0x5ebce7fb38ec380c

def z981 : W := mkw 0x23a8019a02480088 0x08ea006680920022 0xeffc01ff007c03fc 0xfbff007fc01f00ff

def z982 : W := mkw 0x64fd3e8f493e483c 0x593f4fa3d24f920f 0xa0fc1e0f003c003c 0x683f0783c00f000f

def z983 : W := mkw 0x338ac172b6c9b7c8 0x8ce2b05cadb26df2 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z984 : W := mkw 0x0c7196ece5b36771 0x031c65bb396cd9dc 0x7ef39ffcffb3e3f2 0xdfbce7ff3fecf8fc

def z985 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x13fffff3fc000000 0x04fffffcff000000

def z986 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0xfbfffffffc4c00cc 0x3effffffff130033

def z987 : W := mkw 0x0c7196ece5b36775 0x031c65bb396cd9dd 0xfef39fece3b3e3fe 0xffbce7fb38ecf8ff

def z988 : W := mkw 0x57df7b10037ed880 0x55f7dec400dfb620 0x77fffe1003fffcc3 0x1dffff8400ffff30

def z989 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x7fffffffff83e002 0x1fffffffffe0f800

def z990 : W := mkw 0x0c7192e881b26221 0x031c64ba206c9888 0x22f39fe003b0e002 0x08bce7f800ec3800

def z991 : W := mkw 0x338e69131e4c9ccc 0x8ce39a44c7932733 0x810c60131c4c1ccd 0x20431804c7130733

def z992 : W := mkw 0x082084ece4812775 0x0208213b392049dd 0x880001ece00003fc 0xe200007b380000ff

def z993 : W := mkw 0x0c7196ece5b367f1 0x831c65bb396cd9fc 0x7ef39fece3b3e3f2 0xdfbce7fb38ecf8fc

def z994 : W := mkw 0x04519664e1b36310 0x01146599386cd8c4 0x7ef39fece3b3e332 0xdfbce7fb38ecf8cc

def z995 : W := mkw 0x1410022025b3f771 0x85040088096cfddc 0x0400000003b3ff33 0xc100000000ecffcc

def z996 : W := mkw 0x63ef7d9f48000000 0x18fbdf67d2000000 0x7bfffffffc000000 0x1effffffff000000

def z997 : W := mkw 0x0c753e8d49364835 0x031d4fa3524d920d 0x20f01e0c00300030 0x483c0783000c000c

def z998 : W := mkw 0x0c7194ece1a16321 0x031c653b386858c8 0x7ef39fece383e302 0x9fbce7fb38e0f8c0

def z999 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x7fff9fece3ffe332 0xdfffe7fb38fff8cc

def z1000 : W := mkw 0x00042a0024170d40 0x00010a800905c350 0xfd0c7e1ffc7f1ffd 0xff431f87ff1fc7ff

def z1001 : W := mkw 0xf38e69131e4894c8 0xbce39a44c7922532 0x810c60131c4c1ccd 0x20431804c7130733

def z1002 : W := mkw 0xa82085fffc812775 0x2a08217fff2049dd 0x880001fffc0003fc 0xe200007fff0000ff

def z1003 : W := mkw 0x77df7b12037ed888 0x5df7dec480dfb622 0xfffffe1f03ffffff 0xffffff87c0ffffff

def z1004 : W := mkw 0x4beffddcd0000000 0x12fbff7734000000 0x7bfffffcfc000000 0x1effffff3f000000

def z1005 : W := mkw 0x0c7116ac41b24231 0x031c45ab106c908c 0x7ef39fec03b3e332 0xdfbce7fb00ecf8cc

def z1006 : W := mkw 0x0c7196ecc1b26231 0x031c65bb306c988c 0x76f39fec03b3e032 0x5dbce7fb00ecf80c

def z1007 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0xf7fffe0f03fffc3f 0x7dffff83c0ffff0f

def z1008 : W := mkw 0x082085fdfc8127f5 0x8208217f7f2049fd 0x880001fffc0003fc 0xe200007fff0000ff

def z1009 : W := mkw 0x57db5200037ed800 0x55f6d48000dfb600 0x76f39e0003fffc03 0x1dbce78000ffff00

def z1010 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x76f3fe0003b3fc03 0x1dbcff8000ecff00

def z1011 : W := mkw 0x1302c170b481b740 0x84c0b05c2d206dd0 0x5f03e1f0ff83ff03 0x97c0f87c3fe0ffc0

def z1012 : W := mkw 0x145112000372d000 0x0514448000dcb400 0x76f39e0003f3fc03 0x1dbce78000fcff00

def z1013 : W := mkw 0xebeffddfda400000 0x3afbff77f6900000 0x7fffffffffc00000 0x1ffffffffff00000

def z1014 : W := mkw 0x0c7196ecf5b36771 0x831c65bb3d6cd9dc 0x7ef39fecffb3e332 0xdfbce7fb3fecf8cc

def z1015 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0xfef39fffe3b3e3fe 0xffbce7fff8ecf8ff

def z1016 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x7ff39ffce3f3e3f2 0xdffce7ff38fcf8fc

def z1017 : W := mkw 0x1302c170b6c1b7d4 0x84c0b05c2db06df5 0xdf03e1f0ffc3ffff 0xf7c0f87c3ff0ffff

def z1018 : W := mkw 0x0c7192c881324000 0x031c64b2204c9000 0x76f39fe003b3e002 0x1dbce7f800ecf800

def z1019 : W := mkw 0x57df7a00037ed888 0x55f7de8000dfb622 0xf7fffe0003fffccf 0x3dffff8000ffff33

def z1020 : W := mkw 0x003086ece1b32330 0x000c21bb386cc8cc 0x7ef39fece3b3e332 0xdfbce7fb38ecf8cc

def z1021 : W := mkw 0x145352000132d000 0x0514d480004cb400 0x76f3fe0003b3fc03 0x1dbcff8000ecff00

def z1022 : W := mkw 0xecfd3e8f493e4814 0x7b3f4fa3d24f9205 0xa0fc1e0f003c003c 0x683f0783c00f000f

def z1023 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x29fc7ffffc000000 0x0a7f1fffff000000

def z1024 : W := mkw 0x3ffbd1fa93e8f2a9 0x8ffef47ea4fa3caa 0x02f381e00380e002 0x00bce07800e03800

def z1025 : W := mkw 0xebeff9da90000000 0x3afbfe76a4000000 0x7bfffff0fc000000 0x1efffffc3f000000

def z1026 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x1af39fece383e332 0xc6bce7fb38e0f8cc

def z1027 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0x76f39fe0e3b3e002 0x1dbce7f838ecf800

def z1028 : W := mkw 0x738e69130e4c9ccc 0x5ce39a44c3932733 0x810c60131c4c1ccd 0x20431804c7130733

def z1029 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x7ffffe10fffffc03 0x1fffff843fffff00

def z1030 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x1af3fffffc000000 0x06bcffffff000000

def z1031 : W := mkw 0xe8effccfd8000000 0x3a3bff33f6000000 0x7affffeffc000000 0x1ebffffbff000000

def z1032 : W := mkw 0x082084ece48127f1 0x8208213b392049fc 0x080001ece00003f0 0xc200007b380000fc

def z1033 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x7ffffe1003ffffc3 0x9fffff8400fffff0

def z1034 : W := mkw 0xe3ba41ba13e802a8 0x38ee906e84fa00aa 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z1035 : W := mkw 0xebedbddfd8000000 0x3afb6f77f6000000 0x6bfc1ffffc000000 0x1aff07ffff000000

def z1036 : W := mkw 0x0c7196ccc1324031 0x031c65b3304c900c 0x7ef39fece3b3e032 0x5fbce7fb38ecf80c

def z1037 : W := mkw 0xe8edbddfd8000000 0x3a3b6f77f6000000 0x7aff9ffffc000000 0x1ebfe7ffff000000

def z1038 : W := mkw 0x53df780003689000 0x14f7de0000da2400 0x77fffe0003fffc03 0x1dffff8000ffff00

def z1039 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x7ffffffffc7c0000 0x1fffffffff1f0000

def z1040 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x1603e1e0ffc3ffc3 0x8580f8783ff0fff0

def z1041 : W := mkw 0x338ac172b6c1b7c0 0x8ce2b05cadb06df0 0x5f0fe1f3ffc3ffc3 0x97c3f87cfff0fff0

def z1042 : W := mkw 0x17db5200037ad000 0x05f6d48000deb400 0x77fffe0003fffc03 0x1dffff8000ffff00

def z1043 : W := mkw 0x23ba41ba03e802a8 0x08ee906e80fa00aa 0xffffe1ff03fc03fc 0xfffff87fc0ff00ff

def z1044 : W := mkw 0x33ba41ba03e892a8 0x0cee906e80fa24aa 0xeffc61ff03fc1ffd 0xfbff187fc0ff07ff

def z1045 : W := mkw 0x33b801ba03e8b2a8 0x8cee006e80fa2caa 0xeffc01ff03fce3fe 0xfbff007fc0ff38ff

def z1046 : W := mkw 0x00008170b48127c0 0x8000205c2d2049f0 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z1047 : W := mkw 0x0c7194ccc1204000 0x031c653330481000 0x7af39fece380e002 0x1ebce7fb38e03800

def z1048 : W := mkw 0xe8edbddfd8000000 0x3a3b6f77f6000000 0x79fc7ffffc000000 0x1e7f1fffff000000

def z1049 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0xfbfffffffc3c003c 0x7effffffff0f000f

def z1050 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x7ffffffffc431c01 0x1fffffffff10c700

def z1051 : W := mkw 0xa82085fffc8127d4 0xaa08217fff2049f5 0x880001fffc0003fc 0xe200007fff0000ff

def z1052 : W := mkw 0x23ba41ba13e802a8 0x08ee906e84fa00aa 0xeffc61ff1ffc03fc 0xfbff187fc7ff00ff

def z1053 : W := mkw 0xd7df7a011b7ed800 0x75f7de8046dfb600 0x77fffe001ffffc03 0x1dffff8007ffff00

def z1054 : W := mkw 0x0c6196ece0936311 0x031865bb3824d8c4 0x7ef39fece383e302 0x9fbce7fb38e0f8c0

def z1055 : W := mkw 0x1302c150b6419540 0x04c0b0542d906550 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z1056 : W := mkw 0x1410022027f7fff5 0x8504008809fdfffd 0x8400000003ffffff 0xe100000000ffffff

def z1057 : W := mkw 0x139e6a00037e9800 0x04e79a8000dfa600 0x77fffe0003fffc03 0x1dffff8000ffff00

def z1058 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x7ffffffffc300330 0xdfffffffff0c00cc

def z1059 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x7f0fe1ffffc3ffc3 0x9fc3f87ffff0fff0

def z1060 : W := mkw 0xfbeffddfda489000 0x7efbff77f6922400 0x7bfffffffc000000 0x1effffffff000000

def z1061 : W := mkw 0x1002c170b6c1b7c0 0x8400b05c2db06df0 0x1c03e1f0ffc3ffc3 0x8700f87c3ff0fff0

def z1062 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0x26ff9e0003fffc03 0x09bfe78000ffff00

def z1063 : W := mkw 0x77df7a02037ed808 0x5df7de8080dfb602 0xf7fffe0303fffc0f 0x3dffff80c0ffff03

def z1064 : W := mkw 0x538e6910164094c0 0x94e39a4405902530 0x010c60101c401cc1 0x0043180407100730

def z1065 : W := mkw 0x33ba41ba13e892a8 0x8cee906e84fa24aa 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z1066 : W := mkw 0x57df7a00037ed800 0x55f7de8000dfb600 0xf7fffe1303fffccf 0x3dffff84c0ffff33

def z1067 : W := mkw 0x086194ece0812331 0x0218653b382048cc 0x7ef39fece383e332 0xdfbce7fb38e0f8cc

def z1068 : W := mkw 0xc867fccdd8000000 0x3219ff3376000000 0x7bfffffffc000000 0x1effffffff000000

def z1069 : W := mkw 0x73ba41ba03e892a8 0x5cee906e80fa24aa 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z1070 : W := mkw 0x57df7b10037ed800 0x55f7dec400dfb600 0x7ffffff003fffc03 0x1ffffffc00ffff00

def z1071 : W := mkw 0x738e6912164c9cc8 0xdce39a4485932732 0x810c60131c4c1ccd 0x20431804c7130733

def z1072 : W := mkw 0x2c7196eee1b36339 0x0b1c65bbb86cd8ce 0xfef39fefe3b3e33e 0xffbce7fbf8ecf8cf

def z1073 : W := mkw 0x0c7196cce1334110 0x031c65b3384cd044 0x7ef39fece3b3e332 0xdfbce7fb38ecf8cc

def z1074 : W := mkw 0x33ba41ba03e892a8 0x0cee906e80fa24aa 0xefff81ff03fce3fe 0xfbffe07fc0ff38ff

def z1075 : W := mkw 0x0471128801324000 0x011c44a2004c9000 0x7ef39fec03b3e002 0x1fbce7fb00ecf800

def z1076 : W := mkw 0xebeffddfd8000014 0x3afbff77f6000005 0xfbfffffffc00003c 0x7effffffff00000f

def z1077 : W := mkw 0x00008060a4812740 0x00002018292049d0 0x5e03e1e0ff83ff03 0x9780f8783fe0ffc0

def z1078 : W := mkw 0x54dd3a00037ed800 0x55374e8000dfb600 0x76ff9e0003fffc03 0x1dbfe78000ffff00

def z1079 : W := mkw 0x033001b803e002a0 0x00cc006e00f800a8 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z1080 : W := mkw 0x77df7b12037ed888 0x5df7dec480dfb622 0x77fffe0003fffc03 0x1dffff8000ffff00

def z1081 : W := mkw 0x0c7196ece1b76b31 0x031c65bb386ddacc 0x7ef39fece3ffff33 0xdfbce7fb38ffffcc

def z1082 : W := mkw 0x23a801ba02c00280 0x08ea006e80b000a0 0xeffc01ff03fc03fc 0xfbff007fc0ff00ff

def z1083 : W := mkw 0x57db5200037ad000 0x55f6d48000deb400 0x77f3fe0003f3fc03 0x1dfcff8000fcff00

def z1084 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0xaafc01ff03bc03fc 0xeabf007fc0ef00ff

def z1085 : W := mkw 0xf38e69131e4c9c44 0x7ce39a44c7932711 0x810c60131c4c1ccd 0x20431804c7130733

def z1086 : W := mkw 0x1002c060b481b740 0x8400b0182d206dd0 0x5f03e1f0ffc3ffc3 0x97c0f87c3ff0fff0

def z1087 : W := mkw 0x3302c172b6c1b7c8 0x8cc0b05cadb06df2 0xdf03e1f3ffc3ffcf 0xb7c0f87cfff0fff3

def z1088 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0xdf0fe1f3ffcfffcf 0xb7c3f87cfff3fff3

def z1089 : W := mkw 0x0c7196ece5b76f75 0x031c65bb396ddbdd 0xfff3fffcffffffff 0xfffcffff3fffffff

def z1090 : W := mkw 0x086195dcd0000000 0x0218657734000000 0x7af39ffcfc000000 0x1ebce7ff3f000000

def z1091 : W := mkw 0x07dd3a00037e4800 0x01f74e8000df9200 0x77fffe0003fffc03 0x1dffff8000ffff00

def z1092 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x7ffffffffc4003c0 0x9fffffffff1000f0

def z1093 : W := mkw 0x0c7196ece1b36331 0x031c65bb386cd8cc 0xfeff9fefe3bfe33e 0xffbfe7fbf8eff8cf

def z1094 : W := mkw 0x23b801ba03e802a8 0x08ee006e80fa00aa 0xa9fc01ff007c03fc 0xea7f007fc01f00ff

def z1095 : W := mkw 0x0020008800000000 0x0008002200000000 0xeffc01ff007c03fc 0xfbff007fc01f00ff

def z1096 : W := mkw 0x1302c150b641b540 0x84c0b0542d906d50 0x5f03e1f0ffc3fc03 0x17c0f87c3ff0ff00

def z1097 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0xdf03e1f0ffffffff 0xf7c0f87c3fffffff

def z1098 : W := mkw 0x54577a00037ed800 0x5515de8000dfb600 0x76f3fe0003fffc03 0x1dbcff8000ffff00

def z1099 : W := mkw 0xf38e69131e4c9cc0 0xfce39a44c7932730 0x010c60131c4c1cc1 0x00431804c7130730

def z1100 : W := mkw 0x538e6910124c9880 0xd4e39a4404932620 0x010c6000004c1c01 0x0043180000130700

def z1101 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x73ffffe0fc000000 0x1cfffff83f000000

def z1102 : W := mkw 0x1302c170b6c1b7c0 0x84c0b05c2db06df0 0x5b03e1f0ff83fc03 0x16c0f87c3fe0ff00

def z1103 : W := mkw 0x23a801ba008002a8 0x08ea006e802000aa 0xeffc01ff007c03fc 0xfbff007fc01f00ff

def z1104 : W := mkw 0x0410022025b367f1 0x81040088096cd9fc 0x0400000003b3e3f2 0xc100000000ecf8fc

def z1105 : W := mkw 0x0c7196ededb36775 0x031c65bb7b6cd9dd 0xfff3fffffff3ffff 0xfffcfffffffcffff

def z1106 : W := mkw 0xebeffddfd8000000 0x3afbff77f6000000 0x2aff9ffffc000000 0x0abfe7ffff000000

def z1107 : W := mkw 0xa82085fffc8127f1 0xaa08217fff2049fc 0x080001fffc0003f0 0xc200007fff0000fc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z7,z4,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z9]),(0,[z10,z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z12,z6]),(0,[z1,z13,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z14,z5,z6]),(0,[z15,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z16,z4,z5,z6])],[(0,[z17,z1,z18,z3,z4,z5,z6]),(0,[z1,z19,z18,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z20,z6]),(0,[z1,z2,z3,z21,z4,z5,z6]),(0,[z1,z2,z22,z3,z4,z5,z6])],[],[(0,[z23,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z4,z5,z24]),(0,[z1,z25,z26,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z27,z5,z6]),(0,[z1,z28,z2,z3,z4,z29,z6]),(0,[z1,z2,z3,z4,z5,z6,z30])],[(0,[z1,z31,z2,z18,z3,z4,z5]),(0,[z1,z32,z2,z3,z4,z5,z6]),(0,[z1,z2,z33,z4,z5,z34,z6])],[(0,[z1,z2,z3,z35,z4,z5,z6]),(0,[z1,z36,z2,z3,z4,z5,z6]),(0,[z1,z37,z3,z4,z5,z34,z6]),(0,[z38,z1,z2,z3,z4,z5,z6])],[(1,[z1,z39,z2,z3,z4,z5]),(0,[z40,z1,z2,z3,z4,z5,z6]),(0,[z1,z41,z2,z3,z4,z5,z6]),(0,[z42,z1,z2,z3,z4,z5,z6]),(0,[z1,z43,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z44,z6]),(0,[z1,z2,z3,z4,z5,z45,z6]),(0,[z1,z2,z3,z4,z46,z5,z6])],[(0,[z1,z2,z3,z47,z4,z5,z6]),(0,[z1,z2,z48,z3,z4,z5,z6]),(0,[z1,z49,z2,z3,z4,z5,z6]),(0,[z50,z1,z2,z51,z4,z5,z6]),(0,[z1,z25,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z52]),(0,[z1,z53,z2,z3,z4,z5,z6])],[(0,[z1,z49,z2,z54,z4,z5,z6])],[(0,[z55,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z56,z5,z6]),(0,[z57,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z58,z4,z5,z6])],[],[(0,[z1,z2,z59,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z60,z6]),(0,[z61,z1,z19,z2,z3,z4,z6]),(1,[z1,z2,z3,z62,z4,z6]),(0,[z1,z2,z63,z3,z4,z5,z6]),(0,[z1,z2,z33,z3,z4,z5,z64]),(0,[z1,z2,z3,z4,z5,z65,z6])],[(0,[z1,z2,z3,z4,z5,z66,z6]),(0,[z1,z67,z3,z4,z5,z68,z6]),(0,[z1,z19,z28,z3,z4,z5,z6]),(0,[z1,z69,z2,z3,z4,z5,z70]),(0,[z1,z71,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z72]),(0,[z1,z2,z3,z4,z5,z6,z73]),(0,[z1,z2,z3,z4,z74,z6,z75]),(0,[z76,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z77,z6]),(0,[z1,z78,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z79,z5,z6]),(0,[z1,z2,z3,z4,z5,z80,z6]),(0,[z1,z2,z3,z4,z5,z81,z6])],[(0,[z1,z2,z3,z4,z5,z82,z6]),(0,[z1,z2,z3,z4,z5,z6,z83]),(0,[z1,z2,z3,z4,z5,z84,z6]),(0,[z1,z2,z3,z4,z5,z85,z6])],[(1,[z86,z2,z87,z4,z5,z6]),(0,[z1,z2,z3,z4,z88,z5,z6]),(0,[z89,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z90,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z91,z6]),(0,[z1,z2,z54,z3,z92,z5,z6]),(0,[z1,z2,z3,z93,z4,z5,z6]),(0,[z1,z2,z94,z3,z4,z5,z6]),(0,[z1,z2,z95,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z96,z5,z6]),(0,[z97,z1,z28,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z98,z6])],[(0,[z1,z2,z87,z4,z99,z5,z6]),(1,[z61,z2,z3,z4,z88,z6])],[(0,[z1,z100,z2,z3,z4,z5,z6]),(0,[z101,z1,z2,z3,z4,z5,z6]),(0,[z101,z1,z2,z3,z4,z88,z6]),(1,[z1,z2,z3,z102,z5,z6]),(1,[z1,z26,z3,z103,z5,z6])],[(0,[z104,z1,z2,z3,z4,z5,z6]),(0,[z1,z105,z3,z4,z5,z68,z6]),(0,[z1,z2,z106,z3,z4,z5,z6]),(0,[z1,z2,z3,z107,z4,z5,z6]),(0,[z1,z2,z3,z92,z4,z5,z6]),(0,[z1,z108,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z109,z5,z6])]],
   [[(0,[z1,z69,z105,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z110,z5,z6]),(0,[z1,z2,z111,z3,z4,z5,z83]),(0,[z1,z2,z3,z112,z4,z5,z6]),(0,[z1,z2,z3,z4,z74,z5,z6])],[(0,[z1,z2,z3,z4,z5,z113,z6]),(0,[z1,z2,z3,z4,z5,z114,z6]),(0,[z1,z2,z115,z3,z4,z5,z6]),(0,[z1,z2,z111,z3,z116,z4,z5])],[(0,[z1,z2,z3,z117,z4,z5,z6]),(1,[z1,z49,z67,z4,z5,z6]),(0,[z1,z26,z2,z3,z118,z5,z6]),(0,[z1,z2,z4,z119,z5,z34,z6]),(1,[z1,z120,z2,z3,z5,z121])],[(0,[z1,z122,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z123,z6]),(0,[z1,z2,z3,z4,z5,z124,z6])],[(0,[z1,z49,z18,z3,z4,z5,z6]),(1,[z1,z125,z2,z3,z5,z6]),(0,[z86,z2,z3,z87,z4,z5,z6]),(0,[z1,z126,z2,z3,z4,z5,z6]),(0,[z1,z108,z126,z2,z3,z4,z5]),(0,[z127,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z128,z6])],[(0,[z129,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z130,z3,z4,z5,z6]),(0,[z1,z126,z2,z111,z3,z4,z5]),(0,[z1,z131,z2,z3,z4,z132,z6])],[(0,[z133,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z134,z5,z6]),(1,[z1,z2,z3,z5,z135,z6]),(0,[z136,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z137,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z138,z5,z6]),(1,[z1,z2,z63,z4,z5,z6]),(0,[z1,z2,z3,z4,z139,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z140,z5,z6]),(0,[z1,z141,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z142,z6]),(0,[z1,z2,z3,z4,z143,z5,z6]),(0,[z1,z2,z3,z4,z5,z144,z6])],[(0,[z1,z145,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z146,z5,z6]),(0,[z1,z147,z2,z3,z4,z5,z6])],[(0,[z1,z18,z3,z4,z5,z68,z6]),(0,[z57,z1,z2,z3,z5,z121,z6]),(0,[z1,z2,z3,z4,z5,z148,z6])],[(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z150,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z151]),(0,[z1,z2,z3,z152,z4,z5,z6]),(0,[z1,z2,z3,z4,z119,z5,z6]),(0,[z1,z2,z3,z4,z153,z5,z6]),(0,[z1,z2,z3,z4,z154,z5,z6])],[(0,[z61,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z155,z5,z6]),(0,[z1,z120,z2,z3,z156,z5,z6])],[(0,[z2,z3,z4,z88,z5,z157,z6]),(0,[z1,z28,z2,z3,z4,z158,z6])],[(0,[z57,z2,z3,z7,z4,z5,z6]),(0,[z1,z159,z2,z3,z4,z5,z6]),(0,[z1,z160,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z19,z2,z3,z4,z6,z75]),(0,[z1,z2,z3,z4,z5,z6,z161]),(0,[z97,z1,z2,z4,z119,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z162]),(0,[z1,z2,z3,z4,z5,z163,z6]),(0,[z1,z2,z3,z4,z164,z5,z6]),(0,[z165,z1,z2,z3,z4,z5,z6])],[(1,[z40,z2,z166,z4,z5,z6]),(0,[z1,z2,z3,z158,z5,z132,z6])],[(1,[z1,z167,z3,z4,z5,z6]),(0,[z1,z19,z2,z33,z3,z4,z6]),(0,[z1,z168,z2,z3,z4,z5,z6])],[(0,[z1,z2,z169,z3,z4,z5,z6]),(0,[z1,z2,z170,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z121,z11]),(0,[z1,z171,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z172,z4,z5,z6]),(0,[z97,z1,z19,z2,z3,z4,z6]),(0,[z1,z3,z4,z5,z68,z6,z173]),(0,[z1,z108,z2,z4,z5,z6,z83]),(0,[z1,z174,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z175,z6]),(0,[z1,z2,z3,z4,z176,z5,z6]),(1,[z1,z2,z3,z4,z5,z64])],[(0,[z177,z1,z2,z3,z4,z5,z6]),(0,[z1,z178,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z179,z4,z5,z6]),(0,[z1,z2,z33,z3,z4,z74,z6]),(0,[z1,z2,z3,z180,z4,z5,z6]),(0,[z1,z2,z3,z181,z4,z5,z6]),(0,[z1,z182,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z70,z6]),(1,[z1,z3,z4,z5,z6,z183])],[(0,[z1,z184,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z185])]],
   [[(0,[z1,z2,z3,z4,z186,z5,z6]),(0,[z1,z2,z3,z187,z4,z5,z6]),(0,[z1,z2,z3,z4,z188,z5,z6]),(0,[z10,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z121,z24]),(0,[z1,z189,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z19,z2,z3,z4,z5,z6]),(0,[z190,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z191]),(0,[z1,z192,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z193,z4,z5,z6]),(0,[z1,z194,z2,z4,z99,z5,z6]),(0,[z1,z2,z54,z3,z99,z5,z6]),(1,[z1,z2,z3,z58,z4,z5]),(0,[z1,z2,z195,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z196,z5,z6]),(0,[z1,z2,z3,z197,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z3,z198,z4,z5,z6]),(0,[z1,z194,z2,z3,z4,z5,z6])],[(0,[z1,z2,z199,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z200]),(0,[z1,z2,z3,z4,z5,z6,z201])],[(0,[z202,z1,z2,z3,z7,z5,z6]),(0,[z203,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z204,z5,z6]),(0,[z1,z108,z2,z3,z4,z74,z5])],[(0,[z205,z1,z2,z3,z4,z5,z6]),(1,[z10,z2,z3,z4,z5,z11]),(0,[z97,z1,z2,z3,z4,z119,z6]),(0,[z1,z3,z4,z5,z6,z183,z75])],[(0,[z1,z2,z206,z3,z4,z5,z6]),(1,[z50,z1,z51,z4,z5,z6]),(0,[z207,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z208,z5,z6]),(0,[z1,z2,z3,z4,z209,z5,z6]),(0,[z1,z2,z3,z4,z210,z5,z6]),(0,[z97,z1,z2,z3,z4,z74,z6]),(0,[z1,z2,z3,z4,z211,z5,z6])],[(0,[z1,z212,z2,z3,z4,z5,z6]),(0,[z61,z1,z28,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z213,z6]),(0,[z1,z2,z214,z3,z4,z5,z6]),(0,[z1,z126,z2,z3,z4,z5,z68]),(0,[z1,z215,z2,z3,z4,z5,z6]),(0,[z1,z216,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z217,z6]),(0,[z218,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z219,z6]),(0,[z1,z2,z111,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z220,z5,z6]),(0,[z221,z1,z2,z3,z4,z5,z6])],[(0,[z105,z2,z18,z3,z4,z5,z6]),(0,[z1,z2,z54,z166,z4,z5,z6]),(0,[z1,z25,z3,z4,z29,z5,z6]),(0,[z222,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z223,z4,z5,z6])],[(0,[z224,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z225,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z226]),(0,[z1,z2,z3,z4,z5,z142,z6]),(0,[z1,z2,z3,z156,z4,z5,z121])],[(0,[z1,z227,z2,z3,z4,z5,z6]),(1,[z1,z228,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z229,z6])],[(0,[z1,z2,z3,z4,z230,z5,z6])],[(0,[z231,z1,z2,z3,z4,z5,z6]),(1,[z1,z232,z3,z4,z5,z6]),(0,[z233,z1,z2,z3,z4,z5,z6]),(0,[z1,z108,z2,z4,z119,z5,z6])]],
   [[(0,[z1,z234,z2,z3,z4,z5,z6]),(0,[z86,z1,z49,z2,z4,z5,z6]),(0,[z235,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z236,z5,z6])],[(0,[z237,z1,z2,z3,z4,z5,z6]),(0,[z1,z238,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z239,z4,z5,z6]),(0,[z50,z1,z2,z67,z4,z5,z6]),(0,[z1,z2,z3,z156,z5,z6,z240])],[(0,[z1,z241,z2,z18,z3,z4,z6]),(0,[z1,z2,z3,z242,z4,z5,z6]),(0,[z1,z2,z33,z3,z243,z5,z6]),(0,[z1,z244,z3,z4,z5,z6,z83])],[(0,[z50,z1,z3,z4,z29,z5,z6]),(0,[z97,z1,z2,z3,z4,z5,z6]),(0,[z1,z245,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z246,z4,z5,z6])],[(0,[z1,z49,z2,z51,z4,z5,z6]),(0,[z1,z2,z3,z247,z4,z5,z6])],[(0,[z1,z100,z2,z18,z3,z4,z6]),(0,[z1,z2,z3,z248,z4,z8,z5]),(0,[z1,z2,z3,z249,z4,z5,z6]),(0,[z1,z2,z3,z103,z4,z5,z6]),(0,[z250,z1,z2,z3,z4,z5,z6]),(0,[z1,z251,z2,z3,z4,z5,z6])],[(0,[z252,z1,z2,z3,z4,z5,z6]),(0,[z1,z69,z2,z3,z4,z5,z173]),(1,[z1,z108,z2,z4,z5,z83])],[(0,[z253,z1,z2,z3,z4,z5,z6]),(0,[z1,z254,z2,z3,z4,z5,z6]),(0,[z1,z126,z2,z3,z4,z5,z121]),(0,[z1,z2,z3,z4,z5,z255,z6])]],
   [[(1,[z1,z2,z256,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z257]),(0,[z1,z2,z3,z4,z5,z258,z6]),(0,[z1,z2,z3,z4,z5,z6,z259]),(0,[z260,z1,z2,z3,z4,z5,z6]),(0,[z261,z1,z2,z3,z4,z5,z6])],[(0,[z1,z262,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z263,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z264]),(0,[z1,z2,z3,z4,z5,z265,z6]),(0,[z1,z266,z2,z3,z4,z5,z6]),(0,[z267,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z7,z4,z5,z6]),(0,[z1,z2,z3,z268,z4,z5,z6]),(0,[z1,z269,z2,z3,z4,z5,z6])],[(0,[z1,z2,z270,z3,z4,z5,z6]),(0,[z1,z49,z2,z4,z99,z5,z6]),(0,[z1,z271,z2,z3,z4,z5,z6]),(0,[z1,z25,z2,z3,z118,z5,z6]),(0,[z1,z131,z2,z3,z4,z158,z6]),(0,[z1,z2,z3,z4,z5,z272,z6])],[(0,[z1,z2,z3,z4,z5,z273,z6]),(0,[z1,z2,z3,z5,z135,z6,z11])],[(0,[z274,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z275,z6]),(0,[z1,z2,z3,z276,z4,z5,z6]),(0,[z1,z277,z2,z3,z4,z5,z6]),(0,[z1,z3,z103,z4,z118,z5,z6])],[(0,[z1,z2,z3,z278,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z279,z6]),(0,[z1,z2,z3,z4,z280,z5,z6]),(0,[z1,z281,z2,z3,z4,z5,z6]),(0,[z282,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z283,z4,z5,z6]),(0,[z1,z2,z3,z4,z284,z5,z6]),(0,[z1,z2,z3,z4,z5,z70,z83]),(0,[z1,z131,z2,z3,z246,z5,z6])]],
   [[(0,[z285,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z286,z4,z5,z6]),(0,[z1,z2,z3,z4,z29,z5,z287]),(0,[z1,z288,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z74,z5,z75])],[(0,[z1,z2,z3,z4,z5,z6,z289]),(0,[z290,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z291,z3,z4,z5,z6]),(0,[z1,z2,z292,z3,z4,z5,z6]),(0,[z1,z2,z293,z3,z4,z5,z6]),(0,[z1,z294,z2,z3,z4,z5,z6])],[(0,[z295,z1,z2,z3,z4,z5,z6]),(0,[z296,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z297,z5,z6])],[],[(0,[z1,z2,z3,z102,z4,z5,z6]),(0,[z55,z1,z126,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z68,z6])],[(1,[z1,z298,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z299,z6]),(0,[z1,z2,z3,z4,z300,z5,z6]),(0,[z1,z126,z2,z3,z4,z5,z75]),(0,[z1,z2,z3,z156,z4,z5,z6])],[(0,[z1,z241,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z301,z5,z6]),(0,[z1,z2,z3,z4,z5,z302,z6]),(0,[z1,z303,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z304,z6])],[(0,[z2,z166,z3,z87,z4,z5,z6]),(0,[z1,z2,z3,z4,z305,z5,z6]),(1,[z1,z306,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z307,z6]),(0,[z1,z2,z3,z4,z308,z5,z6]),(0,[z1,z2,z63,z103,z4,z5,z6]),(0,[z1,z2,z309,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z310,z2,z3,z4,z5,z6]),(0,[z311,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z111,z3,z4,z74,z5]),(0,[z1,z2,z3,z4,z312,z5,z6])],[(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z313,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z314,z6])],[],[(0,[z1,z2,z3,z315,z4,z5,z6]),(0,[z1,z2,z3,z4,z88,z132,z6]),(0,[z50,z1,z3,z51,z4,z5,z6]),(0,[z1,z2,z3,z4,z316,z5,z6])],[(0,[z1,z2,z3,z317,z4,z5,z6]),(0,[z55,z10,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z318]),(0,[z319,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z320,z6]),(0,[z1,z2,z3,z4,z5,z6,z321]),(0,[z1,z322,z2,z3,z4,z5,z6]),(0,[z1,z323,z2,z3,z4,z5,z6]),(0,[z1,z2,z324,z3,z4,z5,z6]),(0,[z1,z2,z3,z103,z4,z265,z6]),(0,[z325,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z326,z5,z6])],[(0,[z1,z2,z327,z3,z4,z5,z6]),(0,[z1,z105,z3,z4,z118,z5,z6]),(0,[z202,z1,z306,z3,z4,z5,z6]),(0,[z1,z328,z2,z3,z4,z5,z6]),(0,[z1,z329,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z330]),(0,[z202,z1,z2,z3,z4,z5,z6]),(0,[z57,z1,z2,z3,z156,z5,z6]),(0,[z1,z2,z3,z4,z5,z331,z6]),(0,[z1,z2,z3,z4,z332,z5,z6]),(0,[z1,z2,z3,z62,z4,z5,z6]),(0,[z1,z333,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z334,z5,z6])]],
   [[(0,[z50,z1,z49,z3,z4,z5,z6])],[(0,[z274,z1,z18,z3,z4,z5,z6]),(0,[z1,z335,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z336,z5,z6]),(0,[z1,z2,z3,z337,z4,z5,z6])],[(0,[z86,z1,z2,z87,z4,z5,z6]),(0,[z101,z1,z2,z3,z4,z157,z6]),(0,[z1,z2,z3,z338,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z135,z6]),(0,[z1,z2,z3,z339,z4,z5,z6])],[(0,[z340,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z287])],[(0,[z1,z341,z2,z3,z4,z5,z6]),(0,[z1,z69,z67,z3,z4,z5,z6]),(0,[z1,z2,z342,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z83,z75])],[(0,[z1,z2,z3,z4,z5,z343,z6]),(1,[z1,z2,z344,z4,z5,z6]),(0,[z1,z2,z3,z4,z345,z5,z6]),(0,[z1,z28,z2,z3,z116,z4,z6])],[(0,[z1,z2,z3,z346,z4,z5,z6]),(0,[z1,z2,z3,z4,z347,z5,z6]),(0,[z1,z2,z3,z4,z348,z5,z6])]],
   [[(0,[z202,z1,z25,z2,z3,z5,z6]),(0,[z61,z1,z2,z3,z4,z88,z6]),(0,[z1,z2,z3,z4,z5,z349,z6])],[(0,[z1,z18,z3,z4,z118,z5,z6]),(0,[z350,z1,z2,z3,z4,z5,z6])],[(0,[z202,z1,z2,z3,z4,z142,z6]),(0,[z1,z2,z3,z351,z4,z5,z6]),(0,[z1,z19,z2,z3,z4,z352,z6]),(0,[z1,z2,z3,z4,z5,z352,z6]),(1,[z97,z1,z2,z4,z119,z6]),(0,[z1,z2,z3,z353,z4,z5,z6])],[(0,[z354,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z355]),(0,[z1,z2,z3,z4,z5,z356,z6]),(0,[z1,z2,z3,z4,z5,z6,z75])],[(0,[z1,z2,z3,z4,z5,z24,z6])],[(0,[z1,z105,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z257]),(0,[z1,z2,z3,z4,z357,z5,z6]),(0,[z1,z358,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z268,z4,z68,z6])],[(0,[z359,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z360,z6,z83]),(0,[z1,z361,z2,z3,z4,z5,z6])],[(0,[z1,z26,z105,z3,z4,z5,z6]),(0,[z1,z362,z2,z3,z4,z5,z6]),(0,[z57,z1,z2,z3,z7,z5,z6]),(0,[z363,z1,z2,z3,z4,z5,z6]),(0,[z1,z364,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z4,z265,z6]),(1,[z1,z2,z33,z4,z34,z6])],[(0,[z1,z2,z3,z4,z5,z365,z6]),(0,[z1,z2,z3,z366,z4,z5,z6]),(0,[z1,z367,z2,z3,z4,z5,z6]),(1,[z1,z194,z2,z99,z5,z6]),(0,[z1,z2,z3,z4,z368,z5,z6])],[(0,[z61,z1,z2,z3,z4,z157,z6]),(1,[z1,z2,z3,z276,z4,z5]),(0,[z1,z369,z2,z3,z4,z5,z6]),(0,[z1,z126,z2,z3,z4,z5,z240])],[(0,[z1,z2,z3,z4,z5,z370,z6]),(1,[z1,z2,z3,z4,z143,z6]),(0,[z1,z2,z3,z4,z5,z6,z371]),(0,[z1,z26,z3,z103,z4,z5,z6]),(0,[z1,z2,z3,z4,z372,z5,z6]),(0,[z1,z2,z3,z4,z373,z5,z34]),(1,[z1,z2,z111,z4,z5,z374]),(0,[z1,z2,z3,z116,z4,z5,z70])],[(0,[z202,z1,z2,z3,z4,z5,z257])],[(0,[z202,z1,z167,z3,z4,z5,z6]),(0,[z375,z1,z2,z3,z4,z5,z6])],[(0,[z1,z376,z2,z3,z4,z5,z6]),(0,[z1,z108,z2,z111,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z377,z83]),(0,[z1,z2,z3,z4,z5,z378,z6])],[(0,[z86,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z379,z3,z4,z5,z6])]],
   [[(0,[z55,z2,z3,z4,z5,z24,z6]),(0,[z380,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z381])],[(0,[z10,z1,z126,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z382]),(0,[z1,z2,z383,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z384,z5,z6])],[(0,[z385,z1,z2,z3,z4,z5,z6]),(0,[z1,z386,z2,z3,z4,z5,z6]),(0,[z55,z1,z2,z3,z156,z4,z5]),(0,[z1,z19,z2,z3,z4,z132,z6]),(0,[z1,z3,z4,z29,z5,z68,z6]),(0,[z1,z2,z3,z4,z387,z5,z6]),(0,[z1,z2,z3,z4,z388,z5,z6]),(0,[z1,z2,z3,z4,z5,z132,z6])],[(0,[z1,z2,z3,z4,z389,z5,z6]),(0,[z61,z2,z3,z4,z88,z5,z6]),(0,[z1,z2,z3,z92,z5,z132,z6])],[(0,[z1,z39,z2,z3,z4,z5,z6]),(0,[z1,z2,z54,z87,z4,z5,z6]),(0,[z1,z49,z2,z67,z4,z5,z6]),(0,[z1,z2,z3,z4,z390,z5,z6]),(0,[z1,z391,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z392,z5,z6])],[(0,[z1,z2,z3,z393,z4,z5,z6]),(0,[z394,z1,z2,z3,z4,z5,z6]),(0,[z1,z395,z2,z3,z4,z5,z6]),(0,[z1,z396,z2,z3,z4,z5,z6]),(0,[z1,z397,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z398,z6]),(0,[z1,z2,z3,z4,z399,z5,z6]),(0,[z1,z2,z3,z4,z5,z64,z6]),(0,[z1,z2,z3,z400,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z157,z6]),(0,[z1,z401,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z402]),(0,[z1,z2,z403,z3,z4,z5,z6]),(0,[z1,z2,z404,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z405,z132,z6])],[]],
   [[(0,[z1,z2,z3,z4,z5,z6,z183])],[(0,[z1,z69,z2,z3,z4,z5,z6]),(0,[z406,z1,z2,z3,z4,z5,z6]),(0,[z1,z407,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z408,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z409])],[(0,[z1,z298,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z410,z6]),(0,[z411,z1,z2,z3,z4,z5,z6]),(0,[z1,z69,z2,z111,z3,z4,z5]),(0,[z1,z412,z2,z3,z4,z5,z6]),(0,[z1,z2,z95,z4,z5,z6,z75])],[(0,[z1,z2,z33,z4,z5,z374,z6]),(1,[z1,z3,z4,z5,z6,z377])],[(1,[z57,z2,z3,z7,z5,z6])],[(0,[z17,z1,z105,z3,z4,z5,z6]),(0,[z413,z1,z2,z3,z4,z5,z6]),(0,[z1,z414,z2,z3,z4,z5,z6]),(0,[z1,z19,z2,z3,z4,z29,z6]),(0,[z415,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z74,z75])],[(1,[z1,z31,z2,z3,z4,z5]),(0,[z1,z2,z416,z3,z4,z5,z6]),(1,[z1,z362,z2,z3,z4,z5]),(0,[z1,z2,z3,z417,z4,z5,z6]),(0,[z1,z2,z3,z418,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z419]),(1,[z1,z19,z3,z4,z352,z6]),(0,[z1,z2,z3,z4,z5,z420,z6]),(1,[z1,z421,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z422,z5,z6]),(0,[z1,z2,z3,z423,z4,z5,z6]),(0,[z1,z424,z2,z3,z4,z5,z6]),(0,[z1,z425,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z240])],[(0,[z426,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z5,z6]),(0,[z427,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z287]),(0,[z1,z2,z428,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z429]),(0,[z1,z2,z3,z4,z5,z374,z6])],[(0,[z1,z430,z2,z3,z4,z5,z6]),(0,[z202,z1,z26,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z431,z6]),(0,[z1,z2,z3,z4,z5,z6,z432])],[(0,[z1,z2,z256,z3,z4,z5,z6]),(1,[z1,z2,z3,z246,z158,z6])],[(0,[z1,z2,z433,z3,z4,z5,z6]),(0,[z1,z2,z3,z246,z4,z132,z6])],[(0,[z1,z2,z434,z3,z4,z5,z6]),(0,[z1,z2,z3,z435,z4,z5,z6]),(0,[z1,z2,z33,z3,z4,z34,z6])],[(0,[z1,z436,z2,z3,z4,z5,z6]),(0,[z1,z2,z67,z3,z4,z5,z6]),(0,[z1,z3,z103,z4,z29,z5,z6]),(0,[z1,z2,z3,z4,z5,z437,z6]),(0,[z1,z2,z438,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z360,z5,z6]),(1,[z1,z3,z4,z5,z405,z6]),(0,[z1,z2,z3,z4,z5,z6,z439])],[(0,[z202,z1,z2,z3,z8,z5,z6]),(0,[z1,z440,z2,z3,z4,z5,z6]),(0,[z1,z2,z228,z3,z4,z5,z6]),(0,[z1,z441,z2,z3,z4,z5,z6]),(0,[z1,z2,z33,z3,z4,z5,z429]),(0,[z1,z2,z442,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z443])]],
   [[(0,[z1,z3,z4,z29,z5,z352,z6]),(0,[z1,z444,z2,z3,z4,z5,z6]),(0,[z1,z2,z54,z3,z4,z5,z6]),(0,[z445,z1,z2,z3,z4,z5,z6])],[(0,[z446,z1,z2,z3,z4,z5,z6]),(0,[z1,z39,z2,z18,z3,z4,z5]),(0,[z1,z2,z3,z447,z4,z5,z6]),(0,[z1,z2,z3,z4,z29,z5,z448]),(0,[z1,z2,z3,z449,z4,z5,z6]),(0,[z450,z1,z2,z3,z4,z5,z6]),(0,[z1,z451,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z452,z5,z6]),(1,[z1,z2,z3,z4,z6,z355]),(0,[z1,z194,z2,z3,z99,z5,z6]),(0,[z1,z2,z33,z3,z453,z5,z6]),(0,[z1,z2,z3,z4,z454,z5,z6]),(0,[z1,z2,z4,z5,z374,z6,z83]),(0,[z1,z2,z3,z4,z5,z455,z6])],[(0,[z1,z2,z3,z4,z456,z5,z6]),(0,[z457,z1,z2,z3,z4,z5,z6])],[],[(0,[z1,z69,z18,z3,z4,z5,z6]),(0,[z86,z50,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z458]),(0,[z101,z2,z3,z4,z5,z157,z6])],[(0,[z86,z1,z212,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z459]),(0,[z1,z2,z460,z3,z4,z5,z6]),(0,[z1,z2,z3,z461,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z462,z6])],[(0,[z1,z2,z3,z4,z5,z6,z463]),(0,[z1,z2,z3,z4,z5,z464,z6]),(0,[z1,z67,z3,z4,z29,z5,z6]),(0,[z1,z2,z3,z4,z465,z5,z6])]],
   [[(0,[z466,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z166,z4,z99,z5,z6]),(1,[z1,z310,z2,z3,z4,z6]),(0,[z1,z2,z467,z3,z4,z5,z6]),(0,[z1,z108,z2,z33,z4,z5,z6]),(0,[z1,z2,z4,z119,z5,z374,z6]),(0,[z1,z2,z4,z5,z6,z439,z75]),(0,[z1,z2,z3,z4,z5,z468,z6])],[(0,[z469,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z166,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z470,z6]),(0,[z1,z2,z3,z103,z4,z5,z419]),(0,[z471,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z54,z92,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z472]),(0,[z1,z473,z2,z3,z4,z5,z6])],[(0,[z474,z1,z2,z3,z4,z5,z6]),(0,[z1,z475,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z476,z5,z6]),(0,[z1,z2,z3,z4,z5,z477,z6])],[(0,[z1,z2,z3,z4,z478,z5,z6]),(0,[z1,z2,z3,z4,z5,z479,z6]),(0,[z1,z26,z2,z3,z103,z5,z6]),(0,[z1,z2,z3,z480,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z481,z6]),(0,[z1,z2,z3,z4,z482,z5,z6]),(0,[z1,z2,z3,z483,z4,z5,z6]),(1,[z1,z2,z3,z116,z4,z70])],[(0,[z1,z2,z3,z4,z484,z5,z6]),(0,[z1,z69,z2,z3,z4,z5,z68])],[(1,[z17,z18,z3,z4,z5,z6]),(0,[z86,z40,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z485])],[(0,[z1,z105,z3,z4,z29,z5,z6]),(0,[z10,z1,z2,z3,z156,z4,z5]),(0,[z1,z2,z3,z4,z5,z121,z6]),(0,[z1,z2,z3,z116,z4,z70,z6])]],
   [[(0,[z1,z49,z105,z3,z4,z5,z6]),(0,[z61,z101,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z486])],[(0,[z40,z2,z166,z3,z4,z5,z6]),(1,[z1,z126,z3,z4,z5,z68]),(0,[z487,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z488,z4,z5,z6]),(0,[z489,z1,z2,z3,z4,z5,z6]),(0,[z490,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z491,z5,z6]),(0,[z1,z120,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z116,z4,z5,z6])],[(0,[z1,z2,z3,z492,z4,z5,z6]),(0,[z1,z2,z3,z493,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z258]),(0,[z1,z494,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z243,z5,z6]),(0,[z1,z2,z3,z495,z4,z5,z6])],[(1,[z1,z100,z2,z3,z4,z6]),(0,[z202,z1,z2,z3,z5,z121,z6]),(0,[z1,z2,z3,z4,z5,z496,z6]),(0,[z1,z2,z103,z4,z284,z5,z6]),(0,[z1,z37,z2,z3,z4,z5,z6])],[(0,[z1,z497,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z74,z5,z70])],[(0,[z1,z125,z2,z3,z4,z5,z6]),(0,[z1,z19,z2,z3,z4,z158,z6]),(0,[z1,z28,z2,z3,z4,z6,z75]),(0,[z1,z2,z498,z3,z4,z5,z6])]],
   [[(0,[z499,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z68,z6,z355])],[(0,[z1,z26,z18,z3,z4,z5,z6]),(0,[z1,z2,z306,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z500,z6]),(0,[z1,z2,z3,z4,z373,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z18,z3,z4,z29,z5,z6]),(0,[z1,z2,z3,z501,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z502,z6]),(0,[z503,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z504,z6]),(0,[z505,z1,z2,z3,z4,z5,z6]),(0,[z1,z28,z2,z33,z3,z4,z6]),(0,[z1,z421,z2,z3,z4,z5,z6]),(0,[z506,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z156,z4,z5,z240]),(1,[z1,z507,z3,z4,z5,z6])],[(0,[z1,z298,z2,z18,z3,z5,z6]),(0,[z508,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z509]),(0,[z1,z323,z2,z3,z51,z4,z5]),(1,[z1,z2,z4,z284,z5,z6]),(0,[z1,z69,z2,z3,z4,z5,z121]),(0,[z1,z126,z2,z3,z4,z5,z70]),(0,[z1,z2,z54,z92,z4,z5,z6])],[(0,[z1,z2,z3,z103,z4,z348,z6]),(1,[z1,z2,z3,z4,z5,z419]),(1,[z1,z2,z3,z268,z4,z6]),(0,[z1,z2,z3,z510,z4,z5,z6]),(0,[z1,z2,z3,z4,z511,z5,z6])],[(0,[z17,z2,z18,z3,z4,z5,z6]),(0,[z1,z512,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z373,z5]),(0,[z1,z2,z3,z513,z4,z5,z6])],[(0,[z1,z2,z514,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z429]),(0,[z1,z515,z2,z3,z4,z5,z6])],[(0,[z1,z67,z3,z51,z4,z5,z6]),(0,[z1,z2,z3,z4,z516,z6,z83])]],
   [[(0,[z202,z1,z2,z344,z4,z5,z6]),(0,[z1,z517,z2,z3,z4,z5,z6]),(0,[z1,z28,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z518])],[(0,[z17,z274,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z519,z4,z5,z6]),(1,[z1,z2,z3,z453,z5,z6])],[(0,[z520,z1,z2,z3,z4,z5,z6]),(1,[z274,z105,z3,z4,z5,z6]),(0,[z521,z1,z2,z3,z4,z5,z6]),(0,[z40,z1,z2,z166,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z522,z6]),(0,[z1,z2,z3,z523,z4,z5,z6]),(0,[z524,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z525,z6])],[(0,[z1,z2,z526,z3,z4,z5,z6]),(0,[z1,z527,z2,z3,z4,z5,z6]),(0,[z1,z69,z3,z4,z29,z5,z6]),(0,[z1,z2,z3,z528,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z529]),(0,[z1,z2,z3,z4,z5,z530,z6])],[(0,[z1,z2,z3,z531,z4,z5,z6]),(0,[z1,z2,z532,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z173]),(1,[z1,z2,z3,z4,z516,z6])],[(0,[z533,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z534,z6]),(0,[z535,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z536,z6]),(1,[z1,z25,z3,z118,z5,z6]),(0,[z1,z194,z2,z3,z92,z5,z6]),(0,[z1,z537,z2,z3,z4,z5,z6])],[(0,[z1,z105,z3,z51,z4,z5,z6]),(0,[z1,z2,z3,z538,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z539]),(0,[z1,z2,z540,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z448,z6]),(0,[z1,z2,z541,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z317,z4,z5,z6]),(0,[z50,z1,z69,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z542,z5,z6])],[(0,[z543,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z544,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z545]),(0,[z1,z69,z2,z3,z4,z5,z75]),(0,[z1,z2,z3,z546,z4,z5,z6]),(0,[z1,z2,z3,z246,z4,z158,z6])],[(1,[z1,z212,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z547]),(0,[z1,z548,z2,z3,z4,z5,z6])],[(0,[z274,z105,z2,z3,z4,z5,z6]),(0,[z50,z1,z3,z4,z5,z68,z6]),(0,[z1,z2,z3,z4,z549,z5,z6]),(0,[z1,z2,z3,z550,z4,z5,z6])],[(0,[z2,z3,z4,z5,z24,z6,z11]),(0,[z1,z2,z3,z4,z5,z551,z6]),(0,[z1,z25,z19,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z552,z6])],[(0,[z202,z1,z2,z3,z4,z143,z6]),(0,[z1,z2,z3,z4,z5,z553,z6]),(0,[z1,z421,z3,z4,z5,z132,z6]),(0,[z1,z2,z3,z4,z5,z554,z6])],[(0,[z1,z2,z18,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z555,z6]),(0,[z556,z1,z2,z3,z4,z5,z6])],[(0,[z202,z1,z2,z317,z4,z5,z6]),(0,[z1,z2,z557,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z348,z6]),(0,[z1,z2,z3,z4,z558,z5,z6])]],
   [[(0,[z50,z40,z1,z2,z4,z5,z6]),(0,[z1,z559,z2,z3,z4,z5,z6]),(0,[z1,z560,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z11]),(0,[z1,z310,z2,z3,z51,z4,z6]),(0,[z1,z561,z2,z3,z4,z5,z6]),(0,[z1,z507,z3,z4,z5,z6,z75])],[(0,[z562,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z240]),(0,[z563,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z374,z75])],[(0,[z1,z18,z3,z51,z4,z5,z6]),(1,[z1,z244,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z564,z6]),(0,[z1,z565,z2,z3,z4,z5,z6])],[(0,[z57,z1,z26,z2,z3,z5,z6]),(0,[z50,z1,z19,z3,z4,z5,z6]),(0,[z1,z2,z3,z566,z4,z5,z6]),(0,[z1,z2,z3,z4,z567,z5,z6]),(0,[z1,z126,z69,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z568,z5,z6]),(1,[z1,z69,z3,z4,z5,z173]),(0,[z97,z1,z2,z33,z4,z5,z6]),(0,[z1,z2,z3,z243,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z569,z6]),(0,[z1,z2,z3,z4,z5,z6,z570]),(1,[z1,z106,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z571,z5,z6]),(0,[z1,z2,z3,z4,z5,z572,z6])],[(0,[z573,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z574,z6]),(0,[z1,z2,z3,z246,z92,z5,z6]),(0,[z1,z575,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z62,z51,z4,z6]),(0,[z1,z2,z3,z103,z4,z5,z124]),(0,[z1,z126,z3,z4,z5,z68,z6]),(0,[z1,z2,z111,z4,z5,z374,z6])]],
   [[(0,[z1,z19,z105,z3,z4,z5,z6]),(0,[z1,z2,z576,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z34,z6])],[(0,[z1,z2,z577,z3,z4,z5,z6]),(0,[z578,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z579,z3,z4,z5,z6]),(0,[z1,z2,z3,z99,z5,z132,z6]),(0,[z1,z2,z3,z580,z4,z5,z6])],[(0,[z1,z2,z3,z4,z581,z5,z6]),(0,[z1,z2,z3,z582,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z448]),(0,[z1,z2,z3,z4,z5,z583,z6])],[(0,[z1,z584,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z11,z240]),(0,[z1,z585,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z70,z6,z75])],[(0,[z1,z25,z2,z3,z103,z5,z6]),(0,[z1,z19,z3,z103,z4,z5,z6]),(0,[z1,z120,z2,z3,z4,z5,z121])],[(0,[z104,z1,z2,z18,z4,z5,z6]),(1,[z1,z2,z3,z248,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z586]),(0,[z50,z1,z2,z4,z99,z5,z6]),(1,[z1,z28,z3,z4,z29,z6]),(0,[z587,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z588,z6]),(0,[z1,z2,z3,z4,z5,z589,z6])],[(0,[z1,z2,z3,z4,z5,z6,z590]),(0,[z1,z232,z2,z3,z4,z5,z6]),(0,[z55,z1,z69,z2,z3,z4,z5]),(0,[z50,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z591]),(0,[z50,z1,z2,z54,z4,z5,z6]),(0,[z1,z2,z3,z4,z592,z5,z6]),(0,[z1,z69,z3,z4,z5,z6,z173]),(0,[z1,z2,z3,z4,z593,z5,z6]),(1,[z1,z3,z4,z146,z5,z6]),(0,[z1,z3,z4,z146,z5,z34,z6]),(0,[z1,z2,z3,z594,z4,z5,z6])]],
   [[(0,[z1,z125,z2,z18,z3,z5,z6]),(0,[z595,z1,z2,z3,z4,z5,z6]),(0,[z40,z1,z49,z2,z4,z5,z6]),(1,[z55,z2,z3,z4,z5,z24]),(0,[z596,z1,z2,z3,z4,z5,z6]),(0,[z1,z597,z2,z3,z4,z5,z6])],[(0,[z598,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z599,z6]),(0,[z1,z2,z3,z4,z5,z516,z6]),(0,[z1,z2,z3,z4,z600,z5,z6]),(0,[z1,z2,z3,z4,z5,z601,z6])],[(0,[z602,z1,z2,z3,z4,z5,z6]),(0,[z55,z1,z120,z2,z3,z4,z5]),(0,[z1,z19,z67,z3,z4,z5,z6]),(0,[z1,z2,z3,z603,z4,z5,z6]),(0,[z1,z604,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z605]),(0,[z1,z2,z3,z4,z5,z606,z6])],[(0,[z1,z607,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z608,z6]),(0,[z1,z108,z2,z3,z4,z5,z374])],[(0,[z1,z2,z3,z4,z5,z609,z6])],[(0,[z61,z1,z106,z3,z4,z5,z6]),(0,[z1,z2,z610,z3,z4,z5,z6]),(0,[z611,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z377]),(0,[z1,z131,z2,z3,z4,z5,z6]),(1,[z1,z131,z2,z3,z132,z6])],[(0,[z1,z69,z2,z3,z4,z5,z240]),(0,[z1,z2,z3,z58,z4,z5,z34])],[(0,[z612,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z26,z2,z3,z4,z5,z6]),(0,[z1,z613,z2,z3,z4,z5,z6]),(0,[z1,z19,z69,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z614,z6]),(0,[z1,z2,z3,z4,z615,z5,z6]),(0,[z1,z2,z3,z616,z4,z5,z6]),(0,[z1,z2,z3,z246,z158,z5,z6])],[(1,[z1,z241,z2,z3,z4,z6])],[(1,[z1,z170,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z124]),(0,[z1,z108,z69,z2,z3,z4,z5]),(0,[z97,z1,z2,z3,z4,z34,z6]),(0,[z1,z2,z3,z4,z5,z6,z617]),(0,[z1,z2,z3,z116,z4,z74,z6]),(0,[z1,z2,z3,z116,z4,z5,z75])],[(0,[z1,z2,z3,z618,z4,z5,z6]),(0,[z55,z1,z2,z3,z4,z5,z11]),(0,[z1,z619,z2,z3,z4,z5,z6]),(0,[z1,z19,z3,z4,z5,z68,z6]),(0,[z1,z244,z2,z3,z4,z5,z6])],[(0,[z57,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z29,z5,z6])],[(1,[z101,z2,z3,z4,z157,z6]),(0,[z1,z2,z3,z4,z5,z620,z6])],[(1,[z104,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z621,z4,z5,z6]),(0,[z1,z622,z2,z3,z4,z5,z6]),(0,[z1,z2,z344,z3,z4,z5,z6]),(0,[z1,z2,z3,z623,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z624,z6]),(0,[z1,z2,z3,z276,z51,z4,z5]),(0,[z1,z2,z3,z4,z118,z5,z6]),(0,[z1,z625,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z626,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z627,z6])],[(0,[z86,z1,z2,z166,z4,z5,z6]),(0,[z1,z2,z628,z3,z4,z5,z6]),(0,[z55,z1,z2,z3,z4,z5,z24]),(0,[z629,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z630,z4,z5,z6]),(0,[z1,z2,z631,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z632,z5,z6]),(0,[z1,z2,z3,z633,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z405,z6]),(0,[z1,z634,z2,z3,z4,z5,z6])],[(0,[z1,z167,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z635,z4,z5,z6])],[(0,[z202,z1,z2,z3,z156,z5,z6]),(0,[z1,z2,z3,z4,z636,z5,z6]),(0,[z1,z2,z637,z3,z4,z5,z6]),(0,[z1,z28,z3,z4,z29,z5,z6]),(0,[z1,z126,z2,z3,z4,z5,z173])],[(0,[z638,z1,z2,z3,z4,z5,z6]),(0,[z1,z639,z2,z3,z4,z5,z6])],[(0,[z274,z1,z105,z3,z4,z5,z6]),(1,[z202,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z640,z6])],[(0,[z57,z1,z25,z2,z3,z5,z6]),(0,[z1,z2,z3,z641,z4,z5,z6]),(0,[z1,z2,z642,z3,z4,z5,z6]),(0,[z1,z2,z3,z246,z99,z5,z6]),(1,[z1,z37,z3,z4,z5,z6])],[(0,[z643,z1,z2,z3,z4,z5,z6]),(0,[z1,z644,z2,z3,z4,z5,z6])],[(0,[z101,z1,z28,z2,z3,z4,z6]),(0,[z1,z19,z2,z3,z116,z4,z6]),(0,[z1,z2,z3,z645,z4,z5,z6]),(1,[z1,z2,z3,z4,z360,z6])]],
   [[(0,[z1,z2,z3,z4,z646,z5,z6]),(0,[z1,z2,z3,z87,z4,z5,z6]),(0,[z1,z2,z3,z4,z647,z5,z6]),(0,[z1,z120,z2,z3,z5,z121,z6])],[(0,[z648,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z649,z6]),(0,[z202,z2,z3,z4,z8,z5,z6]),(0,[z1,z2,z650,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z651,z6]),(0,[z1,z28,z2,z3,z4,z352,z6]),(0,[z652,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z33,z3,z4,z119,z6])],[(1,[z1,z424,z3,z4,z5,z6]),(0,[z1,z2,z3,z653,z4,z5,z6]),(0,[z1,z2,z92,z4,z99,z5,z6]),(0,[z654,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z70,z374]),(0,[z1,z2,z3,z5,z121,z6,z240]),(1,[z1,z2,z4,z5,z6,z439])],[(0,[z655,z1,z2,z3,z4,z5,z6])],[(0,[z1,z656,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z657,z4,z5,z6]),(0,[z1,z49,z67,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z658,z5,z6]),(1,[z1,z2,z3,z156,z5,z240])],[(0,[z17,z1,z2,z3,z4,z5,z6]),(0,[z202,z1,z2,z3,z4,z5,z258]),(0,[z1,z2,z3,z4,z158,z88,z6]),(0,[z1,z2,z659,z3,z4,z5,z6]),(0,[z1,z2,z3,z660,z4,z5,z6]),(0,[z1,z2,z3,z4,z158,z5,z6]),(0,[z1,z661,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z662,z6]),(1,[z1,z2,z95,z4,z5,z6])],[(1,[z1,z323,z2,z3,z4,z5])]],
   [[(0,[z1,z31,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z663,z5,z6]),(0,[z1,z2,z3,z4,z5,z664,z6]),(0,[z55,z1,z228,z3,z4,z5,z6])],[(0,[z10,z2,z3,z4,z5,z6,z11]),(0,[z1,z19,z3,z4,z5,z352,z6]),(0,[z1,z2,z3,z4,z5,z6,z665]),(0,[z1,z194,z2,z54,z4,z5,z6])],[(0,[z1,z2,z3,z666,z4,z5,z6]),(0,[z1,z2,z3,z4,z667,z5,z6]),(0,[z668,z1,z2,z3,z4,z5,z6]),(0,[z55,z1,z232,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z669,z6]),(0,[z1,z2,z3,z4,z5,z6,z670]),(0,[z1,z2,z3,z4,z671,z5,z6])],[(0,[z40,z1,z2,z87,z4,z5,z6]),(0,[z1,z672,z2,z3,z4,z5,z6]),(0,[z10,z1,z69,z2,z3,z4,z5]),(0,[z1,z2,z33,z3,z4,z70,z6]),(0,[z1,z673,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z51,z4,z5,z6]),(0,[z1,z674,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z675,z5,z6]),(0,[z676,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z677,z5,z6])],[(0,[z1,z2,z3,z4,z453,z5,z6]),(0,[z1,z108,z2,z3,z4,z5,z83]),(0,[z1,z2,z678,z3,z4,z5,z6]),(0,[z679,z1,z2,z3,z4,z5,z6])],[(0,[z680,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z33,z3,z4,z5,z6]),(0,[z1,z108,z2,z3,z116,z4,z5]),(0,[z1,z2,z111,z3,z4,z5,z374]),(0,[z1,z131,z2,z3,z5,z132,z6])],[(0,[z10,z1,z120,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z681]),(0,[z1,z2,z3,z4,z5,z682,z6]),(0,[z1,z2,z3,z4,z5,z6,z683]),(0,[z1,z120,z2,z3,z4,z5,z240])]],
   [[(0,[z202,z57,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z157,z132,z6]),(0,[z1,z2,z3,z4,z158,z157,z6])],[(0,[z86,z1,z170,z3,z4,z5,z6]),(0,[z1,z2,z684,z3,z4,z5,z6]),(0,[z1,z2,z3,z685,z4,z5,z6]),(0,[z1,z2,z3,z686,z4,z5,z6]),(0,[z1,z687,z2,z3,z4,z5,z6]),(0,[z1,z28,z2,z3,z4,z132,z6]),(0,[z1,z2,z3,z4,z688,z5,z6])],[(0,[z1,z2,z3,z4,z689,z5,z6]),(0,[z61,z1,z424,z3,z4,z5,z6]),(0,[z1,z25,z3,z4,z118,z5,z6]),(0,[z690,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z691,z4,z5,z6]),(0,[z1,z692,z2,z3,z4,z5,z6])],[(0,[z1,z362,z2,z3,z4,z8,z5]),(0,[z1,z2,z3,z4,z693,z5,z6]),(0,[z1,z2,z3,z4,z99,z5,z6]),(0,[z694,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z3,z248,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z695,z6])],[(0,[z696,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z697,z4,z5,z6]),(0,[z97,z1,z2,z3,z4,z70,z6]),(0,[z1,z2,z698,z3,z4,z5,z6])],[(0,[z1,z2,z256,z18,z4,z5,z6]),(0,[z1,z2,z3,z4,z699,z5,z6]),(0,[z1,z2,z3,z700,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z701]),(0,[z1,z2,z3,z102,z5,z6,z11]),(0,[z1,z2,z3,z702,z4,z5,z6]),(0,[z1,z2,z3,z703,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z704,z6]),(0,[z1,z2,z3,z4,z705,z5,z6]),(0,[z101,z1,z19,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z706,z6]),(0,[z1,z507,z2,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z707,z2,z4,z5,z6])],[(0,[z1,z170,z3,z4,z5,z6]),(0,[z1,z100,z298,z2,z3,z6]),(0,[z1,z2,z4,z708,z5,z6]),(0,[z97,z1,z37,z3,z4,z6]),(0,[z1,z2,z4,z5,z6,z709])],[(0,[z104,z1,z241,z2,z4,z6]),(0,[z1,z19,z3,z4,z710,z6]),(0,[z1,z2,z3,z4,z5,z711])],[(0,[z1,z3,z4,z5,z6,z712]),(0,[z1,z2,z3,z4,z5,z713]),(0,[z1,z2,z3,z4,z360,z75])],[(0,[z1,z2,z3,z4,z5,z714]),(0,[z101,z2,z3,z4,z715,z6]),(0,[z1,z26,z63,z103,z5,z6]),(0,[z1,z3,z4,z5,z6,z716]),(0,[z1,z108,z2,z4,z360,z5]),(0,[z1,z131,z421,z3,z132,z6])],[(0,[z17,z256,z18,z4,z5,z6]),(0,[z104,z1,z2,z4,z5,z6]),(0,[z1,z18,z3,z4,z5,z448]),(0,[z1,z2,z3,z4,z717,z6]),(0,[z1,z2,z3,z4,z718,z6]),(0,[z50,z1,z276,z51,z4,z5]),(0,[z1,z2,z4,z373,z119,z5])],[(0,[z1,z18,z3,z62,z4,z6]),(0,[z1,z19,z241,z3,z4,z6]),(0,[z1,z37,z33,z3,z4,z6]),(0,[z1,z3,z58,z4,z146,z5]),(0,[z1,z719,z3,z4,z5,z6]),(0,[z1,z2,z720,z4,z5,z6])],[(0,[z1,z2,z4,z721,z5,z6]),(0,[z233,z105,z3,z4,z5,z6]),(0,[z1,z722,z3,z4,z5,z6]),(0,[z1,z2,z3,z723,z4,z6]),(0,[z724,z2,z3,z4,z5,z6]),(0,[z1,z126,z3,z4,z68,z355]),(0,[z1,z3,z4,z360,z6,z377]),(0,[z1,z3,z4,z5,z405,z725])]],
   [[(0,[z1,z2,z726,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z727]),(0,[z97,z1,z2,z4,z627,z6])],[(0,[z1,z19,z2,z3,z453,z6])],[(0,[z202,z306,z3,z8,z5,z6]),(0,[z2,z3,z4,z5,z24,z728]),(0,[z1,z2,z95,z4,z74,z6])],[(0,[z1,z125,z31,z2,z3,z5]),(0,[z202,z2,z3,z8,z5,z6]),(0,[z1,z729,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z730,z6])],[(0,[z1,z2,z3,z4,z710,z6]),(0,[z1,z108,z2,z3,z4,z360])],[(0,[z1,z2,z3,z4,z5,z731]),(0,[z1,z2,z3,z732,z5,z6])],[(0,[z1,z125,z100,z2,z3,z6]),(0,[z40,z2,z166,z4,z5,z6]),(0,[z1,z733,z2,z3,z4,z6]),(0,[z1,z3,z4,z5,z734,z6]),(0,[z1,z2,z3,z116,z4,z504]),(0,[z1,z2,z3,z4,z5,z735])],[(0,[z1,z323,z18,z3,z4,z5]),(0,[z1,z323,z67,z3,z4,z5]),(0,[z1,z2,z736,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z737,z5]),(0,[z1,z738,z3,z4,z5,z6]),(0,[z1,z2,z3,z739,z4,z5])],[(0,[z1,z424,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z740,z6]),(0,[z1,z2,z4,z284,z5,z124]),(0,[z1,z126,z3,z112,z4,z5]),(0,[z1,z2,z4,z5,z6,z439])],[(0,[z1,z2,z741,z3,z4,z5]),(0,[z1,z742,z3,z4,z5,z6]),(0,[z1,z26,z3,z103,z265,z6]),(0,[z1,z2,z3,z4,z743,z6]),(0,[z1,z28,z2,z95,z4,z6]),(0,[z1,z2,z698,z92,z5,z6]),(0,[z1,z2,z33,z4,z373,z5]),(0,[z1,z2,z95,z4,z70,z6])],[(0,[z1,z2,z3,z744,z5,z6]),(1,[z2,z745,z4,z5,z6]),(0,[z587,z2,z3,z4,z157,z6]),(0,[z55,z1,z2,z3,z102,z5]),(0,[z746,z2,z3,z4,z5,z6]),(0,[z1,z747,z3,z4,z5,z6])],[(0,[z104,z1,z39,z2,z4,z5]),(0,[z1,z2,z3,z748,z5,z6]),(0,[z1,z2,z3,z4,z749,z6]),(0,[z1,z3,z4,z710,z352,z6]),(0,[z1,z2,z3,z156,z5,z240])],[(0,[z1,z2,z3,z4,z750,z6]),(0,[z1,z2,z3,z751,z5,z6]),(0,[z1,z2,z3,z4,z5,z752]),(1,[z1,z3,z753,z5,z6]),(0,[z1,z2,z95,z4,z5,z6])],[(0,[z1,z2,z3,z4,z754,z6]),(0,[z1,z323,z2,z3,z4,z5]),(0,[z1,z67,z4,z5,z6,z670]),(0,[z1,z755,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z756,z6]),(0,[z1,z2,z4,z74,z439,z75])],[]],
   [[(0,[z1,z67,z4,z675,z5,z6])],[(0,[z17,z757,z3,z4,z5,z6]),(0,[z202,z2,z344,z8,z5,z6]),(0,[z1,z2,z3,z758,z4,z5]),(0,[z1,z2,z3,z4,z5,z759]),(0,[z1,z760,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z761,z6]),(0,[z1,z19,z3,z4,z113,z6]),(0,[z1,z167,z3,z4,z142,z6]),(0,[z2,z3,z4,z715,z157,z6]),(0,[z10,z2,z3,z4,z5,z11])],[(0,[z10,z2,z3,z102,z5,z11]),(0,[z1,z2,z762,z4,z5,z6]),(0,[z1,z194,z2,z708,z5,z6])],[(0,[z1,z2,z3,z4,z5,z763]),(0,[z1,z764,z3,z4,z5,z6]),(0,[z61,z303,z2,z3,z4,z6]),(0,[z1,z69,z379,z3,z4,z5]),(0,[z1,z126,z3,z268,z4,z68]),(0,[z1,z3,z4,z5,z405,z765])],[(0,[z1,z2,z3,z4,z5,z766])],[(0,[z50,z1,z323,z3,z4,z5]),(0,[z1,z310,z2,z3,z276,z4]),(0,[z1,z69,z404,z3,z4,z5]),(0,[z1,z3,z4,z5,z716,z429]),(0,[z1,z37,z3,z4,z373,z5])],[(0,[z2,z745,z87,z4,z5,z6]),(0,[z1,z3,z103,z753,z5,z6])]],
   [[(0,[z1,z767,z3,z4,z5,z6]),(0,[z202,z2,z3,z8,z5,z257]),(0,[z1,z2,z3,z4,z620,z75])],[(0,[z1,z768,z3,z4,z5,z6]),(0,[z1,z19,z3,z4,z144,z6]),(0,[z1,z2,z769,z4,z5,z6]),(0,[z1,z2,z3,z243,z5,z429]),(0,[z97,z1,z2,z3,z4,z373]),(0,[z1,z244,z3,z4,z5,z75])],[],[(0,[z1,z232,z3,z4,z5,z6]),(0,[z1,z100,z2,z256,z4,z6]),(0,[z1,z3,z4,z770,z5,z6])],[(0,[z10,z2,z3,z5,z135,z11]),(0,[z1,z2,z3,z102,z5,z121])],[(0,[z50,z1,z703,z4,z5,z6]),(0,[z1,z2,z771,z4,z5,z6]),(0,[z1,z2,z3,z4,z348,z124]),(0,[z1,z28,z3,z4,z29,z287])],[(0,[z1,z2,z772,z4,z5,z6]),(0,[z1,z2,z3,z773,z5,z6]),(0,[z1,z2,z3,z4,z5,z774]),(0,[z202,z2,z3,z8,z143,z6]),(0,[z1,z2,z3,z4,z5,z775]),(0,[z1,z2,z33,z4,z326,z6]),(0,[z1,z2,z4,z360,z374,z6])],[(0,[z1,z2,z776,z4,z5,z6]),(0,[z1,z2,z3,z4,z777,z6]),(0,[z1,z2,z3,z4,z778,z6]),(0,[z1,z779,z3,z4,z5,z6])]],
   [[(0,[z411,z18,z3,z4,z5,z6]),(0,[z202,z2,z317,z8,z5,z6]),(0,[z1,z2,z780,z4,z5,z6])],[(0,[z1,z781,z170,z3,z4,z5]),(0,[z1,z19,z59,z3,z4,z6]),(0,[z50,z1,z21,z4,z5,z6]),(0,[z1,z2,z782,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z765]),(0,[z1,z95,z4,z5,z6,z183])],[(0,[z1,z31,z69,z3,z4,z5]),(0,[z1,z2,z3,z5,z783,z6]),(0,[z1,z2,z3,z4,z784,z5]),(0,[z1,z19,z2,z95,z4,z6]),(0,[z1,z69,z3,z4,z5,z148]),(0,[z1,z108,z2,z4,z5,z83])],[(0,[z17,z104,z18,z4,z5,z6]),(0,[z17,z241,z18,z3,z4,z6]),(0,[z1,z241,z39,z2,z3,z4]),(0,[z1,z3,z4,z785,z5,z6])],[(0,[z1,z786,z170,z3,z4,z6]),(0,[z252,z1,z2,z3,z156,z5]),(0,[z1,z787,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z788]),(0,[z1,z2,z33,z4,z373,z6])],[(0,[z1,z789,z3,z4,z5,z6])],[(0,[z1,z39,z2,z3,z4,z5]),(0,[z1,z790,z3,z4,z5,z6]),(0,[z1,z791,z3,z4,z5,z6]),(0,[z1,z2,z3,z453,z5,z429])],[(0,[z2,z3,z4,z5,z728,z6]),(0,[z1,z3,z4,z5,z766,z6]),(0,[z319,z1,z2,z3,z4,z74])]],
   [[(0,[z1,z125,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z792]),(0,[z1,z793,z3,z4,z5,z6]),(0,[z1,z794,z106,z3,z4,z5]),(0,[z1,z2,z4,z5,z6,z795]),(0,[z1,z3,z4,z5,z796,z6])],[(0,[z1,z2,z3,z4,z5,z797]),(0,[z1,z798,z106,z3,z4,z5]),(0,[z50,z1,z62,z51,z4,z6]),(0,[z1,z28,z115,z3,z4,z6])],[(0,[z1,z799,z3,z4,z5,z6]),(0,[z1,z2,z3,z800,z5,z6]),(0,[z1,z801,z3,z4,z5,z6])],[(0,[z1,z3,z4,z753,z5,z6]),(0,[z1,z2,z4,z802,z5,z6]),(0,[z1,z182,z2,z3,z4,z75]),(0,[z1,z2,z95,z4,z74,z5])],[(0,[z1,z2,z3,z4,z5,z803]),(0,[z202,z271,z2,z3,z5,z6]),(0,[z1,z2,z3,z804,z5,z6]),(0,[z1,z25,z3,z204,z5,z6]),(0,[z1,z28,z2,z3,z453,z6])],[(0,[z104,z1,z49,z4,z5,z6]),(0,[z1,z241,z298,z2,z3,z6]),(0,[z1,z2,z3,z62,z4,z6])],[(0,[z1,z2,z3,z4,z805,z6])],[(0,[z1,z2,z3,z4,z806,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z807]),(0,[z1,z2,z3,z4,z5,z808]),(1,[z1,z809,z4,z5,z6]),(0,[z1,z108,z244,z4,z5,z83])],[(0,[z1,z298,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z810]),(0,[z1,z811,z2,z3,z4,z6]),(0,[z1,z812,z3,z4,z5,z6]),(0,[z350,z2,z3,z4,z5,z24]),(0,[z1,z49,z809,z4,z5,z6]),(0,[z1,z813,z2,z3,z4,z5]),(0,[z2,z3,z4,z5,z6,z814]),(0,[z1,z2,z3,z815,z5,z6]),(1,[z1,z2,z3,z5,z816])],[(0,[z1,z2,z817,z4,z5,z6]),(0,[z1,z818,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z74,z711])],[(0,[z1,z2,z819,z4,z5,z6]),(0,[z1,z306,z3,z4,z5,z6]),(0,[z1,z794,z2,z3,z4,z5]),(0,[z1,z69,z3,z4,z5,z259])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z820,z6]),(0,[z61,z2,z3,z4,z88,z6]),(0,[z1,z19,z63,z4,z5,z6])],[(0,[z1,z2,z3,z102,z5,z6]),(0,[z1,z2,z3,z5,z121,z509]),(0,[z1,z26,z3,z103,z5,z6])],[(0,[z1,z3,z4,z29,z710,z6]),(0,[z1,z2,z3,z702,z132,z6]),(0,[z1,z2,z3,z4,z756,z6])],[(0,[z1,z2,z3,z4,z5,z821]),(1,[z2,z3,z822,z5,z6]),(0,[z1,z823,z2,z3,z4,z5]),(0,[z679,z2,z3,z4,z5,z11])]],
   [[(0,[z1,z2,z3,z4,z5,z824]),(0,[z1,z2,z825,z4,z5,z6])],[(0,[z1,z49,z67,z4,z5,z6]),(0,[z2,z3,z4,z5,z826,z6])],[(0,[z1,z3,z4,z5,z6,z827]),(0,[z1,z3,z4,z5,z183,z287]),(0,[z1,z828,z3,z4,z5,z6]),(0,[z1,z2,z4,z119,z6,z73]),(0,[z1,z2,z95,z4,z74,z75])],[(0,[z1,z2,z3,z829,z5,z6]),(0,[z1,z830,z2,z3,z5,z6]),(0,[z1,z2,z3,z641,z5,z121]),(0,[z1,z2,z3,z831,z4,z5])],[(0,[z1,z125,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z832,z6]),(0,[z1,z2,z3,z833,z4,z5]),(0,[z1,z2,z3,z834,z5,z6]),(0,[z1,z835,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z711,z6])],[(0,[z1,z2,z836,z4,z5,z6]),(0,[z1,z2,z3,z4,z837,z6]),(0,[z1,z838,z3,z4,z5,z6]),(0,[z1,z28,z106,z3,z4,z6]),(0,[z1,z839,z3,z4,z5,z6])],[(0,[z1,z306,z3,z4,z142,z6]),(0,[z1,z2,z3,z5,z135,z6]),(0,[z61,z2,z3,z4,z715,z6]),(0,[z1,z2,z63,z4,z5,z6]),(0,[z1,z244,z3,z4,z516,z6])],[(0,[z1,z2,z4,z840,z5,z6]),(0,[z1,z841,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z142,z6]),(0,[z1,z126,z2,z95,z4,z5]),(0,[z1,z3,z4,z5,z842,z6])]],
   [[(0,[z50,z1,z626,z4,z5,z6]),(0,[z1,z2,z708,z99,z5,z6]),(0,[z1,z3,z4,z516,z6,z377])],[(0,[z757,z18,z3,z4,z5,z6]),(0,[z57,z2,z3,z5,z588,z6])],[(0,[z1,z2,z3,z843,z5,z6]),(0,[z1,z2,z3,z4,z844,z6]),(0,[z1,z2,z3,z4,z5,z845]),(0,[z2,z3,z7,z822,z5,z6]),(0,[z1,z19,z3,z4,z265,z6]),(0,[z1,z126,z3,z4,z5,z766])],[(0,[z1,z846,z2,z3,z4,z5]),(0,[z1,z847,z3,z4,z5,z6])],[(0,[z1,z2,z3,z848,z4,z5]),(0,[z1,z69,z460,z3,z4,z5])],[(0,[z1,z849,z3,z4,z5,z6])],[(0,[z1,z2,z3,z5,z850,z6]),(0,[z1,z2,z3,z4,z851,z6]),(0,[z1,z49,z4,z392,z5,z6]),(0,[z1,z26,z3,z103,z5,z419]),(0,[z97,z1,z2,z4,z119,z6])],[(0,[z1,z2,z678,z99,z5,z6]),(0,[z2,z3,z4,z5,z6,z852]),(0,[z1,z2,z3,z853,z4,z6])]],
   [[(0,[z50,z1,z170,z4,z5,z6]),(0,[z1,z3,z4,z854,z5,z6]),(0,[z1,z306,z3,z4,z5,z257]),(0,[z1,z2,z4,z5,z6,z759])],[(0,[z104,z1,z19,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z257]),(0,[z1,z2,z855,z4,z5,z6]),(0,[z450,z2,z3,z4,z88,z6]),(0,[z1,z69,z2,z3,z4,z355]),(0,[z1,z2,z3,z4,z388,z75])],[(0,[z1,z167,z3,z4,z5,z6]),(0,[z1,z2,z3,z102,z5,z257]),(0,[z1,z2,z3,z4,z5,z856])],[(0,[z1,z3,z753,z118,z5,z6]),(0,[z1,z120,z2,z3,z5,z816])],[(0,[z1,z2,z3,z4,z265,z6]),(0,[z1,z2,z3,z4,z5,z64]),(0,[z1,z2,z3,z4,z857,z5])],[(0,[z524,z18,z3,z4,z5,z6]),(0,[z105,z757,z3,z4,z5,z6]),(0,[z1,z2,z344,z4,z142,z6]),(0,[z1,z19,z3,z93,z4,z6]),(0,[z1,z3,z4,z5,z6,z183])],[(0,[z1,z2,z3,z276,z4,z5]),(0,[z1,z858,z3,z4,z5,z6])],[(0,[z1,z241,z2,z256,z4,z6]),(0,[z202,z2,z3,z8,z5,z258]),(0,[z1,z69,z3,z4,z5,z287]),(0,[z1,z2,z111,z4,z5,z374]),(0,[z1,z2,z859,z4,z5,z6])]],
   [[(0,[z86,z212,z87,z4,z5,z6]),(0,[z1,z860,z3,z4,z5,z6])],[(0,[z17,z39,z18,z3,z4,z5]),(0,[z1,z31,z228,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z861]),(0,[z2,z3,z4,z822,z5,z6]),(0,[z1,z3,z4,z29,z123,z6]),(0,[z1,z2,z3,z58,z4,z5]),(0,[z1,z862,z3,z4,z5,z6]),(0,[z1,z863,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z68,z287]),(0,[z1,z2,z3,z180,z4,z70])],[(0,[z1,z19,z39,z3,z4,z5]),(0,[z1,z864,z3,z4,z5,z6]),(0,[z1,z2,z3,z865,z4,z5]),(0,[z1,z2,z3,z4,z5,z866])],[(0,[z1,z2,z3,z4,z142,z257]),(0,[z1,z2,z3,z4,z867,z6]),(0,[z1,z323,z2,z3,z62,z4]),(0,[z1,z2,z3,z868,z4,z6])],[(0,[z1,z2,z3,z869,z5,z6]),(0,[z1,z19,z106,z3,z4,z6]),(0,[z1,z25,z3,z753,z5,z6]),(0,[z1,z2,z3,z4,z5,z870]),(0,[z1,z69,z3,z4,z5,z554]),(0,[z1,z871,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z872]),(0,[z50,z1,z51,z4,z5,z6]),(0,[z1,z2,z63,z4,z265,z6])],[(0,[z690,z105,z3,z4,z5,z6]),(0,[z1,z2,z54,z47,z5,z6]),(0,[z1,z2,z3,z4,z873,z6]),(0,[z1,z2,z3,z4,z5,z874])]],
   [[(0,[z1,z875,z3,z4,z5,z6]),(0,[z1,z167,z344,z4,z5,z6]),(0,[z1,z19,z69,z3,z4,z75])],[(0,[z1,z241,z3,z4,z29,z6]),(0,[z1,z2,z3,z4,z5,z876]),(0,[z1,z26,z3,z103,z348,z6]),(0,[z1,z2,z3,z708,z5,z6])],[(0,[z1,z2,z3,z877,z4,z6]),(0,[z1,z2,z54,z708,z5,z6]),(0,[z1,z2,z4,z5,z374,z429])],[(0,[z340,z18,z3,z4,z5,z6]),(0,[z1,z39,z298,z2,z3,z5]),(0,[z1,z656,z2,z99,z5,z6]),(0,[z1,z19,z3,z4,z496,z6]),(0,[z1,z507,z4,z5,z6,z439])],[(0,[z1,z228,z3,z4,z5,z6]),(0,[z1,z2,z317,z4,z142,z6]),(0,[z1,z878,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z360,z429])],[],[(0,[z1,z2,z3,z4,z879,z6]),(0,[z1,z28,z3,z4,z29,z448])],[(0,[z1,z2,z3,z880,z4,z5]),(0,[z1,z167,z3,z4,z5,z257]),(0,[z10,z2,z3,z417,z4,z5]),(0,[z881,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z882]),(0,[z1,z2,z883,z4,z5,z6]),(0,[z1,z884,z3,z4,z5,z6]),(0,[z1,z507,z95,z4,z5,z6])]],
   [[(0,[z57,z2,z3,z7,z5,z6]),(0,[z1,z885,z3,z4,z5,z6])],[(0,[z1,z886,z2,z4,z5,z6])],[(0,[z1,z31,z2,z3,z4,z5]),(0,[z1,z105,z3,z268,z4,z6])],[(0,[z104,z1,z4,z29,z5,z6]),(0,[z1,z2,z3,z887,z4,z5]),(0,[z1,z421,z3,z4,z5,z6]),(0,[z1,z19,z3,z4,z352,z6]),(0,[z1,z2,z3,z4,z888,z6]),(0,[z1,z2,z95,z4,z5,z429])],[(0,[z1,z19,z3,z4,z6,z355]),(1,[z1,z2,z708,z5,z6]),(0,[z1,z2,z33,z4,z34,z64])],[(0,[z2,z166,z745,z4,z5,z6]),(0,[z1,z167,z3,z4,z143,z6])],[(0,[z104,z1,z31,z2,z4,z5]),(0,[z1,z889,z3,z4,z5,z6]),(0,[z1,z890,z3,z4,z5,z6])],[(0,[z1,z2,z256,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z891]),(0,[z1,z2,z3,z246,z158,z6])]],
   [[(0,[z1,z892,z2,z3,z5,z6]),(0,[z1,z893,z3,z4,z5,z6])],[(0,[z104,z1,z100,z2,z4,z6]),(0,[z1,z894,z2,z3,z4,z5]),(0,[z1,z2,z3,z895,z5,z6]),(0,[z1,z367,z69,z3,z4,z5]),(0,[z1,z2,z3,z4,z896,z6])],[(0,[z311,z105,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z897]),(0,[z1,z3,z4,z5,z405,z6]),(0,[z1,z131,z2,z3,z756,z6])],[(0,[z1,z2,z3,z4,z898,z5]),(0,[z1,z2,z447,z99,z5,z6]),(0,[z1,z69,z3,z4,z5,z183]),(1,[z1,z2,z95,z4,z74])],[(0,[z1,z899,z170,z3,z4,z6]),(0,[z1,z126,z228,z3,z4,z5]),(0,[z1,z67,z3,z268,z4,z6]),(0,[z1,z900,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z901]),(0,[z1,z2,z3,z4,z5,z902])],[(0,[z1,z2,z3,z4,z5,z903])],[(0,[z1,z781,z2,z3,z4,z5]),(0,[z1,z2,z904,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z355]),(0,[z1,z2,z905,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z906])],[(0,[z1,z2,z3,z4,z5,z907]),(0,[z1,z2,z3,z546,z5,z240]),(0,[z1,z244,z3,z4,z5,z70])]],
   [[(0,[z1,z2,z3,z908,z4,z6]),(0,[z1,z2,z909,z4,z5,z6]),(0,[z1,z910,z3,z4,z5,z6]),(0,[z1,z911,z3,z4,z5,z6]),(0,[z1,z244,z3,z4,z360,z6]),(0,[z1,z2,z111,z4,z5,z759]),(0,[z912,z2,z3,z4,z5,z6])],[(0,[z1,z786,z2,z3,z4,z6]),(0,[z1,z913,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z914,z6]),(0,[z1,z2,z3,z4,z5,z915]),(0,[z1,z3,z4,z5,z916,z6])],[(0,[z1,z2,z3,z4,z5,z917]),(0,[z1,z918,z3,z4,z5,z6]),(0,[z1,z108,z245,z2,z4,z5])],[(0,[z1,z2,z4,z919,z5,z6]),(0,[z1,z2,z3,z920,z4,z5]),(0,[z1,z921,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z922,z6]),(0,[z1,z923,z3,z4,z5,z6]),(0,[z1,z2,z33,z58,z4,z34])],[(0,[z1,z924,z3,z4,z5,z6]),(0,[z1,z2,z925,z4,z5,z6]),(0,[z1,z26,z3,z103,z5,z124]),(0,[z1,z2,z3,z16,z158,z6]),(0,[z1,z926,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z711,z75])],[(0,[z1,z2,z3,z927,z5,z6]),(0,[z10,z1,z2,z3,z102,z5]),(0,[z10,z168,z2,z3,z4,z5]),(0,[z928,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z929])],[(0,[z1,z2,z3,z4,z930,z6])],[(0,[z1,z26,z3,z753,z5,z6]),(0,[z1,z2,z95,z3,z4,z74])]],
   [[(0,[z1,z2,z3,z351,z158,z6]),(0,[z931,z2,z3,z4,z5,z6]),(0,[z1,z63,z4,z29,z5,z6]),(0,[z1,z3,z103,z5,z20,z6])],[(0,[z1,z2,z3,z4,z932,z6]),(0,[z1,z933,z3,z4,z5,z6]),(0,[z1,z19,z3,z4,z6,z183]),(0,[z1,z28,z2,z3,z4,z287])],[(0,[z17,z18,z3,z4,z5,z6]),(0,[z1,z2,z3,z934,z5,z6]),(0,[z1,z935,z2,z3,z4,z6]),(0,[z1,z4,z5,z6,z439,z183])],[(0,[z104,z1,z51,z4,z5,z6]),(0,[z1,z31,z241,z2,z3,z4]),(0,[z1,z2,z3,z4,z5,z936]),(0,[z1,z2,z33,z3,z4,z373]),(1,[z1,z108,z2,z4,z360])],[(0,[z1,z3,z4,z5,z6,z937]),(0,[z55,z2,z3,z4,z5,z728]),(0,[z1,z2,z3,z753,z5,z6]),(0,[z1,z2,z3,z4,z456,z70]),(0,[z1,z2,z3,z938,z4,z5])],[(0,[z1,z39,z2,z256,z4,z5]),(0,[z1,z939,z228,z3,z4,z6]),(0,[z1,z2,z33,z626,z4,z6]),(0,[z1,z126,z3,z4,z5,z68])],[(0,[z1,z940,z170,z3,z4,z5]),(0,[z1,z941,z3,z4,z5,z6]),(0,[z1,z3,z4,z29,z265,z6]),(0,[z1,z2,z3,z4,z5,z942]),(1,[z1,z2,z3,z4,z711])],[(0,[z1,z2,z3,z4,z943,z6]),(0,[z1,z944,z3,z4,z5,z6]),(0,[z1,z2,z3,z156,z332,z5]),(0,[z1,z33,z4,z146,z34,z6])]],
   [[(0,[z1,z105,z3,z4,z5,z448]),(0,[z1,z2,z3,z945,z5,z6]),(0,[z1,z19,z3,z4,z420,z6]),(0,[z1,z2,z3,z243,z5,z6])],[(0,[z1,z100,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z715,z6]),(0,[z1,z2,z3,z4,z5,z946])],[(0,[z1,z2,z3,z947,z4,z6]),(0,[z1,z69,z3,z4,z5,z463]),(0,[z1,z2,z33,z4,z802,z6])],[(0,[z1,z67,z809,z4,z5,z6]),(0,[z1,z2,z3,z948,z5,z6])],[(0,[z1,z100,z69,z3,z4,z6]),(0,[z1,z2,z3,z4,z949,z6]),(0,[z1,z306,z344,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z950])],[(0,[z1,z2,z344,z4,z5,z6]),(0,[z55,z53,z2,z3,z4,z5]),(0,[z55,z585,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z951])],[(0,[z1,z2,z952,z4,z5,z6]),(0,[z1,z49,z684,z4,z5,z6]),(0,[z50,z1,z809,z4,z5,z6]),(0,[z1,z953,z2,z3,z4,z5])],[(0,[z1,z39,z3,z4,z29,z5]),(0,[z1,z2,z4,z284,z5,z6])]],
   [[(0,[z1,z940,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z954]),(0,[z1,z955,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z419]),(0,[z1,z956,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z957,z6]),(0,[z1,z2,z3,z4,z373,z5]),(0,[z1,z958,z3,z4,z5,z6])],[(0,[z2,z757,z3,z4,z5,z6]),(0,[z1,z2,z3,z102,z5,z240]),(0,[z1,z67,z3,z4,z5,z448])],[(0,[z1,z2,z3,z959,z5,z6]),(0,[z1,z960,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z142,z258]),(0,[z1,z160,z2,z3,z5,z121]),(0,[z1,z3,z4,z5,z710,z6])],[],[],[(0,[z274,z105,z3,z4,z5,z6]),(0,[z1,z26,z3,z187,z5,z6])],[(0,[z1,z2,z3,z4,z961,z6]),(0,[z1,z2,z3,z5,z121,z257]),(0,[z1,z2,z33,z4,z34,z6]),(0,[z1,z2,z3,z4,z6,z962])]],
   [[(0,[z57,z2,z3,z822,z5,z6]),(0,[z1,z194,z2,z99,z5,z6]),(0,[z1,z2,z3,z246,z491,z6])],[(0,[z1,z125,z3,z118,z5,z6]),(0,[z1,z306,z3,z4,z143,z6]),(0,[z1,z19,z2,z3,z4,z287])],[(0,[z1,z2,z3,z4,z143,z6]),(0,[z1,z2,z3,z4,z963,z6]),(0,[z1,z25,z3,z118,z5,z6]),(0,[z1,z2,z63,z4,z5,z419])],[(0,[z1,z125,z2,z256,z5,z6]),(0,[z1,z306,z317,z4,z5,z6]),(0,[z1,z964,z3,z4,z5,z6]),(0,[z55,z232,z3,z4,z5,z24]),(0,[z1,z108,z2,z4,z326,z5])],[(0,[z1,z2,z3,z4,z965,z6]),(0,[z1,z2,z317,z4,z5,z6]),(0,[z57,z1,z2,z3,z248,z5]),(0,[z1,z2,z3,z4,z360,z70])],[(0,[z1,z2,z4,z5,z6,z966]),(0,[z1,z2,z3,z4,z5,z728]),(0,[z1,z967,z2,z3,z4,z5]),(1,[z1,z3,z4,z710,z6]),(0,[z679,z1,z2,z3,z156,z5])],[(0,[z1,z212,z3,z4,z5,z6]),(0,[z1,z167,z3,z4,z5,z258]),(0,[z202,z2,z3,z822,z5,z6]),(0,[z1,z2,z111,z3,z4,z360])],[(0,[z1,z125,z241,z2,z3,z6]),(0,[z1,z31,z298,z2,z3,z5]),(0,[z1,z2,z968,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z969,z6]),(0,[z1,z2,z3,z970,z5,z6]),(0,[z1,z2,z3,z243,z5,z64])],[(0,[z1,z2,z4,z971,z5,z6]),(0,[z86,z2,z745,z4,z5,z6]),(0,[z972,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z759,z83])],[(0,[z1,z2,z344,z4,z5,z257])],[(0,[z1,z973,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z348,z6]),(0,[z1,z3,z4,z373,z146,z5]),(0,[z1,z2,z3,z116,z4,z609])],[(0,[z1,z18,z3,z268,z4,z6])],[(0,[z86,z184,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z6,z974]),(0,[z1,z28,z2,z3,z4,z429]),(0,[z1,z2,z4,z5,z374,z759])],[(0,[z17,z298,z18,z3,z5,z6]),(0,[z1,z2,z4,z5,z6,z975]),(0,[z1,z2,z3,z4,z5,z976]),(0,[z1,z2,z3,z4,z977,z5]),(0,[z1,z2,z3,z4,z5,z978]),(0,[z1,z2,z4,z284,z265,z6]),(0,[z1,z2,z3,z979,z4,z6]),(0,[z1,z244,z111,z3,z4,z5])]],
   [[(0,[z1,z980,z3,z4,z5,z6]),(0,[z1,z2,z344,z4,z143,z6]),(0,[z1,z2,z3,z4,z265,z419]),(0,[z1,z3,z4,z29,z6,z355]),(0,[z1,z69,z3,z4,z5,z173])],[(0,[z1,z2,z3,z981,z5,z6]),(0,[z202,z362,z2,z3,z8,z5]),(0,[z61,z106,z3,z4,z88,z6])],[(0,[z274,z757,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z982,z6]),(0,[z1,z3,z4,z5,z6,z377])],[(0,[z1,z125,z306,z3,z5,z6]),(0,[z1,z2,z4,z5,z374,z605])],[(0,[z1,z25,z306,z3,z5,z6]),(0,[z1,z2,z54,z286,z5,z6]),(0,[z1,z28,z3,z4,z6,z183]),(0,[z1,z2,z3,z4,z74,z75])],[(0,[z1,z31,z3,z4,z5,z68]),(0,[z1,z2,z4,z983,z5,z6]),(0,[z1,z984,z3,z4,z5,z6]),(0,[z1,z362,z2,z3,z4,z5]),(0,[z1,z2,z63,z4,z348,z6])],[(0,[z1,z2,z3,z4,z5,z985]),(1,[z1,z3,z4,z5,z766])],[(0,[z1,z2,z3,z4,z143,z257]),(0,[z1,z3,z4,z5,z68,z545])]],
   [[(0,[z1,z2,z3,z4,z5,z986]),(0,[z1,z987,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z988,z6]),(0,[z1,z2,z3,z4,z5,z287])],[(0,[z1,z125,z39,z2,z3,z5]),(0,[z1,z2,z317,z4,z5,z257]),(0,[z1,z28,z3,z4,z29,z6]),(0,[z1,z3,z4,z5,z766,z173]),(0,[z1,z131,z3,z405,z132,z6])],[(0,[z17,z125,z18,z3,z5,z6]),(0,[z1,z167,z317,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z989]),(0,[z1,z527,z2,z3,z4,z75]),(0,[z1,z990,z3,z4,z5,z6])],[(0,[z1,z3,z4,z991,z5,z6]),(0,[z1,z992,z228,z3,z4,z6])],[(0,[z55,z2,z3,z4,z5,z24]),(0,[z1,z19,z3,z4,z5,z124]),(0,[z1,z993,z3,z4,z5,z6])],[(0,[z1,z994,z3,z4,z5,z6]),(0,[z1,z2,z3,z995,z4,z5])],[(0,[z1,z2,z3,z4,z5,z996]),(0,[z1,z2,z997,z4,z5,z6]),(0,[z1,z2,z3,z4,z74,z349])],[(0,[z1,z998,z3,z4,z5,z6]),(0,[z1,z2,z317,z4,z143,z6]),(0,[z1,z999,z3,z4,z5,z6]),(0,[z97,z1,z2,z90,z4,z6]),(0,[z1000,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1001])]],
   [[(0,[z104,z1,z170,z4,z5,z6]),(0,[z1,z2,z3,z4,z1002,z6]),(0,[z1,z2,z3,z4,z1003,z6]),(0,[z489,z105,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1004,z5]),(0,[z1,z1005,z3,z4,z5,z6]),(0,[z1,z2,z3,z246,z756,z6])],[(0,[z1,z100,z3,z4,z68,z6]),(0,[z1,z26,z103,z284,z5,z6]),(0,[z1,z2,z33,z4,z70,z374]),(0,[z1,z108,z2,z4,z360,z83]),(0,[z1,z108,z244,z3,z4,z5])],[(0,[z1,z1006,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1007,z6]),(0,[z50,z1,z3,z268,z4,z6])],[(0,[z1,z1008,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1009,z6]),(0,[z86,z170,z87,z4,z5,z6]),(0,[z57,z171,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z816])],[(0,[z1,z2,z3,z4,z1010,z6]),(0,[z652,z2,z166,z4,z5,z6]),(0,[z1,z310,z323,z2,z3,z4]),(1,[z1,z2,z3,z756,z6])],[(0,[z1,z241,z2,z3,z4,z6]),(0,[z1,z2,z1011,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z124]),(0,[z1,z19,z2,z3,z4,z429]),(0,[z1,z2,z3,z1012,z4,z6]),(0,[z1,z2,z3,z5,z121,z816])],[(0,[z1,z310,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1013]),(0,[z1,z1014,z3,z4,z5,z6]),(0,[z1,z2,z92,z708,z5,z6])]],
   [[(0,[z1,z1015,z3,z4,z5,z6]),(0,[z1,z2,z54,z92,z5,z6])],[(0,[z1,z31,z2,z256,z4,z5]),(0,[z1,z899,z2,z3,z4,z6]),(0,[z1,z1016,z3,z4,z5,z6]),(0,[z101,z2,z3,z4,z157,z6]),(0,[z1,z2,z1017,z4,z5,z6]),(0,[z1,z1018,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1019,z6]),(0,[z1,z2,z3,z633,z132,z6]),(0,[z1,z69,z2,z95,z4,z5]),(0,[z1,z2,z3,z4,z70,z381]),(0,[z1,z2,z3,z5,z816,z6])],[(0,[z1,z1020,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1021,z4,z6]),(0,[z1,z2,z3,z116,z4,z70])],[(0,[z1,z2,z4,z5,z6,z1022]),(0,[z1,z992,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1023]),(0,[z1,z69,z3,z4,z5,z766])],[(0,[z104,z1,z69,z4,z5,z6])],[(0,[z2,z3,z4,z1024,z5,z6]),(0,[z1,z2,z33,z4,z219,z6]),(0,[z1,z2,z3,z4,z802,z6])],[(0,[z1,z2,z3,z4,z5,z1025]),(0,[z1,z1026,z3,z4,z5,z6]),(0,[z1,z1027,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1028,z6]),(0,[z1,z120,z2,z3,z236,z5]),(0,[z1,z3,z4,z5,z68,z766])]],
   [[(0,[z1,z2,z3,z4,z1029,z6]),(0,[z1,z2,z3,z4,z5,z1030]),(0,[z1,z2,z3,z4,z5,z1031]),(0,[z1,z2,z63,z4,z5,z124]),(0,[z1,z1032,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1033,z6]),(0,[z202,z2,z3,z417,z5,z6]),(1,[z2,z3,z4,z715,z6]),(0,[z1,z37,z3,z4,z5,z6]),(0,[z1,z28,z3,z4,z405,z6])],[(0,[z1,z306,z3,z4,z5,z258]),(0,[z50,z1,z323,z51,z4,z5]),(0,[z1,z19,z434,z3,z4,z6]),(0,[z1,z2,z3,z4,z74,z429]),(0,[z1,z2,z4,z802,z34,z6]),(0,[z1,z108,z2,z4,z516,z83])],[(0,[z1,z2,z3,z5,z1034,z6]),(0,[z1,z2,z3,z4,z5,z258]),(0,[z1,z2,z3,z4,z5,z1035]),(0,[z1,z2,z3,z4,z360,z6]),(0,[z1,z1036,z3,z4,z5,z6])],[(0,[z1,z105,z3,z62,z4,z6]),(0,[z1,z2,z3,z4,z5,z1037]),(0,[z1,z2,z3,z4,z1038,z6])],[(0,[z1,z2,z3,z4,z5,z1039]),(0,[z1,z2,z1040,z4,z5,z6]),(0,[z2,z3,z4,z715,z5,z6]),(0,[z1,z2,z4,z1041,z5,z6]),(0,[z1,z108,z4,z5,z377,z83])],[(0,[z104,z1,z125,z2,z5,z6]),(0,[z1,z323,z105,z3,z4,z5]),(0,[z1,z26,z306,z3,z5,z6]),(0,[z61,z424,z3,z4,z88,z6]),(0,[z1,z911,z3,z4,z5,z429])],[]],
   [[(0,[z2,z3,z745,z4,z5,z6]),(0,[z1,z2,z3,z1042,z4,z6]),(0,[z1,z2,z3,z1043,z5,z6])],[(0,[z1,z2,z3,z1044,z5,z6]),(0,[z1,z507,z3,z4,z5,z6]),(0,[z1,z3,z4,z6,z183,z355]),(1,[z1,z2,z4,z802,z6]),(0,[z1,z2,z95,z4,z5,z374]),(0,[z1,z2,z3,z4,z5,z725])],[(0,[z1,z2,z3,z1045,z5,z6]),(0,[z50,z1,z310,z51,z4,z6]),(0,[z1,z19,z3,z4,z601,z6]),(0,[z1,z2,z3,z4,z70,z429])],[(0,[z1,z125,z19,z3,z5,z6]),(0,[z1,z298,z2,z256,z5,z6]),(0,[z1046,z1,z2,z4,z5,z6]),(0,[z1,z2,z745,z4,z5,z6]),(0,[z202,z2,z3,z8,z142,z6]),(0,[z1,z1047,z3,z4,z5,z6]),(0,[z1,z2,z3,z268,z4,z6]),(0,[z1,z2,z3,z158,z756,z6]),(0,[z1,z2,z3,z5,z816,z240])],[(0,[z1,z2,z3,z4,z5,z1048]),(0,[z1,z2,z3,z156,z5,z257])],[(0,[z1,z2,z3,z4,z5,z429])],[(0,[z1,z809,z51,z4,z5,z6]),(0,[z1,z67,z3,z62,z4,z6]),(0,[z1,z2,z3,z4,z265,z124])],[(0,[z1,z2,z3,z4,z5,z1049]),(0,[z1,z126,z2,z3,z4,z355])]],
   [[(0,[z17,z31,z18,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1050]),(0,[z1,z2,z3,z4,z1051,z6]),(0,[z50,z1,z3,z4,z5,z448]),(0,[z1,z2,z3,z453,z5,z6])],[(0,[z1,z2,z344,z4,z5,z258]),(0,[z1,z939,z2,z3,z4,z6]),(0,[z50,z1,z3,z62,z4,z6]),(0,[z1,z126,z3,z4,z5,z662])],[(0,[z1,z125,z3,z29,z5,z6]),(0,[z1,z2,z3,z1052,z5,z6]),(0,[z1,z2,z3,z4,z1053,z6]),(0,[z1,z1054,z3,z4,z5,z6])],[(0,[z1,z2,z1055,z4,z5,z6]),(0,[z1,z108,z2,z4,z360,z6])],[(0,[z104,z1,z298,z2,z5,z6]),(0,[z1,z2,z3,z1056,z4,z5]),(0,[z1,z2,z3,z1057,z4,z6]),(0,[z55,z228,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z516,z6])],[(0,[z1,z2,z3,z4,z5,z1058]),(0,[z1,z2,z1059,z4,z5,z6]),(1,[z2,z3,z4,z5,z728]),(0,[z1,z2,z111,z660,z4,z5])],[(0,[z202,z167,z3,z8,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1060]),(0,[z101,z625,z2,z3,z4,z6]),(0,[z2,z3,z4,z88,z715,z6]),(0,[z1,z2,z3,z276,z62,z4]),(0,[z1,z2,z1061,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z1062,z6]),(0,[z1,z2,z3,z4,z1063,z6]),(0,[z1,z2,z111,z513,z4,z5])],[(0,[z1,z19,z3,z4,z405,z6]),(0,[z1,z37,z33,z4,z34,z6]),(1,[z1,z2,z4,z5,z759]),(0,[z1,z3,z4,z1064,z5,z6])],[],[(0,[z104,z1,z4,z5,z68,z6]),(0,[z1,z2,z3,z1065,z5,z6]),(0,[z1,z2,z3,z4,z1066,z6]),(0,[z1,z49,z169,z4,z5,z6]),(0,[z1,z2,z4,z284,z5,z419]),(0,[z1,z2,z33,z243,z34,z6]),(0,[z1,z1067,z3,z4,z5,z6]),(0,[z1,z2,z631,z4,z5,z374])],[(1,[z757,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1068]),(0,[z1,z2,z3,z5,z1069,z6])],[(0,[z202,z1,z2,z3,z248,z5]),(0,[z1,z108,z2,z4,z5,z429]),(0,[z97,z1,z2,z4,z802,z6])],[(0,[z1,z2,z3,z4,z143,z258]),(0,[z1,z37,z3,z58,z4,z5]),(0,[z1,z108,z2,z4,z5,z759])],[(0,[z1,z757,z3,z4,z5,z6]),(0,[z1,z108,z2,z33,z4,z74])]],
   [[(0,[z1,z2,z317,z4,z5,z258]),(0,[z1,z3,z4,z405,z265,z6]),(0,[z1,z2,z3,z4,z1070,z6])],[(0,[z2,z3,z822,z8,z5,z6]),(0,[z1,z244,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1071,z6]),(0,[z1,z3,z4,z1072,z5,z6])],[(0,[z207,z18,z3,z4,z5,z6]),(0,[z1,z2,z809,z4,z5,z6]),(0,[z1,z69,z3,z4,z5,z681]),(0,[z1,z28,z3,z4,z710,z6])],[(0,[z40,z2,z659,z4,z5,z6])],[(0,[z1,z106,z3,z4,z5,z6]),(0,[z1,z1073,z3,z4,z5,z6])],[(0,[z1,z2,z33,z4,z34,z429]),(0,[z1,z3,z4,z74,z183,z75])],[(0,[z1,z2,z3,z1074,z5,z6]),(0,[z10,z2,z3,z4,z5,z728]),(0,[z1,z69,z228,z3,z4,z5]),(0,[z1,z2,z4,z119,z802,z6]),(0,[z1,z1075,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1076]),(0,[z1077,z1,z2,z4,z5,z6]),(0,[z42,z1,z19,z3,z4,z6]),(0,[z1,z2,z3,z4,z1078,z6])]],
   [[(0,[z1,z1079,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z1080,z6]),(0,[z202,z2,z3,z248,z8,z5]),(0,[z1,z1081,z3,z4,z5,z6]),(0,[z1,z3,z4,z29,z5,z124]),(0,[z1,z2,z3,z453,z5,z64]),(0,[z1,z2,z33,z453,z34,z6])],[(0,[z1,z2,z3,z1082,z5,z6]),(0,[z1,z2,z3,z4,z5,z448])],[(0,[z1,z31,z100,z2,z3,z4]),(0,[z1,z2,z3,z4,z1083,z6]),(0,[z375,z2,z87,z4,z5,z6])],[(0,[z1,z2,z3,z1084,z5,z6]),(0,[z1,z3,z4,z5,z6,z1085]),(0,[z1,z19,z3,z550,z4,z6]),(0,[z1,z2,z95,z4,z5,z83])],[(0,[z1,z2,z1086,z4,z5,z6]),(0,[z1,z2,z3,z248,z4,z5]),(0,[z1,z2,z4,z1087,z5,z6]),(0,[z1,z2,z33,z4,z349,z6]),(0,[z1,z2,z95,z116,z4,z5])],[(0,[z1,z241,z106,z3,z4,z6]),(0,[z1,z2,z1088,z4,z5,z6]),(0,[z1,z159,z2,z3,z132,z6]),(0,[z1,z1089,z3,z4,z5,z6])],[(0,[z86,z2,z87,z4,z5,z6]),(0,[z1,z3,z4,z146,z5,z6]),(0,[z1,z2,z4,z284,z348,z6]),(0,[z1,z2,z33,z4,z373,z34]),(0,[z1,z1090,z2,z3,z4,z5])],[(0,[z17,z100,z18,z3,z4,z6]),(0,[z1,z100,z39,z2,z3,z4]),(0,[z1,z2,z3,z4,z348,z419])]],
   [[(0,[z1,z1091,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z1092]),(0,[z1,z1093,z3,z4,z5,z6]),(0,[z1,z26,z557,z3,z5,z6]),(0,[z1,z798,z2,z3,z4,z5]),(0,[z1,z3,z809,z4,z5,z6]),(0,[z1,z126,z3,z4,z5,z183])],[(0,[z40,z2,z745,z4,z5,z6]),(0,[z1,z2,z3,z1094,z5,z6]),(0,[z1,z1095,z2,z3,z5,z6]),(0,[z1,z108,z2,z21,z4,z5]),(0,[z1,z2,z1096,z4,z5,z6])],[(0,[z1,z49,z170,z4,z5,z6]),(0,[z1,z2,z1097,z4,z5,z6]),(0,[z1,z2,z3,z4,z1098,z6]),(1,[z1,z2,z33,z4,z373]),(0,[z1,z3,z4,z5,z6,z1099]),(0,[z1,z2,z3,z156,z5,z816]),(0,[z1,z2,z3,z116,z4,z711])],[(0,[z1,z3,z4,z1100,z5,z6]),(0,[z1,z2,z3,z4,z5,z1101]),(0,[z1,z2,z1102,z4,z5,z6]),(0,[z1,z2,z3,z1103,z5,z6]),(0,[z1,z131,z2,z3,z132,z6])],[(0,[z1,z1104,z2,z3,z4,z5]),(0,[z1,z1105,z3,z4,z5,z6]),(0,[z1,z2,z3,z756,z132,z6])],[(0,[z1,z120,z2,z3,z5,z121]),(0,[z1,z507,z3,z4,z74,z75])],[(0,[z1,z2,z3,z4,z5,z1106]),(0,[z1,z2,z3,z822,z5,z6]),(0,[z2,z3,z4,z5,z728,z11]),(0,[z1,z2,z3,z4,z1107,z6]),(0,[z1,z2,z3,z4,z70,z711])]]]

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
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 545).take 543) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1088).take 2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1090)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [545, 543, 2] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 138).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 138).take 118).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [138, 118] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_45668

theorem PEqualNP.Outside.L_meta_45668 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241824 * 2 ^ 32 + 3940592128) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241824 * 2 ^ 32 + 3940592128) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45668.solve