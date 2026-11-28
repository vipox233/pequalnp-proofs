import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38571

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
  Nat.testBit (4276677320 * 2 ^ 32 + 3941133000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x90002344c411a262#64 ++ 0x480011a26208d131#64 ++ 0xed0067cfccf3e7e7#64 ++ 0xf68033e7e679f3f3#64 : BitVec 256),
   (0x200388921944490d#64 ++ 0x1001c4490ca22486#64 ++ 0xdd8798f27f4c793f#64 ++ 0xeec3cc793fa63c9f#64 : BitVec 256),
   (0xc038152c628a9630#64 ++ 0x601c0a9631454b18#64 ++ 0xbf781f3c738f9e39#64 ++ 0xdfbc0f9e39c7cf1c#64 : BitVec 256),
   (0x005dc03b03e01d81#64 ++ 0x802ee01d81f00ec0#64 ++ 0x7effe03f83f01fc1#64 ++ 0xbf7ff01fc1f80fe0#64 : BitVec 256),
   (0x01eefec003ff6000#64 ++ 0x00f77f6001ffb000#64 ++ 0xfbffffc003ffe001#64 ++ 0x7dffffe001fff000#64 : BitVec 256),
   (0x02f77ffffc000000#64 ++ 0x017bbffffe000000#64 ++ 0xfafffffffc000000#64 ++ 0xfd7ffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [8, 6]⟩, ⟨.and, [9, 4]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x7effe03f83f01fc1 0xbf7ff01fc1f80fe0

def z1 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfbffffc003ffe001 0x7dffffe001fff000

def z2 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfafffffffc000000 0xfd7ffffffe000000

def z3 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xdd8798f27f4c793f 0xeec3cc793fa63c9f

def z4 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xed0067cfccf3e7e7 0xf68033e7e679f3f3

def z5 : W := mkw 0x91ffffffc7ffffe3 0xc8ffffffe3fffff1 0xffffffffcfffffe7 0xffffffffe7fffff3

def z6 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xbf781f3c738f9e39 0xdfbc0f9e39c7cf1c

def z7 : W := mkw 0x005d403b02a01d81 0x802ea01d81500ec0 0x2678603f80b01fc0 0x933c301fc0580fe0

def z8 : W := mkw 0xc030152c600a8230 0x60180a9630054118 0xbb781f3c700f8038 0xddbc0f9e3807c01c

def z9 : W := mkw 0x91a23fc4c41fe262 0x48d11fe2620ff131 0x81001fc04c0fe026 0x40800fe02607f013

def z10 : W := mkw 0x91eeffc4c7ffe262 0x48f77fe263fff131 0xffffffcfcfffe7e7 0xffffffe7e7fff3f3

def z11 : W := mkw 0x22c7ead39d44490d 0x1163f569cea22486 0x4087e0c38c406106 0x2043f061c6203083

def z12 : W := mkw 0xc211013ffc009630 0x6108809ffe004b18 0x0400003ffc001e38 0x8200001ffe000f1c

def z13 : W := mkw 0x8000010440008220 0x4000008220004110 0xad00070c40838621 0xd68003862041c310

def z14 : W := mkw 0xd038376ce69bb672 0x681c1bb6734ddb39 0xff787fffffffffff 0xffbc3fffffffffff

def z15 : W := mkw 0x21efdc921bee490d 0x10f7ee490df72486 0xdfff98f27f4c793f 0xefffcc793fa63c9f

def z16 : W := mkw 0x01dfeafb03f57d81 0x80eff57d81fabec0 0x7effe0ff83f07fc1 0xbf7ff07fc1f83fe0

def z17 : W := mkw 0x01eedc8003ee4000 0x00f76e4001f72000 0xbbff9f00038f8001 0x5dffcf8001c7c000

def z18 : W := mkw 0x200100121800090d 0x100080090c000486 0x040000327c00193e 0x820000193e000c9f

def z19 : W := mkw 0x22f77ffffc00090d 0x117bbffffe000486 0xfefffffffc00193e 0xff7ffffffe000c9f

def z20 : W := mkw 0x00f67fec60000000 0x007b3ff630000000 0xfafffffc70000000 0xfd7ffffe38000000

def z21 : W := mkw 0xc1feffec63fff630 0x60ff7ff631fffb18 0xfffffffc73fffe39 0xfffffffe39ffff1c

def z22 : W := mkw 0x02f4776de4000000 0x017a3bb6f2000000 0x2278670d80000000 0x113c3386c0000000

def z23 : W := mkw 0x200080000144490d 0x1000400000a22486 0x05000000034c793f 0x0280000001a63c9f

def z24 : W := mkw 0x0000000000000000 0x0000000000000000 0x6c00600f80f007c1 0xb6003007c07803e0

def z25 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xff787f3ff3ff9ff9 0xffbc3f9ff9ffcffc

def z26 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0xfaffffc000000000 0x7d7fffe000000000

def z27 : W := mkw 0x00e6fec001444000 0x00737f6000a22000 0xfbffffc0034c6001 0x7dffffe001a63000

def z28 : W := mkw 0xd0082344c69bb672 0x680411a2634ddb39 0xed0067cfcfffffff 0xf68033e7e7ffffff

def z29 : W := mkw 0x0211013ffc001d81 0x8108809ffe000ec0 0x0400003ffc001fc0 0x8200001ffe000fe0

def z30 : W := mkw 0x0000800001444000 0x0000400000a22000 0x01000000034c6001 0x0080000001a63000

def z31 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xfd87f8fffffc7fff 0xfec3fc7ffffe3fff

def z32 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xe90067cd80f3e6c1 0x748033e6c079f360

def z33 : W := mkw 0x202b9c921bce490d 0x1015ce490de72486 0xffff9ff27fcff93f 0xffffcff93fe7fc9f

def z34 : W := mkw 0x01c6eac001756000 0x00e3756000bab000 0x4087e0c000706000 0x2043f06000383000

def z35 : W := mkw 0x90002344c411a262 0x480011a26208d131 0x0000070000038000 0x000003800001c000

def z36 : W := mkw 0x00281400028a0000 0x00140a0001450000 0xbb781f00038f8001 0x5dbc0f8001c7c000

def z37 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0x0100000003ffe001 0x0080000001fff000

def z38 : W := mkw 0x0030152c60000000 0x00180a9630000000 0xba781f3c70000000 0xdd3c0f9e38000000

def z39 : W := mkw 0x03ff7ffffebb2000 0x01ffbfffff5d9000 0xfafffffffcb38000 0xfd7ffffffe59c000

def z40 : W := mkw 0x900022408411a262 0x480011204208d131 0x450060c38cf3e7e7 0x22803061c679f3f3

def z41 : W := mkw 0x004cc00003e00000 0x0026600001f00000 0x7affe00003f00001 0x3d7ff00001f80000

def z42 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x7affe03f80000000 0xbd7ff01fc0000000

def z43 : W := mkw 0x90032bd6dc11a262 0x480195eb6e08d131 0xfd87fffffcf3e7e7 0xfec3fffffe79f3f3

def z44 : W := mkw 0xc2fc776de68a9630 0x617e3bb6f3454b18 0x2278670d80838600 0x113c3386c041c300

def z45 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0xfffff83ff3fc1ff9 0xfffffc1ff9fe0ffc

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x9d001830730c1839 0xce800c1839860c1c

def z47 : W := mkw 0x004ce24003f12000 0x0026712001f89000 0xfbffe7c003f3e001 0x7dfff3e001f9f000

def z48 : W := mkw 0x905de37fc7f1bfe3 0xc82ef1bfe3f8dff1 0xffffe7ffcff3ffe7 0xfffff3ffe7f9fff3

def z49 : W := mkw 0x0108800003ee4000 0x0084400001f72000 0x00000000030c0000 0x0000000001860000

def z50 : W := mkw 0x01eedc8003ee4000 0x00f76e4001f72000 0x12ff9800030c0000 0x097fcc0001860000

def z51 : W := mkw 0x205dc03b03e45d8d 0x902ee01d81f22ec6 0x7fffe03f83fc7fff 0xbffff01fc1fe3fff

def z52 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x0400000003f01fc1 0x0200000001f80fe0

def z53 : W := mkw 0x21effed21bff690d 0x10f7ff690dffb486 0xfffffff27ffff93f 0xfffffff93ffffc9f

def z54 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xc10067c3cc73e1e6 0x608033e1e639f0f3

def z55 : W := mkw 0xb003abd6dd55eb6f 0x5801d5eb6eaaf5b7 0xfd87ffffffffffff 0xfec3ffffffffffff

def z56 : W := mkw 0x22f7fffffd44490d 0x117bfffffea22486 0xffffffffff4c793f 0xffffffffffa63c9f

def z57 : W := mkw 0xc2ff7ffffe8a9630 0x617fbfffff454b18 0xffffffffff8f9e39 0xffffffffffc7cf1c

def z58 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xa3781f0c708f8638 0x51bc0f863847c31c

def z59 : W := mkw 0x0044400100200080 0x8022200080100040 0x00006001803000c0 0x00003000c0180060

def z60 : W := mkw 0x01fffefb03ff7d81 0x80ffff7d81ffbec0 0xfbfffff003fff801 0x7dfffff801fffc00

def z61 : W := mkw 0x01ec764002bb2000 0x00f63b20015d9000 0x2278670000b38000 0x113c33800059c000

def z62 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x12ff983030000000 0x097fcc1818000000

def z63 : W := mkw 0x200080000144490d 0x1000400000a22486 0x0000000000406106 0x0000000000203083

def z64 : W := mkw 0x01fefee903ff7480 0x80ff7f7481ffba40 0xfbffffcd83ffe6c1 0x7dffffe6c1fff360

def z65 : W := mkw 0x0002088000000000 0x0001044000000000 0xd88798c000000000 0x6c43cc6000000000

def z66 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x7effe03f80f007c1 0xbf7ff01fc07803e0

def z67 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfffffffffcf3e7e7 0xfffffffffe79f3f3

def z68 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x12ff803003001800 0x097fc01801800c00

def z69 : W := mkw 0xb000a344c555eb6f 0x580051a262aaf5b7 0xed0067cfcfffffff 0xf68033e7e7ffffff

def z70 : W := mkw 0x22f77ffffc04400c 0x117bbffffe022006 0xfbfffffffc0c603e 0xfdfffffffe06301f

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z72 : W := mkw 0x20e7fed21944490d 0x1073ff690ca22486 0xfffffff27f4c793f 0xfffffff93fa63c9f

def z73 : W := mkw 0x0045c01301600981 0x8022e00980b004c0 0x5c87e033837019c1 0xae43f019c1b80ce0

def z74 : W := mkw 0x00eefec003e00000 0x00777f6001f00000 0xfaffffc003f00001 0x7d7fffe001f80000

def z75 : W := mkw 0x2003abd6dd44490d 0x1001d5eb6ea22486 0xfd87ffffff4c793f 0xfec3ffffffa63c9f

def z76 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xffffffc24fffe127 0xffffffe127fff093

def z77 : W := mkw 0x01fffefb03ff7d81 0x80ffff7d81ffbec0 0xffffffff83ffffc1 0xffffffffc1ffffe0

def z78 : W := mkw 0x0255413ffc000000 0x012aa09ffe000000 0x7affe03ffc000000 0xbd7ff01ffe000000

def z79 : W := mkw 0x0000010440000000 0x0000008220000000 0xa800070c40000000 0xd400038620000000

def z80 : W := mkw 0x0001801201400901 0x0000c00900a00480 0x5c87803203401901 0xae43c01901a00c80

def z81 : W := mkw 0x0055637fc4000000 0x002ab1bfe2000000 0xfaffe7ffcc000000 0xfd7ff3ffe6000000

def z82 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xffffffffff0c1839 0xffffffffff860c1c

def z83 : W := mkw 0x0211013ffc000000 0x0108809ffe000000 0x0000003ffc000000 0x8000001ffe000000

def z84 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xa10067cdccb3e6e6 0x508033e6e659f373

def z85 : W := mkw 0x02a33fd6fc000000 0x01519feb7e000000 0xd8879ff27c000000 0xec43cff93e000000

def z86 : W := mkw 0x01e6fec001756000 0x00f37f6000bab000 0xfaffffc000706000 0x7d7fffe000383000

def z87 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xffffffcf83ffe7c1 0xffffffe7c1fff3e0

def z88 : W := mkw 0x0002888001444000 0x0001444000a22000 0xdd8798f0734c7839 0xeec3cc7839a63c1c

def z89 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfefffffffcf007c1 0xff7ffffffe7803e0

def z90 : W := mkw 0x0000000000000000 0x0000000000000000 0x10001830330c1818 0x08000c1819860c0c

def z91 : W := mkw 0x200208801804400c 0x100104400c022006 0x9d0018f07f0c783f 0xce800c783f863c1f

def z92 : W := mkw 0x02f7fffffd444000 0x017bfffffea22000 0xfbffffffff4c6001 0xfdffffffffa63000

def z93 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x1678183c730c1e38 0x8b3c0c1e39860f1c

def z94 : W := mkw 0x205fc8bb1be45d8d 0x902fe45d8df22ec6 0x7efff83fb3fc1fd9 0xbf7ffc1fd9fe0fec

def z95 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x62ffe00f80f007c0 0x317ff007c07803e0

def z96 : W := mkw 0x005c402902a01480 0x802e201481500a40 0x2278600d80b006c0 0x113c3006c0580360

def z97 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x918798f07f0c783e 0x48c3cc783f863c1f

def z98 : W := mkw 0x01fefee803ff7400 0x00ff7f7401ffba00 0xfffffffc03fffe01 0xfffffffe01ffff00

def z99 : W := mkw 0x00331dbe78000000 0x00198edf3c000000 0xfaff9ffe7c000000 0xfd7fcfff3e000000

def z100 : W := mkw 0xe03b9dbe7bcedf3d 0x701dcedf3de76f9e 0xffff9ffe7fcfff3f 0xffffcfff3fe7ff9f

def z101 : W := mkw 0x01c6eac001756000 0x00e3756000bab000 0xe987e7c000f3e001 0x74c3f3e00079f000

def z102 : W := mkw 0x900000000011a262 0x480000000008d131 0x0500000000f3e7e7 0x028000000079f3f3

def z103 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x0087800000000000 0x0043c00000000000

def z104 : W := mkw 0x01aabec003ff6000 0x00d55f6001ffb000 0x81001fc003ffe001 0x40800fe001fff000

def z105 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfbfffffffc03e026 0xfdfffffffe01f013

def z106 : W := mkw 0x00002344c4000000 0x000011a262000000 0xec0067cfccf007c1 0xf60033e7e67803e0

def z107 : W := mkw 0xc0201504600a8230 0x60100a8230054118 0x0000070000038000 0x000003800001c000

def z108 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xd88798f27f0c1818 0xec43cc793f860c0c

def z109 : W := mkw 0x01c7ead301756981 0x80e3f56980bab4c0 0x4087e0c3807061c0 0x2043f061c03830e0

def z110 : W := mkw 0x01ecf64003fb2000 0x00f67b2001fd9000 0x7affe70003f38001 0x3d7ff38001f9c000

def z111 : W := mkw 0x200080000144490d 0x1000400000a22486 0x00000000030c1818 0x0000000001860c0c

def z112 : W := mkw 0x22c7ead39d44490d 0x1163f569cea22486 0xdd87f8f3ff4c793f 0xeec3fc79ffa63c9f

def z113 : W := mkw 0x02c7ead39d600981 0x8163f569ceb004c0 0x4087e0c38c7001c0 0x2043f061c63800e0

def z114 : W := mkw 0x00281400028a0000 0x00140a0001450000 0xbf781f30738f9839 0xdfbc0f9839c7cc1c

def z115 : W := mkw 0x0211237ffc000000 0x010891bffe000000 0xe80067fffc000000 0xf40033fffe000000

def z116 : W := mkw 0x01fc766902bb3480 0x80fe3b34815d9a40 0x2278670d80b386c0 0x113c3386c059c360

def z117 : W := mkw 0x0045c01301600981 0x8022e00980b004c0 0x4087e003807001c0 0x2043f001c03800e0

def z118 : W := mkw 0x03ffffffffff6000 0x01ffffffffffb000 0xfbffffffffffe001 0xfdfffffffffff000

def z119 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x2278070c00838600 0x113c03860041c300

def z120 : W := mkw 0xb0022bc4dc15e26e 0x580115e26e0af137 0xed007fcffcffe7ff 0xf6803fe7fe7ff3ff

def z121 : W := mkw 0xc239153ffe8a9630 0x611c8a9fff454b18 0xbf781f3fff8f9e39 0xdfbc0f9fffc7cf1c

def z122 : W := mkw 0xc0180028028a9630 0x600c001401454b18 0x3f78003c038f9e39 0x9fbc001e01c7cf1c

def z123 : W := mkw 0x0018002802801400 0x000c001401400a00 0x3e78003c03801e01 0x9f3c001e01c00f00

def z124 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x32ffe03d83b01ec0 0x197ff01ec1d80f60

def z125 : W := mkw 0x03feffede7ff6000 0x01ff7ff6f3ffb000 0xfbffffcd83ffe001 0x7dffffe6c1fff000

def z126 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x6c00600f83f01fc1 0xb6003007c1f80fe0

def z127 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x10879830330c1818 0x0843cc1819860c0c

def z128 : W := mkw 0x0019803b03e01d81 0x800cc01d81f00ec0 0x0400003f83f01fc1 0x8200001fc1f80fe0

def z129 : W := mkw 0x00002344c4000000 0x000011a262000000 0xe80067cfcc000000 0xf40033e7e6000000

def z130 : W := mkw 0x12f77ffffc112042 0x097bbffffe089021 0xfafffffffc7061c6 0xfd7ffffffe3830e3

def z131 : W := mkw 0x00002344c4000000 0x000011a262000000 0x800007c04c000000 0x400003e026000000

def z132 : W := mkw 0x0000000000000000 0x0000000000000000 0x810000c04c006026 0x4080006026003013

def z133 : W := mkw 0x90000104c4008262 0x4800008262004131 0x0400000fcc0007e6 0x82000007e60003f3

def z134 : W := mkw 0x90002344c411a262 0x480011a26208d131 0x810007c04c03e026 0x408003e02601f013

def z135 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x408780c20c406106 0x2043c06106203083

def z136 : W := mkw 0xc030152c600a9630 0x60180a9630054b18 0x85001f3c700f9e38 0xc2800f9e3807cf1c

def z137 : W := mkw 0x01a23ec0001f6000 0x00d11f60000fb000 0x81001fc0000fe000 0x40800fe00007f000

def z138 : W := mkw 0x0001801201400901 0x0000c00900a00480 0xdd8780f24f407927 0xeec3c07927a03c93

def z139 : W := mkw 0x0008800003e00000 0x0004400001f00000 0x0000000003f00001 0x0000000001f80000

def z140 : W := mkw 0xc1feffec63fff630 0x60ff7ff631fffb18 0xfbffffcc03ffe601 0x7dffffe601fff300

def z141 : W := mkw 0x02ffffffffe01d81 0x817ffffffff00ec0 0xfefffffffff01fc1 0xff7ffffffff80fe0

def z142 : W := mkw 0xc108800003fff630 0x6084400001fffb18 0x0500000003fffe39 0x0280000001ffff1c

def z143 : W := mkw 0x200208801804400c 0x100104400c022006 0x810018c07c0c603e 0x40800c603e06301f

def z144 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xad00670dc0b386e1 0xd6803386e059c370

def z145 : W := mkw 0x02f75dbf78000000 0x017baedfbc000000 0xbaff9f3c70000000 0xdd7fcf9e38000000

def z146 : W := mkw 0x1000224084112042 0x0800112042089021 0x400060c38c7061c6 0x20003061c63830e3

def z147 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x0000000003001800 0x0000000001800c00

def z148 : W := mkw 0x905c636dc6b1b6e2 0xc82e31b6e358db71 0x2278670d80b386c0 0x113c3386c059c360

def z149 : W := mkw 0x1045e253857129c3 0x8822f129c2b894e1 0x4087e0c38c7061c6 0x2043f061c63830e3

def z150 : W := mkw 0x0000224000112000 0x0000112000089000 0xe90067c000f3e001 0x748033e00079f000

def z151 : W := mkw 0x9211013ffc008262 0x4908809ffe004131 0x0400003ffc0007e6 0x8200001ffe0003f3

def z152 : W := mkw 0x00ee7ec0028a0000 0x00773f6001450000 0xfbffffc0038f8001 0x7dffffe001c7c000

def z153 : W := mkw 0x9011013fc4009fe3 0xc808809fe2004ff1 0x0400003fcc001fe6 0x8200001fe6000ff3

def z154 : W := mkw 0x03f77ffffc1f6000 0x01fbbffffe0fb000 0xfbfffffffc0fe000 0xfdfffffffe07f000

def z155 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xfd007fffffffffff 0xfe803fffffffffff

def z156 : W := mkw 0x01000000001f6000 0x00800000000fb000 0x01000000000fe000 0x008000000007f000

def z157 : W := mkw 0xc2fc776de68a9630 0x617e3bb6f3454b18 0xbf787f3df38f9e39 0xdfbc3f9ef9c7cf1c

def z158 : W := mkw 0x11eefec087ff6042 0x08f77f6043ffb021 0xfbffffc38fffe1c7 0x7dffffe1c7fff0e3

def z159 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000f800007c0 0x82000007c00003e0

def z160 : W := mkw 0x01fdf67b03fb3d81 0x80fefb3d81fd9ec0 0x7effe73f83f39fc1 0xbf7ff39fc1f9cfe0

def z161 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xe90067c04cf3e027 0x748033e02679f013

def z162 : W := mkw 0x90002344c411a262 0x480011a26208d131 0x850007c04cf3e7e7 0x428003e02679f3f3

def z163 : W := mkw 0xc1eeffc463ffe230 0x60f77fe231fff118 0xfbffffc073ffe039 0x7dffffe039fff01c

def z164 : W := mkw 0x200100121800090d 0x100080090c000486 0x9d0018327f0c193f 0xce800c193f860c9f

def z165 : W := mkw 0x02ffdcbb3be01d81 0x817fee5d9df00ec0 0x7efff83fb3f01fc1 0xbf7ffc1fd9f80fe0

def z166 : W := mkw 0x805dc13f43e09fa1 0xc02ee09fa1f04fd0 0xffffe73fc3f39fe1 0xfffff39fe1f9cff0

def z167 : W := mkw 0xc010012c60009630 0x6008009630004b18 0x0400003c70001e38 0x8200001e38000f1c

def z168 : W := mkw 0x002a9c8003ce4000 0x00154e4001e72000 0xfbff9fc003cfe001 0x7dffcfe001e7f000

def z169 : W := mkw 0x2057c8bb1944490d 0x102be45d8ca22486 0xfffff8ffff4c793f 0xfffffc7fffa63c9f

def z170 : W := mkw 0x0011003b00001d81 0x8008801d80000ec0 0x0400003f80001fc0 0x8200001fc0000fe0

def z171 : W := mkw 0x0003089218000000 0x000184490c000000 0xd88798f27c000000 0xec43cc793e000000

def z172 : W := mkw 0x21eefec01bff600c 0x10f77f600dffb006 0xfbffffc07fffe03f 0x7dffffe03ffff01f

def z173 : W := mkw 0x0075553f60000000 0x003aaa9fb0000000 0xfaffff3ff0000000 0xfd7fff9ff8000000

def z174 : W := mkw 0xc07dd53f63ea9fb1 0xe03eea9fb1f54fd8 0xffffff3ff3ff9ff9 0xffffff9ff9ffcffc

def z175 : W := mkw 0x0003089218000000 0x000184490c000000 0x1087983030000000 0x0843cc1818000000

def z176 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0x62ffe7c000f3e000 0x317ff3e00079f000

def z177 : W := mkw 0x0000000000000000 0x0000000000000000 0x6800600000f00001 0x3400300000780000

def z178 : W := mkw 0xc039953e63ca9f31 0x601cca9f31e54f98 0xffff9f3e73cf9f39 0xffffcf9f39e7cf9c

def z179 : W := mkw 0x40201400200a0010 0x20100a0010050008 0x00001800300c0018 0x00000c001806000c

def z180 : W := mkw 0x0030142820000000 0x00180a1410000000 0x1278183030000000 0x093c0c1818000000

def z181 : W := mkw 0x40381428228a1410 0x201c0a1411450a08 0x12781830330c1818 0x093c0c1819860c0c

def z182 : W := mkw 0xc010012c60009630 0x6008009630004b18 0x0000000c00000600 0x0000000600000300

def z183 : W := mkw 0x00e67fc4c4000000 0x00733fe262000000 0xfaffffcfcc000000 0xfd7fffe7e6000000

def z184 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xe90067cfcc03e026 0xf48033e7e601f013

def z185 : W := mkw 0x02a23fc4fc000000 0x01511fe27e000000 0x80001fc07c000000 0x40000fe03e000000

def z186 : W := mkw 0x8000010440008220 0x4000008220004110 0x2000070c00838600 0x100003860041c300

def z187 : W := mkw 0x02f75dbffc000000 0x017baedffe000000 0x12ff983ffc000000 0x897fcc1ffe000000

def z188 : W := mkw 0x205fc8bb1be45d8d 0x902fe45d8df22ec6 0xfffff8fffffc7fff 0xfffffc7ffffe3fff

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0xcd0000c24c406127 0xe680006126203093

def z190 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0x32ffff0003bf8000 0x197fff8001dfc000

def z191 : W := mkw 0x02a03744e4000000 0x01501ba272000000 0x0000070000000000 0x0000038000000000

def z192 : W := mkw 0x9108800003ffe262 0x4884400001fff131 0x0500000003ffe7e7 0x0280000001fff3f3

def z193 : W := mkw 0x0044400000000000 0x0022200000000000 0x7affe00000000000 0x3d7ff00000000000

def z194 : W := mkw 0xc2f77ffffc0a8230 0x617bbffffe054118 0xfbfffffffc0f8038 0xfdfffffffe07c01c

def z195 : W := mkw 0x01eeffc4c7ff6000 0x00f77fe263ffb000 0xfbffffcfcfffe001 0xfdffffe7e7fff000

def z196 : W := mkw 0x02e77ed39c000000 0x0173bf69ce000000 0xfaffffc38c000000 0x7d7fffe1c6000000

def z197 : W := mkw 0x004dc01303e01d81 0x8026e00981f00ec0 0x4487e00383f01fc1 0x2243f001c1f80fe0

def z198 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfffffffffc406127 0xfffffffffe203093

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0x6800600f80000000 0xb4003007c0000000

def z200 : W := mkw 0x03ffdcbb3bee4000 0x01ffee5d9df72000 0x12ff9830330c0000 0x097fcc1819860000

def z201 : W := mkw 0x0011003b00000000 0x0008801d80000000 0x0000003f80000000 0x8000001fc0000000

def z202 : W := mkw 0xd2ff7ffffe9bb672 0x697fbfffff4ddb39 0xffffffffffffffff 0xffffffffffffffff

def z203 : W := mkw 0xe008800003cedf3d 0x7004400001e76f9e 0x0500000003cfff3f 0x0280000001e7ff9f

def z204 : W := mkw 0xe03b9dbe7bcedf3d 0x701dcedf3de76f9e 0xbfff9f3c738f9e39 0xdfffcf9e39c7cf1c

def z205 : W := mkw 0x0108000002bb2000 0x00840000015d9000 0x0000000000b38000 0x000000000059c000

def z206 : W := mkw 0x90002344c411a262 0x480011a26208d131 0x2500670d80f3e7e7 0x12803386c079f3f3

def z207 : W := mkw 0x01effed203ff6901 0x00f7ff6901ffb480 0xfffffff203fff901 0xfffffff901fffc80

def z208 : W := mkw 0x0002888001444000 0x0001444000a22000 0x408780c000406000 0x2043c06000203000

def z209 : W := mkw 0x03effed39fff6000 0x01f7ff69cfffb000 0xfbffffc38fffe001 0x7dffffe1c7fff000

def z210 : W := mkw 0x90002344c4008262 0x480011a262004131 0xec0067cfcc0007e6 0xf60033e7e60003f3

def z211 : W := mkw 0x0000224000112000 0x0000112000089000 0xed0067c24cf3e127 0xf68033e12679f093

def z212 : W := mkw 0x90002344c411a262 0x480011a26208d131 0x2000670d80b386c0 0x10003386c059c360

def z213 : W := mkw 0x00c66ac000000000 0x0063356000000000 0x4087e0c000000000 0x2043f06000000000

def z214 : W := mkw 0x02f77efb38000000 0x017bbf7d9c000000 0xfafffff030000000 0x7d7ffff818000000

def z215 : W := mkw 0x201b88ba1bc45d0d 0x100dc45d0de22e86 0xffff98fe7fcc7f3f 0xffffcc7f3fe63f9f

def z216 : W := mkw 0x22f7fffffd44490d 0x117bfffffea22486 0xfafffffffc406106 0xfd7ffffffe203083

def z217 : W := mkw 0x02f4776de4000000 0x017a3bb6f2000000 0xba787f3df0000000 0xdd3c3f9ef8000000

def z218 : W := mkw 0x01a2bec0015f6000 0x00d15f6000afb000 0xd9879fc0034fe001 0x6cc3cfe001a7f000

def z219 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xbb781f0c038f8601 0x5dbc0f8601c7c300

def z220 : W := mkw 0x00e67ec000112000 0x00733f6000089000 0xfbffffc000f3e001 0x7dffffe00079f000

def z221 : W := mkw 0x9211237ffc11a262 0x490891bffe08d131 0xed0067fffcf3e7e7 0xf68033fffe79f3f3

def z222 : W := mkw 0x01c6c88001644000 0x00e3644000b22000 0x0087800000000000 0x0043c00000000000

def z223 : W := mkw 0x02c76ad39c000000 0x0163b569ce000000 0x4087e0c38c000000 0x2043f061c6000000

def z224 : W := mkw 0xc0080000028a9630 0x6004000001454b18 0x05000000038f9e39 0x0280000001c7cf1c

def z225 : W := mkw 0x01ec540002aa0000 0x00f62a0001550000 0x0278000000000000 0x013c000000000000

def z226 : W := mkw 0xe00b88921bcedf3d 0x7005c4490de76f9e 0xdd8798f27fcfff3f 0xeec3cc793fe7ff9f

def z227 : W := mkw 0x22f7fffffd44490d 0x117bfffffea22486 0xfaffffffff0c1818 0xfd7fffffff860c0c

def z228 : W := mkw 0x02f5777fe4000000 0x017abbbff2000000 0x7affe73f80000000 0xbd7ff39fc0000000

def z229 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xd98798c20f4c6107 0x6cc3cc6107a63083

def z230 : W := mkw 0xc07cd52c63ea9630 0x603e6a9631f54b18 0xffffff3c73ff9e39 0xffffff9e39ffcf1c

def z231 : W := mkw 0xc000010460008230 0x6000008230004118 0x0000000070000038 0x000000003800001c

def z232 : W := mkw 0x01e67ec0001f6000 0x00f33f60000fb000 0xfbffffc0000fe000 0x7dffffe00007f000

def z233 : W := mkw 0x22a3bfd6fd44490d 0x1151dfeb7ea22486 0xdd879ff27f4c793f 0xeec3cff93fa63c9f

def z234 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x12ff803000000000 0x097fc01800000000

def z235 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xc18798c27c4c613e 0x60c3cc613e26309f

def z236 : W := mkw 0x00281400028a0000 0x00140a0001450000 0x2278070000838000 0x113c03800041c000

def z237 : W := mkw 0x0000000000000000 0x0000000000000000 0x40006003807001c0 0x20003001c03800e0

def z238 : W := mkw 0xd038152ce68a9672 0x681c0a9673454b39 0xbf781f3fff8f9fff 0xdfbc0f9fffc7cfff

def z239 : W := mkw 0xc0201504600a8230 0x60100a8230054118 0x81001f00700f8038 0x40800f803807c01c

def z240 : W := mkw 0x00e65c8000000000 0x00732e4000000000 0x12ff980000000000 0x097fcc0000000000

def z241 : W := mkw 0x02f77ffffc112000 0x017bbffffe089000 0xfbfffffffcf3e001 0xfdfffffffe79f000

def z242 : W := mkw 0x0003089218000000 0x000184490c000000 0xdd8798f27c406127 0xeec3cc793e203093

def z243 : W := mkw 0x200208801804400c 0x100104400c022006 0x00001800300c0018 0x00000c001806000c

def z244 : W := mkw 0xe2ffffffffcedf3d 0x717fffffffe76f9e 0xffffffffffcfff3f 0xffffffffffe7ff9f

def z245 : W := mkw 0x900000000011a262 0x480000000008d131 0xcd0000c24cf3e7e7 0xe68000612679f3f3

def z246 : W := mkw 0x0038152c628a0000 0x001c0a9631450000 0xbb781f3c738f8001 0xddbc0f9e39c7c000

def z247 : W := mkw 0x21c7ead21975690d 0x10e3f5690cbab486 0x4087e0c20c706106 0x2043f06106383083

def z248 : W := mkw 0x00002344c4000000 0x000011a262000000 0xed0067cfcc406127 0xf68033e7e6203093

def z249 : W := mkw 0x9008a344c7f1bfe3 0xc80451a263f8dff1 0xed0067cfcff3ffe7 0xf68033e7e7f9fff3

def z250 : W := mkw 0x0000224084000000 0x0000112042000000 0x400060c38c000000 0x20003061c6000000

def z251 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c00000c00800601 0x9600000600400300

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0x040000024c000126 0x8200000126000093

def z253 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfffffff073fff839 0xfffffff839fffc1c

def z254 : W := mkw 0xc1a23fc4601fe230 0x60d11fe2300ff118 0x81001fc0700fe038 0x40800fe03807f01c

def z255 : W := mkw 0x0054402900000000 0x002a201480000000 0x2278600d80000000 0x113c3006c0000000

def z256 : W := mkw 0x02f67fede4000000 0x017b3ff6f2000000 0xfaffffcd80000000 0x7d7fffe6c0000000

def z257 : W := mkw 0x0002088000044000 0x0001044000022000 0x810018c0000c6000 0x40800c6000063000

def z258 : W := mkw 0xc1fc776c62bbb630 0x60fe3bb6315ddb18 0x2278670c00b38600 0x113c33860059c300

def z259 : W := mkw 0x0055c03b01400901 0x002ae01d80a00480 0x7effe03f83401901 0xbf7ff01fc1a00c80

def z260 : W := mkw 0x004cc00003e00000 0x0026600001f00000 0x7effe00f83f007c1 0xbf7ff007c1f803e0

def z261 : W := mkw 0x01eefec003ee4000 0x00f77f6001f72000 0xfaffffc0030c0000 0x7d7fffe001860000

def z262 : W := mkw 0xd010012ce4009672 0x6808009672004b39 0x0400003ffc001ffe 0x8200001ffe000fff

def z263 : W := mkw 0x0003889201444901 0x0001c44900a22480 0xdd8798f2034c7901 0xeec3cc7901a63c80

def z264 : W := mkw 0x0045401300000000 0x0022a00980000000 0x4087e00380000000 0x2043f001c0000000

def z265 : W := mkw 0x0000224000112000 0x0000112000089000 0xed0067cf80f3e7c1 0xf68033e7c079f3e0

def z266 : W := mkw 0x8000010440008220 0x4000008220004110 0x0400000c40000620 0x8200000620000310

def z267 : W := mkw 0xe011013e78009f3d 0x7008809f3c004f9e 0x0400003e7c001f3e 0x8200001f3e000f9f

def z268 : W := mkw 0x2047c8931964498d 0x9023e4498cb224c6 0x4087e0c38c7061c6 0x2043f061c63830e3

def z269 : W := mkw 0xc008800003ea9fb1 0xe004400001f54fd8 0x0500000003ff9ff9 0x0280000001ffcffc

def z270 : W := mkw 0xc0281504628a8230 0x60140a8231454118 0xbb781f00738f8039 0x5dbc0f8039c7c01c

def z271 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0x93ff9fc0030fe000 0x49ffcfe00187f000

def z272 : W := mkw 0x200000001800000c 0x100000000c000006 0x000000007c00003e 0x000000003e00001f

def z273 : W := mkw 0x0003889219444000 0x0001c4490ca22000 0xd98798f27f4c6001 0xecc3cc793fa63000

def z274 : W := mkw 0x0002aac001556000 0x0001556000aab000 0xf987ffc003ffe001 0x7cc3ffe001fff000

def z275 : W := mkw 0x900000000011a262 0x480000000008d131 0x6d00600f80f3e7e7 0xb6803007c079f3f3

def z276 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xad0007cc4c83e627 0xd68003e62641f313

def z277 : W := mkw 0xc1feddac63eed630 0x60ff6ed631f76b18 0xbfff9f3c738f9e39 0xdfffcf9e39c7cf1c

def z278 : W := mkw 0x0008000002800000 0x0004000001400000 0x3a78000003800001 0x1d3c000001c00000

def z279 : W := mkw 0xc038952c63ea9fb1 0xe01c4a9631f54fd8 0xbf781f3c73ff9ff9 0xdfbc0f9e39ffcffc

def z280 : W := mkw 0x0108800003ff7d81 0x8084400001ffbec0 0x0500000003ffffc1 0x0280000001ffffe0

def z281 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000000f007c1 0x02000000007803e0

def z282 : W := mkw 0x4010002820001410 0x2008001410000a08 0x0000003030001818 0x0000001818000c0c

def z283 : W := mkw 0x80002344c4008220 0x400011a262004110 0xed0067cfcc838621 0xf68033e7e641c310

def z284 : W := mkw 0xc2ff7ffffe8a9630 0x617fbfffff454b18 0xfafffffffc838600 0xfd7ffffffe41c300

def z285 : W := mkw 0x0000224000112000 0x0000112000089000 0x810007c00003e000 0x408003e00001f000

def z286 : W := mkw 0x205fc8bb1be45d8d 0x902fe45d8df22ec6 0x12ff9830330c1818 0x097fcc1819860c0c

def z287 : W := mkw 0xd07df77fe7fbbff3 0xe83efbbff3fddff9 0xffffffffffffffff 0xffffffffffffffff

def z288 : W := mkw 0x91eeffc4c7ffe262 0x48f77fe263fff131 0xfbffffc04fffe027 0x7dffffe027fff013

def z289 : W := mkw 0x40080000028a1410 0x2004000001450a08 0x00000000030c1818 0x0000000001860c0c

def z290 : W := mkw 0x9055637fc411a262 0x482ab1bfe208d131 0xffffe7ffccf3e7e7 0xfffff3ffe679f3f3

def z291 : W := mkw 0xe1fffffe7bffff3d 0x70ffffff3dffff9e 0xfffffffe7fffff3f 0xffffffff3fffff9f

def z292 : W := mkw 0x005fc8bb1be01d81 0x802fe45d8df00ec0 0xfefff8fffff01fc1 0xff7ffc7ffff80fe0

def z293 : W := mkw 0x22ffffffffe45d8d 0x917ffffffff22ec6 0xfffffffffffc7fff 0xfffffffffffe3fff

def z294 : W := mkw 0x9018236cc691b662 0x480c11b66348db31 0xff7867ffcff3ffe7 0xffbc33ffe7f9fff3

def z295 : W := mkw 0x2008800003e45d8d 0x9004400001f22ec6 0x0500000003fc7fff 0x0280000001fe3fff

def z296 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xd88798f27c406106 0xec43cc793e203083

def z297 : W := mkw 0x0000000000000000 0x0000000000000000 0x8d00000040000021 0xc680000020000010

def z298 : W := mkw 0x90002344c411a262 0x480011a26208d131 0x600067cf8cf3e7c6 0x300033e7c679f3e3

def z299 : W := mkw 0x005dc03b03e00000 0x002ee01d81f00000 0x7affe03f83f00001 0xbd7ff01fc1f80000

def z300 : W := mkw 0x40381428228a1410 0x201c0a1411450a08 0xbb781f30338f9819 0x5dbc0f9819c7cc0c

def z301 : W := mkw 0x93ffffffffffe262 0x49fffffffffff131 0xffffffffffffe7e7 0xfffffffffffff3f3

def z302 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x148798327f0c193e 0x8a43cc193f860c9f

def z303 : W := mkw 0xc03b1dbe7a8a9630 0x601d8edf3d454b18 0xffff9ffe7f8f9e39 0xffffcfff3fc7cf1c

def z304 : W := mkw 0x01eefec003ff7d81 0x80f77f6001ffbec0 0xffffffc003ffffc1 0x7fffffe001ffffe0

def z305 : W := mkw 0x0211003b38000000 0x0108801d9c000000 0x0000003030000000 0x0000001818000000

def z306 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfafffffffcb386c0 0xfd7ffffffe59c360

def z307 : W := mkw 0x0000800001400901 0x0000400000a00480 0x0400000003401901 0x0200000001a00c80

def z308 : W := mkw 0x40381428228a1410 0x201c0a1411450a08 0x3e78183c338c1e19 0x9f3c0c1e19c60f0c

def z309 : W := mkw 0x0231153ffc000000 0x01188a9ffe000000 0xba781f3ffc000000 0xdd3c0f9ffe000000

def z310 : W := mkw 0x0002888001444000 0x0001444000a22000 0x10879800030c0000 0x0843cc0001860000

def z311 : W := mkw 0x21effed21bff690d 0x10f7ff690dffb486 0xfbfffff033fff819 0x7dfffff819fffc0c

def z312 : W := mkw 0x0044c00001600000 0x0022600000b00000 0x4087e00000700000 0x2043f00000380000

def z313 : W := mkw 0x90002344c411a262 0x480011a26208d131 0x850007cfcc03e7e6 0xc28003e7e601f3f3

def z314 : W := mkw 0x005cc02903e01d81 0x802e601481f00ec0 0x2678600d83f01fc1 0x133c3006c1f80fe0

def z315 : W := mkw 0x01effed303ff6981 0x80f7ff6981ffb4c0 0xfbffffc383ffe1c1 0x7dffffe1c1fff0e0

def z316 : W := mkw 0xb0038996dd44cb6f 0x5801c4cb6ea265b7 0xdd8798ffff4c7fff 0xeec3cc7fffa63fff

def z317 : W := mkw 0x0030152c60000000 0x00180a9630000000 0xbf781f3c730c1839 0xdfbc0f9e39860c1c

def z318 : W := mkw 0x02f4776de4000000 0x017a3bb6f2000000 0xea7867cfcc000000 0xf53c33e7e6000000

def z319 : W := mkw 0x92fffffffff1bfe3 0xc97ffffffff8dff1 0xfffffffffff3ffe7 0xfffffffffff9fff3

def z320 : W := mkw 0x02f67fedfc000000 0x017b3ff6fe000000 0xa2787fcdfc000000 0x513c3fe6fe000000

def z321 : W := mkw 0x02822ac09c000000 0x014115604e000000 0x000000c00c000000 0x0000006006000000

def z322 : W := mkw 0x1000224084112042 0x0800112042089021 0xe90067c38cf3e1c7 0x748033e1c679f0e3

def z323 : W := mkw 0x200080000144490d 0x1000400000a22486 0xcd0000c24f4c793f 0xe680006127a63c9f

def z324 : W := mkw 0x0001001300000981 0x80008009800004c0 0x00000003800001c0 0x00000001c00000e0

def z325 : W := mkw 0xc0201504600a8230 0x60100a8230054118 0x9d001f30730f9839 0xce800f983987cc1c

def z326 : W := mkw 0x1000224084112042 0x0800112042089021 0x6c0060cf8cf067c7 0xb6003067c67833e3

def z327 : W := mkw 0x00fffefb03e01d81 0x807fff7d81f00ec0 0xfeffffff83f01fc1 0xff7fffffc1f80fe0

def z328 : W := mkw 0x0108a24003ff6000 0x0084512001ffb000 0xe90067c003ffe001 0x748033e001fff000

def z329 : W := mkw 0xd038376ce69bb672 0x681c1bb6734ddb39 0x2278670d80b386c0 0x113c3386c059c360

def z330 : W := mkw 0x1000224084112042 0x0800112042089021 0x000000c00c006006 0x0000006006003003

def z331 : W := mkw 0x01ffdcbb03ee5d81 0x80ffee5d81f72ec0 0x12ff9830030c1800 0x097fcc1801860c00

def z332 : W := mkw 0x0002888001444000 0x0001444000a22000 0xd98798c0034c6001 0x6cc3cc6001a63000

def z333 : W := mkw 0xc1fc776c62bbb630 0x60fe3bb6315ddb18 0xbf787f3c73bf9e39 0xdfbc3f9e39dfcf1c

def z334 : W := mkw 0x00283640029b2000 0x00141b20014d9000 0xfb787fc003ffe001 0x7dbc3fe001fff000

def z335 : W := mkw 0x004ec88003e44000 0x0027644001f22000 0xfbfff8c003fc6001 0x7dfffc6001fe3000

def z336 : W := mkw 0xc0281504628a9630 0x60140a8231454b18 0x85001f00738f9e39 0x42800f8039c7cf1c

def z337 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400003070001838 0x8200001838000c1c

def z338 : W := mkw 0xc05dc13f63e09fb1 0xe02ee09fb1f04fd8 0x7effe03ff3f01ff9 0xbf7ff01ff9f80ffc

def z339 : W := mkw 0xd038376ce69bb672 0x681c1bb6734ddb39 0xbf781ffc7f8ffe3f 0xdfbc0ffe3fc7ff1f

def z340 : W := mkw 0x005de27b03f13d81 0x802ef13d81f89ec0 0xffffe7ff83f3ffc1 0xfffff3ffc1f9ffe0

def z341 : W := mkw 0x91ec7744c6bba262 0x48f63ba2635dd131 0x2278670d80b386c0 0x113c3386c059c360

def z342 : W := mkw 0x01eedc8003ee4000 0x00f76e4001f72000 0x7afff80003fc0001 0x3d7ffc0001fe0000

def z343 : W := mkw 0x02f4542920000000 0x017a2a1490000000 0x0278000000000000 0x013c000000000000

def z344 : W := mkw 0x2011003b18001d8d 0x9008801d8c000ec6 0x0400003ffc001ffe 0x8200001ffe000fff

def z345 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x2678073c70839e38 0x933c039e3841cf1c

def z346 : W := mkw 0x1000000000112042 0x0800000000089021 0x00000000007061c6 0x00000000003830e3

def z347 : W := mkw 0x200100121800090d 0x100080090c000486 0x0000003030001818 0x0000001818000c0c

def z348 : W := mkw 0x8000010440008220 0x4000008220004110 0xbd001f3c738f9e39 0xde800f9e39c7cf1c

def z349 : W := mkw 0x0000800001600981 0x8000400000b004c0 0x00000000007001c0 0x00000000003800e0

def z350 : W := mkw 0x8000010440008220 0x4000008220004110 0xed00670fc0f387e1 0xf6803387e079c3f0

def z351 : W := mkw 0x9002abc4c555e262 0x480155e262aaf131 0xfd87ffcfcfffe7e7 0xfec3ffe7e7fff3f3

def z352 : W := mkw 0x00281400028a0000 0x00140a0001450000 0x12781800030c0000 0x093c0c0001860000

def z353 : W := mkw 0x014cc00003ff6000 0x00a6600001ffb000 0x7bffe00003ffe001 0x3dfff00001fff000

def z354 : W := mkw 0x21eefec003ff690d 0x10f77f6001ffb486 0xffffffc003fff93f 0x7fffffe001fffc9f

def z355 : W := mkw 0x205fc8bb1be45d8d 0x902fe45d8df22ec6 0x7effe0ff8ff07fc7 0xbf7ff07fc7f83fe3

def z356 : W := mkw 0xd038376ce69bb672 0x681c1bb6734ddb39 0xef7867cfccf3e7e7 0xf7bc33e7e679f3f3

def z357 : W := mkw 0x9008800003f1bfe3 0xc804400001f8dff1 0x0500000003f3ffe7 0x0280000001f9fff3

def z358 : W := mkw 0x0045c01301600981 0x8022e00980b004c0 0x6c87e00f80f007c1 0xb643f007c07803e0

def z359 : W := mkw 0x005748bb18000000 0x002ba45d8c000000 0xfafff8fffc000000 0xfd7ffc7ffe000000

def z360 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xcd0007c24c43e127 0xe68003e12621f093

def z361 : W := mkw 0x9000000000008262 0x4800000000004131 0x04000000000007e6 0x02000000000003f3

def z362 : W := mkw 0xc010012c60009630 0x6008009630004b18 0x9d00183c730c1e39 0xce800c1e39860f1c

def z363 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x32781f3c338f9e18 0x193c0f9e19c7cf0c

def z364 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0xdaff98f27c000000 0xed7fcc793e000000

def z365 : W := mkw 0x00381428028a1400 0x001c0a1401450a00 0xbf781f3c038f9e01 0xdfbc0f9e01c7cf00

def z366 : W := mkw 0x01ee7ec002bf6000 0x00f73f60015fb000 0xa3787fc000bfe000 0x51bc3fe0005ff000

def z367 : W := mkw 0x004cc00003e00000 0x0026600001f00000 0x12ff800003000000 0x097fc00001800000

def z368 : W := mkw 0x02f77efbbc000000 0x017bbf7dde000000 0x52fff8f3bc000000 0x297ffc79de000000

def z369 : W := mkw 0x005d403b02a01480 0x802ea01d81500a40 0x7affe03f80b006c0 0xbd7ff01fc0580360

def z370 : W := mkw 0x0020150460000000 0x00100a8230000000 0x80001f0070000000 0x40000f8038000000

def z371 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x93781f30730f9838 0x49bc0f983987cc1c

def z372 : W := mkw 0x9045e357c571abe3 0xc822f1abe2b8d5f1 0xed87e7cfccf3e7e7 0xf6c3f3e7e679f3f3

def z373 : W := mkw 0x905dc03b03f1bfe3 0xc82ee01d81f8dff1 0x7fffe03f83f3ffe7 0xbffff01fc1f9fff3

def z374 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0x62ffe7cf8c000000 0x317ff3e7c6000000

def z375 : W := mkw 0x004dc01303e00981 0x8026e00981f004c0 0x7affe00383f001c1 0x3d7ff001c1f800e0

def z376 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0xffffe0ffcff07fe7 0xfffff07fe7f83ff3

def z377 : W := mkw 0x0000000000001d81 0x8000000000000ec0 0x0400000000001fc0 0x0200000000000fe0

def z378 : W := mkw 0x200000000000090d 0x1000000000000486 0x040000000000193e 0x0200000000000c9f

def z379 : W := mkw 0x200080000144490d 0x1000400000a22486 0x9d001830734c793f 0xce800c1839a63c9f

def z380 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0x92ff9ff07c000000 0x497fcff83e000000

def z381 : W := mkw 0x0030152c60000000 0x00180a9630000000 0x2278070c00000000 0x113c038600000000

def z382 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000600d80b006c0 0x10003006c0580360

def z383 : W := mkw 0xc07dd53f63ea9fb1 0xe03eea9fb1f54fd8 0x7effe73f83f39fc1 0xbf7ff39fc1f9cfe0

def z384 : W := mkw 0xc011013f60009fb1 0xe008809fb0004fd8 0x0400003ff0001ff8 0x8200001ff8000ffc

def z385 : W := mkw 0x90000104c4008262 0x4800008262004131 0x6c00600fccf007e7 0xb6003007e67803f3

def z386 : W := mkw 0x0001801201400901 0x0000c00900a00480 0x7c87e03f83f01fc1 0xbe43f01fc1f80fe0

def z387 : W := mkw 0x4038152c628a1410 0x201c0a9631450a08 0xba781f3c730c1818 0xdd3c0f9e39860c0c

def z388 : W := mkw 0x02a23fc4fc000000 0x01511fe27e000000 0xe8007fcffc000000 0xf4003fe7fe000000

def z389 : W := mkw 0x0000000000000000 0x0000000000000000 0x81001800700c0038 0x40800c003806001c

def z390 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xff781ffe7fcfff3f 0xffbc0fff3fe7ff9f

def z391 : W := mkw 0xe038952c63cedf3d 0x701c4a9631e76f9e 0xbf781f3c73cfff3f 0xdfbc0f9e39e7ff9f

def z392 : W := mkw 0xc07d553f628a9630 0x603eaa9fb1454b18 0xffffff3ff38f9e39 0xffffff9ff9c7cf1c

def z393 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x9d879830730c1839 0xcec3cc1839860c1c

def z394 : W := mkw 0x0001801201400901 0x0000c00900a00480 0xdd879832734c1939 0xeec3cc1939a60c9c

def z395 : W := mkw 0xc2a23fc4fc0a8230 0x61511fe27e054118 0x81001fc07c0f8038 0x40800fe03e07c01c

def z396 : W := mkw 0x00080000028a0000 0x0004000001450000 0x01000000038f8001 0x0080000001c7c000

def z397 : W := mkw 0x0001801201400901 0x0000c00900a00480 0x1087803003001800 0x0843c01801800c00

def z398 : W := mkw 0x02fc776de6a01480 0x817e3bb6f3500a40 0x2278670d80b006c0 0x113c3386c0580360

def z399 : W := mkw 0x200180121944490d 0x1000c0090ca22486 0x050000327f4c793f 0x828000193fa63c9f

def z400 : W := mkw 0xc07c552d62aa96b0 0xe03e2a96b1554b58 0x2278670d80b386c0 0x113c3386c059c360

def z401 : W := mkw 0x2047c8931964498d 0x9023e4498cb224c6 0xdd87f8f3ff7c79ff 0xeec3fc79ffbe3cff

def z402 : W := mkw 0x0008000002a01480 0x8004000001500a40 0x0000000000b006c0 0x0000000000580360

def z403 : W := mkw 0x01c4624000312000 0x00e2312000189000 0x0000600000300000 0x0000300000180000

def z404 : W := mkw 0x90283744c69ba262 0x48141ba2634dd131 0xff787fcfcfffe7e7 0xffbc3fe7e7fff3f3

def z405 : W := mkw 0xc0fe7fec628a9630 0x607f3ff631454b18 0xfffffffc738f9e39 0xfffffffe39c7cf1c

def z406 : W := mkw 0xc05dc03b03ea9fb1 0xe02ee01d81f54fd8 0x7fffe03f83ff9ff9 0xbffff01fc1ffcffc

def z407 : W := mkw 0x0010012c60000000 0x0008009630000000 0x0000003c70000000 0x8000001e38000000

def z408 : W := mkw 0x02f5777ffc000000 0x017abbbffe000000 0x2278673ffc000000 0x913c339ffe000000

def z409 : W := mkw 0x01ffdcbb03ee5d81 0x80ffee5d81f72ec0 0x7efff83f83fc1fc1 0xbf7ffc1fc1fe0fe0

def z410 : W := mkw 0x02ff7ffffe8a0000 0x017fbfffff450000 0xfbffffffff8f8001 0xfdffffffffc7c000

def z411 : W := mkw 0xd010236ce411b672 0x680811b67208db39 0xed0067fffcf3ffff 0xf68033fffe79ffff

def z412 : W := mkw 0x021309bffc000000 0x010984dffe000000 0xd88798fffc000000 0xec43cc7ffe000000

def z413 : W := mkw 0xc000000000009630 0x6000000000004b18 0x0400000000001e38 0x0200000000000f1c

def z414 : W := mkw 0x210b88921bff690d 0x1085c4490dffb486 0xdd8798f27ffff93f 0xeec3cc793ffffc9f

def z415 : W := mkw 0x9030376ce411a262 0x48181bb67208d131 0xff787ffffcf3e7e7 0xffbc3ffffe79f3f3

def z416 : W := mkw 0xc2f77ffffc009630 0x617bbffffe004b18 0xfefffffffc001e38 0xff7ffffffe000f1c

def z417 : W := mkw 0x01822ac000156000 0x00c11560000ab000 0x000000c000006000 0x0000006000003000

def z418 : W := mkw 0x92f4776de411a262 0x497a3bb6f208d131 0x2278670d80b386c0 0x113c3386c059c360

def z419 : W := mkw 0x0055403b00001d81 0x802aa01d80000ec0 0x7effe03f80001fc0 0xbf7ff01fc0000fe0

def z420 : W := mkw 0x21c7ead21975690d 0x10e3f5690cbab486 0xdd87f8f27f7c793f 0xeec3fc793fbe3c9f

def z421 : W := mkw 0x22f7dcbb3944490d 0x117bee5d9ca22486 0x12ff9830330c1818 0x097fcc1819860c0c

def z422 : W := mkw 0xc039153f628a9fb1 0xe01c8a9fb1454fd8 0xbf781f3ff38f9ff9 0xdfbc0f9ff9c7cffc

def z423 : W := mkw 0xf03bbffeffdfff7f 0x781ddfff7fefffbf 0xffffffffffffffff 0xffffffffffffffff

def z424 : W := mkw 0xc3fffffffffff630 0x61fffffffffffb18 0xfffffffffffffe39 0xffffffffffffff1c

def z425 : W := mkw 0x8000010440008220 0x4000008220004110 0xed0007ce4cc3e727 0xf68003e72661f393

def z426 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x3e78073c03839e01 0x9f3c039e01c1cf00

def z427 : W := mkw 0x2003aad21955690d 0x1001d5690caab486 0xfd87fff27ffff93f 0xfec3fff93ffffc9f

def z428 : W := mkw 0x900001044011a262 0x480000822008d131 0xad00070c40f3e7e7 0xd68003862079f3f3

def z429 : W := mkw 0x105de27b87f13dc3 0x882ef13dc3f89ee1 0x7effe0ff8ff07fc7 0xbf7ff07fc7f83fe3

def z430 : W := mkw 0xc0080104428a9630 0x6004008221454b18 0xad00070c438f9e39 0xd680038621c7cf1c

def z431 : W := mkw 0x0001001200000901 0x0000800900000480 0x0400003200001900 0x8200001900000c80

def z432 : W := mkw 0xc0281400028a9630 0x60140a0001454b18 0xbf781f00038f9e39 0x5fbc0f8001c7cf1c

def z433 : W := mkw 0x00e77ed218000000 0x0073bf690c000000 0xfafffff27c000000 0xfd7ffff93e000000

def z434 : W := mkw 0x90000104c4008262 0x4800008262004131 0x0000000d800006c0 0x00000006c0000360

def z435 : W := mkw 0x200288801944490d 0x100144400ca22486 0x850018c07f4c793f 0x42800c603fa63c9f

def z436 : W := mkw 0xc0080000028a9630 0x6004000001454b18 0x0000000000838600 0x000000000041c300

def z437 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0x32ffff3db0000000 0x197fff9ed8000000

def z438 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x5c879832334c1919 0xae43cc1919a60c8c

def z439 : W := mkw 0x205dc03b1be01d8d 0x902ee01d8df00ec6 0x7effe03ffff01fff 0xbf7ff01ffff80fff

def z440 : W := mkw 0x81eeffc443ffe220 0x40f77fe221fff110 0xffffffcc43ffe621 0xffffffe621fff310

def z441 : W := mkw 0x02e67fc4fc000000 0x01733fe27e000000 0xfaffffc07c000000 0x7d7fffe03e000000

def z442 : W := mkw 0x02e77fd7fc000000 0x0173bfebfe000000 0xc087ffc3fc000000 0x6043ffe1fe000000

def z443 : W := mkw 0x82f77ffffc008220 0x417bbffffe004110 0xfffffffffc838621 0xfffffffffe41c310

def z444 : W := mkw 0x0001001218000000 0x000080090c000000 0x000000327c000000 0x800000193e000000

def z445 : W := mkw 0x9108a344c7ffe262 0x488451a263fff131 0xed0067cfcfffe7e7 0xf68033e7e7fff3f3

def z446 : W := mkw 0x01eedc8003ee4000 0x00f76e4001f72000 0xdbff98c0034c6001 0x6dffcc6001a63000

def z447 : W := mkw 0x1000224084112042 0x0800112042089021 0xcd0060c3cc7061e7 0xe6803061e63830f3

def z448 : W := mkw 0x0010002800000000 0x0008001400000000 0x3a78003c00000000 0x9d3c001e00000000

def z449 : W := mkw 0xb05febffdff5ffef 0xd82ff5ffeffafff7 0xffffffffffffffff 0xffffffffffffffff

def z450 : W := mkw 0xc010012c60009630 0x6008009630004b18 0xad00073c70839e39 0xd680039e3841cf1c

def z451 : W := mkw 0x01ee7ec002bb2000 0x00f73f60015d9000 0xfaffffc000b38000 0x7d7fffe00059c000

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0x0500000000406127 0x0280000000203093

def z453 : W := mkw 0x41fefee823ff7410 0x20ff7f7411ffba08 0xfbfffff033fff819 0x7dfffff819fffc0c

def z454 : W := mkw 0x0001001200000000 0x0000800900000000 0x5887803200000000 0xac43c01900000000

def z455 : W := mkw 0x0045c01301600981 0x8022e00980b004c0 0x0087800000000000 0x0043c00000000000

def z456 : W := mkw 0xd038152c629bb672 0x681c0a96314ddb39 0xbf781f3c73ffffff 0xdfbc0f9e39ffffff

def z457 : W := mkw 0x201388bb19445d8d 0x9009c45d8ca22ec6 0xdd8798ffff4c7fff 0xeec3cc7fffa63fff

def z458 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xaf78070c40838621 0xd7bc03862041c310

def z459 : W := mkw 0x00e4764000000000 0x00723b2000000000 0x2278670000000000 0x113c338000000000

def z460 : W := mkw 0x0000224000000000 0x0000112000000000 0xe80067c000000000 0x740033e000000000

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0x05000000030c1839 0x0280000001860c1c

def z462 : W := mkw 0xc07c552d62aa96b0 0xe03e2a96b1554b58 0xbf787f3df3bf9ef9 0xdfbc3f9ef9dfcf7c

def z463 : W := mkw 0x200180121940090d 0x1000c0090ca00486 0x5c8780327f40193f 0xae43c0193fa00c9f

def z464 : W := mkw 0x00f77efb00000000 0x007bbf7d80000000 0xfaffffff80000000 0xfd7fffffc0000000

def z465 : W := mkw 0x8000000000008220 0x4000000000004110 0x0500000000838621 0x028000000041c310

def z466 : W := mkw 0x005de37fc7e01d81 0x802ef1bfe3f00ec0 0xfeffe7ffcff01fc1 0xff7ff3ffe7f80fe0

def z467 : W := mkw 0xd038376ce69bb672 0x681c1bb6734ddb39 0xbf787f3df3bf9ef9 0xdfbc3f9ef9dfcf7c

def z468 : W := mkw 0x0001801201400901 0x0000c00900a00480 0x4087800200400100 0x2043c00100200080

def z469 : W := mkw 0x007dd53f63e01d81 0x803eea9fb1f00ec0 0xfeffff3ff3f01fc1 0xff7fff9ff9f80fe0

def z470 : W := mkw 0x21a3bed2195f690d 0x10d1df690cafb486 0xdd879ff27f4ff93f 0xeec3cff93fa7fc9f

def z471 : W := mkw 0x200b88921be45d8d 0x9005c4490df22ec6 0xdd8798f27ffc7fff 0xeec3cc793ffe3fff

def z472 : W := mkw 0x00000104c4000000 0x0000008262000000 0x0000000fcc000000 0x80000007e6000000

def z473 : W := mkw 0x006cd40003ea0000 0x00366a0001f50000 0xfbffff0003ff8001 0x7dffff8001ffc000

def z474 : W := mkw 0x0210012de4000000 0x01080096f2000000 0x0000000d80000000 0x00000006c0000000

def z475 : W := mkw 0x02c7489318000000 0x0163a4498c000000 0x0087800000000000 0x0043c00000000000

def z476 : W := mkw 0xb003abd6dd55eb6f 0x5801d5eb6eaaf5b7 0xdd879ff27f4ff93f 0xeec3cff93fa7fc9f

def z477 : W := mkw 0x91eefec003ffe262 0x48f77f6001fff131 0xffffffc003ffe7e7 0x7fffffe001fff3f3

def z478 : W := mkw 0x0020140000000000 0x00100a0000000000 0xba781f0000000000 0x5d3c0f8000000000

def z479 : W := mkw 0x0010002900001480 0x8008001480000a40 0x0000000d800006c0 0x00000006c0000360

def z480 : W := mkw 0x2108800003ff690d 0x1084400001ffb486 0x0500000003fff93f 0x0280000001fffc9f

def z481 : W := mkw 0x900000000011a262 0x480000000008d131 0x010000000003e026 0x008000000001f013

def z482 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x7afff83fb0000000 0xbd7ffc1fd8000000

def z483 : W := mkw 0x0011803b01401d81 0x8008c01d80a00ec0 0x5c87803f83401fc1 0xae43c01fc1a00fe0

def z484 : W := mkw 0xb003abd6dd55eb6f 0x5801d5eb6eaaf5b7 0xed87e7cfccf3e7e7 0xf6c3f3e7e679f3f3

def z485 : W := mkw 0x904ce344c7f1a262 0x482671a263f8d131 0xffffe7cfcff3e7e7 0xfffff3e7e7f9f3f3

def z486 : W := mkw 0x42ff7ffffe8a1410 0x217fbfffff450a08 0xfaffffffff0c1818 0xfd7fffffff860c0c

def z487 : W := mkw 0x004c400002a00000 0x0026200001500000 0x2278600000b00000 0x113c300000580000

def z488 : W := mkw 0x020100139c000000 0x01008009ce000000 0x000000038c000000 0x00000001c6000000

def z489 : W := mkw 0x92c76bd7dc11a262 0x4963b5ebee08d131 0xed87e7cfccf3e7e7 0xf6c3f3e7e679f3f3

def z490 : W := mkw 0x005c402902a01480 0x802e201481500a40 0x6e78600f80f007c1 0xb73c3007c07803e0

def z491 : W := mkw 0x205fc8bb1be45d8d 0x902fe45d8df22ec6 0xdfff98f27f4c793f 0xefffcc793fa63c9f

def z492 : W := mkw 0x004dc01203e00901 0x0026e00901f00480 0x7effe03203f01901 0xbf7ff01901f80c80

def z493 : W := mkw 0x02000104fc000000 0x010000827e000000 0x000000007c000000 0x000000003e000000

def z494 : W := mkw 0x02ffffffffe01d81 0x817ffffffff00ec0 0xfaffffffff001800 0xfd7fffffff800c00

def z495 : W := mkw 0x90000104c4008262 0x4800008262004131 0x000000004c000026 0x0000000026000013

def z496 : W := mkw 0x40381428228a1410 0x201c0a1411450a08 0x0278000000000000 0x013c000000000000

def z497 : W := mkw 0x200000000004400c 0x1000000000022006 0x01000000000c603e 0x008000000006301f

def z498 : W := mkw 0x02a21c8038000000 0x01510e401c000000 0x0000180030000000 0x00000c0018000000

def z499 : W := mkw 0x92f77ffffc008262 0x497bbffffe004131 0xfefffffffc0007e6 0xff7ffffffe0003f3

def z500 : W := mkw 0xc018012c62809630 0x600c009631404b18 0x3e78003c73801e39 0x9f3c001e39c00f1c

def z501 : W := mkw 0x21fffefb1bff7d8d 0x90ffff7d8dffbec6 0xffffffffffffffff 0xffffffffffffffff

def z502 : W := mkw 0xe07fddbf7beedfbd 0xf03feedfbdf76fde 0xffffffffffffffff 0xffffffffffffffff

def z503 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x508798f23f4c791e 0x2843cc791fa63c8f

def z504 : W := mkw 0x90000104c411a262 0x480000826208d131 0x0500000fccf3e7e7 0x82800007e679f3f3

def z505 : W := mkw 0x015dc03b03ff7d81 0x80aee01d81ffbec0 0x7fffe03f83ffffc1 0xbffff01fc1ffffe0

def z506 : W := mkw 0x905de37fc7f1bfe3 0xc82ef1bfe3f8dff1 0x7effe73f83f39fc1 0xbf7ff39fc1f9cfe0

def z507 : W := mkw 0x005c402902a01480 0x802e201481500a40 0x3e78603d83b01ec1 0x9f3c301ec1d80f60

def z508 : W := mkw 0x603b9cba3bce5d1d 0x301dce5d1de72e8e 0x12ff9830330c1818 0x097fcc1819860c0c

def z509 : W := mkw 0x0010002800001400 0x0008001400000a00 0x0400003c00001e00 0x8200001e00000f00

def z510 : W := mkw 0x010a888003ff6000 0x0085444001ffb000 0xd98798c003ffe001 0x6cc3cc6001fff000

def z511 : W := mkw 0x01fffefb03ff6000 0x00ffff7d81ffb000 0xfbffffff83ffe001 0xfdffffffc1fff000

def z512 : W := mkw 0x2211013ffc00090d 0x1108809ffe000486 0x0400003ffc00193e 0x8200001ffe000c9f

def z513 : W := mkw 0x02c4624184000000 0x01623120c2000000 0x0000600180000000 0x00003000c0000000

def z514 : W := mkw 0x92a23fc4fc11a262 0x49511fe27e08d131 0x81001fc07c03e026 0x40800fe03e01f013

def z515 : W := mkw 0x200308921804400c 0x100184490c022006 0xd98798f27c0c603e 0xecc3cc793e06301f

def z516 : W := mkw 0x0018002802801400 0x000c001401400a00 0x7e78603f83f01fc1 0xbf3c301fc1f80fe0

def z517 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0x52fff8c0037c6000 0x297ffc6001be3000

def z518 : W := mkw 0x0000224000112000 0x0000112000089000 0x2000670000b38000 0x100033800059c000

def z519 : W := mkw 0x90002344c411a262 0x480011a26208d131 0x440060cfcc7067e6 0xa2003067e63833f3

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0xc80000c24c000000 0xe400006126000000

def z521 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xe80067cfccb386c0 0xf40033e7e659c360

def z522 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xcd8780c24c406127 0xe6c3c06126203093

def z523 : W := mkw 0x91a23fc4c41fe262 0x48d11fe2620ff131 0xed007fcfccffe7e7 0xf6803fe7e67ff3f3

def z524 : W := mkw 0x01ceeac003ff6000 0x00e7756001ffb000 0x4187e0c003ffe001 0x20c3f06001fff000

def z525 : W := mkw 0x00a23ec000000000 0x00511f6000000000 0x80001fc000000000 0x40000fe000000000

def z526 : W := mkw 0x00002344c4112000 0x000011a262089000 0xe90067cfccf3e001 0xf48033e7e679f000

def z527 : W := mkw 0x01ec764002bb2000 0x00f63b20015d9000 0xbb787f0003bf8001 0x5dbc3f8001dfc000

def z528 : W := mkw 0xd0203744e41ba272 0x68101ba2720dd139 0x81001fc07c0fe03e 0x40800fe03e07f01f

def z529 : W := mkw 0x03ffffffffee4000 0x01fffffffff72000 0xfaffffffff0c0000 0xfd7fffffff860000

def z530 : W := mkw 0x200308921804490d 0x100184490c022486 0x850018f27c0c793e 0xc2800c793e063c9f

def z531 : W := mkw 0x0018002802801400 0x000c001401400a00 0x1278003003001800 0x093c001801800c00

def z532 : W := mkw 0x8030152c60008220 0x40180a9630004110 0xbf781f3c70838621 0xdfbc0f9e3841c310

def z533 : W := mkw 0x200288801944400c 0x100144400ca22006 0xd98798c07f4c603f 0x6cc3cc603fa6301f

def z534 : W := mkw 0x905c636dc6b1b6e2 0xc82e31b6e358db71 0xef7867cfccf3e7e7 0xf7bc33e7e679f3f3

def z535 : W := mkw 0x005cc02903e01480 0x802e601481f00a40 0x7affe00d83f006c1 0x3d7ff006c1f80360

def z536 : W := mkw 0x005d403b02801400 0x002ea01d81400a00 0x7effe03f83801e01 0xbf7ff01fc1c00f00

def z537 : W := mkw 0x02c76ad39c000000 0x0163b569ce000000 0xd887f8f3fc000000 0xec43fc79fe000000

def z538 : W := mkw 0x22a23fc4fc04400c 0x11511fe27e022006 0x81001fc07c0c603e 0x40800fe03e06301f

def z539 : W := mkw 0x00002344c4000000 0x000011a262000000 0x2000670d80000000 0x10003386c0000000

def z540 : W := mkw 0x01eedc8003ff6000 0x00f76e4001ffb000 0x13ff980003ffe001 0x09ffcc0001fff000

def z541 : W := mkw 0xc038376ce68a9630 0x601c1bb673454b18 0xff787fffff8f9e39 0xffbc3fffffc7cf1c

def z542 : W := mkw 0x02f77ffffc001d81 0x817bbffffe000ec0 0xfefffffffc001fc0 0xff7ffffffe000fe0

def z543 : W := mkw 0xe03a1dac7a8ed63c 0x701d0ed63d476b1e 0xbf781ffc7f8ffe3f 0xdfbc0ffe3fc7ff1f

def z544 : W := mkw 0x8000010440008220 0x4000008220004110 0x8100070040038020 0x408003802001c010

def z545 : W := mkw 0x01aa3ec0029f6000 0x00d51f60014fb000 0xbb781fc0038fe001 0x5dbc0fe001c7f000

def z546 : W := mkw 0x02ff7ffffe801400 0x017fbfffff400a00 0xfeffffffff801e01 0xff7fffffffc00f00

def z547 : W := mkw 0xd1feffece7fff672 0x68ff7ff673fffb39 0xffffffffffffffff 0xffffffffffffffff

def z548 : W := mkw 0x0000224000112000 0x0000112000089000 0x400060c000706000 0x2000306000383000

def z549 : W := mkw 0xc1eefec003fff630 0x60f77f6001fffb18 0xffffffc003fffe39 0x7fffffe001ffff1c

def z550 : W := mkw 0x03fffefb3bff6000 0x01ffff7d9dffb000 0xfbfffff033ffe001 0x7dfffff819fff000

def z551 : W := mkw 0xc138952c63fff630 0x609c4a9631fffb18 0xbf781f3c73fffe39 0xdfbc0f9e39ffff1c

def z552 : W := mkw 0x80281504428a8220 0x40140a8221454110 0xbf781f0c438f8621 0xdfbc0f8621c7c310

def z553 : W := mkw 0x03f7fffffd756000 0x01fbfffffebab000 0xfafffffffc706000 0xfd7ffffffe383000

def z554 : W := mkw 0x0008000002801400 0x0004000001400a00 0x0400000003801e01 0x0200000001c00f00

def z555 : W := mkw 0x03a23fc4fc1f6000 0x01d11fe27e0fb000 0x81001fc07c0fe000 0x40800fe03e07f000

def z556 : W := mkw 0x02dfeafb9fe01d81 0x816ff57dcff00ec0 0x7effe0ff8ff01fc1 0xbf7ff07fc7f80fe0

def z557 : W := mkw 0x005cc02803e01400 0x002e601401f00a00 0x7effe03c03f01e01 0xbf7ff01e01f80f00

def z558 : W := mkw 0xc0080000028a9630 0x6004000001454b18 0x9d001830738f9e39 0xce800c1839c7cf1c

def z559 : W := mkw 0x005fc8bb03e45d81 0x802fe45d81f22ec0 0xfffff8ff83fc7fc1 0xfffffc7fc1fe3fe0

def z560 : W := mkw 0x02fdf77fe7e01d81 0x817efbbff3f00ec0 0x7effe73f83f01fc1 0xbf7ff39fc1f80fe0

def z561 : W := mkw 0xc1ffffff63ffffb1 0xe0ffffffb1ffffd8 0xfffffffff3fffff9 0xfffffffff9fffffc

def z562 : W := mkw 0x0019003b02801d81 0x800c801d81400ec0 0x3e78003f83801fc1 0x9f3c001fc1c00fe0

def z563 : W := mkw 0xc0000000000a8230 0x6000000000054118 0x01000000000f8038 0x008000000007c01c

def z564 : W := mkw 0x0100800001756000 0x0080400000bab000 0x0000000000706000 0x0000000000383000

def z565 : W := mkw 0x21efdc921bee490d 0x10f7ee490df72486 0x12ff9830330c1818 0x097fcc1819860c0c

def z566 : W := mkw 0x21effed21bff690d 0x10f7ff690dffb486 0xfbffffc20fffe107 0x7dffffe107fff083

def z567 : W := mkw 0x03c7ead39d756000 0x01e3f569cebab000 0x4087e0c38c706000 0x2043f061c6383000

def z568 : W := mkw 0x005c402902a01480 0x802e201481500a40 0x0278000000000000 0x013c000000000000

def z569 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x5eff803203401901 0xaf7fc01901a00c80

def z570 : W := mkw 0x02d76afb9c000000 0x016bb57dce000000 0x7affe0ff8c000000 0xbd7ff07fc6000000

def z571 : W := mkw 0x200308921800090d 0x100184490c000486 0xdc8798f27c00193e 0xee43cc793e000c9f

def z572 : W := mkw 0x200180120144490d 0x1000c00900a22486 0x5d878032034c793f 0xaec3c01901a63c9f

def z573 : W := mkw 0xa00389965944cb2d 0x5001c4cb2ca26596 0xfd879ffe7fcfff3f 0xfec3cfff3fe7ff9f

def z574 : W := mkw 0x200208801804400c 0x100104400c022006 0x000000c00c006006 0x0000006006003003

def z575 : W := mkw 0xc038376c629bb630 0x601c1bb6314ddb18 0xff787ffc73fffe39 0xffbc3ffe39ffff1c

def z576 : W := mkw 0xb00388921955eb6f 0x5801c4490caaf5b7 0xdd8798f27fffffff 0xeec3cc793fffffff

def z577 : W := mkw 0x3003aad29d55694f 0x1801d5694eaab4a7 0x4087e0c38c7061c6 0x2043f061c63830e3

def z578 : W := mkw 0x02d76bfffc000000 0x016bb5fffe000000 0x4087e0fffc000000 0xa043f07ffe000000

def z579 : W := mkw 0x0011003b00001d81 0x8008801d80000ec0 0x6c00603f80f01fc1 0xb600301fc0780fe0

def z580 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x7affe03f83001800 0xbd7ff01fc1800c00

def z581 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xd98798f0334c7819 0x6cc3cc7819a63c0c

def z582 : W := mkw 0x0055c03b01601d81 0x802ae01d80b00ec0 0x4487e03f80701fc0 0xa243f01fc0380fe0

def z583 : W := mkw 0x20339dbe7944490d 0x1019cedf3ca22486 0xffff9ffe7f4c793f 0xffffcfff3fa63c9f

def z584 : W := mkw 0x200208801804400c 0x100104400c022006 0xcd0018c27c4c613f 0xe6800c613e26309f

def z585 : W := mkw 0xb0012356dc11ab6f 0x580091ab6e08d5b7 0xed0067fffcf3ffff 0xf68033fffe79ffff

def z586 : W := mkw 0x01a03640001b2000 0x00d01b20000d9000 0x0000070000038000 0x000003800001c000

def z587 : W := mkw 0x90002344c411a262 0x480011a26208d131 0x2400670fccb387e6 0x92003387e659c3f3

def z588 : W := mkw 0x91c6ebc4c575e262 0x48e375e262baf131 0xed87e7cfccf3e7e7 0xf6c3f3e7e679f3f3

def z589 : W := mkw 0xc030152c60009630 0x60180a9630004b18 0xbe781f3c70001e38 0xdf3c0f9e38000f1c

def z590 : W := mkw 0x0000000000000000 0x0000000000000000 0xdd0018f27f4c793f 0xee800c793fa63c9f

def z591 : W := mkw 0x407dd43b23ea1d91 0xa03eea1d91f50ec8 0x7efff83fb3fc1fd9 0xbf7ffc1fd9fe0fec

def z592 : W := mkw 0x0011003b00001d81 0x8008801d80000ec0 0x0000003000001800 0x0000001800000c00

def z593 : W := mkw 0x02ff7ffffea01480 0x817fbfffff500a40 0xfafffffffcb006c0 0xfd7ffffffe580360

def z594 : W := mkw 0x01e6fec0017f6000 0x00f37f6000bfb000 0xc187ffc0007fe000 0x60c3ffe0003ff000

def z595 : W := mkw 0x0009801203e01d81 0x8004c00901f00ec0 0x5c87803203f01fc1 0xae43c01901f80fe0

def z596 : W := mkw 0x40381428228a1410 0x201c0a1411450a08 0x9f781830730c1839 0xcfbc0c1839860c1c

def z597 : W := mkw 0xc1ba3fec629ff630 0x60dd1ff6314ffb18 0xbf781ffc738ffe39 0xdfbc0ffe39c7ff1c

def z598 : W := mkw 0x905dc13fc7e09fe3 0xc82ee09fe3f04ff1 0x7effe03fcff01fe7 0xbf7ff01fe7f80ff3

def z599 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x52ffe033837019c0 0x297ff019c1b80ce0

def z600 : W := mkw 0x8018012c42809620 0x400c009621404b10 0xbf78073c43839e21 0xdfbc039e21c1cf10

def z601 : W := mkw 0x12c76ad39c112042 0x0963b569ce089021 0x4087e0c38c7061c6 0x2043f061c63830e3

def z602 : W := mkw 0x22f7dcbb3944490d 0x117bee5d9ca22486 0xdfff98f27f4c793f 0xefffcc793fa63c9f

def z603 : W := mkw 0x03eeffc4ffff6000 0x01f77fe27fffb000 0xfbffffc07fffe001 0x7dffffe03ffff000

def z604 : W := mkw 0x1000000084000042 0x0800000042000021 0x000000038c0001c6 0x00000001c60000e3

def z605 : W := mkw 0x01ceeac003f56000 0x00e7756001fab000 0x7affe0c003f06001 0x3d7ff06001f83000

def z606 : W := mkw 0x200288800144490d 0x1001444000a22486 0xdd8798c0034c793f 0x6ec3cc6001a63c9f

def z607 : W := mkw 0x800023444011a220 0x400011a22008d110 0xed0067cc40f3e621 0xf68033e62079f310

def z608 : W := mkw 0x0000000000112000 0x0000000000089000 0x0100000000f3e001 0x008000000079f000

def z609 : W := mkw 0xc03a9dac63ced630 0x601d4ed631e76b18 0xffff9ffc73cffe39 0xffffcffe39e7ff1c

def z610 : W := mkw 0x90000104c4008262 0x4800008262004131 0xcd0000cfcc4067e7 0xe6800067e62033f3

def z611 : W := mkw 0x0038152c62801400 0x001c0a9631400a00 0xbe781f3c73801e01 0xdf3c0f9e39c00f00

def z612 : W := mkw 0xc0201504600a8230 0x60100a8230054118 0xad001f0c708f8639 0xd6800f863847c31c

def z613 : W := mkw 0xb0010116dc008b6f 0x5800808b6e0045b7 0x0400003ffc001ffe 0x8200001ffe000fff

def z614 : W := mkw 0x3003aad29d55694f 0x1801d5694eaab4a7 0xdd87f8f3ff7c79ff 0xeec3fc79ffbe3cff

def z615 : W := mkw 0x200100121800090d 0x100080090c000486 0x000000020c000106 0x0000000106000083

def z616 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xba781f3c70838600 0xdd3c0f9e3841c300

def z617 : W := mkw 0x11c6eac085756042 0x08e3756042bab021 0x4087e0c38c7061c6 0x2043f061c63830e3

def z618 : W := mkw 0x91eeffc4c7ffe262 0x48f77fe263fff131 0xfbffffcd83ffe6c1 0x7dffffe6c1fff360

def z619 : W := mkw 0x0000000000000000 0x0000000000000000 0x9800183070000000 0xcc000c1838000000

def z620 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x458780c20f4c793f 0x22c3c06107a63c9f

def z621 : W := mkw 0x0018002802801400 0x000c001401400a00 0xbf78183c738c1e39 0xdfbc0c1e39c60f1c

def z622 : W := mkw 0xc07dd53f63ea9fb1 0xe03eea9fb1f54fd8 0xbfff9f3c738f9e39 0xdfffcf9e39c7cf1c

def z623 : W := mkw 0x90e67fc4c411a262 0x48733fe26208d131 0xffffffcfccf3e7e7 0xffffffe7e679f3f3

def z624 : W := mkw 0xb1efffd6dfffeb6f 0x58f7ffeb6ffff5b7 0xffffffffffffffff 0xffffffffffffffff

def z625 : W := mkw 0x0002888001444000 0x0001444000a22000 0xdd8798c24f4c6127 0xeec3cc6127a63093

def z626 : W := mkw 0x42ff5cbb3a8a1410 0x217fae5d9d450a08 0x12ff9830330c1818 0x097fcc1819860c0c

def z627 : W := mkw 0x03fc776de6bb2000 0x01fe3bb6f35d9000 0x2278670d80b38000 0x113c3386c059c000

def z628 : W := mkw 0xe01389be7944df3d 0x7009c4df3ca26f9e 0xdd8798fe7f4c7f3f 0xeec3cc7f3fa63f9f

def z629 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x16ff803f83001fc0 0x8b7fc01fc1800fe0

def z630 : W := mkw 0x02f7fffffd600981 0x817bfffffeb004c0 0xfafffffffc7001c0 0xfd7ffffffe3800e0

def z631 : W := mkw 0x0003089218000000 0x000184490c000000 0xdd8798f27f0c1839 0xeec3cc793f860c1c

def z632 : W := mkw 0x03ffffffffff7d81 0x81ffffffffffbec0 0xffffffffffffffc1 0xffffffffffffffe0

def z633 : W := mkw 0x00032bd6dc000000 0x000195eb6e000000 0xf887fffffc000000 0xfc43fffffe000000

def z634 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x7affe03003f01801 0x3d7ff01801f80c00

def z635 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x2778070c038f9e39 0x13bc038601c7cf1c

def z636 : W := mkw 0xd0203744e41ba272 0x68101ba2720dd139 0xed007fcffcffe7ff 0xf6803fe7fe7ff3ff

def z637 : W := mkw 0x01c6eac001756000 0x00e3756000bab000 0xd987f8c0037c6001 0x6cc3fc6001be3000

def z638 : W := mkw 0x23ffffffffff690d 0x11ffffffffffb486 0xfffffffffffff93f 0xfffffffffffffc9f

def z639 : W := mkw 0x90002344c411a262 0x480011a26208d131 0x6c00670f80f387c1 0xb6003387c079c3e0

def z640 : W := mkw 0x0000000000000000 0x0000000000000000 0xa900070000838001 0x548003800041c000

def z641 : W := mkw 0x007dd43b03ea1d81 0x803eea1d81f50ec0 0xffffff3f83ff9fc1 0xffffff9fc1ffcfe0

def z642 : W := mkw 0x01feffec63ff6000 0x00ff7ff631ffb000 0xfbfffffc73ffe001 0xfdfffffe39fff000

def z643 : W := mkw 0x02b33ffffc000000 0x01599ffffe000000 0x80001ffffc000000 0xc0000ffffe000000

def z644 : W := mkw 0x02b23fecfc000000 0x01591ff67e000000 0xba781ffc7c000000 0xdd3c0ffe3e000000

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0x400000c20c406106 0x2000006106203083

def z646 : W := mkw 0xc2ff5dbf7a8a9630 0x617faedfbd454b18 0xbfff9f3c738f9e39 0xdfffcf9e39c7cf1c

def z647 : W := mkw 0x02f7fffffd400901 0x017bfffffea00480 0xfeffffffff401901 0xff7fffffffa00c80

def z648 : W := mkw 0x01a23ec0001f6000 0x00d11f60000fb000 0xe9007fc000ffe001 0x74803fe0007ff000

def z649 : W := mkw 0x92a23fc4fc11a262 0x49511fe27e08d131 0xed007fcffcf3e7e7 0xf6803fe7fe79f3f3

def z650 : W := mkw 0x200100121800090d 0x100080090c000486 0xcd0000f27c40793f 0xe68000793e203c9f

def z651 : W := mkw 0x900000000011a262 0x480000000008d131 0x0000000000b386c0 0x000000000059c360

def z652 : W := mkw 0x0018802803e01d81 0x800c401401f00ec0 0x3e78003c03f01fc1 0x9f3c001e01f80fe0

def z653 : W := mkw 0xb00080000155eb6f 0x5800400000aaf5b7 0x0500000003ffffff 0x0280000001ffffff

def z654 : W := mkw 0x01effed21bff6000 0x00f7ff690dffb000 0xfbfffff27fffe001 0xfdfffff93ffff000

def z655 : W := mkw 0xc2ffffffffea9fb1 0xe17ffffffff54fd8 0xffffffffffff9ff9 0xffffffffffffcffc

def z656 : W := mkw 0x221389bffd44490d 0x1109c4dffea22486 0xdd8798ffff4c793f 0xeec3cc7fffa63c9f

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0xc90000c000406001 0x6480006000203000

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c00003003001801 0x8e00001801800c00

def z659 : W := mkw 0x603b9cba3bce5d1d 0x301dce5d1de72e8e 0xdfff98f27f4c793f 0xefffcc793fa63c9f

def z660 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x3eff803c03801e01 0x9f7fc01e01c00f00

def z661 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x15879830334c793f 0x0ac3cc1819a63c9f

def z662 : W := mkw 0xb2f7fffffd55eb6f 0x597bfffffeaaf5b7 0xffffffffffffffff 0xffffffffffffffff

def z663 : W := mkw 0x900022400011a262 0x480011200008d131 0xed0067c000f3e7e7 0x768033e00079f3f3

def z664 : W := mkw 0x90000104c4008262 0x4800008262004131 0xad00070fcc8387e7 0xd6800387e641c3f3

def z665 : W := mkw 0x0002088018000000 0x000104400c000000 0x800018c07c000000 0x40000c603e000000

def z666 : W := mkw 0x0018002802801400 0x000c001401400a00 0x2278000c00800600 0x113c000600400300

def z667 : W := mkw 0x0128940003ff6000 0x00944a0001ffb000 0xbb781f0003ffe001 0x5dbc0f8001fff000

def z668 : W := mkw 0xe0239d96794ecb3d 0x7011cecb3ca7659e 0xdd879ff27f4ff93f 0xeec3cff93fa7fc9f

def z669 : W := mkw 0x0003889219400901 0x0001c4490ca00480 0xdc8798f27f401901 0xee43cc793fa00c80

def z670 : W := mkw 0xc018012c628a9630 0x600c009631454b18 0x0500003c738f9e39 0x8280001e39c7cf1c

def z671 : W := mkw 0x0019803a03c01d01 0x000cc01d01e00e80 0x7eff803e03c01f01 0xbf7fc01f01e00f80

def z672 : W := mkw 0x407dd43b23ea1d91 0xa03eea1d91f50ec8 0x12ff9830330c1818 0x097fcc1819860c0c

def z673 : W := mkw 0x10002344c4112042 0x080011a262089021 0xe80067cfcc7061c6 0xf40033e7e63830e3

def z674 : W := mkw 0xc0381428228a9630 0x601c0a1411454b18 0x17781830338f9e39 0x0bbc0c1819c7cf1c

def z675 : W := mkw 0xb0022bc4dc15e26e 0x580115e26e0af137 0x81001fc07c0fe03e 0x40800fe03e07f01f

def z676 : W := mkw 0x41fedca823ee5410 0x20ff6e5411f72a08 0x12ff9830330c1818 0x097fcc1819860c0c

def z677 : W := mkw 0x1000224084112042 0x0800112042089021 0x00006001803000c0 0x00003000c0180060

def z678 : W := mkw 0x01ec764002bb2000 0x00f63b20015d9000 0xeb7867c000f3e001 0x75bc33e00079f000

def z679 : W := mkw 0xd0080000029bb672 0x68040000014ddb39 0x0500000003ffffff 0x0280000001ffffff

def z680 : W := mkw 0x9011237fc411bfe3 0xc80891bfe208dff1 0xed0067ffccf3ffe7 0xf68033ffe679fff3

def z681 : W := mkw 0x004cc00003e01d81 0x8026600001f00ec0 0x7effe00003f01fc1 0x3f7ff00001f80fe0

def z682 : W := mkw 0x0003089218000000 0x000184490c000000 0x408780c20c000000 0x2043c06106000000

def z683 : W := mkw 0x0000000000000000 0x0000000000000000 0xed0060cfccf067e7 0xf6803067e67833f3

def z684 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x16ff803003f01fc1 0x0b7fc01801f80fe0

def z685 : W := mkw 0x01ecf64003ff6000 0x00f67b2001ffb000 0x2378670003ffe001 0x11bc338001fff000

def z686 : W := mkw 0x0000800001400000 0x0000400000a00000 0x5887800003400001 0x2c43c00001a00000

def z687 : W := mkw 0x00201400000a0000 0x00100a0000050000 0x81001f00000f8000 0x40800f800007c000

def z688 : W := mkw 0x0055c03b01600981 0x802ae01d80b004c0 0x7affe03f807001c0 0xbd7ff01fc03800e0

def z689 : W := mkw 0x02c76bd7dc000000 0x0163b5ebee000000 0xe887e7cfcc000000 0xf443f3e7e6000000

def z690 : W := mkw 0xe0221d84780ec23c 0x70110ec23c07611e 0x81001fc07c0fe03e 0x40800fe03e07f01f

def z691 : W := mkw 0x204fc8921be4490d 0x1027e4490df22486 0xfffff8f27ffc793f 0xfffffc793ffe3c9f

def z692 : W := mkw 0x91ec7744c6bba262 0x48f63ba2635dd131 0xef7867cfccf3e7e7 0xf7bc33e7e679f3f3

def z693 : W := mkw 0x92f4776de411a262 0x497a3bb6f208d131 0xef7867cfccf3e7e7 0xf7bc33e7e679f3f3

def z694 : W := mkw 0x025dc13fffe01d81 0x812ee09ffff00ec0 0x7effe03ffff01fc1 0xbf7ff01ffff80fe0

def z695 : W := mkw 0x02ffdcbb3be01d81 0x817fee5d9df00ec0 0x12ff983033001800 0x097fcc1819800c00

def z696 : W := mkw 0x21a23ec0181f600c 0x10d11f600c0fb006 0x81001fc07c0fe03e 0x40800fe03e07f01f

def z697 : W := mkw 0xc2ba3fecfe8a9630 0x615d1ff67f454b18 0xbf781ffc7f8f9e39 0xdfbc0ffe3fc7cf1c

def z698 : W := mkw 0x02ffffffffe00000 0x017ffffffff00000 0xfafffffffff00001 0xfd7ffffffff80000

def z699 : W := mkw 0x0030376ce4000000 0x00181bb672000000 0xfa787ffffc000000 0xfd3c3ffffe000000

def z700 : W := mkw 0x01a21c80000e4000 0x00d10e4000072000 0x00001800000c0000 0x00000c0000060000

def z701 : W := mkw 0x9001a356c551ab63 0x4800d1ab62a8d5b1 0xfd87e7ffcff3ffe7 0xfec3f3ffe7f9fff3

def z702 : W := mkw 0x0000000000000000 0x0000000000000000 0x99001800030c0001 0x4c800c0001860000

def z703 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x5c8780f20f407907 0xae43c07907a03c83

def z704 : W := mkw 0xe039153e7a8a9f3d 0x701c8a9f3d454f9e 0xbf781f3e7f8f9f3f 0xdfbc0f9f3fc7cf9f

def z705 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x448780f27c40793e 0xa243c0793e203c9f

def z706 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c00000200400101 0xa600000100200080

def z707 : W := mkw 0x1000224084112042 0x0800112042089021 0xed0067cf8cf3e7c7 0xf68033e7c679f3e3

def z708 : W := mkw 0x00e77ed200000000 0x0073bf6900000000 0xfafffff200000000 0xfd7ffff900000000

def z709 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0xfbffffc0030c0001 0x7dffffe001860000

def z710 : W := mkw 0x1108800003ff6042 0x0884400001ffb021 0x0100000003ffe1c7 0x0080000001fff0e3

def z711 : W := mkw 0x01e67ec0001f6000 0x00f33f60000fb000 0xfbffffc000ffe001 0x7dffffe0007ff000

def z712 : W := mkw 0x004eeac003f56000 0x0027756001fab000 0xfbffffc003ffe001 0x7dffffe001fff000

def z713 : W := mkw 0x9211013ffc008262 0x4908809ffe004131 0x0000003ffc0006c0 0x8000001ffe000360

def z714 : W := mkw 0x01e67ec0001f6000 0x00f33f60000fb000 0x93ff9fc0000fe000 0x49ffcfe00007f000

def z715 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0x22ffe70d80000000 0x117ff386c0000000

def z716 : W := mkw 0x03aabfc4ffff6000 0x01d55fe27fffb000 0x81001fc07fffe001 0x40800fe03ffff000

def z717 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x7effe03ff3f01ff9 0xbf7ff01ff9f80ffc

def z718 : W := mkw 0x0108800003ee5d81 0x8084400001f72ec0 0x00000000030c1800 0x0000000001860c00

def z719 : W := mkw 0x9055637fc411a262 0x482ab1bfe208d131 0xfbffe7ffcc03e026 0xfdfff3ffe601f013

def z720 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfffffffffcf067e7 0xfffffffffe7833f3

def z721 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0x0000000000f3e000 0x000000000079f000

def z722 : W := mkw 0x8108800003ffe220 0x4084400001fff110 0x0500000003ffe621 0x0280000001fff310

def z723 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xff787f3c73ff9e39 0xffbc3f9e39ffcf1c

def z724 : W := mkw 0x92f5777fe411a262 0x497abbbff208d131 0xffffe7ffccf3e7e7 0xfffff3ffe679f3f3

def z725 : W := mkw 0xc019813f63ea9fb1 0xe00cc09fb1f54fd8 0x0500003ff3ff9ff9 0x8280001ff9ffcffc

def z726 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xe90067cf8cf3e7c7 0x748033e7c679f3e3

def z727 : W := mkw 0x005d403b02a01480 0x802ea01d81500a40 0x62ffe00f80b006c0 0x317ff007c0580360

def z728 : W := mkw 0x0055403b00000981 0x802aa01d800004c0 0x7affe03f800001c0 0xbd7ff01fc00000e0

def z729 : W := mkw 0x00e67ec000112000 0x00733f6000089000 0xfbffffc00003e000 0x7dffffe00001f000

def z730 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x52fff833b0000000 0x297ffc19d8000000

def z731 : W := mkw 0xc0f67fec60009630 0x607b3ff630004b18 0xfefffffc70001e38 0xff7ffffe38000f1c

def z732 : W := mkw 0x92f77ffffc008262 0x497bbffffe004131 0xfffffffffc8387e7 0xfffffffffe41c3f3

def z733 : W := mkw 0x200980121be01d8d 0x9004c0090df00ec6 0x040000327ff01fff 0x820000193ff80fff

def z734 : W := mkw 0xb011013fdc009fef 0xd808809fee004ff7 0x0400003ffc001ffe 0x8200001ffe000fff

def z735 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfbfffff073ffe001 0xfdfffff839fff000

def z736 : W := mkw 0xc030152c600a8230 0x60180a9630054118 0xbf781f3c730f9839 0xdfbc0f9e3987cc1c

def z737 : W := mkw 0x22f77ffffc001d8d 0x917bbffffe000ec6 0xfefffffffc001ffe 0xff7ffffffe000fff

def z738 : W := mkw 0x02d76afb9c000000 0x016bb57dce000000 0xfafff8fffc000000 0xfd7ffc7ffe000000

def z739 : W := mkw 0x02e67ec184000000 0x01733f60c2000000 0xfaffffc180000000 0x7d7fffe0c0000000

def z740 : W := mkw 0x0008800003e00000 0x0004400001f00000 0x0000000003000000 0x0000000001800000

def z741 : W := mkw 0x0055403b00001d81 0x802aa01d80000ec0 0x7effe03f80f01fc1 0xbf7ff01fc0780fe0

def z742 : W := mkw 0xd2f77ffffc1ba272 0x697bbffffe0dd139 0xfbfffffffc0fe03e 0xfdfffffffe07f01f

def z743 : W := mkw 0x2055403b1800090d 0x102aa01d8c000486 0x7effe03ffc00193e 0xbf7ff01ffe000c9f

def z744 : W := mkw 0x01e65c80000e4000 0x00f32e4000072000 0x12ff9800000c0000 0x097fcc0000060000

def z745 : W := mkw 0x004dc01203e00901 0x0026e00901f00480 0x7effe03f83f01fc1 0xbf7ff01fc1f80fe0

def z746 : W := mkw 0x0019803b03e01d81 0x800cc01d81f00ec0 0x0400003f83001fc0 0x8200001fc1800fe0

def z747 : W := mkw 0x2019803b1be45d8d 0x900cc01d8df22ec6 0x0500003ffffc7fff 0x8280001ffffe3fff

def z748 : W := mkw 0x015dc03b03ee5d81 0x80aee01d81f72ec0 0x7effe03f83fc1fc1 0xbf7ff01fc1fe0fe0

def z749 : W := mkw 0x012a9c8003ff6000 0x00954e4001ffb000 0xfbff9fc003ffe001 0x7dffcfe001fff000

def z750 : W := mkw 0x9255637ffc11a262 0x492ab1bffe08d131 0xffffe7fffcf3e7e7 0xfffff3fffe79f3f3

def z751 : W := mkw 0x2008800003e4490d 0x1004400001f22486 0x0500000003fc793f 0x0280000001fe3c9f

def z752 : W := mkw 0x405dc03b23e01d91 0xa02ee01d91f00ec8 0x7effe03fb3f01fd9 0xbf7ff01fd9f80fec

def z753 : W := mkw 0x93a23fc4fc1fe262 0x49d11fe27e0ff131 0x81001fc07c0fe026 0x40800fe03e07f013

def z754 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xdd8798ffff4c7fff 0xeec3cc7fffa63fff

def z755 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfbfffffffcf3e027 0xfdfffffffe79f013

def z756 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x12ff803f80000000 0x897fc01fc0000000

def z757 : W := mkw 0x200180121940090d 0x1000c0090ca00486 0x040000327f40193f 0x820000193fa00c9f

def z758 : W := mkw 0x0044624000112000 0x0022312000089000 0xfbffe7c000f3e001 0x7dfff3e00079f000

def z759 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfbfffffffcb3e6e6 0xfdfffffffe59f373

def z760 : W := mkw 0x2008800003ce490d 0x1004400001e72486 0x0500000003cff93f 0x0280000001e7fc9f

def z761 : W := mkw 0x12d76afb9c112042 0x096bb57dce089021 0x7effe0ff8cf067c7 0xbf7ff07fc67833e3

def z762 : W := mkw 0xe03b9dbe7bcedf3d 0x701dcedf3de76f9e 0x62ff87ce0cc3e706 0x317fc3e70661f383

def z763 : W := mkw 0x0255637ffc000000 0x012ab1bffe000000 0xfaffe7fffc000000 0xfd7ff3fffe000000

def z764 : W := mkw 0x00f67ee820000000 0x007b3f7410000000 0xfafffff030000000 0x7d7ffff818000000

def z765 : W := mkw 0x210980121bff690d 0x1084c0090dffb486 0x050000327ffff93f 0x828000193ffffc9f

def z766 : W := mkw 0x0009801303e01d81 0x8004c00981f00ec0 0x0400000383f01fc1 0x02000001c1f80fe0

def z767 : W := mkw 0x00f77efb18000000 0x007bbf7d8c000000 0xfafffffffc000000 0xfd7ffffffe000000

def z768 : W := mkw 0x91aabfc4c7ffe262 0x48d55fe263fff131 0x85001fc04fffe7e7 0x42800fe027fff3f3

def z769 : W := mkw 0x90f67fece411a262 0x487b3ff67208d131 0xfffffffffcf3e7e7 0xfffffffffe79f3f3

def z770 : W := mkw 0xc2f77ffffc009fb1 0xe17bbffffe004fd8 0xfefffffffc001ff8 0xff7ffffffe000ffc

def z771 : W := mkw 0x02f77efb38000000 0x017bbf7d9c000000 0x32ffff3030000000 0x197fff9818000000

def z772 : W := mkw 0x0044400000000000 0x0022200000000000 0x12ff800000000000 0x097fc00000000000

def z773 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0x92ff9fc000000000 0x497fcfe000000000

def z774 : W := mkw 0xd011013fe4009ff3 0xe808809ff2004ff9 0x0400003ffc001ffe 0x8200001ffe000fff

def z775 : W := mkw 0x0008800003ea0000 0x0004400001f50000 0x0100000003ff8001 0x0080000001ffc000

def z776 : W := mkw 0x9008800003e09fe3 0xc804400001f04ff1 0x0400000003f01fe7 0x0200000001f80ff3

def z777 : W := mkw 0x0108800003ee4000 0x0084400001f72000 0x01000000038f8001 0x0080000001c7c000

def z778 : W := mkw 0xc1fe7fec629ff630 0x60ff3ff6314ffb18 0xfffffffc738ffe39 0xfffffffe39c7ff1c

def z779 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfefffffffc7067e6 0xff7ffffffe3833f3

def z780 : W := mkw 0x01eefec003ff7d81 0x80f77f6001ffbec0 0xffffffcf83ffffc1 0xffffffe7c1ffffe0

def z781 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xd98798f07f4c783f 0x6cc3cc783fa63c1f

def z782 : W := mkw 0x8018012c42809620 0x400c009621404b10 0xbf781f3c738f9e39 0xdfbc0f9e39c7cf1c

def z783 : W := mkw 0x02f77efbbc000000 0x017bbf7dde000000 0xfafffff3bc000000 0x7d7ffff9de000000

def z784 : W := mkw 0xc0381428228a9630 0x601c0a1411454b18 0xbf781f30338f9e39 0x5fbc0f9819c7cf1c

def z785 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0xfefff83ff3f01fc1 0xff7ffc1ff9f80fe0

def z786 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x02ff800000000000 0x017fc00000000000

def z787 : W := mkw 0x01eefec003ff7400 0x00f77f6001ffba00 0xffffffc003fffe01 0x7fffffe001ffff00

def z788 : W := mkw 0x0001801201400901 0x0000c00900a00480 0xdd8798f27f4c793f 0xeec3cc793fa63c9f

def z789 : W := mkw 0xc2f75dbf780a8230 0x617baedfbc054118 0x93ff9f30700f8038 0x49ffcf983807c01c

def z790 : W := mkw 0x12f77ffffc112042 0x097bbffffe089021 0xfefffffffcf067c7 0xff7ffffffe7833e3

def z791 : W := mkw 0x0255403b9c000000 0x012aa01dce000000 0x7affe03f8c000000 0xbd7ff01fc6000000

def z792 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfffffff003fff801 0xfffffff801fffc00

def z793 : W := mkw 0x11eefec087ff6042 0x08f77f6043ffb021 0xffffffcf8fffe7c7 0xffffffe7c7fff3e3

def z794 : W := mkw 0x0045401300000000 0x0022a00980000000 0x7affe00380000000 0x3d7ff001c0000000

def z795 : W := mkw 0x42f77ffffc0a0010 0x217bbffffe050008 0xfafffffffc0c0018 0xfd7ffffffe06000c

def z796 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfafffffdb0000000 0x7d7ffffed8000000

def z797 : W := mkw 0x004cc00003e00000 0x0026600001f00000 0x7affe00d83f006c1 0x3d7ff006c1f80360

def z798 : W := mkw 0x00e67fc440000000 0x00733fe220000000 0xfaffffcc40000000 0xfd7fffe620000000

def z799 : W := mkw 0x20e67ec01804400c 0x10733f600c022006 0xfbffffc07c0c603e 0x7dffffe03e06301f

def z800 : W := mkw 0x0108a344c7ff6000 0x008451a263ffb000 0xe90067cfcfffe001 0xf48033e7e7fff000

def z801 : W := mkw 0x02f5777fe4000000 0x017abbbff2000000 0x32ffe73d80000000 0x197ff39ec0000000

def z802 : W := mkw 0x10e67ec084112042 0x08733f6042089021 0xfaffffc38c7061c6 0x7d7fffe1c63830e3

def z803 : W := mkw 0x00f75cbb00000000 0x007bae5d80000000 0x7afff83f80000000 0xbd7ffc1fc0000000

def z804 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xfd87f8ffff4c793f 0xfec3fc7fffa63c9f

def z805 : W := mkw 0xc211013ffc009fb1 0xe108809ffe004fd8 0x0400003ffc001ff8 0x8200001ffe000ffc

def z806 : W := mkw 0xc065d517616a8bb1 0xe032ea8bb0b545d8 0xc187ff03f07f81f8 0x60c3ff81f83fc0fc

def z807 : W := mkw 0xc018012c62809630 0x600c009631404b18 0x0400003c73801e39 0x8200001e39c00f1c

def z808 : W := mkw 0x02f77efbbc000000 0x017bbf7dde000000 0x7afff8ffbc000000 0xbd7ffc7fde000000

def z809 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfbffffc20fffe107 0x7dffffe107fff083

def z810 : W := mkw 0x9008800003f1bfe3 0xc804400001f8dff1 0x0400000003f39fc1 0x0200000001f9cfe0

def z811 : W := mkw 0x01e67ec000312000 0x00f33f6000189000 0xfaffffc000300000 0x7d7fffe000180000

def z812 : W := mkw 0x02e77ed39c000000 0x0173bf69ce000000 0xfafffff3fc000000 0xfd7ffff9fe000000

def z813 : W := mkw 0x00eefec003ce4000 0x00777f6001e72000 0xfbffffc003cfe001 0x7dffffe001e7f000

def z814 : W := mkw 0x00ee5c80028a0000 0x00772e4001450000 0xbbff9f00038f8001 0x5dffcf8001c7c000

def z815 : W := mkw 0x00ee7ec0028a0000 0x00773f6001450000 0xfaffffc000838000 0x7d7fffe00041c000

def z816 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0xfbffffc000838001 0x7dffffe00041c000

def z817 : W := mkw 0x01eedc8003ee4000 0x00f76e4001f72000 0xfbffff0003ff8001 0x7dffff8001ffc000

def z818 : W := mkw 0x20e7fed21955690d 0x1073ff690caab486 0xfffffff27ffff93f 0xfffffff93ffffc9f

def z819 : W := mkw 0x00221c8000000000 0x00110e4000000000 0xfaff9fc000000000 0x7d7fcfe000000000

def z820 : W := mkw 0x21ed76521abb290d 0x10f6bb290d5d9486 0x267867327cb3993e 0x933c33993e59cc9f

def z821 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x9aff983070000000 0xcd7fcc1838000000

def z822 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xffffffc003ffe7c1 0x7fffffe001fff3e0

def z823 : W := mkw 0x00e67ec0000a0000 0x00733f6000050000 0xfbffffc0000f8000 0x7dffffe00007c000

def z824 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0x33ffff0003ffe001 0x19ffff8001fff000

def z825 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0x01000000030fe000 0x008000000187f000

def z826 : W := mkw 0x02f77ffffc001d81 0x817bbffffe000ec0 0xfafffffffc001800 0xfd7ffffffe000c00

def z827 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x958798f07f4c793f 0x4ac3cc783fa63c9f

def z828 : W := mkw 0x005c402902a01480 0x802e201481500a40 0x7affe00d80b006c0 0x3d7ff006c0580360

def z829 : W := mkw 0x8108810443ffe220 0x4084408221fff110 0xad00070c43ffe621 0xd680038621fff310

def z830 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0x32ffff3ffc000000 0x997fff9ffe000000

def z831 : W := mkw 0x005cc02903e01d81 0x802e601481f00ec0 0x7effe00d83f01fc1 0x3f7ff006c1f80fe0

def z832 : W := mkw 0x01ee7ec002bb2000 0x00f73f60015d9000 0xfbffffc003bf8001 0x7dffffe001dfc000

def z833 : W := mkw 0x205748bb18001d8d 0x902ba45d8c000ec6 0xfefff8fffc001ffe 0xff7ffc7ffe000fff

def z834 : W := mkw 0x00446344c4000000 0x002231a262000000 0xfaffe7cfcc000000 0xfd7ff3e7e6000000

def z835 : W := mkw 0x00f67ee900000000 0x007b3f7480000000 0xfaffffcd80000000 0x7d7fffe6c0000000

def z836 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0x62ffe7c000000000 0x317ff3e000000000

def z837 : W := mkw 0x32c7ead39d55694f 0x1963f569ceaab4a7 0x4087e0c38c7061c6 0x2043f061c63830e3

def z838 : W := mkw 0xc018012c628a9630 0x600c009631454b18 0x0400003c730c1e38 0x8200001e39860f1c

def z839 : W := mkw 0x22f75cbb3800090d 0x117bae5d9c000486 0x16ff98327c00193e 0x8b7fcc193e000c9f

def z840 : W := mkw 0x03f77ffffc1f6000 0x01fbbffffe0fb000 0xfbfffffffcffe001 0xfdfffffffe7ff000

def z841 : W := mkw 0xc0281400028a9630 0x60140a0001454b18 0xbf781f30738f9e39 0xdfbc0f9839c7cf1c

def z842 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfbfffffffc406001 0xfdfffffffe203000

def z843 : W := mkw 0x22f4f76de544490d 0x117a7bb6f2a22486 0x2778670d834c793f 0x13bc3386c1a63c9f

def z844 : W := mkw 0x0108a24003ff6000 0x0084512001ffb000 0x810007c003ffe001 0x408003e001fff000

def z845 : W := mkw 0x0319813fffff6000 0x018cc09fffffb000 0x0100003fffffe001 0x8080001ffffff000

def z846 : W := mkw 0xd2fc776de69bb672 0x697e3bb6f34ddb39 0x2278670d80b386c0 0x113c3386c059c360

def z847 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xfd87f8f27ffc793f 0xfec3fc793ffe3c9f

def z848 : W := mkw 0x90a23fc4c411a262 0x48511fe26208d131 0x81001fc04c03e026 0x40800fe02601f013

def z849 : W := mkw 0x0255413fe4000000 0x012aa09ff2000000 0x7affe03f80000000 0xbd7ff01fc0000000

def z850 : W := mkw 0x21eefec01bff600c 0x10f77f600dffb006 0xfbffffc00fffe007 0x7dffffe007fff003

def z851 : W := mkw 0x0108a24003ff7d81 0x8084512001ffbec0 0xed0067cf83ffffc1 0xf68033e7c1ffffe0

def z852 : W := mkw 0x200a88801be45d8d 0x900544400df22ec6 0x850018c07ffc7fff 0x42800c603ffe3fff

def z853 : W := mkw 0x1008a24087f13dc3 0x8804512043f89ee1 0x440060c38ff07fc7 0x22003061c7f83fe3

def z854 : W := mkw 0x90e67fc4c4008262 0x48733fe262004131 0xfeffffcfcc0007e6 0xff7fffe7e60003f3

def z855 : W := mkw 0xb2f77ffffc15e26e 0x597bbffffe0af137 0xfffffffffcffe7ff 0xfffffffffe7ff3ff

def z856 : W := mkw 0x02f77ffffc000981 0x817bbffffe0004c0 0xfafffffffc0001c0 0xfd7ffffffe0000e0

def z857 : W := mkw 0x904cc104c7e08262 0x4826608263f04131 0x7effe00fcff007e7 0xbf7ff007e7f803f3

def z858 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0x12ff9f00030f8000 0x097fcf800187c000

def z859 : W := mkw 0x40381428228a1410 0x201c0a1411450a08 0xbf781f30738f9839 0xdfbc0f9839c7cc1c

def z860 : W := mkw 0x12f77ffffc000042 0x097bbffffe000021 0xfafffffffc0001c6 0xfd7ffffffe0000e3

def z861 : W := mkw 0xb211013ffc008b6f 0x5908809ffe0045b7 0x0400003ffc001ffe 0x8200001ffe000fff

def z862 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x1c00003003f01fc1 0x8e00001801f80fe0

def z863 : W := mkw 0x0008800003e44000 0x0004400001f22000 0x0100000003fc6001 0x0080000001fe3000

def z864 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xe80067cfccf3e7c6 0xf40033e7e679f3e3

def z865 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0xffffe73f83f39fc1 0xfffff39fc1f9cfe0

def z866 : W := mkw 0x005d403b02801400 0x002ea01d81400a00 0x7effe03f83f01fc1 0xbf7ff01fc1f80fe0

def z867 : W := mkw 0x00f77ffe78000000 0x007bbfff3c000000 0xfafffffe7c000000 0xfd7fffff3e000000

def z868 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x7effe03f800007c0 0xbf7ff01fc00003e0

def z869 : W := mkw 0x8030152c60008220 0x40180a9630004110 0xbf781f3c738f9e39 0xdfbc0f9e39c7cf1c

def z870 : W := mkw 0xb003abd6dd55eb6f 0x5801d5eb6eaaf5b7 0x3087ff3db3bf9ed8 0x1843ff9ed9dfcf6c

def z871 : W := mkw 0x905de37fc7f1bfe3 0xc82ef1bfe3f8dff1 0x93ff87f04f03f826 0x49ffc3f82781fc13

def z872 : W := mkw 0x0108800003ee4000 0x0084400001f72000 0x0000000003fc0001 0x0000000001fe0000

def z873 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0x92ff9ffffc000000 0xc97fcffffe000000

def z874 : W := mkw 0x02f67fede4000000 0x017b3ff6f2000000 0xfafffffdf0000000 0xfd7ffffef8000000

def z875 : W := mkw 0x00231c9218000000 0x00118e490c000000 0xfaff9ff27c000000 0xfd7fcff93e000000

def z876 : W := mkw 0x02d748bb18000000 0x016ba45d8c000000 0x7affe03f80000000 0xbd7ff01fc0000000

def z877 : W := mkw 0x4008800003ea1d91 0xa004400001f50ec8 0x0400000003fc1fd9 0x0200000001fe0fec

def z878 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xff787fffffffffff 0xffbc3fffffffffff

def z879 : W := mkw 0x00e67ec018000000 0x00733f600c000000 0xfaffffc07c000000 0x7d7fffe03e000000

def z880 : W := mkw 0x0003089218000000 0x000184490c000000 0xdd8798f27f4c793f 0xeec3cc793fa63c9f

def z881 : W := mkw 0x02f67fedfc000000 0x017b3ff6fe000000 0xfaffffcdfc000000 0x7d7fffe6fe000000

def z882 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x00000000037019c0 0x0000000001b80ce0

def z883 : W := mkw 0x82f77ffffc11a220 0x417bbffffe08d110 0xfffffffffcf3e621 0xfffffffffe79f310

def z884 : W := mkw 0x014ce24003ff6000 0x00a6712001ffb000 0xfbffe7c003ffe001 0x7dfff3e001fff000

def z885 : W := mkw 0x11eefec087ff6042 0x08f77f6043ffb021 0xffffffc3cfffe1e7 0xffffffe1e7fff0f3

def z886 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x97781f30738f9e39 0x4bbc0f9839c7cf1c

def z887 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xe3ffffc000ffe000 0x71ffffe0007ff000

def z888 : W := mkw 0x02b33ffefc000000 0x01599fff7e000000 0xfaff9ffe7c000000 0xfd7fcfff3e000000

def z889 : W := mkw 0x02f5543b20000000 0x017aaa1d90000000 0x7affe03f80000000 0xbd7ff01fc0000000

def z890 : W := mkw 0x004ce24003f12000 0x0026712001f89000 0x7affe70003f38001 0x3d7ff38001f9c000

def z891 : W := mkw 0x01b33efb001f7d81 0x80d99f7d800fbec0 0x85001fff800fffc0 0xc2800fffc007ffe0

def z892 : W := mkw 0x00eefec003f12000 0x00777f6001f89000 0xfbffffc003f3e001 0x7dffffe001f9f000

def z893 : W := mkw 0x03f77ffffc1b2000 0x01fbbffffe0d9000 0xfafffffffc038000 0xfd7ffffffe01c000

def z894 : W := mkw 0x004cc00003e01d81 0x8026600001f00ec0 0x7effe00f83f01fc1 0xbf7ff007c1f80fe0

def z895 : W := mkw 0x200388921964498d 0x9001c4490cb224c6 0xdd8798f27f7c79ff 0xeec3cc793fbe3cff

def z896 : W := mkw 0x005d403b02a01d81 0x802ea01d81500ec0 0x7effe03f80b01fc0 0xbf7ff01fc0580fe0

def z897 : W := mkw 0x92a23fc4fc11a262 0x49511fe27e08d131 0x80001fc07c038000 0x40000fe03e01c000

def z898 : W := mkw 0x03f77ffffc0e4000 0x01fbbffffe072000 0xfafffffffc0c0000 0xfd7ffffffe060000

def z899 : W := mkw 0xe2f77ffffc009f3d 0x717bbffffe004f9e 0xfefffffffc001f3e 0xff7ffffffe000f9f

def z900 : W := mkw 0x02f75dbf78000000 0x017baedfbc000000 0xfaffff3ff0000000 0xfd7fff9ff8000000

def z901 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0x00000000037c6000 0x0000000001be3000

def z902 : W := mkw 0x22f75cbb3800090d 0x117bae5d9c000486 0x12ff983030001818 0x097fcc1818000c0c

def z903 : W := mkw 0x0128940003ff6000 0x00944a0001ffb000 0x81001f0003ffe001 0x40800f8001fff000

def z904 : W := mkw 0x205dc03b1be01d8d 0x902ee01d8df00ec6 0x7effe03fb3f01fd9 0xbf7ff01fd9f80fec

def z905 : W := mkw 0x00d76afb00000000 0x006bb57d80000000 0x7affe0ff80000000 0xbd7ff07fc0000000

def z906 : W := mkw 0x9255413ffc008262 0x492aa09ffe004131 0x7effe03ffcf007e7 0xbf7ff01ffe7803f3

def z907 : W := mkw 0x01eefec003ff7d81 0x80f77f6001ffbec0 0xfbffffc003fff801 0x7dffffe001fffc00

def z908 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfaffffc000f3e000 0x7d7fffe00079f000

def z909 : W := mkw 0x00e67ec000112000 0x00733f6000089000 0xfaffffc000b38000 0x7d7fffe00059c000

def z910 : W := mkw 0x50383668a69b3452 0x281c1b34534d9a29 0x527878f3bf7c79de 0x293c3c79dfbe3cef

def z911 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfffffffffcb386e1 0xfffffffffe59c370

def z912 : W := mkw 0x02f77ffffc0a0000 0x017bbffffe050000 0xfbfffffffc0f8000 0xfdfffffffe07c000

def z913 : W := mkw 0x01e6fec0015f6000 0x00f37f6000afb000 0xfbffffc0034fe001 0x7dffffe001a7f000

def z914 : W := mkw 0x01e67ec0001b2000 0x00f33f60000d9000 0xfaffffc000038000 0x7d7fffe00001c000

def z915 : W := mkw 0x00e65c8000000000 0x00732e4000000000 0x7afff80000000000 0x3d7ffc0000000000

def z916 : W := mkw 0xc2f75dbf78009630 0x617baedfbc004b18 0x16ff983c70001e38 0x8b7fcc1e38000f1c

def z917 : W := mkw 0x0044400000000000 0x0022200000000000 0x7affe00000f00001 0x3d7ff00000780000

def z918 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xffffffcfcfffe7e7 0xffffffe7e7fff3f3

def z919 : W := mkw 0x2008800003e45d8d 0x9004400001f22ec6 0x0400000003f07fc7 0x0200000001f83fe3

def z920 : W := mkw 0x0008a24003f13d81 0x8004512001f89ec0 0xed0067c003f3ffc1 0x768033e001f9ffe0

def z921 : W := mkw 0x03f77ffffc312000 0x01fbbffffe189000 0xfafffffffc300000 0xfd7ffffffe180000

def z922 : W := mkw 0x02f77efb38112000 0x017bbf7d9c089000 0xfbfffff030f3e001 0x7dfffff81879f000

def z923 : W := mkw 0x004dc01303e00981 0x8026e00981f004c0 0x7effe00f83f007c1 0xbf7ff007c1f803e0

def z924 : W := mkw 0x01e6fec001756000 0x00f37f6000bab000 0xfbffffc000f3e001 0x7dffffe00079f000

def z925 : W := mkw 0x0011227b00113d81 0x8008913d80089ec0 0xed0067ff80f3ffc1 0xf68033ffc079ffe0

def z926 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xd2fffff3fc000000 0x697ffff9fe000000

def z927 : W := mkw 0x0044400000000000 0x0022200000000000 0x7effe00f80f007c1 0xbf7ff007c07803e0

def z928 : W := mkw 0xc008800003ea9fb1 0xe004400001f54fd8 0x0400000003f39fc1 0x0200000001f9cfe0

def z929 : W := mkw 0xd038152ce68a9672 0x681c0a9673454b39 0xff781fffffcfffff 0xffbc0fffffe7ffff

def z930 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0x9900180003ffe001 0x4c800c0001fff000

def z931 : W := mkw 0x01eefec103ff6080 0x80f77f6081ffb040 0xfbffffc183ffe0c1 0x7dffffe0c1fff060

def z932 : W := mkw 0x02f5777fe4000000 0x017abbbff2000000 0x62ffe70f80000000 0x317ff387c0000000

def z933 : W := mkw 0x205dc03b03e01d8d 0x902ee01d81f00ec6 0x7effe03f83f01fff 0xbf7ff01fc1f80fff

def z934 : W := mkw 0x200308921804400c 0x100184490c022006 0xdd8798f27f0c783f 0xeec3cc793f863c1f

def z935 : W := mkw 0x91eedd84c7eec262 0x48f76ec263f76131 0x16ff980fcf0c07e6 0x8b7fcc07e78603f3

def z936 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfafffffffcf3e7c6 0xfd7ffffffe79f3e3

def z937 : W := mkw 0x02e65c8038000000 0x01732e401c000000 0x12ff980030000000 0x097fcc0018000000

def z938 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xfd007fcfcfffe7e7 0xfe803fe7e7fff3f3

def z939 : W := mkw 0x0044400000000000 0x0022200000000000 0x7affe00f80000000 0xbd7ff007c0000000

def z940 : W := mkw 0x0008800003ea1d81 0x8004400001f50ec0 0x0500000003ff9fc1 0x0280000001ffcfe0

def z941 : W := mkw 0x005748bb18000000 0x002ba45d8c000000 0x7afff83fb0000000 0xbd7ffc1fd8000000

def z942 : W := mkw 0x00e67ec084000000 0x00733f6042000000 0xfaffffc38c000000 0x7d7fffe1c6000000

def z943 : W := mkw 0x0075543b20000000 0x003aaa1d90000000 0x7afff83fb0000000 0xbd7ffc1fd8000000

def z944 : W := mkw 0x01c66ac000156000 0x00e33560000ab000 0x4087e0c000006000 0x2043f06000003000

def z945 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0xfaffffc000f00001 0x7d7fffe000780000

def z946 : W := mkw 0x01aabec003ff7d81 0x80d55f6001ffbec0 0x85001fc003ffffc1 0x42800fe001ffffe0

def z947 : W := mkw 0x01eedc8003ee4000 0x00f76e4001f72000 0x93ff9f00030f8000 0x49ffcf800187c000

def z948 : W := mkw 0x00f67fec60000000 0x007b3ff630000000 0xfaffffcc00000000 0x7d7fffe600000000

def z949 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfafffffffc406106 0xfd7ffffffe203083

def z950 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x7efff83fb3fc1fd9 0xbf7ffc1fd9fe0fec

def z951 : W := mkw 0xd211013ffc009672 0x6908809ffe004b39 0x0400003ffc001ffe 0x8200001ffe000fff

def z952 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0xfaffffc24c000000 0xfd7fffe126000000

def z953 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x0000000000f007c0 0x00000000007803e0

def z954 : W := mkw 0x2008800003e45d8d 0x9004400001f22ec6 0x05000000034c793f 0x0280000001a63c9f

def z955 : W := mkw 0xc3f77ffffc1fe230 0x61fbbffffe0ff118 0xfbfffffffc0fe038 0xfdfffffffe07f01c

def z956 : W := mkw 0xc00b08921a8a9630 0x600584490d454b18 0xdd8798f27f8f9e39 0xeec3cc793fc7cf1c

def z957 : W := mkw 0x00201400000a0000 0x00100a0000050000 0xbb781f00000f8000 0x5dbc0f800007c000

def z958 : W := mkw 0x001308ba18000000 0x0009845d0c000000 0xfaff98fe7c000000 0xfd7fcc7f3e000000

def z959 : W := mkw 0x005748bb00000000 0x002ba45d80000000 0xfafff8ff80000000 0xfd7ffc7fc0000000

def z960 : W := mkw 0x92f67fede411a262 0x497b3ff6f208d131 0xfbffffcd80f3e6c1 0x7dffffe6c079f360

def z961 : W := mkw 0x00f67ee800000000 0x007b3f7400000000 0xfafffffc00000000 0xfd7ffffe00000000

def z962 : W := mkw 0x205dc03b1be45d8d 0x902ee01d8df22ec6 0x7fffe03ffffc7fff 0xbffff01ffffe3fff

def z963 : W := mkw 0x01ee7ec002bb2000 0x00f73f60015d9000 0x62ffe7c000b38000 0x317ff3e00059c000

def z964 : W := mkw 0x205e48a91aa4548c 0x902f24548d522a46 0xa37878cdfcbc66fe 0x51bc3c66fe5e337f

def z965 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x2400600d83f01fc1 0x12003006c1f80fe0

def z966 : W := mkw 0x200388931944498d 0x9001c4498ca224c6 0xdd8798f3ff4c79ff 0xeec3cc79ffa63cff

def z967 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xffffffffff4c793f 0xffffffffffa63c9f

def z968 : W := mkw 0x00e67ec000112000 0x00733f6000089000 0xfaffffc000706000 0x7d7fffe000383000

def z969 : W := mkw 0x0046488000000000 0x0023244000000000 0xfafff8c000000000 0x7d7ffc6000000000

def z970 : W := mkw 0xb2f77ffffc11ab6f 0x597bbffffe08d5b7 0xfffffffffcf3ffff 0xfffffffffe79ffff

def z971 : W := mkw 0x0055413fc4000000 0x002aa09fe2000000 0x7affe03fcc000000 0xbd7ff01fe6000000

def z972 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0xdfff98f27c406127 0xefffcc793e203093

def z973 : W := mkw 0x41eefec003ff7410 0x20f77f6001ffba08 0xfbffffc003fff819 0x7dffffe001fffc0c

def z974 : W := mkw 0x90e67fc4c411a262 0x48733fe26208d131 0xfbffffc04c03e026 0x7dffffe02601f013

def z975 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0xfafff83ff0000000 0xfd7ffc1ff8000000

def z976 : W := mkw 0x12f77ffffc112042 0x097bbffffe089021 0xfbfffffffcf3e1c7 0xfdfffffffe79f0e3

def z977 : W := mkw 0x02f5777ffc000000 0x017abbbffe000000 0x7affe73ffc000000 0xbd7ff39ffe000000

def z978 : W := mkw 0x02aabfc4ffe01d81 0x81555fe27ff00ec0 0x84001fc07ff01fc1 0x42000fe03ff80fe0

def z979 : W := mkw 0x0108800003fb3d81 0x8084400001fd9ec0 0x0400000003f39fc1 0x0200000001f9cfe0

def z980 : W := mkw 0x00e77ed218000000 0x0073bf690c000000 0xfaffffc20c000000 0x7d7fffe106000000

def z981 : W := mkw 0x200288801944400c 0x100144400ca22006 0xdd8798f07f4c783f 0xeec3cc783fa63c1f

def z982 : W := mkw 0x91e67fc4c41fe262 0x48f33fe2620ff131 0xfbffffcfcc0fe026 0xfdffffe7e607f013

def z983 : W := mkw 0xc2f77ffffc0a8230 0x617bbffffe054118 0xfafffffffc038000 0xfd7ffffffe01c000

def z984 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfffffffffc43e127 0xfffffffffe21f093

def z985 : W := mkw 0x2108800003ff600c 0x1084400001ffb006 0x0100000003ffe03f 0x0080000001fff01f

def z986 : W := mkw 0x01ecf64003fb2000 0x00f67b2001fd9000 0xfbffe7c003f3e001 0x7dfff3e001f9f000

def z987 : W := mkw 0x0044624000000000 0x0022312000000000 0xfaffe7c000000000 0x7d7ff3e000000000

def z988 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfffffffffc03e7e6 0xfffffffffe01f3f3

def z989 : W := mkw 0x21e77ed2181f600c 0x10f3bf690c0fb006 0xfbfffff27c0fe03e 0xfdfffff93e07f01f

def z990 : W := mkw 0x92f5777fe411a262 0x497abbbff208d131 0x7effe73f80f387c1 0xbf7ff39fc079c3e0

def z991 : W := mkw 0x9008a344c7f1bfe3 0xc80451a263f8dff1 0x850007c04ff3ffe7 0x428003e027f9fff3

def z992 : W := mkw 0xc011013e60009f31 0x6008809f30004f98 0x0400003e70001f38 0x8200001f38000f9c

def z993 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfbfffffffcf3e6c1 0xfdfffffffe79f360

def z994 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x0500000003f07fe7 0x0280000001f83ff3

def z995 : W := mkw 0x02f77efb38000000 0x017bbf7d9c000000 0x92ff9ff030000000 0x497fcff818000000

def z996 : W := mkw 0x9075777fe411a262 0x483abbbff208d131 0xfffffffffcf3e7e7 0xfffffffffe79f3f3

def z997 : W := mkw 0x02f77efbbc000000 0x017bbf7dde000000 0x42ffe0c38c000000 0x217ff061c6000000

def z998 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xebffe7c000f3e001 0x75fff3e00079f000

def z999 : W := mkw 0xe008800003cedf3d 0x7004400001e76f9e 0x05000000038f9e39 0x0280000001c7cf1c

def z1000 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0x12ff9f3030000000 0x097fcf9818000000

def z1001 : W := mkw 0x005d403b02a01480 0x802ea01d81500a40 0x7effe03f80f007c1 0xbf7ff01fc07803e0

def z1002 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xeaffe7cfcc000000 0xf57ff3e7e6000000

def z1003 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xbf781f3c73ff9ff9 0xdfbc0f9e39ffcffc

def z1004 : W := mkw 0xc018812c63e09fb1 0xe00c409631f04fd8 0x0400003c73f01ff9 0x8200001e39f80ffc

def z1005 : W := mkw 0xc2f77ffffc0a8230 0x617bbffffe054118 0xfffffffffc8f8639 0xfffffffffe47c31c

def z1006 : W := mkw 0x0008800003e00000 0x0004400001f00000 0x6c00600f83f007c1 0xb6003007c1f803e0

def z1007 : W := mkw 0x02f77ffffc112000 0x017bbffffe089000 0xfafffffffcb38000 0xfd7ffffffe59c000

def z1008 : W := mkw 0x01eefec01bff6000 0x00f77f600dffb000 0xfbffffc07fffe001 0x7dffffe03ffff000

def z1009 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xbf781ffc7f8ffe3f 0xdfbc0ffe3fc7ff1f

def z1010 : W := mkw 0x00f77efb00000000 0x007bbf7d80000000 0xfafffff000000000 0x7d7ffff800000000

def z1011 : W := mkw 0x0011003b00000000 0x0008801d80000000 0x0400003f800007c0 0x8200001fc00003e0

def z1012 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfefffffffc400101 0xff7ffffffe200080

def z1013 : W := mkw 0xd038152c628a9672 0x681c0a9631454b39 0xbf781f3c738f9fff 0xdfbc0f9e39c7cfff

def z1014 : W := mkw 0x2057c8bb1944490d 0x102be45d8ca22486 0xfffff8fffffc7fff 0xfffffc7ffffe3fff

def z1015 : W := mkw 0x40381428228a1410 0x201c0a1411450a08 0x93781f30330f9818 0x49bc0f981987cc0c

def z1016 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x92ff98f07c000000 0x497fcc783e000000

def z1017 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0x32ffff3db0b386c0 0x197fff9ed859c360

def z1018 : W := mkw 0x82f77ffffc008220 0x417bbffffe004110 0xfafffffffc838600 0xfd7ffffffe41c300

def z1019 : W := mkw 0x02c76ad39c000000 0x0163b569ce000000 0x7affe0c38c000000 0x3d7ff061c6000000

def z1020 : W := mkw 0x02f75cbb38001d81 0x817bae5d9c000ec0 0x16ff983fb0001fc0 0x8b7fcc1fd8000fe0

def z1021 : W := mkw 0x00c66ac000000000 0x0063356000000000 0x7affe0c000000000 0x3d7ff06000000000

def z1022 : W := mkw 0x00f5767b00000000 0x007abb3d80000000 0x7affe73f80000000 0xbd7ff39fc0000000

def z1023 : W := mkw 0xc1d6ebec6175f630 0x60eb75f630bafb18 0x4487e0fc70707e38 0xa243f07e38383f1c

def z1024 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfbffffcf83ffe001 0xfdffffe7c1fff000

def z1025 : W := mkw 0x0008800003e45d81 0x8004400001f22ec0 0x0500000003fc7fc1 0x0280000001fe3fe0

def z1026 : W := mkw 0x0055403b00001480 0x802aa01d80000a40 0x7affe03f800006c0 0xbd7ff01fc0000360

def z1027 : W := mkw 0xc128950463ffe230 0x60944a8231fff118 0x81001f0073ffe039 0x40800f8039fff01c

def z1028 : W := mkw 0x22f77ffffc00090d 0x117bbffffe000486 0xfffffffffc40793f 0xfffffffffe203c9f

def z1029 : W := mkw 0x2108800003ee490d 0x1084400001f72486 0x05000000034c793f 0x0280000001a63c9f

def z1030 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x7affe03f80b006c0 0xbd7ff01fc0580360

def z1031 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xff787f3ff38f9e39 0xffbc3f9ff9c7cf1c

def z1032 : W := mkw 0x00f67fece4000000 0x007b3ff672000000 0xfafffffffc000000 0xfd7ffffffe000000

def z1033 : W := mkw 0xc108800003eed630 0x6084400001f76b18 0x05000000038f9e39 0x0280000001c7cf1c

def z1034 : W := mkw 0x0047489218000000 0x0023a4490c000000 0xfafff8f27c000000 0xfd7ffc793e000000

def z1035 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xed0067cfcfffffff 0xf68033e7e7ffffff

def z1036 : W := mkw 0x00281400028a0000 0x00140a0001450000 0xbb781f30338f9819 0x5dbc0f9819c7cc0c

def z1037 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0x72ffffc003ffe000 0x397fffe001fff000

def z1038 : W := mkw 0x02e77fd7fc000000 0x0173bfebfe000000 0xfaffffc3fc000000 0x7d7fffe1fe000000

def z1039 : W := mkw 0xc011013e78009630 0x6008809f3c004b18 0x0400003e7c001e38 0x8200001f3e000f1c

def z1040 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfafffffffc7001c0 0xfd7ffffffe3800e0

def z1041 : W := mkw 0x2108a24003ff690d 0x1084512001ffb486 0xed0067c24ffff93f 0xf68033e127fffc9f

def z1042 : W := mkw 0x92e77fd7dc11a262 0x4973bfebee08d131 0xffffffcfccf3e7e7 0xffffffe7e679f3f3

def z1043 : W := mkw 0x8211013ffc008220 0x4108809ffe004110 0x0400003ffc000620 0x8200001ffe000310

def z1044 : W := mkw 0x9019a37fc7f1bfe3 0xc80cd1bfe3f8dff1 0xed0067ffcff3ffe7 0xf68033ffe7f9fff3

def z1045 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xbb781f30738f9839 0x5dbc0f9839c7cc1c

def z1046 : W := mkw 0x01ee7ec002bb2000 0x00f73f60015d9000 0xfbffffc000f3e001 0x7dffffe00079f000

def z1047 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x958798f27f0c793e 0xcac3cc793f863c9f

def z1048 : W := mkw 0x0108800003ff7d81 0x8084400001ffbec0 0x0100000003fff801 0x0080000001fffc00

def z1049 : W := mkw 0x0055c03b01400901 0x002ae01d80a00480 0x7effe03f83f01fc1 0xbf7ff01fc1f80fe0

def z1050 : W := mkw 0xc108800003fff630 0x6084400001fffb18 0x0100000003ffe601 0x0080000001fff300

def z1051 : W := mkw 0x9008800003f1a262 0x4804400001f8d131 0x0500000003f3e7e7 0x0280000001f9f3f3

def z1052 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xbf781f3ff38f9ff9 0xdfbc0f9ff9c7cffc

def z1053 : W := mkw 0x21eefec003ff690d 0x10f77f6001ffb486 0xfbffffc003fff819 0x7dffffe001fffc0c

def z1054 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x2c00000c03f01fc1 0x9600000601f80fe0

def z1055 : W := mkw 0x005dc03b1be01d81 0x802ee01d8df00ec0 0x7effe03ffff01fc1 0xbf7ff01ffff80fe0

def z1056 : W := mkw 0x02f77efb38000000 0x017bbf7d9c000000 0x52fff8f030000000 0x297ffc7818000000

def z1057 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x0400000003001fc0 0x0200000001800fe0

def z1058 : W := mkw 0x02d76afb9c000000 0x016bb57dce000000 0x52ffe0f38c000000 0x297ff079c6000000

def z1059 : W := mkw 0x93f77ffffc1fe262 0x49fbbffffe0ff131 0xfbfffffffc0fe026 0xfdfffffffe07f013

def z1060 : W := mkw 0xd1fc776ce6bbb672 0x68fe3bb6735ddb39 0x2278670d80b386c0 0x113c3386c059c360

def z1061 : W := mkw 0xc2cf6ad39e8a9630 0x6167b569cf454b18 0x4587e0c38f8f9e39 0x22c3f061c7c7cf1c

def z1062 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x0000000003b01ec0 0x0000000001d80f60

def z1063 : W := mkw 0x205dc03b1be01d8d 0x902ee01d8df00ec6 0xffffe0fffff07fff 0xfffff07ffff83fff

def z1064 : W := mkw 0x005748bb18000000 0x002ba45d8c000000 0x7affe0ff8c000000 0xbd7ff07fc6000000

def z1065 : W := mkw 0xc2f77ffffc008230 0x617bbffffe004118 0xfafffffffc000038 0xfd7ffffffe00001c

def z1066 : W := mkw 0x02d76bffdc000000 0x016bb5ffee000000 0xfaffe7ffcc000000 0xfd7ff3ffe6000000

def z1067 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0xfeffe0ffcff01fc1 0xff7ff07fe7f80fe0

def z1068 : W := mkw 0xc2f77ffffc009630 0x617bbffffe004b18 0xfffffffffc839e39 0xfffffffffe41cf1c

def z1069 : W := mkw 0x0055403b00001d81 0x802aa01d80000ec0 0x16ff803f80001fc0 0x8b7fc01fc0000fe0

def z1070 : W := mkw 0x02f5777fe4000000 0x017abbbff2000000 0xfaffe7ffcc000000 0xfd7ff3ffe6000000

def z1071 : W := mkw 0xd2f77ffffc009672 0x697bbffffe004b39 0xfefffffffc001ffe 0xff7ffffffe000fff

def z1072 : W := mkw 0xc008800003ca9f31 0x6004400001e54f98 0x0500000003cf9f39 0x0280000001e7cf9c

def z1073 : W := mkw 0x4008800003ea1d91 0xa004400001f50ec8 0x00000000030c1818 0x0000000001860c0c

def z1074 : W := mkw 0xe008810443cedf3d 0x7004408221e76f9e 0xed0007ce4fcfff3f 0xf68003e727e7ff9f

def z1075 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xb3781f3c738f9e38 0x59bc0f9e39c7cf1c

def z1076 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0x62ffe7fffc000000 0xb17ff3fffe000000

def z1077 : W := mkw 0x0019803b03e01d81 0x800cc01d81f00ec0 0x0400003003f01fc1 0x0200001801f80fe0

def z1078 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x5aff983230000000 0xad7fcc1918000000

def z1079 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x36ffe03d83f01fc1 0x1b7ff01ec1f80fe0

def z1080 : W := mkw 0x2108800003ff690d 0x1084400001ffb486 0x0100000003ffe107 0x0080000001fff083

def z1081 : W := mkw 0x21eefec003ff690d 0x10f77f6001ffb486 0xfffffff073fff93f 0xfffffff839fffc9f

def z1082 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xbbffff0003bf8001 0x5dffff8001dfc000

def z1083 : W := mkw 0x02e77fd6fc000000 0x0173bfeb7e000000 0xfafffff27c000000 0xfd7ffff93e000000

def z1084 : W := mkw 0x00c66ac000112000 0x0063356000089000 0x4087e0c000706000 0x2043f06000383000

def z1085 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x7effe03f80400101 0xbf7ff01fc0200080

def z1086 : W := mkw 0x90000104c4008262 0x4800008262004131 0x0400000fccf007e7 0x82000007e67803f3

def z1087 : W := mkw 0xc211013ffc008230 0x6108809ffe004118 0x0000003ffc000038 0x8000001ffe00001c

def z1088 : W := mkw 0x22f77ffffc00000c 0x117bbffffe000006 0xfafffffffc00003e 0xfd7ffffffe00001f

def z1089 : W := mkw 0x02f67fecfc000000 0x017b3ff67e000000 0xfafffffc7c000000 0xfd7ffffe3e000000

def z1090 : W := mkw 0xe008800003eedfbd 0xf004400001f76fde 0x0500000003ffffff 0x0280000001ffffff

def z1091 : W := mkw 0xc0281504628a9630 0x60140a8231454b18 0x81001f00730f9838 0x40800f803987cc1c

def z1092 : W := mkw 0x205dc03b03e45d8d 0x902ee01d81f22ec6 0x7effe03f83fc1fd9 0xbf7ff01fc1fe0fec

def z1093 : W := mkw 0x02e75c9318000000 0x0173ae498c000000 0x12ff980000000000 0x097fcc0000000000

def z1094 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x7affe03000000000 0x3d7ff01800000000

def z1095 : W := mkw 0x9008a344c7f1bfe3 0xc80451a263f8dff1 0x2400670d83f39fc1 0x12003386c1f9cfe0

def z1096 : W := mkw 0x02f77efbbc000000 0x017bbf7dde000000 0x12fff831b0000000 0x097ffc18d8000000

def z1097 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0x52fff8fffc000000 0xa97ffc7ffe000000

def z1098 : W := mkw 0x005dc03b03e01480 0x802ee01d81f00a40 0x7affe03f83f006c1 0xbd7ff01fc1f80360

def z1099 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0x63ffe7c003ffe001 0x31fff3e001fff000

def z1100 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xbaffff3df0000000 0xdd7fff9ef8000000

def z1101 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x0500000003fc1ff9 0x0280000001fe0ffc

def z1102 : W := mkw 0xc055413f60009630 0x602aa09fb0004b18 0x7effe03ff0001e38 0xbf7ff01ff8000f1c

def z1103 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x0400000003401901 0x0200000001a00c80

def z1104 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x32fff83db0000000 0x197ffc1ed8000000

def z1105 : W := mkw 0x02e67fc4fc000000 0x01733fe27e000000 0x92ff9fc07c000000 0x497fcfe03e000000

def z1106 : W := mkw 0xf011013efc009f7f 0x7808809f7e004fbf 0x0400003ffc001ffe 0x8200001ffe000fff

def z1107 : W := mkw 0x01ee7ec0029f6000 0x00f73f60014fb000 0xfbffffc0038fe001 0x7dffffe001c7f000

def z1108 : W := mkw 0x0055627b00000000 0x002ab13d80000000 0xfaffe7ff80000000 0xfd7ff3ffc0000000

def z1109 : W := mkw 0x0002888001444000 0x0001444000a22000 0xdd8798f27f4c793f 0xeec3cc793fa63c9f

def z1110 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xefffe7cfccf3e7e7 0xf7fff3e7e679f3f3

def z1111 : W := mkw 0x01ec764002bb2000 0x00f63b20015d9000 0x7affe70000b38000 0x3d7ff3800059c000

def z1112 : W := mkw 0x006c5400028a0000 0x00362a0001450000 0xfbffff00038f8001 0x7dffff8001c7c000

def z1113 : W := mkw 0x0108800003ff7400 0x0084400001ffba00 0x0500000003fffe01 0x0280000001ffff00

def z1114 : W := mkw 0x42f75cbb380a0010 0x217bae5d9c050008 0x12ff9830300c0018 0x097fcc181806000c

def z1115 : W := mkw 0x005dc03b03e00000 0x002ee01d81f00000 0x7effe03f83f007c1 0xbf7ff01fc1f803e0

def z1116 : W := mkw 0x00fffefb03f13d81 0x807fff7d81f89ec0 0xffffffff83f3ffc1 0xffffffffc1f9ffe0

def z1117 : W := mkw 0x40381428228a1410 0x201c0a1411450a08 0x32781f30338f9818 0x193c0f9819c7cc0c

def z1118 : W := mkw 0x00e4764000000000 0x00723b2000000000 0x7affe70000000000 0x3d7ff38000000000

def z1119 : W := mkw 0x9108800003ffe262 0x4884400001fff131 0x0100000003ffe027 0x0080000001fff013

def z1120 : W := mkw 0x91e67fc4c41fe262 0x48f33fe2620ff131 0xffffffcfccffe7e7 0xffffffe7e67ff3f3

def z1121 : W := mkw 0x9055637fc411a262 0x482ab1bfe208d131 0x7affe73f80b386c0 0xbd7ff39fc059c360

def z1122 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0x7affe7c003f3e001 0x3d7ff3e001f9f000

def z1123 : W := mkw 0x002a9c8003ce4000 0x00154e4001e72000 0xbbff9f00038f8001 0x5dffcf8001c7c000

def z1124 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0x6d00600f83ffe7c1 0xb6803007c1fff3e0

def z1125 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0xa900070003ffe001 0x5480038001fff000

def z1126 : W := mkw 0xc008800003ea9630 0x6004400001f54b18 0x0500000003ff9e39 0x0280000001ffcf1c

def z1127 : W := mkw 0x9211013ffc009fe3 0xc908809ffe004ff1 0x0400003ffc001fe6 0x8200001ffe000ff3

def z1128 : W := mkw 0x00ee7ec0029b2000 0x00773f60014d9000 0xfbffffc003ffe001 0x7dffffe001fff000

def z1129 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x3effe03d83b01ec1 0x9f7ff01ec1d80f60

def z1130 : W := mkw 0x9055637fc4009fe3 0xc82ab1bfe2004ff1 0xfeffe7ffcc001fe6 0xff7ff3ffe6000ff3

def z1131 : W := mkw 0x200288801944490d 0x100144400ca22486 0x810018c07f0c783e 0x40800c603f863c1f

def z1132 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfffffffffc83e627 0xfffffffffe41f313

def z1133 : W := mkw 0x21eefec003ff690d 0x10f77f6001ffb486 0xffffffc24ffff93f 0xffffffe127fffc9f

def z1134 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x36781f3c738f9e38 0x9b3c0f9e39c7cf1c

def z1135 : W := mkw 0x01aabec003df6000 0x00d55f6001efb000 0xfbff9fc003cfe001 0x7dffcfe001e7f000

def z1136 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfbfffff033fff819 0x7dfffff819fffc0c

def z1137 : W := mkw 0x02f65ca920000000 0x017b2e5490000000 0x12ff980000000000 0x097fcc0000000000

def z1138 : W := mkw 0x03eefec187ff6000 0x01f77f60c3ffb000 0xfbffffc183ffe001 0x7dffffe0c1fff000

def z1139 : W := mkw 0x6008800003ce5d1d 0x3004400001e72e8e 0x05000000034c793f 0x0280000001a63c9f

def z1140 : W := mkw 0x31c7ead29d75694f 0x18e3f5694ebab4a7 0x4087e0c38c7061c6 0x2043f061c63830e3

def z1141 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0x0500000003ffe127 0x0280000001fff093

def z1142 : W := mkw 0x02f75dbf78000000 0x017baedfbc000000 0x32ff9f3c30000000 0x197fcf9e18000000

def z1143 : W := mkw 0x01aabec003ff6000 0x00d55f6001ffb000 0xe9007fc003ffe001 0x74803fe001fff000

def z1144 : W := mkw 0x03eefec03bff6000 0x01f77f601dffb000 0xfbffffc033ffe001 0x7dffffe019fff000

def z1145 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xed007fcffcffe7ff 0xf6803fe7fe7ff3ff

def z1146 : W := mkw 0x00a23ec000112000 0x00511f6000089000 0x81001fc00003e000 0x40800fe00001f000

def z1147 : W := mkw 0x00381428028a1400 0x001c0a1401450a00 0xbf781f3c738f9e39 0xdfbc0f9e39c7cf1c

def z1148 : W := mkw 0x0002088000000000 0x0001044000000000 0xd98798c000406001 0x6cc3cc6000203000

def z1149 : W := mkw 0x00e6fec001556000 0x00737f6000aab000 0xfbffffc003ffe001 0x7dffffe001fff000

def z1150 : W := mkw 0x004cc00003e00000 0x0026600001f00000 0xfbffe70003f38001 0x7dfff38001f9c000

def z1151 : W := mkw 0x0055c03b01600981 0x802ae01d80b004c0 0x7effe03f80f007c1 0xbf7ff01fc07803e0

def z1152 : W := mkw 0x02f75dbffc000000 0x017baedffe000000 0x12ff98307c000000 0x097fcc183e000000

def z1153 : W := mkw 0x12f77ffffc112042 0x097bbffffe089021 0xfafffffffc006006 0xfd7ffffffe003003

def z1154 : W := mkw 0x01fffefb03ff6000 0x00ffff7d81ffb000 0xffffffff83ffe7c1 0xffffffffc1fff3e0

def z1155 : W := mkw 0x2008800003e01d8d 0x9004400001f00ec6 0x0400000003f01fff 0x0200000001f80fff

def z1156 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfffffffffc000021 0xfffffffffe000010

def z1157 : W := mkw 0xb2a23fc4fc15e26e 0x59511fe27e0af137 0x81001fc07c0fe03e 0x40800fe03e07f01f

def z1158 : W := mkw 0x0019803a03c01d01 0x000cc01d01e00e80 0x7effe03f83f01fc1 0xbf7ff01fc1f80fe0

def z1159 : W := mkw 0xd0002344e411a272 0x680011a27208d139 0xed0067cffcf3e7ff 0xf68033e7fe79f3ff

def z1160 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x0400000f83f01fc1 0x82000007c1f80fe0

def z1161 : W := mkw 0x005d403b02a01480 0x802ea01d81500a40 0x32ffe03d80b006c0 0x197ff01ec0580360

def z1162 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x7effe03f83001801 0xbf7ff01fc1800c00

def z1163 : W := mkw 0x2030952c6144490d 0x10184a9630a22486 0xbf781f3c734c793f 0xdfbc0f9e39a63c9f

def z1164 : W := mkw 0x92f75cbb3811a262 0x497bae5d9c08d131 0x17ff983030f3e7e7 0x0bffcc181879f3f3

def z1165 : W := mkw 0x01eefec003ff7480 0x80f77f6001ffba40 0xfbffffc003ffe6c1 0x7dffffe001fff360

def z1166 : W := mkw 0x01ecf64003fb2000 0x00f67b2001fd9000 0x32ffe70003b38000 0x197ff38001d9c000

def z1167 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x7effe0ff8ff07fc7 0xbf7ff07fc7f83fe3

def z1168 : W := mkw 0x01eedc8003ee4000 0x00f76e4001f72000 0xfbff9fc003cfe001 0x7dffcfe001e7f000

def z1169 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xdd87f8f3ff7c79ff 0xeec3fc79ffbe3cff

def z1170 : W := mkw 0x02f77efb38000000 0x017bbf7d9c000000 0xfafffff27c000000 0xfd7ffff93e000000

def z1171 : W := mkw 0x22f77ffffc00090d 0x117bbffffe000486 0xfafffffffc000106 0xfd7ffffffe000083

def z1172 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xdd8798f27ffc7fff 0xeec3cc793ffe3fff

def z1173 : W := mkw 0x0054402900000000 0x002a201480000000 0x7affe00d80000000 0x3d7ff006c0000000

def z1174 : W := mkw 0x0108800003ff7480 0x8084400001ffba40 0x0100000003ffe6c1 0x0080000001fff360

def z1175 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0x22ffe70000b38000 0x117ff3800059c000

def z1176 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xbf781f3e7f8f9f3f 0xdfbc0f9f3fc7cf9f

def z1177 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0xc90000c003ffe001 0x6480006001fff000

def z1178 : W := mkw 0x02331dbffc000000 0x01198edffe000000 0xfaff9ffffc000000 0xfd7fcffffe000000

def z1179 : W := mkw 0x02f77fff78000000 0x017bbfffbc000000 0xfafffffc70000000 0xfd7ffffe38000000

def z1180 : W := mkw 0x025dc03b3be01d81 0x812ee01d9df00ec0 0x7effe03fb3f01fc1 0xbf7ff01fd9f80fe0

def z1181 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x12ff9830330c1818 0x097fcc1819860c0c

def z1182 : W := mkw 0xc011013f60009fb1 0xe008809fb0004fd8 0x0400003f80001fc0 0x8200001fc0000fe0

def z1183 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x12781f30330f9818 0x093c0f981987cc0c

def z1184 : W := mkw 0x42f77ffffc001410 0x217bbffffe000a08 0xfafffffffc001818 0xfd7ffffffe000c0c

def z1185 : W := mkw 0x0028940003ca0000 0x00144a0001e50000 0xfbff9f0003cf8001 0x7dffcf8001e7c000

def z1186 : W := mkw 0x4108800003ee5410 0x2084400001f72a08 0x00000000030c1818 0x0000000001860c0c

def z1187 : W := mkw 0x0045401300000000 0x0022a00980000000 0x4087e003807001c0 0x2043f001c03800e0

def z1188 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x22ffe00d80b006c0 0x117ff006c0580360

def z1189 : W := mkw 0x0008800003e00000 0x0004400001f00000 0x6800600003f00001 0x3400300001f80000

def z1190 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0xcd0000c24ff07fe7 0xe680006127f83ff3

def z1191 : W := mkw 0x006cf64003fb2000 0x00367b2001fd9000 0xfbffffc003ffe001 0x7dffffe001fff000

def z1192 : W := mkw 0x01e67ec000156000 0x00f33f60000ab000 0xfaffffc000006000 0x7d7fffe000003000

def z1193 : W := mkw 0x00f65ca820000000 0x007b2e5410000000 0x12ff983030000000 0x097fcc1818000000

def z1194 : W := mkw 0x205dc03b1be01d8d 0x902ee01d8df00ec6 0xfffff83ffffc1fff 0xfffffc1ffffe0fff

def z1195 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xfd0067ffcff3ffe7 0xfe8033ffe7f9fff3

def z1196 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xbf787f3df3bf9ef9 0xdfbc3f9ef9dfcf7c

def z1197 : W := mkw 0xc01289ac6144d630 0x600944d630a26b18 0xdd8798fc734c7e39 0xeec3cc7e39a63f1c

def z1198 : W := mkw 0x92f77ffffc11bfe3 0xc97bbffffe08dff1 0xfffffffffcf3ffe7 0xfffffffffe79fff3

def z1199 : W := mkw 0x01ecf64003ff6000 0x00f67b2001ffb000 0x7bffe70003ffe001 0x3dfff38001fff000

def z1200 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x7affe03f80f00001 0xbd7ff01fc0780000

def z1201 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xd98798f27f0c783e 0xecc3cc793f863c1f

def z1202 : W := mkw 0x9008a344c7f1a262 0x480451a263f8d131 0xed0067cfcff3e7e7 0xf68033e7e7f9f3f3

def z1203 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x52ffe03380000000 0x297ff019c0000000

def z1204 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xfd879ff27fcff93f 0xfec3cff93fe7fc9f

def z1205 : W := mkw 0x01eefec003ff6901 0x00f77f6001ffb480 0xffffffc003fff901 0x7fffffe001fffc80

def z1206 : W := mkw 0x11eefec087ff6042 0x08f77f6043ffb021 0xfbffffc00fffe007 0x7dffffe007fff003

def z1207 : W := mkw 0x200180121944490d 0x1000c0090ca22486 0x040000327f0c193e 0x820000193f860c9f

def z1208 : W := mkw 0x2008800003c45d0d 0x1004400001e22e86 0x0500000003cc7f3f 0x0280000001e63f9f

def z1209 : W := mkw 0x00f77fffc4000000 0x007bbfffe2000000 0xfaffffffcc000000 0xfd7fffffe6000000

def z1210 : W := mkw 0xb008800003f5ffef 0xd804400001fafff7 0x0500000003ffffff 0x0280000001ffffff

def z1211 : W := mkw 0x0055637fc4000000 0x002ab1bfe2000000 0x7affe73f80000000 0xbd7ff39fc0000000

def z1212 : W := mkw 0x4108800003ff7410 0x2084400001ffba08 0x0100000003fff819 0x0080000001fffc0c

def z1213 : W := mkw 0x205dc03b1be01d8d 0x902ee01d8df00ec6 0x7effe03f8ff01fc7 0xbf7ff01fc7f80fe3

def z1214 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x0000000003f01801 0x0000000001f80c00

def z1215 : W := mkw 0x80e67fc440008220 0x40733fe220004110 0xffffffcc40838621 0xffffffe62041c310

def z1216 : W := mkw 0x22f77ffffc04400c 0x117bbffffe022006 0xfafffffffc0c0018 0xfd7ffffffe06000c

def z1217 : W := mkw 0x0019803b03e01d81 0x800cc01d81f00ec0 0x0000003003001800 0x0000001801800c00

def z1218 : W := mkw 0xc008810443ea9fb1 0xe004408221f54fd8 0xed00670fc3ff9ff9 0xf6803387e1ffcffc

def z1219 : W := mkw 0x1108a24087ff6042 0x0884512043ffb021 0x410060c38fffe1c7 0x20803061c7fff0e3

def z1220 : W := mkw 0x8055413f40008220 0x402aa09fa0004110 0xffffe73fc0838621 0xfffff39fe041c310

def z1221 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x9d00183073fc1ff9 0xce800c1839fe0ffc

def z1222 : W := mkw 0x0008800003e00901 0x0004400001f00480 0x0400000003f01901 0x0200000001f80c80

def z1223 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfbfffffffc006026 0xfdfffffffe003013

def z1224 : W := mkw 0xd038152ce68a9672 0x681c0a9673454b39 0xbf781f3df38f9ef9 0xdfbc0f9ef9c7cf7c

def z1225 : W := mkw 0x0075543b00000000 0x003aaa1d80000000 0xfaffff3f80000000 0xfd7fff9fc0000000

def z1226 : W := mkw 0x0031153e60000000 0x00188a9f30000000 0xfaff9f3e70000000 0xfd7fcf9f38000000

def z1227 : W := mkw 0x01aabec003ff6000 0x00d55f6001ffb000 0x81001fc0030fe000 0x40800fe00187f000

def z1228 : W := mkw 0x01cce24003ff6000 0x00e6712001ffb000 0x0100600003ffe001 0x0080300001fff000

def z1229 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xff781ffe7f8f9e39 0xffbc0fff3fc7cf1c

def z1230 : W := mkw 0x90002344c411a262 0x480011a26208d131 0x650067cf8cf3e7e7 0x328033e7c679f3f3

def z1231 : W := mkw 0x006cd40003ea0000 0x00366a0001f50000 0x7affe70003f38001 0x3d7ff38001f9c000

def z1232 : W := mkw 0x0074552c60000000 0x003a2a9630000000 0xfaffff3c70000000 0xfd7fff9e38000000

def z1233 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0x7affe7ff8c000000 0xbd7ff3ffc6000000

def z1234 : W := mkw 0x22f77ffffc04400c 0x117bbffffe022006 0xffffffffff0c783f 0xffffffffff863c1f

def z1235 : W := mkw 0x0054402900000000 0x002a201480000000 0x2278600d80b006c0 0x113c3006c0580360

def z1236 : W := mkw 0x80281504428a8220 0x40140a8221454110 0xbf781f3c738f9e39 0xdfbc0f9e39c7cf1c

def z1237 : W := mkw 0x0108800003f57d81 0x8084400001fabec0 0x0400000003f07fc1 0x0200000001f83fe0

def z1238 : W := mkw 0xb008a344c7f5ffef 0xd80451a263fafff7 0xed0067cfcfffffff 0xf68033e7e7ffffff

def z1239 : W := mkw 0x00e77ed218000000 0x0073bf690c000000 0xfafffff030000000 0x7d7ffff818000000

def z1240 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xb2fffffdfc000000 0x597ffffefe000000

def z1241 : W := mkw 0x0055403b00001d81 0x802aa01d80000ec0 0x12ff803000001800 0x097fc01800000c00

def z1242 : W := mkw 0xc118812c63fff630 0x608c409631fffb18 0x0500003c73fffe39 0x8280001e39ffff1c

def z1243 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xba781f3c738f9e18 0xdd3c0f9e39c7cf0c

def z1244 : W := mkw 0x91a23fc4c41fe262 0x48d11fe2620ff131 0x81001fc0000fe000 0x40800fe00007f000

def z1245 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0xfaffffcf80000000 0xfd7fffe7c0000000

def z1246 : W := mkw 0x0255413ffc000000 0x012aa09ffe000000 0x12ff803ffc000000 0x897fc01ffe000000

def z1247 : W := mkw 0x01ee7ec002bb2000 0x00f73f60015d9000 0x32ffff0000b38000 0x197fff800059c000

def z1248 : W := mkw 0x21c7ead21975690d 0x10e3f5690cbab486 0x4087e0c000706000 0x2043f06000383000

def z1249 : W := mkw 0x02e67ec09c000000 0x01733f604e000000 0xfaffffc00c000000 0x7d7fffe006000000

def z1250 : W := mkw 0x40381428228a1410 0x201c0a1411450a08 0xbf781f3c338f9e19 0xdfbc0f9e19c7cf0c

def z1251 : W := mkw 0x02f75cbb38001d81 0x817bae5d9c000ec0 0x12ff983030001800 0x097fcc1818000c00

def z1252 : W := mkw 0x02f5777fe4000000 0x017abbbff2000000 0xfaffff3ff0000000 0xfd7fff9ff8000000

def z1253 : W := mkw 0x01aa9c8003ee4000 0x00d54e4001f72000 0x00001800030c0000 0x00000c0001860000

def z1254 : W := mkw 0xe108800003ffff3d 0x7084400001ffff9e 0x0500000003ffff3f 0x0280000001ffff9f

def z1255 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x7affe03d83f01ec1 0x3d7ff01ec1f80f60

def z1256 : W := mkw 0x01f77efb001f6000 0x00fbbf7d800fb000 0xfbffffff800fe000 0xfdffffffc007f000

def z1257 : W := mkw 0x02f75cbbbc000000 0x017bae5dde000000 0x12ff9833bc000000 0x097fcc19de000000

def z1258 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfafffffffcf00001 0xfd7ffffffe780000

def z1259 : W := mkw 0x210a88801bff600c 0x108544400dffb006 0x810018c07fffe03f 0x40800c603ffff01f

def z1260 : W := mkw 0x92f77ffffc008262 0x497bbffffe004131 0xfffffffffc4067e7 0xfffffffffe2033f3

def z1261 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xffffffffffffffff 0xffffffffffffffff

def z1262 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0xfffffff0730c1839 0xfffffff839860c1c

def z1263 : W := mkw 0xd038152ce68a9672 0x681c0a9673454b39 0xff787f3fffff9fff 0xffbc3f9fffffcfff

def z1264 : W := mkw 0x02f75dbffc000000 0x017baedffe000000 0xbaff9f3ffc000000 0xdd7fcf9ffe000000

def z1265 : W := mkw 0x02f77ffffc112000 0x017bbffffe089000 0xfffffffffcf3e7c1 0xfffffffffe79f3e0

def z1266 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0x93ff9fc003ffe001 0x49ffcfe001fff000

def z1267 : W := mkw 0x02f75dbffc000000 0x017baedffe000000 0x12ff983db0000000 0x097fcc1ed8000000

def z1268 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x5aff803200000000 0xad7fc01900000000

def z1269 : W := mkw 0xc038152c62aa96b0 0xe01c0a9631554b58 0xbf781f3c73bf9ef9 0xdfbc0f9e39dfcf7c

def z1270 : W := mkw 0x92d76bffdc11a262 0x496bb5ffee08d131 0xffffe7ffccf3e7e7 0xfffff3ffe679f3f3

def z1271 : W := mkw 0x12f77efbbc112042 0x097bbf7dde089021 0x52fff8f3bc7061c6 0x297ffc79de3830e3

def z1272 : W := mkw 0x0018802803e01d81 0x800c401401f00ec0 0x0400003c03f01fc1 0x8200001e01f80fe0

def z1273 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0x0500000003ffe7c1 0x0280000001fff3e0

def z1274 : W := mkw 0x025749bffc000000 0x012ba4dffe000000 0xfafff8fffc000000 0xfd7ffc7ffe000000

def z1275 : W := mkw 0x02f77ffffc112000 0x017bbffffe089000 0xfafffffffc706000 0xfd7ffffffe383000

def z1276 : W := mkw 0x02f77ffffc001400 0x017bbffffe000a00 0xfefffffffc001e00 0xff7ffffffe000f00

def z1277 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xffffffc043ffe021 0xffffffe021fff010

def z1278 : W := mkw 0x01e6fec0017f6000 0x00f37f6000bfb000 0xfbffffc0007fe000 0x7dffffe0003ff000

def z1279 : W := mkw 0x2008800003e45d8d 0x9004400001f22ec6 0x0400000003fc1fd9 0x0200000001fe0fec

def z1280 : W := mkw 0x02f77efb38000000 0x017bbf7d9c000000 0xfaffffffb0000000 0xfd7fffffd8000000

def z1281 : W := mkw 0x93f77ffffc1fe262 0x49fbbffffe0ff131 0xfffffffffcffe7e7 0xfffffffffe7ff3f3

def z1282 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x62ffe00f80000000 0x317ff007c0000000

def z1283 : W := mkw 0x0054402800000000 0x002a201400000000 0x7affe03c00000000 0xbd7ff01e00000000

def z1284 : W := mkw 0x00e67fc4c4000000 0x00733fe262000000 0xfaffffc04c000000 0x7d7fffe026000000

def z1285 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfbffffc0030fe000 0x7dffffe00187f000

def z1286 : W := mkw 0x03eefec09fff6000 0x01f77f604fffb000 0xfbffffc00fffe001 0x7dffffe007fff000

def z1287 : W := mkw 0x21eefec003ff7d8d 0x90f77f6001ffbec6 0xffffffc003ffffff 0x7fffffe001ffffff

def z1288 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0xfeffffcf80f007c1 0xff7fffe7c07803e0

def z1289 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x36ffe03f83b01fc0 0x9b7ff01fc1d80fe0

def z1290 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0x62ffe7cf8cf3e7c6 0x317ff3e7c679f3e3

def z1291 : W := mkw 0x02f77efbbc000000 0x017bbf7dde000000 0xdafff8f3fc000000 0xed7ffc79fe000000

def z1292 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x6c00600003f01fc1 0x3600300001f80fe0

def z1293 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xfd007ffffcf3e7e7 0xfe803ffffe79f3f3

def z1294 : W := mkw 0xd008800003fbbff3 0xe804400001fddff9 0x0500000003ffffff 0x0280000001ffffff

def z1295 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xe10067cfccf3e7e6 0x708033e7e679f3f3

def z1296 : W := mkw 0x0064540000000000 0x00322a0000000000 0xfaffff0000000000 0x7d7fff8000000000

def z1297 : W := mkw 0x02f77ffffc112000 0x017bbffffe089000 0xfffffffffcf3e127 0xfffffffffe79f093

def z1298 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x37781f3c338f9e39 0x1bbc0f9e19c7cf1c

def z1299 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfefffffffc0007c0 0xff7ffffffe0003e0

def z1300 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0xfafff8fffc000000 0xfd7ffc7ffe000000

def z1301 : W := mkw 0xc108a34443fff630 0x608451a221fffb18 0xed0067cc43fffe39 0xf68033e621ffff1c

def z1302 : W := mkw 0x0075777fe4000000 0x003abbbff2000000 0xfafffffffc000000 0xfd7ffffffe000000

def z1303 : W := mkw 0x82f77ffffc008220 0x417bbffffe004110 0xfffffffffcf387e1 0xfffffffffe79c3f0

def z1304 : W := mkw 0xc2f77ffffc0a8230 0x617bbffffe054118 0xffffffffff0f9839 0xffffffffff87cc1c

def z1305 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfbffffffff0c0001 0xfdffffffff860000

def z1306 : W := mkw 0x41eefec023ff6010 0x20f77f6011ffb008 0xfbffffc033ffe019 0x7dffffe019fff00c

def z1307 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfefffffffcb387e6 0xff7ffffffe59c3f3

def z1308 : W := mkw 0x01eefec087ff6000 0x00f77f6043ffb000 0xfbffffc38fffe001 0x7dffffe1c7fff000

def z1309 : W := mkw 0x9011013fc4008262 0x4808809fe2004131 0x0400003fcc0007e6 0x8200001fe60003f3

def z1310 : W := mkw 0x005748bb18000000 0x002ba45d8c000000 0xfffff8fffcf067e7 0xfffffc7ffe7833f3

def z1311 : W := mkw 0x0255403b38000000 0x012aa01d9c000000 0x12ff803030000000 0x097fc01818000000

def z1312 : W := mkw 0x0008800003ce4000 0x0004400001e72000 0x0100000003cfe001 0x0080000001e7f000

def z1313 : W := mkw 0x92f67fede411a262 0x497b3ff6f208d131 0xffffffcfccf3e7e7 0xffffffe7e679f3f3

def z1314 : W := mkw 0x00f65dac60000000 0x007b2ed630000000 0xbaff9f3c70000000 0xdd7fcf9e38000000

def z1315 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x7effe03f80800601 0xbf7ff01fc0400300

def z1316 : W := mkw 0x21aabec01bff690d 0x10d55f600dffb486 0x85001fc07ffff93f 0x42800fe03ffffc9f

def z1317 : W := mkw 0x205dc03b03e45d8d 0x902ee01d81f22ec6 0xffffe0ffcffc7fff 0xfffff07fe7fe3fff

def z1318 : W := mkw 0x00e4764000112000 0x00723b2000089000 0x2278670000b38000 0x113c33800059c000

def z1319 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xbb781f3c730f9838 0xddbc0f9e3987cc1c

def z1320 : W := mkw 0x8075553f60008220 0x403aaa9fb0004110 0xffffff3ff0f387e1 0xffffff9ff879c3f0

def z1321 : W := mkw 0x90002344c411a262 0x480011a26208d131 0x640067cfccf3e7e6 0xb20033e7e679f3f3

def z1322 : W := mkw 0x005cc02903e01480 0x802e601481f00a40 0x32ffe00d83b006c0 0x197ff006c1d80360

def z1323 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfffffff27ffff93f 0xfffffff93ffffc9f

def z1324 : W := mkw 0xc108800003ffffb1 0xe084400001ffffd8 0x0500000003fffff9 0x0280000001fffffc

def z1325 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xdaff9ff27c000000 0xed7fcff93e000000

def z1326 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xe2ffffcffc000000 0x717fffe7fe000000

def z1327 : W := mkw 0xe0331dbe780ec23c 0x70198edf3c07611e 0xfbff9ffe7c0fe03e 0xfdffcfff3e07f01f

def z1328 : W := mkw 0x82f77ffffc008220 0x417bbffffe004110 0xfbfffffffc038020 0xfdfffffffe01c010

def z1329 : W := mkw 0x00e65c8000000000 0x00732e4000000000 0xdaff98c000000000 0x6d7fcc6000000000

def z1330 : W := mkw 0x005dc03b03e45d81 0x802ee01d81f22ec0 0x7fffe03f83fc7fc1 0xbffff01fc1fe3fe0

def z1331 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x52ff98f23c000000 0x297fcc791e000000

def z1332 : W := mkw 0x3047ead39d7569cf 0x9823f569cebab4e7 0x4087e0c38c7061c6 0x2043f061c63830e3

def z1333 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0xbaff9f3030000000 0x5d7fcf9818000000

def z1334 : W := mkw 0x12f77ffffc112042 0x097bbffffe089021 0xfafffffffc3000c0 0xfd7ffffffe180060

def z1335 : W := mkw 0x21ffdcbb1bee5d8d 0x90ffee5d8df72ec6 0x12ff9830330c1818 0x097fcc1819860c0c

def z1336 : W := mkw 0x92f77ffffc008262 0x497bbffffe004131 0xfafffffffc000026 0xfd7ffffffe000013

def z1337 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x0400000003801e01 0x0200000001c00f00

def z1338 : W := mkw 0x02f75dbf78000000 0x017baedfbc000000 0xfaff9ffe7c000000 0xfd7fcfff3e000000

def z1339 : W := mkw 0x90576bffdc11a262 0x482bb5ffee08d131 0xfffffffffcf3e7e7 0xfffffffffe79f3f3

def z1340 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfefffffffc000126 0xff7ffffffe000093

def z1341 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0x93ff9ff07c03e026 0x49ffcff83e01f013

def z1342 : W := mkw 0x11eefec003ff6042 0x08f77f6001ffb021 0xfbffffc003ffe1c7 0x7dffffe001fff0e3

def z1343 : W := mkw 0xd038152ce68a9672 0x681c0a9673454b39 0xbf781f3c7f8f9e3f 0xdfbc0f9e3fc7cf1f

def z1344 : W := mkw 0x92e67fc4fc11a262 0x49733fe27e08d131 0xffffffcffcf3e7e7 0xffffffe7fe79f3f3

def z1345 : W := mkw 0x9108a344c7ffe262 0x488451a263fff131 0x810007c04fffe027 0x408003e027fff013

def z1346 : W := mkw 0xc2f77ffffc009630 0x617bbffffe004b18 0xfafffffffc000600 0xfd7ffffffe000300

def z1347 : W := mkw 0xb1a23fc4dc1fe26e 0x58d11fe26e0ff137 0x81001fc07c0fe03e 0x40800fe03e07f01f

def z1348 : W := mkw 0x02f67fede4000000 0x017b3ff6f2000000 0x32ffff0d80000000 0x197fff86c0000000

def z1349 : W := mkw 0x02d5627b84000000 0x016ab13dc2000000 0x7affe03f80000000 0xbd7ff01fc0000000

def z1350 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfaffffc003bf8000 0x7d7fffe001dfc000

def z1351 : W := mkw 0x82f77ffffc008220 0x417bbffffe004110 0xfffffffffcc3e727 0xfffffffffe61f393

def z1352 : W := mkw 0x00e67ec000044000 0x00733f6000022000 0xfbffffc0000c6000 0x7dffffe000063000

def z1353 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x3aff983c30000000 0x9d7fcc1e18000000

def z1354 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xbf781f3c73cfff3f 0xdfbc0f9e39e7ff9f

def z1355 : W := mkw 0x1055627b84112042 0x082ab13dc2089021 0x7affe0ff8c7061c6 0xbd7ff07fc63830e3

def z1356 : W := mkw 0x405dc03b03ea1d91 0xa02ee01d81f50ec8 0x7effe03f83fc1fd9 0xbf7ff01fc1fe0fec

def z1357 : W := mkw 0x00f75cbb00000000 0x007bae5d80000000 0x12ff983000000000 0x097fcc1800000000

def z1358 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfafffffffc038000 0xfd7ffffffe01c000

def z1359 : W := mkw 0x82f77ffffc008220 0x417bbffffe004110 0xffffffffff8f9e39 0xffffffffffc7cf1c

def z1360 : W := mkw 0x21eefec01bff600c 0x10f77f600dffb006 0xfffffff07ffff83f 0xfffffff83ffffc1f

def z1361 : W := mkw 0x00f77efb00001d81 0x807bbf7d80000ec0 0xfeffffff80001fc0 0xff7fffffc0000fe0

def z1362 : W := mkw 0x02f77ffffc200080 0x817bbffffe100040 0xfafffffffc3000c0 0xfd7ffffffe180060

def z1363 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xbbff9fc0038fe001 0x5dffcfe001c7f000

def z1364 : W := mkw 0x0108800003ee4000 0x0084400001f72000 0x01000000034c6001 0x0080000001a63000

def z1365 : W := mkw 0x21e7fed2195f690d 0x10f3ff690cafb486 0xfffffff27f4ff93f 0xfffffff93fa7fc9f

def z1366 : W := mkw 0x0008800003e01480 0x8004400001f00a40 0x0000000003f006c1 0x0000000001f80360

def z1367 : W := mkw 0x90002344c411a262 0x480011a26208d131 0xed0067fffcf3ffff 0xf68033fffe79ffff

def z1368 : W := mkw 0x21eefec01bff690d 0x10f77f600dffb486 0xffffffc07ffff93f 0x7fffffe03ffffc9f

def z1369 : W := mkw 0xe0331dbe78009f3d 0x70198edf3c004f9e 0xfeff9ffe7c001f3e 0xff7fcfff3e000f9f

def z1370 : W := mkw 0xc211013ffc009630 0x6108809ffe004b18 0x0000003ffc000600 0x8000001ffe000300

def z1371 : W := mkw 0x0108800003ff6901 0x0084400001ffb480 0x0500000003fff901 0x0280000001fffc80

def z1372 : W := mkw 0x005dc03b03ea1d81 0x802ee01d81f50ec0 0x7fffe03f83ff9fc1 0xbffff01fc1ffcfe0

def z1373 : W := mkw 0x8000010440008220 0x4000008220004110 0xed0067cfccf3e7e7 0xf68033e7e679f3f3

def z1374 : W := mkw 0x0055c03b01601d81 0x802ae01d80b00ec0 0x7effe03f80701fc0 0xbf7ff01fc0380fe0

def z1375 : W := mkw 0x02f77ffffc001d81 0x817bbffffe000ec0 0xfefffffffcf01fc1 0xff7ffffffe780fe0

def z1376 : W := mkw 0x21eefec01bff600c 0x10f77f600dffb006 0xffffffc27fffe13f 0xffffffe13ffff09f

def z1377 : W := mkw 0xd008a344c7fbbff3 0xe80451a263fddff9 0xed0067cfcfffffff 0xf68033e7e7ffffff

def z1378 : W := mkw 0xc038152ce68a9630 0x601c0a9673454b18 0xbf781f3fff8f9e39 0xdfbc0f9fffc7cf1c

def z1379 : W := mkw 0x2008800003e45d8d 0x9004400001f22ec6 0xed0060cfcffc7fff 0xf6803067e7fe3fff

def z1380 : W := mkw 0x01e67ec0000e4000 0x00f33f6000072000 0xfaffffc0000c0000 0x7d7fffe000060000

def z1381 : W := mkw 0xb108800003ffeb6f 0x5884400001fff5b7 0x0500000003ffffff 0x0280000001ffffff

def z1382 : W := mkw 0x00331cba38000000 0x00198e5d1c000000 0xdaff98f27c000000 0xed7fcc793e000000

def z1383 : W := mkw 0x00e65c8000000000 0x00732e4000000000 0xbaff9f0000000000 0x5d7fcf8000000000

def z1384 : W := mkw 0x02e67fc4fc000000 0x01733fe27e000000 0xfaffffcffc000000 0xfd7fffe7fe000000

def z1385 : W := mkw 0x8011013f40009fa1 0xc008809fa0004fd0 0x0400003fc0001fe0 0x8200001fe0000ff0

def z1386 : W := mkw 0x0055403b18000000 0x002aa01d8c000000 0x7affe03ffc000000 0xbd7ff01ffe000000

def z1387 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x7afff83030000000 0x3d7ffc1818000000

def z1388 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x7efff83fb0f007c1 0xbf7ffc1fd87803e0

def z1389 : W := mkw 0xe019813e7bcedf3d 0x700cc09f3de76f9e 0x0500003e7fcfff3f 0x8280001f3fe7ff9f

def z1390 : W := mkw 0x00331cba38000000 0x00198e5d1c000000 0x12ff983030000000 0x097fcc1818000000

def z1391 : W := mkw 0x016cd40003ff6000 0x00b66a0001ffb000 0xfbffff0003ffe001 0x7dffff8001fff000

def z1392 : W := mkw 0x9108800003ffe262 0x4884400001fff131 0x0100000003ffe6c1 0x0080000001fff360

def z1393 : W := mkw 0x0108800003fb2000 0x0084400001fd9000 0x0000000003f38001 0x0000000001f9c000

def z1394 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x9d8798f07f0c783f 0xcec3cc783f863c1f

def z1395 : W := mkw 0x1008800003f13dc3 0x8804400001f89ee1 0x0400000003f07fc7 0x0200000001f83fe3

def z1396 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x7affe03f80f007c0 0xbd7ff01fc07803e0

def z1397 : W := mkw 0x92e67fc4fc11a262 0x49733fe27e08d131 0xfbffffc07cf3e027 0x7dffffe03e79f013

def z1398 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfefffffffc800601 0xff7ffffffe400300

def z1399 : W := mkw 0x0000224000112000 0x0000112000089000 0xed0067cfccf3e7e7 0xf68033e7e679f3f3

def z1400 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfeffffffff001801 0xff7fffffff800c00

def z1401 : W := mkw 0xc008800003ced630 0x6004400001e76b18 0x0500000003cffe39 0x0280000001e7ff1c

def z1402 : W := mkw 0x0019803b03e01d81 0x800cc01d81f00ec0 0x6c00603f83f01fc1 0xb600301fc1f80fe0

def z1403 : W := mkw 0x9055637fc411bfe3 0xc82ab1bfe208dff1 0xffffe7ffccf3ffe7 0xfffff3ffe679fff3

def z1404 : W := mkw 0x00e75c9218000000 0x0073ae490c000000 0xdaff98f27c000000 0xed7fcc793e000000

def z1405 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x7fffe03f83fc1ff9 0xbffff01fc1fe0ffc

def z1406 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0xffffe03fc3f01fe1 0xfffff01fe1f80ff0

def z1407 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x4400600383f01fc1 0x22003001c1f80fe0

def z1408 : W := mkw 0x12e77ed39c112042 0x0973bf69ce089021 0xfbffffc38cf3e1c7 0x7dffffe1c679f0e3

def z1409 : W := mkw 0x0055627b84000000 0x002ab13dc2000000 0x7affe0ff8c000000 0xbd7ff07fc6000000

def z1410 : W := mkw 0x22f77ffffc04490d 0x117bbffffe022486 0xfffffffffc0c793e 0xfffffffffe063c9f

def z1411 : W := mkw 0xc011013f60009630 0x6008809fb0004b18 0x0400003ff0001e38 0x8200001ff8000f1c

def z1412 : W := mkw 0x01eefec003fb2000 0x00f77f6001fd9000 0xfaffffc003f38001 0x7d7fffe001f9c000

def z1413 : W := mkw 0xb108a344c7ffeb6f 0x588451a263fff5b7 0xed0067cfcfffffff 0xf68033e7e7ffffff

def z1414 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0x7affff3fb0000000 0xbd7fff9fd8000000

def z1415 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xb3ffffc003bfe000 0x59ffffe001dff000

def z1416 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0x9d00183073fff839 0xce800c1839fffc1c

def z1417 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xff781ffc73cffe39 0xffbc0ffe39e7ff1c

def z1418 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0xfbffffc000406001 0x7dffffe000203000

def z1419 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xbb781f3c338f9e19 0x5dbc0f9e19c7cf0c

def z1420 : W := mkw 0x205748bb1804400c 0x102ba45d8c022006 0xfbfff8fffc0c603e 0xfdfffc7ffe06301f

def z1421 : W := mkw 0x0108a24003ff6000 0x0084512001ffb000 0x2100670003ffe001 0x1080338001fff000

def z1422 : W := mkw 0x03f75cbb380e4000 0x01fbae5d9c072000 0x12ff9830300c0000 0x097fcc1818060000

def z1423 : W := mkw 0x21eefec01bff600c 0x10f77f600dffb006 0xfbffffc033ffe019 0x7dffffe019fff00c

def z1424 : W := mkw 0x9211013ffc008262 0x4908809ffe004131 0x0000003ffc000026 0x8000001ffe000013

def z1425 : W := mkw 0x0108800003ee5d81 0x8084400001f72ec0 0x0400000003fc1fc1 0x0200000001fe0fe0

def z1426 : W := mkw 0x2008800003e45d8d 0x9004400001f22ec6 0x00000000030c1818 0x0000000001860c0c

def z1427 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x72ffe03f83f01fc0 0x397ff01fc1f80fe0

def z1428 : W := mkw 0x02f75dbffc000000 0x017baedffe000000 0x7afff83ffc000000 0xbd7ffc1ffe000000

def z1429 : W := mkw 0x0219813fffe01d81 0x810cc09ffff00ec0 0x0400003ffff01fc1 0x8200001ffff80fe0

def z1430 : W := mkw 0xc008800003ea9fb1 0xe004400001f54fd8 0x05000000038f9e39 0x0280000001c7cf1c

def z1431 : W := mkw 0x00e77fd6dc000000 0x0073bfeb6e000000 0xfafffffffc000000 0xfd7ffffffe000000

def z1432 : W := mkw 0x90088104c7e09fe3 0xc804408263f04ff1 0x0400000fcff01fe7 0x82000007e7f80ff3

def z1433 : W := mkw 0x0008800003e01400 0x0004400001f00a00 0x0400000003f01e01 0x0200000001f80f00

def z1434 : W := mkw 0x02d76afb9c000000 0x016bb57dce000000 0x62ffe0cf8c000000 0x317ff067c6000000

def z1435 : W := mkw 0x23c7ead39d75690d 0x11e3f569cebab486 0x4087e0c38c706106 0x2043f061c6383083

def z1436 : W := mkw 0x005cc02903e01480 0x802e601481f00a40 0x7effe03d83f01ec1 0xbf7ff01ec1f80f60

def z1437 : W := mkw 0x00333ffefc000000 0x00199fff7e000000 0xfafffffffc000000 0xfd7ffffffe000000

def z1438 : W := mkw 0x9055413fc4008262 0x482aa09fe2004131 0x7effe03fcc0007e6 0xbf7ff01fe60003f3

def z1439 : W := mkw 0x0108800003ff6981 0x8084400001ffb4c0 0x0100000003ffe1c1 0x0080000001fff0e0

def z1440 : W := mkw 0x0119803b03ff7d81 0x808cc01d81ffbec0 0x0500003f83ffffc1 0x8280001fc1ffffe0

def z1441 : W := mkw 0x0038152c628a0000 0x001c0a9631450000 0xbf781f3c738f9839 0xdfbc0f9e39c7cc1c

def z1442 : W := mkw 0x90f77fffc411a262 0x487bbfffe208d131 0xffffffffccf3e7e7 0xffffffffe679f3f3

def z1443 : W := mkw 0x02f77efb9c000000 0x017bbf7dce000000 0xfaffffff8c000000 0xfd7fffffc6000000

def z1444 : W := mkw 0x02f75dbf78000000 0x017baedfbc000000 0x92ff9f3070000000 0x497fcf9838000000

def z1445 : W := mkw 0x91088104c7ffe262 0x4884408263fff131 0x0500000fcfffe7e7 0x82800007e7fff3f3

def z1446 : W := mkw 0x01ee7ec002bf6000 0x00f73f60015fb000 0xfbffffc000bfe000 0x7dffffe0005ff000

def z1447 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0x0000000003bf8000 0x0000000001dfc000

def z1448 : W := mkw 0x018aaac003ff6000 0x00c5556001ffb000 0x010000c003ffe001 0x0080006001fff000

def z1449 : W := mkw 0x01eedc8003ee4000 0x00f76e4001f72000 0x32ff9f00038f8000 0x197fcf8001c7c000

def z1450 : W := mkw 0x0055403b00001d81 0x802aa01d80000ec0 0x7affe03f80001800 0xbd7ff01fc0000c00

def z1451 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x32ffe03d80000000 0x197ff01ec0000000

def z1452 : W := mkw 0x92f77ffffc008262 0x497bbffffe004131 0xfefffffffcf007e7 0xff7ffffffe7803f3

def z1453 : W := mkw 0x9055403b0011a262 0x482aa01d8008d131 0x7fffe03f80f3e7e7 0xbffff01fc079f3f3

def z1454 : W := mkw 0x01eefec003ff6981 0x80f77f6001ffb4c0 0xfbffffc003ffe1c1 0x7dffffe001fff0e0

def z1455 : W := mkw 0xc0e67fc4600a8230 0x60733fe230054118 0xfbffffc0700f8038 0x7dffffe03807c01c

def z1456 : W := mkw 0x02f4776de4000000 0x017a3bb6f2000000 0x7affe70d80000000 0x3d7ff386c0000000

def z1457 : W := mkw 0x202914121a8a090d 0x10148a090d450486 0xbf781f327f8f993f 0xdfbc0f993fc7cc9f

def z1458 : W := mkw 0x22f75cbb3804400c 0x117bae5d9c022006 0x12ff9830300c0018 0x097fcc181806000c

def z1459 : W := mkw 0x0055403b00000901 0x002aa01d80000480 0x7effe03f80001900 0xbf7ff01fc0000c80

def z1460 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0xfffff83ff30c1839 0xfffffc1ff9860c1c

def z1461 : W := mkw 0x02e67ec038000000 0x01733f601c000000 0xfaffffc030000000 0x7d7fffe018000000

def z1462 : W := mkw 0x0075543b20000000 0x003aaa1d90000000 0x12ff983030000000 0x097fcc1818000000

def z1463 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x66ffe03f80f01fc0 0xb37ff01fc0780fe0

def z1464 : W := mkw 0x02f77ffffc001480 0x817bbffffe000a40 0xfafffffffc0006c0 0xfd7ffffffe000360

def z1465 : W := mkw 0x00775dbf78000000 0x003baedfbc000000 0xfafffffffc000000 0xfd7ffffffe000000

def z1466 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfbfffffffc0c0038 0xfdfffffffe06001c

def z1467 : W := mkw 0x90e77fd6dc11a262 0x4873bfeb6e08d131 0xfffffffffcf3e7e7 0xfffffffffe79f3f3

def z1468 : W := mkw 0x02f75dbffc000000 0x017baedffe000000 0xdaff98fffc000000 0xed7fcc7ffe000000

def z1469 : W := mkw 0x11eefec087ff6042 0x08f77f6043ffb021 0xfbffffc183ffe0c1 0x7dffffe0c1fff060

def z1470 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0xfffff8fffffc7fff 0xfffffc7ffffe3fff

def z1471 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x3e781f3c338f9e19 0x9f3c0f9e19c7cf0c

def z1472 : W := mkw 0x00321dac60000000 0x00190ed630000000 0xfaff9ffc70000000 0xfd7fcffe38000000

def z1473 : W := mkw 0x0055413f40000000 0x002aa09fa0000000 0xfaffe73fc0000000 0xfd7ff39fe0000000

def z1474 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xfd8798fe7fcc7f3f 0xfec3cc7f3fe63f9f

def z1475 : W := mkw 0x0018802903e01d81 0x800c401481f00ec0 0x0400000d83f01fc1 0x02000006c1f80fe0

def z1476 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x7affe03f83b01ec0 0xbd7ff01fc1d80f60

def z1477 : W := mkw 0x0008800003e01d81 0x8004400001f00ec0 0x4c00000203f01fc1 0xa600000101f80fe0

def z1478 : W := mkw 0x0108a24003ff6000 0x0084512001ffb000 0x410060c003ffe001 0x2080306001fff000

def z1479 : W := mkw 0x01e47640001b2000 0x00f23b20000d9000 0x2278670000038000 0x113c33800001c000

def z1480 : W := mkw 0x0008800003f12000 0x0004400001f89000 0x0100000003f3e001 0x0080000001f9f000

def z1481 : W := mkw 0x0075553f60000000 0x003aaa9fb0000000 0xbaff9f3c70000000 0xdd7fcf9e38000000

def z1482 : W := mkw 0x20e77ed21800090d 0x1073bf690c000486 0xfefffff27c00193e 0xff7ffff93e000c9f

def z1483 : W := mkw 0x006edc8003ee4000 0x00376e4001f72000 0xfbffffc003ffe001 0x7dffffe001fff000

def z1484 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfefffffffcf387c1 0xff7ffffffe79c3e0

def z1485 : W := mkw 0x0008800003e00981 0x8004400001f004c0 0x0000000003f001c1 0x0000000001f800e0

def z1486 : W := mkw 0x00e67fc4c4000000 0x00733fe262000000 0xfaffffcd80000000 0x7d7fffe6c0000000

def z1487 : W := mkw 0x006cd40003ea0000 0x00366a0001f50000 0xbbff9f00038f8001 0x5dffcf8001c7c000

def z1488 : W := mkw 0x9019813fc7f1bfe3 0xc80cc09fe3f8dff1 0x0500003fcff3ffe7 0x8280001fe7f9fff3

def z1489 : W := mkw 0x2108800003ee490d 0x1084400001f72486 0x00000000030c1818 0x0000000001860c0c

def z1490 : W := mkw 0x01eedc8003ff6000 0x00f76e4001ffb000 0xbbff9f0003ffe001 0x5dffcf8001fff000

def z1491 : W := mkw 0x02f77fffe4000000 0x017bbffff2000000 0xfaffffff80000000 0xfd7fffffc0000000

def z1492 : W := mkw 0x02e77ed39c000000 0x0173bf69ce000000 0x62ffe7c38c000000 0x317ff3e1c6000000

def z1493 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x9f781f30730f9839 0xcfbc0f983987cc1c

def z1494 : W := mkw 0x01aa9c8003ff6000 0x00d54e4001ffb000 0x0100180003ffe001 0x00800c0001fff000

def z1495 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfaffffcf8c000000 0x7d7fffe7c6000000

def z1496 : W := mkw 0x01ecf64003fb2000 0x00f67b2001fd9000 0xfbffff0003ff8001 0x7dffff8001ffc000

def z1497 : W := mkw 0x02f77efbbc000000 0x017bbf7dde000000 0x12ff98f03c000000 0x097fcc781e000000

def z1498 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0xcd0000c24fffe127 0xe680006127fff093

def z1499 : W := mkw 0x0008800003e00000 0x0004400001f00000 0x0400000003f007c1 0x0200000001f803e0

def z1500 : W := mkw 0xb2f77ffffc008b6f 0x597bbffffe0045b7 0xfefffffffc001ffe 0xff7ffffffe000fff

def z1501 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xbaff9ffc7c000000 0xdd7fcffe3e000000

def z1502 : W := mkw 0x005cc02903e01480 0x802e601481f00a40 0x62ffe00d80f006c0 0x317ff006c0780360

def z1503 : W := mkw 0x0011003a00000000 0x0008801d00000000 0x7aff803e00000000 0xbd7fc01f00000000

def z1504 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x7fffe03f83f07fe7 0xbffff01fc1f83ff3

def z1505 : W := mkw 0x02f77ffffc000901 0x017bbffffe000480 0xfefffffffc001900 0xff7ffffffe000c80

def z1506 : W := mkw 0x92f77ffffc008262 0x497bbffffe004131 0xfafffffffc0006c0 0xfd7ffffffe000360

def z1507 : W := mkw 0xc008800003e09fb1 0xe004400001f04fd8 0x0400000003f01ff9 0x0200000001f80ffc

def z1508 : W := mkw 0x02e77ed39c000000 0x0173bf69ce000000 0x52fff8c38c000000 0x297ffc61c6000000

def z1509 : W := mkw 0x2108800003ff690d 0x1084400001ffb486 0x0100000003fff819 0x0080000001fffc0c

def z1510 : W := mkw 0x12f77ffffc112042 0x097bbffffe089021 0xfffffffffc7061e7 0xfffffffffe3830f3

def z1511 : W := mkw 0x02d76bfffc000000 0x016bb5fffe000000 0x7affe0fffc000000 0xbd7ff07ffe000000

def z1512 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0x97781f3c730f9e38 0xcbbc0f9e3987cf1c

def z1513 : W := mkw 0xe2f77ffffc0ec23c 0x717bbffffe07611e 0xfbfffffffc0fe03e 0xfdfffffffe07f01f

def z1514 : W := mkw 0x8008800003e09fa1 0xc004400001f04fd0 0x0500000003f39fe1 0x0280000001f9cff0

def z1515 : W := mkw 0xc028950463ea9fb1 0xe0144a8231f54fd8 0x85001f0073ff9ff9 0x42800f8039ffcffc

def z1516 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x56ffe03f83701fc0 0xab7ff01fc1b80fe0

def z1517 : W := mkw 0x80331dbe78008220 0x40198edf3c004110 0xffff9ffe7cc3e727 0xffffcfff3e61f393

def z1518 : W := mkw 0x92f75dbffc008262 0x497baedffe004131 0x16ff983ffc0007e6 0x8b7fcc1ffe0003f3

def z1519 : W := mkw 0xf008800003dfff7f 0x7804400001efffbf 0x0500000003ffffff 0x0280000001ffffff

def z1520 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfafffff07c000000 0x7d7ffff83e000000

def z1521 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0xd18798f27f4c793e 0x68c3cc793fa63c9f

def z1522 : W := mkw 0xf0223fc4fc1fe27e 0x78111fe27e0ff13f 0x81001fc07c0fe03e 0x40800fe03e07f01f

def z1523 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfbffffc04fffe027 0x7dffffe027fff013

def z1524 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfbffffc383ffe1c1 0x7dffffe1c1fff0e0

def z1525 : W := mkw 0x005748bb18000000 0x002ba45d8c000000 0xdaff98f27c000000 0xed7fcc793e000000

def z1526 : W := mkw 0x205dc03b03e45d8d 0x902ee01d81f22ec6 0xfffff83ff3fc7fff 0xfffffc1ff9fe3fff

def z1527 : W := mkw 0x01a8b64003ff6000 0x00d45b2001ffb000 0x0100070003ffe001 0x0080038001fff000

def z1528 : W := mkw 0xd2f77ffffc1ba272 0x697bbffffe0dd139 0xfffffffffcffe7ff 0xfffffffffe7ff3ff

def z1529 : W := mkw 0x0055403b00200080 0x802aa01d80100040 0x7affe03f803000c0 0xbd7ff01fc0180060

def z1530 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xdbff9fc0034fe001 0x6dffcfe001a7f000

def z1531 : W := mkw 0x90333ffefc11a262 0x48199fff7e08d131 0xfffffffffcf3e7e7 0xfffffffffe79f3f3

def z1532 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfbfffffffc838001 0xfdfffffffe41c000

def z1533 : W := mkw 0x02f67fede4000000 0x017b3ff6f2000000 0x62ffe7cd80000000 0x317ff3e6c0000000

def z1534 : W := mkw 0x005748bb18000000 0x002ba45d8c000000 0x12ff983030000000 0x097fcc1818000000

def z1535 : W := mkw 0x42f75cbb38001410 0x217bae5d9c000a08 0x12ff983030001818 0x097fcc1818000c0c

def z1536 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfafffffffcb006c0 0xfd7ffffffe580360

def z1537 : W := mkw 0x21c7ead31975698d 0x90e3f5698cbab4c6 0x4087e0c38c7061c6 0x2043f061c63830e3

def z1538 : W := mkw 0x00f77fff60000000 0x007bbfffb0000000 0xfafffffff0000000 0xfd7ffffff8000000

def z1539 : W := mkw 0x02e67fc4e4000000 0x01733fe272000000 0xfaffffc000000000 0x7d7fffe000000000

def z1540 : W := mkw 0xd07c776de6bbb6f2 0xe83e3bb6f35ddb79 0x2278670d80b386c0 0x113c3386c059c360

def z1541 : W := mkw 0x02d748bb18000000 0x016ba45d8c000000 0x12ff803000000000 0x097fc01800000000

def z1542 : W := mkw 0xc108800003ffe230 0x6084400001fff118 0x0100000003ffe039 0x0080000001fff01c

def z1543 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0xdaff98f030000000 0x6d7fcc7818000000

def z1544 : W := mkw 0x205dc03b03e45d8d 0x902ee01d81f22ec6 0x7effe03f83f07fc7 0xbf7ff01fc1f83fe3

def z1545 : W := mkw 0x03f77efb381f6000 0x01fbbf7d9c0fb000 0x93ff9ff0300fe000 0x49ffcff81807f000

def z1546 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfbffffc073ffe039 0x7dffffe039fff01c

def z1547 : W := mkw 0x01ceeac003f56000 0x00e7756001fab000 0xfbffe7c003f3e001 0x7dfff3e001f9f000

def z1548 : W := mkw 0xc211013f78009630 0x6108809fbc004b18 0x0400003c70001e38 0x8200001e38000f1c

def z1549 : W := mkw 0x02f5543b20000000 0x017aaa1d90000000 0x12ff803000000000 0x097fc01800000000

def z1550 : W := mkw 0x22f77ffffc04400c 0x117bbffffe022006 0xfffffffffc4c613f 0xfffffffffe26309f

def z1551 : W := mkw 0xe011013f78009fbd 0xf008809fbc004fde 0x0400003ffc001ffe 0x8200001ffe000fff

def z1552 : W := mkw 0x02f67fede4000000 0x017b3ff6f2000000 0xfaffffcfcc000000 0xfd7fffe7e6000000

def z1553 : W := mkw 0xd108800003fff672 0x6884400001fffb39 0x0500000003ffffff 0x0280000001ffffff

def z1554 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0x72ffffffbc000000 0x397fffffde000000

def z1555 : W := mkw 0x0055403b00001400 0x002aa01d80000a00 0x7effe03f80001e00 0xbf7ff01fc0000f00

def z1556 : W := mkw 0x90446344c411a262 0x482231a26208d131 0xffffe7cfccf3e7e7 0xfffff3e7e679f3f3

def z1557 : W := mkw 0xc038152d628a96b0 0xe01c0a96b1454b58 0xbf781f3df38f9ef9 0xdfbc0f9ef9c7cf7c

def z1558 : W := mkw 0x21eefec003ff600c 0x10f77f6001ffb006 0xfbffffc003ffe03f 0x7dffffe001fff01f

def z1559 : W := mkw 0x0008a344c7e01d81 0x800451a263f00ec0 0xec0067cfcff01fc1 0xf60033e7e7f80fe0

def z1560 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfefffffffc001838 0xff7ffffffe000c1c

def z1561 : W := mkw 0xd2a23fc4fc1ba272 0x69511fe27e0dd139 0x81001fc07c0fe03e 0x40800fe03e07f01f

def z1562 : W := mkw 0x4038152c628a1410 0x201c0a9631450a08 0xbb781f3c738f9819 0xddbc0f9e39c7cc0c

def z1563 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0xfffff83f83fc1fc1 0xfffffc1fc1fe0fe0

def z1564 : W := mkw 0xc07d553f628a9630 0x603eaa9fb1454b18 0xffffff3ff3ff9ff9 0xffffff9ff9ffcffc

def z1565 : W := mkw 0xc075553f600a8230 0x603aaa9fb0054118 0xfbffff3ff00f8038 0xfdffff9ff807c01c

def z1566 : W := mkw 0xe02a9d847bcedf3d 0x70154ec23de76f9e 0x85001fc07fcfff3f 0x42800fe03fe7ff9f

def z1567 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0x32ffff0000000000 0x197fff8000000000

def z1568 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x7affe00f83f007c1 0x3d7ff007c1f803e0

def z1569 : W := mkw 0x0010002800000000 0x0008001400000000 0x3e78003c00800601 0x9f3c001e00400300

def z1570 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x12ff98327c000000 0x897fcc193e000000

def z1571 : W := mkw 0x23f77ffffc1f600c 0x11fbbffffe0fb006 0xfbfffffffc0fe03e 0xfdfffffffe07f01f

def z1572 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xffffffc003ffe127 0x7fffffe001fff093

def z1573 : W := mkw 0xc038152c628a9630 0x601c0a9631454b18 0xff781f3e73cf9f39 0xffbc0f9f39e7cf9c

def z1574 : W := mkw 0x0055413f60000000 0x002aa09fb0000000 0x7affe03ff0000000 0xbd7ff01ff8000000

def z1575 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0x0500000003fff839 0x0280000001fffc1c

def z1576 : W := mkw 0x00f77efb00112000 0x007bbf7d80089000 0xffffffff80f3e7c1 0xffffffffc079f3e0

def z1577 : W := mkw 0x00eefec003ea0000 0x00777f6001f50000 0xfbffffc003ff8001 0x7dffffe001ffc000

def z1578 : W := mkw 0x0000224000112000 0x0000112000089000 0xe90067c00003e000 0x748033e00001f000

def z1579 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0xffffe0ffcc406127 0xfffff07fe6203093

def z1580 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xd3ffffc0037fe000 0x69ffffe001bff000

def z1581 : W := mkw 0x02f75dbf78000000 0x017baedfbc000000 0x12ff983c70000000 0x897fcc1e38000000

def z1582 : W := mkw 0xb2f77ffffc15e26e 0x597bbffffe0af137 0xfbfffffffc0fe03e 0xfdfffffffe07f01f

def z1583 : W := mkw 0x01ecf64003fb2000 0x00f67b2001fd9000 0x62ffe70000f38000 0x317ff3800079c000

def z1584 : W := mkw 0x6008800003ce5d1d 0x3004400001e72e8e 0x00000000030c1818 0x0000000001860c0c

def z1585 : W := mkw 0x00576bffdc000000 0x002bb5ffee000000 0xfafffffffc000000 0xfd7ffffffe000000

def z1586 : W := mkw 0xd2f77ffffc11b672 0x697bbffffe08db39 0xfffffffffcf3ffff 0xfffffffffe79ffff

def z1587 : W := mkw 0x9108800003ffffe3 0xc884400001fffff1 0x0500000003ffffe7 0x0280000001fffff3

def z1588 : W := mkw 0x8008810443e09fa1 0xc004408221f04fd0 0xad00070c43f39fe1 0xd680038621f9cff0

def z1589 : W := mkw 0xc075553f60009fb1 0xe03aaa9fb0004fd8 0xfeffff3ff0001ff8 0xff7fff9ff8000ffc

def z1590 : W := mkw 0x00e75c9218000000 0x0073ae490c000000 0x12ff983030000000 0x097fcc1818000000

def z1591 : W := mkw 0x0008800003f13d81 0x8004400001f89ec0 0x0500000003f3ffc1 0x0280000001f9ffe0

def z1592 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xffffffc003fff839 0x7fffffe001fffc1c

def z1593 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0xfafffff070000000 0xfd7ffff838000000

def z1594 : W := mkw 0x02e77ed318000000 0x0173bf698c000000 0xfaffffc000000000 0x7d7fffe000000000

def z1595 : W := mkw 0x92f77ffffc009fe3 0xc97bbffffe004ff1 0xfefffffffc001fe6 0xff7ffffffe000ff3

def z1596 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0xfaffe0ffcc000000 0xfd7ff07fe6000000

def z1597 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfbffffc24fffe001 0xfdffffe127fff000

def z1598 : W := mkw 0x02f77ffffc000000 0x017bbffffe000000 0xfaffffffff0c1818 0xfd7fffffff860c0c

def z1599 : W := mkw 0x607fdcbb3bee5d9d 0xb03fee5d9df72ece 0x12ff9830330c1818 0x097fcc1819860c0c

def z1600 : W := mkw 0x22f77ffffc00090d 0x117bbffffe000486 0xfafffffffc001818 0xfd7ffffffe000c0c

def z1601 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x6effe00f80f007c1 0xb77ff007c07803e0

def z1602 : W := mkw 0xf008a344c7dfff7f 0x780451a263efffbf 0xed0067cfcfffffff 0xf68033e7e7ffffff

def z1603 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0x7affff0003ff8001 0x3d7fff8001ffc000

def z1604 : W := mkw 0x0255403b38000000 0x012aa01d9c000000 0x7affe03fb0000000 0xbd7ff01fd8000000

def z1605 : W := mkw 0xc0fe7fec629bb630 0x607f3ff6314ddb18 0xfffffffc73fffe39 0xfffffffe39ffff1c

def z1606 : W := mkw 0xc1f67fec601fe230 0x60fb3ff6300ff118 0xfbfffffc700fe038 0xfdfffffe3807f01c

def z1607 : W := mkw 0x92f77ffffc11a262 0x497bbffffe08d131 0xfbfffffffc73e1e6 0xfdfffffffe39f0f3

def z1608 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0xffffffc24c406127 0xffffffe126203093

def z1609 : W := mkw 0x9108a344c7ffe262 0x488451a263fff131 0x2100670d83ffe6c1 0x10803386c1fff360

def z1610 : W := mkw 0x9011013fc4009fe3 0xc808809fe2004ff1 0x0400003f80001fc0 0x8200001fc0000fe0

def z1611 : W := mkw 0x9108a344c7ffffe3 0xc88451a263fffff1 0xed0067cfcfffffe7 0xf68033e7e7fffff3

def z1612 : W := mkw 0x002abec003df6000 0x00155f6001efb000 0xfbffffc003ffe001 0x7dffffe001fff000

def z1613 : W := mkw 0x00e77ed300000000 0x0073bf6980000000 0xfaffffc380000000 0x7d7fffe1c0000000

def z1614 : W := mkw 0x0008800003c01d01 0x0004400001e00e80 0x0400000003c01f01 0x0200000001e00f80

def z1615 : W := mkw 0x90e67ec00011a262 0x48733f600008d131 0xffffffc000f3e7e7 0x7fffffe00079f3f3

def z1616 : W := mkw 0x80f67fec6011a220 0x407b3ff63008d110 0xfffffffc70f3e621 0xfffffffe3879f310

def z1617 : W := mkw 0x0008a24003f12000 0x0004512001f89000 0xe90067c003f3e001 0x748033e001f9f000

def z1618 : W := mkw 0x82f75dbf78008220 0x417baedfbc004110 0xbfff9f3c70838621 0xdfffcf9e3841c310

def z1619 : W := mkw 0x90002344c411a262 0x480011a26208d131 0x6c0067cf8cf3e7c7 0xb60033e7c679f3e3

def z1620 : W := mkw 0x00e67fc460000000 0x00733fe230000000 0xfaffffc070000000 0x7d7fffe038000000

def z1621 : W := mkw 0x005cc02803e01400 0x002e601401f00a00 0x7effe03f83f01fc1 0xbf7ff01fc1f80fe0

def z1622 : W := mkw 0x22f77ffffc00090d 0x117bbffffe000486 0xffffffffff0c193f 0xffffffffff860c9f

def z1623 : W := mkw 0x0020140000000000 0x00100a0000000000 0xbb781f0000838001 0x5dbc0f800041c000

def z1624 : W := mkw 0x02e77fd7dc000000 0x0173bfebee000000 0xfaffffcfcc000000 0xfd7fffe7e6000000

def z1625 : W := mkw 0x02f67ee920000000 0x017b3f7490000000 0xfaffffc000000000 0x7d7fffe000000000

def z1626 : W := mkw 0xc2f77ffffc0a9630 0x617bbffffe054b18 0xfffffffffc0f9e38 0xfffffffffe07cf1c

def z1627 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x3aff803c00000000 0x9d7fc01e00000000

def z1628 : W := mkw 0xd108a344c7fff672 0x688451a263fffb39 0xed0067cfcfffffff 0xf68033e7e7ffffff

def z1629 : W := mkw 0x00e67ec000000000 0x00733f6000000000 0x52fff8c000000000 0x297ffc6000000000

def z1630 : W := mkw 0x005cc02903e01480 0x802e601481f00a40 0x7effe00f83f007c1 0xbf7ff007c1f803e0

def z1631 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x66ffe00f83f01fc1 0x337ff007c1f80fe0

def z1632 : W := mkw 0x2108800003ff7d8d 0x9084400001ffbec6 0x0500000003ffffff 0x0280000001ffffff

def z1633 : W := mkw 0x0055627b00112000 0x002ab13d80089000 0xfbffe7ff80f3e001 0xfdfff3ffc079f000

def z1634 : W := mkw 0x0108800003f56000 0x0084400001fab000 0x0000000003f06001 0x0000000001f83000

def z1635 : W := mkw 0x0001001200000000 0x0000800900000000 0x5c87803200400101 0xae43c01900200080

def z1636 : W := mkw 0x21eefec003ff690d 0x10f77f6001ffb486 0xfbffffc003ffe107 0x7dffffe001fff083

def z1637 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xffffffc203ffe101 0xffffffe101fff080

def z1638 : W := mkw 0x0002088000044000 0x0001044000022000 0xd98798c0000c6000 0x6cc3cc6000063000

def z1639 : W := mkw 0x010a888003ff6000 0x0085444001ffb000 0x810018c003ffe001 0x40800c6001fff000

def z1640 : W := mkw 0x002a1c80028a0000 0x00150e4001450000 0xfbff9fc0038f8001 0x7dffcfe001c7c000

def z1641 : W := mkw 0x200388921944490d 0x1001c4490ca22486 0x548798f27f4c793e 0xaa43cc793fa63c9f

def z1642 : W := mkw 0x0075553f60000000 0x003aaa9fb0000000 0x7affe73f80000000 0xbd7ff39fc0000000

def z1643 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xffffffcc03ffe601 0xffffffe601fff300

def z1644 : W := mkw 0x004cc00103e01d81 0x8026600081f00ec0 0x0400600183f01fc1 0x02003000c1f80fe0

def z1645 : W := mkw 0x91aabfc4c7ffe262 0x48d55fe263fff131 0xed007fcfcfffe7e7 0xf6803fe7e7fff3f3

def z1646 : W := mkw 0x01eefec003ff6000 0x00f77f6001ffb000 0xfbffffcd83ffe6c1 0x7dffffe6c1fff360

def z1647 : W := mkw 0x005d403b02a01480 0x802ea01d81500a40 0x7effe03f83b01ec1 0xbf7ff01fc1d80f60

def z1648 : W := mkw 0xc0281504628a8230 0x60140a8231454118 0xbf781f30738f9839 0xdfbc0f9839c7cc1c

def z1649 : W := mkw 0x0275553ffc000000 0x013aaa9ffe000000 0xfaffff3ffc000000 0xfd7fff9ffe000000

def z1650 : W := mkw 0xc2f77ffffc009630 0x617bbffffe004b18 0xffffffffff0c1e39 0xffffffffff860f1c

def z1651 : W := mkw 0x0009801203e01d81 0x8004c00901f00ec0 0x0400003203f01fc1 0x8200001901f80fe0

def z1652 : W := mkw 0xc011013f60009fb1 0xe008809fb0004fd8 0x0400003c70001e38 0x8200001e38000f1c

def z1653 : W := mkw 0x01eefec003ee4000 0x00f77f6001f72000 0xfbffffc0038f8001 0x7dffffe001c7c000

def z1654 : W := mkw 0x03f77ffffc156000 0x01fbbffffe0ab000 0xfafffffffc006000 0xfd7ffffffe003000

def z1655 : W := mkw 0x00331dbe78000000 0x00198edf3c000000 0xbaff9f3c70000000 0xdd7fcf9e38000000

def z1656 : W := mkw 0xc1aabfc463fff630 0x60d55fe231fffb18 0x85001fc073fffe39 0x42800fe039ffff1c

def z1657 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0x7effe03fcff01fe7 0xbf7ff01fe7f80ff3

def z1658 : W := mkw 0x22f77ffffc04400c 0x117bbffffe022006 0xfafffffffc006006 0xfd7ffffffe003003

def z1659 : W := mkw 0x00e77ed218112000 0x0073bf690c089000 0xfffffff27cf3e127 0xfffffff93e79f093

def z1660 : W := mkw 0x02f77ffffc112000 0x017bbffffe089000 0xfbfffffffc03e000 0xfdfffffffe01f000

def z1661 : W := mkw 0xe011013e78009f3d 0x7008809f3c004f9e 0x0400003c70001e38 0x8200001e38000f1c

def z1662 : W := mkw 0x02f77ffffc044000 0x017bbffffe022000 0xfbfffffffc0c6000 0xfdfffffffe063000

def z1663 : W := mkw 0x0045401200000000 0x0022a00900000000 0x7affe03200000000 0xbd7ff01900000000

def z1664 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x9fff9830730c1839 0xcfffcc1839860c1c

def z1665 : W := mkw 0x005dc03b03e01d81 0x802ee01d81f00ec0 0xffffe0ff83f07fc1 0xfffff07fc1f83fe0

def z1666 : W := mkw 0x82f77ffffc008220 0x417bbffffe004110 0xfefffffffc000620 0xff7ffffffe000310

def z1667 : W := mkw 0xd1a23fc4e41fe272 0x68d11fe2720ff139 0x81001fc07c0fe03e 0x40800fe03e07f01f

def z1668 : W := mkw 0x02f75cbb38000000 0x017bae5d9c000000 0x12ff983fb0000000 0x897fcc1fd8000000

def z1669 : W := mkw 0x0108800003ff6000 0x0084400001ffb000 0x6900600003ffe001 0x3480300001fff000

def z1670 : W := mkw 0x90e67fc4c411a262 0x48733fe26208d131 0xfaffffcd80b386c0 0x7d7fffe6c059c360

def z1671 : W := mkw 0x22f75cbb3804400c 0x117bae5d9c022006 0x93ff98f07c0c603e 0x49ffcc783e06301f

def z1672 : W := mkw 0xe211013ffc009f3d 0x7108809ffe004f9e 0x0400003ffc001f3e 0x8200001ffe000f9f

def z1673 : W := mkw 0x0055403b00000000 0x002aa01d80000000 0x7affe03f807001c0 0xbd7ff01fc03800e0

def z1674 : W := mkw 0xc238152de68a9630 0x611c0a96f3454b18 0xbf781f3df38f9e39 0xdfbc0f9ef9c7cf1c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z9,z10,z6]),(0,[z0,z1,z2,z3,z11,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z12]),(1,[z0,z1,z2,z3,z13,z14])],[(0,[z0,z1,z2,z3,z15,z4,z6])],[(0,[z0,z16,z1,z2,z3,z4,z6]),(1,[z0,z17,z2,z3,z4,z6])],[(0,[z0,z1,z18,z3,z19,z4,z6]),(0,[z0,z20,z1,z3,z4,z6,z21]),(0,[z0,z1,z22,z23,z3,z4,z6])],[(0,[z24,z0,z1,z2,z3,z4,z25]),(0,[z24,z0,z26,z1,z3,z4,z6]),(0,[z0,z27,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z28])],[(0,[z0,z1,z29,z2,z3,z4,z6]),(0,[z30,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z31,z4,z6]),(0,[z0,z1,z2,z3,z32,z4,z6]),(0,[z0,z1,z2,z3,z33,z4,z6]),(0,[z0,z34,z1,z2,z3,z4,z14])],[(0,[z0,z1,z2,z3,z35,z4,z6]),(0,[z36,z0,z37,z1,z3,z4,z6]),(0,[z38,z0,z37,z1,z3,z4,z6]),(0,[z0,z1,z2,z39,z3,z4,z6]),(0,[z0,z1,z2,z3,z40,z4,z6])],[],[(0,[z41,z42,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z43,z6]),(0,[z0,z1,z2,z3,z4,z6,z44]),(1,[z45,z1,z2,z3,z4,z6]),(0,[z46,z0,z1,z2,z3,z4,z6])],[(0,[z47,z0,z2,z3,z4,z48,z6]),(0,[z0,z49,z50,z1,z3,z4,z6]),(1,[z1,z2,z3,z51,z4,z6])],[(0,[z52,z0,z1,z3,z53,z4,z6]),(0,[z0,z1,z2,z3,z54,z4,z6]),(0,[z0,z26,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z56,z4,z6,z57])],[(0,[z52,z0,z1,z3,z4,z6,z14]),(0,[z0,z1,z2,z3,z4,z58,z6]),(0,[z59,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z60,z2,z3,z4,z6]),(0,[z0,z61,z1,z62,z3,z4,z6]),(0,[z0,z1,z62,z18,z3,z4,z6]),(0,[z0,z1,z2,z63,z3,z4,z6])],[(0,[z0,z1,z64,z2,z3,z4,z6]),(0,[z65,z0,z26,z1,z3,z4,z6]),(0,[z66,z1,z2,z3,z4,z67,z6])],[(0,[z24,z68,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z69,z6])]],
   [[(1,[z0,z1,z3,z70,z4,z6]),(0,[z71,z0,z26,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z72,z4,z6]),(0,[z38,z0,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z6])],[(0,[z0,z74,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z75,z4,z6]),(1,[z0,z76,z2,z3,z4,z6])],[(1,[z41,z77,z2,z3,z4,z6]),(0,[z0,z26,z77,z2,z3,z4,z6]),(1,[z0,z1,z78,z3,z4,z6]),(0,[z0,z50,z1,z2,z3,z4,z6]),(0,[z79,z0,z1,z2,z3,z4,z6])],[(0,[z80,z0,z26,z1,z3,z4,z6]),(1,[z81,z0,z1,z3,z4,z6]),(0,[z46,z0,z1,z82,z3,z4,z6])],[(0,[z52,z0,z1,z83,z3,z4,z6]),(0,[z0,z1,z2,z3,z84,z4,z6]),(0,[z0,z1,z85,z2,z3,z4,z6]),(0,[z0,z86,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z3,z56,z4,z6]),(0,[z0,z1,z62,z3,z4,z67,z6])],[(1,[z0,z87,z2,z3,z4,z6]),(0,[z88,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z89,z3,z4,z6]),(0,[z90,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z91,z3,z4,z6]),(0,[z0,z1,z2,z92,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z93,z6]),(0,[z0,z1,z3,z4,z67,z55,z6]),(0,[z0,z1,z2,z3,z94,z4,z6]),(0,[z95,z0,z1,z2,z3,z4,z6])],[(0,[z52,z96,z0,z1,z3,z4,z6]),(0,[z24,z0,z1,z2,z97,z4,z6]),(0,[z0,z1,z98,z2,z3,z4,z6]),(0,[z99,z0,z1,z3,z4,z6,z100]),(0,[z0,z101,z1,z2,z3,z4,z6])],[(1,[z0,z1,z62,z3,z102,z6]),(0,[z0,z1,z2,z103,z3,z4,z6])],[(1,[z0,z104,z1,z3,z4,z6])],[(1,[z0,z1,z3,z4,z105,z6])],[(0,[z42,z68,z0,z1,z3,z4,z6])],[(0,[z106,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z107,z6]),(0,[z0,z1,z2,z108,z3,z4,z6])],[]],
   [[(0,[z0,z109,z1,z2,z3,z4,z6]),(0,[z0,z110,z1,z2,z3,z4,z6])],[(0,[z0,z1,z111,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z112,z4,z6])],[(0,[z0,z1,z113,z2,z3,z4,z6]),(0,[z0,z37,z1,z3,z4,z6,z100]),(0,[z114,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z115,z2,z3,z4,z6])],[(0,[z0,z1,z116,z2,z3,z4,z6]),(0,[z117,z42,z0,z1,z3,z4,z6]),(0,[z42,z0,z34,z1,z3,z4,z6]),(0,[z42,z0,z1,z118,z3,z4,z6]),(0,[z0,z26,z1,z3,z4,z67,z6]),(0,[z0,z37,z1,z18,z3,z4,z6])],[(0,[z42,z0,z1,z3,z4,z119,z6]),(0,[z0,z1,z2,z3,z4,z120,z6]),(0,[z0,z1,z2,z3,z4,z6,z121])],[(0,[z0,z1,z2,z3,z4,z122,z6]),(0,[z123,z0,z1,z62,z3,z4,z6])],[(0,[z0,z1,z3,z4,z10,z67,z6]),(0,[z124,z0,z1,z2,z3,z4,z6])],[(0,[z0,z2,z3,z53,z4,z10,z6]),(0,[z0,z1,z2,z125,z3,z4,z6]),(0,[z126,z0,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z127,z3,z4,z6]),(0,[z128,z0,z1,z2,z3,z4,z6]),(0,[z129,z0,z37,z1,z3,z4,z6]),(1,[z0,z1,z130,z3,z4,z6])],[(0,[z131,z0,z1,z2,z3,z4,z6]),(0,[z132,z0,z1,z2,z3,z4,z6]),(0,[z0,z50,z1,z2,z3,z133,z6])],[(0,[z24,z0,z1,z2,z3,z134,z6])],[(0,[z0,z37,z1,z3,z4,z67,z6]),(0,[z0,z1,z83,z3,z4,z67,z6]),(1,[z0,z1,z62,z3,z4,z6]),(0,[z0,z1,z62,z135,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z136,z6]),(0,[z0,z137,z1,z3,z4,z67,z6]),(0,[z138,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z62,z23,z3,z4,z6])],[(1,[z139,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z140])],[],[(0,[z0,z1,z2,z141,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z142])]],
   [[(0,[z46,z0,z1,z2,z3,z4,z100])],[(0,[z96,z1,z2,z143,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z2,z3,z144,z4,z6]),(0,[z0,z1,z145,z146,z3,z4,z6])],[(0,[z147,z0,z1,z2,z3,z4,z6]),(0,[z52,z0,z26,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z148,z6]),(0,[z0,z1,z2,z149,z3,z4,z6]),(0,[z150,z0,z26,z2,z3,z4,z6]),(1,[z0,z2,z3,z4,z151,z6])],[(0,[z52,z0,z1,z3,z134,z4,z6]),(0,[z38,z0,z1,z3,z4,z6,z57]),(0,[z0,z152,z2,z3,z4,z6,z57])],[(0,[z0,z1,z2,z143,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z153,z6]),(0,[z0,z26,z1,z3,z72,z4,z6])],[(0,[z0,z1,z2,z154,z3,z4,z6])],[(0,[z24,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z155,z6])],[(0,[z0,z156,z37,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z157]),(0,[z0,z1,z2,z158,z3,z4,z6])],[(0,[z159,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z160,z2,z3,z4,z6]),(0,[z0,z50,z1,z2,z3,z10,z6])],[],[(0,[z0,z1,z2,z3,z161,z4,z6]),(0,[z0,z1,z78,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z162,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z163]),(0,[z0,z26,z1,z23,z3,z4,z6]),(0,[z0,z1,z2,z164,z3,z4,z6]),(0,[z0,z1,z62,z165,z3,z4,z6]),(0,[z0,z1,z2,z3,z166,z4,z6])],[(0,[z42,z0,z1,z3,z4,z167,z6]),(0,[z52,z38,z0,z1,z3,z4,z6]),(1,[z168,z0,z2,z3,z4,z6])],[(0,[z42,z0,z1,z3,z169,z4,z6])],[(0,[z0,z37,z1,z62,z3,z4,z6])],[(0,[z170,z0,z1,z62,z3,z4,z6]),(0,[z0,z137,z83,z2,z3,z4,z6]),(0,[z171,z52,z0,z1,z3,z4,z6]),(1,[z0,z2,z3,z172,z4,z6]),(0,[z0,z173,z1,z3,z4,z6,z174]),(0,[z0,z34,z1,z62,z3,z4,z6]),(0,[z171,z0,z1,z22,z3,z4,z6]),(0,[z175,z0,z1,z2,z3,z4,z6]),(0,[z46,z0,z176,z2,z3,z4,z6])],[(0,[z177,z0,z1,z2,z3,z4,z6]),(0,[z41,z0,z26,z1,z3,z4,z6]),(0,[z0,z156,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z178]),(0,[z0,z1,z2,z3,z179,z4,z6]),(0,[z65,z0,z1,z2,z3,z4,z6]),(0,[z180,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z52,z0,z1,z3,z181,z4,z6]),(0,[z0,z1,z2,z3,z4,z182,z6]),(0,[z0,z183,z1,z3,z4,z10,z6])],[(0,[z0,z1,z2,z3,z184,z4,z6]),(0,[z0,z26,z1,z185,z3,z4,z6]),(0,[z150,z0,z26,z1,z3,z4,z6]),(0,[z0,z37,z1,z135,z3,z4,z6]),(0,[z0,z1,z62,z3,z4,z55,z6]),(0,[z0,z1,z2,z3,z186,z4,z6])],[(0,[z171,z42,z0,z1,z3,z4,z6]),(0,[z0,z37,z1,z23,z3,z4,z6]),(1,[z0,z1,z187,z3,z4,z6])],[(0,[z52,z0,z1,z3,z188,z4,z6]),(0,[z189,z0,z190,z2,z3,z4,z6])],[(0,[z52,z0,z61,z1,z3,z4,z6])],[(0,[z0,z1,z191,z2,z3,z4,z6]),(0,[z46,z0,z37,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z192,z10,z6])],[(0,[z193,z41,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z194]),(0,[z0,z34,z1,z2,z135,z3,z4]),(0,[z0,z1,z195,z2,z3,z4,z6])],[(1,[z0,z1,z196,z3,z4,z6]),(0,[z0,z1,z62,z3,z4,z4,z6]),(0,[z197,z0,z1,z2,z3,z4,z6]),(0,[z189,z0,z1,z198,z3,z4,z6])],[(0,[z199,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z200,z3,z4,z6])],[(0,[z201,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z202]),(0,[z0,z1,z76,z2,z3,z4,z6]),(1,[z0,z1,z3,z4,z6,z203])],[(0,[z0,z1,z62,z143,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z204])],[(0,[z0,z2,z143,z3,z172,z4,z6]),(0,[z0,z205,z1,z2,z3,z4,z6])],[(0,[z36,z41,z0,z2,z3,z4,z6]),(0,[z0,z83,z2,z3,z4,z167,z6]),(0,[z36,z0,z2,z3,z4,z10,z6]),(0,[z0,z1,z2,z3,z4,z6,z21]),(0,[z0,z1,z2,z3,z206,z4,z6]),(0,[z0,z45,z1,z2,z3,z4,z6])],[(0,[z0,z1,z207,z2,z3,z4,z6]),(0,[z208,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z51,z4,z6]),(0,[z0,z1,z2,z209,z3,z4,z6])],[(0,[z0,z1,z143,z3,z70,z4,z6]),(0,[z0,z37,z1,z3,z210,z4,z6]),(0,[z211,z0,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z3,z212,z4,z6]),(0,[z0,z213,z26,z1,z3,z4,z6]),(0,[z0,z1,z214,z2,z3,z4,z6])]],
   [[(0,[z42,z1,z2,z141,z3,z4,z6]),(0,[z0,z1,z2,z3,z215,z4,z6]),(0,[z0,z61,z83,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z216,z4,z6]),(0,[z0,z1,z217,z2,z3,z4,z6])],[(0,[z52,z0,z137,z1,z3,z4,z6]),(0,[z0,z218,z1,z2,z3,z4,z6]),(0,[z36,z0,z50,z2,z3,z4,z6])],[(0,[z52,z0,z1,z77,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z219,z6]),(0,[z0,z220,z1,z2,z3,z4,z6])],[(0,[z0,z26,z1,z141,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z221,z6]),(0,[z0,z222,z1,z2,z3,z4,z6]),(1,[z0,z1,z223,z3,z4,z224])],[],[(0,[z0,z225,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z226]),(0,[z0,z1,z2,z3,z227,z4,z6])],[(0,[z41,z0,z2,z3,z4,z167,z6]),(0,[z123,z0,z1,z3,z4,z67,z6]),(0,[z189,z0,z76,z2,z3,z4,z6])],[(0,[z0,z37,z1,z3,z4,z55,z6]),(0,[z0,z1,z2,z3,z4,z10,z6])],[(0,[z0,z26,z1,z143,z3,z4,z6]),(0,[z0,z1,z228,z143,z3,z4,z6]),(0,[z117,z0,z26,z1,z3,z4,z6]),(1,[z36,z0,z2,z3,z4,z21]),(0,[z0,z1,z2,z229,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z230]),(0,[z0,z1,z2,z3,z4,z231,z6]),(1,[z0,z232,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z233,z4,z6]),(0,[z234,z68,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z235,z3,z4,z6]),(0,[z236,z0,z1,z2,z3,z4,z6])],[(0,[z237,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z238])],[(0,[z52,z0,z37,z1,z3,z4,z6]),(1,[z117,z1,z2,z3,z4,z239]),(0,[z0,z240,z26,z1,z3,z4,z6]),(0,[z150,z0,z1,z241,z3,z4,z6]),(0,[z242,z0,z1,z3,z4,z67,z6])],[(0,[z0,z1,z2,z243,z3,z4,z6]),(1,[z0,z1,z3,z4,z67,z6])],[(0,[z0,z104,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z244]),(0,[z0,z1,z2,z3,z245,z4,z6])],[(0,[z170,z0,z77,z2,z3,z4,z6]),(0,[z0,z26,z2,z3,z133,z4,z6]),(0,[z246,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z247,z4]),(0,[z248,z0,z1,z2,z3,z4,z6])],[(0,[z52,z0,z1,z3,z4,z249,z6]),(0,[z0,z2,z3,z53,z4,z6,z21]),(0,[z250,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z37,z1,z143,z3,z4,z6]),(0,[z251,z0,z1,z2,z3,z4,z6]),(1,[z0,z26,z61,z3,z4,z6]),(1,[z150,z0,z26,z3,z4,z6]),(0,[z0,z61,z1,z2,z18,z4,z6]),(0,[z252,z0,z1,z2,z3,z4,z6]),(1,[z0,z253,z2,z3,z4,z6])],[(0,[z52,z0,z1,z3,z102,z4,z6]),(0,[z0,z1,z214,z3,z133,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z254]),(0,[z0,z1,z2,z127,z3,z212,z6])],[(0,[z255,z0,z1,z2,z3,z4,z6])],[(0,[z52,z0,z1,z2,z3,z4,z6]),(1,[z66,z0,z1,z3,z4,z6])],[(1,[z0,z1,z256,z3,z4,z6]),(0,[z36,z0,z34,z2,z3,z4,z6])],[(0,[z257,z0,z1,z2,z3,z4,z6]),(0,[z117,z0,z1,z2,z3,z4,z174]),(0,[z0,z2,z18,z3,z53,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z258]),(0,[z259,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z223,z62,z3,z4,z6])],[(0,[z0,z1,z2,z3,z53,z4,z6])],[(0,[z260,z0,z1,z2,z3,z4,z6]),(0,[z0,z261,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z262]),(0,[z0,z1,z2,z3,z4,z6,z14])],[(0,[z263,z0,z1,z2,z3,z4,z6]),(0,[z264,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z146,z3,z4,z14])],[(0,[z265,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z266,z4,z6]),(0,[z0,z2,z3,z4,z6,z267,z100])],[(0,[z0,z1,z2,z3,z268,z4,z6]),(0,[z96,z0,z1,z62,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z269,z6])],[(0,[z0,z1,z2,z3,z4,z270,z6]),(0,[z52,z36,z0,z1,z3,z4,z6]),(0,[z24,z0,z271,z2,z3,z4,z6])],[(0,[z42,z0,z1,z3,z4,z6,z174]),(0,[z0,z26,z2,z118,z3,z4,z6])],[(0,[z0,z1,z2,z272,z3,z4,z6]),(0,[z52,z0,z1,z3,z4,z239,z6]),(0,[z273,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z62,z3,z4,z10,z6]),(0,[z274,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z181,z4,z119])],[],[(0,[z170,z0,z1,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z275,z4,z6]),(0,[z0,z1,z2,z3,z276,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z277]),(0,[z0,z34,z1,z3,z4,z67,z6]),(0,[z46,z95,z1,z2,z3,z4,z6])]],
   [[(0,[z114,z0,z1,z2,z3,z53,z4])],[(0,[z278,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z279]),(0,[z24,z0,z37,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z55,z6,z14]),(0,[z0,z17,z2,z146,z3,z4,z6]),(1,[z0,z1,z145,z3,z4,z6])],[(1,[z0,z280,z1,z3,z4,z6]),(0,[z281,z0,z1,z2,z3,z4,z6]),(0,[z150,z0,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z3,z4,z6,z100]),(0,[z0,z1,z2,z3,z282,z4,z6]),(0,[z0,z1,z2,z3,z283,z4,z6]),(0,[z0,z1,z2,z135,z4,z119,z6]),(0,[z0,z1,z2,z3,z4,z6,z284])],[(0,[z285,z0,z1,z2,z3,z4,z6]),(0,[z42,z0,z1,z18,z3,z4,z6]),(0,[z0,z1,z2,z3,z286,z4,z6]),(1,[z0,z1,z89,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z287]),(0,[z0,z1,z2,z3,z4,z288,z6]),(0,[z0,z1,z2,z3,z289,z4,z6])],[(0,[z0,z1,z2,z3,z4,z290,z6]),(0,[z52,z0,z1,z3,z133,z4,z6]),(0,[z24,z1,z185,z2,z3,z4,z6]),(0,[z0,z1,z3,z188,z4,z67,z6]),(0,[z0,z1,z2,z3,z4,z6,z291]),(0,[z0,z20,z1,z2,z3,z4,z6]),(0,[z0,z292,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z293,z4,z6]),(0,[z0,z1,z2,z3,z172,z4,z6]),(0,[z0,z1,z2,z3,z4,z294,z6]),(0,[z0,z1,z2,z3,z181,z4,z174])],[(0,[z52,z0,z1,z223,z3,z4,z6]),(1,[z0,z1,z3,z295,z4,z6]),(0,[z0,z26,z1,z22,z3,z4,z6]),(0,[z0,z1,z2,z296,z3,z4,z6]),(0,[z297,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z127,z212,z4,z6]),(0,[z46,z0,z1,z2,z3,z298,z6])],[(0,[z299,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z300,z133,z4])],[(0,[z0,z1,z2,z3,z4,z301,z6]),(0,[z0,z1,z2,z302,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z303]),(0,[z0,z1,z3,z4,z67,z6,z202]),(0,[z0,z220,z2,z3,z4,z67,z6]),(0,[z0,z1,z223,z2,z3,z4,z224])],[(1,[z0,z304,z2,z3,z4,z6])],[(0,[z0,z26,z1,z3,z4,z10,z6]),(0,[z0,z1,z305,z2,z3,z4,z6]),(0,[z0,z1,z3,z212,z4,z306,z6])],[(0,[z307,z52,z0,z1,z3,z4,z6]),(0,[z0,z110,z2,z143,z3,z4,z6]),(0,[z0,z1,z2,z3,z308,z4,z6]),(0,[z71,z0,z37,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z247,z4,z6]),(0,[z0,z1,z3,z4,z67,z6,z21])],[(0,[z0,z1,z309,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z181,z4,z100])],[(0,[z42,z0,z104,z1,z3,z4,z6])],[(0,[z52,z170,z0,z1,z3,z4,z6]),(0,[z80,z0,z37,z1,z3,z4,z6]),(0,[z310,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z311,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z96,z0,z1,z2,z143,z4,z6]),(0,[z0,z213,z1,z2,z3,z4,z6]),(0,[z0,z37,z83,z2,z3,z4,z6])],[(0,[z1,z185,z2,z141,z3,z4,z6]),(0,[z0,z1,z18,z3,z4,z67,z6])],[],[(0,[z312,z0,z1,z2,z3,z4,z6])],[(0,[z71,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z313,z4,z6]),(0,[z36,z0,z2,z3,z4,z6,z21]),(0,[z314,z0,z1,z2,z3,z4,z6])],[(0,[z41,z0,z61,z2,z3,z4,z6]),(0,[z0,z1,z315,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z316,z6]),(0,[z317,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z318,z2,z3,z4,z6])],[(0,[z0,z205,z37,z1,z3,z4,z6])],[(0,[z42,z0,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z319,z6]),(0,[z80,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z320,z2,z3,z4,z6]),(0,[z0,z1,z2,z146,z3,z212,z6])],[(0,[z0,z1,z62,z141,z3,z4,z6]),(0,[z0,z1,z3,z134,z4,z105,z6]),(1,[z38,z0,z1,z3,z4,z57])],[(0,[z0,z1,z321,z2,z3,z4,z6]),(1,[z0,z1,z228,z3,z4,z6]),(0,[z150,z0,z1,z2,z3,z133,z6]),(0,[z0,z1,z2,z322,z3,z4,z6]),(0,[z0,z1,z2,z323,z3,z4,z6])],[(0,[z324,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z325,z6]),(0,[z0,z1,z2,z326,z3,z4,z6]),(0,[z0,z26,z1,z3,z53,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z238])],[(0,[z0,z26,z1,z3,z4,z6,z14])],[(0,[z0,z37,z1,z185,z3,z4,z6]),(0,[z0,z240,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z306,z6])],[(1,[z0,z232,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z134,z4,z6]),(0,[z0,z327,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z62,z3,z4,z6]),(1,[z0,z328,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z329])],[(0,[z139,z52,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z330,z3,z4,z6])]],
   [[(0,[z0,z77,z2,z3,z4,z10,z6])],[(0,[z0,z1,z331,z2,z3,z4,z6]),(0,[z42,z0,z1,z146,z3,z4,z6]),(0,[z52,z0,z1,z3,z4,z224,z6]),(0,[z0,z1,z87,z2,z3,z4,z6])],[(0,[z42,z0,z1,z135,z3,z4,z6]),(0,[z332,z0,z2,z3,z53,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z333]),(0,[z0,z328,z1,z62,z3,z4,z6])],[(0,[z42,z0,z1,z23,z3,z4,z6]),(0,[z334,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z146,z3,z181])],[(0,[z335,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z3,z53,z4,z67,z6])],[(0,[z0,z1,z2,z3,z4,z336,z6]),(0,[z337,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z338]),(0,[z0,z1,z223,z3,z4,z67,z6])],[(0,[z0,z1,z3,z4,z67,z6,z14])],[(0,[z68,z1,z2,z3,z134,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z339]),(0,[z150,z0,z1,z2,z3,z10,z6])],[(0,[z0,z340,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z341,z6])],[(0,[z0,z1,z143,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z4,z192,z6]),(0,[z0,z1,z2,z3,z181,z4,z6])],[(0,[z96,z0,z1,z3,z4,z67,z6]),(0,[z0,z1,z3,z4,z48,z67,z6]),(0,[z0,z342,z1,z2,z3,z4,z6]),(0,[z0,z1,z343,z2,z3,z4,z6]),(1,[z66,z1,z3,z4,z67,z6]),(0,[z189,z0,z1,z2,z3,z212,z6])],[(0,[z0,z1,z127,z3,z4,z67,z6])],[(0,[z0,z1,z2,z3,z188,z4,z6]),(0,[z0,z1,z23,z3,z4,z67,z6])],[(0,[z0,z37,z1,z141,z3,z4,z6]),(0,[z0,z1,z2,z3,z344,z4,z6])],[(1,[z42,z96,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z345,z6]),(0,[z0,z1,z62,z323,z3,z4,z6])]],
   [[(0,[z0,z50,z2,z3,z53,z4,z6])],[(0,[z189,z0,z1,z3,z4,z67,z6])],[(0,[z52,z1,z185,z2,z3,z4,z6]),(1,[z0,z220,z3,z4,z67,z6]),(0,[z0,z1,z2,z346,z3,z4,z6])],[(0,[z52,z0,z1,z3,z4,z48,z6]),(0,[z47,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z347,z3,z4,z6])],[(0,[z80,z0,z1,z2,z188,z4,z6]),(0,[z0,z1,z2,z3,z348,z4,z6])],[(0,[z0,z137,z1,z154,z3,z4,z6]),(0,[z349,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z350,z4,z6]),(0,[z0,z1,z2,z3,z4,z351,z6]),(0,[z352,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z62,z3,z4,z6,z21])],[(0,[z0,z183,z1,z2,z3,z4,z6])],[(0,[z0,z353,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z14]),(1,[z0,z2,z3,z354,z4,z6]),(0,[z0,z1,z2,z3,z355,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z356])],[(0,[z42,z0,z1,z3,z4,z55,z6]),(0,[z0,z232,z1,z2,z3,z4,z6]),(0,[z68,z1,z2,z3,z188,z4,z6]),(0,[z0,z1,z2,z3,z4,z357,z6]),(0,[z358,z0,z1,z2,z3,z4,z6])],[(0,[z359,z0,z1,z3,z188,z4,z6]),(1,[z128,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z67,z301,z6])],[(0,[z170,z0,z2,z3,z133,z4,z6]),(0,[z0,z1,z2,z3,z360,z4,z6])],[(0,[z41,z0,z37,z1,z3,z4,z6])],[(0,[z1,z185,z2,z3,z188,z4,z6]),(0,[z0,z1,z185,z62,z3,z4,z6]),(0,[z0,z1,z2,z3,z361,z4,z6]),(0,[z0,z1,z2,z3,z4,z362,z6])],[(0,[z150,z0,z37,z1,z3,z4,z6]),(0,[z66,z0,z1,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z4,z151,z6]),(1,[z0,z1,z2,z3,z4,z363]),(0,[z0,z1,z364,z2,z3,z4,z6])],[(0,[z52,z41,z0,z1,z3,z4,z6]),(0,[z123,z42,z0,z1,z3,z4,z6]),(0,[z42,z1,z2,z3,z134,z4,z6])],[(0,[z42,z96,z1,z2,z3,z4,z6])]],
   [[(1,[z52,z0,z1,z3,z4,z6]),(0,[z0,z26,z26,z1,z3,z4,z6]),(1,[z124,z1,z2,z3,z4,z6])],[(0,[z0,z26,z1,z3,z134,z4,z6]),(0,[z0,z26,z327,z1,z3,z4,z6]),(0,[z1,z2,z23,z3,z51,z4,z6]),(1,[z189,z0,z1,z2,z55,z6])],[],[(0,[z41,z0,z1,z2,z3,z4,z6]),(0,[z365,z0,z1,z2,z3,z4,z6]),(0,[z52,z0,z50,z1,z3,z4,z6]),(0,[z0,z26,z1,z3,z4,z6,z21]),(0,[z189,z0,z1,z62,z3,z4,z6])],[(1,[z42,z0,z1,z3,z4,z6]),(0,[z0,z366,z1,z2,z3,z4,z6])],[(0,[z367,z0,z1,z2,z3,z4,z6])],[(0,[z52,z0,z1,z304,z3,z4,z6]),(0,[z0,z1,z368,z2,z3,z4,z6])],[(0,[z369,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z67,z319,z6])],[(0,[z52,z0,z1,z3,z56,z4,z6]),(0,[z370,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z371]),(0,[z0,z1,z2,z3,z4,z372,z6]),(0,[z0,z1,z2,z3,z4,z373,z6]),(1,[z0,z1,z374,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z249,z6]),(0,[z68,z0,z1,z2,z3,z48,z6]),(0,[z375,z0,z1,z2,z3,z4,z6]),(0,[z0,z190,z1,z2,z3,z4,z6])],[(0,[z171,z0,z26,z1,z3,z4,z6]),(1,[z376,z1,z2,z3,z4,z6])],[(1,[z193,z0,z1,z3,z4,z6]),(0,[z377,z52,z0,z1,z3,z4,z6]),(0,[z68,z0,z1,z62,z3,z4,z6]),(0,[z0,z1,z2,z378,z3,z4,z6]),(0,[z0,z37,z1,z3,z4,z6,z21]),(0,[z0,z1,z2,z3,z102,z4,z6]),(0,[z0,z1,z2,z379,z3,z4,z6]),(0,[z0,z17,z1,z2,z3,z4,z6])],[(1,[z0,z1,z380,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z174,z14]),(0,[z381,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z382,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z383])],[(0,[z42,z1,z2,z3,z188,z4,z6]),(0,[z0,z2,z3,z4,z384,z6,z174]),(0,[z0,z1,z3,z4,z269,z6,z174]),(0,[z0,z26,z1,z3,z181,z4,z6])],[(0,[z0,z1,z2,z3,z385,z4,z6]),(0,[z42,z0,z1,z3,z4,z67,z6]),(0,[z0,z1,z62,z3,z53,z4,z6])]],
   [[(0,[z52,z68,z0,z1,z3,z4,z6]),(0,[z332,z0,z1,z3,z4,z67,z6]),(0,[z0,z1,z62,z3,z4,z6,z14]),(0,[z386,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z146,z158,z3,z4,z6])],[(0,[z0,z26,z1,z3,z188,z4,z6])],[(0,[z150,z170,z0,z2,z3,z4,z6]),(0,[z0,z37,z1,z22,z3,z4,z6]),(1,[z260,z1,z2,z3,z4,z6])],[(1,[z52,z42,z1,z3,z4,z6]),(0,[z171,z38,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z4,z67,z6]),(0,[z0,z1,z2,z3,z387,z4,z6]),(1,[z99,z0,z1,z3,z4,z6])],[(0,[z0,z1,z388,z2,z3,z4,z6]),(0,[z117,z0,z37,z1,z3,z4,z6])],[],[(0,[z0,z1,z77,z2,z3,z4,z6]),(0,[z24,z42,z1,z2,z3,z4,z6]),(0,[z52,z0,z1,z118,z3,z4,z6]),(0,[z389,z0,z1,z2,z3,z4,z6]),(1,[z0,z26,z3,z53,z4,z6]),(0,[z0,z37,z1,z3,z4,z10,z6]),(1,[z0,z1,z2,z3,z4,z390]),(0,[z0,z1,z2,z82,z3,z4,z6])],[(0,[z170,z42,z0,z1,z3,z4,z6]),(0,[z52,z0,z1,z3,z4,z119,z6]),(0,[z0,z26,z2,z3,z4,z167,z6]),(0,[z0,z1,z2,z3,z4,z6,z391])],[(0,[z0,z1,z2,z3,z4,z6,z392]),(0,[z0,z1,z2,z393,z3,z4,z6])],[(0,[z52,z0,z1,z3,z4,z6,z57]),(0,[z394,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z395])],[(0,[z396,z0,z37,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z247,z53,z4]),(0,[z234,z0,z1,z62,z3,z4,z6])],[(0,[z397,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z398,z3,z4,z6]),(0,[z52,z0,z1,z3,z13,z4,z6]),(0,[z117,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z399,z3,z4,z6]),(0,[z36,z0,z1,z3,z4,z67,z6])],[(0,[z0,z1,z2,z3,z4,z6,z400]),(0,[z0,z1,z2,z3,z401,z4,z6]),(1,[z0,z1,z2,z135,z4,z119])],[(0,[z402,z52,z0,z1,z3,z4,z6]),(0,[z0,z403,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z404,z6])],[(1,[z0,z110,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z405]),(1,[z0,z1,z3,z4,z6,z142])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z406])],[],[(1,[z0,z1,z3,z4,z290,z6]),(0,[z0,z2,z3,z4,z153,z48,z6]),(0,[z147,z68,z0,z1,z3,z4,z6]),(0,[z396,z0,z1,z2,z3,z4,z6]),(0,[z407,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z408,z2,z3,z4,z6]),(0,[z332,z0,z1,z62,z3,z4,z6]),(0,[z0,z1,z409,z2,z3,z4,z6]),(0,[z0,z1,z2,z410,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z411])],[],[(1,[z170,z137,z2,z3,z4,z6]),(0,[z42,z42,z0,z1,z3,z4,z6]),(0,[z0,z1,z412,z2,z3,z4,z6]),(0,[z0,z1,z2,z146,z3,z181,z6])],[(0,[z41,z0,z137,z2,z3,z4,z6]),(1,[z0,z1,z154,z3,z4,z6]),(0,[z0,z26,z1,z83,z3,z4,z6]),(0,[z0,z37,z1,z3,z53,z4,z6])],[(1,[z47,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z413,z6]),(0,[z0,z37,z1,z3,z4,z6,z14]),(0,[z0,z1,z2,z3,z414,z4,z6]),(1,[z0,z61,z2,z18,z4,z6])],[(0,[z0,z1,z146,z130,z3,z4,z6])],[(0,[z0,z61,z2,z18,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z415,z6])],[(0,[z0,z1,z256,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z416])],[],[(0,[z0,z1,z253,z2,z3,z4,z6])],[(0,[z0,z417,z1,z2,z3,z4,z6]),(0,[z0,z240,z50,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z418,z6]),(0,[z0,z1,z368,z3,z13,z4,z6])],[(0,[z42,z0,z1,z185,z3,z4,z6]),(0,[z0,z1,z185,z3,z4,z67,z6]),(1,[z0,z26,z37,z3,z4,z6]),(0,[z0,z37,z1,z83,z3,z4,z6])],[(0,[z36,z0,z1,z62,z3,z4,z6]),(0,[z38,z0,z1,z62,z3,z4,z6])],[(0,[z1,z185,z2,z3,z134,z4,z6]),(0,[z0,z26,z1,z3,z102,z4,z6]),(0,[z419,z0,z37,z1,z3,z4,z6]),(1,[z0,z1,z2,z3,z300,z4]),(0,[z0,z1,z2,z3,z420,z4,z6]),(0,[z0,z1,z2,z3,z421,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z422]),(0,[z0,z50,z1,z62,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z203,z100])],[(0,[z0,z1,z2,z3,z4,z6,z423]),(1,[z0,z1,z364,z3,z4,z6])],[(0,[z0,z61,z1,z2,z53,z4,z6]),(1,[z114,z0,z1,z2,z3,z4])],[(0,[z123,z0,z26,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z424]),(0,[z38,z0,z1,z23,z3,z4,z6]),(0,[z46,z0,z1,z2,z3,z155,z6]),(0,[z0,z1,z2,z3,z425,z4,z6])],[(0,[z0,z1,z2,z3,z4,z426,z6]),(1,[z0,z1,z2,z31,z4,z6]),(0,[z0,z1,z2,z3,z427,z4,z6]),(0,[z0,z1,z62,z2,z3,z67,z6]),(0,[z0,z1,z2,z3,z428,z4,z6]),(0,[z0,z1,z2,z429,z3,z4,z6])],[(1,[z129,z0,z1,z3,z67,z6])],[(0,[z0,z1,z62,z3,z134,z4,z6]),(1,[z0,z1,z3,z4,z6,z194]),(1,[z1,z2,z3,z4,z9,z6]),(0,[z36,z0,z1,z2,z135,z3,z4]),(0,[z0,z1,z2,z3,z4,z430,z6])],[(1,[z68,z1,z2,z3,z134,z6]),(0,[z419,z0,z1,z2,z3,z4,z6])],[(0,[z431,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z432,z6]),(0,[z0,z433,z1,z3,z53,z4,z6]),(0,[z0,z1,z2,z3,z434,z4,z6]),(0,[z0,z1,z196,z2,z3,z4,z6]),(0,[z0,z1,z3,z56,z4,z67,z6]),(0,[z0,z152,z1,z2,z3,z4,z6])],[(0,[z0,z1,z83,z2,z3,z4,z6]),(0,[z0,z1,z2,z241,z3,z4,z6])],[(0,[z137,z1,z2,z3,z134,z4,z6]),(0,[z0,z1,z2,z435,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z436,z6]),(0,[z0,z1,z223,z22,z3,z4,z6]),(1,[z0,z1,z437,z3,z4,z6])],[(0,[z0,z1,z2,z438,z3,z4,z6]),(1,[z1,z2,z3,z439,z4,z6]),(0,[z171,z0,z1,z2,z3,z4,z6]),(0,[z369,z1,z2,z23,z3,z4,z6]),(0,[z0,z1,z2,z3,z440,z4,z6])],[(0,[z0,z1,z441,z2,z3,z4,z6]),(0,[z68,z0,z1,z3,z4,z67,z6]),(0,[z0,z1,z442,z2,z3,z4,z6]),(0,[z129,z0,z1,z3,z4,z67,z6]),(0,[z0,z1,z3,z13,z443,z4,z6])],[(0,[z444,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z445,z6]),(0,[z0,z1,z22,z2,z3,z4,z6]),(0,[z0,z446,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z447,z3,z4,z6])],[(0,[z42,z0,z1,z141,z3,z4,z6]),(0,[z24,z0,z87,z2,z3,z4,z6])]],
   [[(0,[z448,z42,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z449,z6]),(0,[z0,z26,z1,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z450,z6])],[(0,[z150,z41,z0,z2,z3,z4,z6]),(0,[z150,z0,z2,z3,z4,z10,z6])],[(0,[z52,z0,z1,z3,z212,z4,z6]),(0,[z0,z451,z2,z23,z3,z4,z6]),(0,[z38,z0,z1,z2,z3,z4,z224]),(0,[z189,z0,z1,z2,z3,z4,z363])],[(0,[z52,z42,z1,z2,z3,z4,z6]),(0,[z0,z26,z1,z3,z4,z6,z405]),(0,[z0,z1,z62,z3,z181,z4,z6])],[(0,[z170,z41,z1,z2,z3,z4,z6]),(0,[z42,z0,z1,z143,z3,z4,z6]),(1,[z52,z0,z304,z3,z4,z6]),(1,[z419,z0,z1,z3,z4,z6])],[(0,[z189,z52,z0,z1,z3,z4,z6]),(0,[z0,z1,z304,z2,z3,z4,z6]),(0,[z452,z0,z1,z2,z3,z4,z6]),(0,[z126,z0,z1,z62,z3,z4,z6]),(0,[z189,z124,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z453,z4,z6])],[(0,[z454,z42,z0,z1,z3,z4,z6]),(0,[z0,z1,z62,z3,z188,z4,z6]),(0,[z455,z0,z1,z2,z3,z4,z6]),(0,[z0,z26,z61,z2,z3,z4,z6]),(0,[z150,z0,z50,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z456])],[(0,[z0,z1,z2,z3,z457,z4,z6]),(0,[z0,z1,z3,z4,z67,z239,z6]),(0,[z0,z451,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z458,z6])],[(0,[z0,z459,z26,z1,z3,z4,z6])],[(0,[z189,z42,z0,z1,z3,z4,z6]),(0,[z460,z0,z26,z1,z3,z4,z6]),(0,[z461,z0,z1,z2,z3,z4,z6])],[(0,[z137,z1,z2,z3,z188,z4,z6]),(1,[z0,z26,z137,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z462]),(0,[z96,z1,z2,z3,z4,z48,z6]),(0,[z0,z1,z3,z4,z167,z6,z416]),(0,[z46,z45,z1,z2,z3,z4,z6])],[],[(0,[z170,z0,z26,z1,z3,z4,z6]),(0,[z0,z1,z2,z463,z3,z4,z6]),(0,[z0,z37,z1,z3,z134,z4,z6]),(0,[z0,z61,z1,z2,z3,z4,z6]),(0,[z0,z376,z1,z2,z3,z4,z6])],[(1,[z0,z464,z1,z3,z4,z6]),(0,[z0,z1,z2,z97,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z48,z6]),(0,[z0,z49,z1,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z465,z4,z6])],[(0,[z170,z137,z1,z2,z3,z4,z6]),(0,[z1,z2,z143,z3,z188,z4,z6]),(0,[z0,z466,z1,z2,z3,z4,z6]),(0,[z129,z0,z1,z62,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z467])],[(0,[z189,z376,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z50,z77,z2,z3,z4,z6]),(0,[z468,z0,z1,z2,z3,z4,z6]),(0,[z189,z0,z1,z2,z127,z4,z6])],[(1,[z147,z0,z1,z3,z4,z6]),(1,[z0,z20,z1,z3,z4,z6])],[(1,[z36,z0,z26,z3,z4,z6]),(0,[z0,z469,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z470,z4,z6])],[(0,[z52,z0,z1,z3,z471,z4,z6]),(0,[z472,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z3,z4,z357,z6]),(0,[z0,z473,z2,z3,z4,z6,z174]),(0,[z0,z26,z61,z1,z3,z4,z6]),(0,[z0,z1,z474,z2,z3,z4,z6]),(0,[z0,z1,z62,z2,z3,z102,z6])],[(1,[z52,z1,z185,z3,z4,z6])],[],[(0,[z0,z1,z475,z62,z3,z4,z6])],[(0,[z52,z0,z34,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z476,z6]),(0,[z0,z37,z1,z3,z181,z4,z6])],[(0,[z0,z1,z2,z3,z4,z239,z6]),(1,[z0,z1,z3,z4,z269,z6]),(0,[z0,z1,z2,z3,z4,z477,z6]),(0,[z189,z0,z1,z2,z4,z55,z6]),(0,[z0,z1,z2,z3,z4,z155,z6])],[(0,[z0,z1,z3,z134,z4,z67,z6]),(0,[z478,z0,z26,z1,z3,z4,z6]),(0,[z0,z1,z146,z3,z4,z67,z6]),(0,[z189,z0,z1,z2,z3,z4,z390])],[(1,[z0,z26,z77,z3,z4,z6]),(0,[z0,z464,z1,z77,z3,z4,z6]),(0,[z479,z0,z1,z2,z3,z4,z6]),(0,[z42,z0,z1,z3,z4,z6,z21]),(0,[z0,z37,z1,z3,z188,z4,z6]),(0,[z359,z0,z1,z2,z3,z4,z6]),(0,[z0,z271,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z480,z4,z6]),(0,[z175,z0,z1,z62,z3,z4,z6])],[(0,[z0,z37,z61,z1,z3,z4,z6]),(0,[z46,z0,z253,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z481,z4,z6]),(0,[z52,z0,z1,z127,z3,z4,z6]),(0,[z0,z1,z3,z4,z239,z6,z194])],[(0,[z193,z42,z0,z1,z3,z4,z6]),(0,[z52,z0,z1,z3,z4,z6,z174]),(1,[z0,z1,z482,z3,z4,z6]),(0,[z483,z0,z1,z2,z3,z4,z6]),(0,[z38,z0,z1,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z4,z484,z6])]],
   [[(1,[z0,z433,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z485,z6]),(0,[z0,z50,z1,z3,z4,z67,z6]),(0,[z0,z1,z22,z3,z4,z6,z57])],[(0,[z0,z26,z137,z1,z3,z4,z6]),(1,[z0,z49,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z133,z4,z6])],[(0,[z0,z26,z1,z77,z3,z4,z6]),(0,[z170,z0,z2,z3,z4,z167,z6]),(0,[z42,z0,z1,z22,z3,z4,z6]),(0,[z0,z34,z2,z3,z4,z167,z6]),(0,[z0,z1,z2,z3,z181,z6,z14]),(0,[z0,z1,z2,z3,z486,z4,z6])],[(0,[z487,z0,z1,z2,z3,z4,z6]),(0,[z332,z52,z0,z1,z3,z4,z6]),(0,[z0,z1,z488,z2,z3,z4,z6]),(0,[z0,z1,z62,z3,z102,z4,z6])],[(0,[z0,z1,z2,z3,z4,z489,z6]),(0,[z490,z0,z1,z2,z3,z4,z6])],[(0,[z52,z0,z1,z3,z4,z6,z100]),(0,[z0,z1,z2,z3,z491,z4,z6]),(0,[z0,z1,z62,z2,z3,z4,z6])],[(0,[z42,z0,z1,z3,z4,z10,z6]),(0,[z492,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z493,z2,z3,z4,z6]),(0,[z332,z42,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z494,z3,z4,z6])],[(0,[z171,z0,z1,z3,z4,z224,z6])],[(0,[z0,z37,z1,z3,z4,z445,z6])],[(0,[z0,z1,z2,z3,z495,z4,z6]),(0,[z46,z0,z1,z62,z3,z4,z6])],[(0,[z0,z26,z37,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z496,z4,z6])],[(0,[z0,z464,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z497,z3,z4,z6]),(0,[z0,z1,z498,z2,z3,z4,z6]),(1,[z150,z0,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z4,z499,z6])],[],[(0,[z0,z1,z2,z3,z4,z500,z6]),(0,[z260,z1,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z167,z6])]],
   [[(0,[z0,z1,z2,z3,z501,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z502]),(0,[z0,z1,z62,z3,z4,z239,z6]),(0,[z0,z1,z2,z118,z3,z4,z6]),(0,[z0,z1,z3,z133,z4,z499,z6]),(0,[z0,z1,z2,z503,z3,z4,z6])],[(0,[z52,z0,z1,z3,z4,z167,z6]),(0,[z0,z26,z1,z3,z4,z48,z6]),(0,[z123,z1,z2,z3,z4,z6,z174]),(0,[z0,z1,z2,z3,z504,z4,z6]),(0,[z36,z0,z83,z2,z3,z4,z6]),(0,[z171,z0,z1,z2,z23,z4,z6]),(0,[z0,z1,z2,z3,z4,z119,z6])],[(0,[z0,z1,z2,z3,z354,z4,z6])],[(0,[z137,z1,z77,z2,z3,z4,z6]),(0,[z0,z505,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z57]),(0,[z0,z1,z2,z3,z4,z506,z6]),(0,[z507,z0,z1,z2,z3,z4,z6])],[(0,[z36,z42,z0,z1,z3,z4,z6]),(0,[z0,z1,z228,z2,z3,z4,z6]),(0,[z0,z26,z1,z2,z3,z4,z6]),(0,[z0,z1,z22,z2,z23,z4,z6])],[],[(0,[z42,z0,z1,z3,z53,z4,z6]),(0,[z171,z0,z37,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z508,z4,z6]),(0,[z0,z1,z2,z3,z13,z4,z6])],[(0,[z509,z0,z1,z2,z3,z4,z6]),(0,[z42,z0,z1,z3,z4,z6,z14]),(0,[z0,z510,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z212,z4,z55,z6])],[(0,[z42,z0,z1,z511,z3,z4,z6]),(0,[z96,z0,z26,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z9,z6]),(0,[z0,z1,z62,z3,z133,z4,z6]),(1,[z126,z0,z1,z3,z4,z6])],[(0,[z307,z0,z1,z2,z3,z4,z6]),(0,[z0,z459,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z512,z4,z6]),(1,[z0,z1,z22,z23,z4,z6])],[(0,[z96,z137,z1,z2,z3,z4,z6]),(0,[z52,z0,z0,z1,z3,z4,z6]),(0,[z0,z37,z1,z3,z102,z4,z6]),(0,[z0,z1,z513,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z514,z6])],[],[(1,[z0,z1,z2,z3,z4,z25]),(1,[z0,z26,z1,z3,z4,z6]),(0,[z0,z37,z1,z2,z3,z4,z6]),(1,[z0,z1,z3,z4,z306,z6])],[(0,[z0,z137,z1,z2,z3,z4,z6]),(0,[z52,z0,z1,z515,z3,z4,z6]),(0,[z0,z1,z2,z3,z439,z4,z6]),(0,[z0,z1,z223,z2,z3,z4,z57]),(0,[z516,z0,z1,z2,z3,z4,z6])],[(0,[z0,z26,z1,z3,z4,z239,z6]),(0,[z0,z1,z2,z3,z4,z224,z6])],[(1,[z0,z26,z3,z133,z4,z6]),(0,[z189,z0,z1,z437,z3,z4,z6]),(0,[z0,z517,z1,z2,z3,z4,z6])]],
   [[(0,[z518,z0,z1,z2,z3,z4,z6])],[(0,[z52,z0,z1,z62,z3,z4,z6]),(0,[z0,z26,z50,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z519,z4,z6]),(0,[z520,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z521,z4,z6])],[(0,[z96,z68,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z522,z3,z4,z6])],[(0,[z123,z0,z1,z2,z3,z4,z174]),(0,[z0,z26,z1,z399,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z523,z6]),(0,[z52,z0,z1,z146,z3,z4,z6]),(0,[z139,z0,z37,z1,z3,z4,z6]),(0,[z0,z524,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z3,z4,z290,z6]),(0,[z24,z0,z1,z3,z4,z67,z6]),(0,[z0,z525,z26,z1,z3,z4,z6]),(0,[z526,z0,z1,z2,z3,z4,z6]),(1,[z0,z152,z2,z3,z4,z6])],[(0,[z0,z37,z1,z3,z4,z239,z6]),(0,[z0,z26,z1,z3,z133,z4,z6]),(0,[z0,z527,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z528])],[(0,[z0,z83,z2,z3,z53,z4,z6]),(0,[z0,z1,z2,z529,z3,z4,z6])],[(0,[z0,z1,z2,z530,z3,z4,z6]),(0,[z531,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z181,z4,z239]),(0,[z0,z26,z1,z223,z3,z4,z6]),(0,[z0,z1,z3,z532,z4,z67,z6])],[(0,[z0,z1,z2,z533,z3,z4,z6]),(0,[z1,z2,z3,z188,z4,z48,z6]),(0,[z0,z1,z2,z3,z4,z534,z6]),(0,[z0,z1,z2,z3,z4,z6,z390])],[(1,[z0,z37,z83,z3,z4,z6]),(1,[z0,z1,z3,z4,z192,z6])],[(0,[z0,z37,z1,z1,z3,z4,z6]),(0,[z535,z0,z1,z2,z3,z4,z6]),(0,[z536,z0,z1,z2,z3,z4,z6])],[(0,[z139,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z364,z3,z212,z4,z6]),(0,[z0,z1,z537,z2,z3,z4,z6])],[(0,[z42,z0,z1,z3,z162,z4,z6]),(0,[z0,z61,z50,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z538,z4,z6]),(0,[z0,z2,z23,z3,z354,z4,z6]),(0,[z46,z0,z1,z2,z4,z6,z100])],[(0,[z0,z37,z1,z3,z133,z4,z6]),(0,[z46,z36,z0,z1,z2,z3,z4])],[(0,[z0,z433,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z19,z4,z6]),(0,[z0,z1,z62,z3,z4,z430,z6])]],
   [[(0,[z129,z52,z0,z1,z3,z4,z6]),(1,[z0,z1,z2,z97,z4,z6]),(0,[z0,z37,z1,z223,z3,z4,z6]),(0,[z171,z0,z1,z3,z56,z4,z6]),(0,[z539,z0,z1,z2,z3,z4,z6]),(0,[z0,z540,z1,z2,z3,z4,z6])],[(0,[z41,z0,z2,z3,z53,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z541])],[(0,[z0,z34,z61,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z542,z3,z4,z6]),(0,[z129,z42,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z543]),(0,[z0,z1,z2,z3,z544,z4,z6]),(0,[z0,z545,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z151,z67,z6]),(0,[z0,z1,z62,z3,z4,z224,z6])],[(0,[z24,z0,z1,z2,z3,z48,z6]),(0,[z0,z26,z1,z3,z504,z4,z6]),(0,[z0,z37,z1,z3,z414,z4,z6])],[(0,[z0,z26,z137,z2,z3,z4,z6]),(1,[z0,z1,z241,z3,z4,z6]),(1,[z0,z1,z214,z3,z4,z6])],[(0,[z24,z0,z1,z62,z3,z4,z6]),(0,[z0,z26,z1,z3,z4,z6,z57])],[],[(2,[z0,z232,z3,z4,z6]),(0,[z0,z1,z2,z546,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z547]),(0,[z0,z1,z305,z62,z3,z4,z6])],[(0,[z0,z26,z1,z3,z13,z4,z6]),(0,[z548,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z549])],[(1,[z0,z1,z3,z4,z445,z6])],[(0,[z42,z0,z26,z1,z3,z4,z6]),(0,[z0,z50,z2,z3,z133,z4,z6]),(0,[z46,z0,z1,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z532,z4,z6]),(0,[z0,z1,z2,z550,z3,z4,z6]),(0,[z0,z1,z2,z3,z298,z4,z6])],[(0,[z42,z0,z1,z3,z134,z4,z6]),(0,[z24,z0,z1,z89,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z551]),(0,[z0,z1,z2,z3,z552,z4,z6]),(0,[z0,z34,z1,z2,z3,z4,z167])],[(0,[z0,z1,z2,z553,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z371,z6]),(0,[z123,z0,z37,z1,z3,z4,z6]),(0,[z0,z1,z3,z13,z4,z67,z6])]],
   [[(0,[z0,z26,z37,z2,z3,z4,z6]),(0,[z535,z1,z2,z18,z3,z4,z6]),(0,[z180,z0,z1,z62,z3,z4,z6])],[(0,[z0,z220,z1,z3,z4,z67,z6]),(0,[z0,z1,z3,z4,z67,z119,z6])],[(0,[z554,z52,z0,z1,z3,z4,z6]),(0,[z0,z26,z1,z3,z4,z224,z6]),(0,[z0,z1,z2,z555,z3,z4,z6]),(0,[z71,z0,z1,z62,z3,z4,z6])],[(0,[z234,z42,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z67,z6,z57])],[],[(0,[z80,z0,z1,z62,z3,z4,z6]),(1,[z0,z37,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z56,z4,z6]),(0,[z0,z1,z556,z2,z3,z4,z6])],[(0,[z42,z0,z1,z3,z4,z336,z6]),(0,[z0,z1,z62,z3,z4,z48,z6]),(0,[z557,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z558,z6])],[(0,[z123,z0,z1,z2,z3,z4,z6]),(0,[z0,z559,z1,z2,z3,z4,z6]),(0,[z150,z0,z1,z187,z3,z4,z6]),(0,[z0,z1,z2,z3,z300,z4,z6])],[],[(1,[z0,z1,z3,z4,z249,z6])],[(0,[z42,z0,z1,z3,z181,z4,z6]),(0,[z52,z0,z1,z18,z3,z4,z6]),(1,[z0,z1,z368,z3,z4,z6])],[(0,[z0,z1,z2,z560,z3,z4,z6]),(0,[z0,z1,z374,z2,z3,z4,z6]),(1,[z0,z2,z3,z4,z6,z267])],[(0,[z0,z1,z2,z3,z4,z6,z561]),(0,[z199,z42,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z295,z188,z4,z6]),(0,[z242,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z13,z6,z14])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z37,z137,z1,z3,z4,z6]),(0,[z42,z0,z1,z3,z188,z4,z6]),(0,[z46,z52,z0,z1,z3,z4,z6]),(0,[z562,z0,z1,z2,z3,z4,z6]),(1,[z0,z451,z2,z3,z4,z6])],[(0,[z0,z37,z1,z77,z3,z4,z6]),(0,[z0,z1,z3,z4,z67,z224,z6]),(1,[z46,z0,z1,z2,z4,z100])],[(1,[z42,z1,z141,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z563,z6]),(0,[z52,z0,z232,z1,z3,z4,z6])]],
   [[(0,[z0,z564,z37,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z565,z4,z6]),(0,[z0,z1,z2,z3,z566,z4,z6]),(0,[z0,z1,z145,z2,z3,z4,z6])],[(0,[z46,z42,z0,z1,z3,z4,z6])],[(0,[z52,z0,z1,z3,z4,z67,z6]),(0,[z0,z1,z2,z567,z3,z4,z6]),(0,[z0,z1,z62,z550,z3,z4,z6]),(0,[z0,z1,z2,z198,z3,z4,z6]),(0,[z0,z1,z2,z127,z3,z55,z6]),(0,[z0,z1,z2,z4,z119,z6,z100]),(0,[z0,z1,z2,z135,z3,z4,z119])],[(0,[z568,z0,z1,z2,z3,z4,z6]),(0,[z0,z37,z505,z1,z3,z4,z6]),(0,[z38,z0,z1,z2,z3,z4,z57])],[(1,[z80,z1,z2,z188,z4,z6])],[(0,[z0,z77,z83,z2,z3,z4,z6]),(0,[z81,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z418,z67,z6]),(0,[z46,z0,z1,z374,z3,z4,z6])],[(0,[z96,z1,z2,z3,z4,z6,z174]),(0,[z569,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z82,z3,z4,z6]),(0,[z99,z0,z1,z2,z3,z4,z6])],[(0,[z38,z42,z0,z1,z3,z4,z6]),(0,[z0,z37,z37,z1,z3,z4,z6])],[(0,[z170,z0,z37,z1,z3,z4,z6]),(0,[z0,z1,z570,z2,z3,z4,z6]),(0,[z0,z1,z2,z571,z3,z4,z6]),(0,[z0,z564,z1,z2,z3,z4,z6]),(0,[z332,z0,z1,z2,z18,z4,z6]),(0,[z0,z1,z2,z127,z3,z4,z6])],[(0,[z0,z1,z2,z572,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z174]),(0,[z0,z1,z437,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z573,z6])],[(0,[z0,z1,z2,z574,z3,z4,z6]),(0,[z117,z0,z1,z2,z3,z4,z239]),(0,[z0,z1,z2,z3,z4,z6,z575])],[(0,[z80,z0,z1,z2,z143,z4,z6]),(0,[z0,z1,z62,z3,z56,z4,z6]),(0,[z0,z1,z2,z3,z4,z576,z6]),(0,[z0,z1,z2,z3,z577,z4,z6])],[(1,[z24,z1,z2,z3,z48,z6]),(0,[z0,z37,z1,z3,z4,z48,z6]),(0,[z0,z1,z578,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z514,z6])],[(0,[z460,z0,z1,z2,z3,z4,z6])],[(0,[z0,z137,z50,z2,z3,z4,z6]),(0,[z579,z0,z1,z2,z3,z4,z6]),(0,[z580,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z581,z3,z4,z6]),(0,[z582,z0,z1,z2,z3,z4,z6]),(1,[z0,z220,z1,z3,z4,z6])]],
   [[(0,[z170,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z70,z4,z6]),(1,[z535,z1,z2,z3,z4,z6]),(0,[z0,z34,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z83,z3,z4,z6]),(0,[z189,z0,z26,z1,z3,z4,z6]),(0,[z150,z0,z1,z3,z4,z67,z6]),(0,[z0,z1,z2,z111,z3,z4,z6]),(0,[z0,z1,z2,z3,z583,z4,z6])],[(0,[z0,z1,z570,z3,z4,z239,z6])],[],[(0,[z0,z1,z2,z584,z3,z4,z6]),(0,[z123,z117,z1,z2,z3,z4,z6]),(0,[z0,z473,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z585,z6]),(0,[z147,z0,z1,z3,z4,z67,z6])],[(0,[z0,z586,z1,z2,z3,z4,z6])],[(0,[z42,z96,z0,z1,z3,z4,z6]),(0,[z80,z96,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z587,z4,z6])],[(0,[z0,z1,z2,z3,z4,z588,z6])],[(0,[z52,z0,z1,z135,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z589,z6]),(0,[z590,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z591,z4,z6])],[(0,[z592,z0,z1,z2,z3,z4,z6]),(0,[z52,z0,z1,z23,z3,z4,z6]),(0,[z0,z1,z2,z593,z3,z4,z6]),(0,[z68,z0,z26,z1,z3,z4,z6]),(0,[z0,z26,z1,z3,z56,z4,z6]),(0,[z0,z1,z62,z118,z3,z4,z6]),(1,[z0,z1,z3,z4,z6,z416])],[(1,[z24,z42,z1,z3,z4,z6]),(0,[z0,z2,z18,z3,z4,z167,z6]),(1,[z0,z1,z3,z4,z499,z6]),(0,[z0,z1,z62,z3,z4,z119,z6])],[(0,[z42,z0,z1,z3,z102,z4,z6]),(0,[z402,z0,z1,z2,z3,z4,z6]),(0,[z0,z61,z2,z3,z4,z10,z6]),(0,[z0,z1,z2,z3,z4,z167,z6])],[(0,[z0,z1,z2,z3,z169,z4,z6]),(0,[z0,z1,z2,z3,z4,z105,z6]),(0,[z0,z37,z50,z1,z3,z4,z6]),(0,[z0,z1,z62,z3,z4,z6,z57])],[(0,[z0,z34,z1,z2,z3,z181,z4])],[(0,[z0,z594,z1,z2,z3,z4,z6]),(0,[z595,z0,z1,z2,z3,z4,z6])],[(0,[z478,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z62,z3,z13,z4,z6]),(0,[z0,z1,z2,z3,z596,z4,z6]),(1,[z95,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z597]),(0,[z52,z0,z304,z2,z3,z4,z6]),(0,[z52,z0,z1,z185,z3,z4,z6]),(1,[z0,z26,z118,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z598,z6]),(0,[z0,z1,z22,z2,z56,z4,z6]),(0,[z599,z0,z1,z2,z3,z4,z6])],[(0,[z41,z0,z1,z62,z3,z4,z6]),(0,[z0,z1,z2,z3,z600,z4,z6]),(0,[z0,z1,z601,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z602,z4,z6])],[(1,[z52,z0,z232,z3,z4,z6])],[(0,[z150,z0,z1,z62,z3,z4,z6]),(0,[z71,z0,z1,z3,z4,z67,z6])],[(0,[z0,z1,z2,z603,z3,z4,z6])],[(0,[z170,z0,z61,z2,z3,z4,z6]),(0,[z147,z52,z0,z1,z3,z4,z6]),(0,[z80,z1,z2,z3,z188,z4,z6]),(0,[z0,z1,z2,z127,z188,z4,z6]),(0,[z0,z1,z2,z604,z3,z4,z6])],[(0,[z80,z0,z1,z3,z4,z67,z6]),(1,[z0,z2,z3,z4,z6,z12])],[(0,[z139,z41,z0,z1,z3,z4,z6]),(0,[z0,z605,z1,z2,z3,z4,z6]),(0,[z193,z0,z26,z1,z3,z4,z6]),(0,[z0,z26,z34,z1,z3,z4,z6]),(0,[z0,z26,z1,z118,z3,z4,z6]),(0,[z0,z1,z2,z606,z3,z4,z6])],[(0,[z0,z26,z1,z3,z4,z119,z6]),(0,[z0,z1,z2,z3,z607,z4,z6]),(0,[z0,z1,z2,z146,z3,z55,z6]),(0,[z0,z1,z2,z130,z3,z4,z6])],[(0,[z24,z52,z0,z1,z3,z4,z6]),(0,[z608,z0,z1,z2,z3,z4,z6])],[(1,[z42,z1,z3,z188,z4,z6]),(0,[z52,z117,z0,z1,z3,z4,z6]),(1,[z359,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z609]),(0,[z0,z1,z2,z3,z610,z4,z6])],[(0,[z611,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z612,z6]),(0,[z0,z1,z2,z3,z4,z613,z6]),(0,[z0,z1,z2,z3,z614,z4,z6])],[(1,[z0,z173,z1,z3,z4,z6]),(0,[z0,z26,z1,z127,z3,z4,z6]),(0,[z0,z1,z2,z615,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z616,z6])],[(0,[z24,z42,z0,z1,z3,z4,z6]),(0,[z36,z0,z26,z2,z3,z4,z6]),(0,[z0,z1,z256,z18,z3,z4,z6])],[(0,[z52,z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z2,z146,z3,z4,z6])],[(0,[z0,z37,z1,z118,z3,z4,z6]),(0,[z0,z1,z2,z617,z3,z4,z6]),(1,[z0,z3,z4,z151,z67,z6]),(0,[z1,z2,z3,z4,z514,z67,z6]),(0,[z0,z1,z2,z3,z212,z4,z6])]],
   [[(0,[z332,z0,z26,z1,z3,z4,z6]),(0,[z0,z37,z1,z3,z4,z119,z6])],[(0,[z170,z0,z1,z441,z3,z4,z6]),(0,[z42,z0,z1,z223,z3,z4,z6]),(0,[z24,z0,z1,z2,z3,z4,z371]),(1,[z0,z176,z2,z3,z4,z6])],[(0,[z170,z0,z137,z2,z3,z4,z6]),(0,[z0,z1,z2,z143,z127,z4,z6]),(1,[z0,z271,z2,z3,z4,z6]),(0,[z0,z173,z1,z2,z3,z4,z6]),(0,[z0,z37,z1,z3,z4,z6,z57])],[(0,[z52,z0,z232,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z618,z6])],[(0,[z71,z52,z0,z1,z3,z4,z6]),(0,[z96,z0,z37,z1,z3,z4,z6]),(0,[z24,z1,z2,z3,z4,z48,z6]),(0,[z0,z2,z3,z133,z4,z10,z6])],[(0,[z24,z0,z1,z380,z3,z4,z6]),(0,[z0,z37,z1,z3,z13,z4,z6]),(0,[z619,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z3,z4,z224,z6,z57]),(0,[z168,z0,z1,z2,z3,z4,z6])],[(0,[z80,z52,z0,z1,z3,z4,z6]),(0,[z52,z0,z1,z143,z3,z4,z6]),(1,[z0,z1,z570,z3,z4,z6]),(0,[z0,z1,z223,z2,z3,z4,z6])],[(0,[z71,z42,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z620,z3,z4,z6])],[(0,[z448,z0,z1,z2,z3,z4,z6]),(0,[z621,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z67,z6,z174])],[(0,[z0,z1,z2,z3,z4,z6,z622]),(0,[z117,z0,z1,z62,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z623,z6]),(0,[z0,z1,z2,z3,z4,z624,z6]),(1,[z0,z183,z1,z3,z4,z6])],[(0,[z0,z1,z2,z146,z3,z13,z6]),(0,[z0,z1,z2,z146,z3,z181,z4])],[(0,[z96,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z143,z4,z55,z6]),(0,[z36,z0,z26,z1,z3,z4,z6]),(0,[z38,z0,z26,z1,z3,z4,z6]),(1,[z66,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z601,z3,z4,z6]),(0,[z189,z0,z1,z2,z3,z55,z6]),(0,[z0,z1,z2,z3,z443,z4,z6])],[(0,[z0,z37,z1,z3,z4,z224,z6]),(0,[z625,z0,z1,z2,z3,z4,z6]),(0,[z0,z240,z1,z62,z3,z4,z6]),(0,[z0,z1,z2,z3,z626,z4,z6])],[(0,[z0,z280,z1,z77,z3,z4,z6]),(0,[z68,z0,z1,z2,z3,z134,z6]),(1,[z0,z473,z2,z3,z4,z6]),(0,[z0,z1,z2,z627,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z628]),(0,[z0,z176,z1,z2,z3,z4,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z454,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z25]),(0,[z0,z26,z1,z3,z4,z167,z6])]],
   [[(0,[z201,z42,z0,z1,z3,z4,z6]),(0,[z0,z83,z2,z3,z133,z4,z6])],[(0,[z41,z0,z77,z2,z3,z4,z6]),(0,[z41,z1,z2,z3,z134,z4,z6]),(1,[z0,z1,z542,z3,z4,z6]),(0,[z42,z0,z61,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z471,z4,z6]),(0,[z0,z1,z2,z3,z4,z239,z14]),(0,[z629,z0,z1,z2,z3,z4,z6])],[(0,[z41,z96,z1,z2,z3,z4,z6]),(0,[z189,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z630,z3,z4,z6]),(1,[z0,z220,z2,z3,z4,z6]),(0,[z631,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z3,z4,z357,z48,z6]),(0,[z0,z37,z1,z3,z4,z589,z6])],[(0,[z81,z0,z1,z3,z4,z48,z6]),(0,[z0,z1,z62,z3,z212,z4,z6])],[(0,[z0,z1,z196,z3,z4,z167,z6]),(0,[z0,z1,z2,z3,z4,z14,z100])],[(0,[z0,z1,z2,z632,z3,z4,z6]),(0,[z52,z0,z1,z3,z4,z8,z6]),(0,[z332,z0,z1,z2,z53,z4,z6]),(0,[z332,z0,z2,z3,z4,z167,z6]),(0,[z0,z2,z3,z4,z167,z6,z21]),(0,[z633,z0,z1,z2,z3,z4,z6])],[(0,[z634,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z635,z6])],[(0,[z0,z525,z1,z2,z3,z4,z6]),(0,[z0,z1,z511,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z203])],[(0,[z42,z0,z1,z435,z3,z4,z6]),(0,[z68,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z636]),(0,[z36,z0,z1,z2,z3,z4,z167]),(0,[z0,z1,z3,z181,z4,z67,z6]),(0,[z0,z637,z1,z2,z3,z4,z6])],[(0,[z377,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z638,z4,z6]),(0,[z0,z1,z3,z4,z67,z167,z6])],[(0,[z170,z36,z0,z2,z3,z4,z6]),(0,[z0,z137,z2,z3,z4,z10,z6]),(0,[z0,z1,z2,z3,z639,z4,z6]),(1,[z0,z1,z3,z480,z4,z6]),(0,[z640,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z343,z62,z3,z4,z6])],[(1,[z0,z2,z3,z4,z384,z6]),(0,[z0,z641,z1,z2,z3,z4,z6]),(0,[z0,z1,z642,z2,z3,z4,z6])],[(0,[z42,z0,z137,z1,z3,z4,z6]),(0,[z0,z1,z2,z188,z4,z55,z6]),(0,[z66,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z643,z2,z3,z4,z6]),(0,[z42,z0,z1,z77,z3,z4,z6]),(0,[z0,z280,z1,z2,z3,z4,z6]),(0,[z0,z1,z644,z2,z3,z4,z6]),(0,[z645,z0,z1,z2,z3,z4,z6])]],
   [[],[(0,[z41,z1,z2,z3,z188,z4,z6]),(0,[z0,z1,z2,z3,z181,z13,z4])],[(0,[z41,z0,z1,z3,z4,z67,z6]),(0,[z0,z26,z2,z3,z53,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z646])],[(0,[z0,z26,z1,z3,z212,z4,z6]),(0,[z0,z61,z2,z3,z4,z6,z21]),(0,[z0,z1,z2,z3,z4,z6,z100])],[(0,[z170,z0,z1,z542,z3,z4,z6]),(0,[z0,z1,z2,z18,z3,z4,z6]),(0,[z0,z1,z3,z480,z53,z4,z6]),(1,[z0,z1,z2,z127,z212,z6]),(0,[z168,z0,z2,z3,z4,z6,z100])],[(0,[z0,z50,z2,z3,z4,z167,z6]),(0,[z0,z1,z2,z135,z3,z4,z100])],[(0,[z52,z52,z0,z1,z3,z4,z6]),(0,[z52,z0,z1,z22,z3,z4,z6]),(0,[z0,z1,z2,z647,z3,z4,z6]),(0,[z0,z648,z1,z2,z3,z4,z6])],[],[(0,[z193,z0,z1,z2,z3,z4,z6]),(0,[z42,z0,z37,z1,z3,z4,z6]),(0,[z1,z2,z18,z3,z439,z4,z6])],[(0,[z255,z42,z0,z1,z3,z4,z6]),(0,[z96,z0,z1,z2,z188,z4,z6]),(1,[z0,z2,z3,z4,z153,z6]),(0,[z171,z0,z1,z62,z3,z4,z6])],[(0,[z24,z41,z1,z2,z3,z4,z6]),(0,[z52,z42,z0,z1,z3,z4,z6]),(0,[z52,z0,z1,z3,z4,z10,z6])],[(0,[z0,z1,z2,z3,z4,z649,z6]),(0,[z117,z96,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z650,z3,z4,z6]),(0,[z0,z1,z2,z3,z651,z4,z6]),(0,[z129,z0,z1,z2,z3,z67,z6]),(0,[z652,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z653,z6])],[(0,[z129,z0,z26,z1,z3,z4,z6]),(0,[z0,z37,z1,z3,z4,z6,z551]),(0,[z0,z1,z654,z2,z3,z4,z6]),(0,[z0,z1,z22,z62,z3,z4,z6])],[(0,[z42,z0,z1,z3,z4,z48,z6]),(1,[z42,z1,z3,z134,z4,z6]),(0,[z24,z0,z1,z2,z31,z4,z6]),(0,[z0,z1,z2,z3,z13,z4,z14])],[(0,[z0,z26,z1,z3,z4,z623,z6])],[(0,[z264,z42,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z133,z4,z67,z6]),(1,[z0,z1,z198,z3,z4,z6])]],
   [[(0,[z42,z0,z1,z2,z3,z4,z6]),(0,[z171,z0,z1,z2,z56,z4,z6])],[(1,[z0,z1,z441,z3,z4,z6]),(0,[z332,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z289,z4,z67,z6]),(0,[z0,z1,z62,z127,z3,z4,z6])],[(0,[z0,z1,z62,z3,z4,z6,z174])],[],[(0,[z24,z137,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z655]),(0,[z608,z0,z37,z1,z3,z4,z6]),(0,[z0,z37,z1,z3,z56,z4,z6]),(0,[z0,z328,z1,z2,z3,z4,z6])],[(0,[z0,z1,z77,z3,z4,z67,z6]),(0,[z281,z52,z0,z1,z3,z4,z6]),(0,[z150,z52,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z656,z4,z6]),(0,[z0,z1,z223,z3,z4,z224,z6]),(0,[z0,z1,z2,z3,z212,z6,z14])],[(0,[z150,z0,z83,z2,z3,z4,z6]),(0,[z657,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z187,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z151,z67,z6])],[(0,[z658,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z62,z3,z4,z6,z646]),(0,[z0,z1,z2,z3,z659,z4,z6])],[(0,[z150,z42,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z514,z67,z6]),(0,[z0,z1,z62,z3,z4,z6,z100]),(0,[z660,z0,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z3,z4,z239,z6]),(0,[z0,z1,z2,z515,z3,z4,z6]),(0,[z117,z1,z2,z3,z188,z4,z6]),(0,[z0,z1,z2,z661,z3,z4,z6]),(1,[z1,z3,z4,z514,z67,z6]),(0,[z0,z1,z3,z4,z67,z662,z6]),(1,[z0,z1,z2,z3,z298,z6])],[(0,[z42,z0,z1,z3,z4,z6,z392]),(0,[z117,z0,z1,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z663,z4,z6])],[(0,[z0,z1,z482,z3,z134,z4,z6]),(0,[z0,z1,z2,z3,z133,z4,z238]),(0,[z0,z1,z23,z3,z4,z224,z6])],[(0,[z42,z0,z50,z1,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z6])],[],[(0,[z1,z2,z3,z134,z4,z48,z6]),(0,[z0,z1,z2,z3,z664,z4,z6]),(1,[z369,z1,z2,z3,z4,z6])]],
   [[(0,[z665,z0,z1,z2,z3,z4,z6]),(0,[z666,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z26,z1,z3,z4,z6,z174]),(0,[z0,z667,z1,z2,z3,z4,z6])],[(1,[z0,z34,z2,z3,z4,z167])],[(0,[z42,z0,z1,z3,z133,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z668]),(0,[z0,z37,z34,z1,z3,z4,z6]),(0,[z0,z1,z2,z135,z3,z4,z6])],[(0,[z669,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z670,z6]),(0,[z0,z1,z2,z23,z3,z4,z6]),(0,[z671,z0,z1,z2,z3,z4,z6])],[(0,[z52,z0,z1,z3,z4,z6,z279]),(0,[z0,z1,z2,z3,z672,z4,z6]),(0,[z0,z1,z62,z3,z4,z167,z6]),(0,[z0,z1,z3,z102,z4,z67,z6]),(0,[z0,z1,z2,z673,z3,z4,z6])],[(0,[z52,z0,z1,z141,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z674,z6]),(0,[z0,z1,z2,z3,z4,z675,z6])],[(0,[z332,z0,z61,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z676,z4,z6]),(0,[z0,z1,z2,z677,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z267])],[(0,[z0,z1,z77,z62,z3,z4,z6]),(0,[z0,z1,z2,z3,z295,z4,z6]),(0,[z0,z1,z380,z2,z3,z4,z6]),(0,[z0,z26,z1,z3,z4,z6,z100]),(0,[z0,z37,z1,z571,z3,z4,z6]),(0,[z0,z37,z1,z127,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z12,z57])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z37,z1,z3,z4,z6,z174]),(0,[z0,z26,z1,z18,z3,z4,z6]),(0,[z0,z678,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z679])],[(0,[z46,z0,z26,z1,z3,z4,z6])],[(0,[z41,z1,z77,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z680,z6]),(0,[z681,z0,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z181,z4]),(0,[z682,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z62,z3,z602,z4,z6])],[(0,[z96,z1,z185,z2,z3,z4,z6]),(0,[z683,z0,z1,z2,z3,z4,z6]),(1,[z0,z26,z3,z4,z167,z6]),(0,[z684,z0,z1,z2,z3,z4,z6])],[(0,[z46,z0,z34,z1,z2,z3,z4]),(0,[z129,z0,z1,z2,z3,z102,z6])],[(0,[z189,z0,z37,z1,z3,z4,z6]),(0,[z0,z685,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z662,z6]),(0,[z46,z0,z1,z2,z3,z4,z119])],[(0,[z80,z42,z0,z1,z3,z4,z6]),(0,[z0,z1,z185,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z210,z4,z6]),(1,[z0,z1,z3,z19,z4,z6])]],
   [[(0,[z686,z0,z1,z2,z3,z4,z6]),(0,[z687,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z135,z3,z4,z67,z6])],[(0,[z0,z1,z2,z165,z3,z4,z6]),(0,[z38,z0,z1,z223,z3,z4,z6]),(0,[z688,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z689,z2,z3,z4,z6])],[(0,[z0,z137,z1,z78,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z690])],[(0,[z0,z1,z2,z3,z691,z4,z6]),(0,[z42,z0,z1,z3,z4,z6,z57]),(0,[z0,z1,z2,z3,z4,z692,z6]),(0,[z0,z1,z2,z3,z4,z693,z6]),(0,[z0,z1,z3,z4,z67,z6,z100])],[(0,[z0,z1,z694,z2,z3,z4,z6]),(0,[z0,z1,z62,z62,z3,z4,z6])],[(0,[z68,z0,z37,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z384,z6]),(2,[z66,z1,z3,z4,z6])],[(0,[z42,z0,z1,z3,z13,z4,z6]),(0,[z0,z1,z2,z695,z3,z4,z6]),(0,[z52,z123,z0,z1,z3,z4,z6])],[(0,[z52,z0,z1,z3,z184,z4,z6]),(0,[z0,z1,z2,z3,z696,z4,z6]),(0,[z0,z1,z62,z146,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z697]),(0,[z1,z2,z3,z188,z4,z6,z174]),(1,[z171,z0,z1,z56,z4,z6]),(0,[z0,z1,z2,z3,z4,z55,z6])],[],[(0,[z0,z37,z1,z3,z4,z167,z6]),(0,[z171,z0,z1,z3,z4,z67,z6]),(0,[z46,z0,z1,z2,z135,z4,z6])],[(0,[z0,z1,z2,z698,z3,z4,z6]),(0,[z0,z1,z498,z62,z3,z4,z6]),(0,[z699,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z141,z3,z4,z67,z6]),(0,[z36,z0,z2,z18,z3,z4,z6]),(0,[z0,z34,z1,z2,z3,z4,z21]),(0,[z0,z1,z223,z3,z56,z4,z6]),(0,[z0,z1,z3,z4,z67,z67,z6])],[(0,[z41,z0,z2,z3,z133,z4,z6]),(0,[z0,z1,z22,z3,z4,z67,z6]),(0,[z129,z0,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z3,z4,z224,z6]),(0,[z0,z1,z3,z212,z4,z67,z6])],[]],
   [[(0,[z0,z700,z1,z2,z3,z4,z6])],[(0,[z0,z83,z2,z118,z3,z4,z6])],[(0,[z52,z0,z1,z3,z4,z6,z21]),(0,[z0,z26,z1,z62,z3,z4,z6])],[(1,[z0,z240,z1,z3,z4,z6]),(1,[z332,z0,z2,z53,z4,z6]),(0,[z0,z1,z23,z3,z56,z4,z6])],[(0,[z117,z1,z2,z3,z4,z239,z6])],[(0,[z0,z1,z2,z3,z4,z701,z6]),(0,[z123,z0,z1,z2,z3,z4,z239]),(1,[z123,z1,z2,z3,z4,z174]),(0,[z0,z26,z1,z146,z3,z4,z6])],[(0,[z0,z26,z1,z135,z3,z4,z6]),(0,[z0,z49,z37,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z142,z21])],[(0,[z1,z2,z3,z4,z239,z6,z174]),(0,[z128,z0,z26,z1,z3,z4,z6]),(1,[z0,z1,z3,z4,z623,z6]),(0,[z0,z26,z1,z3,z4,z670,z6]),(0,[z0,z1,z475,z2,z3,z4,z6])],[(0,[z349,z52,z0,z1,z3,z4,z6]),(0,[z702,z0,z1,z2,z3,z4,z6]),(1,[z0,z50,z2,z3,z133,z6])],[(1,[z234,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z703,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z704]),(1,[z0,z1,z62,z3,z67,z6]),(1,[z0,z1,z3,z443,z4,z6])],[(0,[z0,z1,z83,z62,z3,z4,z6]),(0,[z0,z1,z2,z705,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z363,z6])],[(0,[z0,z137,z1,z62,z3,z4,z6]),(0,[z0,z61,z1,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z4,z119,z14])],[(0,[z234,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z482,z2,z3,z4,z6]),(0,[z0,z1,z118,z3,z4,z67,z6]),(0,[z332,z0,z37,z1,z3,z4,z6])],[(0,[z706,z0,z1,z2,z3,z4,z6]),(0,[z0,z37,z1,z146,z3,z4,z6]),(0,[z332,z36,z0,z2,z3,z4,z6]),(2,[z0,z220,z3,z4,z6])],[(0,[z170,z0,z2,z3,z53,z4,z6]),(0,[z30,z0,z37,z1,z3,z4,z6]),(0,[z0,z37,z1,z3,z212,z4,z6]),(0,[z0,z49,z1,z2,z3,z4,z6]),(0,[z0,z34,z2,z3,z53,z4,z6]),(1,[z0,z190,z2,z3,z4,z6])],[(0,[z554,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z67,z6]),(1,[z0,z2,z158,z3,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z707,z3,z6]),(0,[z106,z42,z1,z3,z4,z6]),(0,[z0,z708,z1,z3,z4,z6]),(0,[z0,z1,z97,z4,z67,z6]),(0,[z81,z1,z3,z134,z4,z6]),(0,[z419,z1,z3,z4,z6,z174]),(0,[z0,z256,z3,z4,z167,z6]),(0,[z1,z62,z3,z514,z67,z6]),(0,[z0,z709,z1,z3,z4,z6]),(0,[z0,z1,z710,z3,z4,z6])],[(0,[z52,z0,z1,z3,z298,z6]),(0,[z0,z1,z2,z3,z348,z14])],[(0,[z0,z711,z2,z3,z4,z6]),(0,[z712,z0,z2,z3,z4,z6]),(0,[z0,z1,z601,z3,z4,z224]),(0,[z0,z3,z4,z713,z306,z6])],[(0,[z0,z26,z3,z385,z4,z6]),(0,[z0,z37,z271,z3,z4,z6]),(0,[z0,z37,z1,z31,z4,z6]),(0,[z0,z714,z1,z3,z4,z6]),(0,[z0,z1,z715,z3,z4,z6])],[(0,[z0,z1,z716,z3,z4,z6]),(0,[z717,z1,z2,z3,z4,z6])],[(0,[z0,z26,z280,z3,z4,z6]),(0,[z42,z490,z1,z3,z4,z6]),(0,[z42,z0,z1,z3,z298,z6]),(0,[z386,z1,z2,z188,z4,z6]),(0,[z46,z0,z26,z1,z4,z100]),(0,[z0,z1,z62,z3,z663,z6]),(0,[z625,z0,z2,z53,z4,z6])],[(0,[z0,z718,z1,z3,z4,z6]),(0,[z42,z1,z3,z4,z719,z6]),(0,[z0,z1,z720,z3,z4,z6]),(0,[z419,z96,z1,z3,z4,z6]),(0,[z68,z37,z1,z3,z134,z6]),(0,[z36,z0,z26,z3,z4,z167]),(0,[z0,z1,z2,z3,z300,z4]),(0,[z369,z1,z22,z3,z4,z6]),(0,[z0,z76,z62,z3,z4,z6]),(0,[z0,z721,z176,z3,z4,z6]),(0,[z0,z1,z3,z722,z4,z6])],[(0,[z0,z1,z2,z3,z4,z723]),(0,[z41,z77,z62,z3,z4,z6]),(0,[z1,z185,z2,z31,z4,z6]),(0,[z0,z1,z3,z4,z724,z6]),(0,[z0,z1,z3,z4,z725,z6]),(0,[z0,z26,z17,z3,z4,z6]),(0,[z0,z1,z2,z3,z726,z6]),(0,[z727,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z127,z639,z6]),(0,[z36,z535,z2,z3,z4,z6]),(0,[z728,z0,z1,z3,z4,z6]),(0,[z66,z220,z3,z4,z67,z6])],[(0,[z0,z232,z3,z56,z4,z6]),(0,[z0,z729,z3,z134,z4,z6]),(0,[z0,z1,z730,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z731]),(0,[z0,z26,z190,z3,z4,z6]),(0,[z0,z1,z3,z4,z732,z6]),(0,[z0,z1,z374,z3,z298,z6])],[(0,[z0,z1,z3,z733,z4,z6]),(0,[z47,z2,z3,z188,z4,z6]),(0,[z0,z2,z3,z4,z734,z6]),(0,[z36,z0,z62,z3,z4,z21]),(0,[z0,z735,z2,z3,z4,z6]),(0,[z45,z1,z2,z3,z155,z6]),(0,[z46,z0,z1,z4,z203,z100])],[(0,[z24,z1,z2,z3,z290,z6]),(0,[z0,z87,z62,z3,z4,z6]),(0,[z0,z240,z61,z3,z4,z6]),(0,[z168,z0,z3,z4,z6,z203])],[(0,[z0,z77,z3,z4,z623,z6]),(0,[z52,z0,z1,z3,z4,z736]),(0,[z0,z1,z3,z737,z4,z6]),(0,[z0,z1,z738,z3,z4,z6]),(0,[z0,z61,z18,z19,z4,z6]),(0,[z129,z0,z1,z3,z67,z6]),(0,[z66,z1,z3,z4,z6,z202]),(0,[z0,z739,z3,z4,z6,z267])],[(0,[z740,z0,z1,z3,z4,z6]),(0,[z52,z36,z0,z3,z4,z21]),(0,[z36,z0,z26,z3,z4,z670]),(0,[z741,z49,z1,z3,z4,z6]),(0,[z0,z1,z22,z23,z4,z6]),(0,[z0,z451,z22,z23,z4,z6]),(0,[z0,z1,z3,z4,z6,z742])],[(0,[z170,z66,z1,z3,z4,z6]),(0,[z451,z2,z3,z51,z4,z6])],[(0,[z0,z1,z3,z743,z4,z6]),(0,[z42,z641,z1,z3,z4,z6]),(0,[z0,z744,z1,z3,z4,z6]),(0,[z0,z173,z3,z4,z384,z6]),(0,[z608,z0,z1,z3,z445,z6]),(0,[z745,z1,z2,z3,z4,z6]),(0,[z66,z1,z3,z4,z6,z21]),(0,[z746,z0,z220,z3,z4,z6])]],
   [[(0,[z0,z26,z1,z3,z4,z6]),(0,[z52,z0,z110,z3,z4,z6]),(0,[z81,z1,z3,z188,z4,z6]),(0,[z0,z1,z3,z747,z4,z6]),(0,[z0,z26,z322,z3,z4,z6]),(0,[z37,z748,z1,z3,z4,z6]),(0,[z0,z1,z62,z3,z247,z4]),(0,[z535,z61,z2,z18,z4,z6]),(0,[z0,z1,z3,z4,z306,z6]),(0,[z0,z749,z2,z3,z4,z6])],[(0,[z0,z1,z3,z4,z750,z6]),(0,[z46,z0,z1,z4,z67,z100])],[(0,[z0,z1,z3,z751,z4,z6]),(0,[z1,z2,z3,z439,z4,z6]),(0,[z1,z2,z3,z752,z4,z6]),(0,[z36,z0,z220,z3,z4,z6]),(0,[z1,z3,z4,z67,z753,z6])],[(0,[z0,z441,z3,z4,z167,z6]),(0,[z0,z1,z2,z754,z4,z6]),(0,[z0,z1,z3,z4,z755,z6]),(0,[z170,z0,z2,z3,z300,z4]),(0,[z756,z0,z1,z3,z4,z6]),(0,[z0,z1,z223,z3,z4,z336]),(0,[z0,z232,z757,z3,z4,z6]),(0,[z36,z0,z2,z3,z676,z4]),(0,[z0,z220,z3,z4,z6,z202])],[(0,[z42,z0,z110,z3,z4,z6]),(0,[z758,z0,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z759,z6]),(0,[z173,z1,z3,z188,z4,z6]),(0,[z0,z271,z2,z3,z4,z371]),(0,[z24,z0,z220,z3,z4,z6]),(0,[z0,z1,z3,z760,z4,z6])],[(0,[z0,z1,z761,z3,z4,z6]),(0,[z46,z0,z1,z2,z4,z762])],[(0,[z0,z1,z763,z3,z4,z6]),(0,[z0,z26,z410,z3,z4,z6]),(0,[z0,z220,z3,z4,z6,z21]),(0,[z66,z1,z22,z3,z4,z6]),(0,[z0,z764,z1,z3,z4,z6])],[(0,[z0,z232,z118,z3,z4,z6]),(0,[z80,z26,z1,z188,z4,z6]),(0,[z0,z1,z3,z765,z4,z6]),(0,[z766,z0,z1,z3,z4,z6])],[(0,[z0,z767,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z768,z6]),(0,[z0,z232,z3,z4,z119,z6]),(0,[z0,z1,z3,z4,z769,z6])],[(0,[z402,z42,z1,z3,z4,z6]),(0,[z117,z42,z1,z3,z4,z239]),(0,[z0,z1,z3,z4,z6,z770]),(0,[z0,z152,z2,z3,z4,z6]),(0,[z46,z0,z37,z1,z4,z100]),(0,[z0,z2,z606,z53,z4,z6]),(0,[z0,z1,z771,z3,z4,z6])],[(0,[z772,z0,z1,z3,z4,z6]),(0,[z52,z1,z3,z51,z4,z6]),(0,[z80,z1,z295,z188,z4,z6]),(0,[z0,z773,z271,z3,z4,z6]),(0,[z24,z1,z2,z31,z48,z6]),(0,[z0,z2,z3,z4,z6,z774]),(0,[z775,z0,z473,z3,z4,z6]),(0,[z0,z26,z3,z4,z413,z6]),(0,[z66,z1,z3,z4,z10,z6]),(0,[z0,z1,z3,z4,z776,z6]),(0,[z0,z777,z17,z3,z4,z6])],[(0,[z419,z0,z1,z3,z4,z6]),(0,[z52,z0,z304,z3,z4,z6]),(0,[z42,z1,z3,z31,z4,z6]),(0,[z0,z232,z3,z4,z6,z778]),(0,[z0,z1,z3,z4,z779,z6]),(0,[z0,z780,z62,z3,z4,z6])],[(0,[z170,z137,z441,z3,z4,z6]),(0,[z0,z1,z2,z781,z4,z6]),(0,[z42,z1,z3,z35,z4,z6]),(0,[z0,z232,z127,z3,z4,z6]),(0,[z0,z1,z2,z3,z782,z4]),(0,[z0,z1,z783,z3,z4,z6]),(0,[z0,z220,z220,z3,z4,z6]),(0,[z0,z1,z364,z127,z212,z6])],[(0,[z0,z0,z232,z3,z4,z6]),(0,[z775,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z784]),(0,[z785,z1,z2,z3,z4,z6]),(0,[z0,z220,z22,z3,z4,z6]),(0,[z46,z66,z1,z3,z4,z6]),(0,[z0,z253,z2,z3,z155,z6]),(0,[z0,z1,z786,z3,z155,z6])],[(0,[z52,z0,z787,z3,z4,z6]),(0,[z788,z0,z1,z2,z4,z6]),(0,[z0,z1,z3,z4,z6,z789]),(0,[z0,z1,z790,z3,z4,z6]),(0,[z0,z1,z3,z4,z192,z6]),(0,[z168,z0,z3,z4,z67,z6])],[(0,[z42,z0,z304,z3,z4,z6]),(0,[z24,z26,z1,z3,z48,z6])]],
   [[(0,[z0,z26,z116,z3,z4,z6]),(0,[z0,z26,z101,z3,z4,z6]),(0,[z0,z1,z791,z3,z4,z6])],[(0,[z0,z26,z137,z3,z4,z6]),(0,[z402,z0,z1,z515,z4,z6]),(0,[z0,z792,z2,z3,z4,z6]),(0,[z0,z2,z793,z3,z4,z6]),(0,[z0,z220,z3,z4,z10,z6])],[(0,[z794,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z795,z4,z6]),(0,[z0,z1,z796,z3,z4,z6]),(0,[z797,z1,z2,z3,z4,z6]),(0,[z0,z798,z1,z3,z4,z6])],[(0,[z41,z37,z77,z3,z4,z6]),(0,[z0,z1,z515,z56,z4,z6]),(0,[z0,z1,z3,z799,z4,z6]),(0,[z535,z26,z1,z3,z4,z6]),(0,[z0,z800,z1,z3,z4,z6]),(0,[z0,z777,z1,z3,z4,z6]),(0,[z1,z62,z3,z4,z9,z6])],[(0,[z0,z464,z1,z3,z4,z6]),(0,[z0,z1,z801,z3,z4,z6]),(0,[z0,z1,z802,z3,z4,z6])],[(0,[z0,z803,z1,z3,z4,z6])],[(0,[z139,z0,z232,z3,z4,z6]),(0,[z170,z0,z220,z3,z4,z6]),(0,[z42,z0,z1,z804,z4,z6]),(0,[z0,z2,z3,z4,z6,z805]),(0,[z128,z1,z185,z3,z4,z6]),(0,[z0,z37,z3,z172,z4,z6]),(0,[z1,z2,z3,z4,z239,z806])],[(0,[z0,z26,z195,z3,z4,z6]),(0,[z402,z369,z1,z3,z4,z6]),(0,[z0,z62,z3,z354,z4,z6])],[(0,[z96,z1,z78,z3,z4,z6]),(0,[z0,z232,z3,z4,z807,z6]),(0,[z0,z1,z808,z3,z4,z6]),(0,[z1,z62,z3,z439,z4,z6]),(0,[z0,z809,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z810,z6]),(0,[z0,z811,z1,z3,z4,z6])],[(0,[z36,z0,z26,z3,z4,z6]),(0,[z66,z1,z3,z53,z4,z6]),(0,[z0,z1,z812,z3,z4,z6]),(0,[z0,z813,z2,z3,z4,z6]),(0,[z0,z17,z3,z4,z67,z6]),(0,[z0,z814,z62,z3,z4,z6]),(0,[z0,z815,z2,z3,z4,z6]),(1,[z0,z816,z3,z4,z6])],[(0,[z0,z817,z2,z3,z4,z6]),(0,[z0,z37,z158,z3,z4,z6]),(0,[z66,z1,z3,z4,z6,z14]),(0,[z0,z220,z3,z818,z4,z6])],[(0,[z42,z1,z89,z3,z4,z6]),(0,[z819,z0,z1,z3,z4,z6]),(0,[z114,z0,z1,z3,z4,z67]),(0,[z0,z1,z62,z3,z155,z6])],[(0,[z42,z1,z3,z94,z4,z6]),(0,[z0,z1,z3,z4,z357,z6]),(0,[z0,z2,z820,z53,z4,z6]),(0,[z0,z1,z821,z3,z4,z6])],[(0,[z52,z0,z822,z3,z4,z6]),(0,[z0,z823,z3,z4,z6,z194]),(0,[z0,z26,z241,z3,z4,z6]),(0,[z150,z0,z241,z3,z10,z6]),(0,[z0,z240,z50,z3,z133,z6]),(0,[z0,z824,z2,z3,z4,z6])],[(0,[z36,z193,z0,z3,z4,z6]),(0,[z52,z42,z304,z3,z4,z6]),(0,[z0,z825,z1,z3,z4,z6]),(0,[z24,z81,z1,z3,z48,z6]),(0,[z0,z473,z26,z3,z4,z6]),(0,[z0,z34,z2,z3,z566,z4]),(0,[z0,z816,z2,z3,z4,z6])],[(0,[z0,z1,z826,z3,z4,z6]),(1,[z128,z137,z3,z4,z6]),(0,[z42,z0,z1,z827,z4,z6]),(0,[z0,z232,z3,z4,z167,z6]),(0,[z0,z473,z3,z4,z269,z6]),(0,[z828,z26,z1,z3,z4,z6]),(0,[z0,z1,z3,z829,z4,z6]),(0,[z0,z1,z3,z4,z224,z551])]],
   [[(0,[z80,z52,z1,z188,z4,z6]),(0,[z0,z1,z830,z3,z4,z6]),(0,[z0,z220,z3,z53,z4,z6]),(0,[z45,z1,z3,z4,z67,z6]),(0,[z168,z0,z62,z3,z4,z6])],[(0,[z96,z104,z1,z3,z4,z6]),(0,[z42,z0,z3,z354,z4,z6]),(0,[z831,z1,z2,z3,z4,z6]),(0,[z66,z1,z83,z3,z4,z6]),(0,[z0,z1,z3,z421,z67,z6]),(0,[z0,z832,z2,z3,z4,z6]),(0,[z0,z220,z3,z4,z6,z14])],[(0,[z52,z688,z1,z3,z4,z6]),(0,[z95,z26,z1,z3,z4,z6]),(0,[z0,z190,z2,z3,z4,z363])],[(0,[z0,z26,z77,z3,z4,z6]),(0,[z0,z1,z3,z833,z4,z6])],[(0,[z834,z0,z1,z3,z4,z6]),(0,[z0,z835,z1,z3,z4,z6]),(1,[z0,z729,z3,z4,z6]),(0,[z0,z3,z4,z623,z167,z6]),(0,[z0,z836,z1,z3,z4,z6]),(0,[z260,z2,z3,z53,z4,z6]),(0,[z0,z1,z3,z837,z4,z67]),(0,[z45,z253,z2,z3,z4,z6])],[(0,[z66,z49,z1,z3,z4,z6]),(0,[z0,z220,z3,z4,z838,z6]),(0,[z46,z0,z220,z3,z4,z6]),(0,[z124,z190,z2,z3,z4,z6])],[(0,[z0,z1,z2,z97,z4,z25]),(0,[z26,z1,z3,z439,z4,z6]),(0,[z36,z0,z26,z3,z181,z4]),(0,[z0,z1,z3,z839,z4,z6]),(0,[z0,z1,z62,z3,z489,z6]),(0,[z0,z1,z198,z3,z4,z363])],[(0,[z0,z1,z840,z3,z4,z6]),(0,[z0,z433,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z841]),(0,[z0,z1,z842,z3,z4,z6]),(0,[z36,z0,z2,z3,z4,z609]),(0,[z88,z36,z0,z2,z3,z4]),(1,[z0,z1,z843,z4,z6]),(0,[z66,z1,z3,z289,z4,z6]),(0,[z0,z714,z2,z3,z4,z6])],[(0,[z114,z41,z0,z2,z3,z4]),(0,[z66,z1,z3,z4,z290,z6]),(0,[z24,z52,z1,z3,z48,z6]),(0,[z52,z0,z1,z3,z13,z14]),(0,[z0,z844,z1,z3,z4,z6]),(0,[z0,z26,z253,z3,z4,z6]),(0,[z0,z845,z118,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z846])],[(0,[z0,z1,z2,z847,z4,z6]),(0,[z52,z580,z1,z3,z4,z6]),(0,[z0,z729,z2,z3,z4,z6]),(0,[z0,z26,z3,z453,z4,z6]),(0,[z1,z2,z3,z4,z848,z6]),(0,[z37,z1,z3,z4,z9,z6]),(0,[z0,z1,z849,z3,z4,z6]),(0,[z36,z0,z2,z3,z4,z547]),(0,[z124,z1,z198,z3,z4,z6])],[(0,[z0,z2,z3,z850,z4,z6]),(0,[z535,z2,z3,z4,z167,z6])],[(0,[z0,z851,z1,z3,z4,z6]),(0,[z42,z1,z3,z852,z4,z6]),(0,[z42,z7,z1,z3,z4,z6]),(0,[z36,z0,z3,z4,z67,z21]),(0,[z0,z34,z253,z2,z3,z4])],[(0,[z0,z1,z853,z3,z4,z6]),(0,[z0,z87,z3,z4,z67,z6]),(0,[z150,z128,z0,z3,z4,z6]),(0,[z0,z1,z3,z4,z854,z6]),(0,[z369,z1,z22,z23,z4,z6]),(0,[z66,z1,z3,z4,z301,z6])],[(0,[z41,z66,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z249,z6]),(0,[z0,z1,z3,z4,z855,z6]),(0,[z150,z0,z3,z10,z67,z6]),(0,[z0,z1,z3,z4,z67,z238]),(0,[z0,z816,z1,z3,z4,z6]),(0,[z0,z158,z130,z3,z4,z6])],[(0,[z0,z1,z856,z3,z4,z6]),(0,[z0,z104,z50,z3,z4,z6]),(0,[z117,z1,z3,z4,z67,z239]),(0,[z0,z1,z368,z3,z4,z6]),(0,[z0,z220,z3,z289,z4,z6]),(0,[z0,z17,z145,z3,z4,z6])],[(0,[z170,z137,z542,z3,z4,z6]),(0,[z150,z0,z441,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z267]),(0,[z376,z190,z2,z3,z4,z6])]],
   [[(0,[z0,z2,z3,z4,z857,z6]),(0,[z0,z858,z2,z3,z4,z6]),(0,[z47,z81,z0,z3,z4,z6]),(0,[z0,z240,z1,z3,z623,z6]),(0,[z0,z1,z2,z3,z859,z4]),(0,[z36,z0,z183,z3,z4,z6]),(0,[z0,z1,z860,z3,z4,z6]),(0,[z0,z2,z3,z4,z861,z6]),(0,[z862,z0,z1,z3,z4,z6])],[(1,[z0,z232,z3,z4,z6]),(0,[z863,z0,z1,z3,z4,z6]),(0,[z0,z451,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z864,z6])],[(0,[z0,z473,z37,z3,z4,z6]),(0,[z1,z3,z4,z848,z623,z6]),(0,[z865,z1,z2,z3,z4,z6]),(0,[z866,z1,z2,z3,z4,z6])],[(0,[z42,z1,z141,z3,z4,z6]),(0,[z0,z232,z3,z212,z4,z6]),(0,[z0,z867,z1,z3,z4,z6]),(0,[z868,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z869,z4]),(0,[z1,z3,z51,z4,z67,z6]),(0,[z0,z1,z601,z3,z289,z4]),(0,[z376,z1,z198,z3,z4,z6]),(0,[z0,z1,z2,z212,z870,z6])],[(0,[z24,z1,z2,z3,z871,z6]),(0,[z0,z872,z1,z3,z4,z6]),(0,[z150,z0,z2,z3,z10,z6])],[(0,[z0,z76,z2,z3,z4,z363])],[(0,[z139,z41,z77,z3,z4,z6]),(0,[z0,z1,z873,z3,z4,z6]),(0,[z0,z1,z874,z3,z4,z6]),(0,[z875,z0,z1,z3,z4,z6]),(1,[z0,z714,z3,z4,z6]),(0,[z0,z1,z876,z3,z4,z6]),(0,[z0,z1,z3,z877,z4,z6])],[(0,[z0,z26,z3,z470,z4,z6]),(0,[z554,z0,z232,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z878]),(0,[z0,z879,z1,z3,z4,z6]),(0,[z0,z220,z37,z3,z4,z6]),(0,[z0,z50,z2,z3,z300,z4]),(0,[z880,z0,z1,z2,z4,z6]),(0,[z0,z2,z3,z4,z713,z6]),(0,[z819,z168,z0,z3,z4,z6])],[(0,[z0,z1,z881,z3,z4,z6]),(0,[z882,z0,z1,z3,z4,z6]),(0,[z0,z729,z1,z3,z4,z6]),(0,[z36,z260,z2,z3,z4,z6]),(0,[z0,z1,z3,z883,z4,z6]),(0,[z0,z3,z354,z4,z67,z6]),(0,[z0,z884,z62,z3,z4,z6]),(0,[z124,z76,z2,z3,z4,z6]),(0,[z0,z2,z885,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z886]),(0,[z0,z887,z2,z3,z4,z6]),(0,[z0,z1,z888,z3,z4,z6]),(0,[z0,z3,z133,z4,z623,z6]),(0,[z0,z1,z889,z3,z4,z6]),(0,[z45,z1,z374,z3,z4,z6])],[(0,[z80,z0,z232,z3,z4,z6]),(0,[z0,z1,z82,z3,z4,z6]),(0,[z66,z1,z3,z4,z319,z6]),(0,[z890,z0,z2,z3,z4,z6]),(0,[z46,z0,z2,z4,z267,z100])],[(0,[z891,z1,z2,z3,z4,z6]),(0,[z0,z37,z1,z3,z4,z25]),(1,[z0,z26,z3,z300,z4]),(0,[z0,z1,z62,z3,z504,z6]),(0,[z0,z892,z3,z4,z67,z6]),(0,[z0,z190,z2,z3,z4,z390])],[(0,[z0,z1,z893,z3,z4,z6]),(0,[z42,z96,z1,z435,z4,z6]),(0,[z0,z26,z545,z3,z4,z6]),(0,[z894,z1,z62,z3,z4,z6])],[(0,[z52,z0,z1,z895,z4,z6]),(0,[z896,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z897,z6])],[(0,[z193,z0,z3,z4,z167,z6]),(0,[z0,z1,z898,z3,z4,z6]),(0,[z0,z3,z4,z6,z267,z899])],[(0,[z126,z0,z1,z3,z4,z6]),(0,[z0,z1,z900,z3,z4,z6]),(0,[z66,z26,z1,z3,z4,z6]),(0,[z0,z901,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z589,z57]),(0,[z114,z0,z2,z3,z4,z10]),(0,[z0,z1,z3,z902,z4,z6]),(0,[z0,z1,z62,z3,z4,z238]),(0,[z0,z1,z198,z3,z4,z390])]],
   [[(0,[z66,z1,z3,z134,z4,z6]),(0,[z117,z1,z62,z3,z4,z239]),(0,[z0,z903,z1,z3,z4,z6]),(0,[z0,z2,z3,z4,z167,z704]),(0,[z1,z2,z3,z904,z4,z6]),(0,[z0,z905,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z906,z6]),(0,[z1,z2,z3,z4,z514,z6]),(0,[z0,z907,z2,z3,z4,z6]),(0,[z24,z47,z2,z3,z48,z6]),(0,[z0,z26,z3,z247,z53,z4]),(0,[z0,z908,z2,z3,z4,z6]),(0,[z0,z220,z3,z4,z319,z6]),(0,[z0,z909,z3,z212,z4,z6]),(0,[z0,z1,z2,z146,z3,z910])],[(0,[z24,z42,z1,z3,z134,z6]),(0,[z376,z76,z2,z3,z4,z6])],[(0,[z41,z116,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z25]),(0,[z0,z1,z3,z4,z911,z6]),(0,[z0,z1,z2,z3,z573,z14])],[(0,[z0,z1,z912,z3,z4,z6]),(0,[z52,z0,z913,z3,z4,z6]),(0,[z0,z26,z304,z3,z4,z6]),(0,[z0,z914,z1,z3,z4,z6]),(0,[z0,z87,z89,z3,z4,z6]),(0,[z0,z915,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z916]),(0,[z917,z66,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z910,z14])],[(0,[z41,z0,z220,z3,z4,z6]),(0,[z42,z1,z3,z184,z4,z6]),(0,[z0,z232,z3,z471,z4,z6]),(0,[z0,z918,z2,z3,z4,z6]),(0,[z0,z87,z2,z3,z4,z371]),(0,[z0,z253,z62,z3,z4,z6]),(0,[z0,z1,z3,z919,z4,z6])],[(0,[z920,z0,z1,z3,z4,z6]),(0,[z0,z26,z3,z133,z4,z6]),(0,[z0,z1,z921,z3,z4,z6]),(0,[z0,z1,z922,z3,z4,z6]),(0,[z923,z1,z2,z3,z4,z6]),(0,[z0,z924,z2,z3,z4,z6])],[(0,[z925,z0,z2,z3,z4,z6]),(0,[z0,z1,z926,z3,z4,z6]),(0,[z0,z220,z3,z134,z4,z6]),(0,[z927,z1,z3,z4,z623,z6]),(0,[z36,z0,z2,z615,z3,z4]),(0,[z126,z1,z498,z3,z4,z6]),(0,[z0,z1,z3,z4,z928,z6])],[(0,[z42,z1,z2,z31,z4,z6]),(0,[z0,z26,z845,z3,z4,z6]),(0,[z741,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z929]),(0,[z0,z930,z1,z3,z4,z6])],[(0,[z332,z42,z0,z53,z4,z6]),(0,[z0,z931,z2,z3,z4,z6]),(0,[z0,z87,z380,z3,z4,z6]),(0,[z0,z1,z932,z3,z4,z6])],[(0,[z0,z26,z586,z3,z4,z6]),(0,[z1,z2,z31,z4,z48,z6]),(0,[z1,z2,z3,z933,z4,z6])],[(0,[z281,z0,z1,z3,z249,z6]),(0,[z0,z1,z2,z934,z4,z6]),(0,[z24,z1,z3,z48,z67,z6]),(0,[z0,z183,z3,z53,z4,z6]),(0,[z150,z0,z2,z3,z935,z6]),(0,[z0,z1,z3,z298,z936,z6])],[(0,[z0,z1,z937,z3,z4,z6]),(0,[z96,z1,z228,z3,z4,z6]),(0,[z0,z26,z685,z3,z4,z6]),(0,[z0,z1,z2,z3,z938,z6]),(0,[z150,z0,z3,z192,z10,z6]),(0,[z0,z1,z2,z447,z3,z181])],[(0,[z0,z1,z22,z435,z4,z6]),(0,[z1,z2,z188,z4,z701,z6]),(0,[z0,z26,z3,z414,z4,z6]),(0,[z26,z1,z3,z4,z848,z6]),(0,[z0,z564,z1,z3,z4,z589]),(0,[z0,z37,z3,z4,z151,z6]),(0,[z939,z260,z1,z3,z4,z6]),(0,[z940,z0,z1,z3,z4,z6]),(0,[z66,z1,z3,z181,z4,z6]),(0,[z0,z240,z220,z3,z4,z6]),(0,[z941,z0,z1,z3,z4,z6]),(0,[z0,z942,z158,z3,z4,z6]),(0,[z0,z943,z1,z3,z4,z6])],[(0,[z42,z327,z1,z3,z4,z6]),(0,[z0,z944,z232,z3,z4,z6]),(0,[z0,z945,z1,z3,z4,z6]),(0,[z0,z220,z49,z3,z4,z6]),(0,[z0,z76,z2,z3,z4,z390])],[(0,[z0,z946,z1,z3,z4,z6]),(0,[z0,z26,z3,z495,z4,z6]),(0,[z260,z87,z2,z3,z4,z6]),(0,[z0,z37,z1,z97,z4,z6]),(0,[z0,z947,z2,z3,z4,z6]),(0,[z0,z948,z1,z3,z4,z6])]],
   [[(0,[z454,z0,z1,z169,z4,z6]),(0,[z0,z232,z3,z4,z6,z174]),(0,[z66,z1,z3,z188,z4,z6]),(0,[z0,z26,z3,z4,z6,z416]),(0,[z0,z1,z949,z3,z4,z6]),(0,[z950,z1,z2,z3,z4,z6]),(0,[z0,z17,z2,z146,z3,z181])],[(0,[z42,z1,z3,z51,z4,z6]),(0,[z0,z37,z83,z3,z4,z6]),(0,[z0,z26,z3,z4,z499,z6]),(0,[z66,z61,z1,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z951]),(0,[z0,z952,z76,z3,z4,z6])],[(0,[z126,z42,z1,z3,z4,z6]),(0,[z953,z0,z1,z3,z4,z6]),(0,[z24,z1,z2,z3,z48,z25]),(0,[z0,z1,z3,z954,z4,z6]),(0,[z0,z1,z3,z4,z6,z955]),(0,[z0,z1,z3,z4,z956,z6]),(0,[z0,z1,z23,z843,z4,z6]),(0,[z189,z0,z1,z62,z55,z6])],[(0,[z0,z26,z3,z4,z500,z6]),(0,[z128,z26,z137,z3,z4,z6]),(0,[z957,z0,z232,z3,z4,z6]),(0,[z958,z0,z1,z3,z4,z6]),(0,[z959,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z960,z6]),(1,[z66,z220,z3,z4,z6])],[(0,[z0,z26,z3,z501,z4,z6]),(0,[z0,z961,z1,z3,z4,z6]),(0,[z1,z2,z3,z962,z4,z6]),(0,[z0,z220,z3,z181,z4,z6])],[(0,[z193,z327,z1,z3,z4,z6]),(0,[z0,z1,z843,z56,z4,z6]),(0,[z0,z1,z135,z4,z67,z119]),(0,[z0,z963,z2,z3,z4,z6])],[(0,[z1,z3,z134,z4,z290,z6]),(0,[z1,z2,z3,z964,z4,z6]),(0,[z0,z26,z3,z354,z4,z6]),(0,[z0,z205,z1,z571,z4,z6]),(0,[z0,z1,z3,z532,z4,z57]),(0,[z965,z0,z1,z3,z4,z6])],[(0,[z0,z232,z3,z4,z6,z100]),(0,[z0,z1,z2,z97,z4,z6]),(0,[z0,z220,z3,z188,z4,z6]),(0,[z68,z0,z220,z3,z4,z6]),(0,[z0,z26,z1,z127,z212,z6]),(0,[z1,z62,z3,z4,z514,z6])],[(0,[z41,z160,z2,z3,z4,z6]),(0,[z0,z232,z18,z3,z4,z6]),(0,[z0,z914,z3,z188,z4,z6])],[(0,[z0,z1,z2,z966,z4,z6]),(0,[z42,z559,z1,z3,z4,z6]),(0,[z535,z61,z2,z3,z4,z6]),(0,[z0,z1,z967,z3,z4,z6]),(0,[z0,z968,z1,z3,z4,z6])],[(0,[z969,z0,z1,z3,z4,z6]),(0,[z640,z0,z26,z3,z4,z6]),(0,[z61,z2,z18,z439,z4,z6]),(0,[z0,z1,z3,z4,z970,z6]),(0,[z971,z0,z1,z3,z4,z6]),(0,[z0,z1,z972,z3,z4,z6]),(0,[z0,z3,z973,z4,z67,z6]),(0,[z0,z1,z2,z146,z3,z596]),(0,[z46,z95,z1,z2,z4,z100]),(0,[z46,z0,z253,z2,z4,z100])],[(0,[z137,z2,z3,z4,z288,z6]),(0,[z1,z2,z572,z188,z4,z6]),(0,[z0,z1,z3,z4,z974,z6]),(0,[z0,z26,z3,z427,z4,z6]),(0,[z975,z45,z1,z3,z4,z6])],[(0,[z147,z0,z304,z3,z4,z6]),(0,[z150,z0,z240,z3,z4,z6]),(0,[z0,z1,z3,z300,z4,z67]),(0,[z0,z1,z976,z3,z4,z6]),(0,[z917,z0,z220,z3,z4,z6]),(0,[z95,z1,z82,z3,z4,z6])],[(0,[z0,z1,z977,z3,z4,z6]),(0,[z1,z978,z2,z3,z4,z6]),(0,[z147,z0,z1,z3,z249,z6]),(0,[z52,z0,z1,z3,z155,z6]),(0,[z0,z1,z214,z3,z4,z6]),(0,[z0,z1,z241,z3,z4,z6]),(0,[z0,z979,z1,z3,z4,z6])],[(0,[z359,z0,z1,z3,z4,z6]),(0,[z1,z3,z4,z514,z105,z6]),(0,[z332,z66,z1,z3,z4,z6]),(0,[z0,z980,z1,z3,z4,z6])],[(0,[z0,z1,z2,z981,z4,z6]),(0,[z0,z1,z3,z4,z982,z6]),(0,[z0,z304,z62,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z983]),(0,[z0,z1,z3,z4,z984,z6]),(0,[z0,z1,z3,z985,z4,z6]),(0,[z0,z986,z2,z3,z4,z6]),(0,[z987,z0,z1,z3,z4,z6]),(0,[z0,z26,z3,z434,z4,z6]),(0,[z0,z3,z4,z67,z6,z267]),(0,[z0,z190,z437,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z988,z6]),(0,[z24,z42,z1,z3,z4,z25]),(0,[z0,z1,z3,z989,z4,z6]),(0,[z0,z1,z3,z4,z990,z6]),(0,[z66,z1,z3,z4,z151,z6]),(0,[z0,z3,z4,z67,z861,z6])],[(0,[z0,z1,z3,z4,z991,z6]),(0,[z42,z0,z1,z3,z155,z6]),(0,[z0,z2,z3,z4,z992,z6]),(0,[z0,z1,z3,z4,z993,z6]),(0,[z0,z158,z3,z4,z67,z6]),(0,[z994,z376,z1,z3,z4,z6]),(0,[z590,z0,z1,z2,z55,z6])],[(0,[z0,z1,z995,z3,z4,z6]),(0,[z0,z1,z3,z4,z445,z6]),(0,[z211,z0,z26,z3,z4,z6])],[(0,[z0,z1,z3,z4,z996,z6]),(0,[z0,z37,z17,z3,z4,z6]),(0,[z1,z22,z23,z51,z4,z6]),(0,[z0,z3,z4,z151,z67,z6]),(0,[z0,z1,z997,z3,z4,z6]),(0,[z0,z998,z2,z3,z4,z6])],[(0,[z68,z0,z711,z3,z4,z6]),(0,[z260,z1,z62,z3,z4,z6]),(0,[z3,z4,z151,z514,z67,z6]),(0,[z0,z1,z3,z4,z6,z999])],[(0,[z1,z2,z3,z134,z523,z6]),(1,[z927,z1,z3,z4,z6]),(0,[z26,z1,z3,z4,z514,z6]),(0,[z0,z37,z190,z3,z4,z6]),(0,[z0,z61,z2,z650,z4,z6]),(0,[z129,z0,z3,z151,z67,z6]),(0,[z0,z1,z374,z3,z155,z6])],[(0,[z0,z1,z1000,z3,z4,z6]),(0,[z24,z1,z2,z97,z48,z6]),(0,[z0,z2,z3,z820,z4,z6]),(0,[z1001,z1,z3,z4,z67,z6]),(0,[z0,z1,z1002,z3,z4,z6])],[(0,[z52,z299,z1,z3,z4,z6]),(0,[z52,z0,z1,z3,z4,z1003]),(0,[z0,z1,z3,z4,z1004,z6]),(0,[z0,z1,z3,z4,z6,z1005]),(0,[z1006,z0,z1,z3,z4,z6]),(0,[z0,z1,z1007,z3,z4,z6]),(0,[z0,z220,z3,z4,z151,z6])],[(0,[z42,z1,z409,z3,z4,z6]),(0,[z0,z1,z23,z471,z4,z6]),(0,[z0,z1008,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1009]),(0,[z0,z1010,z1,z3,z4,z6]),(0,[z332,z0,z2,z33,z4,z6])],[(0,[z1011,z66,z1,z3,z4,z6]),(0,[z0,z710,z158,z3,z4,z6])],[(0,[z114,z0,z26,z3,z4,z6])],[(0,[z0,z1,z570,z3,z4,z6]),(0,[z0,z1,z1012,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1013]),(0,[z0,z2,z3,z4,z167,z121]),(0,[z0,z220,z83,z3,z4,z6]),(0,[z66,z1,z3,z1014,z4,z6])],[(0,[z0,z37,z1,z3,z4,z6]),(0,[z24,z1,z78,z3,z4,z6]),(0,[z0,z1,z2,z3,z1015,z4]),(0,[z652,z42,z1,z3,z4,z6]),(0,[z0,z232,z50,z3,z4,z6]),(0,[z52,z0,z451,z3,z4,z6]),(0,[z0,z1,z1016,z3,z4,z6]),(0,[z0,z1,z223,z3,z4,z670]),(0,[z419,z156,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1017,z6])],[(0,[z42,z1,z556,z3,z4,z6]),(0,[z117,z0,z232,z3,z4,z6]),(0,[z0,z26,z1,z3,z298,z6]),(0,[z37,z1,z3,z4,z514,z6]),(0,[z38,z369,z1,z3,z4,z6]),(0,[z0,z1,z3,z1018,z4,z6])],[(0,[z0,z1,z1019,z3,z4,z6]),(0,[z0,z232,z515,z3,z4,z6]),(0,[z332,z0,z2,z820,z4,z6]),(0,[z66,z1,z3,z102,z4,z6]),(0,[z0,z176,z82,z3,z4,z6])],[(0,[z0,z1,z1020,z3,z4,z6]),(0,[z42,z0,z1,z3,z13,z14]),(0,[z0,z1021,z1,z3,z4,z6]),(0,[z128,z0,z3,z4,z167,z6]),(0,[z0,z1022,z1,z3,z4,z6]),(0,[z150,z2,z3,z9,z10,z6])]],
   [[(0,[z260,z42,z1,z3,z4,z6]),(0,[z66,z1,z2,z3,z4,z6]),(0,[z42,z0,z451,z3,z4,z6]),(0,[z24,z2,z3,z153,z48,z6]),(0,[z150,z0,z26,z3,z504,z6]),(0,[z0,z2,z3,z4,z167,z1023]),(0,[z0,z1,z3,z869,z4,z67])],[(0,[z41,z64,z2,z3,z4,z6]),(0,[z170,z42,z137,z3,z4,z6]),(0,[z42,z0,z1024,z3,z4,z6]),(0,[z264,z0,z1,z3,z4,z336]),(0,[z0,z87,z2,z31,z4,z6]),(0,[z37,z1,z3,z439,z4,z6]),(0,[z1025,z0,z1,z3,z4,z6]),(0,[z1026,z0,z1,z3,z4,z6])],[(0,[z129,z0,z1,z3,z290,z6]),(0,[z0,z232,z62,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1027]),(0,[z369,z26,z1,z3,z4,z6]),(0,[z114,z0,z433,z1,z3,z4]),(0,[z0,z1,z3,z1028,z4,z6]),(0,[z0,z76,z437,z3,z4,z6])],[(0,[z419,z1,z141,z3,z4,z6]),(0,[z80,z37,z1,z188,z4,z6]),(0,[z332,z0,z26,z53,z4,z6]),(0,[z0,z1,z3,z1029,z4,z6]),(0,[z0,z1,z3,z521,z67,z6]),(0,[z1030,z0,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z139,z419,z1,z3,z4,z6]),(0,[z579,z137,z2,z3,z4,z6]),(0,[z42,z0,z1,z3,z4,z1031]),(0,[z24,z42,z1,z97,z4,z6]),(0,[z927,z0,z1,z3,z4,z6]),(0,[z0,z1032,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1033]),(0,[z0,z1,z2,z3,z910,z4])],[(0,[z1034,z0,z1,z3,z4,z6]),(0,[z41,z0,z2,z3,z300,z4]),(0,[z24,z104,z1,z3,z4,z6]),(0,[z0,z232,z146,z3,z4,z6]),(0,[z52,z1,z3,z4,z373,z6]),(0,[z1,z3,z4,z9,z67,z6]),(0,[z0,z1,z2,z3,z1035,z6]),(0,[z0,z220,z3,z102,z4,z6]),(0,[z1036,z0,z1,z2,z3,z4]),(0,[z46,z0,z1,z2,z4,z100])],[(0,[z0,z232,z135,z3,z4,z6]),(0,[z52,z0,z34,z3,z4,z167]),(0,[z123,z1,z3,z4,z269,z174]),(0,[z332,z0,z220,z3,z4,z6]),(0,[z0,z220,z3,z4,z301,z6]),(0,[z0,z253,z3,z4,z67,z6]),(0,[z0,z1037,z2,z3,z4,z6])],[(0,[z0,z1,z1038,z3,z4,z6]),(0,[z0,z232,z23,z3,z4,z6])],[(0,[z137,z87,z2,z3,z4,z6]),(0,[z0,z913,z2,z3,z4,z6]),(0,[z0,z914,z2,z3,z4,z6]),(0,[z0,z271,z2,z3,z4,z25]),(0,[z0,z473,z173,z3,z4,z6]),(0,[z896,z37,z1,z3,z4,z6]),(0,[z0,z2,z3,z4,z1039,z6]),(0,[z0,z1,z62,z146,z3,z181])],[(0,[z170,z114,z0,z2,z3,z4]),(0,[z197,z42,z1,z3,z4,z6]),(0,[z0,z1,z1040,z3,z4,z6]),(0,[z0,z1,z3,z1041,z4,z6]),(0,[z0,z1,z3,z4,z1042,z6]),(0,[z746,z0,z1,z3,z4,z6]),(0,[z0,z3,z1043,z443,z4,z6])],[(0,[z42,z0,z34,z3,z4,z167]),(0,[z42,z1,z3,z293,z4,z6]),(0,[z0,z1,z3,z4,z1044,z6]),(0,[z0,z152,z3,z4,z224,z6]),(0,[z953,z95,z1,z3,z4,z6])],[(0,[z265,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1045]),(0,[z52,z45,z1,z3,z4,z6]),(0,[z80,z1,z2,z188,z4,z6]),(0,[z24,z37,z1,z3,z48,z6]),(0,[z0,z1046,z3,z4,z67,z6]),(0,[z0,z1,z145,z146,z3,z181])],[(0,[z0,z1,z2,z1047,z4,z6]),(0,[z0,z26,z110,z3,z4,z6]),(0,[z0,z1048,z1,z3,z4,z6]),(1,[z114,z0,z26,z3,z4]),(0,[z0,z721,z1,z3,z4,z6]),(0,[z1049,z1,z3,z4,z67,z6]),(0,[z0,z1,z3,z4,z6,z1050])],[(0,[z24,z193,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1051,z6]),(0,[z0,z1,z2,z3,z4,z1052]),(0,[z0,z2,z3,z1053,z4,z6])],[(0,[z234,z66,z1,z3,z4,z6]),(0,[z1030,z1,z3,z212,z4,z6]),(0,[z1054,z0,z1,z3,z4,z6])],[(0,[z0,z183,z137,z3,z4,z6]),(0,[z42,z45,z1,z3,z4,z6]),(0,[z0,z473,z2,z3,z181,z4]),(0,[z535,z37,z1,z3,z4,z6]),(0,[z1055,z1,z2,z3,z4,z6]),(0,[z0,z1,z1056,z3,z4,z6]),(0,[z46,z99,z0,z1,z4,z100])]],
   [[(0,[z1057,z0,z1,z3,z4,z6]),(0,[z234,z68,z1,z3,z134,z6]),(0,[z0,z26,z550,z3,z4,z6])],[(0,[z0,z2,z3,z4,z384,z6]),(0,[z0,z74,z37,z3,z4,z6]),(0,[z150,z52,z0,z3,z10,z6]),(0,[z52,z0,z1,z3,z4,z238]),(1,[z0,z914,z3,z4,z6]),(0,[z0,z1,z1058,z3,z4,z6]),(0,[z0,z1,z3,z4,z1059,z6]),(0,[z0,z1,z2,z4,z6,z1060]),(0,[z0,z3,z4,z67,z6,z951]),(0,[z38,z0,z1,z3,z4,z1061]),(0,[z1062,z124,z1,z3,z4,z6])],[(0,[z1,z2,z3,z1063,z4,z6]),(0,[z0,z1,z2,z127,z870,z6]),(1,[z0,z1,z2,z4,z762]),(0,[z1064,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z1065]),(0,[z24,z1,z2,z3,z48,z6]),(0,[z0,z773,z1,z3,z4,z6]),(0,[z0,z26,z3,z480,z4,z6]),(0,[z0,z37,z261,z3,z4,z6]),(0,[z741,z37,z1,z3,z4,z6]),(0,[z114,z0,z1,z62,z3,z4])],[(0,[z260,z77,z2,z3,z4,z6]),(0,[z0,z1,z1066,z3,z4,z6]),(0,[z0,z20,z3,z4,z167,z6]),(0,[z66,z1,z223,z3,z4,z6])],[(0,[z137,z2,z3,z344,z4,z6]),(0,[z42,z0,z1,z3,z4,z238]),(0,[z0,z232,z232,z3,z4,z6]),(0,[z52,z0,z1,z3,z247,z4]),(0,[z1067,z1,z2,z3,z4,z6]),(0,[z189,z0,z1,z198,z55,z6])],[(0,[z52,z1,z3,z4,z6,z395]),(0,[z0,z220,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1068]),(0,[z1069,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z522,z4,z119])],[(0,[z535,z1,z2,z3,z4,z6]),(0,[z170,z2,z3,z4,z6,z338]),(0,[z0,z1,z1070,z3,z4,z6]),(0,[z0,z26,z98,z3,z4,z6]),(0,[z332,z0,z37,z53,z4,z6]),(0,[z0,z816,z3,z13,z4,z6]),(0,[z0,z1,z3,z4,z6,z1071])],[(0,[z0,z1,z3,z4,z1072,z6]),(0,[z117,z419,z1,z3,z4,z6]),(0,[z0,z1,z845,z3,z4,z6]),(0,[z0,z62,z3,z4,z6,z267])],[(0,[z42,z0,z1,z3,z247,z4]),(0,[z0,z1,z3,z249,z67,z6]),(0,[z0,z1,z3,z1073,z4,z6]),(0,[z0,z340,z26,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1074]),(0,[z0,z1,z127,z212,z306,z6]),(0,[z0,z1,z821,z3,z298,z6])],[(0,[z0,z1,z2,z3,z4,z1075]),(0,[z0,z26,z648,z3,z4,z6]),(0,[z0,z1,z1076,z3,z4,z6]),(0,[z1077,z0,z1,z3,z4,z6]),(0,[z0,z3,z4,z67,z6,z12])],[(0,[z193,z0,z104,z3,z4,z6]),(0,[z0,z1,z1078,z3,z4,z6]),(0,[z1079,z1,z2,z3,z4,z6]),(0,[z0,z220,z223,z3,z4,z6])],[(0,[z42,z466,z1,z3,z4,z6]),(0,[z0,z232,z3,z4,z55,z6]),(0,[z0,z271,z2,z97,z4,z6]),(0,[z0,z1,z2,z3,z425,z14]),(0,[z0,z1,z3,z1080,z4,z6])],[(0,[z0,z2,z3,z4,z153,z6]),(0,[z376,z1,z3,z4,z67,z6]),(0,[z0,z2,z3,z1081,z4,z6]),(0,[z994,z0,z1,z3,z4,z6]),(0,[z0,z1082,z2,z3,z4,z6]),(0,[z590,z0,z1,z2,z4,z100])],[(0,[z0,z1,z1083,z3,z4,z6]),(0,[z52,z0,z3,z4,z6,z267]),(0,[z95,z37,z1,z3,z4,z6]),(0,[z0,z1084,z220,z3,z4,z6]),(0,[z0,z1,z3,z298,z67,z6])],[(0,[z128,z41,z1,z3,z4,z6]),(0,[z66,z1,z3,z4,z418,z6]),(0,[z1085,z0,z1,z3,z4,z6]),(0,[z0,z253,z374,z3,z4,z6])]],
   [[(0,[z0,z232,z3,z1086,z4,z6]),(0,[z0,z304,z3,z4,z67,z6]),(0,[z0,z2,z3,z4,z6,z1087]),(0,[z0,z1,z3,z4,z6,z416]),(0,[z0,z2,z3,z4,z1023,z21]),(0,[z2,z3,z51,z354,z4,z6])],[(0,[z24,z42,z1,z3,z4,z6]),(0,[z42,z1,z3,z134,z4,z6]),(0,[z168,z42,z0,z3,z4,z6]),(0,[z0,z1,z3,z4,z499,z6]),(0,[z46,z168,z0,z2,z4,z100])],[(0,[z0,z1,z3,z1088,z4,z6]),(0,[z0,z1,z1089,z3,z4,z6]),(0,[z42,z0,z3,z4,z6,z267]),(0,[z128,z0,z232,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1090]),(0,[z81,z0,z3,z4,z153,z6]),(0,[z66,z1,z3,z4,z1091,z6]),(0,[z0,z1,z62,z3,z4,z363])],[(0,[z917,z0,z1,z3,z4,z6]),(0,[z80,z66,z1,z3,z4,z6]),(0,[z0,z213,z1,z3,z4,z670]),(0,[z828,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z1092,z4,z6]),(0,[z0,z1,z2,z3,z212,z390])],[(0,[z0,z37,z253,z3,z4,z6]),(0,[z0,z1,z1093,z3,z4,z6])],[(0,[z0,z1,z441,z3,z4,z6]),(0,[z1094,z0,z1,z3,z4,z6]),(0,[z0,z37,z29,z3,z4,z6]),(0,[z52,z0,z76,z3,z4,z6]),(0,[z0,z1,z3,z4,z1095,z6]),(0,[z126,z1,z185,z3,z4,z6]),(0,[z36,z0,z26,z3,z4,z21]),(0,[z260,z1,z3,z4,z67,z6]),(0,[z0,z50,z3,z133,z67,z6]),(0,[z124,z1,z62,z3,z4,z6]),(0,[z0,z1,z1096,z3,z4,z6])],[(0,[z42,z582,z1,z3,z4,z6]),(0,[z46,z52,z0,z1,z4,z100]),(0,[z95,z1,z2,z3,z4,z6]),(0,[z0,z1,z1097,z3,z4,z6]),(0,[z0,z220,z3,z4,z418,z6]),(0,[z189,z0,z76,z2,z55,z6])],[(0,[z24,z1,z2,z3,z485,z6]),(0,[z0,z220,z137,z3,z4,z6]),(0,[z52,z0,z50,z3,z133,z6]),(0,[z0,z26,z118,z3,z4,z6]),(0,[z1098,z1,z2,z3,z4,z6]),(0,[z150,z0,z1,z3,z445,z6])],[(0,[z193,z1,z3,z134,z4,z6]),(0,[z123,z26,z1,z3,z4,z174]),(0,[z0,z26,z61,z18,z4,z6]),(0,[z741,z50,z1,z3,z4,z6]),(0,[z0,z1099,z2,z3,z4,z6]),(0,[z0,z1,z1100,z3,z4,z6]),(0,[z1101,z0,z1,z3,z4,z6])],[(0,[z52,z0,z232,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1102]),(0,[z42,z0,z76,z3,z4,z6]),(0,[z1103,z0,z1,z3,z4,z6]),(0,[z0,z110,z3,z70,z4,z6]),(0,[z0,z26,z205,z3,z4,z6])],[(0,[z42,z96,z1,z143,z4,z6]),(0,[z0,z1,z1104,z3,z4,z6]),(0,[z0,z37,z86,z3,z4,z6]),(1,[z0,z2,z820,z4,z6]),(0,[z0,z1,z1105,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z1106])],[(0,[z52,z0,z1107,z3,z4,z6]),(0,[z518,z0,z26,z3,z4,z6]),(0,[z369,z37,z1,z3,z4,z6]),(0,[z1108,z0,z1,z3,z4,z6]),(0,[z1109,z0,z1,z2,z4,z6]),(0,[z0,z1,z3,z4,z1110,z6])],[(0,[z1,z78,z3,z134,z4,z6]),(0,[z42,z0,z1111,z3,z4,z6]),(0,[z42,z0,z1112,z3,z4,z6]),(0,[z0,z1113,z1,z3,z4,z6]),(0,[z0,z1,z3,z1114,z4,z6]),(0,[z1115,z1,z2,z3,z4,z6]),(0,[z0,z220,z1116,z3,z4,z6])],[(0,[z42,z0,z232,z3,z4,z6]),(0,[z0,z1,z62,z3,z4,z371]),(0,[z0,z2,z3,z4,z6,z12]),(0,[z114,z0,z1,z3,z480,z4]),(0,[z0,z1,z2,z3,z1117,z4])],[(0,[z0,z1118,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1119,z6]),(0,[z1,z3,z4,z514,z67,z6]),(0,[z0,z1,z2,z3,z298,z6])],[(0,[z0,z1,z3,z4,z1120,z6]),(0,[z0,z26,z160,z3,z4,z6]),(0,[z376,z1,z62,z3,z4,z6]),(0,[z46,z0,z1,z2,z298,z100]),(0,[z0,z942,z1,z3,z4,z6])]],
   [[(0,[z170,z137,z78,z3,z4,z6]),(0,[z0,z1,z3,z4,z1121,z6]),(0,[z0,z1122,z2,z3,z4,z6])],[(0,[z66,z137,z1,z3,z4,z6]),(0,[z42,z1,z3,z188,z4,z6]),(0,[z0,z328,z50,z3,z4,z6]),(0,[z36,z0,z3,z4,z142,z21]),(0,[z0,z152,z3,z56,z4,z6]),(0,[z1123,z0,z2,z3,z4,z6])],[(0,[z66,z1,z77,z3,z4,z6]),(0,[z42,z684,z1,z3,z4,z6]),(0,[z0,z1124,z1,z3,z4,z6]),(1,[z0,z220,z3,z4,z6]),(0,[z0,z451,z3,z4,z224,z6]),(0,[z66,z3,z4,z151,z67,z6]),(0,[z0,z1,z3,z67,z6,z28])],[(0,[z369,z1,z2,z3,z4,z6]),(0,[z0,z173,z1,z3,z4,z6]),(0,[z0,z232,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z350,z14]),(0,[z0,z823,z1,z3,z4,z6]),(0,[z0,z49,z1,z3,z445,z6]),(0,[z0,z220,z241,z3,z4,z6]),(0,[z369,z451,z2,z3,z4,z6])],[(0,[z41,z340,z2,z3,z4,z6]),(0,[z193,z0,z232,z3,z4,z6]),(0,[z0,z232,z61,z3,z4,z6]),(0,[z0,z787,z2,z3,z4,z6]),(0,[z0,z240,z3,z53,z4,z6]),(0,[z0,z26,z1,z3,z13,z14]),(0,[z0,z1125,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1126,z6]),(0,[z0,z2,z3,z4,z1127,z6]),(0,[z0,z232,z3,z4,z8,z6]),(0,[z0,z1128,z2,z3,z4,z6]),(0,[z1129,z1,z2,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1130,z6]),(0,[z66,z1,z1131,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1132,z6]),(0,[z0,z2,z3,z1133,z4,z6]),(0,[z0,z1,z82,z3,z298,z6])],[(0,[z193,z1,z3,z188,z4,z6]),(0,[z150,z0,z3,z4,z623,z6]),(0,[z0,z26,z3,z519,z4,z6]),(0,[z0,z1,z2,z3,z4,z1134]),(0,[z0,z176,z2,z3,z4,z6])],[(0,[z0,z271,z2,z3,z4,z6]),(0,[z0,z220,z77,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z736]),(0,[z1,z2,z3,z134,z649,z6]),(0,[z1,z2,z964,z188,z4,z6]),(0,[z36,z0,z37,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z1061])],[(0,[z0,z61,z441,z3,z4,z6]),(0,[z0,z1135,z2,z3,z4,z6]),(0,[z0,z37,z3,z4,z477,z6]),(0,[z0,z1136,z2,z3,z4,z6])],[(0,[z285,z0,z26,z3,z4,z6]),(0,[z42,z1,z3,z355,z4,z6]),(0,[z80,z0,z220,z3,z4,z6]),(0,[z0,z1,z62,z3,z623,z6]),(0,[z66,z37,z1,z3,z4,z6]),(0,[z0,z1,z1137,z3,z4,z6]),(0,[z0,z2,z1138,z3,z4,z6]),(0,[z0,z1,z62,z3,z4,z390]),(0,[z0,z1,z3,z1139,z4,z6])],[(0,[z1,z78,z3,z188,z4,z6]),(0,[z52,z42,z232,z3,z4,z6]),(0,[z0,z26,z3,z4,z589,z6]),(0,[z46,z0,z1,z2,z33,z4]),(0,[z0,z1,z3,z67,z69,z6])],[(0,[z45,z26,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z1140,z4])],[(0,[z42,z1,z3,z360,z4,z6]),(0,[z36,z42,z0,z3,z4,z21]),(0,[z0,z26,z61,z399,z4,z6]),(1,[z66,z3,z4,z151,z6]),(0,[z0,z1141,z76,z3,z4,z6]),(0,[z0,z1,z1142,z3,z4,z6])],[(0,[z0,z1143,z1,z3,z4,z6]),(1,[z0,z711,z3,z4,z6]),(0,[z0,z2,z1144,z3,z4,z6]),(0,[z0,z26,z3,z4,z167,z6]),(0,[z189,z0,z1,z67,z55,z6])]],
   [[(0,[z0,z37,z304,z3,z4,z6]),(0,[z0,z1,z2,z3,z1145,z6]),(0,[z66,z1,z3,z4,z48,z6]),(0,[z36,z0,z26,z3,z4,z14]),(0,[z0,z1146,z220,z3,z4,z6])],[(0,[z41,z87,z2,z3,z4,z6]),(0,[z1147,z0,z1,z2,z3,z4]),(0,[z0,z156,z232,z3,z4,z6]),(0,[z0,z3,z4,z67,z384,z6]),(0,[z0,z183,z1,z3,z4,z6]),(0,[z0,z61,z256,z18,z4,z6]),(0,[z0,z1,z2,z3,z935,z6]),(0,[z1148,z0,z220,z3,z4,z6]),(0,[z0,z1149,z3,z4,z67,z6]),(0,[z1150,z0,z2,z3,z4,z6])],[(0,[z42,z96,z1,z169,z4,z6]),(0,[z386,z42,z1,z3,z4,z6]),(0,[z114,z0,z50,z2,z3,z4]),(0,[z1151,z1,z2,z3,z4,z6]),(0,[z0,z1,z62,z135,z4,z119])],[(0,[z0,z1,z1152,z3,z4,z6]),(0,[z0,z1,z3,z19,z4,z6]),(0,[z0,z62,z3,z4,z6,z12])],[(0,[z52,z419,z1,z3,z4,z6]),(0,[z0,z110,z62,z3,z4,z6]),(0,[z0,z1,z1153,z3,z4,z6]),(0,[z0,z26,z3,z4,z598,z6]),(0,[z139,z505,z1,z3,z4,z6]),(0,[z0,z37,z845,z3,z4,z6]),(0,[z0,z183,z3,z133,z4,z6]),(0,[z66,z1,z1154,z3,z4,z6])],[(0,[z0,z473,z2,z3,z4,z6]),(0,[z0,z26,z353,z3,z4,z6]),(0,[z0,z50,z214,z3,z133,z6])],[(1,[z42,z1,z31,z4,z6]),(0,[z0,z1,z3,z1155,z4,z6]),(0,[z66,z220,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z181,z910])],[(0,[z0,z137,z441,z3,z4,z6]),(0,[z307,z0,z232,z3,z4,z6]),(0,[z0,z1,z3,z102,z249,z6]),(0,[z0,z220,z3,z4,z48,z6]),(0,[z0,z1,z1156,z3,z4,z6])],[(0,[z0,z1,z542,z3,z4,z6]),(0,[z0,z26,z603,z3,z4,z6]),(0,[z0,z26,z366,z3,z4,z6]),(0,[z24,z271,z2,z3,z48,z6]),(0,[z114,z0,z26,z3,z53,z4]),(0,[z1,z2,z3,z4,z1157,z6]),(0,[z1158,z1,z2,z3,z4,z6])],[(0,[z52,z41,z77,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1159]),(0,[z170,z137,z62,z3,z4,z6]),(0,[z52,z0,z3,z4,z6,z12]),(0,[z0,z87,z2,z3,z4,z25])],[(0,[z52,z0,z1,z146,z3,z181]),(0,[z0,z220,z2,z3,z4,z6]),(0,[z1160,z0,z1,z3,z4,z6]),(0,[z1161,z1,z2,z3,z4,z6]),(0,[z1162,z0,z1,z3,z4,z6]),(0,[z0,z816,z3,z443,z4,z6])],[(0,[z47,z0,z62,z3,z4,z6]),(0,[z26,z1,z3,z962,z4,z6]),(0,[z168,z0,z26,z3,z4,z6]),(0,[z220,z2,z3,z4,z514,z6])],[(0,[z0,z1,z3,z1163,z4,z6]),(0,[z0,z1,z62,z3,z1164,z6])],[(0,[z0,z104,z3,z4,z10,z6]),(0,[z42,z0,z3,z4,z6,z12]),(0,[z52,z0,z1165,z3,z4,z6]),(0,[z0,z1166,z2,z3,z4,z6]),(0,[z66,z1,z3,z4,z239,z6]),(0,[z0,z62,z3,z1133,z4,z6]),(0,[z0,z1,z223,z3,z4,z1061]),(0,[z1167,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z146,z3,z181]),(0,[z0,z1168,z2,z3,z4,z6])],[(0,[z104,z1,z3,z134,z4,z6]),(0,[z0,z1,z2,z804,z4,z6]),(0,[z0,z1,z2,z1169,z4,z6]),(0,[z0,z26,z3,z4,z613,z6]),(0,[z0,z1,z1170,z3,z4,z6]),(0,[z0,z1,z3,z1171,z4,z6])]],
   [[(0,[z52,z0,z1,z1172,z4,z6]),(0,[z1062,z0,z1,z3,z4,z6]),(0,[z1173,z535,z1,z3,z4,z6]),(0,[z66,z50,z1,z3,z4,z6]),(1,[z0,z1,z2,z3,z910])],[(0,[z0,z232,z185,z3,z4,z6]),(0,[z0,z1174,z1,z3,z4,z6]),(0,[z189,z0,z1,z2,z870,z6]),(0,[z0,z1175,z2,z3,z4,z6])],[(0,[z24,z0,z1,z3,z290,z6]),(0,[z0,z37,z3,z354,z4,z6])],[(0,[z193,z0,z61,z3,z4,z6]),(0,[z307,z0,z1,z471,z4,z6]),(0,[z52,z0,z87,z3,z4,z6]),(0,[z0,z1,z3,z480,z4,z6]),(0,[z0,z37,z1,z127,z212,z6]),(0,[z1,z3,z439,z19,z4,z6]),(0,[z0,z1,z2,z3,z4,z1176]),(0,[z0,z1,z3,z4,z67,z363]),(0,[z0,z1177,z1,z3,z4,z6])],[(0,[z193,z41,z77,z3,z4,z6]),(0,[z0,z220,z3,z4,z239,z6]),(0,[z0,z26,z61,z72,z4,z6]),(0,[z0,z1,z62,z3,z300,z4])],[(0,[z24,z42,z1,z3,z162,z6]),(0,[z939,z0,z1,z3,z4,z6]),(0,[z987,z47,z0,z3,z4,z6]),(0,[z0,z1,z1178,z3,z4,z6]),(0,[z66,z1,z3,z133,z4,z6]),(0,[z0,z1,z1179,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z1023]),(0,[z0,z1,z62,z3,z245,z6]),(0,[z66,z220,z1,z3,z4,z6]),(0,[z1,z1180,z62,z3,z4,z6]),(0,[z0,z1,z1181,z3,z4,z6]),(0,[z0,z2,z3,z4,z1182,z6])],[(0,[z0,z26,z156,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1183]),(0,[z535,z1,z3,z19,z4,z6]),(0,[z0,z1,z3,z1184,z4,z6]),(0,[z124,z1,z3,z4,z67,z6])],[(0,[z1185,z0,z2,z3,z4,z6]),(0,[z0,z240,z1,z3,z4,z6]),(0,[z332,z0,z2,z53,z4,z6]),(0,[z0,z1,z3,z1186,z4,z6]),(0,[z1187,z66,z1,z3,z4,z6]),(0,[z1188,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z827,z4,z6]),(0,[z402,z0,z232,z3,z4,z6])],[(0,[z1189,z0,z1,z3,z4,z6]),(0,[z123,z0,z232,z3,z4,z6]),(0,[z0,z1165,z2,z3,z4,z6]),(0,[z0,z1,z62,z31,z4,z6]),(0,[z123,z1,z2,z3,z4,z174]),(0,[z0,z3,z4,z6,z1087,z194]),(0,[z0,z26,z555,z3,z4,z6]),(0,[z0,z37,z3,z512,z4,z6]),(0,[z0,z451,z3,z56,z4,z6])],[(0,[z1190,z0,z1,z3,z4,z6]),(0,[z68,z1,z2,z3,z871,z6]),(0,[z0,z26,z667,z3,z4,z6]),(0,[z95,z176,z2,z3,z4,z6])],[(0,[z0,z1,z2,z127,z212,z6]),(0,[z0,z1,z2,z4,z119,z762])],[(0,[z52,z535,z1,z3,z4,z6]),(0,[z0,z1,z62,z3,z649,z6]),(0,[z0,z1191,z2,z3,z4,z6]),(0,[z68,z1,z62,z3,z134,z6]),(1,[z0,z823,z3,z4,z6]),(0,[z0,z3,z53,z4,z623,z6]),(0,[z0,z26,z328,z3,z4,z6]),(0,[z0,z50,z2,z3,z133,z6]),(0,[z0,z220,z3,z133,z4,z6]),(0,[z242,z0,z1,z56,z4,z6])],[(1,[z66,z1,z3,z4,z6]),(0,[z0,z1192,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1023]),(0,[z0,z1193,z1,z3,z4,z6]),(0,[z1,z2,z3,z1194,z4,z6]),(0,[z748,z1,z3,z4,z67,z6])],[(0,[z0,z1,z2,z3,z1195,z6]),(0,[z0,z1,z2,z3,z4,z1196]),(0,[z0,z1,z3,z4,z67,z371]),(0,[z0,z26,z3,z300,z4,z6]),(0,[z0,z2,z3,z4,z1197,z6])],[(0,[z0,z1,z3,z4,z1198,z6]),(0,[z104,z1,z3,z188,z4,z6]),(0,[z0,z1111,z2,z3,z4,z6]),(0,[z0,z1199,z2,z3,z4,z6]),(0,[z0,z110,z228,z3,z4,z6]),(0,[z0,z1,z89,z31,z4,z6]),(1,[z1,z2,z3,z4,z806]),(0,[z168,z0,z37,z3,z4,z6]),(0,[z1200,z0,z1,z3,z4,z6])]],
   [[(0,[z42,z1,z398,z3,z4,z6]),(0,[z52,z0,z1,z1201,z4,z6]),(0,[z52,z1,z3,z4,z6,z406]),(0,[z260,z2,z3,z133,z4,z6])],[(0,[z0,z1,z3,z4,z1202,z6]),(0,[z36,z0,z441,z3,z4,z6]),(0,[z1203,z0,z1,z3,z4,z6]),(0,[z419,z1,z3,z134,z4,z6]),(0,[z0,z1,z2,z1204,z4,z6]),(0,[z369,z1,z3,z4,z224,z6])],[(0,[z52,z0,z1205,z3,z4,z6]),(0,[z0,z2,z1206,z3,z4,z6]),(0,[z0,z26,z627,z3,z4,z6]),(0,[z49,z748,z1,z3,z4,z6]),(0,[z0,z190,z2,z3,z4,z6]),(0,[z0,z34,z3,z4,z167,z416]),(0,[z0,z1,z22,z843,z4,z6]),(0,[z0,z176,z2,z3,z298,z6]),(0,[z0,z1,z368,z3,z13,z14])],[(0,[z0,z232,z141,z3,z4,z6]),(0,[z66,z1,z118,z3,z4,z6]),(0,[z0,z2,z158,z3,z4,z6]),(0,[z0,z220,z1207,z3,z4,z6])],[(0,[z0,z183,z77,z3,z4,z6]),(0,[z0,z104,z83,z3,z4,z6]),(0,[z52,z0,z1,z3,z4,z363]),(0,[z66,z1,z3,z4,z119,z6]),(0,[z124,z1,z2,z3,z4,z363])],[(0,[z24,z42,z1,z3,z290,z6]),(0,[z96,z110,z2,z3,z4,z6]),(0,[z0,z1,z3,z1208,z4,z6]),(0,[z0,z1,z2,z4,z870,z6])],[(0,[z0,z1209,z1,z3,z4,z6]),(0,[z0,z1107,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z1210,z6]),(0,[z0,z1,z198,z3,z4,z6]),(0,[z66,z1,z3,z4,z6,z57]),(0,[z1211,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z1212,z4,z6])],[(0,[z595,z42,z1,z3,z4,z6]),(0,[z0,z1118,z110,z3,z4,z6]),(0,[z0,z823,z2,z3,z4,z6]),(0,[z0,z26,z3,z566,z4,z6]),(0,[z1,z2,z3,z1213,z4,z6]),(0,[z0,z1,z3,z4,z224,z1061])],[(0,[z0,z240,z137,z3,z4,z6]),(0,[z128,z137,z2,z3,z4,z6]),(0,[z96,z1,z3,z4,z290,z6]),(0,[z42,z0,z1,z3,z4,z363]),(0,[z0,z232,z143,z3,z4,z6]),(0,[z281,z0,z232,z3,z4,z6]),(0,[z0,z26,z505,z3,z4,z6]),(1,[z150,z0,z3,z623,z6])],[(0,[z170,z891,z2,z3,z4,z6]),(0,[z0,z232,z154,z3,z4,z6]),(0,[z1214,z0,z1,z3,z4,z6]),(0,[z0,z26,z1,z3,z155,z6]),(0,[z0,z37,z1,z3,z298,z6]),(0,[z332,z114,z0,z2,z3,z4]),(1,[z0,z1,z3,z1164,z6]),(0,[z66,z1,z3,z13,z4,z6])],[(0,[z0,z62,z3,z4,z384,z6]),(0,[z0,z1,z3,z1215,z4,z6]),(0,[z0,z1,z2,z3,z664,z14])],[(0,[z0,z26,z632,z3,z4,z6]),(0,[z0,z1,z3,z1216,z4,z6]),(0,[z1217,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1218,z6]),(0,[z0,z256,z3,z53,z4,z6])],[(0,[z0,z26,z64,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z806]),(0,[z0,z1,z1219,z3,z4,z6]),(0,[z0,z1,z3,z4,z67,z390])],[(0,[z0,z1,z3,z1220,z4,z6]),(0,[z1221,z0,z1,z3,z4,z6]),(1,[z741,z1,z3,z4,z6]),(0,[z0,z220,z3,z4,z6,z57]),(0,[z0,z1,z2,z3,z155,z119])],[(0,[z42,z0,z50,z3,z133,z6]),(0,[z1222,z0,z1,z3,z4,z6]),(0,[z117,z0,z220,z3,z4,z6]),(0,[z376,z1,z2,z3,z4,z363])],[(0,[z1,z2,z3,z51,z4,z6]),(0,[z52,z0,z1,z3,z4,z371]),(0,[z0,z1,z1223,z3,z4,z6]),(0,[z0,z26,z3,z638,z4,z6]),(0,[z0,z1,z2,z3,z4,z1224]),(0,[z0,z1225,z1,z3,z4,z6]),(0,[z0,z1,z3,z626,z67,z6])]],
   [[(0,[z52,z0,z3,z4,z384,z6]),(0,[z1226,z0,z1,z3,z4,z6]),(0,[z150,z0,z26,z3,z623,z6]),(0,[z66,z1227,z1,z3,z4,z6]),(0,[z0,z220,z3,z13,z4,z6]),(0,[z0,z1228,z1,z3,z4,z6])],[(0,[z419,z1,z3,z188,z4,z6]),(0,[z0,z823,z3,z4,z239,z6]),(0,[z0,z1,z2,z3,z4,z1229]),(0,[z0,z1,z2,z3,z1230,z6]),(0,[z66,z1,z3,z4,z224,z6]),(0,[z0,z1231,z2,z3,z4,z6])],[],[(0,[z0,z1232,z1,z3,z4,z6]),(0,[z42,z0,z1,z3,z4,z371]),(0,[z0,z1,z1233,z3,z4,z6]),(0,[z0,z1,z3,z1234,z4,z6])],[(0,[z42,z0,z3,z4,z384,z6]),(1,[z1,z978,z3,z4,z6]),(0,[z0,z26,z60,z3,z4,z6]),(0,[z1235,z66,z1,z3,z4,z6]),(0,[z0,z1227,z1,z3,z4,z6]),(0,[z99,z0,z3,z4,z6,z267])],[(0,[z0,z232,z3,z184,z4,z6]),(0,[z52,z1,z3,z4,z9,z6]),(0,[z0,z110,z3,z4,z67,z6]),(0,[z0,z26,z540,z3,z4,z6]),(0,[z0,z76,z2,z3,z4,z6]),(0,[z0,z433,z1,z3,z247,z4])],[(0,[z41,z77,z2,z3,z4,z6]),(0,[z0,z1,z89,z3,z4,z371]),(0,[z0,z62,z3,z4,z153,z6]),(0,[z0,z1,z2,z3,z1236,z4]),(0,[z0,z1237,z1,z3,z4,z6])],[(0,[z128,z137,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1238,z6]),(0,[z0,z1,z223,z3,z4,z558]),(0,[z0,z1239,z1,z3,z4,z6]),(0,[z45,z1,z82,z3,z4,z6])],[(0,[z42,z1,z694,z3,z4,z6]),(0,[z0,z1,z1240,z3,z4,z6]),(0,[z0,z37,z110,z3,z4,z6]),(0,[z1241,z0,z1,z3,z4,z6]),(0,[z0,z729,z3,z4,z105,z6]),(0,[z0,z26,z451,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1242]),(0,[z0,z34,z2,z3,z4,z167]),(0,[z66,z66,z1,z3,z4,z6]),(0,[z1,z3,z4,z67,z1157,z6]),(0,[z0,z220,z3,z4,z224,z6])],[(0,[z0,z1,z2,z3,z4,z1243]),(0,[z0,z1,z62,z3,z428,z6]),(0,[z1,z2,z3,z4,z1244,z6])],[(0,[z0,z240,z77,z3,z4,z6]),(0,[z0,z87,z2,z3,z4,z6]),(0,[z170,z137,z3,z4,z67,z6]),(0,[z147,z0,z232,z3,z4,z6]),(0,[z0,z1,z2,z895,z4,z6]),(0,[z0,z37,z3,z4,z6,z549])],[(0,[z0,z1245,z87,z3,z4,z6]),(0,[z0,z1,z380,z3,z4,z371]),(0,[z0,z1,z1246,z3,z4,z6]),(0,[z0,z1247,z62,z3,z4,z6]),(0,[z0,z1,z2,z3,z1248,z4])],[(0,[z52,z0,z3,z4,z153,z6]),(0,[z47,z0,z3,z4,z67,z6]),(0,[z0,z1249,z3,z4,z384,z6]),(0,[z0,z1,z3,z102,z445,z6]),(0,[z376,z1,z2,z127,z4,z6])],[(0,[z0,z1,z2,z3,z1250,z4]),(0,[z0,z1,z1251,z3,z4,z6]),(0,[z52,z0,z1,z3,z4,z390]),(0,[z516,z1,z2,z3,z4,z174]),(0,[z124,z1,z2,z3,z4,z390])],[(0,[z150,z0,z2,z3,z485,z6]),(0,[z0,z441,z3,z53,z4,z6]),(0,[z80,z359,z1,z188,z4,z6]),(0,[z0,z1,z1252,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z806])],[(0,[z150,z0,z232,z3,z4,z6]),(0,[z52,z117,z1,z3,z4,z239]),(0,[z36,z0,z26,z135,z3,z4]),(0,[z0,z3,z4,z6,z12,z416]),(1,[z0,z909,z3,z4,z6])]],
   [[(0,[z0,z1253,z1,z3,z4,z6]),(0,[z42,z0,z3,z4,z153,z6]),(0,[z0,z1,z3,z4,z105,z6]),(0,[z189,z0,z232,z3,z4,z6]),(0,[z0,z232,z3,z4,z6,z21]),(0,[z0,z1,z3,z4,z6,z1254]),(0,[z1255,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1256,z3,z4,z6]),(0,[z42,z0,z1,z3,z4,z390]),(0,[z0,z1,z2,z3,z871,z6]),(0,[z0,z1,z1257,z3,z4,z6]),(0,[z38,z0,z451,z3,z4,z6]),(0,[z0,z711,z3,z4,z67,z6]),(0,[z0,z1,z3,z155,z67,z6])],[(0,[z0,z1,z1258,z3,z4,z6]),(0,[z0,z1,z3,z1259,z4,z6]),(0,[z0,z26,z34,z3,z4,z167]),(0,[z0,z1,z3,z4,z1260,z6]),(0,[z0,z50,z2,z3,z935,z6]),(0,[z0,z1,z3,z155,z1261,z6])],[(0,[z117,z1,z2,z3,z4,z325]),(0,[z0,z3,z4,z153,z67,z6]),(0,[z0,z1262,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1263]),(0,[z52,z68,z1,z3,z134,z6]),(0,[z52,z0,z1,z135,z4,z119]),(0,[z52,z505,z1,z3,z4,z6]),(0,[z128,z0,z61,z3,z4,z6]),(0,[z0,z1,z1264,z3,z4,z6]),(0,[z0,z2,z3,z935,z10,z6]),(0,[z0,z1,z3,z300,z4,z499])],[(0,[z41,z42,z77,z3,z4,z6]),(0,[z38,z0,z1,z3,z4,z303]),(0,[z0,z714,z62,z3,z4,z6])],[(0,[z0,z1,z1265,z3,z4,z6]),(0,[z66,z68,z1,z3,z4,z6]),(0,[z0,z34,z2,z3,z4,z362]),(0,[z376,z1,z2,z4,z55,z6])],[(0,[z0,z1266,z2,z3,z4,z6]),(0,[z52,z304,z185,z3,z4,z6]),(0,[z0,z232,z22,z3,z4,z6]),(0,[z0,z1,z1267,z3,z4,z6]),(0,[z0,z1,z475,z3,z4,z430]),(0,[z376,z1,z2,z3,z4,z390])],[(0,[z42,z68,z1,z3,z134,z6]),(0,[z42,z0,z1,z135,z4,z119]),(0,[z369,z1,z3,z56,z4,z6]),(0,[z0,z2,z3,z1043,z4,z6])],[(0,[z1268,z0,z1,z3,z4,z6]),(0,[z0,z892,z2,z3,z4,z6]),(0,[z52,z0,z1,z3,z4,z1269]),(0,[z0,z1205,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z1270,z6]),(0,[z0,z26,z654,z3,z4,z6]),(0,[z0,z49,z50,z3,z133,z6]),(0,[z0,z1,z1271,z3,z4,z6])],[(0,[z1272,z0,z1,z3,z4,z6]),(0,[z0,z3,z4,z1127,z67,z6]),(0,[z0,z780,z2,z3,z4,z6])],[(0,[z234,z96,z1,z3,z4,z6]),(0,[z0,z232,z3,z4,z10,z6]),(0,[z0,z1273,z87,z3,z4,z6])],[(0,[z0,z26,z104,z3,z4,z6]),(0,[z46,z36,z0,z26,z3,z4]),(0,[z0,z1,z130,z3,z4,z6])],[(0,[z0,z83,z154,z3,z4,z6]),(0,[z0,z1,z1274,z3,z4,z6]),(0,[z0,z1,z62,z3,z275,z6]),(0,[z0,z26,z1,z3,z4,z238]),(0,[z0,z1,z1275,z3,z4,z6])],[(0,[z0,z1,z1276,z3,z4,z6]),(0,[z52,z0,z176,z3,z4,z6]),(0,[z117,z26,z1,z3,z4,z239]),(0,[z36,z0,z240,z3,z4,z6]),(0,[z0,z1277,z2,z3,z4,z6])],[(0,[z0,z1278,z2,z3,z4,z6]),(0,[z1,z185,z978,z3,z4,z6]),(0,[z171,z0,z1,z56,z4,z6]),(0,[z0,z1,z3,z843,z4,z6]),(0,[z66,z1,z3,z532,z4,z6]),(0,[z46,z0,z1,z62,z4,z100]),(0,[z0,z1,z3,z1279,z4,z6])]],
   [[(0,[z96,z26,z137,z3,z4,z6]),(1,[z758,z0,z3,z4,z6]),(0,[z66,z0,z220,z3,z4,z6])],[(0,[z0,z26,z1,z3,z247,z4]),(0,[z0,z26,z3,z610,z4,z6])],[(0,[z42,z0,z176,z3,z4,z6]),(0,[z150,z0,z62,z3,z10,z6]),(0,[z631,z0,z1,z56,z4,z6])],[(0,[z0,z1,z1280,z3,z4,z6]),(0,[z0,z1,z978,z3,z4,z6]),(0,[z26,z1,z3,z51,z4,z6]),(0,[z95,z1,z2,z3,z298,z6])],[(0,[z0,z1,z3,z4,z1281,z6]),(0,[z123,z37,z1,z3,z4,z174]),(0,[z0,z49,z1,z3,z210,z6]),(0,[z1282,z95,z1,z3,z4,z6])],[(0,[z1,z3,z852,z188,z4,z6]),(0,[z1283,z0,z1,z3,z4,z6]),(0,[z0,z1284,z1,z3,z4,z6])],[(0,[z52,z0,z1285,z3,z4,z6]),(0,[z24,z0,z1,z3,z249,z6]),(0,[z52,z0,z1,z3,z300,z4]),(0,[z0,z220,z3,z532,z4,z6])],[(0,[z0,z2,z1286,z3,z4,z6]),(0,[z0,z2,z3,z1287,z4,z6]),(0,[z0,z1288,z1,z3,z4,z6]),(0,[z0,z83,z2,z3,z300,z4]),(0,[z0,z61,z2,z164,z4,z6])],[(0,[z41,z891,z2,z3,z4,z6]),(0,[z1289,z1,z2,z3,z4,z6]),(0,[z66,z1,z3,z56,z4,z6]),(0,[z0,z1,z3,z4,z1290,z6]),(0,[z0,z152,z3,z4,z67,z6]),(0,[z0,z62,z1144,z3,z4,z6]),(0,[z0,z1,z1291,z3,z4,z6])],[(0,[z201,z0,z104,z3,z4,z6]),(0,[z0,z3,z4,z384,z6,z770]),(0,[z117,z66,z1,z3,z4,z6]),(0,[z0,z20,z61,z3,z4,z6]),(0,[z1292,z0,z1,z3,z4,z6]),(0,[z36,z0,z2,z3,z4,z1023]),(0,[z0,z1,z2,z3,z1293,z6])],[(0,[z42,z0,z87,z3,z4,z6]),(0,[z0,z232,z3,z53,z4,z6]),(0,[z52,z232,z185,z3,z4,z6]),(0,[z52,z0,z220,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1294]),(0,[z123,z473,z2,z3,z4,z174]),(0,[z0,z26,z3,z4,z6,z267]),(0,[z0,z2,z3,z4,z935,z6]),(0,[z0,z1,z2,z3,z155,z6])],[(0,[z0,z232,z3,z4,z6,z14]),(0,[z52,z0,z271,z3,z4,z6]),(0,[z52,z0,z1,z31,z4,z6]),(0,[z0,z1,z3,z4,z8,z57]),(0,[z0,z1,z2,z3,z1295,z6]),(0,[z0,z1296,z473,z3,z4,z6]),(0,[z117,z1,z2,z3,z4,z806]),(0,[z608,z0,z220,z3,z4,z6]),(0,[z46,z0,z1,z2,z155,z100])],[(0,[z0,z641,z26,z3,z4,z6]),(0,[z0,z3,z480,z354,z4,z6]),(0,[z0,z1,z1297,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1298])],[(0,[z0,z1,z1299,z3,z4,z6]),(0,[z42,z1,z3,z4,z476,z6]),(0,[z0,z1,z1300,z3,z4,z6]),(0,[z0,z240,z3,z133,z4,z6]),(0,[z0,z1,z3,z4,z6,z1301])],[(0,[z126,z41,z1,z3,z4,z6]),(0,[z473,z2,z3,z188,z4,z6]),(0,[z0,z1302,z1,z3,z4,z6]),(0,[z0,z1296,z1,z3,z4,z6]),(0,[z0,z1,z3,z1303,z4,z6]),(0,[z0,z1,z3,z4,z623,z6]),(0,[z114,z0,z34,z2,z3,z4]),(0,[z38,z0,z152,z3,z4,z57]),(0,[z0,z1,z437,z3,z4,z363])],[(0,[z42,z0,z271,z3,z4,z6]),(0,[z42,z0,z1,z31,z4,z6]),(0,[z0,z1,z3,z4,z6,z1304]),(0,[z741,z0,z1,z3,z4,z6]),(0,[z168,z0,z2,z3,z4,z6]),(0,[z0,z50,z2,z3,z610,z6]),(0,[z0,z220,z3,z56,z4,z6])]],
   [[(0,[z234,z0,z1,z3,z4,z6]),(0,[z0,z87,z2,z97,z4,z6]),(0,[z0,z37,z1,z3,z13,z14]),(0,[z0,z1,z1305,z3,z4,z6]),(0,[z0,z1,z62,z3,z67,z6]),(0,[z0,z1,z3,z443,z4,z6])],[(0,[z255,z0,z1,z435,z4,z6]),(0,[z0,z1,z62,z3,z4,z25]),(0,[z0,z26,z76,z3,z4,z6]),(0,[z1,z3,z1155,z439,z4,z6]),(0,[z0,z205,z451,z3,z4,z6]),(0,[z124,z1,z437,z3,z4,z6])],[(0,[z0,z2,z3,z172,z4,z6]),(0,[z137,z891,z2,z3,z4,z6]),(0,[z681,z42,z1,z3,z4,z6]),(0,[z42,z1,z3,z481,z4,z6]),(0,[z0,z2,z3,z1306,z4,z6]),(0,[z0,z1,z3,z4,z1307,z6])],[(0,[z199,z0,z1,z3,z290,z6]),(0,[z42,z535,z1,z3,z4,z6]),(0,[z0,z1,z2,z31,z4,z371]),(0,[z0,z26,z50,z3,z133,z6]),(0,[z0,z1308,z2,z3,z4,z6]),(0,[z0,z1,z82,z3,z155,z6])],[(0,[z0,z744,z232,z3,z4,z6]),(0,[z332,z52,z0,z53,z4,z6])],[(0,[z265,z0,z26,z3,z4,z6]),(0,[z0,z26,z232,z3,z4,z6]),(0,[z68,z0,z1,z3,z290,z6]),(0,[z0,z3,z4,z1309,z290,z6]),(0,[z0,z232,z3,z4,z6,z279]),(0,[z81,z96,z1,z3,z4,z6]),(1,[z1,z2,z3,z871,z6]),(0,[z0,z26,z3,z4,z6,z628]),(0,[z535,z2,z3,z53,z4,z6])],[(0,[z1310,z0,z1,z3,z4,z6]),(0,[z0,z26,z218,z3,z4,z6]),(0,[z0,z26,z642,z3,z4,z6]),(0,[z66,z34,z1,z3,z4,z6]),(0,[z0,z1,z673,z3,z67,z6]),(0,[z126,z0,z714,z3,z4,z6])],[(0,[z0,z1,z1311,z3,z4,z6]),(0,[z0,z1112,z2,z3,z4,z6]),(0,[z52,z0,z711,z3,z4,z6]),(0,[z0,z1,z380,z31,z4,z6]),(0,[z1312,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1313,z6]),(0,[z0,z1314,z1,z3,z4,z6]),(0,[z0,z1,z214,z3,z4,z238]),(0,[z46,z0,z1,z374,z4,z100]),(0,[z1315,z0,z1,z3,z4,z6])],[(1,[z24,z1,z3,z290,z6]),(0,[z0,z1,z3,z1316,z4,z6]),(0,[z36,z0,z26,z3,z4,z405]),(0,[z88,z0,z2,z53,z4,z6]),(0,[z66,z0,z3,z4,z151,z6]),(0,[z1,z2,z3,z1317,z4,z6]),(0,[z38,z0,z3,z4,z12,z57]),(0,[z189,z0,z1,z2,z55,z363]),(0,[z0,z1,z2,z3,z13,z14])],[(0,[z123,z2,z3,z4,z384,z174]),(0,[z45,z37,z1,z3,z4,z6]),(0,[z150,z0,z187,z3,z10,z6]),(0,[z0,z1318,z220,z3,z4,z6])],[(0,[z0,z61,z2,z530,z4,z6]),(0,[z52,z0,z1,z3,z4,z1319]),(0,[z0,z26,z61,z53,z4,z6]),(0,[z0,z17,z2,z3,z4,z6]),(0,[z0,z152,z62,z3,z4,z6])],[(0,[z0,z1,z3,z1320,z4,z6]),(0,[z0,z26,z3,z696,z4,z6]),(0,[z0,z1,z2,z3,z1321,z6]),(0,[z1322,z1,z2,z3,z4,z6]),(0,[z0,z1,z62,z3,z43,z6]),(0,[z171,z0,z1,z583,z4,z6]),(0,[z66,z1,z127,z3,z4,z6]),(0,[z376,z1,z437,z3,z4,z6]),(0,[z0,z1323,z2,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z1324]),(0,[z0,z1,z1325,z3,z4,z6]),(0,[z66,z1,z3,z4,z6,z174]),(0,[z0,z1,z23,z4,z6,z226]),(0,[z168,z0,z2,z3,z181,z4])],[(0,[z0,z1,z2,z3,z4,z1031]),(0,[z0,z1,z1326,z3,z4,z6]),(0,[z0,z220,z118,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z203])],[(0,[z189,z42,z0,z1,z55,z6]),(0,[z0,z1,z3,z4,z6,z1327]),(0,[z38,z0,z232,z3,z4,z6]),(0,[z0,z1,z3,z1328,z4,z6]),(0,[z0,z1329,z1,z3,z4,z6]),(0,[z1330,z1,z2,z3,z4,z6]),(0,[z0,z220,z3,z4,z119,z6]),(0,[z0,z1,z1331,z3,z4,z6])],[(0,[z1282,z0,z1,z3,z4,z6]),(0,[z211,z0,z2,z3,z10,z6]),(0,[z0,z1,z3,z4,z1164,z6]),(0,[z66,z1,z3,z4,z514,z6])]],
   [[(0,[z170,z137,z154,z3,z4,z6]),(0,[z42,z469,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z1332,z4]),(0,[z0,z1,z1333,z3,z4,z6]),(0,[z0,z1,z1334,z3,z4,z6]),(0,[z0,z1,z739,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1335,z6]),(0,[z0,z1,z3,z4,z1336,z6]),(0,[z1337,z0,z1,z3,z4,z6]),(0,[z45,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z210,z67,z6]),(0,[z0,z1,z1338,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1339,z6]),(0,[z66,z96,z1,z3,z4,z6]),(0,[z608,z0,z26,z3,z4,z6]),(0,[z0,z220,z127,z3,z4,z6]),(0,[z1,z3,z4,z897,z306,z6])],[(0,[z80,z1,z188,z4,z67,z6]),(0,[z0,z61,z3,z4,z623,z6]),(0,[z0,z1,z1340,z3,z4,z6]),(0,[z0,z1,z343,z323,z4,z6])],[(0,[z0,z1,z3,z4,z1341,z6]),(0,[z66,z1,z111,z3,z4,z6]),(0,[z0,z2,z1342,z3,z4,z6]),(0,[z0,z1,z2,z3,z870,z6])],[(0,[z0,z1,z2,z3,z4,z1343]),(0,[z0,z1,z62,z97,z4,z6]),(0,[z68,z1,z3,z134,z105,z6]),(0,[z36,z0,z1,z2,z3,z155])],[(0,[z0,z1,z3,z4,z1344,z6]),(0,[z171,z0,z1,z169,z4,z6]),(0,[z0,z1,z3,z4,z1345,z6]),(0,[z0,z1,z3,z4,z6,z1346]),(0,[z0,z1,z3,z1164,z67,z6]),(0,[z0,z220,z3,z4,z514,z6])],[(0,[z41,z641,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z167,z422]),(0,[z0,z1,z3,z70,z4,z6]),(0,[z1,z2,z3,z4,z1347,z6]),(0,[z0,z1,z1348,z3,z4,z6]),(0,[z0,z1,z223,z3,z4,z224]),(0,[z0,z1,z437,z3,z4,z390]),(0,[z0,z17,z2,z3,z181,z4])],[(0,[z0,z1,z695,z3,z67,z6]),(0,[z394,z1,z2,z188,z4,z6]),(0,[z332,z0,z480,z53,z4,z6]),(0,[z0,z1,z4,z67,z6,z846]),(0,[z0,z1,z1349,z3,z4,z6])],[(0,[z0,z1,z78,z3,z4,z6]),(0,[z193,z0,z3,z53,z4,z6]),(0,[z126,z234,z1,z3,z4,z6]),(0,[z71,z0,z232,z3,z4,z6]),(0,[z0,z1350,z2,z3,z4,z6]),(0,[z126,z0,z780,z3,z4,z6]),(0,[z46,z45,z1,z2,z4,z100])],[(0,[z81,z0,z1,z3,z4,z6]),(0,[z0,z26,z524,z3,z4,z6]),(0,[z526,z0,z1,z3,z67,z6]),(0,[z0,z37,z1,z3,z247,z4]),(0,[z234,z1,z165,z3,z4,z6]),(0,[z0,z1,z3,z1351,z4,z6])],[(0,[z68,z1,z2,z3,z360,z6]),(0,[z171,z0,z1,z602,z4,z6]),(0,[z0,z220,z111,z3,z4,z6])],[(0,[z24,z1,z3,z4,z290,z6]),(0,[z42,z1,z3,z4,z9,z6]),(0,[z579,z42,z1,z3,z4,z6]),(0,[z0,z1352,z1,z3,z4,z6]),(0,[z0,z1,z1353,z3,z4,z6]),(0,[z36,z0,z2,z3,z4,z21]),(0,[z0,z62,z158,z3,z4,z6])],[(0,[z52,z1,z3,z439,z4,z6]),(0,[z0,z1,z2,z3,z4,z1354])],[(0,[z0,z1,z1355,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z238]),(0,[z66,z1,z3,z4,z167,z6]),(0,[z1,z3,z1356,z4,z67,z6])],[(0,[z0,z1357,z1,z3,z4,z6]),(0,[z52,z0,z907,z3,z4,z6]),(0,[z1,z185,z3,z4,z105,z6]),(0,[z0,z1,z3,z4,z1358,z6]),(0,[z117,z1,z2,z3,z4,z239]),(0,[z36,z0,z20,z3,z4,z6]),(0,[z0,z1,z3,z1359,z4,z6])]],
   [[(0,[z41,z280,z77,z3,z4,z6]),(0,[z0,z137,z3,z4,z623,z6]),(0,[z0,z2,z3,z1360,z4,z6]),(0,[z0,z328,z3,z4,z10,z6]),(0,[z0,z451,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z155,z100]),(0,[z0,z1,z3,z4,z936,z6])],[(0,[z0,z1361,z1,z3,z4,z6]),(0,[z42,z1,z3,z439,z4,z6]),(0,[z0,z2,z3,z4,z1309,z6]),(0,[z0,z232,z3,z134,z4,z6]),(0,[z0,z1,z1362,z3,z4,z6]),(0,[z0,z1363,z2,z3,z4,z6]),(0,[z0,z1364,z1,z3,z4,z6]),(0,[z0,z1,z62,z3,z102,z6]),(0,[z281,z66,z1,z3,z4,z6]),(0,[z175,z0,z1,z602,z4,z6]),(0,[z189,z0,z1,z2,z55,z390])],[(0,[z0,z104,z1,z3,z4,z6]),(0,[z419,z137,z1,z3,z4,z6]),(0,[z0,z232,z3,z1365,z4,z6]),(0,[z52,z0,z158,z3,z4,z6]),(0,[z0,z1,z2,z3,z247,z4]),(0,[z1366,z535,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z1367,z6])],[(0,[z0,z2,z3,z1368,z4,z6]),(0,[z0,z1,z3,z4,z6,z1369]),(0,[z1312,z168,z0,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z1370])],[(0,[z0,z1371,z1,z3,z4,z6]),(0,[z0,z3,z4,z357,z153,z6]),(0,[z0,z26,z61,z3,z4,z6]),(0,[z274,z0,z26,z3,z4,z6]),(0,[z0,z253,z2,z3,z4,z6]),(0,[z0,z1,z786,z3,z4,z6])],[(0,[z52,z66,z1,z3,z4,z6]),(0,[z0,z26,z3,z4,z6,z12]),(0,[z1372,z37,z1,z3,z4,z6]),(0,[z0,z220,z3,z4,z167,z6]),(0,[z171,z0,z1,z843,z4,z6])],[(0,[z42,z0,z158,z3,z4,z6]),(0,[z52,z0,z152,z3,z4,z6]),(0,[z0,z1,z2,z3,z1373,z6]),(0,[z334,z0,z26,z3,z4,z6]),(0,[z0,z26,z1,z146,z3,z181]),(0,[z1374,z1,z2,z3,z4,z6]),(0,[z0,z1,z1375,z3,z4,z6])],[(0,[z66,z0,z1,z3,z4,z6]),(0,[z0,z2,z3,z1376,z4,z6]),(0,[z0,z1,z3,z4,z6,z1377]),(0,[z0,z1,z2,z3,z4,z1378]),(0,[z0,z1,z62,z3,z693,z6]),(0,[z46,z0,z1,z82,z4,z100]),(0,[z0,z1,z2,z4,z6,z762])],[(0,[z0,z50,z2,z3,z385,z6]),(0,[z0,z1,z3,z1379,z4,z6]),(0,[z0,z1380,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1381,z6]),(0,[z1,z62,z3,z51,z4,z6]),(0,[z1382,z0,z1,z3,z4,z6])],[(0,[z36,z0,z2,z3,z4,z230]),(0,[z42,z66,z1,z3,z4,z6]),(0,[z927,z26,z1,z3,z4,z6]),(0,[z260,z2,z3,z4,z167,z6]),(0,[z0,z1383,z17,z3,z4,z6])],[(0,[z42,z1,z3,z4,z6,z528]),(0,[z42,z0,z152,z3,z4,z6])],[(0,[z41,z2,z3,z495,z4,z6]),(0,[z0,z1,z1384,z3,z4,z6]),(0,[z123,z173,z1,z3,z4,z174]),(0,[z0,z26,z3,z33,z4,z6]),(0,[z0,z26,z678,z3,z4,z6]),(0,[z0,z1,z2,z135,z420,z4]),(0,[z0,z2,z3,z1385,z4,z6])],[(0,[z41,z1,z2,z31,z4,z6]),(0,[z52,z536,z1,z3,z4,z6]),(0,[z24,z87,z2,z3,z48,z6]),(0,[z526,z0,z26,z3,z4,z6]),(0,[z0,z26,z39,z3,z4,z6]),(0,[z1386,z1,z3,z439,z4,z6]),(0,[z0,z1,z2,z843,z4,z6])],[(0,[z0,z1,z1387,z3,z4,z6]),(0,[z52,z1,z3,z538,z4,z6]),(0,[z0,z1,z1388,z3,z4,z6]),(0,[z1372,z1,z2,z3,z4,z6]),(0,[z0,z253,z82,z3,z4,z6])],[(0,[z0,z232,z3,z181,z4,z6]),(0,[z0,z1,z3,z4,z6,z1389]),(0,[z0,z50,z1,z3,z445,z6]),(0,[z0,z1,z3,z247,z4,z67]),(0,[z1390,z0,z1,z3,z4,z6]),(0,[z0,z909,z3,z4,z306,z6]),(0,[z0,z176,z2,z3,z155,z6])],[(0,[z96,z0,z232,z3,z4,z6]),(0,[z171,z0,z232,z3,z4,z6]),(0,[z0,z1391,z2,z3,z4,z6]),(0,[z0,z26,z87,z3,z4,z6]),(0,[z49,z1,z3,z4,z514,z6]),(0,[z0,z1,z3,z4,z1392,z6])]],
   [[(0,[z41,z2,z3,z501,z4,z6]),(0,[z0,z1393,z1,z3,z4,z6]),(0,[z0,z1,z2,z1394,z4,z6]),(0,[z0,z50,z2,z3,z519,z6]),(0,[z0,z907,z3,z4,z67,z6]),(0,[z0,z952,z1,z3,z4,z6]),(0,[z0,z1,z1395,z3,z4,z6])],[(0,[z0,z232,z3,z188,z4,z6]),(0,[z0,z1,z22,z399,z4,z6]),(0,[z66,z1,z146,z3,z4,z6]),(0,[z0,z1,z111,z4,z418,z6])],[(0,[z0,z1,z62,z3,z4,z6]),(0,[z683,z0,z1,z2,z55,z6]),(0,[z0,z1,z3,z4,z67,z25]),(0,[z0,z3,z4,z167,z6,z731]),(0,[z0,z1383,z1,z3,z4,z6]),(0,[z0,z22,z23,z354,z4,z6]),(0,[z0,z451,z62,z3,z4,z6]),(0,[z1396,z1,z2,z3,z4,z6]),(0,[z66,z1,z3,z212,z4,z6]),(0,[z0,z1,z3,z13,z67,z14]),(0,[z0,z1,z2,z3,z186,z14])],[(0,[z0,z1,z3,z4,z1397,z6]),(0,[z758,z42,z0,z3,z4,z6]),(0,[z129,z0,z232,z3,z4,z6]),(0,[z0,z1,z3,z4,z224,z279]),(0,[z0,z1,z1398,z3,z4,z6]),(0,[z150,z0,z1,z3,z623,z6]),(0,[z0,z26,z3,z133,z4,z238])],[(0,[z139,z0,z1,z3,z4,z6]),(0,[z1399,z0,z1,z2,z3,z6]),(0,[z234,z0,z1,z3,z162,z6]),(0,[z38,z0,z1,z3,z4,z392]),(0,[z0,z1,z1400,z3,z4,z6]),(0,[z0,z1,z3,z4,z1401,z6]),(0,[z0,z1,z2,z870,z55,z6])],[(0,[z52,z124,z1,z3,z4,z6]),(0,[z147,z68,z1,z3,z134,z6]),(0,[z1402,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1403,z6]),(0,[z0,z37,z1,z3,z155,z6]),(0,[z0,z1404,z1,z3,z4,z6]),(0,[z1405,z1,z2,z3,z4,z6]),(0,[z0,z1,z145,z3,z4,z6]),(0,[z66,z2,z3,z4,z151,z6]),(0,[z1406,z1,z2,z3,z4,z6]),(0,[z168,z99,z0,z3,z4,z6]),(0,[z1407,z0,z1,z3,z4,z6])],[(0,[z137,z1,z2,z31,z4,z6]),(0,[z0,z1,z1408,z3,z4,z6]),(0,[z189,z124,z1,z2,z55,z6]),(0,[z1409,z0,z1,z3,z4,z6])],[(0,[z0,z26,z207,z3,z4,z6]),(0,[z0,z328,z83,z3,z4,z6]),(0,[z741,z1,z3,z4,z67,z6]),(0,[z0,z240,z550,z3,z4,z6])],[(0,[z0,z1,z3,z1410,z4,z6]),(0,[z0,z2,z3,z4,z1411,z6]),(0,[z0,z1412,z2,z3,z4,z6]),(0,[z189,z0,z26,z1,z55,z6]),(0,[z150,z66,z1,z3,z4,z6])],[(0,[z42,z124,z1,z3,z4,z6]),(0,[z80,z1,z62,z188,z4,z6]),(0,[z0,z3,z765,z53,z4,z6]),(0,[z0,z2,z3,z4,z151,z6]),(0,[z0,z1,z3,z4,z1413,z6]),(0,[z0,z220,z3,z212,z4,z6])],[(0,[z0,z304,z3,z4,z249,z6]),(0,[z0,z1,z1414,z3,z4,z6]),(0,[z36,z0,z3,z4,z623,z6]),(1,[z220,z3,z4,z514,z6])],[(0,[z0,z1,z3,z295,z4,z6]),(0,[z0,z1415,z2,z3,z4,z6]),(0,[z38,z0,z1,z3,z4,z405]),(0,[z30,z0,z1,z414,z4,z6]),(0,[z0,z1416,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1417]),(0,[z0,z2,z322,z3,z10,z6]),(0,[z0,z814,z2,z3,z4,z6]),(0,[z0,z1418,z1,z3,z4,z6])],[(0,[z52,z1,z978,z3,z4,z6]),(0,[z0,z473,z2,z3,z4,z14]),(0,[z1101,z45,z1,z3,z4,z6])],[(0,[z42,z0,z1,z3,z300,z4]),(0,[z0,z61,z256,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1419])],[(0,[z0,z1,z3,z1420,z4,z6]),(0,[z37,z1,z3,z51,z4,z6]),(0,[z0,z1421,z1,z3,z4,z6])],[(0,[z0,z1,z1422,z3,z4,z6]),(0,[z114,z42,z0,z1,z3,z4]),(0,[z52,z260,z1,z3,z4,z6]),(0,[z36,z0,z2,z3,z4,z277]),(0,[z66,z1,z62,z3,z67,z6]),(0,[z66,z1,z601,z3,z4,z6])]],
   [[(0,[z42,z1,z978,z3,z4,z6]),(0,[z24,z0,z232,z3,z4,z6]),(0,[z52,z114,z0,z1,z3,z4]),(0,[z0,z2,z3,z1423,z4,z6]),(0,[z0,z3,z4,z1424,z105,z6]),(0,[z0,z26,z1,z3,z4,z363]),(0,[z180,z0,z1,z3,z4,z646])],[(0,[z42,z0,z220,z3,z4,z6]),(0,[z24,z1,z62,z3,z48,z6]),(0,[z0,z1425,z1,z3,z4,z6])],[(0,[z42,z314,z1,z3,z4,z6]),(0,[z52,z1,z555,z3,z4,z6]),(0,[z0,z1,z3,z1426,z4,z6]),(0,[z24,z81,z1,z3,z4,z6])],[(0,[z52,z0,z1,z3,z4,z25]),(0,[z124,z26,z1,z3,z4,z6]),(0,[z114,z0,z26,z2,z3,z4]),(0,[z1427,z1,z2,z3,z4,z6])],[(0,[z24,z26,z137,z3,z4,z6]),(0,[z0,z1,z1428,z3,z4,z6]),(0,[z26,z327,z137,z3,z4,z6]),(0,[z234,z0,z1,z3,z290,z6]),(0,[z0,z1,z1429,z3,z4,z6]),(0,[z24,z1,z3,z357,z48,z6]),(0,[z117,z1,z3,z4,z239,z194]),(0,[z0,z220,z3,z4,z623,z6]),(0,[z0,z37,z451,z3,z4,z6]),(0,[z242,z0,z1,z4,z662,z6])],[(0,[z80,z42,z1,z188,z4,z6]),(0,[z0,z232,z83,z3,z4,z6]),(0,[z0,z3,z985,z172,z4,z6]),(0,[z0,z1,z3,z4,z1430,z6]),(0,[z0,z1431,z1,z3,z4,z6]),(0,[z535,z1,z62,z3,z4,z6]),(0,[z45,z176,z2,z3,z4,z6])],[(0,[z47,z0,z26,z3,z4,z6]),(0,[z0,z26,z3,z210,z4,z6]),(0,[z0,z220,z62,z3,z67,z6]),(0,[z0,z220,z601,z3,z4,z6])],[(0,[z0,z2,z3,z133,z680,z6]),(0,[z42,z0,z1,z3,z4,z25]),(0,[z0,z1,z3,z4,z1432,z6]),(0,[z1433,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1003]),(0,[z0,z1,z1434,z3,z4,z6]),(0,[z0,z3,z133,z4,z854,z6])],[(0,[z52,z376,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z1435,z4]),(0,[z1436,z1,z2,z3,z4,z6]),(0,[z1437,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1438,z6]),(0,[z68,z0,z1,z3,z249,z6]),(0,[z0,z1439,z1,z3,z4,z6]),(0,[z0,z1,z187,z3,z4,z6]),(0,[z1330,z37,z1,z3,z4,z6]),(0,[z189,z376,z1,z2,z55,z6])],[(0,[z0,z1440,z1,z3,z4,z6]),(0,[z0,z1,z89,z3,z4,z25]),(0,[z128,z0,z3,z53,z4,z6]),(0,[z1441,z0,z1,z2,z3,z4])],[(0,[z0,z1,z3,z4,z1442,z6]),(0,[z0,z1,z1443,z3,z4,z6]),(0,[z0,z26,z1,z3,z4,z371]),(0,[z0,z1,z1444,z3,z4,z6]),(0,[z0,z1,z3,z4,z1445,z6]),(0,[z0,z1,z22,z379,z4,z6]),(0,[z147,z0,z220,z3,z4,z6]),(0,[z220,z3,z4,z514,z67,z6])],[(0,[z170,z0,z328,z3,z4,z6]),(0,[z42,z376,z1,z3,z4,z6]),(0,[z0,z26,z3,z4,z384,z6]),(0,[z65,z0,z1,z72,z4,z6]),(0,[z189,z0,z37,z1,z55,z6])],[(0,[z24,z42,z1,z3,z48,z6]),(0,[z0,z1,z228,z3,z4,z6]),(0,[z0,z232,z3,z4,z249,z6]),(0,[z0,z1446,z2,z3,z4,z6]),(0,[z376,z26,z1,z3,z4,z6]),(0,[z0,z1447,z190,z3,z4,z6])],[(0,[z0,z1448,z1,z3,z4,z6]),(0,[z0,z1,z196,z3,z4,z6]),(0,[z0,z37,z34,z3,z4,z167])],[(0,[z42,z1,z560,z3,z4,z6]),(0,[z0,z232,z3,z102,z4,z6]),(0,[z80,z1,z2,z964,z4,z6]),(0,[z0,z1,z380,z3,z4,z25]),(0,[z0,z62,z3,z4,z151,z6]),(0,[z0,z1449,z2,z3,z4,z6])]],
   [[(0,[z150,z0,z220,z3,z4,z6]),(0,[z0,z183,z3,z4,z167,z6]),(0,[z1450,z0,z1,z3,z4,z6]),(0,[z1451,z124,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1452,z6]),(0,[z0,z1,z3,z4,z1453,z6]),(0,[z0,z1454,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1455])],[(0,[z170,z0,z232,z3,z4,z6]),(0,[z0,z825,z271,z3,z4,z6])],[],[(0,[z0,z1,z1456,z3,z4,z6]),(0,[z42,z292,z1,z3,z4,z6]),(1,[z0,z845,z3,z4,z6]),(0,[z0,z1447,z1,z3,z4,z6]),(0,[z0,z2,z3,z1457,z4,z6]),(0,[z0,z34,z2,z3,z4,z1023]),(0,[z95,z1,z62,z3,z4,z6]),(0,[z975,z0,z1,z3,z4,z6])],[(0,[z52,z0,z3,z4,z151,z6]),(0,[z0,z1,z3,z1458,z4,z6]),(0,[z68,z1,z3,z134,z67,z6]),(0,[z123,z66,z1,z3,z4,z6]),(0,[z0,z26,z510,z3,z4,z6]),(0,[z260,z26,z1,z3,z4,z6]),(0,[z1459,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z13,z443,z14])],[(0,[z170,z26,z137,z3,z4,z6]),(0,[z126,z137,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z719,z6]),(0,[z0,z220,z3,z4,z6,z174]),(0,[z66,z1,z3,z4,z6,z100])],[(0,[z1460,z0,z1,z3,z4,z6]),(0,[z52,z0,z1,z97,z4,z6]),(0,[z0,z1,z1461,z3,z4,z6]),(0,[z0,z1462,z1,z3,z4,z6]),(0,[z1463,z1,z2,z3,z4,z6]),(0,[z66,z1,z18,z3,z4,z6]),(0,[z1001,z1,z2,z3,z4,z6])],[(0,[z24,z234,z1,z3,z4,z6]),(0,[z147,z0,z711,z3,z4,z6]),(0,[z0,z26,z3,z4,z153,z6])],[(0,[z681,z77,z2,z3,z4,z6]),(0,[z0,z26,z154,z3,z4,z6]),(0,[z42,z0,z3,z4,z151,z6]),(0,[z377,z0,z232,z3,z4,z6]),(0,[z117,z1,z570,z3,z4,z239]),(0,[z0,z26,z1,z3,z4,z390]),(0,[z0,z37,z1,z3,z4,z238])],[(0,[z0,z1,z1464,z3,z4,z6]),(0,[z0,z884,z2,z3,z4,z6]),(0,[z0,z1465,z1,z3,z4,z6]),(0,[z0,z1,z1466,z3,z4,z6]),(0,[z47,z0,z37,z3,z4,z6]),(0,[z117,z37,z1,z3,z4,z239]),(0,[z0,z1,z3,z4,z1467,z6]),(0,[z0,z1,z1468,z3,z4,z6]),(0,[z129,z66,z1,z3,z67,z6]),(0,[z0,z2,z1469,z3,z4,z6]),(0,[z0,z1,z2,z3,z910,z6]),(0,[z1470,z1,z2,z3,z4,z6])],[(0,[z0,z62,z3,z172,z4,z6]),(0,[z0,z1,z2,z3,z4,z1471]),(0,[z0,z1,z62,z3,z206,z6])],[(0,[z891,z77,z2,z3,z4,z6]),(0,[z52,z1,z3,z4,z514,z6]),(0,[z1472,z0,z1,z3,z4,z6]),(0,[z332,z0,z433,z53,z4,z6]),(0,[z129,z1,z3,z514,z67,z6]),(0,[z1473,z0,z1,z3,z4,z6])],[(0,[z0,z1,z2,z1172,z4,z6]),(0,[z0,z1,z2,z1474,z4,z6]),(0,[z68,z1,z482,z3,z134,z6]),(0,[z0,z2,z845,z3,z4,z6]),(0,[z1475,z0,z1,z3,z4,z6]),(0,[z1476,z1,z2,z3,z4,z6]),(0,[z0,z220,z3,z4,z6,z100]),(0,[z1477,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z393,z212,z6]),(0,[z0,z1478,z1,z3,z4,z6])],[(0,[z0,z280,z83,z3,z4,z6]),(0,[z193,z0,z511,z3,z4,z6]),(0,[z0,z1479,z232,z3,z4,z6]),(0,[z0,z1,z89,z97,z4,z6]),(0,[z1480,z0,z1,z3,z4,z6]),(0,[z0,z1481,z1,z3,z4,z6]),(0,[z0,z1,z3,z1482,z4,z6]),(0,[z0,z83,z241,z3,z4,z6]),(0,[z894,z1,z2,z3,z4,z6]),(0,[z332,z0,z2,z247,z53,z4]),(0,[z0,z2,z18,z4,z6,z628]),(0,[z0,z220,z18,z3,z4,z6])],[(0,[z47,z42,z0,z3,z4,z6]),(0,[z0,z1483,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z1484,z6]),(0,[z0,z20,z3,z53,z4,z6]),(0,[z0,z909,z2,z3,z4,z6]),(0,[z95,z1,z2,z3,z155,z6])]],
   [[(0,[z0,z232,z1,z3,z4,z6]),(0,[z42,z1,z3,z4,z514,z6]),(0,[z0,z26,z1,z135,z4,z119])],[(0,[z170,z2,z3,z4,z598,z6]),(0,[z52,z0,z3,z172,z4,z6]),(0,[z1485,z0,z1,z3,z4,z6]),(0,[z1374,z37,z1,z3,z4,z6]),(0,[z369,z1,z62,z3,z4,z6]),(0,[z1,z62,z3,z1317,z4,z6]),(0,[z0,z1486,z1,z3,z4,z6])],[(0,[z0,z1487,z2,z3,z4,z6])],[(0,[z0,z1,z3,z4,z67,z6]),(0,[z42,z96,z1,z3,z4,z6]),(0,[z150,z42,z0,z3,z10,z6]),(0,[z0,z1,z380,z97,z4,z6]),(0,[z0,z1,z3,z4,z1488,z6]),(0,[z0,z1,z3,z1489,z4,z6]),(0,[z260,z1,z3,z4,z192,z6]),(0,[z0,z1490,z2,z3,z4,z6]),(0,[z0,z328,z305,z3,z4,z6])],[(0,[z0,z1,z1491,z3,z4,z6]),(0,[z0,z26,z3,z4,z182,z6]),(0,[z0,z1,z1492,z3,z4,z6]),(0,[z36,z0,z256,z3,z4,z6]),(0,[z0,z2,z3,z300,z4,z10]),(0,[z0,z1,z3,z4,z1261,z6]),(0,[z866,z1,z3,z4,z67,z6])],[(0,[z42,z0,z3,z172,z4,z6]),(0,[z0,z232,z223,z3,z4,z6]),(0,[z0,z1,z2,z964,z4,z6]),(0,[z24,z47,z2,z3,z4,z6]),(0,[z126,z1,z3,z4,z48,z6]),(0,[z358,z1,z2,z3,z4,z239]),(0,[z396,z0,z26,z3,z4,z6]),(0,[z0,z1,z3,z4,z1061,z57])],[(0,[z0,z1,z62,z3,z162,z6]),(0,[z52,z259,z1,z3,z4,z6]),(0,[z621,z1,z2,z3,z4,z174]),(0,[z0,z1,z2,z3,z4,z1493]),(0,[z0,z1494,z1,z3,z4,z6]),(0,[z0,z37,z3,z4,z6,z267]),(0,[z0,z1,z1495,z3,z4,z6]),(0,[z0,z176,z62,z3,z4,z6]),(0,[z0,z145,z158,z3,z4,z6])],[(0,[z0,z137,z232,z3,z4,z6]),(0,[z0,z1496,z2,z3,z4,z6]),(0,[z0,z271,z62,z3,z4,z6]),(0,[z0,z1,z1497,z3,z4,z6]),(0,[z128,z525,z1,z3,z4,z6]),(0,[z150,z0,z26,z3,z4,z6]),(0,[z150,z0,z2,z3,z623,z6]),(0,[z0,z1498,z1,z3,z4,z6]),(0,[z1499,z260,z1,z3,z4,z6]),(0,[z0,z190,z198,z3,z4,z6])],[(0,[z1173,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1500,z6])],[(0,[z758,z0,z3,z4,z290,z6]),(0,[z0,z228,z3,z172,z4,z6]),(0,[z0,z1273,z1,z3,z4,z6]),(0,[z114,z0,z26,z1,z3,z4]),(0,[z0,z1,z3,z4,z6,z1061])],[(0,[z193,z96,z1,z3,z4,z6]),(0,[z0,z1,z1501,z3,z4,z6]),(0,[z128,z36,z0,z3,z4,z6]),(0,[z0,z26,z176,z3,z4,z6]),(0,[z1502,z1,z2,z3,z4,z6])],[(0,[z52,z0,z17,z3,z4,z6]),(0,[z0,z1,z256,z3,z4,z6]),(0,[z1030,z1,z3,z4,z306,z6])],[(0,[z150,z193,z0,z3,z4,z6]),(0,[z42,z1,z3,z591,z4,z6]),(0,[z0,z1,z1249,z3,z4,z6]),(0,[z0,z1046,z2,z3,z4,z6]),(0,[z0,z1,z3,z532,z4,z202])],[(0,[z128,z0,z1,z3,z4,z6]),(0,[z0,z1440,z77,z3,z4,z6]),(0,[z1,z3,z188,z4,z290,z6]),(0,[z1503,z0,z1,z3,z4,z6]),(0,[z42,z1,z593,z3,z4,z6]),(0,[z52,z0,z190,z3,z4,z6]),(0,[z123,z0,z220,z3,z4,z6]),(0,[z0,z37,z76,z3,z4,z6]),(0,[z114,z0,z2,z3,z4,z21]),(0,[z1049,z1,z2,z3,z4,z6]),(0,[z1504,z1,z2,z3,z4,z6]),(0,[z242,z0,z220,z3,z4,z6])],[(0,[z0,z909,z1,z3,z4,z6])],[(0,[z0,z1,z1505,z3,z4,z6]),(0,[z42,z0,z17,z3,z4,z6]),(0,[z0,z37,z50,z3,z133,z6]),(0,[z0,z1,z3,z4,z1506,z6]),(0,[z0,z1,z3,z4,z1507,z6])]],
   [[(0,[z42,z1,z3,z4,z105,z6]),(0,[z147,z0,z907,z3,z4,z6]),(0,[z0,z1,z1508,z3,z4,z6]),(0,[z0,z34,z1,z2,z3,z155]),(0,[z0,z2,z146,z158,z3,z181])],[(0,[z42,z0,z190,z3,z4,z6]),(0,[z52,z0,z1454,z3,z4,z6]),(0,[z52,z0,z473,z3,z4,z6]),(0,[z0,z37,z232,z3,z4,z6]),(0,[z0,z822,z2,z3,z4,z6]),(0,[z0,z26,z209,z3,z4,z6]),(0,[z0,z1,z3,z480,z247,z4]),(0,[z0,z3,z4,z151,z499,z6]),(0,[z66,z1,z62,z3,z4,z6])],[(0,[z52,z0,z1278,z3,z4,z6]),(0,[z0,z26,z1,z3,z300,z4]),(0,[z0,z220,z50,z3,z4,z6]),(0,[z129,z0,z220,z3,z67,z6]),(0,[z71,z66,z1,z3,z4,z6]),(0,[z0,z1,z3,z1509,z4,z6]),(0,[z0,z1,z1510,z3,z4,z6])],[(0,[z0,z1,z3,z184,z67,z6]),(0,[z1,z2,z3,z4,z871,z6]),(0,[z0,z473,z62,z3,z4,z6]),(0,[z1,z3,z439,z4,z67,z6])],[(0,[z52,z0,z1,z3,z4,z6]),(0,[z0,z891,z2,z3,z4,z6]),(0,[z0,z1,z1511,z3,z4,z6]),(0,[z0,z1,z2,z135,z4,z762])],[(0,[z0,z1,z2,z3,z4,z1512]),(0,[z66,z1,z135,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1513]),(0,[z0,z1,z3,z1514,z4,z6])],[(0,[z0,z1,z62,z3,z290,z6]),(0,[z147,z66,z1,z3,z4,z6]),(0,[z0,z26,z220,z3,z4,z6]),(0,[z535,z1,z3,z4,z67,z6]),(0,[z66,z1,z23,z3,z4,z6]),(0,[z2,z3,z4,z151,z514,z6])],[(0,[z0,z26,z271,z3,z4,z6]),(0,[z0,z26,z1,z31,z4,z6]),(0,[z0,z1,z2,z31,z4,z25])],[(0,[z42,z0,z1,z3,z4,z6]),(0,[z139,z0,z304,z3,z4,z6]),(0,[z0,z220,z62,z3,z4,z6]),(0,[z0,z924,z3,z4,z67,z6]),(0,[z1161,z1,z62,z3,z4,z6])],[(0,[z0,z280,z1,z3,z4,z6]),(0,[z42,z1,z127,z188,z4,z6]),(0,[z0,z1,z3,z4,z1515,z6]),(0,[z1516,z1,z2,z3,z4,z6]),(0,[z0,z3,z1053,z4,z67,z6]),(0,[z0,z1,z3,z1517,z4,z6])],[(0,[z1,z185,z3,z295,z4,z6]),(0,[z68,z26,z1,z3,z134,z6]),(0,[z0,z1,z200,z3,z67,z6]),(0,[z0,z1,z3,z4,z1518,z6]),(0,[z0,z1,z62,z3,z40,z6]),(0,[z396,z0,z152,z3,z4,z6]),(0,[z0,z76,z198,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1519])],[(0,[z41,z0,z328,z3,z4,z6]),(0,[z0,z1,z1520,z3,z4,z6]),(0,[z0,z1,z89,z3,z4,z6]),(0,[z349,z0,z232,z3,z4,z6]),(0,[z0,z1,z2,z1521,z4,z6]),(0,[z748,z1,z2,z3,z4,z6]),(0,[z0,z220,z146,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1522])],[(0,[z170,z0,z104,z3,z4,z6]),(0,[z0,z1523,z2,z3,z4,z6]),(0,[z0,z1524,z2,z3,z4,z6]),(0,[z1525,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z326,z3,z181]),(0,[z0,z1,z374,z3,z4,z6]),(0,[z189,z66,z1,z3,z4,z6]),(0,[z0,z220,z135,z3,z4,z6]),(0,[z1,z2,z3,z1526,z4,z6])],[(0,[z0,z26,z3,z4,z231,z6]),(0,[z42,z0,z1266,z3,z4,z6]),(0,[z0,z1527,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1528]),(0,[z114,z0,z37,z1,z3,z4]),(1,[z0,z2,z3,z935,z6]),(0,[z36,z0,z253,z2,z3,z4]),(0,[z0,z220,z23,z3,z4,z6]),(0,[z0,z1,z2,z4,z762,z100])],[(0,[z128,z0,z137,z3,z4,z6]),(0,[z42,z507,z1,z3,z4,z6]),(0,[z376,z1,z2,z3,z4,z6]),(0,[z150,z0,z26,z3,z133,z6]),(0,[z260,z37,z1,z3,z4,z6]),(0,[z535,z1,z256,z3,z4,z6]),(0,[z150,z0,z183,z3,z4,z6]),(0,[z0,z1,z3,z4,z499,z238]),(0,[z45,z1,z2,z3,z298,z6]),(0,[z1529,z0,z1,z3,z4,z6])],[(0,[z193,z0,z1,z3,z4,z6]),(0,[z0,z1530,z2,z3,z4,z6]),(0,[z0,z459,z1,z399,z4,z6]),(0,[z0,z26,z3,z4,z93,z6]),(0,[z38,z0,z220,z3,z4,z6])]],
   [[(0,[z42,z0,z1,z3,z4,z886]),(0,[z42,z96,z1,z188,z4,z6]),(0,[z0,z1,z380,z3,z4,z6]),(0,[z66,z1,z3,z4,z662,z6]),(0,[z0,z1,z3,z4,z1531,z6])],[(0,[z0,z304,z2,z3,z4,z6]),(0,[z36,z0,z232,z3,z4,z6]),(0,[z68,z1,z2,z31,z4,z6]),(0,[z0,z1,z1532,z3,z4,z6]),(0,[z0,z1,z1533,z3,z4,z6])],[(0,[z1534,z0,z1,z3,z4,z6]),(0,[z0,z914,z3,z295,z4,z6]),(0,[z96,z173,z1,z3,z4,z6])],[(0,[z0,z232,z77,z3,z4,z6]),(0,[z0,z3,z4,z269,z384,z6]),(0,[z0,z240,z328,z3,z4,z6]),(0,[z1386,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z1535,z4,z6]),(0,[z220,z1,z3,z4,z514,z6])],[(0,[z42,z0,z3,z4,z1309,z6]),(0,[z0,z1,z1536,z3,z4,z6]),(1,[z0,z1,z3,z4,z1061]),(0,[z0,z1,z2,z3,z55,z390])],[(0,[z0,z1,z2,z3,z1537,z4]),(0,[z0,z1538,z1,z3,z4,z6]),(0,[z147,z0,z1,z3,z184,z6]),(0,[z138,z1,z2,z188,z4,z6]),(0,[z0,z1,z1539,z3,z4,z6]),(0,[z47,z0,z3,z4,z357,z6]),(0,[z0,z1,z2,z4,z6,z1540]),(0,[z0,z1,z1541,z3,z4,z6]),(0,[z95,z1,z3,z4,z67,z6])],[(0,[z260,z1,z2,z3,z4,z6]),(0,[z42,z0,z3,z1368,z4,z6]),(0,[z1,z228,z3,z188,z4,z6]),(0,[z0,z2,z3,z4,z1424,z6]),(0,[z0,z1,z3,z4,z6,z1542]),(0,[z0,z1,z1543,z3,z4,z6]),(0,[z150,z260,z2,z3,z4,z6]),(0,[z1,z2,z3,z1544,z4,z6]),(0,[z0,z1,z146,z3,z181,z67])],[(0,[z0,z1,z1545,z3,z4,z6]),(0,[z52,z42,z1,z3,z4,z6]),(0,[z0,z1546,z2,z3,z4,z6]),(0,[z0,z1547,z2,z3,z4,z6]),(0,[z129,z0,z1,z3,z623,z6]),(0,[z0,z220,z3,z4,z662,z6]),(0,[z0,z2,z3,z4,z6,z1548])],[(0,[z0,z1,z1549,z3,z4,z6]),(0,[z0,z1,z3,z1550,z4,z6]),(0,[z396,z0,z1,z3,z4,z551]),(0,[z171,z66,z1,z3,z4,z6])],[(0,[z349,z0,z1,z3,z4,z8]),(0,[z0,z83,z845,z3,z4,z6]),(0,[z0,z1,z3,z4,z224,z391]),(0,[z0,z1,z62,z127,z212,z6]),(0,[z95,z253,z2,z3,z4,z6])],[(0,[z0,z441,z3,z133,z4,z6]),(0,[z0,z2,z3,z4,z6,z1551]),(0,[z24,z1,z89,z3,z48,z6]),(0,[z0,z26,z3,z53,z4,z6]),(0,[z0,z2,z18,z820,z4,z6]),(0,[z0,z1,z1552,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1553]),(0,[z71,z0,z220,z3,z4,z6]),(0,[z0,z1,z1554,z3,z4,z6]),(0,[z0,z1,z2,z3,z910,z13])],[(0,[z0,z26,z3,z4,z6,z262]),(0,[z114,z0,z83,z2,z3,z4]),(0,[z0,z220,z34,z3,z4,z6]),(0,[z1555,z0,z1,z3,z4,z6]),(0,[z66,z1,z3,z4,z55,z6]),(0,[z1115,z1,z3,z4,z67,z6])],[(0,[z0,z1,z3,z4,z1556,z6]),(0,[z0,z1,z2,z3,z4,z1557]),(0,[z0,z26,z315,z3,z4,z6])],[(0,[z0,z2,z3,z1558,z4,z6]),(0,[z150,z0,z26,z3,z10,z6]),(0,[z0,z26,z3,z266,z4,z6])],[(0,[z1559,z0,z1,z3,z4,z6]),(0,[z52,z0,z1,z934,z4,z6]),(0,[z1,z3,z295,z51,z4,z6]),(0,[z0,z3,z172,z70,z4,z6]),(0,[z0,z26,z125,z3,z4,z6]),(0,[z114,z0,z2,z18,z3,z4]),(0,[z0,z1,z1560,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1561]),(0,[z0,z836,z176,z3,z4,z6])],[(0,[z24,z1,z380,z3,z48,z6]),(0,[z0,z1,z22,z323,z4,z6]),(0,[z0,z152,z22,z3,z4,z6]),(0,[z38,z0,z1,z3,z4,z57]),(0,[z0,z3,z4,z6,z203,z267])]],
   [[(0,[z193,z0,z137,z3,z4,z6]),(0,[z128,z0,z77,z3,z4,z6]),(0,[z52,z168,z0,z3,z4,z6])],[(0,[z0,z232,z3,z4,z48,z6]),(0,[z0,z1,z2,z3,z1562,z4]),(0,[z0,z37,z3,z4,z6,z12]),(0,[z0,z83,z3,z4,z6,z416]),(0,[z1563,z1,z2,z3,z4,z6]),(0,[z66,z1,z3,z4,z6,z1564]),(0,[z0,z253,z2,z3,z298,z6]),(0,[z0,z1,z2,z135,z4,z119])],[(0,[z365,z0,z26,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1565]),(0,[z0,z1,z3,z4,z6,z1566]),(0,[z0,z37,z1,z146,z3,z181]),(0,[z0,z34,z2,z3,z4,z262]),(0,[z317,z0,z1,z3,z4,z57]),(0,[z369,z1,z3,z4,z67,z6]),(0,[z0,z220,z3,z4,z55,z6]),(0,[z0,z1567,z190,z3,z4,z6]),(0,[z0,z17,z130,z3,z4,z6])],[(0,[z123,z42,z1,z3,z4,z174]),(0,[z0,z1,z3,z4,z6,z142]),(0,[z1568,z1,z2,z3,z4,z6]),(0,[z183,z1,z3,z4,z9,z6]),(0,[z0,z1,z2,z3,z837,z4]),(0,[z1569,z66,z1,z3,z4,z6])],[(0,[z0,z232,z2,z3,z4,z6]),(0,[z96,z473,z2,z3,z4,z6]),(0,[z0,z1,z1570,z3,z4,z6]),(0,[z189,z0,z220,z3,z4,z6]),(0,[z0,z1128,z3,z4,z67,z6]),(0,[z46,z168,z0,z2,z3,z4])],[(0,[z42,z1,z3,z471,z4,z6]),(0,[z0,z328,z1,z3,z4,z6]),(0,[z0,z1,z3,z1571,z4,z6]),(0,[z0,z1572,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1269]),(0,[z0,z1,z2,z3,z4,z1573]),(0,[z1574,z0,z1,z3,z4,z6]),(0,[z0,z1575,z1,z3,z4,z6])],[(0,[z41,z26,z77,z3,z4,z6]),(0,[z0,z1576,z1,z3,z4,z6]),(0,[z0,z1577,z2,z3,z4,z6]),(0,[z0,z1,z62,z3,z221,z6]),(0,[z0,z176,z3,z4,z67,z6])],[(1,[z891,z2,z3,z4,z6]),(0,[z26,z137,z3,z134,z4,z6]),(0,[z1578,z0,z232,z3,z4,z6]),(0,[z0,z271,z3,z4,z67,z6]),(0,[z1,z3,z4,z192,z9,z6]),(0,[z242,z66,z1,z3,z4,z6])],[(0,[z0,z1,z154,z3,z4,z6]),(0,[z1579,z0,z1,z3,z4,z6]),(0,[z0,z1580,z2,z3,z4,z6]),(0,[z0,z1567,z1,z3,z4,z6]),(1,[z0,z2,z3,z4,z1023])],[(0,[z0,z26,z3,z172,z4,z6]),(0,[z123,z1,z2,z3,z4,z806]),(0,[z0,z61,z2,z18,z4,z6]),(0,[z0,z1,z1581,z3,z4,z6]),(0,[z0,z1,z3,z4,z1582,z6]),(0,[z0,z1,z2,z146,z3,z181])],[(0,[z1,z2,z463,z188,z4,z6]),(0,[z42,z0,z3,z4,z1411,z6]),(0,[z683,z42,z1,z3,z4,z6]),(0,[z106,z0,z1,z3,z67,z6]),(0,[z0,z37,z87,z3,z4,z6]),(0,[z0,z1583,z2,z3,z4,z6]),(0,[z260,z61,z2,z3,z4,z6]),(0,[z36,z0,z20,z3,z4,z21]),(0,[z0,z1,z3,z1584,z4,z6])],[(0,[z1499,z0,z1,z3,z4,z6]),(0,[z52,z95,z1,z3,z4,z6]),(0,[z52,z0,z253,z3,z4,z6]),(0,[z1585,z0,z1,z3,z4,z6]),(0,[z0,z1245,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1586]),(0,[z1030,z1,z2,z3,z4,z6]),(0,[z46,z0,z176,z2,z4,z100])],[(0,[z0,z1,z3,z4,z1587,z6]),(0,[z927,z1,z2,z3,z4,z6]),(0,[z246,z0,z26,z3,z4,z6]),(0,[z0,z62,z3,z4,z6,z1548])],[(0,[z42,z0,z1,z97,z4,z6]),(0,[z0,z232,z3,z4,z239,z6]),(0,[z0,z1,z3,z1588,z4,z6]),(0,[z24,z419,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1589]),(0,[z0,z26,z158,z3,z4,z6]),(0,[z0,z1590,z1,z3,z4,z6]),(0,[z1591,z0,z1,z3,z4,z6]),(0,[z0,z1592,z2,z3,z4,z6]),(0,[z95,z1,z374,z3,z4,z6]),(0,[z0,z1593,z253,z3,z4,z6])],[(0,[z36,z0,z2,z3,z4,z405]),(0,[z0,z1,z62,z3,z298,z6]),(0,[z0,z1,z1594,z3,z4,z6])]],
   [[(0,[z42,z95,z1,z3,z4,z6]),(0,[z42,z0,z253,z3,z4,z6]),(0,[z96,z0,z220,z3,z4,z6]),(0,[z0,z3,z4,z153,z1595,z6]),(0,[z0,z1,z2,z3,z181,z519]),(0,[z171,z0,z220,z3,z4,z6]),(0,[z1596,z376,z1,z3,z4,z6])],[(0,[z358,z42,z1,z3,z4,z6]),(0,[z0,z26,z37,z3,z4,z6]),(0,[z0,z27,z37,z3,z4,z6]),(0,[z150,z0,z37,z3,z10,z6]),(0,[z0,z1,z571,z56,z4,z6]),(0,[z1151,z1,z3,z4,z67,z6]),(0,[z0,z17,z2,z3,z4,z14])],[(0,[z193,z0,z77,z3,z4,z6]),(0,[z42,z1,z188,z4,z55,z6]),(0,[z0,z1,z2,z97,z4,z371]),(0,[z0,z26,z152,z3,z4,z6]),(0,[z0,z1149,z2,z3,z4,z6]),(0,[z66,z1,z3,z4,z67,z6])],[(0,[z0,z26,z3,z311,z4,z6]),(0,[z0,z50,z3,z133,z499,z6])],[(0,[z0,z232,z304,z3,z4,z6]),(0,[z46,z0,z232,z3,z4,z6]),(0,[z0,z473,z3,z4,z67,z6]),(0,[z1,z1180,z2,z3,z4,z6]),(0,[z150,z0,z183,z3,z10,z6]),(0,[z0,z1597,z2,z3,z4,z6]),(0,[z129,z0,z220,z3,z4,z6]),(0,[z0,z1,z1598,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1599,z6]),(0,[z0,z1,z3,z1600,z4,z6]),(0,[z0,z1,z364,z3,z4,z6]),(0,[z0,z62,z3,z151,z67,z6]),(0,[z0,z1,z3,z283,z67,z6])],[(0,[z0,z232,z3,z133,z4,z6]),(0,[z0,z26,z2,z3,z300,z4]),(0,[z114,z0,z1,z2,z3,z4]),(0,[z0,z34,z62,z3,z4,z167]),(0,[z147,z0,z3,z4,z151,z6])],[(0,[z52,z170,z137,z3,z4,z6]),(0,[z0,z1461,z3,z4,z153,z6]),(0,[z478,z0,z1,z3,z4,z405]),(0,[z1601,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1602])],[(0,[z26,z137,z3,z188,z4,z6]),(0,[z260,z137,z2,z3,z4,z6]),(0,[z0,z1,z2,z31,z4,z6]),(0,[z0,z1603,z2,z3,z4,z6]),(0,[z0,z1,z1604,z3,z4,z6]),(0,[z0,z220,z3,z4,z6,z1605])],[(0,[z0,z240,z3,z4,z167,z6]),(0,[z0,z26,z3,z4,z316,z6]),(0,[z0,z26,z3,z4,z6,z731]),(0,[z0,z220,z3,z4,z67,z6]),(0,[z0,z1,z127,z212,z67,z6])],[(0,[z1,z2,z3,z4,z9,z6]),(0,[z0,z1,z3,z4,z6,z194]),(0,[z110,z2,z3,z188,z4,z6]),(0,[z0,z26,z527,z3,z4,z6]),(0,[z171,z0,z1,z72,z4,z6]),(0,[z0,z220,z61,z3,z4,z6]),(0,[z38,z66,z1,z3,z4,z6])],[(0,[z41,z0,z104,z3,z4,z6]),(0,[z41,z464,z77,z3,z4,z6]),(0,[z0,z2,z533,z53,z4,z6]),(0,[z0,z1,z3,z4,z6,z1606]),(0,[z68,z1,z2,z3,z134,z6]),(0,[z126,z68,z1,z3,z4,z6]),(0,[z38,z0,z152,z3,z4,z6])],[(0,[z0,z1393,z110,z3,z4,z6]),(0,[z0,z1,z3,z4,z1607,z6]),(0,[z0,z1608,z1,z3,z4,z6]),(0,[z0,z37,z1,z3,z4,z363]),(0,[z0,z1,z3,z4,z1609,z6]),(0,[z150,z260,z2,z3,z10,z6]),(0,[z0,z2,z3,z4,z1610,z6])],[(0,[z147,z1,z3,z4,z514,z6])],[(0,[z0,z1,z3,z4,z1611,z6]),(0,[z0,z711,z1,z3,z4,z6]),(0,[z0,z2,z3,z354,z4,z6]),(0,[z0,z1,z2,z820,z4,z6]),(0,[z0,z1,z437,z3,z4,z6]),(0,[z1612,z0,z2,z3,z4,z6])],[(0,[z128,z193,z1,z3,z4,z6]),(0,[z687,z0,z26,z3,z4,z6]),(0,[z124,z37,z1,z3,z4,z6]),(1,[z0,z1,z2,z870,z6])]],
   [[(0,[z0,z1,z2,z1201,z4,z6]),(0,[z0,z271,z89,z3,z4,z6]),(0,[z0,z1613,z1,z3,z4,z6]),(0,[z0,z240,z1,z3,z504,z6]),(0,[z0,z61,z2,z399,z4,z6]),(0,[z0,z176,z374,z3,z4,z6])],[(0,[z1614,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1615,z6]),(0,[z189,z0,z190,z2,z55,z6])],[(0,[z332,z0,z232,z3,z4,z6]),(0,[z0,z1,z3,z1616,z4,z6])],[(0,[z1617,z0,z1,z3,z4,z6]),(0,[z554,z0,z1,z3,z4,z279]),(0,[z1,z2,z3,z871,z48,z6]),(0,[z128,z0,z3,z133,z4,z6]),(0,[z0,z1,z3,z1618,z4,z6]),(0,[z880,z0,z1,z4,z67,z6])],[(0,[z0,z1,z2,z3,z1619,z6]),(0,[z0,z1620,z1,z3,z4,z6]),(0,[z1621,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z1622,z4,z6]),(0,[z1623,z0,z220,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z363])],[(0,[z0,z271,z380,z3,z4,z6]),(0,[z0,z2,z617,z3,z4,z167])],[(0,[z0,z77,z441,z3,z4,z6]),(0,[z0,z3,z295,z1287,z4,z6]),(0,[z332,z0,z53,z4,z67,z6]),(0,[z1,z3,z4,z9,z1059,z6]),(0,[z0,z1,z1624,z3,z4,z6]),(0,[z0,z1,z1625,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z1626]),(0,[z26,z137,z77,z3,z4,z6]),(0,[z1627,z0,z1,z3,z4,z6]),(0,[z52,z123,z1,z3,z4,z174]),(0,[z0,z232,z3,z4,z6,z57]),(0,[z0,z1,z2,z3,z4,z1319]),(0,[z124,z1,z2,z3,z4,z6]),(0,[z0,z37,z1,z3,z4,z371]),(0,[z0,z26,z3,z765,z4,z6]),(0,[z0,z1,z3,z4,z6,z1628]),(0,[z0,z451,z22,z3,z4,z6]),(0,[z0,z49,z3,z4,z151,z6])],[(0,[z42,z0,z473,z3,z4,z6]),(0,[z123,z1,z3,z4,z67,z174]),(0,[z0,z37,z3,z4,z384,z6]),(0,[z0,z1629,z1,z3,z4,z6]),(0,[z1630,z1,z2,z3,z4,z6]),(0,[z1631,z1,z2,z3,z4,z6]),(0,[z1,z3,z1092,z4,z67,z6]),(0,[z189,z0,z1,z2,z55,z6])],[(0,[z0,z1,z3,z1632,z4,z6]),(0,[z1633,z0,z1,z3,z4,z6]),(0,[z0,z1634,z1,z3,z4,z6]),(0,[z0,z152,z37,z3,z4,z6]),(0,[z376,z37,z1,z3,z4,z6]),(0,[z0,z50,z2,z3,z133,z238]),(0,[z248,z0,z1,z3,z67,z6]),(0,[z1635,z66,z1,z3,z4,z6]),(0,[z0,z1593,z1,z3,z4,z6])],[(0,[z0,z232,z3,z13,z4,z6]),(0,[z1,z185,z89,z3,z4,z6]),(0,[z66,z1,z89,z3,z4,z6]),(0,[z0,z26,z3,z4,z6,z338]),(0,[z0,z2,z3,z1636,z4,z6]),(0,[z1,z2,z3,z1356,z4,z6])],[(0,[z46,z42,z0,z1,z4,z100])],[(0,[z0,z50,z2,z3,z300,z133]),(1,[z1030,z1,z3,z4,z6])],[(0,[z0,z280,z304,z3,z4,z6]),(0,[z0,z1637,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z806,z174]),(0,[z0,z1,z146,z130,z3,z181])],[(0,[z1638,z0,z232,z3,z4,z6]),(0,[z397,z1,z2,z188,z4,z6]),(0,[z0,z1639,z1,z3,z4,z6]),(0,[z1,z3,z4,z67,z6,z1561]),(0,[z0,z1575,z253,z3,z4,z6])],[(0,[z1,z978,z141,z3,z4,z6]),(0,[z0,z232,z3,z4,z1120,z6]),(0,[z0,z1,z2,z3,z4,z371]),(0,[z0,z26,z1,z3,z4,z25])]],
   [[(0,[z758,z0,z1,z3,z4,z6]),(0,[z24,z42,z87,z3,z4,z6]),(0,[z66,z1,z185,z3,z4,z6]),(0,[z0,z1,z3,z445,z67,z6]),(0,[z0,z2,z3,z133,z221,z6]),(0,[z1640,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1641,z4,z6]),(0,[z0,z190,z3,z4,z67,z6]),(0,[z0,z2,z3,z973,z4,z6]),(0,[z0,z1642,z1,z3,z4,z6])],[(0,[z265,z0,z2,z3,z10,z6]),(0,[z170,z37,z137,z3,z4,z6]),(0,[z0,z232,z3,z4,z224,z6]),(0,[z0,z1643,z2,z3,z4,z6]),(0,[z460,z0,z1,z3,z623,z6]),(0,[z1,z2,z3,z4,z753,z6]),(0,[z0,z34,z196,z3,z4,z167]),(0,[z1644,z0,z1,z3,z4,z6])],[(0,[z128,z42,z1,z3,z4,z6]),(0,[z1,z3,z134,z4,z719,z6]),(0,[z0,z61,z2,z820,z4,z6]),(0,[z260,z183,z1,z3,z4,z6])],[(0,[z41,z0,z232,z3,z4,z6]),(0,[z0,z26,z1440,z3,z4,z6]),(0,[z0,z1,z3,z4,z1645,z6]),(0,[z0,z1646,z2,z3,z4,z6]),(0,[z0,z37,z3,z4,z153,z6]),(0,[z1480,z47,z0,z3,z4,z6]),(0,[z0,z83,z3,z480,z4,z6])],[(0,[z193,z0,z3,z133,z4,z6]),(0,[z147,z0,z1,z3,z4,z6]),(0,[z24,z42,z271,z3,z4,z6]),(0,[z24,z42,z1,z31,z4,z6]),(0,[z0,z26,z594,z3,z4,z6]),(0,[z0,z20,z1,z3,z4,z6]),(0,[z0,z37,z1,z3,z4,z390]),(0,[z1647,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1648]),(0,[z0,z1,z1649,z3,z4,z6]),(0,[z281,z42,z1,z3,z4,z6]),(0,[z234,z1,z3,z134,z4,z6]),(0,[z0,z1,z3,z4,z6,z1650])],[(0,[z0,z220,z185,z3,z4,z6]),(0,[z1651,z0,z1,z3,z4,z6])],[(0,[z170,z2,z3,z696,z4,z6]),(0,[z47,z96,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1652,z6]),(0,[z332,z0,z62,z53,z4,z6]),(0,[z0,z1653,z2,z3,z4,z6])],[(0,[z0,z1,z1654,z3,z4,z6]),(0,[z42,z1,z3,z4,z675,z6]),(0,[z52,z0,z1446,z3,z4,z6]),(0,[z1655,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z1656]),(0,[z52,z1,z185,z3,z4,z6]),(0,[z52,z0,z3,z354,z4,z6]),(0,[z123,z1,z62,z3,z4,z174]),(0,[z99,z0,z1,z3,z4,z6]),(0,[z0,z1247,z2,z3,z4,z6])],[(0,[z42,z1,z3,z295,z4,z6]),(0,[z52,z0,z1,z127,z212,z6]),(0,[z1,z256,z3,z439,z4,z6]),(0,[z1657,z1,z2,z3,z4,z6])],[(0,[z0,z37,z1,z135,z4,z119]),(0,[z1596,z0,z1,z3,z4,z6])],[(0,[z0,z1024,z2,z3,z4,z6]),(0,[z0,z50,z62,z3,z133,z6]),(0,[z0,z1,z2,z3,z4,z390]),(0,[z0,z1,z3,z4,z6,z899])],[(0,[z0,z1,z3,z852,z4,z6]),(0,[z0,z1,z3,z4,z269,z6]),(0,[z0,z1,z3,z1658,z4,z6]),(0,[z24,z1,z2,z3,z48,z371]),(0,[z26,z1,z3,z4,z9,z6]),(0,[z0,z1659,z1,z3,z4,z6]),(0,[z114,z0,z253,z2,z3,z4])],[(0,[z0,z1,z1660,z3,z4,z6]),(0,[z42,z0,z1,z127,z212,z6]),(0,[z0,z26,z511,z3,z4,z6]),(0,[z1,z2,z3,z134,z871,z6]),(0,[z236,z0,z26,z3,z4,z6]),(0,[z0,z1,z214,z3,z300,z4]),(0,[z129,z66,z1,z3,z4,z6])]],
   [[(0,[z683,z1,z2,z3,z48,z6]),(0,[z0,z26,z3,z4,z362,z6]),(0,[z0,z26,z3,z361,z4,z6]),(0,[z0,z1,z23,z414,z4,z6]),(0,[z0,z1141,z1,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z1661])],[(0,[z0,z1,z1662,z3,z4,z6]),(0,[z448,z0,z1,z3,z4,z392]),(0,[z0,z879,z3,z172,z4,z6]),(0,[z0,z26,z3,z4,z151,z6])],[(0,[z1663,z0,z1,z3,z4,z6]),(0,[z1451,z0,z1,z3,z4,z6]),(0,[z66,z1,z141,z3,z4,z6]),(0,[z0,z1,z1664,z3,z4,z6])],[(0,[z0,z1,z482,z3,z4,z6]),(0,[z0,z1285,z2,z3,z4,z6]),(0,[z0,z26,z1,z97,z4,z6]),(0,[z0,z190,z62,z3,z4,z6]),(0,[z0,z1,z223,z3,z4,z430]),(0,[z189,z0,z1,z437,z55,z6])],[(0,[z382,z42,z1,z3,z4,z6]),(0,[z1665,z1,z2,z3,z4,z6]),(0,[z66,z1,z3,z4,z4,z6]),(0,[z0,z76,z3,z4,z67,z6])],[(0,[z41,z77,z3,z4,z67,z6]),(0,[z42,z1,z165,z3,z4,z6]),(0,[z0,z83,z3,z4,z499,z6]),(0,[z0,z183,z61,z3,z4,z6]),(0,[z168,z0,z2,z135,z3,z4])],[(0,[z0,z110,z2,z3,z4,z6]),(0,[z234,z1,z3,z188,z4,z6]),(0,[z68,z0,z232,z3,z4,z6]),(0,[z0,z49,z1,z3,z4,z6]),(0,[z0,z37,z176,z3,z4,z6]),(0,[z0,z1,z3,z1666,z4,z6]),(0,[z0,z1,z23,z4,z418,z6]),(0,[z0,z1,z62,z3,z13,z14])],[(0,[z66,z1,z143,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1667]),(0,[z0,z34,z3,z4,z67,z167]),(0,[z0,z1,z2,z3,z4,z762])],[(0,[z0,z1,z1668,z3,z4,z6]),(0,[z52,z369,z1,z3,z4,z6]),(0,[z0,z17,z62,z3,z4,z6])],[(0,[z0,z1,z3,z4,z290,z6]),(0,[z0,z220,z141,z3,z4,z6]),(0,[z189,z52,z0,z1,z55,z6]),(0,[z0,z1669,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1670,z6]),(0,[z0,z1,z62,z3,z415,z6]),(0,[z168,z0,z2,z3,z4,z14])],[(0,[z52,z47,z0,z3,z4,z6]),(0,[z1366,z0,z1,z3,z4,z6]),(0,[z0,z3,z172,z4,z67,z6]),(0,[z0,z1,z3,z1671,z4,z6]),(0,[z47,z2,z3,z134,z4,z6]),(0,[z0,z50,z1,z3,z623,z6]),(0,[z36,z66,z1,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z1672])],[(0,[z170,z137,z2,z3,z4,z6]),(0,[z516,z42,z1,z3,z4,z6]),(0,[z0,z1,z31,z4,z67,z6]),(0,[z0,z2,z3,z133,z935,z6]),(0,[z129,z0,z1,z3,z1164,z6]),(0,[z0,z220,z3,z4,z4,z6]),(0,[z38,z0,z1,z3,z4,z646]),(0,[z1673,z0,z1,z3,z4,z6])],[(0,[z42,z369,z1,z3,z4,z6]),(0,[z24,z66,z1,z3,z4,z6]),(0,[z24,z42,z1,z3,z4,z371]),(0,[z0,z34,z232,z3,z4,z6]),(0,[z0,z26,z3,z4,z854,z6]),(0,[z0,z1,z2,z3,z4,z1674]),(0,[z36,z0,z2,z3,z453,z4]),(0,[z0,z1,z3,z102,z1164,z6])],[(0,[z47,z0,z2,z3,z4,z6]),(0,[z0,z271,z2,z31,z4,z6]),(0,[z0,z1,z3,z4,z1595,z6]),(0,[z369,z2,z3,z354,z4,z6])],[(0,[z0,z220,z143,z3,z4,z6]),(0,[z0,z37,z1,z3,z300,z4]),(0,[z332,z114,z0,z2,z53,z4]),(0,[z0,z1,z2,z3,z1164,z6])],[(0,[z41,z419,z1,z3,z4,z6]),(0,[z0,z26,z3,z300,z133,z4]),(0,[z1,z1604,z3,z4,z9,z6]),(0,[z45,z1,z62,z3,z4,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 466) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 466).take 456) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 922).take 465) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1387).take 257) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1644)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [466, 456, 465, 257] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 61).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 61).take 57).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 118).take 65).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 183).take 67).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 250).take 64).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 314).take 66).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 380).take 56).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc7 : chunkOK 5 ((bkB.flatten.drop 436).take 68).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc8 : chunkOK 5 ((bkB.flatten.drop 504).take 8).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [61, 57, 65, 67, 64, 66, 56, 68, 8] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_cons pc7 (windowsF_cons pc8 (windowsF_nil pcend)))))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38571

theorem PEqualNP.Outside.L_meta_38571 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 3941133000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 3941133000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38571.solve