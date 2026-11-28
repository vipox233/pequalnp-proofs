import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42816

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
  Nat.testBit (4008373984 * 2 ^ 32 + 4008372352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00014870c085436c#64 ++ 0x0000521c302150db#64 ++ 0xbd27d8f1d18fc7ff#64 ++ 0xef49f63c7463f1ff#64 : BitVec 256),
   (0x044b0b16063318b5#64 ++ 0x4112c2c5818cc62d#64 ++ 0xfedb2f1e2e7338ff#64 ++ 0xffb6cbc78b9cce3f#64 : BitVec 256),
   (0x0b14300b705c2d19#64 ++ 0x82c50c02dc170b46#64 ++ 0xcf1c301ff07c3f1f#64 ++ 0xb3c70c07fc1f0fc7#64 : BitVec 256),
   (0x13a035a03b8036c2#64 ++ 0x04e80d680ee00db0#64 ++ 0xf7e03fe03f803fe3#64 ++ 0x7df80ff80fe00ff8#64 : BitVec 256),
   (0x03fe80003d6a8000#64 ++ 0x00ffa0000f5aa000#64 ++ 0x9bffc0003fffc002#64 ++ 0xe6fff0000ffff000#64 : BitVec 256),
   (0x23fffedd80000000#64 ++ 0x08ffffb760000000#64 ++ 0xe3ffffffc0000001#64 ++ 0xf8fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00014870c085436c 0x0000521c302150db 0xbd27d8f1d18fc7ff 0xef49f63c7463f1ff

def z1 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x9bffc0003fffc002 0xe6fff0000ffff000

def z2 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xfedb2f1e2e7338ff 0xffb6cbc78b9cce3f

def z3 : W := mkw 0x080000027d7ead19 0x820000009f5fab46 0x1c0000003fffff1e 0x070000000fffffc7

def z4 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xcf1c301ff07c3f1f 0xb3c70c07fc1f0fc7

def z5 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xf7e03fe03f803fe3 0x7df80ff80fe00ff8

def z6 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xe3ffffffc0000001 0xf8fffffff0000000

def z7 : W := mkw 0x044b0b14062310a4 0x4112c2c50188c429 0x30c30f000e0300e0 0x4c30c3c00380c038

def z8 : W := mkw 0x0b143009704c2508 0x82c50c025c130942 0x01041001d00c0700 0x00410400740301c0

def z9 : W := mkw 0x14eb0fb40fa312e6 0x453ac3ed03e8c4b9 0x30e30fe00f8300e0 0x4c38c3f803e0c038

def z10 : W := mkw 0x23b5fedd80000000 0x08ed7fb760000000 0x6124ffffc0000001 0x18493ffff0000000

def z11 : W := mkw 0x04014b76c2955bfd 0x410052ddb0a556ff 0xfd27ffffd18fffff 0xff49fffff463ffff

def z12 : W := mkw 0x17eb3fb63fb33ef7 0x45facfed8feccfbd 0xfffb3ffe3ff33fff 0xfffecfff8ffccfff

def z13 : W := mkw 0x20017edd80000000 0x08005fb760000000 0x60003fffc0000001 0x18000ffff0000000

def z14 : W := mkw 0x0800300b40142d19 0x82000c02d0050b46 0xce18301fe0703f1f 0xb3860c07f81c0fc7

def z15 : W := mkw 0x03fe8000046a8000 0x00ffa000011aa000 0x8bffc000007fc000 0xe2fff000001ff000

def z16 : W := mkw 0x0000000000000000 0x0000000000000000 0xc218201e00000001 0xb086080780000000

def z17 : W := mkw 0x00014970c28553ec 0x0000525c30a154fb 0xffe7fff1ff8fffff 0xfff9fffc7fe3ffff

def z18 : W := mkw 0x004b0a1400000000 0x0012c28500000000 0xe2db2f1e00000001 0xf8b6cbc780000000

def z19 : W := mkw 0x23b4f4c980000000 0x08ed3d3260000000 0x0124d0e1c0000000 0x0049343870000000

def z20 : W := mkw 0x20ea868400000000 0x083aa1a100000000 0x00c0070000000000 0x003001c000000000

def z21 : W := mkw 0x0b14300b30582c11 0x82c50c02cc160b04 0xc718300e30703f03 0x31c60c038c1c0fc0

def z22 : W := mkw 0x23a17edd80000000 0x08e85fb760000000 0xe3e03fffc0000001 0x78f80ffff0000000

def z23 : W := mkw 0x24017fdf821118b5 0x49005ff7e084462d 0x64003fffc00038fd 0x19000ffff0000e3f

def z24 : W := mkw 0x044b4b76c6b75bfd 0x4112d2ddb1add6ff 0xffffffffffffffff 0xffffffffffffffff

def z25 : W := mkw 0x07ff8b163f7b98b5 0x41ffe2c58fdee62d 0xffffef1e3ffff8ff 0xfffffbc78ffffe3f

def z26 : W := mkw 0x03fec060fdeec348 0x00ffb0183f7bb0d2 0x9bffd0e1ffffc702 0xe6fff4387ffff1c0

def z27 : W := mkw 0x10000120028036c2 0x0400004800a00db0 0x0400000000003fe0 0x0100000000000ff8

def z28 : W := mkw 0x20ebced480000000 0x083af3b520000000 0x20e3cfe000000000 0x4838f3f800000000

def z29 : W := mkw 0x044b4b7686b35af5 0x4112d2dda1acd6bd 0xfefbeffe2ff3f8ff 0xffbefbff8bfcfe3f

def z30 : W := mkw 0x000000204085436c 0x00000008102150db 0x1c000000118fc7fe 0x070000000463f1ff

def z31 : W := mkw 0x03ffc870c085436c 0x00fff21c302150db 0xbfffd8f1d18fc7ff 0xeffff63c7463f1ff

def z32 : W := mkw 0x0000000200100811 0x0000000080040204 0xce18201e2070381f 0xb3860807881c0e07

def z33 : W := mkw 0x0314300900000000 0x00c50c0240000000 0x01041001c0000000 0x0041040070000000

def z34 : W := mkw 0x1ba035a27bdc3fdb 0x86e80d689ef70ff6 0xffe03fe03ffc3fff 0x7ff80ff80fff0fff

def z35 : W := mkw 0x004a000004220000 0x0012800001088000 0x02d800002e700000 0x00b600000b9c0000

def z36 : W := mkw 0x10017df0c28577ee 0x04005f7c30a15dfb 0x64003ff1c0003ffd 0x19000ffc70000fff

def z37 : W := mkw 0x004a000004220000 0x0012800001088000 0x9adb00002e730002 0xe6b6c0000b9cc000

def z38 : W := mkw 0x03b4800039488000 0x00ed20000e522000 0x0124c000118cc000 0x0049300004633000

def z39 : W := mkw 0x100035a0028036c2 0x04000d6800a00db0 0xf6c03fe02e003fe3 0x7db00ff80b800ff8

def z40 : W := mkw 0x0b14300b40142d19 0x82c50c02d0050b46 0xc71c301fc0003f1d 0xb1c70c07f0000fc7

def z41 : W := mkw 0x37ffffffbfb33ef7 0x4dffffffefeccfbd 0xfffffffffff33fff 0xfffffffffffccfff

def z42 : W := mkw 0x04000102063318b5 0x41000040818cc62d 0xde18201e2e7338ff 0xb78608078b9cce3f

def z43 : W := mkw 0x0800300b40142d19 0x82000c02d0050b46 0xcd04301fd00c3f1f 0xb3410c07f4030fc7

def z44 : W := mkw 0x0000010002001080 0x0000004000800420 0x42c027002e003800 0x10b009c00b800e00

def z45 : W := mkw 0x0b147069f0cc6748 0x82c51c1a7c3319d2 0x0124d0e1d18cc700 0x00493438746331c0

def z46 : W := mkw 0x00014850c005412c 0x000052143001504b 0x0807c011c00fc01c 0x8201f0047003f007

def z47 : W := mkw 0x00ea80000d228000 0x003aa0000348a000 0x10e3c0000f83c000 0x4438f00003e0f000

def z48 : W := mkw 0x23fffeddbd6a8000 0x08ffffb76f5aa000 0xfbffffffffffc003 0xfefffffffffff000

def z49 : W := mkw 0x03ff8a143d6a8000 0x00ffe2850f5aa000 0xfbffef1e3fffc003 0xfefffbc78ffff000

def z50 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x240018f1c00007fd 0x0900063c700001ff

def z51 : W := mkw 0x23157edd80000000 0x08c55fb760000000 0xe31c3fffc0000001 0xb8c70ffff0000000

def z52 : W := mkw 0x23fffefdfdefc36c 0x08ffffbf7f7bf0db 0xffffffffffffc7ff 0xfffffffffffff1ff

def z53 : W := mkw 0x0f5f3b1f767f3dbd 0xc3d7cec7dd9fcf6f 0xffdf3f1ffe7f3fff 0xfff7cfc7ff9fcfff

def z54 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x1c07c011d18fc7fe 0x8701f0047463f1ff

def z55 : W := mkw 0x00010910020110a4 0x0000424400804429 0xfec32f102e0338ff 0xffb0cbc40b80ce3f

def z56 : W := mkw 0x0000002000800240 0x0000000800200090 0xbd27d8e0118fc7e3 0xef49f6380463f1f8

def z57 : W := mkw 0x00ea80000d228000 0x003aa0000348a000 0x00c000000e000000 0x0030000003800000

def z58 : W := mkw 0x005e8000046a8000 0x0017a000011aa000 0x081fc000007fc000 0x8207f000001ff000

def z59 : W := mkw 0x004b0a1400000000 0x0012c28500000000 0x001b001e00000000 0x8006c00780000000

def z60 : W := mkw 0x24ebcfd6863318b5 0x493af3f5a18cc62d 0xfefbeffe2e7338ff 0xffbefbff8b9cce3f

def z61 : W := mkw 0x03a0000039000000 0x00e800000e400000 0x93e000003f800002 0x64f800000fe00000

def z62 : W := mkw 0x13feb5a03feab6c2 0x04ffad680ffaadb0 0xffffffe03fffffe3 0xfffffff80ffffff8

def z63 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x1c1b001e2e7338fe 0x8706c0078b9cce3f

def z64 : W := mkw 0x100001203b8036c2 0x040000480ee00db0 0x140000003f803fe2 0x050000000fe00ff8

def z65 : W := mkw 0x205fca5d80000000 0x0817f29760000000 0x001fc01fc0000000 0x8007f007f0000000

def z66 : W := mkw 0x04014b76c2955bfd 0x410052ddb0a556ff 0x64003fffc0003ffd 0x19000ffff0000fff

def z67 : W := mkw 0x204b7edd80000000 0x0812dfb760000000 0xe2db3fffc0000001 0xf8b6cffff0000000

def z68 : W := mkw 0x2fffffdff67f3dbd 0xcbfffff7fd9fcf6f 0xfffffffffe7f3fff 0xffffffffff9fcfff

def z69 : W := mkw 0x08000002705c2d19 0x820000009c170b46 0x0c000000307c3f1e 0x030000000c1f0fc7

def z70 : W := mkw 0x2bfffedff05c2d19 0x8affffb7fc170b46 0xeffffffff07c3f1f 0xfbfffffffc1f0fc7

def z71 : W := mkw 0x33fffffdbb8036c2 0x0cffffff6ee00db0 0xf7ffffffff803fe3 0xfdffffffffe00ff8

def z72 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x66c03fe02e003fe1 0x19b00ff80b800ff8

def z73 : W := mkw 0x0800300b00102c11 0x82000c02c0040b04 0x4000200e00003800 0x1000080380000e00

def z74 : W := mkw 0x0000002000800240 0x0000000800200090 0x240018e0000007e1 0x09000638000001f8

def z75 : W := mkw 0x03b4800039488000 0x00ed20000e522000 0x8b3cc00031fcc002 0xa2cf30000c7f3000

def z76 : W := mkw 0x0000010202101891 0x0000004080840624 0xfed82f1e2e7038ff 0xffb60bc78b9c0e3f

def z77 : W := mkw 0x0300300030002400 0x00c00c000c000900 0x4200200020003800 0x1080080008000e00

def z78 : W := mkw 0x0001485080000000 0x0000521420000000 0x0007c011c0000000 0x8001f00470000000

def z79 : W := mkw 0x044b0b1606321891 0x4112c2c5818c8624 0xe2db2f1e2e703801 0xf8b6cbc78b9c0e00

def z80 : W := mkw 0x0000010002001080 0x0000004000800420 0xf6c02f002e0038e3 0x7db00bc00b800e38

def z81 : W := mkw 0x100035a0028036c2 0x04000d6800a00db0 0x64003fe000003fe1 0x19000ff800000ff8

def z82 : W := mkw 0x23fffeddb0480000 0x08ffffb76c120000 0xebfffffff07c0003 0xfafffffffc1f0000

def z83 : W := mkw 0x10a005a03b8036c2 0x042801680ee00db0 0x34e00fe03f803fe2 0x4d3803f80fe00ff8

def z84 : W := mkw 0x0814000b405c0919 0x82050002d0170246 0x081c001fc07c001c 0x82070007f01f0007

def z85 : W := mkw 0x0bfeb00b7d7ead19 0x82ffac02df5fab46 0xdffff01fffffff1f 0xf7fffc07ffffffc7

def z86 : W := mkw 0x2bfffedffd7ead19 0x8affffb7ff5fab46 0xffffffffffffff1f 0xffffffffffffffc7

def z87 : W := mkw 0x00fe80000d6a8000 0x003fa000035aa000 0x18ffc0000fffc000 0xc63ff00003fff000

def z88 : W := mkw 0x045f8b16067b98b5 0x4117e2c5819ee62d 0xfedfef1e2e7ff8ff 0xffb7fbc78b9ffe3f

def z89 : W := mkw 0x00014850c005412c 0x000052143001504b 0xbc07c811c00fc0ff 0xef01f2047003f03f

def z90 : W := mkw 0x04000102063318b5 0x41000040818cc62d 0x1c0000002e7338fe 0x070000000b9cce3f

def z91 : W := mkw 0x0800300b40142d19 0x82000c02d0050b46 0x4400301fc0003f1d 0x11000c07f0000fc7

def z92 : W := mkw 0x0b15787bf0dd6f7d 0x82c55e1efc375bdf 0xff3ff8fff1ffffff 0xffcffe3ffc7fffff

def z93 : W := mkw 0x07fe83063f7a9891 0x41ffa0c18fdea624 0x42d8270e2e703800 0x10b609c38b9c0e00

def z94 : W := mkw 0x0801787bc0956f7d 0x82005e1ef0255bdf 0xfd27f8ffd18fffff 0xff49fe3ff463ffff

def z95 : W := mkw 0x03a0348039000000 0x00e80d200e400000 0xf3e03fe03f800003 0x7cf80ff80fe00000

def z96 : W := mkw 0x13a034a039802642 0x04e80d280e600990 0x012010e011800700 0x00480438046001c0

def z97 : W := mkw 0x13eb3fb43b8036c2 0x04facfed0ee00db0 0xf7fb3ffe3f803fe3 0xfdfecfff8fe00ff8

def z98 : W := mkw 0x0c4b0b16767f3dbd 0xc312c2c59d9fcf6f 0xfedb2f1e3e7f3fff 0xffb6cbc78f9fcfff

def z99 : W := mkw 0x0001081000010024 0x0000420400004009 0xbc030810000300ff 0xef00c2040000c03f

def z100 : W := mkw 0x23fffedd80010024 0x08ffffb760004009 0xffffffffc00300ff 0xfffffffff000c03f

def z101 : W := mkw 0x07fe83063f7a9891 0x41ffa0c18fdea624 0xdbffe70e3ffff802 0xf6fff9c38ffffe00

def z102 : W := mkw 0x03a14870f985436c 0x00e8521c3e6150db 0xbfe7d8f1ff8fc7ff 0xeff9f63c7fe3f1ff

def z103 : W := mkw 0x03feb48000000000 0x00ffad2000000000 0xe3ffffe000000001 0xf8fffff800000000

def z104 : W := mkw 0x0001487080814264 0x0000521c20205099 0xb523d8e01183c7e3 0x6d48f6380460f1f8

def z105 : W := mkw 0x13a075e0fb8477ca 0x04e81d783ee11df2 0xf7e4ffe1ff8cffe3 0x7df93ff87fe33ff8

def z106 : W := mkw 0x13a035803b003482 0x04e80d600ec00d20 0x42c027002e003800 0x10b009c00b800e00

def z107 : W := mkw 0x13a17df0fb8577ee 0x04e85f7c3ee15dfb 0xffe7fff1ff8fffff 0xfff9fffc7fe3ffff

def z108 : W := mkw 0x00004060c0844348 0x00001018302110d2 0x0124d0e1d18cc700 0x00493438746331c0

def z109 : W := mkw 0x044a030606321891 0x411280c1818c8624 0x42d8270e2e703800 0x10b609c38b9c0e00

def z110 : W := mkw 0x044a030406221080 0x411280c101888420 0x00c007000e000000 0x003001c003800000

def z111 : W := mkw 0x00014870c085436c 0x0000521c302150db 0xa527d8f1c00007fd 0xe949f63c700001ff

def z112 : W := mkw 0x000000003d6a8000 0x000000000f5aa000 0x180000003fffc002 0x060000000ffff000

def z113 : W := mkw 0x0000002000800240 0x0000000800200090 0xb52018e0118007e3 0x6d480638046001f8

def z114 : W := mkw 0x13feb5803f6ab482 0x04ffad600fdaad20 0xdbffe7003ffff802 0xf6fff9c00ffffe00

def z115 : W := mkw 0x03a0300039002400 0x00e80c000e400900 0xd7e030003f803f03 0x75f80c000fe00fc0

def z116 : W := mkw 0x044b4b74c6a753ec 0x4112d2dd31a9d4fb 0xbde7dff1df8fc7ff 0xef79f7fc77e3f1ff

def z117 : W := mkw 0x03a0348000000000 0x00e80d2000000000 0xe3e03fe000000001 0x78f80ff800000000

def z118 : W := mkw 0x07ffcb76ffffdbfd 0x41fff2ddbffff6ff 0xffffffffffffffff 0xffffffffffffffff

def z119 : W := mkw 0x0400000204330835 0x41000000810cc20d 0x080000000073001c 0x02000000001cc007

def z120 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x0d041001f07c3f1e 0x034104007c1f0fc7

def z121 : W := mkw 0x1bb434a979cc274a 0x86ed0d2a5e7309d2 0x012410e1d18c0700 0x00490438746301c0

def z122 : W := mkw 0x1bb435ab7bdc3fdb 0x86ed0d6adef70ff6 0xfffc3ffffffc3fff 0xffff0fffffff0fff

def z123 : W := mkw 0x180001227bdc3fdb 0x860000489ef70ff6 0x1c0000003ffc3ffe 0x070000000fff0fff

def z124 : W := mkw 0x0000000000000000 0x0000000000000000 0x0124c000118cc000 0x0049300004633000

def z125 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x4adb271e2e73381c 0x92b6c9c78b9cce07

def z126 : W := mkw 0x10a035a00b8036c2 0x04280d6802e00db0 0x74e03fe00f803fe1 0x5d380ff803e00ff8

def z127 : W := mkw 0x0314300030482400 0x00c50c000c120900 0xcf1c3000307c3f03 0xb3c70c000c1f0fc0

def z128 : W := mkw 0x13feb5a03b8036c2 0x04ffad680ee00db0 0xf7ffffe03f803fe3 0xfdfffff80fe00ff8

def z129 : W := mkw 0x03b4000039480000 0x00ed00000e520000 0x9bfc00003ffc0002 0xe6ff00000fff0000

def z130 : W := mkw 0x044b0b14062310a4 0x4112c2c50188c429 0xf6c32f002e0338e3 0x7db0cbc00b80ce38

def z131 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x02d800002e700000 0x00b600000b9c0000

def z132 : W := mkw 0x004b4a5480000000 0x0012d29520000000 0xe3ffffffc0000001 0xf8fffffff0000000

def z133 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x9adb00002e730002 0xe6b6c0000b9cc000

def z134 : W := mkw 0x1bb435ab3bd83ed3 0x86ed0d6acef60fb4 0xf7f83fee3ff03fe3 0x7dfe0ffb8ffc0ff8

def z135 : W := mkw 0x0001081000010024 0x0000420400004009 0xbd27c810118fc0ff 0xef49f2040463f03f

def z136 : W := mkw 0x0814300b405c2d19 0x82050c02d0170b46 0x4c1c301fc07c3f1d 0x93070c07f01f0fc7

def z137 : W := mkw 0x044b4b7486a352e4 0x4112d2dd21a8d4b9 0x30e3cfe00f83c0e0 0x4c38f3f803e0f038

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0x8500100010000703 0x21400400040001c0

def z139 : W := mkw 0x0000000000000000 0x0000000000000000 0x9927c000118fc002 0xe649f0000463f000

def z140 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x4618301fe0703f1d 0x11860c07f81c0fc7

def z141 : W := mkw 0x0b14300b30582c11 0x82c50c02cc160b04 0x4218200e20703800 0x10860803881c0e00

def z142 : W := mkw 0x04010b16021118b5 0x410042c58084462d 0x64002f1e000038fd 0x19000bc780000e3f

def z143 : W := mkw 0x044b0a1604330835 0x4112c285810cc20d 0x081b001e0073001c 0x8206c007801cc007

def z144 : W := mkw 0x23fffefdc085436c 0x08ffffbf702150db 0xe7ffffffc00007fd 0xf9fffffff00001ff

def z145 : W := mkw 0x2b157edff05c2d19 0x8ac55fb7fc170b46 0xef1c3ffff07c3f1f 0xbbc70ffffc1f0fc7

def z146 : W := mkw 0x0001081000010024 0x0000420400004009 0x24000810000000fd 0x090002040000003f

def z147 : W := mkw 0x0000000040040108 0x0000000010010042 0x8d041011d00c071f 0xa3410404740301c7

def z148 : W := mkw 0x17eb3f963f333cb7 0x45facfe58fcccf2d 0xfedb2f1e2e7338ff 0xffb6cbc78b9cce3f

def z149 : W := mkw 0x03fe80207defc36c 0x00ffa0081f7bf0db 0x9fffc0003fffc7fe 0xe7fff0000ffff1ff

def z150 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xffe7ffe03f8fffe3 0xfff9fff80fe3fff8

def z151 : W := mkw 0x13b4b5a03bc8b6c2 0x04ed2d680ef22db0 0xf7e4ffe03f8cffe3 0x7df93ff80fe33ff8

def z152 : W := mkw 0x205ffedd80000000 0x0817ffb760000000 0x601fffffc0000001 0x9807fffff0000000

def z153 : W := mkw 0x10a14df08b8152e6 0x0428537c22e054b9 0x30e3cfe00f83c0e0 0x4c38f3f803e0f038

def z154 : W := mkw 0x23feb68d00000000 0x08ffada340000000 0x42d8270e00000000 0x10b609c380000000

def z155 : W := mkw 0x23ffced480000000 0x08fff3b520000000 0xa3ffcfe000000000 0xe8fff3f800000000

def z156 : W := mkw 0x23fffedd846a8000 0x08ffffb7611aa000 0xebffffffc07fc001 0xfafffffff01ff000

def z157 : W := mkw 0x0b14300b7d7ead19 0x82c50c02df5fab46 0xdf1c301fffffff1f 0xb7c70c07ffffffc7

def z158 : W := mkw 0x005fc850c46fc12c 0x0017f214311bf04b 0x081fc011c07fc01c 0x8207f004701ff007

def z159 : W := mkw 0x0bfeb00b3d7aac11 0x82ffac02cf5eab04 0xdbffe00e3ffff802 0xf6fff8038ffffe00

def z160 : W := mkw 0x1fff3fbf7fff3fff 0xc7ffcfefdfffcfff 0xffff3fffffff3fff 0xffffcfffffffcfff

def z161 : W := mkw 0x0300300030002400 0x00c00c000c000900 0x0100100010000700 0x00400400040001c0

def z162 : W := mkw 0x200074c980000000 0x08001d3260000000 0x000010e1c0000000 0x0000043870000000

def z163 : W := mkw 0x0b143009704c2508 0x82c50c025c130942 0xc7043001f00c3f03 0x31c10c007c030fc0

def z164 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x3827c8f1c18fc0fc 0xce09f23c7063f03f

def z165 : W := mkw 0x00004060c0844348 0x00001018302110d2 0x000010e1c0000700 0x00000438700001c0

def z166 : W := mkw 0x23fffefd80800240 0x08ffffbf60200090 0xf7ffffffd18007e3 0xfdfffffff46001f8

def z167 : W := mkw 0x13ea35a03fa236c2 0x04fa8d680fe88db0 0xfffb3fe03ff33fe3 0xfffecff80ffccff8

def z168 : W := mkw 0x044a0306063318b5 0x411280c1818cc62d 0x5ed8270e2e7338fe 0x17b609c38b9cce3f

def z169 : W := mkw 0x03fe800000000000 0x00ffa00000000000 0x83ffc00000000000 0xe0fff00000000000

def z170 : W := mkw 0x0300300030002400 0x00c00c000c000900 0xc700300030003f03 0x31c00c000c000fc0

def z171 : W := mkw 0x10a005a00b8012c2 0x0428016802e004b0 0x30e00fe00f8000e0 0x4c3803f803e00038

def z172 : W := mkw 0x03feb4803d6a8000 0x00ffad200f5aa000 0xfbffffe03fffc003 0xfefffff80ffff000

def z173 : W := mkw 0x23fef6cd80000000 0x08ffbdb360000000 0x43fcf7efc0000000 0x10ff3dfbf0000000

def z174 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x42dfe71fc0000000 0x90b7f9c7f0000000

def z175 : W := mkw 0x23feb68d00000000 0x08ffada340000000 0xe3f83fee00000001 0x78fe0ffb80000000

def z176 : W := mkw 0x03a034a000800240 0x00e80d2800200090 0xf7e03fe0118007e3 0x7df80ff8046001f8

def z177 : W := mkw 0x00014870c085436c 0x0000521c302150db 0xbc0318f1c00307ff 0xef00c63c7000c1ff

def z178 : W := mkw 0x2bfffedfc0142d19 0x8affffb7f0050b46 0xe7ffffffc0003f1d 0xf9fffffff0000fc7

def z179 : W := mkw 0x03a0000039000000 0x00e800000e400000 0x9be7c0003f8fc002 0xe6f9f0000fe3f000

def z180 : W := mkw 0x0001485080000000 0x0000521420000000 0xa127d8f1c0000001 0xe849f63c70000000

def z181 : W := mkw 0x0314000230580811 0x00c500008c160204 0xcf1c201e307c381f 0xb3c708078c1f0e07

def z182 : W := mkw 0x23feb68d3d6a8000 0x08ffada34f5aa000 0x42d8270e2e700000 0x10b609c38b9c0000

def z183 : W := mkw 0x13a035803b003482 0x04e80d600ec00d20 0xd3e027003f803802 0x74f809c00fe00e00

def z184 : W := mkw 0x0b14000b705c0919 0x82c50002dc170246 0x8b1c001ff07c001e 0xa2c70007fc1f0007

def z185 : W := mkw 0x23ffca5d80000000 0x08fff29760000000 0x83ffc01fc0000000 0xe0fff007f0000000

def z186 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000000118fc002 0x060000000463f000

def z187 : W := mkw 0x0800300b705c2d19 0x82000c02dc170b46 0x4c00301ff07c3f1f 0x13000c07fc1f0fc7

def z188 : W := mkw 0x08000000704c2508 0x820000001c130942 0x00000000100c0700 0x00000000040301c0

def z189 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xfbffffffd18fc003 0xfefffffff463f000

def z190 : W := mkw 0x03ffc870fdefc36c 0x00fff21c3f7bf0db 0xbfffd8f1ffffc7ff 0xeffff63c7ffff1ff

def z191 : W := mkw 0x0bfff87bfdffef7d 0x82fffe1eff7ffbdf 0xfffff8ffffffffff 0xfffffe3fffffffff

def z192 : W := mkw 0x04000102021118b5 0x410000408084462d 0x04000000000038fc 0x0100000000000e3f

def z193 : W := mkw 0x27ffffdfbf7b98b5 0x49fffff7efdee62d 0xfffffffffffff8ff 0xfffffffffffffe3f

def z194 : W := mkw 0x13a035a03feab6c2 0x04e80d680ffaadb0 0xffe03fe03fffffe3 0x7ff80ff80ffffff8

def z195 : W := mkw 0x27ffffdf863318b5 0x49fffff7e18cc62d 0xffffffffee7338ff 0xfffffffffb9cce3f

def z196 : W := mkw 0x1000002039802642 0x040000080e600990 0x0000000011800700 0x00000000046001c0

def z197 : W := mkw 0x23feb68d00000000 0x08ffada340000000 0xc3ffe70e00000000 0xf0fff9c380000000

def z198 : W := mkw 0x23feb68d3d6a8000 0x08ffada34f5aa000 0xdbffe70e3fffc002 0xf6fff9c38ffff000

def z199 : W := mkw 0x23fffeddb9488000 0x08ffffb76e522000 0xe3ffffffd18cc001 0xf8fffffff4633000

def z200 : W := mkw 0x100005a0028012c2 0x0400016800a004b0 0x20000fe0000000e0 0x080003f800000038

def z201 : W := mkw 0x27feb78f06321891 0x49ffade3c18c8624 0x42d8270e2e703800 0x10b609c38b9c0e00

def z202 : W := mkw 0x0bfe800b7d7e8919 0x82ffa002df5fa246 0x9bffc01fffffc01e 0xe6fff007fffff007

def z203 : W := mkw 0x0000002000800240 0x0000000800200090 0x012010e011800700 0x00480438046001c0

def z204 : W := mkw 0x10017df0c28577ee 0x04005f7c30a15dfb 0xfd27fff1d18fffff 0xff49fffc7463ffff

def z205 : W := mkw 0x000000204085436c 0x00000008102150db 0x04000000000007fc 0x01000000000001ff

def z206 : W := mkw 0x00ea80000d228000 0x003aa0000348a000 0x9afbc0002ff3c002 0xe6bef0000bfcf000

def z207 : W := mkw 0x0300300070042508 0x00c00c001c010942 0xcf043011f00c3f1f 0xb3c10c047c030fc7

def z208 : W := mkw 0x044b0a1604330835 0x4112c285810cc20d 0xbc1b081e007300ff 0xef06c207801cc03f

def z209 : W := mkw 0x044a0102063318b5 0x41128040818cc62d 0x9edb00002e7338fe 0xe7b6c0000b9cce3f

def z210 : W := mkw 0x0001083000810264 0x0000420c00204099 0xbd2318f0118307ff 0xef48c63c0460c1ff

def z211 : W := mkw 0x0001487080814264 0x0000521c20205099 0x3023c8e00183c0e0 0x4c08f2380060f038

def z212 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x1ad800003fffc002 0x06b600000ffff000

def z213 : W := mkw 0x074b3b1636333cb5 0x41d2cec58d8ccf2d 0xffdb3f1e3e733fff 0xfff6cfc78f9ccfff

def z214 : W := mkw 0x204bca5480000000 0x0812f29520000000 0x0003c00000000000 0x0000f00000000000

def z215 : W := mkw 0x000000204085436c 0x00000008102150db 0xbd2018e0118fc7ff 0x6f4806380463f1ff

def z216 : W := mkw 0x27ffffdf86321891 0x49fffff7e18c8624 0xe3ffffffee703801 0xf8fffffffb9c0e00

def z217 : W := mkw 0x004b4870c4a7436c 0x0012d21c3129d0db 0xbfffd8f1ffffc7ff 0xeffff63c7ffff1ff

def z218 : W := mkw 0x0b5e300b747e2d19 0x82d78c02dd1f8b46 0xdfdf301ffe7f3f1f 0xf7f7cc07ff9fcfc7

def z219 : W := mkw 0x00ea800000000000 0x003aa00000000000 0x00e3c00000000000 0x4038f00000000000

def z220 : W := mkw 0x00014850c005412c 0x000052143001504b 0x9927c011d18fc01e 0xe649f0047463f007

def z221 : W := mkw 0x33fffffd828036c2 0x0cffffff60a00db0 0xe7ffffffc0003fe1 0xf9fffffff0000ff8

def z222 : W := mkw 0x33feb78d3b003482 0x0cffade34ec00d20 0x42d8270e2e003800 0x10b609c38b800e00

def z223 : W := mkw 0x0314000030480000 0x00c500000c120000 0x8b1c0000307c0002 0xa2c700000c1f0000

def z224 : W := mkw 0x0bb4348b705c2d19 0x82ed0d22dc170b46 0xeffc3ffff07c3f1f 0xfbff0ffffc1f0fc7

def z225 : W := mkw 0x23b4f4c9b9488000 0x08ed3d326e522000 0x0124d0e1d18cc000 0x0049343874633000

def z226 : W := mkw 0x33a17ffdbb8036c2 0x0ce85fff6ee00db0 0xf7e03fffff803fe3 0x7df80fffffe00ff8

def z227 : W := mkw 0x0314300900000000 0x00c50c0240000000 0xc31c301fc0000001 0xb0c70c07f0000000

def z228 : W := mkw 0x03feb0093d6a8000 0x00ffac024f5aa000 0xdbfff01fffffc003 0xf6fffc07fffff000

def z229 : W := mkw 0x005e80003d6a8000 0x0017a0000f5aa000 0x181fc0003fffc002 0x8607f0000ffff000

def z230 : W := mkw 0x00014850c005412c 0x000052143001504b 0x00000011c000001c 0x0000000470000007

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0xa12018e000000001 0x6848063800000000

def z232 : W := mkw 0x000000003d6a8000 0x000000000f5aa000 0x9927c0003fffc002 0xe649f0000ffff000

def z233 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x74c32f1e0e0338fd 0x5d30cbc78380ce3f

def z234 : W := mkw 0x13a001203b8036c2 0x04e800480ee00db0 0x97e000003f803fe2 0x65f800000fe00ff8

def z235 : W := mkw 0x0bfeb00b7d7ead19 0x82ffac02df5fab46 0xcfdc301ffe7c3f1f 0xb3f70c07ff9f0fc7

def z236 : W := mkw 0x23fffefdc085436c 0x08ffffbf702150db 0xffffffffd18fc7ff 0xfffffffff463f1ff

def z237 : W := mkw 0x0000000000000000 0x0000000000000000 0x92c000002e000002 0x64b000000b800000

def z238 : W := mkw 0x085e800b447e8919 0x8217a002d11fa246 0x081fc01fc07fc01c 0x8207f007f01ff007

def z239 : W := mkw 0x1b1435ab72dc3fdb 0x86c50d6adcb70ff6 0xef1c3ffff07c3fff 0xbbc70ffffc1f0fff

def z240 : W := mkw 0x044a030606321891 0x411280c1818c8624 0xdadb270e2e733802 0xf6b6c9c38b9cce00

def z241 : W := mkw 0x13a17df0bb8176e6 0x04e85f7c2ee05db9 0xf7e3ffe03f83ffe3 0x7df8fff80fe0fff8

def z242 : W := mkw 0x0c013b1f42153dbd 0xc3004ec7d0854f6f 0x64003f1fc0003ffd 0x19000fc7f0000fff

def z243 : W := mkw 0x0bb4b00b795cad19 0x82ed2c02de572b46 0xcf3cf01ff1fcff1f 0xb3cf3c07fc7f3fc7

def z244 : W := mkw 0x00014872c0954b7d 0x0000521cb02552df 0xff3ff8fff1ffffff 0xffcffe3ffc7fffff

def z245 : W := mkw 0x03b4348900000000 0x00ed0d2240000000 0xe3fc3fffc0000001 0xf8ff0ffff0000000

def z246 : W := mkw 0x30017ffd828036c2 0x0c005fff60a00db0 0x64003fffc0003fe1 0x19000ffff0000ff8

def z247 : W := mkw 0x0000000000000000 0x0000000000000000 0x0807c000000fc000 0x8201f0000003f000

def z248 : W := mkw 0x23b4b48900000000 0x08ed2d2240000000 0x0000000000000000 0x0000000000000000

def z249 : W := mkw 0x03fe800000000000 0x00ffa00000000000 0x9bffc000118fc002 0xe6fff0000463f000

def z250 : W := mkw 0x00ea80003d6a8000 0x003aa0000f5aa000 0x18e3c0003fffc002 0x4638f0000ffff000

def z251 : W := mkw 0x044b0b16463719bd 0x4112c2c5918dc66f 0xffdf3f1ffe7f3fff 0xfff7cfc7ff9fcfff

def z252 : W := mkw 0x20ebcef480814264 0x083af3bd20205099 0x30e3cfe00183c0e0 0x4c38f3f80060f038

def z253 : W := mkw 0x044b0a1604330835 0x4112c285810cc20d 0xeadb2f1e0073001d 0xfab6cbc7801cc007

def z254 : W := mkw 0x27ffffdf821118b5 0x49fffff7e084462d 0xe7ffffffc00038fd 0xf9fffffff0000e3f

def z255 : W := mkw 0x0b14310b725c3d99 0x82c50c42dc970f66 0xffdc3f1ffe7c3fff 0xfff70fc7ff9f0fff

def z256 : W := mkw 0x0b14300b30582c11 0x82c50c02cc160b04 0xcb1c200e307c3802 0xb2c708038c1f0e00

def z257 : W := mkw 0x0014800000488000 0x0005200000122000 0x0004c000000cc000 0x0001300000033000

def z258 : W := mkw 0x044b0b163f7b98b5 0x4112c2c58fdee62d 0xfedb2f1e3ffff8ff 0xffb6cbc78ffffe3f

def z259 : W := mkw 0x285fca5fc05c0919 0x8a17f297f0170246 0x081fc01fc07c001c 0x8207f007f01f0007

def z260 : W := mkw 0x205fca5dc005412c 0x0817f2977001504b 0x081fc01fc00fc01c 0x8207f007f003f007

def z261 : W := mkw 0x100035a03b8036c2 0x04000d680ee00db0 0x74003fe03f803fe3 0x1d000ff80fe00ff8

def z262 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x83ffc0002e700000 0xe0fff0000b9c0000

def z263 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x31e01fe01f8007e0 0x4c7807f807e001f8

def z264 : W := mkw 0x10a004a009800242 0x0428012802600090 0x002000e001800000 0x0008003800600000

def z265 : W := mkw 0x004a000004220000 0x0012800001088000 0x9bffc0003fffc002 0xe6fff0000ffff000

def z266 : W := mkw 0x04010b16021118b5 0x410042c58084462d 0xee182f1e207038ff 0xbb860bc7881c0e3f

def z267 : W := mkw 0x005e800000000000 0x0017a00000000000 0x001fc00000000000 0x8007f00000000000

def z268 : W := mkw 0x205fca5d846a8000 0x0817f297611aa000 0x081fc01fc07fc000 0x8207f007f01ff000

def z269 : W := mkw 0x23fffeddb0002400 0x08ffffb76c000900 0xe7fffffff0003f03 0xf9fffffffc000fc0

def z270 : W := mkw 0x245fcb5f863318b5 0x4917f2d7e18cc62d 0xfedfef1fee7338ff 0xffb7fbc7fb9cce3f

def z271 : W := mkw 0x0b15785bf05d6d3d 0x82c55e16fc175b4f 0xcf1ff01ff07fff1f 0xb3c7fc07fc1fffc7

def z272 : W := mkw 0x07fe81023f7b98b5 0x41ffa0408fdee62d 0x9fffc0003ffff8fe 0xe7fff0000ffffe3f

def z273 : W := mkw 0x33b4f5e9bb8036c2 0x0ced3d7a6ee00db0 0xf7e4ffe1ff803fe3 0x7df93ff87fe00ff8

def z274 : W := mkw 0x044b4b56863318b5 0x4112d2d5a18cc62d 0xffffffffee7338ff 0xfffffffffb9cce3f

def z275 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x56c027003f803fe2 0x15b009c00fe00ff8

def z276 : W := mkw 0x2bfeb68f705c2d19 0x8affada3dc170b46 0xcfdc371ff07c3f1f 0xb3f70dc7fc1f0fc7

def z277 : W := mkw 0x004a000204320811 0x00128000810c8204 0xdedb201e2e73381f 0xf7b6c8078b9cce07

def z278 : W := mkw 0x044b4b56c63759bd 0x4112d2d5b18dd66f 0xfedfef1fee7ff8ff 0xffb7fbc7fb9ffe3f

def z279 : W := mkw 0x20017efdc085436c 0x08005fbf702150db 0xfd27ffffd18fc7ff 0xff49fffff463f1ff

def z280 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x72db2f0e2e7338e0 0x5cb6cbc38b9cce38

def z281 : W := mkw 0x00ea80000d228000 0x003aa0000348a000 0x99e7c0001f8fc002 0xe679f00007e3f000

def z282 : W := mkw 0x0800000240142d19 0x8200000090050b46 0x0400000000003f1c 0x0100000000000fc7

def z283 : W := mkw 0x00000000046a8000 0x00000000011aa000 0x08000000007fc000 0x02000000001ff000

def z284 : W := mkw 0x0bfeb00b705c2d19 0x82ffac02dc170b46 0xcffff01ff07c3f1f 0xf3fffc07fc1f0fc7

def z285 : W := mkw 0x23fffeddbd6a8000 0x08ffffb76f5aa000 0xe3ffffffee700001 0xf8fffffffb9c0000

def z286 : W := mkw 0x035f3a1d00000000 0x00d7ce8740000000 0xe3df3f1fc0000001 0xf8f7cfc7f0000000

def z287 : W := mkw 0x0000000000000000 0x0000000000000000 0x89040000100c0002 0xa241000004030000

def z288 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x2524d8f1d18cc7fd 0x0949363c746331ff

def z289 : W := mkw 0x004a000004220000 0x0012800001088000 0x081b000000730000 0x8206c000001cc000

def z290 : W := mkw 0x20ebced480000000 0x083af3b520000000 0xe2fbeffe00000001 0xf8befbff80000000

def z291 : W := mkw 0x0814000b705c2d19 0x82050002dc170b46 0x0c1c001ff07c3f1e 0x83070007fc1f0fc7

def z292 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x4e18200e307c3f1e 0x138608038c1f0fc7

def z293 : W := mkw 0x03a0000000000000 0x00e8000000000000 0x83e0000000000000 0x60f8000000000000

def z294 : W := mkw 0x100001203feab6c2 0x040000480ffaadb0 0x1c0000003fffffe2 0x070000000ffffff8

def z295 : W := mkw 0x23fef4c980000000 0x08ffbd3260000000 0x83ffd0e1c0000000 0xe0fff43870000000

def z296 : W := mkw 0x044b0b16021118b5 0x4112c2c58084462d 0xe6db2f1e000038fd 0xf9b6cbc780000e3f

def z297 : W := mkw 0x031400003d6a8000 0x00c500000f5aa000 0x9b1c00003fffc002 0xa6c700000ffff000

def z298 : W := mkw 0x1bfeb5ab7ffebfdb 0x86ffad6adfffaff6 0xffffffffffffffff 0xffffffffffffffff

def z299 : W := mkw 0x100001200b8012c2 0x0400004802e004b0 0x100000000f8000e0 0x0400000003e00038

def z300 : W := mkw 0x23fffedd84220000 0x08ffffb761088000 0xfbffffffee730003 0xfefffffffb9cc000

def z301 : W := mkw 0x27ffffdd862310a4 0x49fffff76188c429 0xf3ffffffce0300e1 0xfcfffffff380c038

def z302 : W := mkw 0x30ebcff48b8012c2 0x0c3af3fd22e004b0 0x30e3cfe00f8000e0 0x4c38f3f803e00038

def z303 : W := mkw 0x03ffc85080000000 0x00fff21420000000 0xa3ffd8f1c0000001 0xe8fff63c70000000

def z304 : W := mkw 0x13a17df0bb8036c2 0x04e85f7c2ee00db0 0xf7e7fff1ff803fe3 0xfdf9fffc7fe00ff8

def z305 : W := mkw 0x0314000030480000 0x00c500000c120000 0x01040000100c0000 0x0041000004030000

def z306 : W := mkw 0x1ba035ab7b943fdb 0x86e80d6adee50ff6 0xf7e03fffff803fff 0x7df80fffffe00fff

def z307 : W := mkw 0x0000000200100811 0x0000000080040204 0x0c0000002070381e 0x03000000081c0e07

def z308 : W := mkw 0x20017edd80000000 0x08005fb760000000 0xe127ffffc0000001 0xf849fffff0000000

def z309 : W := mkw 0x100001203b8036c2 0x040000480ee00db0 0xf6c02f003f803fe3 0x7db00bc00fe00ff8

def z310 : W := mkw 0x044b0a1604330835 0x4112c285810cc20d 0xce1b201e2073381f 0xb386c807881cce07

def z311 : W := mkw 0x13b435a03bc836c2 0x04ed0d680ef20db0 0xfffc3fe03ffc3fe3 0xffff0ff80fff0ff8

def z312 : W := mkw 0x0b5eb00b747ead19 0x82d7ac02dd1fab46 0xcf1ff01ff07fff1f 0xb3c7fc07fc1fffc7

def z313 : W := mkw 0x03140000704c0108 0x00c500001c130042 0x8f1c1011f07c071f 0xa3c704047c1f01c7

def z314 : W := mkw 0x0bb4300b795c2d19 0x82ed0c02de570b46 0xdffc301ffffc3f1f 0xf7ff0c07ffff0fc7

def z315 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x03fcc0003ffcc000 0x00ff30000fff3000

def z316 : W := mkw 0x08000002705c2d19 0x820000009c170b46 0x8d041011f07c3f1f 0xa34104047c1f0fc7

def z317 : W := mkw 0x03fe800004220000 0x00ffa00001088000 0x9bffc0002e730002 0xe6fff0000b9cc000

def z318 : W := mkw 0x00ebc8708da3c264 0x003af21c2368f099 0x30e3c8e00f83c0e0 0x4c38f23803e0f038

def z319 : W := mkw 0x20ebced48d228000 0x083af3b52348a000 0x30e3cfe00f83c000 0x4c38f3f803e0f000

def z320 : W := mkw 0x0c5f0b1f467f19bd 0xc317c2c7d19fc66f 0xfedf2f1fee7f38ff 0xffb7cbc7fb9fce3f

def z321 : W := mkw 0x23feb68d00000000 0x08ffada340000000 0xc3dc371fc0000001 0xb0f70dc7f0000000

def z322 : W := mkw 0x04eb8b160f3398b5 0x413ae2c583cce62d 0xfefbef1e2ff3f8ff 0xffbefbc78bfcfe3f

def z323 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x3c0018f1d18fc7ff 0x0f00063c7463f1ff

def z324 : W := mkw 0x04000100062310a4 0x410000400188c429 0x100000000e0300e0 0x040000000380c038

def z325 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x43e037e03f803f00 0x10f80df80fe00fc0

def z326 : W := mkw 0x0800300940042508 0x82000c0250010942 0x00001001c0000700 0x00000400700001c0

def z327 : W := mkw 0x03a0348000000000 0x00e80d2000000000 0x012010e000000000 0x0048043800000000

def z328 : W := mkw 0x10a14df0cb8553ee 0x0428537c32e154fb 0xbde7dff1df8fc7ff 0xef79f7fc77e3f1ff

def z329 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x0adfc0002e7fc000 0x82b7f0000b9ff000

def z330 : W := mkw 0x0001485080000000 0x0000521420000000 0xb927d8f1d18fc003 0xee49f63c7463f000

def z331 : W := mkw 0x0314300930480000 0x00c50c024c120000 0xcb1c301ff07c0003 0xb2c70c07fc1f0000

def z332 : W := mkw 0x03feb0003d6aa400 0x00ffac000f5aa900 0xdffff0003fffff03 0xf7fffc000fffffc0

def z333 : W := mkw 0x0800000230582c11 0x820000008c160b04 0x0000000020703800 0x00000000081c0e00

def z334 : W := mkw 0x0300310032003480 0x00c00c400c800d20 0xf7c03f003e003fe3 0x7df00fc00f800ff8

def z335 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x152010e03f803fe2 0x054804380fe00ff8

def z336 : W := mkw 0x14eb0fb60fb31af7 0x453ac3ed83ecc6bd 0xfefb2ffe2ff338ff 0xffbecbff8bfcce3f

def z337 : W := mkw 0x0314000000000000 0x00c5000000000000 0x831c000000000000 0xa0c7000000000000

def z338 : W := mkw 0x33fffffdbfeab6c2 0x0cffffff6ffaadb0 0xffffffffffffffe3 0xfffffffffffffff8

def z339 : W := mkw 0x20a0c4c080000000 0x0828313020000000 0x0020c0e000000000 0x0008303800000000

def z340 : W := mkw 0x000000004005412c 0x000000001001504b 0x08000000000fc01c 0x020000000003f007

def z341 : W := mkw 0x0b14300b30582c11 0x82c50c02cc160b04 0xc31c301fe0703801 0xb0c70c07f81c0e00

def z342 : W := mkw 0x0c000102767f3dbd 0xc30000409d9fcf6f 0x1c0000003e7f3ffe 0x070000000f9fcfff

def z343 : W := mkw 0x0001485080000000 0x0000521420000000 0x200018f1c0000001 0x0800063c70000000

def z344 : W := mkw 0x0000000039488000 0x000000000e522000 0x00000000118cc000 0x0000000004633000

def z345 : W := mkw 0x205fca7dc085436c 0x0817f29f702150db 0xbd3fd8ffd18fc7ff 0xef4ff63ff463f1ff

def z346 : W := mkw 0x03ffc850bd6a8000 0x00fff2142f5aa000 0xbbffd8f1ffffc003 0xeefff63c7ffff000

def z347 : W := mkw 0x03feb00900000000 0x00ffac0240000000 0xc3fff01fc0000001 0xf0fffc07f0000000

def z348 : W := mkw 0x0000000200100811 0x0000000080040204 0x0818001e0070001c 0x82060007801c0007

def z349 : W := mkw 0x08014872f0dd6f7d 0x8200521cbc375bdf 0xbd27d8f1f1ffffff 0xef49f63c7c7fffff

def z350 : W := mkw 0x0bfe80027d7ead19 0x82ffa0009f5fab46 0x9fffc0003fffff1e 0xe7fff0000fffffc7

def z351 : W := mkw 0x205fca5d80000000 0x0817f29760000000 0xa13fd8ffc0000001 0xe84ff63ff0000000

def z352 : W := mkw 0x044b0b3646b75bfd 0x4112c2cd91add6ff 0xfedb2f1e3fffffff 0xffb6cbc78fffffff

def z353 : W := mkw 0x03a001003b001080 0x00e800400ec00420 0xf7e02f003f8038e3 0x7df80bc00fe00e38

def z354 : W := mkw 0x0b15787bf0dd6f7d 0x82c55e1efc375bdf 0xef1c38fff07c3fff 0xbbc70e3ffc1f0fff

def z355 : W := mkw 0x23b4f4c980000000 0x08ed3d3260000000 0xe3e4ffe1c0000001 0x78f93ff870000000

def z356 : W := mkw 0x2bfffedfc05c0919 0x8affffb7f0170246 0xebffffffc07c001d 0xfafffffff01f0007

def z357 : W := mkw 0x13feb4a03deaa642 0x04ffad280f7aa990 0x9bffd0e03fffc702 0xe6fff4380ffff1c0

def z358 : W := mkw 0x0000002000800240 0x0000000800200090 0x14000000118007e2 0x05000000046001f8

def z359 : W := mkw 0x17a035a23fb33ef7 0x45e80d688feccfbd 0xffe03fe03ff33fff 0x7ff80ff80ffccfff

def z360 : W := mkw 0x0c4b3b1f46373dbd 0xc312cec7d18dcf6f 0xfedb3f1fee733fff 0xffb6cfc7fb9ccfff

def z361 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x3c23c8e0118fc7fe 0x4f08f2380463f1ff

def z362 : W := mkw 0x2bfffeddf04c2508 0x8affffb77c130942 0xe3ffffffd00c0701 0xf8fffffff40301c0

def z363 : W := mkw 0x20017efdc085436c 0x08005fbf702150db 0x64003fffc00007fd 0x19000ffff00001ff

def z364 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x2c07d8f1c00fc7fd 0x8b01f63c7003f1ff

def z365 : W := mkw 0x100001203b8036c2 0x040000480ee00db0 0xb52018e03f803fe3 0x6d4806380fe00ff8

def z366 : W := mkw 0x0000000000000000 0x0000000000000000 0x8a18000020700002 0xa2860000081c0000

def z367 : W := mkw 0x00a0048000000000 0x0028012000000000 0x20e00fe000000000 0x483803f800000000

def z368 : W := mkw 0x0000000240140919 0x0000000090050246 0xcf1c301ff07c3f1f 0xb3c70c07fc1f0fc7

def z369 : W := mkw 0x10a005a00b8012c2 0x0428016802e004b0 0xf6e02fe02f8038e3 0x7db80bf80be00e38

def z370 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z371 : W := mkw 0x0300000030000000 0x00c000000c000000 0x8300000030000002 0x20c000000c000000

def z372 : W := mkw 0x004b0a1404220000 0x0012c28501088000 0xfadb2f1e2e730003 0xfeb6cbc78b9cc000

def z373 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x4504301fd00c3f1d 0x11410c07f4030fc7

def z374 : W := mkw 0x0000000040040108 0x0000000010010042 0x0c000000100c071e 0x03000000040301c7

def z375 : W := mkw 0x03a17cd080000000 0x00e85f3420000000 0xe3e7fff1c0000001 0xf8f9fffc70000000

def z376 : W := mkw 0x004a000004220000 0x0012800001088000 0x10c300000e030000 0x4430c0000380c000

def z377 : W := mkw 0x07ff8a163d7b8835 0x41ffe2858f5ee20d 0x9bffc01e3fffc01e 0xe6fff0078ffff007

def z378 : W := mkw 0x004b0a1600100811 0x0012c28580040204 0xeedb2f1e2070381f 0xfbb6cbc7881c0e07

def z379 : W := mkw 0x13a035a07b8577ee 0x04e80d681ee15dfb 0xffe03fe03f8fffff 0x7ff80ff80fe3ffff

def z380 : W := mkw 0x23fffeddb9000000 0x08ffffb76e400000 0xf3ffffffff800003 0xfcffffffffe00000

def z381 : W := mkw 0x0b14300b30582c11 0x82c50c02cc160b04 0xce18201e2070381f 0xb3860807881c0e07

def z382 : W := mkw 0x0314000030480000 0x00c500000c120000 0x9b3fc00031ffc002 0xe6cff0000c7ff000

def z383 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xdf3ff01ff1ffff1f 0xf7cffc07fc7fffc7

def z384 : W := mkw 0x045f8a16047b8835 0x4117e285811ee20d 0x081fc01e007fc01c 0x8207f007801ff007

def z385 : W := mkw 0x00004060c085436c 0x00001018302150db 0x1d24d0e1d18fc7fe 0x074934387463f1ff

def z386 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x62d83fffc0000001 0x18b60ffff0000000

def z387 : W := mkw 0x0000406080804240 0x0000101820201090 0x0020c0e00180c000 0x0008303800603000

def z388 : W := mkw 0x0000000030480000 0x000000000c120000 0x08000000307c0002 0x020000000c1f0000

def z389 : W := mkw 0x00ebc870cda7c36c 0x003af21c3369f0db 0xbde7d8f1df8fc7ff 0xef79f63c77e3f1ff

def z390 : W := mkw 0x03b4800039488000 0x00ed20000e522000 0x93e4c0003f8cc002 0x64f930000fe33000

def z391 : W := mkw 0x20ffcedd80000000 0x083ff3b760000000 0x20ffcfffc0000000 0xc83ff3fff0000000

def z392 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xffffef1e3ffff8ff 0xfffffbc78ffffe3f

def z393 : W := mkw 0x03b4800039488000 0x00ed20000e522000 0x9927c000118fc002 0xe649f0000463f000

def z394 : W := mkw 0x00014850c005412c 0x000052143001504b 0x8d07d011d00fc71f 0xa341f4047403f1c7

def z395 : W := mkw 0x0314000030480000 0x00c500000c120000 0x0218000020700000 0x00860000081c0000

def z396 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x431c300ff07c3f00 0x10c70c03fc1f0fc0

def z397 : W := mkw 0x0b140002705c2d19 0x82c500009c170b46 0x8f1c0000307c3f1e 0xa3c700000c1f0fc7

def z398 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x3127d8e1d18fc7e0 0x4c49f6387463f1f8

def z399 : W := mkw 0x13a034a039802642 0x04e80d280e600990 0xe3e03fe011800701 0x78f80ff8046001c0

def z400 : W := mkw 0x03fe800039000000 0x00ffa0000e400000 0x93ffc0003f800002 0xe4fff0000fe00000

def z401 : W := mkw 0x03017870f085676c 0x00c05e1c3c2159db 0xff27f8f1f18fffff 0xffc9fe3c7c63ffff

def z402 : W := mkw 0x03ff88103d6b8024 0x00ffe2040f5ae009 0xbfffc8103fffc0ff 0xeffff2040ffff03f

def z403 : W := mkw 0x23fffefdc0844348 0x08ffffbf702110d2 0xe3ffffffd18cc701 0xf8fffffff46331c0

def z404 : W := mkw 0x00014870c085436c 0x0000521c302150db 0xad0418f1d00c07ff 0xab41063c740301ff

def z405 : W := mkw 0x0000002040844348 0x00000008102110d2 0x00000000118cc700 0x00000000046331c0

def z406 : W := mkw 0x040001023f7b98b5 0x410000408fdee62d 0x1c0000003ffff8fe 0x070000000ffffe3f

def z407 : W := mkw 0x03b4800039488000 0x00ed20000e522000 0x0000000000000000 0x0000000000000000

def z408 : W := mkw 0x044a020604320811 0x41128081810c8204 0x0018000e00700000 0x00060003801c0000

def z409 : W := mkw 0x03a000003d6a8000 0x00e800000f5aa000 0x9be000003fffc002 0x66f800000ffff000

def z410 : W := mkw 0x205e820d00000000 0x0817a08340000000 0x0018000e00000000 0x0006000380000000

def z411 : W := mkw 0x0314300940040108 0x00c50c0250010042 0xcf1c301fd00c071f 0xb3c70c07f40301c7

def z412 : W := mkw 0x0814000b405c0919 0x82050002d0170246 0xce1c201fe07c381f 0xb3870807f81f0e07

def z413 : W := mkw 0x000108304085436c 0x0000420c102150db 0xbc030810118fc7ff 0xef00c2040463f1ff

def z414 : W := mkw 0x044b0b14062310a4 0x4112c2c50188c429 0xf2db2f1e0e0300e1 0xfcb6cbc78380c038

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c0000100000001f 0xa300000400000007

def z416 : W := mkw 0x13a035803b003482 0x04e80d600ec00d20 0xc7c037003e003f03 0x31f00dc00f800fc0

def z417 : W := mkw 0x0f5f3a1f747f2d3d 0xc3d7ce87dd1fcb4f 0xcf1f301ff07f3f1f 0xb3c7cc07fc1fcfc7

def z418 : W := mkw 0x03a0348000000000 0x00e80d2000000000 0x42c0270000000000 0x10b009c000000000

def z419 : W := mkw 0x044b0a1604330835 0x4112c285810cc20d 0x9adb001e2e73001e 0xe6b6c0078b9cc007

def z420 : W := mkw 0x03ea00003d220000 0x00fa80000f488000 0x9bfb00003ff30002 0xe6fec0000ffcc000

def z421 : W := mkw 0x0000000040040108 0x0000000010010042 0x01041001d00c0700 0x00410400740301c0

def z422 : W := mkw 0x044b0b14062310a4 0x4112c2c50188c429 0xbcc30f100e0300ff 0xef30c3c40380c03f

def z423 : W := mkw 0x004b0a1400010024 0x0012c28500004009 0xfedb2f1e000300ff 0xffb6cbc78000c03f

def z424 : W := mkw 0x13fffdf0ffeff7ee 0x04ffff7c3ffbfdfb 0xfffffff1ffffffff 0xfffffffc7fffffff

def z425 : W := mkw 0x23fffedd8d228000 0x08ffffb76348a000 0xf3ffffffcf83c001 0xfcfffffff3e0f000

def z426 : W := mkw 0x180035ab42943fdb 0x86000d6ad0a50ff6 0x64003fffc0003ffd 0x19000ffff0000fff

def z427 : W := mkw 0x0014000900000000 0x0005000240000000 0x001c001fc0000000 0x80070007f0000000

def z428 : W := mkw 0x0b143009704c2508 0x82c50c025c130942 0x8d041011d00c071f 0xa3410404740301c7

def z429 : W := mkw 0x0800002270dd6f7d 0x820000089c375bdf 0x1c00000031fffffe 0x070000000c7fffff

def z430 : W := mkw 0x0000010002001080 0x0000004000800420 0x64002f00000038e1 0x19000bc000000e38

def z431 : W := mkw 0x04010a1600110835 0x410042858004420d 0x0000001e0000001c 0x0000000780000007

def z432 : W := mkw 0x000108104005012c 0x000042041001404b 0xbd071811d00f07ff 0xef41c6047403c1ff

def z433 : W := mkw 0x044b4b76c6b75bfd 0x4112d2ddb1add6ff 0xfedb3fffee733fff 0xffb6cffffb9ccfff

def z434 : W := mkw 0x0001081000000000 0x0000420400000000 0xa003081000000001 0xe800c20400000000

def z435 : W := mkw 0x0001487080814264 0x0000521c20205099 0xb927c8e0118fc0e2 0xee49f2380463f038

def z436 : W := mkw 0x13a17df0fb8577ee 0x04e85f7c3ee15dfb 0xf7e03ff1ff803fff 0x7df80ffc7fe00fff

def z437 : W := mkw 0x0001485080014024 0x0000521420005009 0x0003c0000003c000 0x0000f0000000f000

def z438 : W := mkw 0x004a010006221080 0x0012804001888420 0xfedb2f002e7338e3 0xffb6cbc00b9cce38

def z439 : W := mkw 0x144b3fb606b33ef7 0x4512cfed81accfbd 0xfedb3ffe2e733fff 0xffb6cfff8b9ccfff

def z440 : W := mkw 0x235ffa5d80000000 0x08d7fe9760000000 0xc31ff01fc0000001 0xb0c7fc07f0000000

def z441 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x8bdc00003e7c0002 0xa2f700000f9f0000

def z442 : W := mkw 0x0f5f3b1f367b3cb5 0xc3d7cec7cd9ecf2d 0xfedb2f1e2e7338ff 0xffb6cbc78b9cce3f

def z443 : W := mkw 0x04000102063318b5 0x41000040818cc62d 0xfec02f002e7338ff 0x7fb00bc00b9cce3f

def z444 : W := mkw 0x0001487080814264 0x0000521c20205099 0x200008e0000000e0 0x0800023800000038

def z445 : W := mkw 0x004b0b1402001080 0x0012c2c500800420 0xf6db2f1e2e0038e3 0xfdb6cbc78b800e38

def z446 : W := mkw 0x0b14300930482400 0x82c50c024c120900 0x0000000000000000 0x0000000000000000

def z447 : W := mkw 0x0000300900000000 0x00000c0240000000 0x4000301fc0000001 0x10000c07f0000000

def z448 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x0927d0f1d18fc71c 0x8249f43c7463f1c7

def z449 : W := mkw 0x17eb7ff6ffb77fff 0x45fadffdbfeddfff 0xffffffffffffffff 0xffffffffffffffff

def z450 : W := mkw 0x000000204085436c 0x00000008102150db 0x9d041011d18fc7ff 0xa74104047463f1ff

def z451 : W := mkw 0x0000000000010024 0x0000000000004009 0x1c000000000300fe 0x070000000000c03f

def z452 : W := mkw 0x0000300000002400 0x00000c0000000900 0x4400300000003f01 0x11000c0000000fc0

def z453 : W := mkw 0x03a0002039800240 0x00e800080e600090 0xb7e018e03f8007e3 0x6df806380fe001f8

def z454 : W := mkw 0x13a035a07b8437ca 0x04e80d681ee10df2 0xffe43ff1ff8c3fff 0xfff90ffc7fe30fff

def z455 : W := mkw 0x03ffc870bdebc264 0x00fff21c2f7af099 0xbbffc8e03fffc0e2 0xeefff2380ffff038

def z456 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x3cc30f002e7338fe 0x4f30c3c00b9cce3f

def z457 : W := mkw 0x0f153b1f725d3dbd 0xc3c54ec7dc974f6f 0xef1c3f1ff07c3fff 0xbbc70fc7fc1f0fff

def z458 : W := mkw 0x0b143009704c2508 0x82c50c025c130942 0x8b1c1001f07c0702 0xa2c704007c1f01c0

def z459 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x21e7dfe1c0000000 0x4879f7f870000000

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x9120000011800002 0x6448000004600000

def z461 : W := mkw 0x07ff8b163f7b98b5 0x41ffe2c58fdee62d 0xfedb2f1e2e7338ff 0xffb6cbc78b9cce3f

def z462 : W := mkw 0x3bfffffffbdc3fdb 0x8efffffffef70ff6 0xfffffffffffc3fff 0xffffffffffff0fff

def z463 : W := mkw 0x004a000000000000 0x0012800000000000 0x82db000000000000 0xe0b6c00000000000

def z464 : W := mkw 0x0001081000010024 0x0000420400004009 0x30030800000300e0 0x4c00c2000000c038

def z465 : W := mkw 0x0000000000000000 0x0000000000000000 0x81041011c0000001 0xa041040470000000

def z466 : W := mkw 0x0315785980000000 0x00c55e1660000000 0xe33ff8ffc0000001 0xf8cffe3ff0000000

def z467 : W := mkw 0x1bb434ab79dc2f5b 0x86ed0d2ade770bd6 0xcf3c30fff1fc3f1f 0xb3cf0c3ffc7f0fc7

def z468 : W := mkw 0x00014850c005412c 0x000052143001504b 0xa927d8f1c00fc01d 0xea49f63c7003f007

def z469 : W := mkw 0x00000120028012c0 0x0000004800a004b0 0xf7e03fe03f803fe3 0x7df80ff80fe00ff8

def z470 : W := mkw 0x044b0b14062310a4 0x4112c2c50188c429 0xbadb0f002e7300e2 0xeeb6c3c00b9cc038

def z471 : W := mkw 0x0fffbb1f7f7fbdbd 0xc3ffeec7dfdfef6f 0xffffff1fffffffff 0xffffffc7ffffffff

def z472 : W := mkw 0x13a034a039802642 0x04e80d280e600990 0xc72030e031803f03 0x31c80c380c600fc0

def z473 : W := mkw 0x0b14302b70dc2f59 0x82c50c0adc370bd6 0xff3c38fff1fc3fff 0xffcf0e3ffc7f0fff

def z474 : W := mkw 0x17ffbfb63ffbbef7 0x45ffefed8ffeefbd 0xfffffffe3fffffff 0xffffffff8fffffff

def z475 : W := mkw 0x13a005a03b8012c2 0x04e801680ee004b0 0xb3e00fe03f8000e2 0x6cf803f80fe00038

def z476 : W := mkw 0x0314300b00100811 0x00c50c02c0040204 0xcf1c301fe070381f 0xb3c70c07f81c0e07

def z477 : W := mkw 0x2bfffefff0dd6f7d 0x8affffbffc375bdf 0xfffffffff1ffffff 0xfffffffffc7fffff

def z478 : W := mkw 0x04010b14020110a4 0x410042c500804429 0x20000f00000000e0 0x080003c000000038

def z479 : W := mkw 0x03a0358002001080 0x00e80d6000800420 0xf7e03fe02e0038e3 0x7df80ff80b800e38

def z480 : W := mkw 0x0000002000814264 0x0000000800205099 0x100000000183c0e0 0x040000000060f038

def z481 : W := mkw 0x13a035a0028036c2 0x04e80d6800a00db0 0xe7e03fe000003fe1 0x79f80ff800000ff8

def z482 : W := mkw 0x2b5ffa5ff05c2d19 0x8ad7fe97fc170b46 0xcf1ff01ff07c3f1f 0xb3c7fc07fc1f0fc7

def z483 : W := mkw 0x04010912063318b5 0x41004244818cc62d 0xbc0308102e7338ff 0xef00c2040b9cce3f

def z484 : W := mkw 0x17a13fb63b913ef7 0x45e84fed8ee44fbd 0xf7e03ffe3f803fff 0x7df80fff8fe00fff

def z485 : W := mkw 0x005e8000046a8000 0x0017a000011aa000 0x9adfc0002e7fc002 0xe6b7f0000b9ff000

def z486 : W := mkw 0x000000204085436c 0x00000008102150db 0x9d27c000118fc7fe 0xe749f0000463f1ff

def z487 : W := mkw 0x005e8000046a8000 0x0017a000011aa000 0x0018000000700000 0x00060000001c0000

def z488 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x093fc00011ffc000 0x824ff000047ff000

def z489 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x013fd0ffc0000000 0x804ff43ff0000000

def z490 : W := mkw 0x0001487080800240 0x0000521c20200090 0xb527d8f1d18007e3 0xed49f63c746001f8

def z491 : W := mkw 0x00a0000009000000 0x0028000002400000 0x10e000000f800000 0x4438000003e00000

def z492 : W := mkw 0x0000010002001080 0x0000004000800420 0x140000002e0038e2 0x050000000b800e38

def z493 : W := mkw 0x00004060c0844348 0x00001018302110d2 0xb524d8e1d18cc7e3 0x6d493638746331f8

def z494 : W := mkw 0x0400012246b75bfd 0x4100004891add6ff 0x1c0000003ffffffe 0x070000000fffffff

def z495 : W := mkw 0x13a074e0f984674a 0x04e81d383e6119d2 0x0124d0e1d18cc700 0x00493438746331c0

def z496 : W := mkw 0x0014000000480000 0x0005000000120000 0x081c0000007c0000 0x82070000001f0000

def z497 : W := mkw 0x03eb3e9400000000 0x00facfa500000000 0xe3fb3ffe00000001 0xf8fecfff80000000

def z498 : W := mkw 0x0001081000010024 0x0000420400004009 0x080300100003001c 0x8200c0040000c007

def z499 : W := mkw 0x0000000030002400 0x000000000c000900 0x0400000030003f02 0x010000000c000fc0

def z500 : W := mkw 0x13b435a93b8036c2 0x04ed0d6a4ee00db0 0xf7fc3fffff803fe3 0xfdff0fffffe00ff8

def z501 : W := mkw 0x130031203b8036c2 0x04c00c480ee00db0 0xd70030003f803fe3 0x35c00c000fe00ff8

def z502 : W := mkw 0x0314300900000000 0x00c50c0240000000 0x4218200e00000000 0x1086080380000000

def z503 : W := mkw 0x0000348000000000 0x00000d2000000000 0x60003fe000000001 0x18000ff800000000

def z504 : W := mkw 0x2bfeb68f30582c11 0x8affada3cc160b04 0x42d8270e20703800 0x10b609c3881c0e00

def z505 : W := mkw 0x03a0348030002400 0x00e80d200c000900 0xe7e03fe030003f03 0x79f80ff80c000fc0

def z506 : W := mkw 0x1bb4358b7b5c3d9b 0x86ed0d62ded70f66 0xcfdc371ffe7c3f1f 0xb3f70dc7ff9f0fc7

def z507 : W := mkw 0x100001003b003482 0x040000400ec00d20 0x000000002e003800 0x000000000b800e00

def z508 : W := mkw 0x03154870f0cd436c 0x00c5521c3c3350db 0xbf3fd8f1f1ffc7ff 0xefcff63c7c7ff1ff

def z509 : W := mkw 0x0f5e330f367a3c91 0xc3d78cc3cd9e8f24 0x42d8270e2e703800 0x10b609c38b9c0e00

def z510 : W := mkw 0x044b4a76c4b74b7d 0x4112d29db12dd2df 0xbd3fd8ffd1ffc7ff 0xef4ff63ff47ff1ff

def z511 : W := mkw 0x00014850c0040108 0x0000521430010042 0xad27d8f1d00c071f 0xeb49f63c740301c7

def z512 : W := mkw 0x0b14300b405c0919 0x82c50c02d0170246 0xcb1c301fc07c001d 0xb2c70c07f01f0007

def z513 : W := mkw 0x23b4f4e9c0844348 0x08ed3d3a702110d2 0x0124d0e1d18cc700 0x00493438746331c0

def z514 : W := mkw 0x04010b16021118b5 0x410042c58084462d 0xfc032f1e000338ff 0xff00cbc78000ce3f

def z515 : W := mkw 0x33fffefdb9802642 0x0cffffbf6e600990 0xe3ffffffd1800701 0xf8fffffff46001c0

def z516 : W := mkw 0x03b5c870f9cdc36c 0x00ed721c3e7370db 0xbd27d8f1d18fc7ff 0xef49f63c7463f1ff

def z517 : W := mkw 0x004a800004228000 0x0012a0000108a000 0x0003c0000003c000 0x0000f0000000f000

def z518 : W := mkw 0x044b0a1404230024 0x4112c2850108c009 0x0003000000030000 0x0000c0000000c000

def z519 : W := mkw 0x2bfffedfb0582c11 0x8affffb7ec160b04 0xe3ffffffe0703801 0xf8fffffff81c0e00

def z520 : W := mkw 0x17ea37863f323c93 0x45fa8de18fcc8f24 0x42d8270e2e703800 0x10b609c38b9c0e00

def z521 : W := mkw 0x044b4a56c437493d 0x4112d295b10dd24f 0x081fc01fc07fc01c 0x8207f007f01ff007

def z522 : W := mkw 0x13b4b4a039c8a642 0x04ed2d280e722990 0x0124d0e0118cc700 0x00493438046331c0

def z523 : W := mkw 0x1bb435a97bcc37ca 0x86ed0d6a5ef30df2 0xf7e43fe1ff8c3fe3 0x7df90ff87fe30ff8

def z524 : W := mkw 0x205fca5d80000000 0x0817f29760000000 0xe2dfef1fc0000001 0xf8b7fbc7f0000000

def z525 : W := mkw 0x03a17cf0c085436c 0x00e85f3c302150db 0xffe7fff1d18fc7ff 0xfff9fffc7463f1ff

def z526 : W := mkw 0x00004060c0844348 0x00001018302110d2 0x8d24d0f1d18cc71f 0xa349343c746331c7

def z527 : W := mkw 0x075f0b16367b18b5 0x41d7c2c58d9ec62d 0xffdf2f1e3e7f38ff 0xfff7cbc78f9fce3f

def z528 : W := mkw 0x03fe800030480000 0x00ffa0000c120000 0x8bffc000307c0002 0xe2fff0000c1f0000

def z529 : W := mkw 0x144b0b363fb33ef7 0x4512c2cd8feccfbd 0xfedb2f1e3ff33fff 0xffb6cbc78ffccfff

def z530 : W := mkw 0x04014972c6b75bfd 0x4100525cb1add6ff 0xbd27d8f1ffffffff 0xef49f63c7fffffff

def z531 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x3423d8f1c183c7fd 0x4d08f63c7060f1ff

def z532 : W := mkw 0x20014ed480000000 0x080053b520000000 0x20000fe000000000 0x080003f800000000

def z533 : W := mkw 0x00014870c0844348 0x0000521c302110d2 0xa127d8f1d18cc701 0xe849f63c746331c0

def z534 : W := mkw 0x0300302030802640 0x00c00c080c200990 0xf72038e031803fe3 0x7dc80e380c600ff8

def z535 : W := mkw 0x0001485080000000 0x0000521420000000 0x2023c8e000000000 0x4808f23800000000

def z536 : W := mkw 0x04010b16021118b5 0x410042c58084462d 0xf6c02f1e2e0038ff 0x7db00bc78b800e3f

def z537 : W := mkw 0x00014870fdefc36c 0x0000521c3f7bf0db 0xbd27d8f1ffffc7ff 0xef49f63c7ffff1ff

def z538 : W := mkw 0x23ffffdd82001080 0x08fffff760800420 0xf7ffffffee0038e3 0xfdfffffffb800e38

def z539 : W := mkw 0x0000000000000000 0x0000000000000000 0xb4000800000000e3 0x6d00020000000038

def z540 : W := mkw 0x244b7fdf863318b5 0x4912dff7e18cc62d 0xfedb3fffee7338ff 0xffb6cffffb9cce3f

def z541 : W := mkw 0x13a0348039002402 0x04e80d200e400900 0x0000000000000000 0x0000000000000000

def z542 : W := mkw 0x0814000b405c0919 0x82050002d0170246 0x8d1c101fd07c071f 0xa3470407f41f01c7

def z543 : W := mkw 0x04eb8b140f2390a4 0x413ae2c503c8e429 0x30e3cf000f83c0e0 0x4c38f3c003e0f038

def z544 : W := mkw 0x0000000040040108 0x0000000010010042 0x9d27d011d18fc71f 0xe749f4047463f1c7

def z545 : W := mkw 0x23b4f4c980000000 0x08ed3d3260000000 0xc33cf0ffc0000001 0xb0cf3c3ff0000000

def z546 : W := mkw 0x1b14312b7bdc3fdb 0x86c50c4adef70ff6 0xdf1c301ffffc3fff 0xb7c70c07ffff0fff

def z547 : W := mkw 0x23fffeddc005412c 0x08ffffb77001504b 0xebffffffc00fc01d 0xfafffffff003f007

def z548 : W := mkw 0x245fca5f84330835 0x4917f297e10cc20d 0x081fc01fc073001c 0x8207f007f01cc007

def z549 : W := mkw 0x0000002040840348 0x00000008102100d2 0xbd2418f1d18c07ff 0xef49063c746301ff

def z550 : W := mkw 0x0000000040040108 0x0000000010010042 0x04001011c000071d 0x01000404700001c7

def z551 : W := mkw 0x0b14706bf0dc6f59 0x82c51c1afc371bd6 0xcf3cf0fff1fcff1f 0xb3cf3c3ffc7f3fc7

def z552 : W := mkw 0x20ebfedd80000000 0x083affb760000000 0x60e3ffffc0000001 0x5838fffff0000000

def z553 : W := mkw 0x0bfeb00b3d7aac11 0x82ffac02cf5eab04 0x42d8200e2e703800 0x10b608038b9c0e00

def z554 : W := mkw 0x20014a5d80000000 0x0800529760000000 0x0000001fc0000000 0x00000007f0000000

def z555 : W := mkw 0x2bb4f4cbf05c2d19 0x8aed3d32fc170b46 0xcf3cf0fff07c3f1f 0xb3cf3c3ffc1f0fc7

def z556 : W := mkw 0x33b4f4e9b9802642 0x0ced3d3a6e600990 0x0124d0e1d1800700 0x00493438746001c0

def z557 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x72e02fe02f8038e0 0x5cb80bf80be00e38

def z558 : W := mkw 0x0814000b00580811 0x82050002c0160204 0x0018000e00700000 0x00060003801c0000

def z559 : W := mkw 0x0300300000000000 0x00c00c0000000000 0xc300300000000001 0x30c00c0000000000

def z560 : W := mkw 0x0314300930002400 0x00c50c024c000900 0xc71c301ff0003f03 0xb1c70c07fc000fc0

def z561 : W := mkw 0x1000358002003482 0x04000d6000800d20 0x4000270000003800 0x100009c000000e00

def z562 : W := mkw 0x0001487080814264 0x0000521c20205099 0xbc23c8f00183c0ff 0xef08f23c0060f03f

def z563 : W := mkw 0x23fffeddc0040108 0x08ffffb770010042 0xefffffffd00c071f 0xfbfffffff40301c7

def z564 : W := mkw 0x0000404080000000 0x0000101020000000 0x0124d0e1c0000000 0x0049343870000000

def z565 : W := mkw 0x03fe80203dea8240 0x00ffa0080f7aa090 0xbfffd8e03fffc7e3 0xeffff6380ffff1f8

def z566 : W := mkw 0x2bb4f4c9f04c2508 0x8aed3d327c130942 0x0124d0e1d00c0700 0x00493438740301c0

def z567 : W := mkw 0x13a034a039802642 0x04e80d280e600990 0xb52018e0118007e3 0x6d480638046001f8

def z568 : W := mkw 0x17eb3fb43fa336e6 0x45facfed0fe8cdb9 0xf7e33fe03f833fe3 0x7df8cff80fe0cff8

def z569 : W := mkw 0x2014c04980000000 0x0805301260000000 0x0004c001c0000000 0x0001300070000000

def z570 : W := mkw 0x0815487bc0dd4b7d 0x8205521ef03752df 0xbd3fd8ffd1ffc7ff 0xef4ff63ff47ff1ff

def z571 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x66d82f1e2e7038fd 0x19b60bc78b9c0e3f

def z572 : W := mkw 0x130035a0328036c2 0x04c00d680ca00db0 0xe7003fe030003fe3 0x39c00ff80c000ff8

def z573 : W := mkw 0x0001485080010024 0x0000521420004009 0xbd27d8f1c00300ff 0xef49f63c7000c03f

def z574 : W := mkw 0x23ffced4bd6a8000 0x08fff3b52f5aa000 0xbbffcfe03fffc002 0xeefff3f80ffff000

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0x1023c0000183c000 0x4408f0000060f000

def z576 : W := mkw 0x13feb5a03feab6c2 0x04ffad680ffaadb0 0xf7f83fe03ff03fe3 0x7dfe0ff80ffc0ff8

def z577 : W := mkw 0x044a030606321891 0x411280c1818c8624 0xced8271e2e70381f 0xb3b609c78b9c0e07

def z578 : W := mkw 0x00014870c085436c 0x0000521c302150db 0xb52018f1d18007ff 0x6d48063c746001ff

def z579 : W := mkw 0x140001223fb33ef7 0x450000488feccfbd 0x1c0000003ff33ffe 0x070000000ffccfff

def z580 : W := mkw 0x03ffc850fd6fc12c 0x00fff2143f5bf04b 0x9bffc011ffffc01e 0xe6fff0047ffff007

def z581 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x11e7c0001f8fc000 0x4479f00007e3f000

def z582 : W := mkw 0x2000368d00000000 0x08000da340000000 0x4000270e00000000 0x100009c380000000

def z583 : W := mkw 0x004a00003d6a8000 0x001280000f5aa000 0x9adb00003fffc002 0xe6b6c0000ffff000

def z584 : W := mkw 0x004b081004230024 0x0012c2040108c009 0xbedb08102e7300ff 0xefb6c2040b9cc03f

def z585 : W := mkw 0x004a020400000000 0x0012808100000000 0x42d8270e00000000 0x10b609c380000000

def z586 : W := mkw 0x0000002000800240 0x0000000800200090 0x302008e0018000e0 0x4c08023800600038

def z587 : W := mkw 0x0815485bc05d493d 0x82055216f017524f 0x081fc01fc07fc01c 0x8207f007f01ff007

def z588 : W := mkw 0x005fc870c4efc36c 0x0017f21c313bf0db 0xbd3fd8f1d1ffc7ff 0xef4ff63c747ff1ff

def z589 : W := mkw 0x100035a0028036c2 0x04000d6800a00db0 0xf5203fe011803fe3 0x7d480ff804600ff8

def z590 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x6c1b2f1e007338fd 0x9b06cbc7801cce3f

def z591 : W := mkw 0x07ff8b16063318b5 0x41ffe2c5818cc62d 0xffffef1e2e7338ff 0xfffffbc78b9cce3f

def z592 : W := mkw 0x23ffca5dbd6a8000 0x08fff2976f5aa000 0x9bffc01fffffc002 0xe6fff007fffff000

def z593 : W := mkw 0x0000010002001080 0x0000004000800420 0x30c00f000e0000e0 0x4c3003c003800038

def z594 : W := mkw 0x17ea37a63fb23ed3 0x45fa8de98fec8fb4 0xf7f83fee3ff03fe3 0x7dfe0ffb8ffc0ff8

def z595 : W := mkw 0x0bb4b009794ca508 0x82ed2c025e532942 0x0124d001d18cc700 0x00493400746331c0

def z596 : W := mkw 0x14013fb602913ef7 0x45004fed80a44fbd 0x64003ffe00003ffd 0x19000fff80000fff

def z597 : W := mkw 0x00004040c0044108 0x0000101030011042 0x0004c001c00cc000 0x0001300070033000

def z598 : W := mkw 0x0001487080814264 0x0000521c20205099 0xb127d8f1c183c0e1 0xec49f63c7060f038

def z599 : W := mkw 0x100001207b8577ee 0x040000481ee15dfb 0x1c0000003f8ffffe 0x070000000fe3ffff

def z600 : W := mkw 0x24ebcfd4862310a4 0x493af3f52188c429 0x30e3cfe00e0300e0 0x4c38f3f80380c038

def z601 : W := mkw 0x03157879c085436c 0x00c55e1e702150db 0xff3ff8ffd18fc7ff 0xffcffe3ff463f1ff

def z602 : W := mkw 0x0801787bc0956f7d 0x82005e1ef0255bdf 0x640038ffc0003ffd 0x19000e3ff0000fff

def z603 : W := mkw 0x08000002705c2d19 0x820000009c170b46 0xce18201e307c3f1f 0xb38608078c1f0fc7

def z604 : W := mkw 0x03fe80000d228000 0x00ffa0000348a000 0x93ffc0000f83c000 0xe4fff00003e0f000

def z605 : W := mkw 0x27ffbf9f063318b5 0x49ffefe7c18cc62d 0xfedb2f1e2e7338ff 0xffb6cbc78b9cce3f

def z606 : W := mkw 0x0b5f3a1f705c2d19 0x82d7ce87dc170b46 0xefdf3f1ff07c3f1f 0xfbf7cfc7fc1f0fc7

def z607 : W := mkw 0x0000000039000000 0x000000000e400000 0x100000003f800002 0x040000000fe00000

def z608 : W := mkw 0x13a17cf0f985676e 0x04e85f3c3e6159db 0xbd27d8f1d18fc7ff 0xef49f63c7463f1ff

def z609 : W := mkw 0x0f5f7b7ff6ff7ffd 0xc3d7dedffdbfdfff 0xffffffffffffffff 0xffffffffffffffff

def z610 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x93f800003ff00002 0x64fe00000ffc0000

def z611 : W := mkw 0x100034a000802642 0x04000d2800200990 0x000010e000000700 0x00000438000001c0

def z612 : W := mkw 0x10014970fb8577ee 0x0400525c3ee15dfb 0xbd27d8f1ff8fffff 0xef49f63c7fe3ffff

def z613 : W := mkw 0x00a0800009008000 0x0028200002402000 0x0020c0000180c000 0x0008300000603000

def z614 : W := mkw 0x33fffffd8b8012c2 0x0cffffff62e004b0 0xf3ffffffcf8000e1 0xfcfffffff3e00038

def z615 : W := mkw 0x0000000200100811 0x0000000080040204 0x4218200e20703800 0x10860803881c0e00

def z616 : W := mkw 0x23ebfed480000000 0x08faffb520000000 0xe3e3ffe000000001 0x78f8fff800000000

def z617 : W := mkw 0x0001081200110835 0x000042048004420d 0xfe1b281e207338ff 0xff86ca07881cce3f

def z618 : W := mkw 0x005e8000046a8000 0x0017a000011aa000 0x993fc00011ffc002 0xe64ff000047ff000

def z619 : W := mkw 0x23b5fcf9c085436c 0x08ed7f3e702150db 0xbd27d8f1d18fc7ff 0xef49f63c7463f1ff

def z620 : W := mkw 0x08140009404c0108 0x8205000250130042 0x00040001c00c0000 0x0001000070030000

def z621 : W := mkw 0x27ffffffc6b75bfd 0x49fffffff1add6ff 0xffffffffffffffff 0xffffffffffffffff

def z622 : W := mkw 0x23b5fcd980000000 0x08ed7f3660000000 0xa127d8f1c0000001 0xe849f63c70000000

def z623 : W := mkw 0x23fffefd80814264 0x08ffffbf60205099 0xf3ffffffc183c0e1 0xfcfffffff060f038

def z624 : W := mkw 0x0000000000000000 0x0000000000000000 0xe2c02f0000000001 0x78b00bc000000000

def z625 : W := mkw 0x1bb57dfbfbdd7fff 0x86ed5f7efef75fff 0xffffffffffffffff 0xffffffffffffffff

def z626 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x65203fe011803fe1 0x19480ff804600ff8

def z627 : W := mkw 0x00004060c0844348 0x00001018302110d2 0x9927d0e1d18fc702 0xe649f4387463f1c0

def z628 : W := mkw 0x03fe80023d7a8811 0x00ffa0008f5ea204 0xdfffe01e3ffff81f 0xf7fff8078ffffe07

def z629 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x091c101fd07c071c 0x82470407f41f01c7

def z630 : W := mkw 0x27fffedf84330835 0x49ffffb7e10cc20d 0xebffffffc073001d 0xfafffffff01cc007

def z631 : W := mkw 0x0b15381b705d2d3d 0x82c54e06dc174b4f 0xff1f381ff07f3fff 0xffc7ce07fc1fcfff

def z632 : W := mkw 0x13a035803b003482 0x04e80d600ec00d20 0xf6c02f002e0038e3 0x7db00bc00b800e38

def z633 : W := mkw 0x0f5e330f767e3d99 0xc3d78cc3dd9f8f66 0xcfdc371ffe7c3f1f 0xb3f70dc7ff9f0fc7

def z634 : W := mkw 0x03ea80003d228000 0x00faa0000f48a000 0x93e3c0003f83c002 0x64f8f0000fe0f000

def z635 : W := mkw 0x0b15785bf05c2d19 0x82c55e16fc170b46 0xef3ff8fff07c3f1f 0xfbcffe3ffc1f0fc7

def z636 : W := mkw 0x004b0a1400000000 0x0012c28500000000 0x20c30f0000000000 0x4830c3c000000000

def z637 : W := mkw 0x13fe85a03fea92c2 0x04ffa1680ffaa4b0 0xbbffcfe03fffc0e2 0xeefff3f80ffff038

def z638 : W := mkw 0x075f3b1f063318b5 0x41d7cec7c18cc62d 0xffdf3f1fee7338ff 0xfff7cfc7fb9cce3f

def z639 : W := mkw 0x33fffffdfb8577ee 0x0cffffff7ee15dfb 0xffffffffff8fffff 0xffffffffffe3ffff

def z640 : W := mkw 0x33feb7ad3b8036c2 0x0cffadeb4ee00db0 0xf7f83fee3f803fe3 0x7dfe0ffb8fe00ff8

def z641 : W := mkw 0x03fe800039488000 0x00ffa0000e522000 0x83ffc000118cc000 0xe0fff00004633000

def z642 : W := mkw 0x23ffbe9d00000000 0x08ffefa740000000 0xe2db2f1e00000001 0xf8b6cbc780000000

def z643 : W := mkw 0x035e8000346a8000 0x00d7a0000d1aa000 0x8b1fc000307fc002 0xa2c7f0000c1ff000

def z644 : W := mkw 0x0000000000000000 0x0000000000000000 0x8127c00000000000 0xe049f00000000000

def z645 : W := mkw 0x13a035a00b8012c2 0x04e80d6802e004b0 0xf3e03fe00f8000e1 0x7cf80ff803e00038

def z646 : W := mkw 0x000000000d228000 0x000000000348a000 0x100000000f83c000 0x0400000003e0f000

def z647 : W := mkw 0x13feb5803f6ab482 0x04ffad600fdaad20 0x42d827002e703800 0x10b609c00b9c0e00

def z648 : W := mkw 0x03a0000039000000 0x00e800000e400000 0x0120000011800000 0x0048000004600000

def z649 : W := mkw 0x20ebcef4c085436c 0x083af3bd302150db 0xbde7dff1d18fc7ff 0xef79f7fc7463f1ff

def z650 : W := mkw 0x08000002405c0919 0x8200000090170246 0x08000000007c001c 0x02000000001f0007

def z651 : W := mkw 0x0000000040040108 0x0000000010010042 0x08040011c00c001c 0x8201000470030007

def z652 : W := mkw 0x04010b16063318b5 0x410042c5818cc62d 0x7c002f1e2e7338ff 0x1f000bc78b9cce3f

def z653 : W := mkw 0x07ff8b143f6b90a4 0x41ffe2c50fdae429 0xbbffcf003fffc0e2 0xeefff3c00ffff038

def z654 : W := mkw 0x0b143009704c2508 0x82c50c025c130942 0xc31c301fd00c0701 0xb0c70c07f40301c0

def z655 : W := mkw 0x07eb3f96063318b5 0x41facfe5818cc62d 0xfffb3ffe2e7338ff 0xfffecfff8b9cce3f

def z656 : W := mkw 0x20ebced480000000 0x083af3b520000000 0xa1e7dff1c0000001 0xe879f7fc70000000

def z657 : W := mkw 0x0000000200100811 0x0000000080040204 0x4400201e0000381d 0x1100080780000e07

def z658 : W := mkw 0x03a0000039000000 0x00e800000e400000 0x02c000002e000000 0x00b000000b800000

def z659 : W := mkw 0x0400010206321891 0x41000040818c8624 0x000000002e703800 0x000000000b9c0e00

def z660 : W := mkw 0x03b4c060f9ccc348 0x00ed30183e7330d2 0x0124d0e1d18cc700 0x00493438746331c0

def z661 : W := mkw 0x000000207defc36c 0x000000081f7bf0db 0x1c0000003fffc7fe 0x070000000ffff1ff

def z662 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x12fbc0002ff3c000 0x44bef0000bfcf000

def z663 : W := mkw 0x10a005800b001082 0x0428016002c00420 0x00c007000e000000 0x003001c003800000

def z664 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x4a1c201fe07c381c 0x92870807f81f0e07

def z665 : W := mkw 0x0c5f0a1f447f093d 0xc317c287d11fc24f 0x081f001fc07f001c 0x8207c007f01fc007

def z666 : W := mkw 0x0b157879f0cd676c 0x82c55e1e7c3359db 0xbd27d8f1d18fc7ff 0xef49f63c7463f1ff

def z667 : W := mkw 0x28017edfc0142d19 0x8a005fb7f0050b46 0x64003fffc0003f1d 0x19000ffff0000fc7

def z668 : W := mkw 0x33ebfff4bb8036c2 0x0cfafffd2ee00db0 0xf7e3ffe03f803fe3 0x7df8fff80fe00ff8

def z669 : W := mkw 0x0b003002705c2d19 0x82c00c009c170b46 0xcf003000307c3f1f 0x33c00c000c1f0fc7

def z670 : W := mkw 0x13eab5a03fa2b6c2 0x04faad680fe8adb0 0xf7e3ffe03f83ffe3 0x7df8fff80fe0fff8

def z671 : W := mkw 0x10ea85a00fa292c2 0x043aa16803e8a4b0 0x30e3cfe00f83c0e0 0x4c38f3f803e0f038

def z672 : W := mkw 0x035e0000346a0000 0x00d780000d1a8000 0x9bdf00003e7f0002 0xe6f7c0000f9fc000

def z673 : W := mkw 0x004b4a74c085436c 0x0012d29d302150db 0xffffffffd18fc7ff 0xfffffffff463f1ff

def z674 : W := mkw 0x03b480003d6a8000 0x00ed20000f5aa000 0x1924c0003fffc002 0x064930000ffff000

def z675 : W := mkw 0x23fef4c9bd6a8000 0x08ffbd326f5aa000 0x9bffd0e1ffffc002 0xe6fff4387ffff000

def z676 : W := mkw 0x044a030606321891 0x411280c1818c8624 0xf6d82f0e2e7038e3 0x7db60bc38b9c0e38

def z677 : W := mkw 0x03fe81003f6a9080 0x00ffa0400fdaa420 0xffffef003ffff8e3 0xfffffbc00ffffe38

def z678 : W := mkw 0x0f14310b767f3dbd 0xc3c50c42dd9fcf6f 0xdf1c301ffe7f3fff 0xb7c70c07ff9fcfff

def z679 : W := mkw 0x000000003d6a8000 0x000000000f5aa000 0x000000002e700000 0x000000000b9c0000

def z680 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x62fbefee00000000 0x58befbfb80000000

def z681 : W := mkw 0x00010a1400000000 0x0000428500000000 0x60002f1e00000001 0x18000bc780000000

def z682 : W := mkw 0x0000000000000000 0x0000000000000000 0xc600200020003803 0x3180080008000e00

def z683 : W := mkw 0x13fe81203feab6c2 0x04ffa0480ffaadb0 0x9fffc0003fffffe2 0xe7fff0000ffffff8

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0x9803000000030002 0xe600c0000000c000

def z685 : W := mkw 0x13a13db03b8136e6 0x04e84f6c0ee04db9 0xffe33ff03f833fff 0xfff8cffc0fe0cfff

def z686 : W := mkw 0x03fe80007d6e8108 0x00ffa0001f5ba042 0x9fffd011ffffc71f 0xe7fff4047ffff1c7

def z687 : W := mkw 0x33ffffddbb003482 0x0cfffff76ec00d20 0xe3ffffffee003801 0xf8fffffffb800e00

def z688 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x38db0f1e0e7300fc 0xce36c3c7839cc03f

def z689 : W := mkw 0x0800000b40140919 0x82000002d0050246 0x0000001fc000001c 0x00000007f0000007

def z690 : W := mkw 0x10a005a00b8012c2 0x0428016802e004b0 0xb5e01fe01f8007e3 0x6d7807f807e001f8

def z691 : W := mkw 0x13a035803b003482 0x04e80d600ec00d20 0xe3e03fe02e003801 0x78f80ff80b800e00

def z692 : W := mkw 0x0300300230102c11 0x00c00c008c040b04 0xcf18301e30703f1f 0xb3c60c078c1c0fc7

def z693 : W := mkw 0x03ff8a1400000000 0x00ffe28500000000 0xe3ffef1e00000001 0xf8fffbc780000000

def z694 : W := mkw 0x07eb0b163f3318b5 0x41fac2c58fccc62d 0xfffb2f1e3ff338ff 0xfffecbc78ffcce3f

def z695 : W := mkw 0x0400030602101891 0x410000c180840624 0x4000270e00003800 0x100009c380000e00

def z696 : W := mkw 0x044b0b3606b31af5 0x4112c2cd81acc6bd 0xfffb3ffe3ff33fff 0xfffecfff8ffccfff

def z697 : W := mkw 0x0b14302b70dd6f7d 0x82c50c0adc375bdf 0xdf1c301ff1ffffff 0xb7c70c07fc7fffff

def z698 : W := mkw 0x0000000004220000 0x0000000001088000 0x180000002e730002 0x060000000b9cc000

def z699 : W := mkw 0x0b00300b70142d19 0x82c00c02dc050b46 0xc700301ff0003f1f 0x31c00c07fc000fc7

def z700 : W := mkw 0x1bb4358b3b583c93 0x86ed0d62ced60f24 0x42d8270e2e703800 0x10b609c38b9c0e00

def z701 : W := mkw 0x13a034a039802642 0x04e80d280e600990 0x93e010e03f800702 0x64f804380fe001c0

def z702 : W := mkw 0x23fffedf80100811 0x08ffffb7e0040204 0xefffffffe070381f 0xfbfffffff81c0e07

def z703 : W := mkw 0x03fe800000000000 0x00ffa00000000000 0x02d8000000000000 0x00b6000000000000

def z704 : W := mkw 0x0bfeb0097d6ea508 0x82ffac025f5ba942 0x9bffd001ffffc702 0xe6fff4007ffff1c0

def z705 : W := mkw 0x13a035a23b903ed3 0x04e80d688ee40fb4 0xfff83ffe3ff03fff 0xfffe0fff8ffc0fff

def z706 : W := mkw 0x03b4800000000000 0x00ed200000000000 0x0124c00000000000 0x0049300000000000

def z707 : W := mkw 0x180001227b943fdb 0x860000489ee50ff6 0x140000003f803ffe 0x050000000fe00fff

def z708 : W := mkw 0x005e80000d6a8000 0x0017a000035aa000 0x181fc0000fffc000 0x8607f00003fff000

def z709 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xffe03fe03f8fffe3 0x7ff80ff80fe3fff8

def z710 : W := mkw 0x23fffeddbd6a8000 0x08ffffb76f5aa000 0x62d83fffee700001 0x18b60ffffb9c0000

def z711 : W := mkw 0x18b405ab4bdc1bdb 0x862d016ad2f706f6 0x38fc0fffcffc00fc 0xce3f03fff3ff003f

def z712 : W := mkw 0x305fcb7dbb8036c2 0x0c17f2df6ee00db0 0x141fc01fff803fe2 0x8507f007ffe00ff8

def z713 : W := mkw 0x0814300b705c2d19 0x82050c02dc170b46 0x4c1c301ff07c3f1f 0x93070c07fc1f0fc7

def z714 : W := mkw 0x03feb4893d6a8000 0x00ffad224f5aa000 0xfbffffffffffc003 0xfefffffffffff000

def z715 : W := mkw 0x10a035a00b8036c2 0x04280d6802e00db0 0xf5e03fe01f803fe3 0x7d780ff807e00ff8

def z716 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xffdf3f1fee7338ff 0xfff7cfc7fb9cce3f

def z717 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x3527d8f1d18fc7fd 0x4d49f63c7463f1ff

def z718 : W := mkw 0x07b58b163b5998b5 0x41ed62c58ed6662d 0x6524ef1e118cf8fd 0x19493bc784633e3f

def z719 : W := mkw 0x23fffeddb9488000 0x08ffffb76e522000 0xf3ffffffff8cc003 0xfcffffffffe33000

def z720 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xefffffffc000001f 0xfbfffffff0000007

def z721 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xdf3c301ff1fc3f1f 0xf7cf0c07fc7f0fc7

def z722 : W := mkw 0x20017eddbd6a8000 0x08005fb76f5aa000 0x78003fffffffc003 0x1e000ffffffff000

def z723 : W := mkw 0x0400012246b75bfd 0x4100004891add6ff 0x1c0000002e733ffe 0x070000000b9ccfff

def z724 : W := mkw 0x14eb4ff48fa352e6 0x453ad3fd23e8d4b9 0x30e3cfe00f83c0e0 0x4c38f3f803e0f038

def z725 : W := mkw 0x13a17dd0fb0575ae 0x04e85f743ec15d6b 0x4ac7e711ee0ff81c 0x92b1f9c47b83fe07

def z726 : W := mkw 0x0bb4300b795c2d19 0x82ed0c02de570b46 0xcf3c301ff1fc3f1f 0xb3cf0c07fc7f0fc7

def z727 : W := mkw 0x08eab00b4d36ad19 0x823aac02d34dab46 0x54e3f01fcf83ff1d 0x5538fc07f3e0ffc7

def z728 : W := mkw 0x0f5f3b1d766f35ac 0xc3d7cec75d9bcd6b 0x31c71f01de0f07e0 0x4c71c7c07783c1f8

def z729 : W := mkw 0x00010912021118b5 0x000042448084462d 0xfedb2f1e2e7338ff 0xffb6cbc78b9cce3f

def z730 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x75e03fe01f803fe1 0x5d780ff807e00ff8

def z731 : W := mkw 0x0b14300b795cad19 0x82c50c02de572b46 0xcf1c301ff1fcff1f 0xb3c70c07fc7f3fc7

def z732 : W := mkw 0x03a0358032003480 0x00e80d600c800d20 0xf7e03fe03e003fe3 0x7df80ff80f800ff8

def z733 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xebffffffd00c0003 0xfafffffff4030000

def z734 : W := mkw 0x13a035a03bc8b6c2 0x04e80d680ef22db0 0xf7e03fe03f8cffe3 0x7df80ff80fe33ff8

def z735 : W := mkw 0x23fffedd8d228000 0x08ffffb76348a000 0xfbffffffdf8fc003 0xfefffffff7e3f000

def z736 : W := mkw 0x03ffc870fdefc36c 0x00fff21c3f7bf0db 0x26d818f1ee7007fd 0x09b6063c7b9c01ff

def z737 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xffdb3f1e3e733fff 0xfff6cfc78f9ccfff

def z738 : W := mkw 0x03a0348900000000 0x00e80d2240000000 0xe3e03fffc0000001 0x78f80ffff0000000

def z739 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x21ffdfffc0000000 0xc87ff7fff0000000

def z740 : W := mkw 0x0814300b405c2d19 0x82050c02d0170b46 0xcd1c301fd07c3f1f 0xb3470c07f41f0fc7

def z741 : W := mkw 0x23feb6ad4085436c 0x08ffadab502150db 0x5ed8270e118fc7fe 0x17b609c38463f1ff

def z742 : W := mkw 0x03feb0093d6a8000 0x00ffac024f5aa000 0x9bffd001ffffc002 0xe6fff4007ffff000

def z743 : W := mkw 0x23feb68d3d6a8000 0x08ffada34f5aa000 0xdbfff71fffffc003 0xf6fffdc7fffff000

def z744 : W := mkw 0x1800012242943fdb 0x8600004890a50ff6 0x0400000000003ffc 0x0100000000000fff

def z745 : W := mkw 0x17eb3eb63db32e77 0x45facfad8f6ccb9d 0x093b10fe11f3071c 0x824ec43f847cc1c7

def z746 : W := mkw 0x28ebced6f05c2d19 0x8a3af3b5bc170b46 0x2ce3cfe0307c3f1e 0x4b38f3f80c1f0fc7

def z747 : W := mkw 0x23fef6cdbd6a8000 0x08ffbdb36f5aa000 0x43fcf7effffcc000 0x10ff3dfbffff3000

def z748 : W := mkw 0x13b435a03b8036c2 0x04ed0d680ee00db0 0xf7fc3fe03f803fe3 0xfdff0ff80fe00ff8

def z749 : W := mkw 0x03a001203b8012c0 0x00e800480ee004b0 0xf7e03fe03f803fe3 0x7df80ff80fe00ff8

def z750 : W := mkw 0x044a0306063318b5 0x411280c1818cc62d 0xfed82f0e2e7338ff 0x7fb60bc38b9cce3f

def z751 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x0d1c101ff07c3f1e 0x83470407fc1f0fc7

def z752 : W := mkw 0x0b15787bb0d96e75 0x82c55e1eec365b9d 0x723be8ee21f3f8e0 0x5c8efa3b887cfe38

def z753 : W := mkw 0x03a000003d6a8000 0x00e800000f5aa000 0x9be7c0003fffc002 0xe6f9f0000ffff000

def z754 : W := mkw 0x005e80003d6a8000 0x0017a0000f5aa000 0x993fc0003fffc002 0xe64ff0000ffff000

def z755 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xf3ffffffee000003 0xfcfffffffb800000

def z756 : W := mkw 0x205fcedd80000000 0x0817f3b760000000 0x201fcfffc0000000 0x8807f3fff0000000

def z757 : W := mkw 0x03feb48900000000 0x00ffad2240000000 0xe3ffffffc0000001 0xf8fffffff0000000

def z758 : W := mkw 0x044a0306063318b5 0x411280c1818cc62d 0xdedb270e2e7338fe 0xf7b6c9c38b9cce3f

def z759 : W := mkw 0x2bb4b48b705c2d19 0x8aed2d22dc170b46 0xcf1c301ff07c3f1f 0xb3c70c07fc1f0fc7

def z760 : W := mkw 0x13b4b5a03bc8b6c2 0x04ed2d680ef22db0 0xffe7ffe03f8fffe3 0xfff9fff80fe3fff8

def z761 : W := mkw 0x13a035a03bc836c2 0x04e80d680ef20db0 0xffe03fe03ffc3fe3 0x7ff80ff80fff0ff8

def z762 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xf7e3ffe03f83ffe3 0x7df8fff80fe0fff8

def z763 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xffe03ff03f803fff 0xfff80ffc0fe00fff

def z764 : W := mkw 0x23fffeddbd6a8000 0x08ffffb76f5aa000 0xfbffffffee730003 0xfefffffffb9cc000

def z765 : W := mkw 0x044b4b56863358b5 0x4112d2d5a18cd62d 0xfedbef1e2e73f8ff 0xffb6fbc78b9cfe3f

def z766 : W := mkw 0x23b5feddb9488000 0x08ed7fb76e522000 0x6124ffffd18cc001 0x18493ffff4633000

def z767 : W := mkw 0x23fffedd84220000 0x08ffffb761088000 0xe3ffffffee700001 0xf8fffffffb9c0000

def z768 : W := mkw 0x20017edd80010024 0x08005fb760004009 0xfc033fffc00300ff 0xff00cffff000c03f

def z769 : W := mkw 0x23a17edd80000000 0x08e85fb760000000 0x62c03fffc0000001 0x18b00ffff0000000

def z770 : W := mkw 0x23157eddb0480000 0x08c55fb76c120000 0xeb1c3ffff07c0003 0xbac70ffffc1f0000

def z771 : W := mkw 0x04014972c2955bfd 0x4100525cb0a556ff 0x240018f1c0003ffd 0x0900063c70000fff

def z772 : W := mkw 0x23fffedd80010024 0x08ffffb760004009 0xebffffffc003001d 0xfafffffff000c007

def z773 : W := mkw 0x23fffedd89008000 0x08ffffb762402000 0xe3ffffffc180c001 0xf8fffffff0603000

def z774 : W := mkw 0x23fffeddb9480000 0x08ffffb76e520000 0xfbfffffffffc0003 0xfeffffffffff0000

def z775 : W := mkw 0x23b5fedd80000000 0x08ed7fb760000000 0x60003fffc0000001 0x18000ffff0000000

def z776 : W := mkw 0x23a17eddb9000000 0x08e85fb76e400000 0xf3e03fffff800003 0x7cf80fffffe00000

def z777 : W := mkw 0x23ffceddbd6a8000 0x08fff3b76f5aa000 0xbbffcfffffffc002 0xeefff3fffffff000

def z778 : W := mkw 0x0b14000b705c2d19 0x82c50002dc170b46 0x8f1c001ff07c3f1e 0xa3c70007fc1f0fc7

def z779 : W := mkw 0x23fffeddb9002400 0x08ffffb76e400900 0xf7ffffffff803f03 0xfdffffffffe00fc0

def z780 : W := mkw 0x23fffeddb0002400 0x08ffffb76c000900 0xe3ffffffe0003801 0xf8fffffff8000e00

def z781 : W := mkw 0x03fe80093d6a8000 0x00ffa0024f5aa000 0x9bffc01fffffc002 0xe6fff007fffff000

def z782 : W := mkw 0x23fffeddb9000000 0x08ffffb76e400000 0xe3ffffffee000001 0xf8fffffffb800000

def z783 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x1afbc0003fffc002 0x46bef0000ffff000

def z784 : W := mkw 0x10a005a03b8036c2 0x042801680ee00db0 0xb5e01fe03f803fe3 0x6d7807f80fe00ff8

def z785 : W := mkw 0x235ffedd80000000 0x08d7ffb760000000 0xe31fffffc0000001 0xb8c7fffff0000000

def z786 : W := mkw 0x13a035a93b8036c2 0x04e80d6a4ee00db0 0xf7e03fffff803fe3 0x7df80fffffe00ff8

def z787 : W := mkw 0x0800300b40142d19 0x82000c02d0050b46 0x4c18301fc0703f1d 0x93060c07f01c0fc7

def z788 : W := mkw 0x044b8b16063398b5 0x4112e2c5818ce62d 0xfedbef1e2e73f8ff 0xffb6fbc78b9cfe3f

def z789 : W := mkw 0x20ffcedd8d6a8000 0x083ff3b7635aa000 0x38ffcfffcfffc000 0xce3ff3fff3fff000

def z790 : W := mkw 0x03a035a0028012c0 0x00e80d6800a004b0 0xf7e03fe03f803fe3 0x7df80ff80fe00ff8

def z791 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x4d1c301fd07c3f1d 0x93470c07f41f0fc7

def z792 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x0bffc0003fffc000 0x82fff0000ffff000

def z793 : W := mkw 0x20017edd80000000 0x08005fb760000000 0xe2183fffc0000001 0xb8860ffff0000000

def z794 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xce18301fe0703f1f 0xb3860c07f81c0fc7

def z795 : W := mkw 0x23a17edd80000000 0x08e85fb760000000 0xe3e7ffffc0000001 0xf8f9fffff0000000

def z796 : W := mkw 0x0c017b7fc2957ffd 0xc3005edff0a55fff 0x64003fffc0003ffd 0x19000ffff0000fff

def z797 : W := mkw 0x23b4f4c980000000 0x08ed3d3260000000 0xe3fcffffc0000001 0xf8ff3ffff0000000

def z798 : W := mkw 0x23fffedd80010024 0x08ffffb760004009 0xe7ffffffc00000fd 0xf9fffffff000003f

def z799 : W := mkw 0x23b5fedd80000000 0x08ed7fb760000000 0xe127ffffc0000001 0xf849fffff0000000

def z800 : W := mkw 0x23fffeddb0480000 0x08ffffb76c120000 0xe3ffffffd00c0001 0xf8fffffff4030000

def z801 : W := mkw 0x23eb7edd80000000 0x08fadfb760000000 0xe3fb3fffc0000001 0xf8fecffff0000000

def z802 : W := mkw 0x23fffeddbd6a8000 0x08ffffb76f5aa000 0xf3ffffffdf8fc001 0xfcfffffff7e3f000

def z803 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xe3dc3fffc0000001 0xb8f70ffff0000000

def z804 : W := mkw 0x131431293b8036c2 0x04c50c4a4ee00db0 0xd71c301fff803fe3 0xb5c70c07ffe00ff8

def z805 : W := mkw 0x07fe81227fffdbfd 0x41ffa0489ffff6ff 0x9fffc0003ffffffe 0xe7fff0000fffffff

def z806 : W := mkw 0x13b435a03bc836c2 0x04ed0d680ef20db0 0xf7f83fe03ff03fe3 0x7dfe0ff80ffc0ff8

def z807 : W := mkw 0x23fffeddb0000000 0x08ffffb76c000000 0xe3fffffff0000003 0xf8fffffffc000000

def z808 : W := mkw 0x23fffedd80002400 0x08ffffb760000900 0xe7ffffffc0003f01 0xf9fffffff0000fc0

def z809 : W := mkw 0x040001227fffdbfd 0x410000489ffff6ff 0x1c0000003ffffffe 0x070000000fffffff

def z810 : W := mkw 0x20017edd80010024 0x08005fb760004009 0x64003fffc00000fd 0x19000ffff000003f

def z811 : W := mkw 0x00fe80000d6a8000 0x003fa000035aa000 0x99ffc0001fffc002 0xe67ff00007fff000

def z812 : W := mkw 0x23fffeddbd228000 0x08ffffb76f48a000 0xf3ffffffff83c003 0xfcffffffffe0f000

def z813 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xc718301ff0703f1f 0x31c60c07fc1c0fc7

def z814 : W := mkw 0x044b4b56863318b5 0x4112d2d5a18cc62d 0xfffffffffffff8ff 0xfffffffffffffe3f

def z815 : W := mkw 0x20fffedd80000000 0x083fffb760000000 0x60ffffffc0000001 0xd83ffffff0000000

def z816 : W := mkw 0x045fca56c47fc93d 0x4117f295b11ff24f 0x081fc01fc07fc01c 0x8207f007f01ff007

def z817 : W := mkw 0x00ea80003d6a8000 0x003aa0000f5aa000 0x99e7c0003fffc002 0xe679f0000ffff000

def z818 : W := mkw 0x23fffeddbd6aa400 0x08ffffb76f5aa900 0xffffffffffffff03 0xffffffffffffffc0

def z819 : W := mkw 0x23fef6cd80000000 0x08ffbdb360000000 0xc3fcf7ffc0000001 0xb0ff3dfff0000000

def z820 : W := mkw 0x00014a5480000000 0x0000529520000000 0x60003fffc0000001 0x18000ffff0000000

def z821 : W := mkw 0x03fe800004220000 0x00ffa00001088000 0x9bffc0003fffc002 0xe6fff0000ffff000

def z822 : W := mkw 0x044b4b7486a352e4 0x4112d2dd21a8d4b9 0x30c30fe00e0300e0 0x4c30c3f80380c038

def z823 : W := mkw 0x20017edd80000000 0x08005fb760000000 0x6124ffffc0000001 0x18493ffff0000000

def z824 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x9fffd0003fffc703 0xe7fff4000ffff1c0

def z825 : W := mkw 0x23ebfedd80000000 0x08faffb760000000 0xe3e3ffffc0000001 0x78f8fffff0000000

def z826 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xefdc3f1ff07c3f1f 0xfbf70fc7fc1f0fc7

def z827 : W := mkw 0x20017edd80002400 0x08005fb760000900 0x64003fffc0003f01 0x19000ffff0000fc0

def z828 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x4e1c201ff07c3f1e 0x93870807fc1f0fc7

def z829 : W := mkw 0x105eb5a006eab6c2 0x0417ad6801baadb0 0x6c1fffe0007fffe1 0x9b07fff8001ffff8

def z830 : W := mkw 0x04000102063318b5 0x41000040818cc62d 0xfed82f1e2e7338ff 0xffb60bc78b9cce3f

def z831 : W := mkw 0x23fffedd80014024 0x08ffffb760005009 0xe3ffffffc003c001 0xf8fffffff000f000

def z832 : W := mkw 0x23fffedd84220000 0x08ffffb761088000 0xf3ffffffce030001 0xfcfffffff380c000

def z833 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x35e01fe03f803fe2 0x4d7807f80fe00ff8

def z834 : W := mkw 0x23feb68d3d6a8000 0x08ffada34f5aa000 0xfbffffee3fffc003 0xfefffffb8ffff000

def z835 : W := mkw 0x204b7edd80000000 0x0812dfb760000000 0x60c33fffc0000001 0x5830cffff0000000

def z836 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xebffffffc00fc001 0xfafffffff003f000

def z837 : W := mkw 0x23fffedd846a8000 0x08ffffb7611aa000 0xfbffffffd1ffc003 0xfefffffff47ff000

def z838 : W := mkw 0x0300300270142d19 0x00c00c009c050b46 0xcf1c301ff07c3f1f 0xb3c70c07fc1f0fc7

def z839 : W := mkw 0x20017edd80000000 0x08005fb760000000 0xe1203fffc0000001 0x78480ffff0000000

def z840 : W := mkw 0x13b435a03bc836c2 0x04ed0d680ef20db0 0xf7e43fe03f8c3fe3 0x7df90ff80fe30ff8

def z841 : W := mkw 0x0814000b405c2d19 0x82050002d0170b46 0x0c1c001fc07c3f1c 0x83070007f01f0fc7

def z842 : W := mkw 0x00014a5480000000 0x0000529520000000 0xe127ffffc0000001 0xf849fffff0000000

def z843 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xe7ffffffd0000703 0xf9fffffff40001c0

def z844 : W := mkw 0x0b14300b40142d19 0x82c50c02d0050b46 0xcf1c301fe0703f1f 0xb3c70c07f81c0fc7

def z845 : W := mkw 0x004a00003d6a8000 0x001280000f5aa000 0x9bffc0003fffc002 0xe6fff0000ffff000

def z846 : W := mkw 0x23fffedd84228000 0x08ffffb76108a000 0xe3ffffffc003c001 0xf8fffffff000f000

def z847 : W := mkw 0x24ebcff486a352e4 0x493af3fd21a8d4b9 0x30e3cfe00f83c0e0 0x4c38f3f803e0f038

def z848 : W := mkw 0x20017edd80000000 0x08005fb760000000 0xf927ffffd18fc003 0xfe49fffff463f000

def z849 : W := mkw 0x20ebfedd80000000 0x083affb760000000 0x60c03fffc0000001 0x18300ffff0000000

def z850 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0xfbffef003fffc003 0xfefffbc00ffff000

def z851 : W := mkw 0x0000348900000000 0x00000d2240000000 0x60003fffc0000001 0x18000ffff0000000

def z852 : W := mkw 0x044b4b56863318b5 0x4112d2d5a18cc62d 0xfedb3fffee7338ff 0xffb6cffffb9cce3f

def z853 : W := mkw 0x00014870c085436c 0x0000521c302150db 0xbfe7d8f1ff8fc7ff 0xeff9f63c7fe3f1ff

def z854 : W := mkw 0x23fffedd8d228000 0x08ffffb76348a000 0xe3ffffffce000001 0xf8fffffff3800000

def z855 : W := mkw 0x23fffedd84220000 0x08ffffb761088000 0xfbffffffffffc003 0xfefffffffffff000

def z856 : W := mkw 0x13b4b5a03bc8b6c2 0x04ed2d680ef22db0 0xfffcffe03ffcffe3 0xffff3ff80fff3ff8

def z857 : W := mkw 0x03feb0003d6aa400 0x00ffac000f5aa900 0x9bffd0003fffc702 0xe6fff4000ffff1c0

def z858 : W := mkw 0x23fffeddbd220000 0x08ffffb76f488000 0xfbfffffffff30003 0xfefffffffffcc000

def z859 : W := mkw 0x044a4366c6b65bd9 0x411290d9b1ad96f6 0x43fcf7effffcff00 0x10ff3dfbffff3fc0

def z860 : W := mkw 0x0814000b705c2d19 0x82050002dc170b46 0xce1c201ff07c3f1f 0xb3870807fc1f0fc7

def z861 : W := mkw 0x03feb4803d6aa400 0x00ffad200f5aa900 0xffffffe03fffff03 0xfffffff80fffffc0

def z862 : W := mkw 0x204b7edd84220000 0x0812dfb761088000 0xfadb3fffee730003 0xfeb6cffffb9cc000

def z863 : W := mkw 0x13a005a03b8036c2 0x04e801680ee00db0 0xb7e00fe03f803fe2 0x6df803f80fe00ff8

def z864 : W := mkw 0x10a005a00b8012c2 0x0428016802e004b0 0xf7e03fe03f803fe3 0x7df80ff80fe00ff8

def z865 : W := mkw 0x1bb4b4a979cca74a 0x86ed2d2a5e7329d2 0x0124d0e1d18cc700 0x00493438746331c0

def z866 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xffffef1e2e7338ff 0xfffffbc78b9cce3f

def z867 : W := mkw 0x20ebfedd80000000 0x083affb760000000 0xe1e7ffffc0000001 0xf879fffff0000000

def z868 : W := mkw 0x23fffeddbd6a8000 0x08ffffb76f5aa000 0xe3fffffffffcc001 0xf8ffffffffff3000

def z869 : W := mkw 0x0c00012276ff7ffd 0xc30000489dbfdfff 0x1c0000003ffffffe 0x070000000fffffff

def z870 : W := mkw 0x1bb4348b795c2d1b 0x86ed0d22de570b46 0xcf1c301ff07c3f1f 0xb3c70c07fc1f0fc7

def z871 : W := mkw 0x27b4f5cb863318b5 0x49ed3d72e18cc62d 0x1d24d0e1ee7338fe 0x074934387b9cce3f

def z872 : W := mkw 0x100035a0028036c2 0x04000d6800a00db0 0x66c03fe02e003fe1 0x19b00ff80b800ff8

def z873 : W := mkw 0x0000002040840348 0x00000008102100d2 0xbd27d8f1d18fc7ff 0xef49f63c7463f1ff

def z874 : W := mkw 0x03feb0003d6a8000 0x00ffac000f5aa000 0xdbfff0003fffc003 0xf6fffc000ffff000

def z875 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xfbffffffc0030003 0xfefffffff000c000

def z876 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xff1c381ff07c3fff 0xffc70e07fc1f0fff

def z877 : W := mkw 0x03feb0003d6aa400 0x00ffac000f5aa900 0xdbffe0003ffff802 0xf6fff8000ffffe00

def z878 : W := mkw 0x20014edd80000000 0x080053b760000000 0x20000fffc0000000 0x080003fff0000000

def z879 : W := mkw 0x180001227bdd7fff 0x860000489ef75fff 0x1c0000003ffffffe 0x070000000fffffff

def z880 : W := mkw 0x3bb4f4e9f9cc274a 0x8eed3d3a7e7309d2 0x0124d0e1d18c0700 0x00493438746301c0

def z881 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xf7e4ffe03f8cffe3 0x7df93ff80fe33ff8

def z882 : W := mkw 0x00014870c085436c 0x0000521c302150db 0xbf3fd8f1f1ffc7ff 0xefcff63c7c7ff1ff

def z883 : W := mkw 0x03b57cd980000000 0x00ed5f3660000000 0xe3ffffffc0000001 0xf8fffffff0000000

def z884 : W := mkw 0x23fffedd84220000 0x08ffffb761088000 0xebffffffc0730001 0xfafffffff01cc000

def z885 : W := mkw 0x23fffedd80488000 0x08ffffb760122000 0xe3ffffffc00cc001 0xf8fffffff0033000

def z886 : W := mkw 0x03ea80003d6a8000 0x00faa0000f5aa000 0x9be3c0003fffc002 0x66f8f0000ffff000

def z887 : W := mkw 0x13b4b5a03bc8b6c2 0x04ed2d680ef22db0 0xf7e03fe03f803fe3 0x7df80ff80fe00ff8

def z888 : W := mkw 0x23fffeddb0480000 0x08ffffb76c120000 0xfbfffffff1ffc003 0xfefffffffc7ff000

def z889 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x1adfc0003fffc002 0x86b7f0000ffff000

def z890 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xf7ffffffc00000e3 0xfdfffffff0000038

def z891 : W := mkw 0x044a030606321891 0x411280c1818c8624 0xfed82f1e2e7038ff 0xffb60bc78b9c0e3f

def z892 : W := mkw 0x00014870c085436c 0x0000521c302150db 0xff27f8f1f18fffff 0xffc9fe3c7c63ffff

def z893 : W := mkw 0x23157edd80000000 0x08c55fb760000000 0x61043fffc0000001 0x18410ffff0000000

def z894 : W := mkw 0x13a035a00b8036c2 0x04e80d6802e00db0 0xf7e03fe00f803fe1 0x7df80ff803e00ff8

def z895 : W := mkw 0x04ebcb748fa3d2e4 0x413af2dd23e8f4b9 0x30e3cfe00f83c0e0 0x4c38f3f803e0f038

def z896 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0xdbffe01e3fffc003 0xf6fff8078ffff000

def z897 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x7ed82f1e2e7338ff 0x1fb60bc78b9cce3f

def z898 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x43fff7ffc0000000 0x90fffdfff0000000

def z899 : W := mkw 0x0b14300b405c2d19 0x82c50c02d0170b46 0xcf1c301fc07c3f1d 0xb3c70c07f01f0fc7

def z900 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0xbbffd8e03fffc003 0xeefff6380ffff000

def z901 : W := mkw 0x23fffeddbd6a8000 0x08ffffb76f5aa000 0xf3fffffffff00003 0xfcfffffffffc0000

def z902 : W := mkw 0x23a17edd80000000 0x08e85fb760000000 0x61203fffc0000001 0x18480ffff0000000

def z903 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x63fcffffc0000001 0x18ff3ffff0000000

def z904 : W := mkw 0x23fffeddb9488000 0x08ffffb76e522000 0xebfffffff1fcc003 0xfafffffffc7f3000

def z905 : W := mkw 0x0814000b705c2d19 0x82050002dc170b46 0x8d1c101ff07c3f1f 0xa3470407fc1f0fc7

def z906 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0xbfffc8003fffc0e3 0xeffff2000ffff038

def z907 : W := mkw 0x0b14348b705c2d19 0x82c50d22dc170b46 0xef1c3ffff07c3f1f 0xbbc70ffffc1f0fc7

def z908 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xe3f83fffc0000001 0x78fe0ffff0000000

def z909 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xcf3ff01ff07c3f1f 0xf3cffc07fc1f0fc7

def z910 : W := mkw 0x13feb4803d6aa402 0x04ffad200f5aa900 0x9bffc0003fffc002 0xe6fff0000ffff000

def z911 : W := mkw 0x23fe820d3d6a8000 0x08ffa0834f5aa000 0x9bffc00e3fffc002 0xe6fff0038ffff000

def z912 : W := mkw 0x20017edd80000000 0x08005fb760000000 0x6007ffffc0000001 0x9801fffff0000000

def z913 : W := mkw 0x0314348900000000 0x00c50d2240000000 0xe31c3fffc0000001 0xb8c70ffff0000000

def z914 : W := mkw 0x044a0306063318b5 0x411280c1818cc62d 0x46d8270e2e7038fc 0x11b609c38b9c0e3f

def z915 : W := mkw 0x10a005a00b8036c2 0x0428016802e00db0 0x34e00fe00f803fe0 0x4d3803f803e00ff8

def z916 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x62ffefffc0000000 0xd8bffbfff0000000

def z917 : W := mkw 0x34ebcff48fa312e6 0x4d3af3fd23e8c4b9 0x30e3cfe00f8300e0 0x4c38f3f803e0c038

def z918 : W := mkw 0x23fef6cd80000000 0x08ffbdb360000000 0xc3fff7efc0000000 0xf0fffdfbf0000000

def z919 : W := mkw 0x0bb4348b795c2d19 0x82ed0d22de570b46 0xfffc3ffffffc3f1f 0xffff0fffffff0fc7

def z920 : W := mkw 0x204b7edd80000000 0x0812dfb760000000 0x601b3fffc0000001 0x9806cffff0000000

def z921 : W := mkw 0x03ffca54bd6a8000 0x00fff2952f5aa000 0xfbffffffffffc003 0xfefffffffffff000

def z922 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x1affc0002fffc000 0xc6bff0000bfff000

def z923 : W := mkw 0x03b4000039480000 0x00ed00000e520000 0x9bffc0003fffc002 0xe6fff0000ffff000

def z924 : W := mkw 0x23fffedd80480000 0x08ffffb760120000 0xebffffffc07c0001 0xfafffffff01f0000

def z925 : W := mkw 0x00014a74c085436c 0x0000529d302150db 0xfd27ffffd18fc7ff 0xff49fffff463f1ff

def z926 : W := mkw 0x27fffedd84230024 0x49ffffb76108c009 0xe3ffffffc0030001 0xf8fffffff000c000

def z927 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x4e18301ff07c3f1f 0x13860c07fc1f0fc7

def z928 : W := mkw 0x23fffedd8d6a8000 0x08ffffb7635aa000 0xfbffffffcfffc001 0xfefffffff3fff000

def z929 : W := mkw 0x23fef6cd80000000 0x08ffbdb360000000 0xe3fcffefc0000001 0x78ff3ffbf0000000

def z930 : W := mkw 0x205ffedd80000000 0x0817ffb760000000 0xe2dfffffc0000001 0xf8b7fffff0000000

def z931 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xf6d82f1e2e7038ff 0x7db60bc78b9c0e3f

def z932 : W := mkw 0x13b435a93b8036c2 0x04ed0d6a4ee00db0 0xf7f83fee3f803fe3 0x7dfe0ffb8fe00ff8

def z933 : W := mkw 0x244bcb56863318b5 0x4912f2d5a18cc62d 0xfedbef1e2e7338ff 0xffb6fbc78b9cce3f

def z934 : W := mkw 0x035e80003d6a8000 0x00d7a0000f5aa000 0x9b1fc0003fffc002 0xa6c7f0000ffff000

def z935 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xcf3cf01ff1fcff1f 0xb3cf3c07fc7f3fc7

def z936 : W := mkw 0x23fffedd80010024 0x08ffffb760004009 0xf3ffffffc00300e1 0xfcfffffff000c038

def z937 : W := mkw 0x13a0b5a03b80b6c2 0x04e82d680ee02db0 0xf7e0ffe03f80ffe3 0x7df83ff80fe03ff8

def z938 : W := mkw 0x23017edd80000000 0x08c05fb760000000 0xe3003fffc0000001 0x38c00ffff0000000

def z939 : W := mkw 0x23fffedd846a8000 0x08ffffb7611aa000 0xe3ffffffc0700001 0xf8fffffff01c0000

def z940 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xef3c38fff07c3f1f 0xfbcf0e3ffc1f0fc7

def z941 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xebffffffe0700003 0xfafffffff81c0000

def z942 : W := mkw 0x200076cd80000000 0x08001db360000000 0x400037efc0000000 0x10000dfbf0000000

def z943 : W := mkw 0x23fffedd8d228000 0x08ffffb76348a000 0xfbffffffeff3c003 0xfefffffffbfcf000

def z944 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xfedfef1e2e7ff8ff 0xffb7fbc78b9ffe3f

def z945 : W := mkw 0x130035a0328036c2 0x04c00d680ca00db0 0xf7c03fe03e003fe3 0x7df00ff80f800ff8

def z946 : W := mkw 0x004a80003d6a8000 0x0012a0000f5aa000 0x1803c0003fffc002 0x0600f0000ffff000

def z947 : W := mkw 0x0400012242955bfd 0x4100004890a556ff 0x0400000000003ffc 0x0100000000000fff

def z948 : W := mkw 0x1bb474e9f9cc674a 0x86ed1d3a7e7319d2 0x0124d0e1d18cc700 0x00493438746331c0

def z949 : W := mkw 0x20ebfedd80000000 0x083affb760000000 0xe2fbffffc0000001 0xf8befffff0000000

def z950 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xffe33fe03f833fe3 0xfff8cff80fe0cff8

def z951 : W := mkw 0x03feb4803d6a8000 0x00ffad200f5aa000 0xdbffe7003fffc002 0xf6fff9c00ffff000

def z952 : W := mkw 0x23fffeddb9488000 0x08ffffb76e522000 0xe3ffffffc0000001 0xf8fffffff0000000

def z953 : W := mkw 0x204bfedd80000000 0x0812ffb760000000 0x6003ffffc0000001 0x1800fffff0000000

def z954 : W := mkw 0x0bb4348b705c2d19 0x82ed0d22dc170b46 0xcfdc371ff07c3f1f 0xb3f70dc7fc1f0fc7

def z955 : W := mkw 0x03fe80003d6aa400 0x00ffa0000f5aa900 0x9fffc0003fffff02 0xe7fff0000fffffc0

def z956 : W := mkw 0x005e80003d6a8000 0x0017a0000f5aa000 0x9adfc0003fffc002 0xe6b7f0000ffff000

def z957 : W := mkw 0x03b4348939480000 0x00ed0d224e520000 0xfbfc3ffffffc0003 0xfeff0fffffff0000

def z958 : W := mkw 0x0000000004220000 0x0000000001088000 0x9927c0003fffc002 0xe649f0000ffff000

def z959 : W := mkw 0x23fffedd84230024 0x08ffffb76108c009 0xffffffffee7300ff 0xfffffffffb9cc03f

def z960 : W := mkw 0x13b435a93bc836c2 0x04ed0d6a4ef20db0 0xfffc3ffffffc3fe3 0xffff0fffffff0ff8

def z961 : W := mkw 0x23fffeddb46a0000 0x08ffffb76d1a8000 0xfbfffffffe7f0003 0xfeffffffff9fc000

def z962 : W := mkw 0x00014870c085436c 0x0000521c302150db 0xffe7fff1d18fc7ff 0xfff9fffc7463f1ff

def z963 : W := mkw 0x23fffeddb9488000 0x08ffffb76e522000 0xfbffffffd18fc003 0xfefffffff463f000

def z964 : W := mkw 0x0814300b405c2d19 0x82050c02d0170b46 0xce1c301fe07c3f1f 0xb3870c07f81f0fc7

def z965 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0xdfffe0003ffff803 0xf7fff8000ffffe00

def z966 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xeed82f1e2e7038ff 0xbbb60bc78b9c0e3f

def z967 : W := mkw 0x0bb4300b705c2d19 0x82ed0c02dc170b46 0xcffc301ff07c3f1f 0xf3ff0c07fc1f0fc7

def z968 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xe3ffffffd18cc001 0xf8fffffff4633000

def z969 : W := mkw 0x23157edd80000000 0x08c55fb760000000 0x62183fffc0000001 0x18860ffff0000000

def z970 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x2d27d8f1d18fc7fd 0x8b49f63c7463f1ff

def z971 : W := mkw 0x1bfeb58b3f7abc93 0x86ffad62cfdeaf24 0x42d8270e2e703800 0x10b609c38b9c0e00

def z972 : W := mkw 0x0b00300b70142d19 0x82c00c02dc050b46 0xcf18301ff0703f1f 0xb3c60c07fc1c0fc7

def z973 : W := mkw 0x1c0001227fff3fff 0xc70000489fffcfff 0x1c0000003fff3ffe 0x070000000fffcfff

def z974 : W := mkw 0x0000000240140919 0x0000000090050246 0xce18301fe0703f1f 0xb3860c07f81c0fc7

def z975 : W := mkw 0x140001227fb77fff 0x450000489feddfff 0x1c0000003ffffffe 0x070000000fffffff

def z976 : W := mkw 0x08000002705c2d19 0x820000009c170b46 0xcf1c301ff07c3f1f 0xb3c70c07fc1f0fc7

def z977 : W := mkw 0x23fffeddbd6a8000 0x08ffffb76f5aa000 0xebffffffd1ffc001 0xfafffffff47ff000

def z978 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x73e03fe03f803fe0 0x5cf80ff80fe00ff8

def z979 : W := mkw 0x00004060c085436c 0x00001018302150db 0x9d27d0e1d18fc7fe 0xe749f4387463f1ff

def z980 : W := mkw 0x205ffedd846a8000 0x0817ffb7611aa000 0x681fffffc07fc001 0x9a07fffff01ff000

def z981 : W := mkw 0x044b4b56863318b5 0x4112d2d5a18cc62d 0xfefbeffe2e7338ff 0xffbefbff8b9cce3f

def z982 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xffdf2f1e3e7f38ff 0xfff7cbc78f9fce3f

def z983 : W := mkw 0x0400012242955bfd 0x4100004890a556ff 0x1c000000118ffffe 0x070000000463ffff

def z984 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xe7ffffffe0003803 0xf9fffffff8000e00

def z985 : W := mkw 0x10a035a00b8036c2 0x04280d6802e00db0 0x64c03fe00e003fe1 0x19300ff803800ff8

def z986 : W := mkw 0x0b14300b795c2d19 0x82c50c02de570b46 0xdf1c301ffffc3f1f 0xb7c70c07ffff0fc7

def z987 : W := mkw 0x10a035a03b8036c2 0x04280d680ee00db0 0x74e03fe03f803fe3 0x5d380ff80fe00ff8

def z988 : W := mkw 0x13b435a93b8036c2 0x04ed0d6a4ee00db0 0xf7e43fe1ff803fe3 0x7df90ff87fe00ff8

def z989 : W := mkw 0x205fca5d80000000 0x0817f29760000000 0xe3ffffffc0000001 0xf8fffffff0000000

def z990 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x19e7c0003fffc002 0x4679f0000ffff000

def z991 : W := mkw 0x23fffeddb0480000 0x08ffffb76c120000 0xe3ffffffe0700001 0xf8fffffff81c0000

def z992 : W := mkw 0x0314300b30102c11 0x00c50c02cc040b04 0xcf1c301ff0703f1f 0xb3c70c07fc1c0fc7

def z993 : W := mkw 0x23157edd80000000 0x08c55fb760000000 0xe33fffffc0000001 0xf8cffffff0000000

def z994 : W := mkw 0x23fffeddbd6a8000 0x08ffffb76f5aa000 0xf3ffffffeff3c001 0xfcfffffffbfcf000

def z995 : W := mkw 0x1bfe81227ffebfdb 0x86ffa0489fffaff6 0x9fffc0003ffffffe 0xe7fff0000fffffff

def z996 : W := mkw 0x100035a0028036c2 0x04000d6800a00db0 0x74c03fe00e003fe1 0x5d300ff803800ff8

def z997 : W := mkw 0x20ffcedd80000000 0x083ff3b760000000 0xa1ffdfffc0000001 0xe87ff7fff0000000

def z998 : W := mkw 0x03ff3e9d00000000 0x00ffcfa740000000 0xe3ff3fffc0000001 0xf8ffcffff0000000

def z999 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x4e1c301fe07c3f1d 0x93870c07f81f0fc7

def z1000 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x62dfffffc0000001 0x98b7fffff0000000

def z1001 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xfffb3ffe2e7338ff 0xfffecfff8b9cce3f

def z1002 : W := mkw 0x04014952863318b5 0x41005254a18cc62d 0xbd27d8f1ee7338ff 0xef49f63c7b9cce3f

def z1003 : W := mkw 0x0814000b405c0919 0x82050002d0170246 0xcf1c301ff07c3f1f 0xb3c70c07fc1f0fc7

def z1004 : W := mkw 0x03feb4803d6a8000 0x00ffad200f5aa000 0x9bffd0e03fffc002 0xe6fff4380ffff000

def z1005 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xf3ffffffd1800003 0xfcfffffff4600000

def z1006 : W := mkw 0x1800012272dc3fdb 0x860000489cb70ff6 0x0c000000307c3ffe 0x030000000c1f0fff

def z1007 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x3d27d8e1d18fc7fe 0x4f49f6387463f1ff

def z1008 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xc71c301fe0703f1d 0xb1c70c07f81c0fc7

def z1009 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x63ffffefc0000000 0x58fffffbf0000000

def z1010 : W := mkw 0x33b4b5a93b8036c2 0x0ced2d6a4ee00db0 0xf7e03fe03f803fe3 0x7df80ff80fe00ff8

def z1011 : W := mkw 0x180001227ffebfdb 0x860000489fffaff6 0x1c0000003ffffffe 0x070000000fffffff

def z1012 : W := mkw 0x23b57edd80000000 0x08ed5fb760000000 0xe3fc3fffc0000001 0xf8ff0ffff0000000

def z1013 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xe2db3fffc0000001 0xf8b6cffff0000000

def z1014 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xfefbef1e2ff3f8ff 0xffbefbc78bfcfe3f

def z1015 : W := mkw 0x0800300b40142d19 0x82000c02d0050b46 0x4618301fe0703f1d 0x11860c07f81c0fc7

def z1016 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x5edb271e2e7338fe 0x97b6c9c78b9cce3f

def z1017 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xf7f83ffe3f803fe3 0xfdfe0fff8fe00ff8

def z1018 : W := mkw 0x03fe80000d6a8000 0x00ffa000035aa000 0x9bffc0000fffc000 0xe6fff00003fff000

def z1019 : W := mkw 0x10a005a03b8036c2 0x042801680ee00db0 0xf6e02fe03f803fe3 0x7db80bf80fe00ff8

def z1020 : W := mkw 0x03ea00003d220000 0x00fa80000f488000 0x9bffc0003fffc002 0xe6fff0000ffff000

def z1021 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x471c301ff07c3f1d 0x11c70c07fc1f0fc7

def z1022 : W := mkw 0x03eb7ed480000000 0x00fadfb520000000 0xe3ffffffc0000001 0xf8fffffff0000000

def z1023 : W := mkw 0x23fef6cd80000000 0x08ffbdb360000000 0x42d837efc0000000 0x10b60dfbf0000000

def z1024 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x76db2f1e2e7338fd 0x5db6cbc78b9cce3f

def z1025 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x7adb2f1e2e7338fc 0xdeb6cbc78b9cce3f

def z1026 : W := mkw 0x03003120328036c0 0x00c00c480ca00db0 0xf7e03fe03f803fe3 0x7df80ff80fe00ff8

def z1027 : W := mkw 0x00ea80000d228000 0x003aa0000348a000 0x9bffc0003fffc002 0xe6fff0000ffff000

def z1028 : W := mkw 0x0bb4b00b795cad19 0x82ed2c02de572b46 0xdf3ff01ff1ffff1f 0xf7cffc07fc7fffc7

def z1029 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xfff83fe03ff03fe3 0xfffe0ff80ffc0ff8

def z1030 : W := mkw 0x0bfeb0093d6aa400 0x82ffac024f5aa900 0x9bffc0003fffc002 0xe6fff0000ffff000

def z1031 : W := mkw 0x004b4a5480000000 0x0012d29520000000 0xe2db3fffc0000001 0xf8b6cffff0000000

def z1032 : W := mkw 0x03fe82043d6a8000 0x00ffa0810f5aa000 0xdbffe70e3fffc002 0xf6fff9c38ffff000

def z1033 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x9bffd011ffffc003 0xe6fff4047ffff000

def z1034 : W := mkw 0x23b5fedd80000000 0x08ed7fb760000000 0xe3e4ffffc0000001 0x78f93ffff0000000

def z1035 : W := mkw 0x00014870c085436c 0x0000521c302150db 0xff3ff8ffd18fc7ff 0xffcffe3ff463f1ff

def z1036 : W := mkw 0x100001203b8036c2 0x040000480ee00db0 0xf7e03fe03f803fe3 0x7df80ff80fe00ff8

def z1037 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x61e7ffffc0000001 0x5879fffff0000000

def z1038 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xe7c03fe03e003fe3 0x39f00ff80f800ff8

def z1039 : W := mkw 0x1bb401227bdc3fdb 0x86ed00489ef70ff6 0x9ffc00003ffc3ffe 0xe7ff00000fff0fff

def z1040 : W := mkw 0x23fffedd846a8000 0x08ffffb7611aa000 0xfbffffffee7fc003 0xfefffffffb9ff000

def z1041 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x76c03fe03f803fe3 0x1db00ff80fe00ff8

def z1042 : W := mkw 0x20017edd80000000 0x08005fb760000000 0xe0033fffc0000001 0xf800cffff0000000

def z1043 : W := mkw 0x2bfffeddb0482400 0x8affffb76c120900 0xe3ffffffc0000001 0xf8fffffff0000000

def z1044 : W := mkw 0x20a17edd80000000 0x08285fb760000000 0x60e03fffc0000001 0x58380ffff0000000

def z1045 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xffe43fe03f8c3fe3 0xfff90ff80fe30ff8

def z1046 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xfffb2f1e3ff338ff 0xfffecbc78ffcce3f

def z1047 : W := mkw 0x23fffeddbd6b8024 0x08ffffb76f5ae009 0xffffffffffffc0ff 0xfffffffffffff03f

def z1048 : W := mkw 0x044a0306063318b5 0x411280c1818cc62d 0xded8271e2e7338ff 0xb7b609c78b9cce3f

def z1049 : W := mkw 0x03ffca5480000000 0x00fff29520000000 0xe3ffffffc0000001 0xf8fffffff0000000

def z1050 : W := mkw 0x204b7edd80000000 0x0812dfb760000000 0xe3ffffffc0000001 0xf8fffffff0000000

def z1051 : W := mkw 0x0bb4348b705c2d19 0x82ed0d22dc170b46 0xcf3c30fff07c3f1f 0xb3cf0c3ffc1f0fc7

def z1052 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x6edb2f1e2e7338fd 0x9bb6cbc78b9cce3f

def z1053 : W := mkw 0x0c5f4a5fc47f493d 0xc317d297f11fd24f 0x081fc01fc07fc01c 0x8207f007f01ff007

def z1054 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x76e02fe03f803fe2 0x5db80bf80fe00ff8

def z1055 : W := mkw 0x205ffedd80000000 0x0817ffb760000000 0xe13fffffc0000001 0xf84ffffff0000000

def z1056 : W := mkw 0x24017fffc2955bfd 0x49005ffff0a556ff 0x64003fffc0003ffd 0x19000ffff0000fff

def z1057 : W := mkw 0x100035a03b8036c2 0x04000d680ee00db0 0xf6c03fe03f803fe3 0x7db00ff80fe00ff8

def z1058 : W := mkw 0x23fffeddb0482400 0x08ffffb76c120900 0xeffffffff07c3f03 0xfbfffffffc1f0fc0

def z1059 : W := mkw 0x23fffeddbd6a8000 0x08ffffb76f5aa000 0xebffffffee7fc001 0xfafffffffb9ff000

def z1060 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xf7e43ff1ff803fe3 0xfdf90ffc7fe00ff8

def z1061 : W := mkw 0x004b0a344085436c 0x0012c28d102150db 0xfedb2f1e118fc7ff 0xffb6cbc78463f1ff

def z1062 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xdf1f301ff07f3f1f 0xf7c7cc07fc1fcfc7

def z1063 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x67e03fe03f803fe1 0x19f80ff80fe00ff8

def z1064 : W := mkw 0x14017ff6c2957fff 0x45005ffdb0a55fff 0x64003fffc0003ffd 0x19000ffff0000fff

def z1065 : W := mkw 0x20ebfedd8d228000 0x083affb76348a000 0x70e3ffffcf83c001 0x5c38fffff3e0f000

def z1066 : W := mkw 0x100035a0028036c2 0x04000d6800a00db0 0xf7e03fe03f803fe3 0x7df80ff80fe00ff8

def z1067 : W := mkw 0x00ea80003d6a8000 0x003aa0000f5aa000 0x9afbc0003fffc002 0xe6bef0000ffff000

def z1068 : W := mkw 0x03feb0093d6a8000 0x00ffac024f5aa000 0xdbffe00e3fffc002 0xf6fff8038ffff000

def z1069 : W := mkw 0x044a012246b75bfd 0x4112804891add6ff 0x9fffc0003ffffffe 0xe7fff0000fffffff

def z1070 : W := mkw 0x00fe80000d6a8000 0x003fa000035aa000 0x9affc0002fffc002 0xe6bff0000bfff000

def z1071 : W := mkw 0x0bb4b00b795cad19 0x82ed2c02de572b46 0xcf1c301ff07c3f1f 0xb3c70c07fc1f0fc7

def z1072 : W := mkw 0x23feb68d00000000 0x08ffada340000000 0xe3fc3fffc0000001 0xf8ff0ffff0000000

def z1073 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xdf1c301ff1ffff1f 0xb7c70c07fc7fffc7

def z1074 : W := mkw 0x0814300b405c2d19 0x82050c02d0170b46 0x4418301fc0703f1d 0x11060c07f01c0fc7

def z1075 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xdfdc301ffe7c3f1f 0xf7f70c07ff9f0fc7

def z1076 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xe6db2f1e2e7038fd 0xf9b6cbc78b9c0e3f

def z1077 : W := mkw 0x0bb4300b795c2d19 0x82ed0c02de570b46 0xcfdc301ffe7c3f1f 0xb3f70c07ff9f0fc7

def z1078 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xf7e7ffe03f803fe3 0xfdf9fff80fe00ff8

def z1079 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0xf3ffffffc183c001 0xfcfffffff060f000

def z1080 : W := mkw 0x23fffeddb46a8000 0x08ffffb76d1aa000 0xebfffffff07fc003 0xfafffffffc1ff000

def z1081 : W := mkw 0x035e0000346a0000 0x00d780000d1a8000 0x9bffc0003fffc002 0xe6fff0000ffff000

def z1082 : W := mkw 0x044b4a56c437493d 0x4112d295b10dd24f 0x081b001fc073001c 0x8206c007f01cc007

def z1083 : W := mkw 0x0800300b705c2d19 0x82000c02dc170b46 0xce18301ff07c3f1f 0xb3860c07fc1f0fc7

def z1084 : W := mkw 0x23fffeddb0002400 0x08ffffb76c000900 0xe3ffffffd0000701 0xf8fffffff40001c0

def z1085 : W := mkw 0x03fe84803d6a8000 0x00ffa1200f5aa000 0xbbffcfe03fffc002 0xeefff3f80ffff000

def z1086 : W := mkw 0x23fffeddbd6a8000 0x08ffffb76f5aa000 0xebfffffffe7c0003 0xfaffffffff9f0000

def z1087 : W := mkw 0x23fffedd89000000 0x08ffffb762400000 0xf3ffffffcf800001 0xfcfffffff3e00000

def z1088 : W := mkw 0x23ffcedd80000000 0x08fff3b760000000 0xa3ffcfffc0000000 0xe8fff3fff0000000

def z1089 : W := mkw 0x03140002705c0919 0x00c500009c170246 0xcf1c301ff07c3f1f 0xb3c70c07fc1f0fc7

def z1090 : W := mkw 0x005e8000046a8000 0x0017a000011aa000 0x9bffc0003fffc002 0xe6fff0000ffff000

def z1091 : W := mkw 0x004a010206321891 0x00128040818c8624 0xfedb2f1e2e7338ff 0xffb6cbc78b9cce3f

def z1092 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x19ffc0001fffc000 0xc67ff00007fff000

def z1093 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x62fbffffc0000001 0x58befffff0000000

def z1094 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xf6c03fe02e003fe3 0x7db00ff80b800ff8

def z1095 : W := mkw 0x18017dfbc2957fff 0x86005f7ef0a55fff 0x64003fffc0003ffd 0x19000ffff0000fff

def z1096 : W := mkw 0x03feb0093d6aa400 0x00ffac024f5aa900 0xdffff01fffffff03 0xf7fffc07ffffffc0

def z1097 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x3927d8f1d18fc7fc 0xce49f63c7463f1ff

def z1098 : W := mkw 0x004b4a5484220000 0x0012d29521088000 0xfbffffffffffc003 0xfefffffffffff000

def z1099 : W := mkw 0x23b5fedd80000000 0x08ed7fb760000000 0xe33cffffc0000001 0xb8cf3ffff0000000

def z1100 : W := mkw 0x00014870c085436c 0x0000521c302150db 0x1d27d0f1d18fc7fe 0x8749f43c7463f1ff

def z1101 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0xfedb2f1e3ffff8ff 0xffb6cbc78ffffe3f

def z1102 : W := mkw 0x235f7edd80000000 0x08d7dfb760000000 0xe3df3fffc0000001 0xf8f7cffff0000000

def z1103 : W := mkw 0x33fffeddb9002402 0x0cffffb76e400900 0xe3ffffffc0000001 0xf8fffffff0000000

def z1104 : W := mkw 0x20157edd80000000 0x08055fb760000000 0x601c3fffc0000001 0x98070ffff0000000

def z1105 : W := mkw 0x13a035a0028036c2 0x04e80d6800a00db0 0xf7e03fe02e003fe3 0x7df80ff80b800ff8

def z1106 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x13ffc0003fffc000 0x44fff0000ffff000

def z1107 : W := mkw 0x000000003d6a8000 0x000000000f5aa000 0x1807c0003fffc002 0x8601f0000ffff000

def z1108 : W := mkw 0x23fffedd80000000 0x08ffffb760000000 0x613fffffc0000001 0x984ffffff0000000

def z1109 : W := mkw 0x035f7a5d80000000 0x00d7de9760000000 0xe3ffffffc0000001 0xf8fffffff0000000

def z1110 : W := mkw 0x10a035a00b8036c2 0x04280d6802e00db0 0xf6e03fe02f803fe3 0x7db80ff80be00ff8

def z1111 : W := mkw 0x00ea80000d6a8000 0x003aa000035aa000 0x18e3c0000fffc000 0x4638f00003fff000

def z1112 : W := mkw 0x0800300b40142d19 0x82000c02d0050b46 0xcf1c301ff07c3f1f 0xb3c70c07fc1f0fc7

def z1113 : W := mkw 0x13b4b5a03b8036c2 0x04ed2d680ee00db0 0xf7e4ffe03f803fe3 0x7df93ff80fe00ff8

def z1114 : W := mkw 0x03b480003d6a8000 0x00ed20000f5aa000 0x9927c0003fffc002 0xe649f0000ffff000

def z1115 : W := mkw 0x23fffeddb9000000 0x08ffffb76e400000 0xfbffffffff8fc003 0xfeffffffffe3f000

def z1116 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0xcf1ff01ff07fff1f 0xb3c7fc07fc1fffc7

def z1117 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0xe7e03fe02e003fe1 0x79f80ff80b800ff8

def z1118 : W := mkw 0x0b14300b705c2d19 0x82c50c02dc170b46 0x4b1c301ff07c3f1c 0x92c70c07fc1f0fc7

def z1119 : W := mkw 0x20ebcedd80000000 0x083af3b760000000 0x20e3cfffc0000000 0x4838f3fff0000000

def z1120 : W := mkw 0x13a035a03b8036c2 0x04e80d680ee00db0 0x76e03fe02f803fe1 0x5db80ff80be00ff8

def z1121 : W := mkw 0x00000120028012c0 0x0000004800a004b0 0xf6c03fe02e003fe3 0x7db00ff80b800ff8

def z1122 : W := mkw 0x23feb4893d6a8000 0x08ffad224f5aa000 0x9bffc0003fffc002 0xe6fff0000ffff000

def z1123 : W := mkw 0x2c5fca5fc47f093d 0xcb17f297f11fc24f 0x081fc01fc07f001c 0x8207f007f01fc007

def z1124 : W := mkw 0x23b4f6cd80000000 0x08ed3db360000000 0x4124f7efc0000000 0x10493dfbf0000000

def z1125 : W := mkw 0x20ebced480000000 0x083af3b520000000 0xe3ffffffc0000001 0xf8fffffff0000000

def z1126 : W := mkw 0x245fca5fc437493d 0x4917f297f10dd24f 0x081fc01fc07fc01c 0x8207f007f01ff007

def z1127 : W := mkw 0x13b435a03bc836c2 0x04ed0d680ef20db0 0xffffffe03fffffe3 0xfffffff80ffffff8

def z1128 : W := mkw 0x0bb4300b795c2d19 0x82ed0c02de570b46 0xdffff01fffffff1f 0xf7fffc07ffffffc7

def z1129 : W := mkw 0x23fffeddb9000000 0x08ffffb76e400000 0xe3ffffffd1800001 0xf8fffffff4600000

def z1130 : W := mkw 0x0bb4b00b705c2d19 0x82ed2c02dc170b46 0xcf3cf01ff07c3f1f 0xb3cf3c07fc1f0fc7

def z1131 : W := mkw 0x0ba03482705c2d19 0x82e80d209c170b46 0xefe03fe0307c3f1f 0x7bf80ff80c1f0fc7

def z1132 : W := mkw 0x20017edd80000000 0x08005fb760000000 0x6023ffffc0000001 0x5808fffff0000000

def z1133 : W := mkw 0x0b14b00b705cad19 0x82c52c02dc172b46 0xcf1cf01ff07cff1f 0xb3c73c07fc1f3fc7

def z1134 : W := mkw 0x23fffedd80010024 0x08ffffb760004009 0xffffffffd18fc0ff 0xfffffffff463f03f

def z1135 : W := mkw 0x23017eddb0002400 0x08c05fb76c000900 0xe7003ffff0003f03 0x39c00ffffc000fc0

def z1136 : W := mkw 0x2015fedd80000000 0x08057fb760000000 0x6004ffffc0000001 0x18013ffff0000000

def z1137 : W := mkw 0x204b7edd80000000 0x0812dfb760000000 0x62d83fffc0000001 0x18b60ffff0000000

def z1138 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x193fc0003fffc002 0x864ff0000ffff000

def z1139 : W := mkw 0x1bb435a93bc836c2 0x86ed0d6a4ef20db0 0xf7e03fe03f803fe3 0x7df80ff80fe00ff8

def z1140 : W := mkw 0x205ffedd80000000 0x0817ffb760000000 0x60183fffc0000001 0x18060ffff0000000

def z1141 : W := mkw 0x20017edd80000000 0x08005fb760000000 0xe2c03fffc0000001 0x78b00ffff0000000

def z1142 : W := mkw 0x0bb4b00b795cad19 0x82ed2c02de572b46 0xdffcf01ffffcff1f 0xf7ff3c07ffff3fc7

def z1143 : W := mkw 0x031400003d6a8000 0x00c500000f5aa000 0x9b3fc0003fffc002 0xe6cff0000ffff000

def z1144 : W := mkw 0x04010b16021118b5 0x410042c58084462d 0xfed82f1e2e7038ff 0xffb60bc78b9c0e3f

def z1145 : W := mkw 0x000000003d6a8000 0x000000000f5aa000 0x1823c0003fffc002 0x4608f0000ffff000

def z1146 : W := mkw 0x044b4b56863318b5 0x4112d2d5a18cc62d 0xfedfef1fee7338ff 0xffb7fbc7fb9cce3f

def z1147 : W := mkw 0x20a1fedd80000000 0x08287fb760000000 0x6020ffffc0000001 0x18083ffff0000000

def z1148 : W := mkw 0x23fe86843d6a8000 0x08ffa1a10f5aa000 0x9bffc7003fffc002 0xe6fff1c00ffff000

def z1149 : W := mkw 0x20ffcedd80000000 0x083ff3b760000000 0xe2ffefffc0000001 0xf8bffbfff0000000

def z1150 : W := mkw 0x03fe80003d6a8000 0x00ffa0000f5aa000 0x9fffc0103fffc01f 0xe7fff0040ffff007

def z1151 : W := mkw 0x0314300b40140919 0x00c50c02d0050246 0xcf1c301ff07c3f1f 0xb3c70c07fc1f0fc7

def z1152 : W := mkw 0x23fef6cdbd6a8000 0x08ffbdb36f5aa000 0xdbfff7efffffc002 0xf6fffdfbfffff000

def z1153 : W := mkw 0x20017edd80000000 0x08005fb760000000 0xe1043fffc0000001 0xb8410ffff0000000

def z1154 : W := mkw 0x044b0b16063318b5 0x4112c2c5818cc62d 0x7edb2f0e2e7338fe 0x5fb6cbc38b9cce3f

def z1155 : W := mkw 0x00fe80003d6a8000 0x003fa0000f5aa000 0x18ffc0003fffc002 0xc63ff0000ffff000

def z1156 : W := mkw 0x004b0b1602101891 0x0012c2c580840624 0xfedb2f1e2e7038ff 0xffb6cbc78b9c0e3f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z7,z2,z8,z5,z6]),(0,[z0,z1,z2,z4,z5,z9,z6])],[(1,[z0,z1,z2,z4,z5,z10]),(0,[z0,z1,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z12,z13]),(0,[z0,z1,z7,z8,z4,z5,z6])],[(0,[z0,z1,z2,z14,z4,z5,z6]),(0,[z0,z15,z1,z2,z4,z5,z6])],[(0,[z16,z0,z1,z2,z4,z5,z6]),(0,[z0,z17,z1,z2,z4,z5,z6]),(0,[z0,z18,z1,z2,z4,z5,z19])],[(0,[z0,z1,z2,z4,z5,z20,z6]),(0,[z0,z1,z2,z21,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z22]),(0,[z0,z1,z2,z4,z5,z6,z23])],[(0,[z0,z1,z24,z25,z4,z5,z6]),(0,[z0,z1,z26,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z27,z5,z6]),(0,[z0,z1,z2,z4,z5,z13,z28])],[(0,[z0,z1,z2,z29,z4,z5,z6]),(0,[z30,z0,z18,z1,z2,z4,z5]),(0,[z0,z1,z31,z2,z4,z5,z6]),(0,[z32,z0,z1,z7,z4,z5,z6]),(0,[z0,z33,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z34,z6])],[(0,[z0,z35,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z36,z5,z6]),(0,[z0,z37,z1,z2,z4,z5,z6]),(0,[z0,z38,z1,z2,z4,z39,z6]),(0,[z0,z1,z2,z40,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z41]),(0,[z0,z1,z42,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z43,z4,z5,z6]),(0,[z44,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z45,z5,z6]),(0,[z46,z0,z1,z2,z4,z5,z6]),(0,[z0,z47,z2,z4,z5,z6,z48]),(0,[z0,z1,z49,z2,z4,z5,z6])],[(0,[z50,z0,z2,z4,z5,z6,z48]),(0,[z0,z1,z2,z4,z5,z51,z6]),(0,[z0,z1,z2,z4,z5,z48,z52]),(0,[z32,z0,z1,z2,z53,z5,z6]),(0,[z54,z0,z1,z2,z4,z5,z6])],[(0,[z55,z0,z1,z2,z4,z5,z6]),(0,[z56,z0,z1,z2,z4,z5,z6])],[(0,[z0,z57,z1,z2,z4,z5,z6]),(0,[z0,z38,z1,z25,z4,z5,z6]),(0,[z0,z58,z2,z4,z5,z6,z48]),(0,[z0,z59,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z19,z6]),(0,[z0,z1,z2,z4,z5,z6,z60])],[(0,[z0,z61,z2,z4,z5,z62,z6]),(0,[z0,z1,z63,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z64,z5,z65])],[(0,[z0,z1,z66,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z67]),(0,[z0,z1,z2,z4,z5,z62,z48]),(0,[z0,z1,z2,z4,z5,z6,z68]),(0,[z0,z1,z2,z69,z4,z5,z70]),(0,[z0,z1,z2,z4,z5,z28,z71])],[(1,[z0,z1,z2,z4,z72,z6]),(0,[z0,z1,z2,z73,z4,z5,z6]),(0,[z74,z0,z1,z2,z4,z5,z6]),(0,[z0,z75,z1,z2,z4,z5,z6]),(0,[z76,z0,z1,z2,z4,z5,z6])],[(0,[z0,z77,z1,z2,z4,z5,z6]),(0,[z78,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z79,z2,z4,z5,z6]),(0,[z80,z0,z1,z2,z4,z62,z6]),(0,[z0,z58,z1,z2,z4,z81,z6])]],
   [[(1,[z0,z1,z2,z4,z5,z82]),(0,[z0,z1,z2,z4,z5,z48,z70]),(0,[z0,z1,z2,z4,z83,z5,z6])],[(0,[z0,z1,z2,z84,z85,z5,z6]),(1,[z0,z1,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z48,z86]),(1,[z0,z87,z2,z4,z5,z6]),(0,[z0,z1,z2,z69,z4,z5,z28])],[(0,[z0,z1,z2,z88,z4,z5,z6]),(0,[z0,z1,z2,z84,z4,z5,z13]),(0,[z80,z0,z1,z2,z4,z5,z6]),(0,[z89,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z90,z4,z5,z19])],[(0,[z0,z1,z2,z91,z92,z5,z6]),(0,[z0,z1,z2,z93,z4,z5,z6]),(0,[z0,z1,z2,z94,z4,z5,z6]),(0,[z0,z95,z1,z2,z4,z5,z6]),(0,[z0,z1,z8,z4,z96,z5,z6]),(0,[z0,z1,z2,z4,z5,z97,z6]),(0,[z0,z1,z2,z4,z98,z5,z6])],[(0,[z0,z1,z2,z4,z72,z5,z6]),(0,[z99,z0,z1,z2,z4,z5,z100]),(0,[z0,z1,z2,z101,z4,z5,z6]),(0,[z0,z102,z1,z2,z4,z5,z6]),(0,[z0,z1,z103,z2,z4,z5,z6]),(0,[z104,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z105,z6]),(0,[z1,z2,z4,z106,z5,z107,z6])],[(0,[z108,z0,z1,z109,z4,z5,z6]),(0,[z0,z1,z110,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z13,z48]),(0,[z111,z0,z1,z2,z4,z5,z6]),(1,[z112,z0,z2,z4,z5,z13])],[(0,[z113,z0,z1,z2,z4,z106,z6]),(0,[z0,z1,z2,z4,z5,z114,z6]),(0,[z0,z1,z2,z4,z85,z5,z6]),(0,[z0,z115,z1,z2,z4,z5,z6]),(0,[z0,z1,z7,z2,z91,z5,z6]),(0,[z0,z1,z2,z116,z4,z5,z6]),(0,[z0,z117,z1,z2,z4,z64,z6])]],
   [[(0,[z0,z1,z2,z118,z4,z5,z6]),(0,[z0,z2,z91,z4,z85,z5,z6]),(0,[z0,z1,z119,z2,z4,z5,z6]),(0,[z0,z1,z2,z120,z4,z5,z6]),(0,[z0,z1,z4,z5,z121,z122,z6]),(0,[z0,z1,z2,z4,z5,z123,z122])],[(0,[z124,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z62,z122,z6])],[(0,[z0,z1,z125,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z126,z5,z6]),(0,[z0,z127,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z128,z6]),(0,[z80,z0,z1,z2,z4,z5,z13]),(0,[z0,z129,z1,z2,z4,z5,z6]),(0,[z0,z1,z130,z2,z4,z5,z6])],[(0,[z0,z131,z1,z2,z4,z5,z6]),(0,[z108,z0,z1,z24,z4,z5,z6]),(1,[z0,z132,z1,z2,z4,z5]),(0,[z0,z133,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z134,z6]),(0,[z135,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z136,z5,z6])],[(1,[z0,z1,z2,z137,z5,z6]),(0,[z138,z0,z1,z2,z4,z5,z6])],[(0,[z139,z0,z1,z2,z140,z5,z6]),(0,[z0,z1,z2,z137,z4,z5,z6]),(0,[z0,z1,z2,z141,z85,z5,z6]),(0,[z0,z1,z142,z2,z4,z5,z6]),(0,[z112,z0,z2,z4,z5,z62,z6]),(0,[z0,z1,z143,z2,z4,z81,z6]),(0,[z0,z1,z1,z2,z4,z5,z13])],[(0,[z0,z1,z2,z4,z5,z6,z144]),(0,[z0,z1,z2,z4,z81,z5,z13]),(0,[z0,z1,z2,z4,z5,z6,z145])],[(0,[z146,z0,z1,z2,z4,z5,z6]),(0,[z50,z131,z1,z2,z4,z5,z6]),(0,[z147,z0,z1,z2,z141,z5,z6]),(0,[z0,z1,z2,z4,z5,z148,z6]),(0,[z0,z1,z149,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z85,z5,z13])]],
   [[(0,[z139,z0,z1,z2,z4,z150,z6]),(0,[z0,z1,z2,z4,z5,z151,z6]),(0,[z0,z1,z2,z91,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z152,z6])],[(0,[z108,z0,z1,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z153,z5,z6]),(0,[z30,z1,z2,z4,z5,z154,z6]),(1,[z0,z1,z2,z4,z151,z6]),(0,[z0,z1,z2,z4,z5,z155,z6]),(1,[z0,z1,z2,z4,z5,z156]),(0,[z0,z1,z2,z4,z157,z5,z6]),(0,[z0,z117,z1,z2,z69,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z71])],[(0,[z0,z158,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z92,z85,z5,z6]),(0,[z0,z1,z2,z4,z159,z5,z6]),(0,[z0,z1,z2,z4,z5,z160,z6]),(0,[z0,z161,z1,z2,z4,z5,z6])],[(0,[z0,z131,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z162,z6]),(0,[z0,z1,z2,z163,z4,z5,z6]),(0,[z164,z0,z1,z2,z4,z5,z6])],[(0,[z165,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z166]),(0,[z0,z1,z2,z4,z5,z167,z6]),(0,[z0,z2,z4,z81,z5,z62,z6])],[(1,[z0,z1,z168,z4,z5,z6]),(0,[z0,z1,z142,z2,z4,z5,z13]),(0,[z0,z169,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z48,z48]),(0,[z0,z170,z1,z2,z4,z171,z6]),(0,[z0,z1,z2,z69,z5,z122,z6]),(0,[z0,z1,z172,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z173,z6]),(0,[z0,z1,z2,z4,z5,z174,z6]),(0,[z0,z1,z2,z4,z5,z175,z6]),(0,[z0,z176,z1,z2,z4,z5,z6]),(0,[z177,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z178]),(0,[z112,z0,z2,z4,z5,z13,z6])],[(0,[z50,z0,z1,z2,z4,z5,z48]),(0,[z108,z99,z1,z2,z4,z5,z6]),(0,[z0,z179,z1,z2,z4,z5,z6]),(0,[z30,z180,z1,z2,z4,z5,z6]),(0,[z0,z181,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z182,z48]),(0,[z0,z1,z2,z4,z5,z122,z6])]],
   [[(0,[z0,z1,z2,z4,z183,z5,z6]),(1,[z147,z1,z2,z92,z5,z6]),(0,[z0,z1,z2,z184,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z185,z6])],[(0,[z186,z0,z1,z2,z4,z5,z6]),(0,[z180,z0,z1,z2,z4,z5,z48]),(0,[z0,z61,z1,z2,z4,z5,z152]),(0,[z0,z1,z2,z187,z4,z5,z6]),(0,[z0,z1,z8,z4,z53,z5,z6]),(0,[z0,z1,z2,z188,z4,z5,z6]),(0,[z0,z1,z143,z4,z96,z5,z6])],[(0,[z139,z0,z1,z2,z4,z5,z189]),(0,[z0,z1,z190,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z191,z5,z6]),(0,[z0,z1,z192,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z48,z193]),(0,[z0,z1,z2,z4,z5,z194,z6]),(0,[z0,z1,z2,z4,z5,z13,z195]),(0,[z0,z1,z2,z4,z196,z5,z6])],[(0,[z0,z1,z2,z4,z5,z197,z6]),(0,[z0,z2,z4,z5,z154,z198,z6]),(0,[z0,z1,z2,z4,z5,z6,z199]),(0,[z0,z1,z2,z4,z200,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z201])],[(0,[z0,z1,z2,z4,z171,z62,z6]),(1,[z0,z1,z7,z8,z5,z6]),(0,[z0,z1,z2,z4,z202,z5,z6])],[(0,[z203,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z204,z5,z6]),(0,[z0,z169,z1,z2,z4,z5,z13]),(0,[z205,z0,z1,z2,z4,z5,z48]),(0,[z0,z206,z1,z2,z4,z5,z6]),(0,[z0,z18,z1,z90,z4,z5,z6])],[(0,[z0,z207,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z28,z48])],[(0,[z99,z0,z1,z109,z4,z5,z6]),(0,[z0,z1,z208,z2,z4,z5,z6]),(0,[z0,z1,z209,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z122,z13]),(0,[z210,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z171,z5,z6]),(0,[z0,z1,z2,z4,z5,z70,z71])]],
   [[(0,[z211,z0,z1,z2,z4,z5,z48]),(0,[z46,z0,z1,z143,z2,z4,z6]),(0,[z0,z212,z1,z2,z4,z5,z6]),(0,[z0,z61,z1,z2,z4,z5,z48]),(0,[z0,z170,z1,z2,z4,z5,z48]),(0,[z0,z1,z2,z213,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z214,z6]),(0,[z215,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z216]),(0,[z0,z217,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z218,z5,z6]),(0,[z0,z219,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z51]),(0,[z220,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z221]),(0,[z0,z1,z2,z4,z64,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z222])],[(0,[z0,z1,z190,z2,z4,z5,z13]),(0,[z0,z223,z1,z2,z4,z5,z82]),(0,[z0,z1,z2,z85,z5,z122,z6]),(0,[z0,z1,z2,z4,z224,z5,z6])],[(0,[z0,z223,z1,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z225,z6]),(0,[z0,z1,z2,z4,z5,z13,z226]),(0,[z0,z227,z228,z2,z4,z5,z6])],[(0,[z99,z0,z1,z24,z4,z5,z6]),(0,[z0,z227,z1,z2,z5,z6,z70]),(0,[z0,z229,z1,z2,z4,z5,z6])],[(0,[z230,z0,z1,z2,z4,z5,z6])],[(0,[z231,z0,z1,z2,z4,z5,z6]),(1,[z232,z0,z2,z4,z5,z6]),(0,[z0,z1,z233,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z234,z5,z13]),(0,[z0,z1,z2,z4,z5,z121,z6])],[(0,[z0,z1,z2,z4,z235,z5,z6]),(0,[z113,z0,z1,z2,z4,z5,z6]),(1,[z180,z1,z2,z4,z5,z236]),(0,[z237,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z238,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z239,z6])]],
   [[(0,[z0,z1,z240,z2,z4,z5,z6]),(1,[z0,z66,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z241,z6]),(0,[z0,z1,z2,z4,z242,z5,z6]),(0,[z0,z1,z90,z2,z4,z5,z6])],[(0,[z1,z2,z141,z4,z92,z5,z6]),(0,[z0,z1,z2,z4,z81,z106,z6]),(1,[z0,z2,z4,z5,z198,z6]),(0,[z0,z1,z2,z4,z243,z5,z6]),(0,[z0,z244,z1,z2,z4,z5,z6]),(1,[z0,z245,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z246])],[(0,[z247,z0,z1,z2,z4,z5,z6]),(0,[z99,z0,z1,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z248,z6]),(0,[z0,z249,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z25,z4,z5,z48]),(0,[z0,z61,z1,z2,z136,z5,z6]),(1,[z0,z61,z2,z4,z62,z6]),(0,[z32,z0,z1,z2,z4,z5,z48]),(0,[z0,z250,z227,z2,z4,z5,z6])],[(0,[z112,z50,z0,z2,z4,z5,z6]),(0,[z0,z1,z109,z2,z4,z5,z48]),(0,[z0,z1,z2,z8,z4,z5,z48])],[(0,[z0,z1,z2,z251,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z252,z6])],[(1,[z0,z1,z2,z140,z5,z6]),(0,[z180,z0,z1,z168,z4,z5,z6]),(0,[z0,z18,z1,z2,z4,z5,z48]),(0,[z0,z1,z253,z2,z4,z5,z6])],[(0,[z32,z0,z1,z2,z8,z5,z6])],[(0,[z113,z0,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z6,z254]),(0,[z0,z1,z7,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z255,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z150,z6]),(0,[z180,z0,z18,z1,z2,z4,z5])],[(0,[z0,z1,z2,z256,z4,z5,z6]),(0,[z0,z257,z1,z2,z4,z5,z6]),(1,[z0,z2,z4,z5,z13,z48]),(0,[z112,z0,z1,z2,z4,z5,z48]),(0,[z0,z1,z2,z258,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z259])],[(0,[z0,z1,z2,z4,z5,z260,z6]),(0,[z0,z1,z2,z4,z261,z5,z6]),(0,[z0,z227,z1,z2,z4,z64,z5])],[(0,[z0,z262,z1,z2,z4,z5,z6]),(0,[z80,z0,z1,z2,z4,z81,z6]),(0,[z0,z1,z2,z4,z263,z5,z6]),(0,[z0,z1,z2,z4,z264,z5,z6])],[(0,[z0,z265,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z107,z6]),(0,[z0,z1,z266,z2,z4,z5,z6]),(0,[z0,z267,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z268,z48]),(0,[z0,z1,z2,z4,z5,z13,z70]),(0,[z0,z1,z2,z4,z5,z6,z269]),(0,[z0,z227,z1,z2,z69,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z270])],[(0,[z0,z1,z2,z4,z271,z5,z6]),(0,[z0,z47,z2,z4,z5,z62,z6]),(0,[z0,z1,z2,z272,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z273])],[(1,[z0,z1,z2,z4,z5,z173]),(0,[z0,z1,z2,z4,z92,z5,z6]),(1,[z0,z1,z274,z4,z5,z6]),(0,[z0,z1,z2,z4,z275,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z276]),(0,[z0,z38,z1,z2,z4,z5,z67]),(0,[z0,z277,z1,z2,z4,z5,z6]),(1,[z0,z47,z2,z4,z5,z48])],[(0,[z0,z1,z2,z278,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z13,z279]),(0,[z0,z170,z1,z2,z4,z122,z6])]],
   [[(0,[z0,z1,z280,z2,z4,z5,z6]),(0,[z0,z281,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z106,z5,z48]),(0,[z0,z1,z2,z4,z5,z19,z154]),(0,[z0,z1,z2,z282,z4,z5,z6])],[(0,[z283,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z284,z5,z6]),(0,[z0,z1,z90,z2,z4,z5,z19])],[(1,[z0,z1,z2,z4,z5,z189]),(1,[z0,z1,z2,z4,z5,z285]),(0,[z0,z38,z1,z2,z4,z5,z48]),(0,[z0,z286,z1,z2,z4,z5,z6])],[(0,[z287,z0,z1,z2,z4,z5,z6]),(0,[z288,z0,z1,z2,z4,z5,z6]),(0,[z0,z289,z1,z2,z4,z5,z6]),(0,[z0,z117,z1,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z290,z6]),(0,[z0,z117,z1,z2,z291,z5,z6])],[(0,[z0,z1,z2,z4,z5,z107,z13]),(0,[z0,z1,z2,z292,z4,z5,z6]),(0,[z0,z293,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z294,z5,z6]),(0,[z0,z1,z2,z84,z4,z5,z6]),(1,[z0,z1,z2,z4,z83,z6])],[(0,[z147,z1,z2,z4,z92,z5,z6]),(0,[z0,z1,z2,z4,z92,z5,z13]),(0,[z0,z223,z1,z2,z91,z5,z6])],[(0,[z30,z0,z1,z2,z4,z5,z236]),(0,[z0,z1,z2,z4,z5,z295,z6]),(0,[z0,z1,z296,z2,z4,z5,z6]),(0,[z0,z170,z1,z2,z84,z5,z6]),(0,[z0,z297,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z298,z6]),(0,[z0,z1,z2,z4,z299,z5,z6]),(1,[z0,z172,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z300]),(0,[z0,z1,z2,z4,z5,z6,z301]),(0,[z0,z18,z1,z2,z4,z5,z195]),(0,[z0,z1,z2,z69,z4,z5,z6]),(0,[z0,z227,z1,z2,z4,z5,z28]),(0,[z0,z1,z2,z4,z5,z65,z6]),(0,[z0,z1,z2,z4,z5,z6,z302])],[(0,[z0,z1,z303,z2,z4,z5,z6]),(0,[z0,z37,z1,z2,z4,z5,z48]),(0,[z0,z169,z2,z4,z5,z6,z48])],[(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z46,z0,z1,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z304,z6]),(0,[z0,z305,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z306,z6]),(0,[z307,z0,z1,z2,z4,z5,z6]),(0,[z0,z87,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z308]),(1,[z0,z38,z142,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z154,z6]),(0,[z32,z0,z1,z2,z91,z5,z6]),(0,[z0,z1,z2,z4,z309,z5,z6]),(0,[z0,z1,z310,z2,z4,z5,z6])],[(0,[z0,z37,z1,z25,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z311,z6]),(0,[z0,z58,z47,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z312,z5,z6]),(1,[z0,z58,z2,z4,z5,z48])],[(0,[z0,z313,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z311,z6]),(0,[z0,z1,z2,z4,z314,z5,z6]),(0,[z0,z1,z2,z4,z96,z5,z6])]],
   [[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z315,z1,z2,z4,z5,z6]),(0,[z108,z0,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z316,z4,z5,z6]),(0,[z0,z317,z1,z2,z4,z5,z6])],[(0,[z0,z318,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z141,z4,z5,z6]),(0,[z0,z1,z2,z4,z81,z5,z6]),(0,[z0,z1,z2,z4,z5,z319,z48]),(0,[z0,z1,z2,z69,z4,z5,z13]),(0,[z0,z1,z2,z4,z320,z5,z6])],[(0,[z0,z38,z1,z2,z4,z151,z6])],[(0,[z0,z1,z2,z4,z5,z321,z6]),(0,[z30,z0,z1,z2,z4,z5,z154]),(0,[z0,z37,z2,z25,z4,z5,z6]),(0,[z0,z1,z2,z322,z4,z5,z6]),(0,[z323,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z324,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z64,z5,z71])],[(0,[z0,z1,z2,z4,z325,z5,z6]),(0,[z0,z1,z2,z326,z4,z5,z6]),(0,[z0,z2,z4,z85,z5,z6,z48]),(0,[z0,z327,z1,z2,z4,z5,z6]),(1,[z0,z1,z4,z5,z121,z6]),(0,[z0,z1,z2,z4,z328,z5,z6]),(0,[z0,z117,z1,z2,z4,z6,z71])],[(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z0,z329,z1,z2,z4,z5,z6]),(0,[z330,z0,z1,z2,z4,z5,z6]),(0,[z0,z331,z1,z2,z4,z5,z6]),(0,[z0,z170,z332,z2,z4,z5,z6])],[(0,[z0,z1,z2,z333,z4,z5,z6]),(0,[z180,z0,z1,z274,z4,z5,z6]),(0,[z0,z334,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z335,z5,z6]),(0,[z0,z1,z2,z4,z5,z336,z6]),(0,[z0,z229,z117,z2,z4,z5,z6])],[(0,[z139,z0,z37,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z100]),(0,[z113,z0,z1,z143,z2,z4,z6]),(0,[z0,z337,z1,z2,z4,z5,z6]),(0,[z0,z58,z1,z2,z4,z5,z22]),(0,[z0,z1,z2,z4,z5,z22,z6]),(0,[z0,z1,z2,z4,z5,z48,z338]),(0,[z0,z1,z2,z4,z96,z5,z13]),(0,[z0,z1,z2,z4,z5,z339,z6])]],
   [[(0,[z340,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z341,z4,z5,z6]),(0,[z0,z1,z2,z4,z342,z5,z6]),(0,[z0,z1,z2,z4,z5,z123,z6])],[(0,[z343,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z141,z4,z5,z13]),(0,[z30,z0,z1,z2,z4,z5,z6]),(0,[z0,z37,z1,z2,z4,z5,z300]),(1,[z0,z47,z2,z91,z5,z6])],[(0,[z147,z0,z1,z2,z4,z5,z13]),(0,[z344,z0,z1,z2,z4,z5,z6]),(0,[z0,z47,z223,z2,z4,z5,z6]),(0,[z0,z227,z1,z2,z4,z5,z48]),(0,[z80,z0,z1,z8,z4,z5,z6]),(1,[z0,z1,z2,z224,z5,z6]),(0,[z0,z1,z2,z4,z5,z345,z6])],[(0,[z139,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z346,z2,z4,z5,z6]),(0,[z0,z1,z347,z2,z4,z5,z6]),(0,[z348,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z143,z2,z4,z12,z6]),(0,[z0,z1,z2,z349,z4,z5,z6])],[(0,[z0,z250,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z350,z5,z6])],[(0,[z32,z211,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z351,z6]),(0,[z0,z1,z2,z352,z4,z5,z6]),(0,[z0,z353,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z354,z5,z6]),(0,[z211,z1,z2,z141,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z355,z6]),(0,[z0,z1,z2,z4,z5,z6,z356])],[(0,[z211,z0,z1,z2,z141,z5,z6]),(0,[z0,z1,z2,z4,z5,z357,z6])]],
   [[(1,[z139,z190,z2,z4,z5,z6]),(0,[z358,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z359,z6])],[(0,[z139,z50,z1,z2,z4,z5,z6]),(0,[z30,z0,z1,z2,z4,z5,z13]),(1,[z0,z1,z2,z243,z5,z6]),(0,[z0,z47,z1,z2,z4,z5,z48]),(0,[z343,z0,z1,z2,z4,z5,z13])],[(0,[z0,z1,z2,z4,z360,z5,z6]),(0,[z0,z1,z209,z2,z4,z5,z6]),(0,[z0,z1,z2,z84,z5,z6,z70]),(0,[z361,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z140,z4,z5,z6]),(0,[z139,z0,z142,z2,z4,z5,z6]),(0,[z139,z0,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z6,z362])],[(1,[z211,z1,z2,z141,z5,z6]),(0,[z0,z1,z2,z4,z5,z363,z6]),(0,[z364,z0,z1,z2,z4,z5,z6]),(0,[z0,z58,z1,z2,z4,z5,z48])],[(0,[z0,z1,z2,z4,z365,z5,z6]),(0,[z366,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z53,z5,z6]),(0,[z0,z367,z1,z2,z4,z5,z6])],[(1,[z368,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z369,z5,z6])],[(0,[z139,z0,z131,z2,z4,z5,z6]),(0,[z99,z0,z1,z2,z4,z5,z173]),(0,[z1,z2,z4,z5,z154,z6,z236]),(0,[z370,z0,z1,z2,z4,z5,z13])]],
   [[(0,[z0,z371,z1,z2,z4,z5,z6]),(0,[z0,z372,z1,z2,z4,z5,z48]),(1,[z0,z1,z2,z84,z171,z6]),(0,[z0,z1,z2,z4,z5,z6,z70]),(1,[z0,z1,z2,z69,z5,z28])],[(0,[z99,z0,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z373,z4,z5,z6]),(0,[z0,z1,z2,z4,z234,z5,z6]),(0,[z0,z1,z2,z4,z64,z171,z6])],[(0,[z374,z0,z1,z2,z4,z5,z6]),(0,[z0,z375,z1,z2,z4,z5,z6]),(0,[z0,z376,z1,z2,z4,z5,z6]),(0,[z112,z0,z2,z4,z85,z5,z6]),(0,[z0,z1,z2,z8,z4,z5,z13]),(0,[z0,z1,z2,z377,z4,z5,z6]),(0,[z0,z378,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z24,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z379,z6]),(1,[z0,z1,z2,z4,z5,z380])],[(0,[z0,z1,z2,z381,z4,z5,z6]),(0,[z30,z0,z1,z90,z2,z4,z5]),(0,[z0,z142,z2,z25,z4,z5,z6])],[(0,[z0,z382,z1,z2,z4,z5,z6]),(0,[z0,z1,z7,z2,z85,z5,z6]),(0,[z0,z1,z2,z4,z53,z5,z13])],[(0,[z0,z1,z2,z4,z383,z5,z6]),(0,[z0,z1,z2,z4,z5,z13,z236]),(0,[z0,z1,z2,z384,z4,z5,z6]),(0,[z0,z1,z7,z2,z4,z5,z13]),(0,[z385,z0,z1,z2,z4,z5,z6]),(0,[z0,z170,z1,z2,z5,z122,z6])],[(1,[z0,z1,z2,z4,z5,z386]),(0,[z387,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z143,z2,z4,z96,z6])]],
   [[(0,[z139,z0,z190,z2,z4,z5,z6]),(0,[z388,z0,z1,z2,z4,z5,z6]),(0,[z0,z389,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z136,z4,z5,z6]),(0,[z112,z0,z1,z2,z4,z5,z13]),(0,[z0,z390,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z391])],[(0,[z0,z1,z2,z392,z4,z5,z6]),(0,[z0,z393,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z28,z6,z70])],[(0,[z0,z1,z143,z2,z4,z5,z48]),(0,[z394,z0,z1,z2,z4,z5,z6])],[(0,[z0,z395,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z396,z4,z5,z6]),(1,[z0,z2,z4,z5,z62,z48]),(0,[z0,z1,z2,z397,z4,z5,z6]),(0,[z398,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z399,z5,z6]),(0,[z0,z400,z1,z2,z4,z5,z6])],[(1,[z113,z1,z2,z4,z107,z6]),(0,[z0,z58,z1,z2,z4,z5,z156]),(0,[z0,z1,z2,z4,z64,z5,z48]),(0,[z0,z401,z1,z2,z4,z5,z6])],[(0,[z0,z1,z402,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z403]),(0,[z404,z0,z1,z2,z4,z5,z6])],[(0,[z405,z0,z1,z2,z4,z5,z6]),(0,[z147,z211,z1,z2,z4,z5,z6]),(0,[z0,z1,z406,z2,z4,z5,z6])],[(0,[z0,z407,z1,z2,z4,z5,z6]),(0,[z0,z1,z408,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z106,z5,z13]),(0,[z0,z409,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z410,z6]),(0,[z0,z411,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z14,z5,z6]),(0,[z0,z1,z2,z412,z4,z5,z6]),(0,[z413,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z414,z2,z4,z5,z6])],[(0,[z415,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z416,z5,z6]),(0,[z0,z38,z142,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z417,z5,z6])],[(0,[z0,z1,z2,z4,z5,z150,z6]),(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z418,z1,z2,z4,z5,z6]),(0,[z0,z1,z419,z2,z4,z5,z6]),(0,[z0,z420,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z421,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z422,z2,z4,z5,z6]),(0,[z0,z423,z1,z2,z4,z5,z6]),(0,[z0,z1,z90,z2,z4,z5,z48]),(0,[z0,z1,z2,z397,z4,z5,z13])],[(0,[z0,z1,z2,z4,z5,z424,z6]),(0,[z0,z1,z2,z4,z5,z6,z82]),(1,[z0,z1,z2,z4,z5,z425]),(0,[z0,z47,z1,z2,z91,z5,z6]),(0,[z0,z1,z2,z4,z5,z426,z6]),(0,[z0,z427,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z428,z4,z5,z6]),(0,[z0,z1,z2,z429,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z48,z236]),(0,[z0,z37,z1,z2,z4,z5,z10]),(0,[z430,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z431,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z48]),(0,[z432,z0,z1,z2,z4,z5,z6])],[(0,[z139,z0,z1,z2,z383,z5,z6]),(0,[z0,z1,z2,z433,z4,z5,z6]),(0,[z434,z0,z1,z2,z4,z5,z6]),(0,[z435,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z436,z6]),(0,[z437,z0,z1,z2,z4,z5,z6]),(0,[z46,z0,z1,z2,z4,z107,z6]),(1,[z0,z1,z2,z314,z5,z6]),(0,[z0,z1,z2,z4,z5,z62,z13]),(0,[z0,z438,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z439,z6]),(0,[z0,z1,z2,z4,z5,z12,z48]),(0,[z0,z1,z2,z4,z5,z440,z6]),(1,[z0,z117,z1,z2,z4,z71])]],
   [[(0,[z0,z441,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z442,z5,z6]),(0,[z0,z1,z2,z4,z5,z13,z6])],[(0,[z180,z0,z1,z2,z4,z5,z236]),(0,[z0,z47,z1,z2,z4,z5,z51]),(0,[z80,z0,z1,z2,z4,z12,z6]),(0,[z0,z1,z443,z2,z4,z5,z6])],[(0,[z444,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z193]),(0,[z0,z1,z2,z91,z84,z5,z6]),(0,[z0,z445,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z446,z4,z5,z6]),(1,[z108,z1,z109,z4,z5,z6]),(0,[z447,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z13]),(0,[z448,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z171,z6,z71])],[(0,[z0,z1,z2,z4,z5,z449,z6]),(0,[z450,z0,z1,z2,z4,z5,z6])],[(0,[z451,z0,z1,z2,z4,z5,z6]),(1,[z30,z1,z2,z4,z5,z154]),(0,[z452,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z84,z4,z171,z6])],[(0,[z0,z453,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z454,z6]),(0,[z0,z1,z455,z2,z4,z5,z6]),(0,[z0,z245,z1,z2,z4,z5,z122]),(0,[z0,z1,z456,z2,z4,z5,z6])],[(0,[z0,z1,z2,z137,z24,z5,z6]),(0,[z0,z1,z2,z4,z457,z5,z6]),(0,[z0,z1,z2,z458,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z459,z6])]],
   [[(0,[z460,z0,z1,z2,z4,z5,z6]),(0,[z139,z0,z2,z4,z5,z6,z48]),(0,[z0,z1,z2,z461,z4,z5,z6]),(0,[z147,z0,z1,z2,z92,z5,z6]),(0,[z0,z1,z2,z4,z5,z13,z13]),(0,[z0,z1,z2,z4,z5,z6,z462]),(0,[z0,z227,z1,z2,z4,z5,z70])],[(0,[z0,z463,z1,z2,z4,z5,z6])],[(0,[z464,z0,z1,z2,z4,z5,z6]),(0,[z465,z0,z1,z2,z4,z5,z6]),(0,[z0,z61,z1,z2,z4,z5,z380])],[(0,[z108,z0,z1,z2,z4,z5,z6]),(0,[z113,z46,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z27,z5,z48]),(0,[z447,z0,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z64,z122,z6])],[(0,[z0,z466,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z467,z6]),(0,[z0,z1,z2,z4,z65,z6,z71]),(0,[z468,z0,z1,z2,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(1,[z50,z131,z2,z4,z5,z6]),(0,[z50,z0,z37,z2,z4,z5,z6]),(0,[z469,z0,z1,z2,z4,z5,z6]),(0,[z211,z0,z1,z2,z92,z5,z6]),(0,[z0,z1,z470,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z156])],[(0,[z0,z1,z2,z4,z5,z236,z195]),(0,[z0,z1,z2,z4,z471,z5,z6]),(0,[z0,z1,z2,z4,z472,z5,z6]),(0,[z0,z1,z2,z5,z122,z6,z70])],[(0,[z0,z1,z2,z4,z473,z5,z6]),(0,[z0,z1,z2,z4,z5,z474,z6]),(0,[z0,z1,z2,z4,z475,z5,z6]),(0,[z0,z1,z90,z2,z4,z5,z195]),(0,[z0,z476,z1,z2,z4,z5,z6]),(0,[z0,z170,z1,z2,z4,z5,z391])]],
   [[(0,[z147,z0,z1,z7,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z477]),(0,[z0,z1,z478,z2,z4,z5,z6]),(0,[z0,z58,z61,z2,z4,z5,z6]),(0,[z0,z1,z2,z84,z4,z5,z48]),(0,[z0,z479,z1,z2,z4,z5,z6])],[(0,[z50,z0,z1,z2,z4,z5,z6]),(1,[z50,z0,z2,z4,z5,z48]),(0,[z147,z32,z0,z1,z2,z5,z6]),(0,[z480,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z85,z5,z62,z6]),(0,[z0,z1,z2,z4,z81,z171,z6]),(0,[z0,z1,z2,z4,z5,z182,z6]),(0,[z0,z1,z2,z4,z5,z19,z48]),(0,[z0,z1,z2,z4,z481,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z195]),(0,[z0,z1,z2,z4,z5,z6,z482])],[(0,[z139,z0,z1,z2,z4,z5,z386]),(0,[z0,z1,z483,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z484,z6]),(0,[z0,z1,z4,z96,z5,z12,z6]),(0,[z0,z485,z1,z2,z4,z5,z6]),(1,[z76,z0,z1,z4,z5,z6])],[(0,[z486,z0,z1,z2,z4,z5,z6])],[(0,[z0,z487,z1,z2,z4,z5,z6]),(0,[z0,z488,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z489,z6]),(0,[z0,z117,z1,z2,z224,z5,z6]),(0,[z490,z0,z1,z2,z4,z5,z6])],[(1,[z469,z0,z1,z2,z4,z6]),(0,[z147,z0,z1,z2,z4,z5,z6]),(0,[z0,z491,z1,z2,z4,z5,z6]),(0,[z80,z0,z1,z2,z4,z96,z6]),(0,[z492,z0,z1,z2,z4,z5,z6]),(0,[z493,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z494,z2,z4,z5]),(0,[z0,z1,z494,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z279,z6]),(1,[z0,z170,z1,z2,z122,z6]),(1,[z0,z1,z2,z4,z5,z123]),(0,[z0,z227,z1,z2,z4,z83,z6])],[(1,[z99,z1,z24,z4,z5,z6]),(0,[z0,z47,z1,z2,z85,z5,z6]),(0,[z0,z61,z1,z2,z4,z62,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z495,z6]),(0,[z0,z1,z2,z4,z5,z154,z48]),(0,[z0,z496,z1,z2,z4,z5,z6]),(0,[z80,z0,z1,z2,z4,z5,z48]),(0,[z0,z497,z1,z2,z4,z5,z6])],[(0,[z50,z0,z142,z2,z4,z5,z6]),(0,[z50,z0,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z308,z6]),(0,[z0,z95,z1,z2,z4,z5,z48])],[(0,[z498,z0,z1,z2,z4,z5,z6]),(0,[z211,z0,z1,z2,z4,z5,z6]),(0,[z0,z38,z1,z2,z243,z5,z6]),(0,[z0,z61,z1,z2,z4,z5,z6]),(0,[z112,z0,z169,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z226]),(0,[z0,z170,z1,z2,z4,z5,z6])],[(0,[z180,z0,z1,z2,z4,z5,z13]),(0,[z0,z47,z2,z91,z4,z5,z6]),(0,[z0,z1,z1,z2,z4,z5,z48]),(0,[z486,z0,z1,z2,z4,z5,z13]),(0,[z499,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z500,z6]),(0,[z0,z1,z2,z4,z501,z5,z6])],[(0,[z0,z502,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z126,z6]),(0,[z0,z1,z2,z4,z81,z5,z48]),(0,[z503,z0,z1,z2,z4,z5,z13]),(0,[z0,z1,z4,z5,z19,z6,z195]),(1,[z0,z1,z2,z4,z500,z6]),(0,[z0,z1,z2,z4,z5,z6,z504]),(0,[z0,z505,z1,z2,z4,z5,z6])],[(0,[z0,z1,z142,z24,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z506,z6]),(0,[z0,z1,z2,z4,z507,z5,z6]),(0,[z0,z508,z1,z2,z4,z5,z6]),(0,[z0,z223,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z85,z5,z48]),(0,[z0,z1,z2,z4,z509,z5,z6]),(0,[z0,z1,z2,z510,z4,z5,z6])],[(1,[z0,z1,z2,z383,z5,z6]),(1,[z139,z0,z2,z4,z5,z48]),(0,[z0,z61,z1,z2,z314,z5,z6]),(0,[z0,z1,z2,z4,z5,z13,z65]),(0,[z511,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z512,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z513,z6]),(0,[z0,z223,z2,z4,z85,z5,z6])]],
   [[(0,[z0,z1,z514,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z515])],[(0,[z0,z131,z1,z2,z4,z5,z48]),(0,[z0,z516,z1,z2,z4,z5,z6]),(0,[z0,z517,z1,z2,z4,z5,z6]),(0,[z0,z1,z518,z2,z4,z5,z6])],[(0,[z370,z0,z1,z2,z4,z5,z6]),(0,[z211,z0,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z6,z519]),(0,[z0,z61,z1,z2,z4,z5,z13]),(0,[z0,z170,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z520,z6])],[(0,[z0,z1,z2,z521,z4,z5,z6]),(0,[z108,z1,z109,z2,z4,z5,z6]),(0,[z0,z1,z142,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z522,z6]),(0,[z0,z1,z2,z4,z5,z523,z6])],[(0,[z0,z1,z2,z4,z5,z6,z52]),(0,[z99,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z25,z4,z5,z6]),(0,[z0,z223,z1,z2,z85,z5,z6]),(0,[z0,z1,z2,z4,z5,z524,z6]),(0,[z0,z525,z1,z2,z4,z5,z6])],[(0,[z0,z1,z109,z2,z4,z5,z6]),(0,[z0,z223,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z8,z4,z5,z6]),(0,[z526,z0,z1,z2,z4,z5,z6])],[(0,[z50,z0,z190,z2,z4,z5,z6]),(0,[z180,z0,z1,z90,z2,z4,z5]),(0,[z0,z1,z2,z527,z4,z5,z6]),(0,[z0,z1,z2,z91,z4,z5,z48]),(0,[z0,z528,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z529,z6])],[(0,[z0,z1,z24,z4,z5,z6,z195]),(0,[z0,z18,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z84,z4,z122,z6])]],
   [[(0,[z0,z1,z530,z2,z4,z5,z6])],[(0,[z531,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z7,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z532,z6]),(0,[z0,z1,z2,z4,z5,z13,z71]),(0,[z32,z80,z0,z1,z4,z5,z6]),(0,[z533,z0,z1,z2,z4,z5,z6])],[(0,[z0,z534,z1,z2,z4,z5,z6]),(0,[z535,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z10,z6]),(0,[z32,z0,z1,z2,z85,z5,z6]),(0,[z0,z1,z536,z2,z4,z5,z6]),(0,[z112,z0,z1,z2,z4,z5,z6]),(0,[z0,z169,z1,z2,z4,z5,z48]),(0,[z0,z537,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z538]),(0,[z0,z1,z2,z171,z5,z122,z6])],[(0,[z539,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z154,z195]),(0,[z0,z1,z2,z25,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z6,z86]),(0,[z32,z0,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z13,z540])],[(0,[z1,z109,z2,z24,z4,z5,z6]),(0,[z0,z1,z2,z4,z541,z5,z6]),(0,[z0,z132,z1,z2,z4,z5,z6]),(0,[z0,z1,z109,z2,z4,z5,z13]),(0,[z0,z1,z2,z542,z4,z5,z6]),(0,[z0,z1,z2,z543,z4,z5,z6]),(0,[z544,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z122,z48]),(1,[z0,z1,z143,z4,z96,z6]),(0,[z0,z1,z2,z4,z122,z6,z71])],[(0,[z0,z1,z2,z4,z5,z268,z6]),(0,[z0,z1,z2,z4,z5,z545,z6])],[(0,[z0,z1,z2,z4,z106,z62,z6]),(1,[z0,z1,z2,z4,z5,z199]),(0,[z0,z18,z1,z2,z4,z5,z13]),(0,[z0,z1,z228,z2,z4,z5,z6]),(0,[z0,z1,z2,z291,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z546,z6])]],
   [[(0,[z0,z1,z190,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z6,z547]),(0,[z0,z1,z192,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z6,z548]),(0,[z549,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z64,z65])],[(0,[z550,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z551,z5,z6]),(0,[z0,z38,z1,z2,z14,z5,z6]),(0,[z0,z1,z2,z4,z5,z552,z6]),(0,[z0,z1,z2,z4,z553,z5,z6]),(0,[z0,z1,z2,z4,z5,z554,z6]),(0,[z80,z0,z1,z143,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z555]),(0,[z0,z1,z2,z4,z5,z6,z556])],[(0,[z0,z1,z2,z4,z106,z5,z6]),(0,[z0,z1,z2,z4,z5,z532,z13])],[(0,[z0,z1,z90,z109,z4,z5,z6]),(0,[z0,z1,z2,z4,z557,z5,z6]),(0,[z0,z1,z2,z558,z4,z5,z6]),(0,[z0,z1,z2,z4,z81,z122,z6]),(0,[z0,z559,z1,z2,z4,z5,z6]),(0,[z0,z560,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z561,z5,z6]),(0,[z0,z38,z1,z2,z4,z5,z6]),(0,[z0,z223,z1,z2,z4,z311,z6]),(0,[z562,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z563]),(1,[z0,z169,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z171,z5,z48]),(1,[z80,z0,z1,z4,z12,z6]),(0,[z0,z117,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z64,z65,z6])],[(0,[z0,z1,z2,z4,z5,z6,z189]),(0,[z0,z1,z2,z4,z5,z6,z285]),(0,[z113,z80,z0,z1,z2,z4,z6])],[(0,[z564,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z565,z2,z4,z5,z6]),(1,[z46,z1,z2,z4,z106,z6]),(0,[z0,z1,z2,z4,z5,z6,z338]),(0,[z0,z1,z2,z4,z5,z6,z566]),(0,[z0,z1,z2,z69,z4,z64,z5])]],
   [[(0,[z0,z1,z90,z24,z4,z5,z6]),(0,[z0,z1,z2,z4,z567,z5,z6]),(0,[z0,z1,z2,z4,z5,z568,z6]),(0,[z0,z1,z2,z4,z5,z569,z6]),(0,[z0,z1,z2,z570,z4,z5,z6])],[(0,[z139,z0,z1,z571,z4,z5,z6]),(0,[z0,z1,z494,z2,z24,z4,z5]),(0,[z0,z1,z2,z4,z572,z5,z6]),(0,[z0,z1,z2,z4,z5,z225,z48]),(0,[z0,z1,z2,z4,z5,z48,z71]),(0,[z0,z1,z2,z4,z5,z554,z13]),(0,[z573,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z391,z6]),(0,[z0,z1,z2,z4,z5,z574,z6])],[(0,[z139,z0,z1,z392,z4,z5,z6]),(0,[z575,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z576,z6]),(0,[z0,z1,z577,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z62,z6]),(0,[z578,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z579,z6]),(0,[z0,z227,z117,z1,z2,z4,z5])],[(0,[z0,z1,z580,z2,z4,z5,z6]),(0,[z0,z581,z1,z2,z4,z5,z6])],[(0,[z0,z38,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z582,z13]),(0,[z0,z583,z1,z2,z4,z5,z6])],[(0,[z0,z584,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z521,z4,z6]),(0,[z0,z585,z1,z2,z4,z5,z6]),(0,[z586,z0,z1,z2,z4,z5,z6]),(0,[z113,z0,z1,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z13,z154]),(0,[z0,z117,z1,z2,z4,z5,z13])],[(0,[z0,z1,z2,z587,z4,z5,z6]),(0,[z0,z223,z1,z2,z4,z126,z6]),(0,[z0,z588,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z589,z5,z6]),(0,[z0,z37,z38,z2,z4,z5,z6]),(0,[z0,z1,z590,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z152])]],
   [[(0,[z368,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z591,z4,z5,z6]),(1,[z0,z250,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z592,z6])],[(0,[z593,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z594,z6]),(0,[z0,z1,z2,z4,z5,z65,z70])],[(0,[z0,z1,z2,z4,z5,z198,z6]),(0,[z0,z1,z2,z4,z595,z5,z6]),(0,[z0,z1,z2,z4,z5,z319,z6]),(0,[z0,z1,z7,z2,z53,z5,z6]),(0,[z0,z1,z2,z4,z5,z596,z6])],[(0,[z0,z37,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z67,z6])],[(0,[z597,z0,z1,z2,z4,z5,z6]),(0,[z46,z0,z1,z2,z4,z5,z13]),(0,[z0,z38,z1,z142,z4,z5,z6]),(0,[z598,z0,z1,z2,z4,z5,z6]),(0,[z0,z117,z172,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z599,z5,z6]),(1,[z0,z37,z25,z4,z5,z6]),(1,[z0,z1,z2,z4,z39,z6]),(1,[z0,z223,z2,z85,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z600]),(0,[z0,z601,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z65,z28]),(1,[z0,z1,z2,z291,z5,z6])],[(0,[z0,z1,z2,z602,z4,z5,z6]),(0,[z0,z1,z2,z603,z4,z5,z6]),(0,[z0,z604,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z605]),(1,[z0,z2,z4,z85,z5,z48]),(0,[z0,z1,z2,z4,z606,z5,z6]),(0,[z0,z1,z332,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z269])],[(0,[z0,z265,z2,z24,z4,z5,z6]),(0,[z607,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z571,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z107,z48]),(0,[z0,z1,z2,z4,z5,z608,z6])],[(0,[z0,z1,z2,z4,z609,z5,z6]),(0,[z0,z610,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z611,z5,z6]),(0,[z0,z61,z1,z2,z4,z81,z6]),(0,[z0,z1,z2,z4,z612,z5,z6])],[(0,[z0,z1,z2,z4,z92,z5,z48]),(0,[z0,z613,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z13,z6,z48]),(0,[z0,z1,z2,z4,z5,z6,z614]),(0,[z0,z227,z1,z2,z4,z5,z6])],[(0,[z615,z0,z1,z2,z4,z5,z6]),(0,[z0,z37,z1,z142,z4,z5,z6]),(0,[z0,z2,z4,z5,z62,z6,z48])],[(0,[z0,z1,z2,z282,z4,z5,z48]),(0,[z0,z245,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z616,z6])],[(0,[z617,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z132,z1,z2,z24,z4,z5]),(0,[z0,z1,z2,z4,z81,z107,z6]),(0,[z180,z0,z1,z2,z4,z5,z154]),(0,[z76,z0,z1,z4,z5,z122,z6])],[(0,[z0,z618,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z619,z6])],[(0,[z0,z1,z2,z620,z4,z5,z6])],[(0,[z0,z47,z1,z2,z4,z5,z6]),(0,[z0,z58,z1,z2,z4,z62,z6]),(0,[z0,z117,z1,z2,z4,z5,z65])],[(0,[z0,z66,z2,z24,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z621]),(0,[z0,z1,z2,z4,z5,z622,z6]),(0,[z0,z1,z2,z4,z5,z6,z623]),(0,[z0,z47,z1,z2,z4,z5,z425]),(0,[z0,z1,z2,z4,z5,z13,z19]),(0,[z0,z227,z1,z2,z4,z5,z13]),(0,[z624,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z625,z6]),(0,[z0,z1,z2,z274,z4,z5,z6]),(0,[z0,z1,z2,z4,z626,z5,z6]),(1,[z0,z1,z2,z4,z5,z300]),(0,[z627,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z552]),(0,[z0,z1,z628,z2,z4,z5,z6]),(0,[z0,z1,z2,z629,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z630])],[(0,[z0,z1,z2,z4,z5,z386,z6]),(0,[z131,z1,z190,z2,z4,z5,z6]),(0,[z180,z0,z1,z2,z4,z5,z6]),(0,[z0,z58,z1,z2,z4,z5,z6])],[(0,[z0,z58,z2,z4,z81,z5,z6]),(0,[z503,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z69,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z65,z48])]],
   [[(0,[z0,z1,z2,z4,z631,z5,z6]),(0,[z0,z1,z2,z4,z632,z5,z6]),(0,[z0,z1,z2,z4,z633,z5,z6]),(0,[z211,z0,z1,z7,z2,z5,z6]),(0,[z0,z58,z2,z4,z85,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z540]),(0,[z0,z634,z1,z2,z4,z5,z6])],[(1,[z0,z1,z571,z4,z5,z6]),(0,[z0,z1,z2,z4,z635,z5,z6]),(0,[z0,z636,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z637,z6]),(0,[z0,z1,z2,z638,z4,z5,z6]),(0,[z0,z1,z2,z69,z5,z28,z6])],[(1,[z0,z1,z392,z4,z5,z6]),(0,[z205,z0,z1,z2,z4,z5,z6]),(0,[z0,z131,z1,z2,z4,z5,z285]),(0,[z0,z1,z2,z4,z5,z6,z639]),(0,[z0,z1,z2,z4,z5,z6,z640]),(0,[z0,z372,z1,z2,z4,z5,z6]),(0,[z0,z641,z1,z2,z4,z5,z6]),(1,[z0,z228,z2,z4,z5,z6]),(1,[z0,z229,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z642,z6]),(0,[z0,z1,z142,z109,z4,z5,z6]),(0,[z80,z46,z0,z1,z2,z4,z6]),(0,[z0,z47,z1,z2,z4,z5,z13]),(0,[z0,z643,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z28,z6])],[(0,[z644,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z645,z5,z6])],[(0,[z0,z1,z2,z24,z4,z5,z6]),(0,[z0,z1,z2,z91,z141,z5,z6]),(0,[z0,z1,z2,z4,z107,z62,z6]),(0,[z0,z1,z2,z4,z5,z6,z236]),(0,[z646,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z91,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z647,z6]),(0,[z0,z1,z2,z4,z96,z5,z48]),(1,[z0,z227,z1,z2,z5,z70])],[(0,[z113,z1,z2,z4,z5,z107,z6]),(0,[z0,z648,z1,z2,z4,z5,z6]),(0,[z0,z58,z1,z2,z4,z5,z13]),(0,[z0,z1,z90,z4,z5,z19,z6]),(0,[z0,z1,z2,z84,z171,z5,z6]),(0,[z0,z1,z2,z4,z5,z649,z6])],[(0,[z469,z0,z1,z2,z24,z4,z6]),(0,[z0,z1,z2,z141,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z6,z380]),(0,[z0,z1,z2,z650,z4,z5,z6]),(0,[z0,z117,z1,z2,z4,z5,z71])]],
   [[(0,[z50,z0,z131,z2,z4,z5,z6]),(1,[z0,z265,z2,z4,z5,z6]),(0,[z651,z0,z1,z2,z4,z5,z6]),(0,[z147,z0,z1,z2,z4,z5,z48]),(0,[z46,z0,z1,z2,z4,z106,z6]),(0,[z112,z0,z47,z2,z4,z5,z6]),(0,[z0,z1,z652,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z162,z13]),(0,[z0,z1,z2,z653,z4,z5,z6]),(0,[z0,z1,z2,z654,z4,z5,z6]),(0,[z0,z1,z2,z655,z4,z5,z6])],[(0,[z0,z1,z109,z4,z5,z6,z195]),(0,[z0,z1,z2,z4,z5,z656,z6]),(0,[z657,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z143,z2,z4,z62,z6]),(0,[z32,z0,z1,z4,z96,z5,z6])],[(0,[z0,z658,z1,z2,z4,z5,z6]),(0,[z0,z1,z659,z2,z4,z5,z6]),(0,[z46,z1,z2,z4,z106,z5,z6]),(0,[z232,z0,z2,z4,z5,z154,z6])],[(0,[z0,z660,z1,z2,z4,z5,z6]),(0,[z661,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z100]),(0,[z0,z662,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z663,z5,z6]),(0,[z0,z1,z2,z664,z4,z5,z6]),(0,[z180,z1,z2,z4,z5,z6,z236]),(0,[z330,z0,z1,z2,z4,z5,z48]),(0,[z0,z331,z1,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z665,z5,z6]),(0,[z0,z1,z2,z4,z666,z5,z6]),(0,[z0,z18,z1,z4,z5,z6,z195]),(0,[z0,z1,z2,z4,z5,z6,z667])],[(0,[z0,z131,z1,z2,z4,z5,z308]),(0,[z0,z1,z143,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z668])],[(0,[z0,z1,z2,z24,z4,z5,z13]),(0,[z232,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z669,z4,z5,z6])],[(0,[z139,z0,z1,z2,z4,z72,z6]),(0,[z139,z112,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z670,z6])],[(0,[z30,z0,z1,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z671,z5,z6]),(0,[z32,z0,z1,z2,z4,z5,z6]),(0,[z0,z672,z1,z2,z4,z5,z6]),(0,[z0,z673,z1,z2,z4,z5,z6]),(0,[z0,z674,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z675,z6]),(0,[z0,z170,z1,z2,z4,z5,z269])]],
   [[(0,[z0,z1,z676,z2,z4,z5,z6]),(0,[z0,z38,z1,z2,z4,z5,z199]),(0,[z0,z1,z677,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z678,z5,z6])],[(0,[z139,z0,z1,z2,z4,z5,z48]),(0,[z679,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z680,z6]),(0,[z681,z0,z1,z2,z4,z5,z6]),(0,[z80,z0,z1,z4,z5,z12,z6])],[(0,[z0,z1,z2,z4,z5,z13,z145]),(1,[z0,z18,z1,z4,z5,z195])],[(0,[z682,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z683,z6])],[(0,[z684,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z685,z6]),(0,[z0,z1,z686,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z687]),(0,[z0,z1,z2,z91,z5,z122,z6]),(0,[z0,z1,z143,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z171,z5,z13]),(0,[z0,z1,z688,z2,z4,z5,z6])],[(0,[z0,z1,z2,z689,z4,z5,z6]),(0,[z370,z0,z1,z2,z4,z5,z48]),(0,[z0,z227,z1,z2,z4,z500,z6])],[(0,[z0,z1,z2,z4,z690,z5,z6]),(0,[z0,z1,z2,z4,z691,z5,z6]),(0,[z0,z1,z2,z4,z5,z48,z195]),(0,[z0,z1,z2,z4,z64,z5,z13]),(0,[z0,z692,z1,z2,z4,z5,z6])],[(0,[z368,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z1,z693,z2,z4,z5,z6]),(0,[z0,z1,z2,z694,z4,z5,z6])]],
   [[(0,[z139,z1,z190,z2,z4,z5,z6]),(0,[z0,z1,z695,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z425]),(0,[z112,z0,z58,z2,z4,z5,z6]),(1,[z32,z0,z1,z53,z5,z6])],[(0,[z113,z0,z1,z2,z4,z107,z6]),(0,[z0,z1,z2,z4,z5,z19,z236]),(1,[z0,z58,z2,z4,z81,z6]),(0,[z681,z0,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z12,z6]),(0,[z0,z87,z170,z2,z4,z5,z6])],[],[(0,[z0,z1,z2,z696,z4,z5,z6]),(0,[z0,z1,z168,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z697,z5,z6]),(0,[z698,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z699,z4,z5,z6]),(0,[z0,z1,z2,z4,z53,z5,z48]),(1,[z0,z332,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z700,z6])],[(0,[z99,z1,z2,z24,z4,z5,z6]),(0,[z0,z1,z109,z25,z4,z5,z6]),(0,[z0,z1,z2,z4,z701,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z702])],[(0,[z0,z703,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z521,z24,z4,z6]),(0,[z0,z1,z90,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z704,z5,z6])],[(0,[z0,z1,z2,z4,z39,z5,z6]),(0,[z0,z1,z2,z4,z5,z705,z6]),(0,[z0,z1,z2,z69,z84,z5,z6])],[(0,[z0,z1,z2,z4,z5,z582,z6]),(0,[z0,z706,z1,z2,z4,z5,z6]),(0,[z0,z223,z1,z2,z4,z5,z552]),(0,[z32,z0,z1,z4,z53,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z4,z5,z707]),(0,[z0,z708,z2,z4,z5,z6])],[],[(0,[z0,z1,z2,z4,z709,z6]),(0,[z0,z2,z4,z5,z710,z48]),(0,[z0,z2,z92,z85,z5,z48]),(0,[z232,z30,z2,z4,z5,z154]),(0,[z0,z488,z2,z4,z81,z6]),(0,[z0,z1,z2,z4,z83,z48]),(1,[z0,z1,z2,z711,z6]),(1,[z0,z1,z2,z4,z712])],[(0,[z0,z2,z4,z354,z5,z48]),(0,[z135,z1,z24,z4,z5,z6]),(0,[z0,z1,z2,z713,z5,z6]),(0,[z0,z245,z714,z2,z4,z5])],[(0,[z0,z1,z2,z4,z715,z6]),(0,[z0,z1,z716,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z300]),(0,[z717,z1,z2,z4,z5,z6])],[(0,[z0,z718,z25,z4,z5,z6]),(0,[z0,z172,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z719]),(0,[z0,z170,z1,z2,z711,z6]),(0,[z0,z1,z2,z4,z500,z28])],[(0,[z0,z1,z2,z4,z5,z720]),(0,[z0,z393,z142,z4,z5,z6]),(0,[z0,z37,z718,z4,z5,z6])],[(0,[z50,z131,z2,z4,z5,z48]),(0,[z0,z2,z4,z85,z5,z156]),(0,[z0,z1,z2,z136,z5,z13]),(0,[z343,z1,z2,z4,z5,z279]),(0,[z0,z1,z332,z2,z122,z6]),(0,[z0,z170,z1,z121,z122,z6])]],
   [[(0,[z0,z1,z2,z721,z5,z6]),(0,[z0,z1,z2,z137,z5,z13]),(0,[z30,z2,z4,z5,z154,z198]),(0,[z0,z2,z4,z5,z722,z48])],[(0,[z0,z1,z723,z2,z4,z5]),(0,[z0,z1,z2,z5,z724,z6]),(0,[z0,z382,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z725,z6]),(0,[z0,z1,z2,z726,z5,z6]),(0,[z0,z38,z142,z4,z5,z48]),(0,[z0,z47,z2,z727,z5,z6]),(0,[z0,z229,z2,z4,z5,z6]),(0,[z0,z1,z4,z728,z5,z6]),(0,[z0,z245,z1,z2,z69,z5]),(0,[z0,z1,z2,z512,z171,z6]),(0,[z0,z1,z2,z669,z5,z28]),(0,[z0,z1,z2,z4,z64,z712])],[(0,[z729,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z730,z6]),(0,[z0,z1,z718,z4,z5,z6]),(0,[z0,z1,z2,z731,z5,z6]),(0,[z0,z732,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z733]),(0,[z0,z2,z4,z5,z197,z48]),(0,[z0,z1,z7,z29,z5,z6]),(0,[z0,z1,z2,z4,z734,z6]),(1,[z0,z2,z314,z62,z6])],[(0,[z0,z1,z2,z4,z5,z735]),(0,[z0,z223,z2,z85,z5,z552]),(0,[z0,z2,z4,z171,z62,z48]),(0,[z76,z0,z1,z4,z5,z48])],[(0,[z0,z618,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z151,z13])],[(0,[z444,z0,z2,z4,z5,z48]),(0,[z131,z736,z2,z4,z5,z6]),(0,[z0,z265,z2,z521,z4,z6]),(0,[z0,z1,z737,z4,z5,z6]),(0,[z0,z115,z1,z2,z122,z6]),(0,[z0,z738,z1,z2,z4,z5]),(0,[z0,z61,z2,z4,z62,z380]),(0,[z0,z1,z2,z4,z5,z739])],[(0,[z0,z1,z2,z740,z5,z6]),(0,[z1,z2,z4,z5,z154,z741]),(0,[z0,z2,z718,z4,z5,z6]),(0,[z0,z742,z2,z4,z5,z6])]],
   [[(0,[z0,z2,z4,z5,z743,z6]),(0,[z46,z1,z2,z510,z4,z6]),(0,[z0,z2,z4,z5,z48,z145]),(0,[z0,z1,z2,z4,z5,z744]),(0,[z0,z1,z7,z8,z5,z6]),(0,[z0,z1,z143,z4,z745,z6]),(0,[z0,z1,z2,z69,z5,z746])],[(0,[z99,z1,z24,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z747]),(0,[z368,z0,z1,z494,z2,z5]),(0,[z0,z1,z90,z274,z4,z5]),(0,[z0,z1,z168,z4,z5,z13]),(0,[z0,z1,z2,z4,z748,z6]),(0,[z0,z331,z2,z85,z5,z6]),(0,[z0,z581,z2,z4,z5,z48]),(0,[z0,z1,z4,z5,z121,z48])],[(0,[z0,z749,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z100]),(0,[z469,z0,z66,z2,z4,z6]),(0,[z0,z1,z750,z4,z5,z6]),(0,[z1,z2,z4,z5,z741,z236]),(0,[z0,z2,z85,z5,z122,z48]),(0,[z0,z170,z1,z2,z122,z269])],[(0,[z0,z2,z4,z383,z5,z48]),(0,[z0,z1,z2,z728,z5,z6]),(0,[z0,z1,z2,z751,z5,z6]),(1,[z0,z1,z2,z5,z746])],[(0,[z147,z1,z2,z752,z5,z6]),(0,[z147,z1,z2,z92,z5,z13]),(0,[z0,z753,z2,z4,z5,z6]),(0,[z0,z754,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z755])],[(0,[z112,z0,z2,z383,z5,z6]),(0,[z0,z1,z2,z383,z72,z6]),(0,[z139,z0,z2,z4,z72,z48]),(0,[z0,z1,z2,z4,z5,z51]),(0,[z0,z1,z2,z4,z126,z82]),(0,[z0,z2,z4,z5,z62,z425]),(0,[z0,z1,z2,z4,z501,z65])],[(0,[z50,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z126,z48]),(0,[z0,z1,z2,z4,z5,z756]),(0,[z0,z1,z757,z2,z4,z5]),(0,[z0,z1,z2,z4,z500,z48]),(0,[z0,z1,z758,z4,z5,z13])],[(0,[z0,z1,z494,z2,z521,z4]),(0,[z0,z1,z2,z5,z6,z759]),(0,[z0,z1,z2,z4,z760,z6]),(0,[z0,z1,z2,z4,z761,z6]),(0,[z0,z2,z238,z4,z5,z48]),(0,[z0,z332,z2,z4,z5,z391])]],
   [[(0,[z0,z1,z2,z383,z5,z48]),(0,[z0,z1,z2,z4,z762,z6]),(0,[z0,z1,z2,z4,z763,z6]),(0,[z0,z1,z2,z4,z5,z764]),(0,[z0,z1,z274,z4,z5,z236]),(0,[z0,z372,z1,z4,z5,z193]),(0,[z0,z1,z7,z8,z5,z13])],[(0,[z0,z1,z765,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z766]),(0,[z0,z38,z142,z4,z151,z6]),(0,[z0,z18,z1,z4,z5,z195])],[(0,[z232,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z767]),(0,[z368,z0,z1,z2,z521,z6]),(0,[z0,z1,z2,z243,z5,z67])],[(0,[z0,z1,z2,z4,z5,z768]),(0,[z0,z1,z2,z4,z5,z769]),(0,[z180,z1,z2,z4,z5,z236]),(0,[z0,z2,z4,z5,z770,z48]),(0,[z0,z771,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z772]),(0,[z0,z1,z2,z4,z5,z773]),(0,[z0,z1,z2,z4,z5,z774])],[(0,[z575,z0,z2,z4,z5,z48]),(0,[z0,z2,z4,z5,z198,z6]),(0,[z0,z1,z2,z4,z5,z775]),(0,[z0,z58,z2,z4,z5,z776]),(0,[z0,z1,z2,z4,z5,z777])],[(0,[z0,z1,z2,z243,z5,z48]),(0,[z0,z61,z2,z4,z62,z6]),(0,[z0,z127,z1,z2,z122,z6]),(0,[z0,z1,z2,z778,z5,z13]),(0,[z0,z117,z1,z2,z224,z71])],[(0,[z0,z2,z4,z5,z150,z48]),(0,[z0,z1,z2,z4,z5,z779]),(0,[z76,z0,z170,z1,z122,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z780]),(0,[z0,z781,z2,z4,z5,z6])],[(0,[z0,z1,z2,z140,z150,z6]),(0,[z0,z1,z2,z4,z5,z782]),(0,[z0,z783,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z784,z6]),(0,[z0,z1,z2,z4,z5,z785]),(0,[z0,z1,z2,z4,z786,z6]),(0,[z0,z1,z2,z787,z5,z6])],[(0,[z232,z0,z2,z4,z5,z13]),(0,[z0,z332,z2,z4,z5,z6]),(0,[z0,z1,z788,z4,z5,z6]),(0,[z0,z61,z2,z314,z62,z6]),(0,[z0,z1,z2,z4,z5,z789]),(0,[z0,z1,z2,z397,z5,z532])],[(0,[z205,z1,z2,z4,z5,z182])],[(0,[z0,z66,z2,z4,z5,z13]),(0,[z0,z790,z1,z2,z4,z6]),(0,[z0,z1,z274,z4,z5,z154]),(0,[z1,z2,z4,z5,z741,z6]),(0,[z0,z1,z2,z791,z5,z6]),(0,[z0,z1,z2,z4,z224,z71])],[(0,[z0,z792,z2,z4,z5,z6]),(0,[z0,z2,z272,z4,z5,z48])],[(0,[z1,z2,z141,z752,z5,z6]),(0,[z0,z61,z2,z4,z62,z13]),(0,[z0,z1,z2,z4,z5,z793])],[(0,[z0,z1,z2,z794,z5,z6]),(0,[z0,z1,z2,z4,z5,z795]),(0,[z0,z2,z4,z796,z5,z6]),(0,[z76,z0,z1,z91,z5,z6]),(0,[z0,z1,z143,z4,z96,z48]),(0,[z0,z1,z2,z4,z5,z797])]],
   [[(0,[z0,z1,z2,z4,z5,z798]),(0,[z32,z0,z2,z85,z5,z48]),(0,[z0,z604,z2,z4,z5,z48]),(0,[z0,z245,z1,z2,z5,z70]),(0,[z0,z1,z2,z171,z711,z6])],[(0,[z0,z1,z2,z140,z5,z13]),(0,[z0,z1,z2,z4,z72,z386]),(0,[z112,z0,z2,z4,z5,z386]),(0,[z0,z1,z2,z4,z5,z799]),(0,[z0,z1,z2,z4,z5,z800]),(0,[z0,z1,z2,z4,z39,z199]),(0,[z0,z47,z2,z4,z5,z82]),(0,[z0,z219,z2,z4,z5,z48]),(0,[z0,z2,z4,z284,z5,z48]),(0,[z0,z1,z2,z4,z786,z13])],[(0,[z0,z1,z274,z4,z5,z6]),(1,[z1,z2,z4,z725,z6]),(0,[z0,z1,z2,z4,z5,z801]),(0,[z0,z641,z2,z4,z5,z48]),(0,[z0,z1,z90,z4,z5,z225]),(0,[z0,z332,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z802]),(0,[z0,z1,z7,z728,z5,z6])],[(0,[z0,z265,z392,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z803]),(0,[z0,z1,z2,z140,z5,z189]),(0,[z0,z1,z2,z4,z5,z22]),(0,[z0,z2,z4,z5,z48,z246]),(0,[z32,z0,z1,z728,z5,z6])],[(0,[z0,z1,z2,z4,z150,z13]),(0,[z627,z1,z109,z4,z5,z6]),(0,[z0,z1,z2,z4,z804,z5])],[(0,[z99,z1,z137,z24,z5,z6]),(0,[z0,z117,z228,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z285]),(0,[z0,z1,z2,z4,z150,z189]),(0,[z99,z1,z24,z4,z5,z100]),(0,[z0,z1,z2,z805,z4,z5]),(0,[z1,z2,z4,z106,z725,z6]),(0,[z0,z1,z2,z243,z151,z6])],[(0,[z0,z1,z2,z4,z806,z6]),(0,[z180,z1,z2,z4,z5,z279]),(0,[z0,z1,z2,z4,z5,z807]),(0,[z0,z1,z2,z4,z5,z808]),(0,[z80,z0,z1,z4,z439,z6]),(0,[z80,z0,z1,z4,z12,z48]),(0,[z0,z117,z1,z2,z4,z226])]],
   [[(0,[z0,z1,z809,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z810]),(0,[z0,z811,z2,z4,z5,z6]),(0,[z330,z1,z2,z4,z5,z236]),(0,[z0,z2,z4,z5,z298,z48]),(0,[z0,z714,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z812]),(0,[z0,z1,z2,z5,z28,z746])],[(0,[z0,z1,z2,z813,z5,z6]),(0,[z113,z1,z2,z4,z107,z48]),(0,[z0,z47,z2,z85,z5,z48]),(0,[z0,z1,z814,z4,z5,z48])],[(0,[z736,z190,z2,z4,z5,z6]),(0,[z0,z1,z274,z4,z5,z13]),(0,[z0,z87,z170,z2,z122,z6])],[],[(0,[z0,z1,z2,z4,z5,z815]),(0,[z0,z228,z2,z4,z64,z5])],[(0,[z0,z1,z2,z816,z4,z6]),(0,[z0,z817,z2,z4,z5,z6]),(0,[z0,z332,z2,z4,z5,z818])],[(0,[z0,z1,z2,z4,z5,z819]),(0,[z0,z820,z1,z2,z4,z5]),(0,[z0,z821,z2,z4,z5,z6])],[(0,[z0,z1,z2,z822,z5,z6]),(0,[z0,z1,z2,z521,z4,z48]),(0,[z0,z1,z2,z4,z5,z823]),(0,[z0,z824,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z825]),(0,[z0,z58,z2,z4,z62,z48]),(0,[z0,z1,z143,z4,z522,z6]),(0,[z0,z2,z4,z5,z776,z48]),(0,[z0,z1,z2,z4,z234,z554]),(0,[z0,z1,z2,z826,z5,z6]),(0,[z0,z1,z2,z4,z171,z269]),(0,[z0,z1,z2,z4,z5,z827])]],
   [[(0,[z0,z1,z2,z828,z5,z6]),(0,[z30,z1,z2,z4,z5,z182]),(0,[z0,z87,z2,z4,z5,z6]),(1,[z0,z2,z4,z829,z6]),(0,[z0,z1,z830,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z831]),(0,[z1,z2,z4,z5,z725,z6]),(0,[z0,z1,z2,z4,z5,z832]),(0,[z0,z1,z2,z4,z151,z199]),(0,[z0,z1,z7,z595,z5,z6]),(0,[z0,z1,z2,z4,z83,z13]),(0,[z0,z1,z2,z4,z833,z6]),(0,[z0,z1,z90,z4,z5,z19]),(0,[z0,z1,z2,z711,z122,z6])],[(0,[z0,z2,z4,z5,z834,z6]),(0,[z0,z58,z2,z4,z5,z48]),(0,[z0,z250,z2,z4,z5,z48]),(0,[z0,z297,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z835]),(0,[z0,z245,z1,z4,z5,z121])],[(0,[z0,z1,z2,z4,z5,z836]),(0,[z0,z1,z2,z4,z5,z837]),(0,[z0,z1,z8,z5,z467,z6]),(1,[z0,z1,z4,z745,z6]),(0,[z0,z245,z1,z2,z4,z64]),(0,[z0,z1,z2,z69,z224,z5]),(0,[z0,z1,z2,z4,z65,z712])],[(0,[z50,z2,z4,z5,z182,z48]),(0,[z0,z838,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z839]),(0,[z0,z1,z2,z4,z840,z6]),(0,[z544,z0,z2,z4,z5,z48]),(0,[z0,z1,z2,z841,z5,z48]),(0,[z0,z172,z2,z4,z5,z13])],[(0,[z0,z1,z494,z2,z137,z5]),(0,[z0,z842,z1,z2,z4,z5]),(0,[z0,z2,z4,z85,z311,z6]),(0,[z0,z674,z2,z4,z5,z13])],[(0,[z0,z1,z2,z4,z5,z843]),(0,[z0,z1,z2,z844,z5,z6]),(0,[z0,z129,z2,z85,z5,z6]),(0,[z0,z2,z4,z5,z13,z675])],[(0,[z0,z179,z2,z4,z62,z6]),(0,[z0,z223,z2,z85,z5,z82]),(0,[z0,z2,z4,z5,z22,z48]),(0,[z0,z1,z2,z4,z712,z71])]],
   [[(0,[z50,z131,z2,z4,z5,z285]),(0,[z0,z845,z2,z4,z5,z6]),(0,[z0,z393,z2,z4,z5,z48]),(1,[z1,z2,z752,z5,z6]),(0,[z0,z38,z142,z4,z5,z13]),(0,[z0,z223,z2,z85,z5,z48]),(0,[z0,z1,z2,z4,z5,z846]),(0,[z0,z1,z2,z291,z5,z48])],[(0,[z0,z1,z2,z5,z6,z847]),(0,[z113,z17,z1,z2,z4,z6]),(0,[z0,z2,z727,z85,z5,z6])],[(0,[z0,z1,z2,z4,z5,z848]),(0,[z0,z1,z2,z4,z5,z849]),(0,[z0,z1,z2,z85,z311,z6]),(0,[z76,z0,z1,z85,z5,z6]),(0,[z0,z1,z2,z4,z27,z268]),(0,[z0,z850,z2,z4,z5,z6])],[(0,[z0,z1,z2,z137,z5,z6]),(0,[z211,z1,z2,z752,z5,z6]),(0,[z0,z1,z2,z4,z311,z13]),(0,[z0,z347,z2,z4,z5,z48]),(0,[z0,z267,z2,z4,z5,z48]),(0,[z851,z0,z1,z2,z4,z5]),(0,[z0,z228,z2,z4,z5,z28])],[(0,[z0,z1,z852,z4,z5,z6]),(0,[z853,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z350,z5,z48]),(0,[z0,z1,z2,z4,z500,z70]),(0,[z0,z1,z2,z5,z6,z746]),(0,[z0,z1,z2,z4,z64,z34])],[(0,[z0,z1,z2,z4,z5,z854]),(0,[z0,z1,z2,z14,z151,z6]),(0,[z0,z47,z2,z91,z5,z6])],[(0,[z0,z265,z2,z4,z5,z855]),(0,[z0,z47,z2,z91,z5,z425]),(0,[z0,z1,z2,z224,z5,z6]),(0,[z0,z227,z1,z2,z5,z746]),(0,[z0,z505,z1,z2,z4,z71])],[(0,[z0,z1,z2,z383,z150,z6]),(0,[z0,z2,z4,z5,z357,z48]),(0,[z0,z1,z2,z4,z856,z6]),(0,[z0,z857,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z858])]],
   [[(0,[z0,z1,z2,z4,z151,z6]),(0,[z0,z1,z2,z4,z5,z156])],[(0,[z139,z190,z2,z140,z5,z6]),(0,[z99,z1,z859,z4,z5,z6]),(0,[z0,z1,z2,z860,z5,z6]),(0,[z0,z861,z2,z4,z5,z6])],[(0,[z50,z131,z2,z4,z5,z308])],[(0,[z1,z736,z2,z4,z5,z6]),(0,[z0,z262,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z862]),(0,[z0,z1,z2,z4,z863,z6])],[(0,[z139,z190,z2,z4,z150,z6]),(0,[z0,z1,z168,z4,z5,z6]),(0,[z0,z132,z1,z90,z4,z5]),(0,[z0,z1,z2,z4,z864,z6]),(0,[z0,z2,z4,z5,z363,z48]),(0,[z0,z1,z4,z5,z865,z6]),(0,[z0,z1,z852,z4,z5,z13]),(0,[z0,z227,z172,z2,z4,z5])],[(0,[z0,z1,z866,z4,z5,z6]),(0,[z0,z132,z66,z2,z4,z5]),(0,[z0,z47,z2,z91,z5,z13]),(0,[z0,z1,z2,z4,z64,z500])],[(0,[z0,z1,z2,z4,z5,z867]),(0,[z0,z1,z2,z4,z5,z868]),(0,[z0,z1,z2,z4,z869,z5]),(0,[z0,z1,z2,z5,z870,z6]),(0,[z0,z1,z2,z224,z5,z13]),(0,[z0,z1,z4,z5,z19,z871])],[(0,[z0,z1,z2,z4,z872,z6]),(0,[z147,z1,z2,z92,z5,z6]),(0,[z0,z37,z25,z4,z5,z300]),(0,[z873,z1,z2,z4,z5,z6]),(0,[z0,z61,z2,z4,z829,z6]),(0,[z0,z643,z2,z4,z81,z6])]],
   [[(0,[z0,z1,z571,z4,z72,z6]),(0,[z469,z0,z1,z494,z2,z4]),(0,[z211,z1,z2,z141,z5,z6]),(0,[z0,z874,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z875]),(0,[z0,z1,z392,z4,z72,z6]),(0,[z0,z1,z2,z383,z5,z189]),(0,[z232,z0,z2,z4,z5,z386]),(0,[z0,z1,z758,z4,z5,z6]),(0,[z0,z206,z2,z4,z5,z48])],[(0,[z0,z1,z2,z876,z5,z6]),(0,[z469,z0,z1,z2,z4,z48]),(0,[z0,z877,z2,z4,z5,z6]),(0,[z0,z332,z2,z4,z5,z878]),(0,[z0,z172,z2,z4,z5,z65])],[(0,[z0,z1,z571,z4,z5,z48]),(0,[z0,z170,z1,z2,z122,z48]),(0,[z0,z1,z2,z4,z863,z13])],[(0,[z0,z1,z392,z4,z5,z48]),(0,[z139,z190,z2,z4,z5,z13]),(0,[z0,z265,z132,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z879]),(0,[z0,z228,z2,z4,z5,z48]),(0,[z0,z1,z209,z4,z5,z19]),(0,[z0,z1,z2,z84,z171,z6]),(0,[z0,z1,z4,z5,z6,z880]),(0,[z0,z1,z2,z69,z5,z28]),(0,[z0,z229,z2,z291,z5,z6])],[(0,[z0,z1,z2,z4,z881,z6]),(1,[z0,z2,z4,z150,z48]),(0,[z0,z1,z2,z243,z5,z13]),(0,[z0,z7,z2,z85,z5,z48]),(0,[z0,z75,z2,z85,z5,z6])],[(0,[z139,z190,z2,z4,z5,z189]),(0,[z882,z1,z2,z4,z5,z6]),(0,[z0,z172,z2,z224,z5,z6])],[(0,[z0,z883,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z884]),(0,[z0,z1,z2,z4,z5,z380])]],
   [[(0,[z0,z1,z2,z140,z5,z386]),(0,[z343,z0,z2,z4,z5,z48]),(0,[z211,z1,z2,z141,z5,z13]),(0,[z180,z1,z2,z4,z5,z741]),(0,[z0,z1,z2,z4,z5,z885]),(0,[z0,z886,z2,z4,z5,z6])],[(0,[z533,z1,z109,z4,z5,z6]),(0,[z0,z1,z2,z778,z5,z6]),(0,[z0,z1,z2,z4,z122,z269])],[(0,[z0,z1,z2,z4,z887,z6]),(0,[z0,z265,z2,z4,z5,z48]),(0,[z368,z0,z1,z2,z5,z13]),(0,[z0,z1,z2,z4,z5,z888]),(0,[z0,z250,z2,z4,z5,z51]),(0,[z0,z2,z4,z829,z5,z6])],[(0,[z0,z1,z2,z4,z150,z386]),(0,[z413,z1,z2,z4,z5,z154]),(0,[z0,z223,z2,z727,z5,z6]),(0,[z0,z1,z2,z314,z5,z380])],[(0,[z0,z889,z2,z4,z5,z6]),(0,[z0,z1,z2,z84,z171,z13]),(0,[z0,z1,z2,z4,z5,z391]),(0,[z0,z367,z1,z2,z4,z71])],[(0,[z0,z1,z2,z4,z5,z890]),(0,[z0,z1,z891,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z871])],[(0,[z0,z265,z25,z4,z5,z6]),(0,[z0,z66,z2,z521,z4,z6]),(0,[z343,z0,z2,z4,z5,z198]),(0,[z0,z58,z2,z4,z81,z22]),(0,[z892,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z893]),(0,[z499,z0,z1,z2,z122,z6])],[(0,[z0,z66,z2,z4,z5,z6]),(0,[z30,z1,z2,z4,z5,z741]),(0,[z0,z1,z2,z4,z894,z6]),(0,[z0,z2,z4,z5,z62,z48]),(0,[z0,z488,z2,z4,z5,z48]),(0,[z0,z1,z4,z5,z123,z121])]],
   [[(0,[z0,z1,z2,z895,z5,z6]),(0,[z1,z859,z24,z4,z5,z6]),(0,[z0,z245,z1,z2,z4,z5])],[(0,[z0,z38,z142,z243,z5,z6]),(0,[z0,z896,z2,z4,z5,z6]),(0,[z0,z1,z2,z84,z5,z269])],[(0,[z0,z1,z897,z4,z5,z6]),(0,[z368,z0,z265,z2,z5,z6]),(0,[z0,z1,z2,z752,z5,z6]),(0,[z0,z49,z2,z4,z5,z13]),(0,[z0,z332,z2,z4,z171,z6])],[(0,[z139,z537,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z898]),(0,[z0,z1,z2,z899,z5,z6]),(0,[z0,z1,z8,z728,z5,z6])],[(0,[z0,z1,z2,z140,z5,z6]),(0,[z0,z1,z2,z521,z137,z6]),(0,[z0,z900,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z901]),(0,[z0,z1,z2,z224,z5,z65])],[(0,[z0,z1,z2,z4,z5,z710]),(0,[z0,z265,z2,z137,z5,z6]),(0,[z0,z329,z2,z4,z5,z48]),(0,[z0,z47,z2,z40,z5,z6]),(0,[z0,z1,z2,z4,z5,z902])],[(0,[z0,z1,z2,z4,z5,z903]),(0,[z0,z95,z1,z2,z4,z338]),(0,[z0,z1,z2,z4,z5,z904])],[(0,[z0,z1,z2,z4,z150,z6]),(0,[z0,z2,z4,z5,z436,z48]),(0,[z368,z0,z132,z1,z2,z5]),(0,[z0,z1,z2,z905,z5,z6]),(0,[z0,z423,z1,z4,z5,z195])]],
   [[(0,[z0,z906,z2,z4,z5,z6]),(0,[z113,z1,z2,z4,z107,z13]),(0,[z0,z212,z2,z4,z5,z13]),(0,[z0,z1,z2,z314,z62,z6]),(0,[z0,z2,z4,z5,z13,z48])],[(0,[z0,z1,z2,z4,z745,z6])],[(0,[z0,z1,z2,z907,z5,z6]),(0,[z32,z0,z1,z53,z5,z48]),(0,[z486,z1,z2,z4,z5,z582])],[(0,[z0,z1,z2,z4,z5,z908]),(0,[z0,z1,z2,z909,z5,z6]),(0,[z0,z2,z4,z5,z910,z6]),(0,[z0,z2,z4,z5,z911,z6]),(0,[z0,z1,z2,z4,z5,z912]),(0,[z0,z1,z2,z314,z5,z6]),(0,[z0,z58,z2,z4,z81,z48]),(0,[z0,z913,z1,z2,z4,z5])],[(0,[z1,z2,z752,z92,z5,z6]),(0,[z0,z1,z2,z14,z5,z13]),(0,[z0,z38,z142,z4,z5,z199]),(0,[z0,z1,z914,z4,z5,z6]),(0,[z0,z1,z2,z4,z915,z6])],[(0,[z0,z1,z2,z4,z5,z173]),(0,[z0,z1,z2,z4,z5,z916]),(0,[z0,z47,z2,z4,z5,z48]),(0,[z0,z127,z2,z85,z5,z6]),(0,[z0,z1,z2,z5,z6,z917]),(0,[z0,z18,z1,z4,z5,z871])],[(0,[z0,z1,z2,z4,z5,z918]),(0,[z0,z2,z4,z5,z13,z198]),(0,[z0,z1,z2,z919,z5,z6]),(0,[z0,z1,z2,z4,z5,z920])],[(0,[z0,z1,z2,z4,z5,z13]),(0,[z139,z190,z2,z383,z5,z6]),(0,[z108,z1,z109,z4,z5,z6]),(0,[z0,z1,z921,z2,z4,z5]),(0,[z0,z922,z2,z4,z5,z6]),(0,[z0,z923,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z924]),(0,[z925,z1,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z926]),(0,[z80,z0,z1,z4,z745,z6]),(0,[z0,z332,z2,z4,z5,z269])]],
   [[(0,[z0,z1,z2,z927,z5,z6]),(1,[z1,z2,z4,z5,z741]),(0,[z30,z1,z530,z2,z4,z5]),(0,[z0,z2,z4,z5,z13,z722]),(0,[z0,z1,z2,z4,z5,z928])],[(0,[z0,z1,z2,z4,z5,z189]),(0,[z0,z1,z2,z4,z5,z929]),(0,[z30,z1,z2,z4,z5,z154]),(0,[z0,z1,z90,z352,z4,z5]),(0,[z0,z1,z2,z4,z5,z930]),(1,[z0,z714,z2,z4,z5])],[(0,[z0,z1,z931,z4,z5,z6]),(0,[z368,z469,z0,z1,z2,z6]),(0,[z0,z1,z2,z4,z932,z6]),(0,[z0,z1,z2,z907,z5,z13]),(0,[z0,z1,z4,z5,z6,z933]),(0,[z0,z934,z2,z4,z5,z6])],[(0,[z0,z1,z2,z935,z5,z6]),(0,[z0,z1,z2,z4,z5,z936]),(0,[z0,z37,z25,z4,z5,z10]),(0,[z0,z1,z2,z4,z937,z6]),(0,[z0,z1,z2,z314,z5,z13]),(0,[z0,z87,z2,z4,z5,z938]),(0,[z0,z1,z2,z5,z500,z70])],[(0,[z0,z1,z2,z4,z5,z939]),(0,[z0,z1,z2,z940,z5,z6]),(0,[z46,z1,z2,z4,z106,z48]),(0,[z0,z1,z2,z397,z5,z28]),(0,[z0,z1,z2,z4,z83,z6])],[(0,[z644,z0,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z941])],[(0,[z0,z1,z2,z4,z5,z942]),(0,[z0,z1,z90,z4,z5,z622]),(0,[z0,z2,z85,z62,z122,z6]),(0,[z0,z1,z2,z84,z475,z6]),(0,[z56,z0,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z943]),(0,[z0,z245,z1,z2,z4,z71])],[(0,[z0,z1,z944,z4,z5,z6]),(0,[z108,z1,z109,z4,z5,z13]),(0,[z0,z1,z2,z4,z945,z6]),(1,[z0,z2,z727,z5,z6]),(0,[z0,z172,z2,z4,z5,z6]),(0,[z0,z129,z2,z4,z62,z6]),(0,[z0,z227,z1,z2,z5,z145]),(0,[z0,z170,z1,z2,z122,z391]),(0,[z0,z946,z245,z2,z4,z5])]],
   [[(0,[z0,z1,z947,z2,z4,z5]),(0,[z0,z1,z4,z5,z948,z6]),(0,[z0,z1,z2,z4,z5,z949]),(0,[z0,z38,z142,z14,z5,z6]),(0,[z578,z0,z2,z4,z5,z48]),(0,[z0,z1,z4,z745,z12,z6]),(0,[z0,z117,z1,z2,z291,z71])],[(0,[z50,z131,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z950,z6]),(0,[z180,z673,z1,z2,z4,z5]),(0,[z0,z95,z2,z4,z62,z48]),(0,[z0,z229,z117,z2,z4,z71])],[(0,[z0,z951,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z722,z6])],[(0,[z0,z1,z2,z4,z5,z308]),(0,[z0,z1,z2,z4,z5,z952]),(0,[z99,z66,z24,z4,z5,z6]),(0,[z0,z1,z143,z278,z4,z6]),(0,[z0,z38,z142,z4,z5,z6]),(0,[z76,z0,z1,z4,z62,z6]),(0,[z0,z58,z2,z4,z81,z156]),(0,[z0,z1,z2,z4,z5,z953])],[(0,[z0,z1,z2,z954,z5,z6]),(0,[z0,z955,z2,z4,z5,z6])],[(0,[z50,z0,z2,z4,z5,z48]),(0,[z0,z2,z727,z4,z5,z6]),(0,[z0,z47,z2,z4,z5,z156]),(0,[z0,z1,z2,z4,z64,z268]),(0,[z0,z673,z1,z4,z5,z195])],[(0,[z0,z1,z2,z383,z5,z386]),(0,[z0,z1,z2,z4,z311,z6]),(0,[z76,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z5,z746,z70])],[(0,[z0,z1,z571,z140,z5,z6]),(0,[z469,z0,z1,z2,z137,z6]),(0,[z0,z1,z2,z4,z39,z67]),(0,[z0,z956,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z392,z140,z5,z6]),(0,[z0,z1,z2,z4,z72,z48])],[(0,[z50,z131,z2,z4,z5,z13]),(0,[z0,z957,z1,z2,z4,z5]),(0,[z958,z0,z2,z4,z5,z6])],[(0,[z0,z1,z571,z4,z150,z6]),(0,[z0,z1,z2,z4,z5,z959]),(0,[z0,z1,z494,z2,z4,z5]),(0,[z0,z265,z2,z4,z5,z775]),(0,[z0,z382,z2,z85,z5,z6]),(0,[z0,z228,z2,z4,z5,z70])],[(0,[z0,z1,z392,z4,z150,z6]),(0,[z139,z190,z2,z4,z5,z386]),(0,[z113,z1,z2,z4,z725,z6]),(0,[z0,z37,z25,z4,z5,z48]),(0,[z0,z1,z2,z4,z39,z48]),(0,[z0,z496,z2,z85,z5,z6]),(0,[z0,z87,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z960,z48]),(0,[z0,z1,z2,z4,z5,z961]),(0,[z0,z1,z4,z5,z121,z6]),(0,[z962,z1,z2,z4,z5,z6])],[(0,[z0,z820,z66,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z963]),(0,[z0,z1,z2,z964,z5,z6]),(0,[z0,z965,z2,z4,z5,z6]),(0,[z0,z87,z2,z4,z5,z269])],[(0,[z0,z1,z966,z4,z5,z6]),(0,[z180,z0,z2,z4,z5,z198]),(0,[z0,z1,z2,z136,z5,z152]),(0,[z0,z1,z2,z967,z5,z6]),(0,[z76,z0,z1,z4,z5,z13])],[(0,[z0,z1,z2,z4,z5,z968]),(0,[z139,z0,z2,z140,z5,z48]),(0,[z368,z99,z1,z24,z5,z6])]],
   [[(0,[z0,z736,z2,z4,z5,z6]),(0,[z147,z244,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z969]),(0,[z970,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z126,z6]),(0,[z1,z2,z4,z5,z971,z6]),(0,[z0,z2,z4,z62,z268,z48]),(0,[z112,z0,z2,z4,z5,z722]),(0,[z0,z1,z2,z5,z122,z269]),(0,[z0,z1,z2,z4,z500,z6])],[(0,[z99,z1,z24,z4,z5,z173]),(0,[z0,z1,z2,z972,z5,z6]),(0,[z0,z117,z1,z2,z4,z712])],[(0,[z0,z1,z2,z383,z5,z6]),(0,[z139,z0,z2,z4,z5,z48]),(0,[z139,z0,z2,z4,z150,z48]),(0,[z0,z229,z2,z4,z5,z22]),(0,[z0,z170,z1,z2,z122,z13]),(0,[z0,z1,z2,z4,z5,z973]),(0,[z0,z1,z2,z84,z645,z6])],[(0,[z974,z0,z1,z2,z5,z6]),(0,[z99,z1,z24,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z975]),(0,[z0,z1,z2,z976,z5,z6]),(0,[z32,z0,z1,z251,z5,z6]),(0,[z0,z2,z4,z5,z670,z48]),(0,[z0,z1,z4,z5,z121,z13]),(0,[z0,z2,z4,z5,z13,z574]),(0,[z0,z1,z2,z4,z5,z977])],[(0,[z0,z1,z571,z4,z5,z189]),(0,[z50,z0,z2,z4,z5,z300]),(0,[z0,z1,z2,z4,z978,z6]),(0,[z979,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z980]),(0,[z0,z332,z2,z84,z5,z6])],[(0,[z0,z1,z392,z4,z5,z189]),(0,[z0,z1,z981,z4,z5,z6]),(0,[z0,z1,z2,z136,z5,z48]),(0,[z0,z560,z1,z2,z122,z6])],[(0,[z0,z1,z982,z4,z5,z6]),(0,[z50,z736,z2,z4,z5,z6]),(0,[z0,z1,z2,z137,z5,z48]),(0,[z0,z662,z2,z4,z5,z48]),(0,[z0,z1,z983,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z984])],[(0,[z139,z190,z2,z4,z5,z6]),(0,[z0,z2,z4,z150,z6,z48]),(0,[z0,z1,z2,z4,z985,z6]),(0,[z0,z1,z2,z4,z151,z67]),(0,[z0,z1,z2,z986,z5,z6]),(0,[z0,z1,z2,z4,z711,z6])]],
   [[(0,[z80,z0,z1,z696,z4,z6]),(0,[z0,z1,z2,z243,z5,z6]),(0,[z0,z1,z2,z4,z126,z13]),(0,[z0,z1,z2,z4,z987,z6]),(0,[z0,z2,z4,z5,z683,z48]),(0,[z0,z1,z2,z4,z500,z13])],[(0,[z469,z0,z265,z2,z4,z6]),(0,[z0,z281,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z988,z6])],[(0,[z0,z1,z2,z383,z5,z13]),(0,[z0,z1,z2,z4,z5,z989]),(0,[z0,z1,z2,z4,z5,z741]),(0,[z0,z2,z4,z5,z532,z48]),(0,[z323,z0,z2,z4,z5,z48]),(0,[z0,z990,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z991]),(0,[z0,z1,z2,z4,z151,z48]),(0,[z0,z992,z1,z2,z5,z6])],[(0,[z0,z1,z2,z4,z5,z993]),(0,[z0,z132,z1,z2,z521,z4]),(0,[z0,z1,z2,z4,z5,z994]),(0,[z0,z2,z4,z5,z48,z226]),(0,[z979,z1,z2,z4,z5,z13])],[(0,[z0,z1,z109,z4,z5,z100]),(0,[z368,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z311,z552]),(0,[z0,z1,z2,z4,z829,z6]),(0,[z0,z245,z1,z2,z4,z500])],[(0,[z0,z132,z1,z274,z4,z5]),(0,[z0,z2,z4,z81,z829,z6]),(0,[z0,z1,z2,z4,z5,z995])],[(0,[z0,z2,z4,z106,z62,z48]),(0,[z0,z1,z168,z4,z5,z48]),(0,[z0,z1,z483,z4,z5,z19]),(0,[z0,z229,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z878]),(1,[z0,z1,z2,z224,z71])]],
   [[(0,[z0,z1,z2,z14,z5,z199]),(0,[z0,z1,z2,z69,z5,z319]),(0,[z0,z1,z2,z4,z996,z6]),(0,[z0,z172,z2,z69,z4,z5])],[(0,[z139,z0,z2,z4,z5,z300]),(0,[z0,z1,z2,z4,z5,z997]),(0,[z486,z1,z2,z4,z5,z154]),(0,[z0,z2,z4,z5,z554,z48]),(0,[z0,z1,z192,z4,z5,z225]),(0,[z0,z1,z998,z2,z4,z5]),(0,[z0,z1,z143,z4,z96,z6])],[(0,[z0,z1,z2,z999,z5,z6]),(0,[z0,z1,z2,z4,z5,z1000]),(0,[z0,z1,z24,z4,z5,z100]),(0,[z0,z2,z4,z829,z62,z6])],[(0,[z139,z736,z2,z4,z5,z6]),(0,[z99,z1,z521,z24,z4,z6]),(0,[z0,z1,z1001,z4,z5,z6]),(0,[z0,z1,z1002,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z199])],[(0,[z0,z1,z2,z1003,z5,z6]),(0,[z0,z2,z91,z727,z5,z6]),(0,[z0,z58,z2,z4,z5,z380]),(0,[z0,z1,z2,z314,z81,z6]),(0,[z0,z634,z2,z4,z5,z48]),(0,[z0,z1004,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1005]),(0,[z0,z1,z2,z4,z5,z1006]),(0,[z1007,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z386]),(0,[z0,z1,z2,z1008,z5,z6]),(0,[z0,z1,z2,z4,z5,z1009]),(0,[z0,z1,z2,z4,z6,z1010]),(0,[z220,z1,z2,z4,z106,z6]),(0,[z0,z1,z2,z4,z5,z1011]),(0,[z0,z1,z2,z4,z5,z1012]),(0,[z0,z1,z7,z8,z5,z48])],[(0,[z0,z1,z2,z4,z5,z1013]),(0,[z0,z1,z1014,z4,z5,z6]),(0,[z0,z565,z2,z4,z5,z48]),(0,[z0,z331,z2,z85,z5,z48])]],
   [[(1,[z0,z2,z4,z5,z722]),(0,[z0,z1,z2,z4,z5,z746])],[(0,[z330,z50,z2,z4,z5,z48]),(0,[z0,z1,z2,z1015,z5,z6]),(0,[z0,z1,z1016,z4,z5,z6]),(0,[z0,z1,z143,z4,z96,z13]),(0,[z0,z1,z2,z4,z1017,z6]),(0,[z0,z1018,z2,z4,z5,z6]),(0,[z0,z227,z228,z2,z5,z70]),(0,[z0,z172,z2,z4,z5,z71])],[(0,[z211,z1,z2,z116,z5,z6]),(0,[z0,z1,z2,z4,z5,z770]),(1,[z0,z1,z728,z5,z6]),(0,[z0,z1,z2,z4,z1019,z6]),(0,[z76,z0,z245,z1,z4,z5]),(0,[z0,z1,z2,z69,z5,z616]),(0,[z0,z1,z2,z500,z6,z70])],[(0,[z0,z1020,z2,z4,z5,z6]),(0,[z113,z1,z2,z4,z107,z6]),(0,[z0,z18,z1,z274,z4,z5]),(0,[z0,z1,z814,z4,z5,z6]),(0,[z0,z18,z1,z4,z5,z540])],[(0,[z0,z1,z2,z1021,z5,z6]),(0,[z99,z1,z494,z24,z4,z5]),(0,[z0,z2,z4,z36,z5,z48]),(0,[z0,z560,z1,z2,z5,z70])],[(0,[z0,z1022,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1023]),(0,[z0,z61,z2,z4,z62,z152]),(0,[z0,z714,z2,z4,z5,z122])],[(0,[z0,z1,z1024,z4,z5,z6]),(0,[z469,z0,z132,z1,z2,z4]),(0,[z0,z1,z1025,z4,z5,z6]),(0,[z0,z2,z4,z5,z51,z48]),(0,[z0,z2,z4,z314,z62,z6]),(0,[z0,z1,z4,z96,z745,z6])],[(0,[z0,z1026,z1,z2,z4,z6]),(0,[z0,z1027,z2,z4,z5,z6]),(0,[z0,z1,z2,z1028,z5,z6]),(0,[z0,z1,z2,z14,z5,z6])]],
   [[(0,[z46,z1,z2,z4,z725,z6]),(0,[z232,z0,z2,z4,z5,z48])],[(1,[z736,z2,z4,z5,z6]),(0,[z0,z1,z2,z521,z4,z6]),(0,[z0,z1,z2,z4,z1029,z6]),(0,[z452,z0,z1,z2,z122,z6]),(0,[z80,z0,z1,z4,z12,z13])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z139,z190,z571,z4,z5,z6]),(0,[z0,z66,z2,z4,z5,z48]),(0,[z0,z2,z4,z1030,z5,z6]),(0,[z925,z1,z2,z4,z5,z6]),(1,[z0,z332,z2,z122,z6])],[(0,[z139,z190,z392,z4,z5,z6]),(0,[z0,z1031,z1,z2,z4,z5]),(0,[z0,z2,z4,z5,z198,z48]),(0,[z0,z1032,z2,z4,z5,z6]),(0,[z0,z1033,z2,z4,z5,z6]),(0,[z46,z1,z2,z4,z106,z13]),(0,[z0,z1,z2,z4,z5,z1034]),(0,[z0,z1,z2,z4,z5,z425])],[(0,[z0,z281,z2,z91,z5,z6]),(0,[z0,z250,z2,z4,z5,z6]),(0,[z0,z491,z2,z4,z62,z6]),(0,[z0,z61,z2,z4,z62,z48]),(0,[z0,z643,z2,z4,z5,z48])],[(0,[z139,z0,z2,z383,z5,z48]),(1,[z0,z718,z4,z5,z6]),(0,[z0,z58,z2,z4,z5,z425]),(0,[z0,z47,z2,z699,z5,z6])],[(0,[z50,z2,z4,z5,z182,z6]),(0,[z0,z2,z84,z85,z5,z48]),(0,[z1035,z1,z2,z4,z5,z6]),(0,[z32,z0,z1,z255,z5,z6]),(0,[z0,z117,z1,z2,z4,z71])],[(0,[z0,z1,z2,z140,z5,z48]),(0,[z0,z1,z2,z4,z1036,z6]),(0,[z0,z2,z602,z4,z5,z48]),(0,[z76,z0,z1,z4,z81,z6]),(0,[z486,z0,z2,z4,z5,z48]),(0,[z0,z317,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z712])]],
   [[(0,[z0,z618,z2,z4,z81,z6]),(0,[z0,z1,z2,z4,z5,z1037]),(0,[z0,z58,z2,z314,z5,z6]),(0,[z0,z332,z2,z4,z5,z48])],[(0,[z0,z1,z2,z4,z1038,z6]),(0,[z139,z217,z2,z4,z5,z6]),(0,[z0,z1,z2,z521,z4,z13]),(0,[z0,z103,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z1039]),(0,[z447,z0,z1,z2,z5,z145]),(0,[z0,z583,z2,z4,z5,z13])],[(0,[z0,z1,z2,z4,z5,z1040])],[(0,[z0,z1,z2,z4,z1041,z6]),(0,[z0,z1,z2,z4,z5,z1042]),(0,[z0,z47,z2,z4,z311,z6]),(0,[z0,z1,z2,z224,z5,z71])],[(0,[z0,z1,z2,z4,z5,z1043]),(0,[z1,z2,z4,z725,z107,z6]),(0,[z0,z58,z2,z4,z481,z6]),(0,[z0,z250,z2,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z269]),(0,[z0,z227,z1,z2,z224,z5])],[(0,[z0,z1,z859,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1044])],[(0,[z0,z1,z2,z4,z1045,z6]),(0,[z0,z1,z1046,z4,z5,z6]),(0,[z50,z0,z2,z4,z5,z285]),(0,[z0,z1,z2,z4,z5,z1047]),(0,[z0,z1,z1048,z4,z5,z6]),(0,[z0,z2,z85,z5,z319,z48]),(0,[z0,z61,z2,z136,z62,z6]),(0,[z112,z0,z2,z4,z5,z22]),(0,[z0,z1,z2,z4,z234,z65]),(0,[z0,z170,z1,z2,z123,z122]),(0,[z0,z117,z172,z2,z4,z71])],[(0,[z0,z1,z1049,z2,z4,z5]),(0,[z0,z585,z1,z4,z5,z195]),(0,[z0,z634,z2,z91,z5,z6]),(0,[z0,z1,z2,z4,z915,z48]),(0,[z0,z946,z2,z4,z5,z6]),(1,[z0,z1,z2,z500,z70])]],
   [[(0,[z0,z1,z274,z4,z5,z48]),(0,[z0,z1,z2,z69,z5,z546])],[(0,[z0,z1,z571,z4,z5,z386]),(0,[z0,z1,z2,z4,z72,z189]),(0,[z0,z1,z2,z4,z5,z1050]),(0,[z0,z1,z2,z1051,z5,z6]),(0,[z0,z250,z2,z4,z83,z6]),(0,[z0,z250,z227,z2,z5,z70])],[(0,[z0,z1,z1052,z4,z5,z6]),(0,[z0,z1,z2,z4,z1053,z6]),(0,[z0,z132,z1,z2,z137,z5]),(0,[z0,z1,z2,z4,z1054,z6]),(0,[z0,z37,z25,z4,z5,z13]),(0,[z0,z223,z2,z85,z5,z13]),(0,[z0,z1,z2,z291,z5,z13]),(0,[z0,z427,z1,z2,z5,z70])],[(1,[z0,z2,z383,z5,z48]),(0,[z0,z1,z2,z4,z5,z1055])],[(0,[z0,z2,z4,z5,z6,z1056]),(0,[z0,z149,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z1057,z6]),(0,[z0,z58,z2,z4,z572,z6]),(0,[z0,z1,z2,z4,z5,z1058]),(0,[z0,z1,z2,z184,z171,z6])],[(0,[z435,z1,z2,z141,z5,z6]),(0,[z0,z346,z2,z4,z5,z13]),(0,[z180,z1,z168,z4,z5,z236]),(0,[z0,z628,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z818])],[(0,[z0,z2,z4,z5,z386,z48]),(0,[z0,z1,z2,z5,z711,z6])],[(0,[z0,z494,z66,z2,z4,z5]),(0,[z0,z2,z4,z159,z5,z48]),(0,[z0,z1,z2,z4,z5,z1059]),(0,[z0,z2,z4,z5,z198,z195])]],
   [[(0,[z0,z1,z2,z4,z1060,z6]),(0,[z0,z1061,z1,z2,z4,z5]),(0,[z0,z1,z728,z53,z5,z6])],[(0,[z0,z1,z2,z1062,z5,z6]),(0,[z0,z1,z2,z4,z1063,z6]),(0,[z0,z1,z2,z4,z5,z552]),(0,[z0,z2,z4,z5,z62,z380]),(0,[z0,z2,z4,z5,z637,z48])],[(0,[z0,z37,z392,z4,z5,z6]),(0,[z0,z2,z4,z5,z1064,z6]),(0,[z0,z38,z142,z4,z5,z67]),(0,[z0,z1,z2,z4,z5,z1065]),(0,[z0,z172,z2,z291,z5,z6])],[(0,[z139,z0,z2,z4,z5,z285])],[(0,[z0,z1,z2,z4,z1066,z6]),(0,[z469,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z243,z5,z199]),(0,[z0,z1067,z2,z4,z5,z6])],[(0,[z0,z1,z571,z4,z5,z6]),(0,[z0,z1068,z2,z4,z5,z6]),(0,[z0,z2,z4,z107,z62,z48]),(0,[z0,z170,z1,z2,z122,z6]),(0,[z0,z1,z2,z4,z5,z123])],[(0,[z0,z1,z392,z4,z5,z6]),(0,[z99,z1,z24,z4,z5,z6]),(0,[z0,z1,z1069,z2,z4,z5]),(0,[z0,z38,z142,z4,z39,z6]),(0,[z0,z228,z2,z4,z5,z6]),(0,[z0,z1070,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1071,z5,z6]),(0,[z0,z1,z2,z4,z5,z1072]),(0,[z0,z332,z2,z4,z122,z6])]],
   [[(0,[z0,z1,z2,z4,z311,z82]),(0,[z0,z95,z1,z2,z4,z71])],[(0,[z0,z1,z2,z1073,z5,z6]),(0,[z0,z132,z1,z4,z5,z195]),(0,[z0,z1,z2,z1074,z5,z6]),(0,[z0,z1,z2,z1075,z5,z6]),(0,[z0,z1,z2,z4,z311,z48]),(0,[z0,z223,z2,z85,z311,z6]),(0,[z80,z0,z2,z4,z62,z48]),(0,[z0,z143,z2,z4,z62,z48]),(0,[z0,z2,z4,z202,z5,z48]),(0,[z0,z227,z1,z2,z5,z70])],[(0,[z0,z1,z1076,z4,z5,z6]),(0,[z0,z1,z2,z1077,z5,z6]),(0,[z0,z38,z718,z4,z5,z6])],[],[(0,[z0,z265,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1078,z6]),(0,[z469,z0,z1,z2,z4,z13]),(0,[z573,z1,z24,z4,z5,z6]),(1,[z0,z1,z2,z122,z269])],[(0,[z0,z1,z571,z4,z5,z13]),(0,[z0,z1,z2,z4,z5,z1079]),(0,[z1,z109,z859,z4,z5,z6]),(0,[z0,z1,z4,z96,z523,z6]),(0,[z0,z1,z2,z4,z5,z1080]),(0,[z0,z250,z2,z4,z500,z6]),(0,[z0,z117,z1,z2,z4,z500])],[(0,[z0,z142,z392,z4,z5,z6]),(0,[z0,z1,z392,z4,z5,z13]),(0,[z0,z228,z2,z4,z5,z13]),(0,[z503,z0,z1,z2,z4,z226]),(0,[z0,z229,z2,z4,z5,z13]),(0,[z0,z170,z245,z1,z2,z122]),(0,[z0,z1,z714,z2,z4,z5])],[(0,[z0,z1081,z2,z4,z5,z6]),(0,[z0,z142,z718,z4,z5,z6]),(0,[z0,z2,z4,z671,z5,z48])]],
   [[(0,[z0,z1,z2,z1082,z4,z6]),(0,[z0,z179,z2,z4,z5,z48]),(0,[z30,z0,z2,z4,z5,z198]),(0,[z0,z1,z2,z1083,z5,z6]),(0,[z0,z677,z2,z4,z5,z48]),(0,[z0,z485,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z1084]),(0,[z0,z245,z1,z2,z224,z5])],[(0,[z0,z249,z2,z4,z5,z48]),(0,[z0,z1,z4,z5,z745,z6]),(0,[z0,z1085,z2,z4,z5,z6])],[(0,[z247,z0,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z1086]),(0,[z0,z1,z2,z4,z5,z1087]),(0,[z0,z1,z2,z4,z5,z1088])],[(0,[z0,z1089,z1,z2,z5,z6]),(0,[z0,z1090,z2,z4,z5,z6]),(0,[z0,z223,z2,z85,z126,z6]),(0,[z0,z47,z2,z91,z5,z48]),(0,[z0,z228,z2,z4,z83,z6]),(0,[z0,z172,z2,z4,z5,z554])],[(0,[z230,z0,z2,z4,z5,z48]),(0,[z0,z265,z2,z4,z5,z13]),(0,[z0,z686,z2,z4,z5,z48]),(0,[z0,z1,z2,z727,z5,z6]),(0,[z0,z1091,z1,z4,z5,z6]),(0,[z0,z1,z2,z224,z5,z48])],[],[(1,[z1,z859,z4,z5,z6]),(0,[z0,z227,z1,z2,z83,z70])],[(0,[z139,z190,z2,z4,z72,z6]),(0,[z0,z47,z2,z4,z5,z770]),(0,[z0,z1,z2,z122,z70,z71])]],
   [[(0,[z1,z859,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z776])],[(0,[z139,z50,z2,z4,z5,z48]),(0,[z0,z115,z2,z4,z62,z6]),(0,[z32,z0,z1,z360,z5,z6]),(0,[z0,z331,z1,z2,z5,z70]),(0,[z0,z1092,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1093]),(0,[z139,z190,z2,z4,z5,z48]),(0,[z0,z58,z2,z4,z829,z6]),(0,[z0,z331,z1,z2,z5,z86])],[(0,[z0,z1,z2,z4,z1094,z6]),(0,[z0,z142,z433,z4,z5,z6]),(0,[z0,z2,z4,z5,z1095,z6]),(0,[z0,z1,z2,z243,z39,z6]),(0,[z0,z1,z2,z282,z5,z319]),(0,[z0,z15,z2,z4,z5,z48]),(0,[z0,z1,z90,z4,z5,z871]),(0,[z0,z1096,z2,z4,z5,z6])],[(0,[z544,z1,z2,z92,z5,z6]),(0,[z32,z0,z1,z53,z5,z6]),(0,[z76,z0,z1,z4,z5,z123])],[(0,[z0,z265,z142,z4,z5,z6]),(0,[z147,z1,z2,z92,z5,z48]),(0,[z1,z2,z4,z752,z5,z6]),(0,[z0,z58,z2,z4,z81,z6]),(0,[z0,z2,z4,z704,z5,z48]),(0,[z0,z2,z4,z5,z48,z667]),(0,[z0,z409,z2,z4,z5,z13])],[(0,[z99,z132,z1,z24,z4,z5]),(0,[z211,z1,z2,z141,z5,z48]),(0,[z180,z1,z274,z4,z5,z236]),(0,[z0,z1,z209,z4,z5,z162]),(0,[z1097,z1,z2,z4,z5,z6])],[(0,[z0,z947,z66,z2,z4,z5]),(0,[z0,z1098,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1099]),(0,[z1100,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z64,z65])]],
   [[(0,[z0,z1,z1101,z4,z5,z6]),(0,[z368,z0,z1,z2,z5,z48]),(0,[z0,z1,z2,z4,z5,z1102])],[(0,[z0,z1,z2,z4,z5,z855]),(0,[z0,z1,z2,z4,z5,z1103]),(0,[z0,z517,z2,z4,z5,z48]),(0,[z0,z505,z1,z2,z122,z6]),(0,[z0,z1,z2,z4,z6,z712])],[(0,[z0,z1,z2,z4,z126,z552]),(0,[z0,z1,z2,z84,z171,z48]),(0,[z0,z1,z2,z4,z5,z1104])],[(0,[z368,z0,z66,z2,z5,z6]),(0,[z0,z1,z2,z4,z1105,z6]),(0,[z112,z0,z2,z4,z5,z51]),(0,[z0,z1,z2,z224,z64,z6])],[(0,[z0,z1106,z2,z4,z5,z6]),(0,[z1107,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1108]),(0,[z0,z1,z2,z91,z311,z6]),(0,[z0,z169,z2,z4,z5,z48]),(0,[z0,z372,z1,z4,z5,z195]),(0,[z32,z0,z1,z53,z5,z13]),(0,[z80,z0,z1,z4,z12,z6])],[(0,[z0,z1109,z1,z2,z4,z5]),(0,[z56,z1,z2,z4,z107,z6]),(0,[z0,z1,z2,z4,z5,z10]),(0,[z0,z1,z2,z4,z1110,z6]),(1,[z0,z2,z85,z311,z6]),(0,[z0,z58,z2,z4,z81,z13]),(0,[z0,z1,z2,z4,z5,z938]),(0,[z0,z1,z2,z224,z6,z71])],[(0,[z46,z1,z2,z4,z106,z6]),(0,[z0,z1111,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1112,z5,z6]),(0,[z0,z265,z494,z2,z4,z5]),(0,[z0,z1,z2,z4,z1113,z6]),(0,[z0,z228,z2,z4,z500,z6])]],
   [[(0,[z0,z1,z571,z383,z5,z6]),(0,[z139,z0,z571,z4,z5,z48]),(0,[z99,z265,z24,z4,z5,z6]),(0,[z0,z1114,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1115]),(0,[z0,z229,z2,z224,z5,z6])],[(0,[z0,z1,z392,z383,z5,z6]),(0,[z139,z0,z392,z4,z5,z48]),(0,[z0,z1,z2,z1116,z5,z6]),(0,[z0,z1,z2,z4,z1117,z6]),(0,[z0,z1,z2,z1118,z5,z6]),(0,[z0,z581,z2,z91,z5,z6]),(0,[z0,z1,z2,z4,z5,z1119]),(0,[z80,z0,z1,z4,z705,z6]),(0,[z0,z1,z2,z69,z64,z122])],[(0,[z404,z0,z2,z4,z5,z48]),(0,[z0,z87,z2,z4,z5,z391]),(0,[z0,z1,z2,z4,z64,z440]),(0,[z0,z227,z1,z2,z500,z70])],[(0,[z0,z1,z2,z4,z1120,z6]),(0,[z1121,z0,z1,z2,z4,z6]),(0,[z0,z2,z4,z5,z1122,z6]),(0,[z0,z95,z2,z4,z62,z6]),(0,[z0,z1,z2,z4,z6,z1123])],[(0,[z0,z1,z2,z4,z5,z1124]),(0,[z0,z1,z2,z4,z5,z1125]),(0,[z0,z1,z2,z4,z6,z1126]),(0,[z0,z1,z2,z4,z1127,z6]),(0,[z0,z169,z2,z4,z5,z722]),(1,[z0,z1,z4,z5,z871]),(0,[z0,z1,z2,z122,z6,z269])],[(0,[z0,z1,z2,z1128,z5,z6]),(0,[z0,z1,z2,z4,z5,z1129]),(0,[z0,z1,z2,z1130,z5,z6]),(0,[z0,z1,z2,z4,z1131,z5])],[(0,[z0,z1,z2,z4,z5,z1132]),(0,[z0,z1,z2,z14,z5,z67]),(0,[z0,z1,z2,z1133,z5,z6]),(0,[z0,z1,z2,z4,z5,z152])],[(0,[z0,z1,z2,z140,z72,z6]),(0,[z573,z1,z2,z4,z5,z236]),(0,[z0,z1,z2,z4,z5,z1134]),(0,[z0,z1,z2,z136,z5,z380]),(0,[z0,z1,z2,z4,z5,z1135]),(0,[z0,z1,z2,z4,z5,z1136])]],
   [[(0,[z0,z2,z383,z5,z6,z48]),(0,[z0,z1,z2,z4,z5,z1137]),(0,[z0,z170,z332,z2,z122,z6])],[(0,[z0,z2,z4,z5,z19,z198]),(0,[z0,z1,z2,z4,z5,z67]),(0,[z0,z1,z2,z841,z5,z6]),(0,[z0,z1138,z2,z4,z5,z6]),(0,[z0,z228,z2,z4,z5,z532])],[(0,[z0,z1,z2,z4,z72,z6]),(0,[z112,z0,z2,z4,z150,z6]),(0,[z0,z1,z2,z4,z1139,z6]),(0,[z0,z1,z2,z4,z5,z1140]),(0,[z0,z1,z2,z14,z5,z48]),(0,[z0,z1,z2,z14,z39,z6]),(0,[z0,z2,z314,z5,z62,z6]),(0,[z0,z1,z2,z314,z5,z152]),(0,[z0,z1,z2,z4,z5,z1141]),(0,[z0,z1,z2,z1142,z5,z6])],[(0,[z0,z1143,z2,z4,z5,z6]),(0,[z0,z47,z2,z91,z5,z51]),(0,[z0,z2,z4,z312,z5,z48])],[(0,[z0,z2,z101,z4,z5,z48]),(0,[z0,z1,z2,z4,z5,z82]),(0,[z0,z528,z2,z4,z5,z48])],[(0,[z0,z1,z2,z4,z5,z48]),(0,[z0,z1,z2,z4,z150,z48]),(0,[z0,z37,z25,z4,z5,z6]),(0,[z0,z1,z2,z4,z39,z6]),(0,[z0,z223,z2,z85,z5,z6]),(0,[z0,z1,z1144,z4,z5,z6]),(0,[z0,z1,z2,z4,z960,z6]),(0,[z681,z0,z1,z4,z5,z540]),(0,[z0,z1,z2,z291,z5,z6])],[(0,[z1145,z0,z2,z4,z5,z6]),(0,[z0,z1,z1146,z4,z5,z6]),(0,[z0,z2,z85,z5,z311,z6]),(0,[z0,z2,z4,z85,z5,z82]),(0,[z0,z2,z4,z5,z48,z23]),(0,[z0,z1,z2,z4,z5,z1147]),(0,[z0,z332,z2,z5,z122,z6])],[(0,[z108,z1,z859,z4,z5,z6]),(0,[z0,z2,z4,z5,z1148,z6]),(0,[z0,z2,z4,z5,z114,z48]),(0,[z0,z2,z4,z85,z5,z48]),(0,[z330,z1,z2,z4,z5,z52]),(0,[z0,z1,z4,z5,z6,z871])]],
   [[(0,[z0,z66,z2,z137,z5,z6]),(0,[z0,z1,z2,z4,z5,z1149]),(0,[z0,z1,z2,z69,z500,z6])],[(0,[z0,z1150,z2,z4,z5,z6]),(0,[z469,z99,z1,z24,z4,z6]),(0,[z0,z1151,z1,z2,z5,z6]),(0,[z0,z1,z2,z314,z5,z48]),(0,[z0,z2,z4,z62,z122,z48]),(0,[z0,z1,z2,z84,z711,z6])],[(0,[z0,z1,z2,z4,z72,z13]),(0,[z139,z0,z2,z4,z5,z710]),(0,[z112,z0,z2,z4,z5,z13]),(0,[z0,z2,z4,z5,z128,z48]),(0,[z0,z1,z914,z4,z5,z48]),(0,[z0,z1,z4,z5,z871,z195])],[],[(0,[z0,z1,z2,z4,z5,z1152]),(0,[z0,z1,z2,z4,z5,z1153]),(0,[z0,z1,z2,z919,z5,z48])],[(0,[z0,z1,z392,z4,z5,z386]),(0,[z108,z1,z109,z4,z5,z48]),(0,[z0,z1,z1154,z4,z5,z6]),(0,[z0,z2,z141,z85,z5,z48]),(0,[z0,z1,z2,z4,z39,z13]),(0,[z0,z390,z2,z4,z62,z6]),(0,[z0,z1,z2,z4,z5,z722]),(0,[z0,z87,z2,z4,z5,z13])],[(0,[z0,z400,z2,z4,z5,z48]),(0,[z0,z87,z2,z4,z5,z928]),(0,[z0,z1155,z2,z4,z5,z6])],[(0,[z0,z132,z1,z2,z4,z5]),(0,[z0,z1,z2,z136,z5,z6]),(0,[z0,z2,z4,z5,z13,z592]),(0,[z0,z1156,z1,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 528) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 528).take 514) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1042).take 184) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1226)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [528, 514, 184] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 86).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 86).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 174).take 82).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [86, 88, 82] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

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

end PEqualNP.Outside.L_meta_42816

theorem PEqualNP.Outside.L_meta_42816 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4008372352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4008372352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_42816.solve