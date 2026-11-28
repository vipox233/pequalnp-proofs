import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37473

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
  Nat.testBit (4008241856 * 2 ^ 32 + 3974684864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0606362de1c0dc78#64 ++ 0x03031b16f0e06e3c#64 ++ 0xbe8e7e7fe3c1fcf9#64 ++ 0x5f473f3ff1e0fe7c#64 : BitVec 256),
   (0x00308a9c285a2d0a#64 ++ 0x0018454e142d1685#64 ++ 0xff718f9c7cfe3f1f#64 ++ 0xffb8c7ce3e7f1f8f#64 : BitVec 256),
   (0x29815160560542b4#64 ++ 0x14c0a8b02b02a15a#64 ++ 0xef81f1e07f07c7ff#64 ++ 0xf7c0f8f03f83e3ff#64 : BitVec 256),
   (0x41da01d687e807c0#64 ++ 0x20ed00eb43f403e0#64 ++ 0xf5fe01ff87f807e0#64 ++ 0x7aff00ffc3fc03f0#64 : BitVec 256),
   (0x91efec0007b7b000#64 ++ 0x48f7f60003dbd800#64 ++ 0xfbfffe0007fff800#64 ++ 0x7dffff0003fffc00#64 : BitVec 256),
   (0x1dfdfffb78000000#64 ++ 0x8efefffdbc000000#64 ++ 0xddfffffff8000000#64 ++ 0x6efffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0xff718f9c7cfe3f1f 0xffb8c7ce3e7f1f8f

def z1 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0xbe8e7e7fe3c1fcf9 0x5f473f3ff1e0fe7c

def z2 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0xef81f1e07f07c7ff 0xf7c0f8f03f83e3ff

def z3 : W := mkw 0x2d857769760542b4 0x16c2bbb4bb02a15a 0xff8fffffff07c7ff 0xffc7ffffff83e3ff

def z4 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z5 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0xfbfffe0007fff800 0x7dffff0003fffc00

def z6 : W := mkw 0x0020880000122000 0x0010440000091000 0x41718000043e0000 0x20b8c000021f0000

def z7 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xddfffffff8000000 0x6efffffffc000000

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z9 : W := mkw 0x0404362960000000 0x02021b14b0000000 0x9c8e7e7fe0000000 0x4e473f3ff0000000

def z10 : W := mkw 0x4002000487e807c0 0x2001000243f403e0 0x2000000007f807e0 0x1000000003fc03f0

def z11 : W := mkw 0x1ffffffff9dafd7a 0x8ffffffffced7ebd 0xffffffffffffffff 0xffffffffffffffff

def z12 : W := mkw 0x2821da287817683e 0x1410ed143c0bb41f 0x0a01fe007807f81f 0x8500ff003c03fc0f

def z13 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0x6170018007f807e0 0x30b800c003fc03f0

def z14 : W := mkw 0x99ffedd21fb7b000 0xccfff6e90fdbd800 0xfbffff801ffff800 0x7dffffc00ffffc00

def z15 : W := mkw 0x19f9c9d2181a2102 0x8cfce4e90c0d1081 0x417181801c3e0306 0xa0b8c0c00e1f0183

def z16 : W := mkw 0x0202000481c0dc78 0x0101000240e06e3c 0x2200000003c1fcf9 0x1100000001e0fe7c

def z17 : W := mkw 0xd1ffedd687ffb7c0 0x68fff6eb43ffdbe0 0xffffffff87ffffe0 0x7fffffffc3fffff0

def z18 : W := mkw 0x91cf640007a59000 0x48e7b20003d2c800 0xba8e7e0003c1f800 0x5d473f0001e0fc00

def z19 : W := mkw 0x45de37ffe7e807c0 0x22ef1bfff3f403e0 0xfdfe7fffe7f807e0 0x7eff3ffff3fc03f0

def z20 : W := mkw 0x2981414016050284 0x14c0a0a00b028142 0x410181801c060306 0xa080c0c00e030183

def z21 : W := mkw 0x3dfdfffb7e0542b4 0x9efefffdbf02a15a 0xffffffffff07c7ff 0xffffffffff83e3ff

def z22 : W := mkw 0x405a009681e80540 0x202d004b40f402a0 0x107e001f80f80000 0x083f000fc07c0000

def z23 : W := mkw 0x69db51f6d7ed47f4 0x34eda8fb6bf6a3fa 0xfffff1ffffffc7ff 0xfffff8ffffffe3ff

def z24 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0x10fe7e7f80000000 0x087f3f3fc0000000

def z25 : W := mkw 0x59fbc9d69fe807c0 0xacfde4eb4ff403e0 0xf5ff81ff9ff807e0 0x7affc0ffcffc03f0

def z26 : W := mkw 0x69835164d7ed47f4 0x34c1a8b26bf6a3fa 0xef81f1e07fffc7ff 0xf7c0f8f03fffe3ff

def z27 : W := mkw 0x00000000001a2102 0x00000000000d1081 0x00000000043e0306 0x80000000021f0183

def z28 : W := mkw 0x00000004005a2d0a 0x00000002002d1685 0x2200000004fe3f1f 0x91000000027f1f8f

def z29 : W := mkw 0x147cae9b28000000 0x8a3e574d94000000 0x107e0e1f80000000 0x083f070fc0000000

def z30 : W := mkw 0x00208a082812280a 0x0010450414091405 0x0a018e007806381f 0x8500c7003c031c0f

def z31 : W := mkw 0x1ddd75f350000000 0x8eeebaf9a8000000 0xd5fe71ff80000000 0x6aff38ffc0000000

def z32 : W := mkw 0x19fdedd218000000 0x8cfef6e90c000000 0xd9ffff8018000000 0x6cffffc00c000000

def z33 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0x4b01f1807c07c31f 0xa580f8c03e03e18f

def z34 : W := mkw 0x2c1013fb780042b4 0x960809fdbc00215a 0x040001fff80007ff 0x820000fffc0003ff

def z35 : W := mkw 0x0180000006000000 0x00c0000003000000 0xe180000007000000 0x70c0000003800000

def z36 : W := mkw 0x01d801d200000000 0x00ec00e900000000 0xd5fe01ff80000000 0x6aff00ffc0000000

def z37 : W := mkw 0x1dcd756350000000 0x8ee6bab1a8000000 0x008e706380000000 0x00473831c0000000

def z38 : W := mkw 0x0006240001809000 0x0003120000c04800 0x008e70000301c000 0x004738000180e000

def z39 : W := mkw 0x91edec000017b000 0x48f6f600000bd800 0xdbfffe000007f800 0x6dffff000003fc00

def z40 : W := mkw 0x2e07762df1c5dc7c 0x1703bb16f8e2ee3e 0xbe8ffe7ffbc7fcff 0xdf47ff3ffde3fe7f

def z41 : W := mkw 0x91efee082fb7b80a 0x48f7f70417dbdc05 0xfbfffe007ffff81f 0xfdffff003ffffc0f

def z42 : W := mkw 0x3da5ff697e0542b4 0x9ed2ffb4bf02a15a 0xef81ffe07f07c7ff 0xf7c0fff03f83e3ff

def z43 : W := mkw 0x0181400006050000 0x00c0a00003028000 0xeb81f0000707c000 0x75c0f8000383e000

def z44 : W := mkw 0x1c7cbffb78000000 0x8e3e5ffdbc000000 0x147e0ffff8000000 0x0a3f07fffc000000

def z45 : W := mkw 0x0636ae9da9dabd4a 0x031b574ed4ed5ea5 0x107e0e1f80f83800 0x083f070fc07c1c00

def z46 : W := mkw 0x0002000481c00440 0x0001000240e00220 0xb48e007f83c004e0 0x5a47003fc1e00270

def z47 : W := mkw 0x9025ec000017b000 0x4812f600000bd800 0x0a01fe000007f800 0x0500ff000003fc00

def z48 : W := mkw 0x47febfffeffafffa 0x23ff5ffff7fd7ffd 0xffffffffffffffff 0xffffffffffffffff

def z49 : W := mkw 0x11fdedd200000000 0x08fef6e900000000 0xddffffff80000000 0x6effffffc0000000

def z50 : W := mkw 0x41da01d687fa2fca 0x20ed00eb43fd17e5 0xf7fe01ff87fe3fff 0xfbff00ffc3ff1fff

def z51 : W := mkw 0x0606260da1c09c48 0x03031306d0e04e24 0x100e0e1f80c03800 0x0807070fc0601c00

def z52 : W := mkw 0x28015020560542b4 0x1400a8102b02a15a 0x2a01f0007f07c7ff 0x9500f8003f83e3ff

def z53 : W := mkw 0x4000000006280380 0x20000000031401c0 0x0000000004380300 0x00000000021c0180

def z54 : W := mkw 0x1dfdffff785a2d0a 0x8efeffffbc2d1685 0xfffffffffcfe3f1f 0xfffffffffe7f1f8f

def z55 : W := mkw 0x0020880000122000 0x0010440000091000 0x10700e0000f83800 0x08380700007c1c00

def z56 : W := mkw 0x19f9c9d218000000 0x8cfce4e90c000000 0x4171818018000000 0x20b8c0c00c000000

def z57 : W := mkw 0x401001d6804807c0 0x200800eb402403e0 0x040001ff800007e0 0x020000ffc00003f0

def z58 : W := mkw 0x1dfffffb79809000 0x8efffffdbcc04800 0xfffffffffbc1f800 0x7ffffffffde0fc00

def z59 : W := mkw 0x91e9c80006372000 0x48f4e400031b9000 0x41718000043e0000 0x20b8c000021f0000

def z60 : W := mkw 0x906eac0001b2b000 0x4837560000d95800 0x107e0e0000f83800 0x083f0700007c1c00

def z61 : W := mkw 0x3dfdfffb780042b4 0x9efefffdbc00215a 0xddfffffff80007ff 0xeefffffffc0003ff

def z62 : W := mkw 0x0404362960004030 0x02021b14b0002018 0xbe8e7e7fe301c4f9 0x5f473f3ff180e27c

def z63 : W := mkw 0x4002000481e80540 0x2001000240f402a0 0x0000000000f80000 0x00000000007c0000

def z64 : W := mkw 0x0981516050000000 0x04c0a8b028000000 0x0080706000000000 0x0040383000000000

def z65 : W := mkw 0x01a1c80006172000 0x00d0e400030b9000 0xfbf1fe0007fff800 0x7df8ff0003fffc00

def z66 : W := mkw 0xd1ffec9687ffb540 0x68fff64b43ffdaa0 0xfbfffe1f87fff800 0x7dffff0fc3fffc00

def z67 : W := mkw 0x404a000281a00040 0x2025000140d00020 0x000e000380000000 0x00070001c0000000

def z68 : W := mkw 0x0600122de0404c78 0x03000916f020263c 0x0400007fe00004f9 0x0200003ff000027c

def z69 : W := mkw 0xd1efed4287b7b2c0 0x68f7f6a143dbd960 0xfbfffe6387fff8e0 0x7dffff31c3fffc70

def z70 : W := mkw 0x69db41d697ed07c4 0x34eda0eb4bf683e2 0xf5ff81ff9ffe07e6 0xfaffc0ffcfff03f3

def z71 : W := mkw 0xd1ffedd207bfb380 0x68fff6e903dfd9c0 0xfbffff8007fffb00 0x7dffffc003fffd80

def z72 : W := mkw 0x2981414016050284 0x14c0a0a00b028142 0xeb81f1801f07c306 0xf5c0f8c00f83e183

def z73 : W := mkw 0x01c8000000000000 0x00e4000000000000 0xd1fe000000000000 0x68ff000000000000

def z74 : W := mkw 0x060436296000d838 0x03021b14b0006c1c 0x9e8e7e7fe001f819 0x4f473f3ff000fc0c

def z75 : W := mkw 0xd1cf654287a592c0 0x68e7b2a143d2c960 0x008e70638301c0e0 0x00473831c180e070

def z76 : W := mkw 0x0010009400480500 0x0008004a00240280 0xf570019c04f80700 0x7ab800ce027c0380

def z77 : W := mkw 0x91ffee9c2fffbd0a 0x48fff74e17ffde85 0xffffff9c7fffff1f 0xffffffce3fffff8f

def z78 : W := mkw 0x9dfffffb7fb7b000 0xcefffffdbfdbd800 0xfffffffffffff800 0x7ffffffffffffc00

def z79 : W := mkw 0x4202000487e8dff8 0x2101000243f46ffc 0x2200000007f9fff9 0x1100000003fcfffc

def z80 : W := mkw 0x47de37ffe7e8dff8 0x23ef1bfff3f46ffc 0xfffe7fffe7f9fff9 0x7fff3ffff3fcfffc

def z81 : W := mkw 0x0c309bff785a2d0a 0x86184dffbc2d1685 0xff718ffffcfe3f1f 0xffb8c7fffe7f1f8f

def z82 : W := mkw 0x15fdee9b28000000 0x8afef74d94000000 0xd9fffe1f80000000 0x6cffff0fc0000000

def z83 : W := mkw 0x28001160500042b4 0x140008b02800215a 0x040001e0780007ff 0x820000f03c0003ff

def z84 : W := mkw 0x1424ae0928000000 0x8a12570494000000 0x00000e0000000000 0x0000070000000000

def z85 : W := mkw 0xa002000007b7f2b4 0x5001000003dbf95a 0x2200000007ffffff 0x9100000003ffffff

def z86 : W := mkw 0x29b1dbfc7e5f6fbe 0x14d8edfe3f2fb7df 0xfff1fffc7fffffff 0xfff8fffe3fffffff

def z87 : W := mkw 0x1ffffffff9c0dc78 0x8ffffffffce06e3c 0xfffffffffbc1fcf9 0x7ffffffffde0fe7c

def z88 : W := mkw 0x0981516050004030 0x04c0a8b028002018 0xef81f1e07b01c4f9 0x77c0f8f03d80e27c

def z89 : W := mkw 0x461013ffe0484ff8 0x230809fff02427fc 0x040001ffe00007f9 0x020000fff00003fc

def z90 : W := mkw 0x97effe2de7f7fc78 0x4bf7ff16f3fbfe3c 0xfffffe7fe7fffcf9 0x7fffff3ff3fffe7c

def z91 : W := mkw 0x906eac0007b7b000 0x4837560003dbd800 0x327e0e0007fff800 0x193f070003fffc00

def z92 : W := mkw 0xb825fc205017f034 0x5c12fe10280bf81a 0x0a01fe007807f81f 0x8500ff003c03fc0f

def z93 : W := mkw 0x0636bebde9dafd7a 0x031b5f5ef4ed7ebd 0xffffffffffffffff 0xffffffffffffffff

def z94 : W := mkw 0x0202000481c09c48 0x0101000240e04e24 0x0000000000c03800 0x0000000000601c00

def z95 : W := mkw 0x1c25fe2978000000 0x8e12ff14bc000000 0x0801fe0078000000 0x0400ff003c000000

def z96 : W := mkw 0xc002000487ffb7c0 0x6001000243ffdbe0 0x2200000007ffffe0 0x1100000003fffff0

def z97 : W := mkw 0x0000020c20400c08 0x0000010610200604 0xbe000e1c60c03c19 0x5f00070e30601e0c

def z98 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0x10700e1c00f83800 0x0838070e007c1c00

def z99 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0x008070600301c0e0 0x004038300180e070

def z100 : W := mkw 0x1dfdfffb78122000 0x8efefffdbc091000 0xfffffffffcfe3800 0x7ffffffffe7f1c00

def z101 : W := mkw 0x8002000407ffbd0a 0x4001000203ffde85 0x2200000007ffff1f 0x9100000003ffff8f

def z102 : W := mkw 0x40000004804807c0 0x20000002402403e0 0x00000000000007e0 0x00000000000003f0

def z103 : W := mkw 0x0000000000000000 0x0000000000000000 0x220000000406071f 0x910000000203038f

def z104 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0x10fe7e0003f9f800 0x087f3f0001fcfc00

def z105 : W := mkw 0x41ca014287a002c0 0x20e500a143d00160 0x008e0063830000e0 0x00470031c1800070

def z106 : W := mkw 0x9025ec000017b000 0x4812f600000bd800 0xfb71fe0004fff800 0x7db8ff00027ffc00

def z107 : W := mkw 0x0d85776970000000 0x06c2bbb4b8000000 0xdd8ffffff8000000 0x6ec7fffffc000000

def z108 : W := mkw 0x01ca000007a00000 0x00e5000003d00000 0x008e000003000000 0x0047000001800000

def z109 : W := mkw 0x000000000012280a 0x0000000000091405 0x020000000006381f 0x8100000000031c0f

def z110 : W := mkw 0x0404342140000000 0x02021a10a0000000 0x008e706380000000 0x00473831c0000000

def z111 : W := mkw 0x01ce240007a09000 0x00e7120003d04800 0xfbfe7e0007f9f800 0x7dff3f0003fcfc00

def z112 : W := mkw 0x01ca000007a00000 0x00e5000003d00000 0xf1fe000007f80000 0x78ff000003fc0000

def z113 : W := mkw 0x00308a9828000000 0x0018454c14000000 0xdd718f9c78000000 0x6eb8c7ce3c000000

def z114 : W := mkw 0x91ebc80007b7b000 0x48f5e40003dbd800 0x6371800007fff800 0x31b8c00003fffc00

def z115 : W := mkw 0x281013fc78484fbe 0x140809fe3c2427df 0x040001fc780007ff 0x820000fe3c0003ff

def z116 : W := mkw 0x95effe2967b7b000 0x4af7ff14b3dbd800 0xfffffe7fe7fff800 0x7fffff3ff3fffc00

def z117 : W := mkw 0x01b08bdc2e5a2f8a 0x00d845ee172d17c5 0xfff18ffc7ffe3fff 0xfff8c7fe3fff1fff

def z118 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a0180007806001f 0x8500c0003c03000f

def z119 : W := mkw 0x401001d200080380 0x200800e9000401c0 0x0000018000000300 0x000000c000000180

def z120 : W := mkw 0xb9effd6057b7f2b4 0x5cf7feb02bdbf95a 0xffffffe07fffffff 0xfffffff03fffffff

def z121 : W := mkw 0x1dfdfffb78004030 0x8efefffdbc002018 0xfffffffffb01c4f9 0x7ffffffffd80e27c

def z122 : W := mkw 0x0400122960000000 0x02000914b0000000 0x0400007fe0000000 0x0200003ff0000000

def z123 : W := mkw 0x41d801d206280380 0x20ec00e9031401c0 0x4170018004380300 0x20b800c0021c0180

def z124 : W := mkw 0x07de37ffe1c0dc78 0x03ef1bfff0e06e3c 0xfffe7fffe3c1fcf9 0x7fff3ffff1e0fe7c

def z125 : W := mkw 0x2801502050054034 0x1400a8102802a01a 0x0a01f0007807c01f 0x8500f8003c03e00f

def z126 : W := mkw 0x0606260da1c09c48 0x03031306d0e04e24 0xbe0e0e1fe0c03c19 0x5f07070ff0601e0c

def z127 : W := mkw 0x1dedff6b78000000 0x8ef6ffb5bc000000 0x088ffe63f8000000 0x0447ff31fc000000

def z128 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0x048e707fe301c4f9 0x0247383ff180e27c

def z129 : W := mkw 0x99f9c9d21e372000 0xccfce4e90f1b9000 0x417181801c3e0000 0x20b8c0c00e1f0000

def z130 : W := mkw 0x0182014487c006c0 0x00c100a243e00360 0xf58e01ff87c007e0 0x7ac700ffc3e003f0

def z131 : W := mkw 0x0000000000000000 0x0000000000000000 0x040001807800071f 0x820000c03c00038f

def z132 : W := mkw 0x4182014487e807c0 0x20c100a243f403e0 0xe58001e007f807e0 0x72c000f003fc03f0

def z133 : W := mkw 0x061012bde8484d7a 0x0308095ef42426bd 0x040001fff80007ff 0x820000fffc0003ff

def z134 : W := mkw 0x01f88bda28000000 0x00fc45ed14000000 0xddff8ffff8000000 0x6effc7fffc000000

def z135 : W := mkw 0x3dfdfffb7e0542b4 0x9efefffdbf02a15a 0xddfffffffb01c0e0 0x6efffffffd80e070

def z136 : W := mkw 0x001001d200000000 0x000800e900000000 0x040001ff80000000 0x020000ffc0000000

def z137 : W := mkw 0x0602122de1c0dc78 0x03010916f0e06e3c 0x2600007fe3c1fcf9 0x1300003ff1e0fe7c

def z138 : W := mkw 0x4dda13ffffe807c0 0xa6ed09fffff403e0 0xf5fe01fffff807e0 0x7aff00fffffc03f0

def z139 : W := mkw 0x0dd813fb78000000 0x86ec09fdbc000000 0xd5fe01fff8000000 0x6aff00fffc000000

def z140 : W := mkw 0x91cf640007a59000 0x48e7b20003d2c800 0xf1fe700007f9c000 0x78ff380003fce000

def z141 : W := mkw 0x0c00116350000000 0x860008b1a8000000 0x0000006380000000 0x00000031c0000000

def z142 : W := mkw 0x01d801d206000280 0x00ec00e903000140 0xf5fe01ff870007e0 0x7aff00ffc38003f0

def z143 : W := mkw 0x41fa8bdeaffa2fca 0x20fd45ef57fd17e5 0xffff8ffffffe3fff 0xffffc7ffffff1fff

def z144 : W := mkw 0x0180014006000280 0x00c000a003000140 0xe58001e0070007e0 0x72c000f0038003f0

def z145 : W := mkw 0xbdfffffb7fb7f2b4 0xdefffffdbfdbf95a 0xffffffffffffffff 0xffffffffffffffff

def z146 : W := mkw 0x00208804005a2d0a 0x00104402002d1685 0xfb718e0004fe3f1f 0xfdb8c700027f1f8f

def z147 : W := mkw 0x00308890081a2102 0x00184448040d1081 0x417181801c3e0306 0xa0b8c0c00e1f0183

def z148 : W := mkw 0x0202020ca1c0dc78 0x0101010650e06e3c 0xbe000e1c63c1fcf9 0x5f00070e31e0fe7c

def z149 : W := mkw 0x41f889d20e3a2382 0x20fc44e9071d11c1 0x417181801c3e0306 0xa0b8c0c00e1f0183

def z150 : W := mkw 0x000002082800080a 0x0000010414000405 0x000000007800001f 0x800000003c00000f

def z151 : W := mkw 0x97effc21c7b7f070 0x4bf7fe10e3dbf838 0xfbfffe6387fff8e0 0x7dffff31c3fffc70

def z152 : W := mkw 0x41da01d287a002c0 0x20ed00e943d00160 0xd5fe01ff830000e0 0x6aff00ffc1800070

def z153 : W := mkw 0x41da01d287a803c0 0x20ed00e943d401e0 0x41fe01e3873803e0 0x20ff00f1c39c01f0

def z154 : W := mkw 0x05dc37fb60000000 0x02ee1bfdb0000000 0xddfe7fffe0000000 0x6eff3ffff0000000

def z155 : W := mkw 0x0010029c28480d0a 0x0008014e14240685 0x0400019c7800071f 0x820000ce3c00038f

def z156 : W := mkw 0x0020880000122000 0x0010440000091000 0xfb718e0004fe3800 0x7db8c700027f1c00

def z157 : W := mkw 0x00328a9ca9da2d4a 0x0019454e54ed16a5 0xffff8ffffffe3fff 0xffffc7ffffff1fff

def z158 : W := mkw 0x8002000007b7b000 0x4001000003dbd800 0x2200000007fff800 0x1100000003fffc00

def z159 : W := mkw 0x0010009400480500 0x0008004a00240280 0x1070001c00f80000 0x0838000e007c0000

def z160 : W := mkw 0x09b1dbfc785a2d0a 0x04d8edfe3c2d1685 0xfff1fffc7cfe3f1f 0xfff8fffe3e7f1f8f

def z161 : W := mkw 0x0010029c285a2d0a 0x0008014e142d1685 0x2600019c7cfe3f1f 0x930000ce3e7f1f8f

def z162 : W := mkw 0x6002000487ed47f4 0x3001000243f6a3fa 0x2200000007ffc7ff 0x9100000003ffe3ff

def z163 : W := mkw 0x2e0576297005d83c 0x1702bb14b802ec1e 0x0a01fe007807f81f 0x8500ff003c03fc0f

def z164 : W := mkw 0x0006240001809000 0x0003120000c04800 0xba8e7e0003c1f800 0x5d473f0001e0fc00

def z165 : W := mkw 0xb9effc2057b7f034 0x5cf7fe102bdbf81a 0xfbfffe007ffff81f 0xfdffff003ffffc0f

def z166 : W := mkw 0x2f87776df7c5defc 0x17c3bbb6fbe2ef7e 0xff8fffffffc7ffff 0xffc7ffffffe3ffff

def z167 : W := mkw 0x0002000481c00440 0x0001000240e00220 0x2000000003c004e0 0x1000000001e00270

def z168 : W := mkw 0x0000102040004030 0x0000081020002018 0xae8070606301c4f9 0x574038303180e27c

def z169 : W := mkw 0xd1ffefdeafffbfca 0x68fff7ef57ffdfe5 0xffffffffffffffff 0xffffffffffffffff

def z170 : W := mkw 0x7dffffffffed47f4 0xbefffffffff6a3fa 0xffffffffffffc7ff 0xffffffffffffe3ff

def z171 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0x2a007e0063c1fcf9 0x15003f0031e0fe7c

def z172 : W := mkw 0xddffffffffffb7c0 0xeeffffffffffdbe0 0xffffffffffffffe0 0x7ffffffffffffff0

def z173 : W := mkw 0x299153fc7e4d4fbe 0x14c8a9fe3f26a7df 0xef81f1fc7f07c7ff 0xf7c0f8fe3f83e3ff

def z174 : W := mkw 0x91edec0006372000 0x48f6f600031b9000 0xd9fffe00043e0000 0x6cffff00021f0000

def z175 : W := mkw 0x0c1013fb78000000 0x860809fdbc000000 0x040001fff8000000 0x020000fffc000000

def z176 : W := mkw 0xb9efed4017b7b284 0x5cf7f6a00bdbd942 0xfbffff801ffffb06 0xfdffffc00ffffd83

def z177 : W := mkw 0x91cf640007a59000 0x48e7b20003d2c800 0x008e70000301c000 0x004738000180e000

def z178 : W := mkw 0x2202000487c5defc 0x1101000243e2ef7e 0x2200000007c7ffff 0x9100000003e3ffff

def z179 : W := mkw 0x0981516050000000 0x04c0a8b028000000 0xcd81f1e078000000 0x66c0f8f03c000000

def z180 : W := mkw 0x01c8000006200000 0x00e4000003100000 0x4170000004380000 0x20b80000021c0000

def z181 : W := mkw 0x4002000487e807c0 0x2001000243f403e0 0xb48e007f87f807e0 0x5a47003fc3fc03f0

def z182 : W := mkw 0x41de25d687e897c0 0x20ef12eb43f44be0 0xfffe7fff87f9ffe0 0x7fff3fffc3fcfff0

def z183 : W := mkw 0x11e9c80000000000 0x08f4e40000000000 0x4171800000000000 0x20b8c00000000000

def z184 : W := mkw 0x91ebc80007b72000 0x48f5e40003db9000 0xf1ff800007fe0000 0x78ffc00003ff0000

def z185 : W := mkw 0x5dffffffffe807c0 0xaefffffffff403e0 0xfdfffffffff807e0 0x7efffffffffc03f0

def z186 : W := mkw 0x20000000060542b4 0x100000000302a15a 0x220000000707c7ff 0x910000000383e3ff

def z187 : W := mkw 0x3dfdfffb78054034 0x9efefffdbc02a01a 0xdffffffff807c01f 0xeffffffffc03e00f

def z188 : W := mkw 0x91effc2047b7f030 0x48f7fe1023dbf818 0xfffffe6067fffcf9 0x7fffff3033fffe7c

def z189 : W := mkw 0x9dfdfffb7e372000 0xcefefffdbf1b9000 0xddfffffffc3e0000 0x6efffffffe1f0000

def z190 : W := mkw 0x0000000400400c08 0x0000000200200604 0x2200000000c03c19 0x1100000000601e0c

def z191 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0x4181f1e01f07c3e6 0xa0c0f8f00f83e1f3

def z192 : W := mkw 0x0020880000000000 0x0010440000000000 0xd9718e0000000000 0x6cb8c70000000000

def z193 : W := mkw 0x0600020da0400c48 0x03000106d0200624 0x0000001f80000000 0x0000000fc0000000

def z194 : W := mkw 0x405a009681e80540 0x202d004b40f402a0 0xb4fe007f83f804e0 0x5a7f003fc1fc0270

def z195 : W := mkw 0x1dfdefdb38000000 0x8efef7ed9c000000 0x517f8f9f98000000 0x28bfc7cfcc000000

def z196 : W := mkw 0x19f9c9d218000000 0x8cfce4e90c000000 0xd5ff81ff98000000 0x6affc0ffcc000000

def z197 : W := mkw 0x00208a082812280a 0x0010450414091405 0xef018f807c063f1f 0xf780c7c03e031f8f

def z198 : W := mkw 0x1dcd776b70000000 0x8ee6bbb5b8000000 0x9c8e7e7fe0000000 0x4e473f3ff0000000

def z199 : W := mkw 0x3fffffffffc5defc 0x9fffffffffe2ef7e 0xffffffffffc7ffff 0xffffffffffe3ffff

def z200 : W := mkw 0x1c7dfebb78000000 0x8e3eff5dbc000000 0x187ffe1ff8000000 0x0c3fff0ffc000000

def z201 : W := mkw 0x0600122de0404c78 0x03000916f020263c 0xae80707fe301c4f9 0x5740383ff180e27c

def z202 : W := mkw 0x0434beb968000000 0x021a5f5cb4000000 0xddfffffff8000000 0x6efffffffc000000

def z203 : W := mkw 0x0004240000000000 0x0002120000000000 0x988e7e0000000000 0x4c473f0000000000

def z204 : W := mkw 0x0002000081800040 0x0001000040c00020 0x008e0063830000e0 0x00470031c1800070

def z205 : W := mkw 0x40000142800002c0 0x200000a140000160 0x00000063800000e0 0x00000031c0000070

def z206 : W := mkw 0x465e36bfe1e8dd78 0x232f1b5ff0f46ebc 0xbefe7e7fe3f9fcf9 0x5f7f3f3ff1fcfe7c

def z207 : W := mkw 0x1c25fe297812280a 0x8e12ff14bc091405 0x0a01fe007806381f 0x8500ff003c031c0f

def z208 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0xeb81f0600707c0e0 0x75c0f8300383e070

def z209 : W := mkw 0xb1efec0007b7f2b4 0x58f7f60003dbf95a 0xfbfffe0007ffffff 0xfdffff0003ffffff

def z210 : W := mkw 0x43da01d687e8dff8 0x21ed00eb43f46ffc 0xf7fe01ff87f9fff9 0x7bff00ffc3fcfffc

def z211 : W := mkw 0x01cb400007a50000 0x00e5a00003d28000 0xfbfff00007ffc000 0x7dfff80003ffe000

def z212 : W := mkw 0x9dfffffb79b2b000 0xcefffffdbcd95800 0xddfffffff8f83800 0x6efffffffc7c1c00

def z213 : W := mkw 0x0404260920000000 0x0202130490000000 0x100e0e1f80000000 0x0807070fc0000000

def z214 : W := mkw 0x147cbebb68000000 0x8a3e5f5db4000000 0x9cfe7e7fe0000000 0x4e7f3f3ff0000000

def z215 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0x0a81f0607b07c0ff 0x8540f8303d83e07f

def z216 : W := mkw 0x9deffd6357b7b000 0xcef7feb1abdbd800 0xfbfffe6387fff800 0x7dffff31c3fffc00

def z217 : W := mkw 0x01ea880007b22000 0x00f5440003d91000 0xfbff8e0007fe3800 0x7dffc70003ff1c00

def z218 : W := mkw 0x0634bebd685afd3a 0x031a5f5eb42d7e9d 0xff71ff9c7cffff1f 0xffb8ffce3e7fff8f

def z219 : W := mkw 0x06063421c180d070 0x03031a10e0c06838 0x008e70638301c0e0 0x00473831c180e070

def z220 : W := mkw 0x0002000481c00440 0x0001000240e00220 0x100e001f80c00000 0x0807000fc0600000

def z221 : W := mkw 0x06001021c0004070 0x03000810e0002038 0x00000063800000e0 0x00000031c0000070

def z222 : W := mkw 0x0004240000009000 0x0002120000004800 0x0a007e000001f800 0x05003f000000fc00

def z223 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xffff81fffffe07ff 0xffffc0ffffff03ff

def z224 : W := mkw 0x004a000001a00000 0x0025000000d00000 0x107e000000f80000 0x083f0000007c0000

def z225 : W := mkw 0x699151f6d64d47f4 0x34c8a8fb6b26a3fa 0xef81f1ffff07c7ff 0xf7c0f8ffff83e3ff

def z226 : W := mkw 0xd1efec0487ffb7c0 0x68f7f60243ffdbe0 0xfbfffe0007ffffe0 0x7dffff0003fffff0

def z227 : W := mkw 0x0981414010000000 0x04c0a0a008000000 0x4101818018000000 0x2080c0c00c000000

def z228 : W := mkw 0xb9e9c94016372284 0x5cf4e4a00b1b9142 0x417181801c3e0306 0xa0b8c0c00e1f0183

def z229 : W := mkw 0x060436296000d838 0x03021b14b0006c1c 0x0a007e006001f819 0x05003f003000fc0c

def z230 : W := mkw 0x0801502050000000 0x0400a81028000000 0x0801f00078000000 0x0400f8003c000000

def z231 : W := mkw 0x0202000481c0dc78 0x0101000240e06e3c 0xb68e007f83c1fcf9 0x5b47003fc1e0fe7c

def z232 : W := mkw 0x3dcd7563560542b4 0x9ee6bab1ab02a15a 0x008e70638301c0e0 0x00473831c180e070

def z233 : W := mkw 0x29d951f2560542b4 0x14eca8f92b02a15a 0xfffff1ffff07c7ff 0xfffff8ffff83e3ff

def z234 : W := mkw 0x11edec0000000000 0x08f6f60000000000 0xd9fffe0000000000 0x6cffff0000000000

def z235 : W := mkw 0x91edec000637b000 0x48f6f600031bd800 0x4b71fe00043ff800 0x25b8ff00021ffc00

def z236 : W := mkw 0x97efee0da7f7bc48 0x4bf7f706d3fbde24 0xfbfffe1f87fff800 0x7dffff0fc3fffc00

def z237 : W := mkw 0x00308a9c28480500 0x0018454e14240280 0xfd718f9c7cf80700 0x7eb8c7ce3e7c0380

def z238 : W := mkw 0x40328a9caffa2fca 0x2019454e57fd17e5 0xff718f9c7ffe3fff 0xffb8c7ce3fff1fff

def z239 : W := mkw 0x29b1c9d01e1f2386 0x14d8e4e80f0f91c3 0x417181801c3e0306 0xa0b8c0c00e1f0183

def z240 : W := mkw 0x0058009200000000 0x002c004900000000 0x107e001f80000000 0x083f000fc0000000

def z241 : W := mkw 0x0000000000000000 0x0000000000000000 0xef0181807c06071f 0xf780c0c03e03038f

def z242 : W := mkw 0x41da009687e80540 0x20ed004b43f402a0 0xf1fe001f87f80000 0x78ff000fc3fc0000

def z243 : W := mkw 0x0c1013ff78480d0a 0x860809ffbc240685 0x040001fff800071f 0x820000fffc00038f

def z244 : W := mkw 0x15fcafdb28000000 0x8afe57ed94000000 0xd5fe0fff80000000 0x6aff07ffc0000000

def z245 : W := mkw 0x06063629e180d878 0x03031b14f0c06c3c 0x0a8e7e63e301f8f9 0x05473f31f180fc7c

def z246 : W := mkw 0x39f9d9f25e0542b4 0x9cfcecf92f02a15a 0xeff1f1e07f07c7ff 0xf7f8f8f03f83e3ff

def z247 : W := mkw 0x906eac0001b2b000 0x4837560000d95800 0xbafe7e0003f9f800 0x5d7f3f0001fcfc00

def z248 : W := mkw 0x39f9c9d21e050284 0x9cfce4e90f028142 0x417181801c060306 0xa0b8c0c00e030183

def z249 : W := mkw 0x02021024c1c0dc78 0x0101081260e06e3c 0xae80706063c1fcf9 0x5740383031e0fe7c

def z250 : W := mkw 0x407a8a9ea9fa2d4a 0x203d454f54fd16a5 0x107e0e1f80f83800 0x083f070fc07c1c00

def z251 : W := mkw 0x0000102040004030 0x0000081020002018 0xef81f1e07f07c7ff 0xf7c0f8f03f83e3ff

def z252 : W := mkw 0x2000000000054034 0x100000000002a01a 0x020000000007c01f 0x810000000003e00f

def z253 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0x108e7e7f83c1f8e0 0x08473f3fc1e0fc70

def z254 : W := mkw 0x0406362de1c00440 0x02031b16f0e00220 0xbc8e7e7fe3c004e0 0x5e473f3ff1e00270

def z255 : W := mkw 0x1dfdfffb7e050000 0x8efefffdbf028000 0xffffffffff07c000 0x7fffffffff83e000

def z256 : W := mkw 0x0800116050000000 0x040008b028000000 0x040001e078000000 0x020000f03c000000

def z257 : W := mkw 0xf9fffdf6d7fff7f4 0x7cfffefb6bfffbfa 0xffffffffffffffff 0xffffffffffffffff

def z258 : W := mkw 0x0c309bfb78000000 0x86184dfdbc000000 0xdd718ffff8000000 0x6eb8c7fffc000000

def z259 : W := mkw 0x0180014000000000 0x00c000a000000000 0xc58001e000000000 0x62c000f000000000

def z260 : W := mkw 0x91efee0c27f7bc08 0x48f7f70613fbde04 0xfffffe1c67fffc19 0x7fffff0e33fffe0c

def z261 : W := mkw 0x0012009481c80540 0x0009004a40e402a0 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z262 : W := mkw 0x2981414016050284 0x14c0a0a00b028142 0xef0181807c06071f 0xf780c0c03e03038f

def z263 : W := mkw 0x800000000017b000 0x40000000000bd800 0x020000000007f800 0x010000000003fc00

def z264 : W := mkw 0x0787762de7c5dc78 0x03c3bb16f3e2ee3c 0xff8ffe7fe7c7fcf9 0x7fc7ff3ff3e3fe7c

def z265 : W := mkw 0x20000004065f6fbe 0x10000002032fb7df 0x2200000007ffffff 0x9100000003ffffff

def z266 : W := mkw 0x1dedfd6350000000 0x8ef6feb1a8000000 0xd9fffe6380000000 0x6cffff31c0000000

def z267 : W := mkw 0x19f9d9f258000000 0x8cfcecf92c000000 0xcdf1f1e078000000 0x66f8f8f03c000000

def z268 : W := mkw 0x0010029c28480d0a 0x0008014e14240685 0xef01819c7c06071f 0xf780c0ce3e03038f

def z269 : W := mkw 0x5dfffffbffa002c0 0xaefffffdffd00160 0xddfffffffb0000e0 0x6efffffffd800070

def z270 : W := mkw 0x2801502050054034 0x1400a8102802a01a 0xef01f1807c07c71f 0xf780f8c03e03e38f

def z271 : W := mkw 0x0181414006050280 0x00c0a0a003028140 0xef81f1e00707c7e0 0x77c0f8f00383e3f0

def z272 : W := mkw 0x00308a98281a2102 0x0018454c140d1081 0xdd718f9c7c3e0306 0xeeb8c7ce3e1f0183

def z273 : W := mkw 0x4058009200280100 0x202c004900140080 0x0070000000380000 0x00380000001c0000

def z274 : W := mkw 0x1ffffffbf980d070 0x8ffffffdfcc06838 0xddfffffffb01c0e0 0x6efffffffd80e070

def z275 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0x228070600707c7ff 0x914038300383e3ff

def z276 : W := mkw 0x06309abde85a6d7a 0x03184d5ef42d36bd 0xff718ffffcfe3fff 0xffb8c7fffe7f1fff

def z277 : W := mkw 0x1c35febd785a2d0a 0x8e1aff5ebc2d1685 0xff71ff9c7cfe3f1f 0xffb8ffce3e7f1f8f

def z278 : W := mkw 0xd1f9c9d2063f2380 0x68fce4e9031f91c0 0x41718180043e0300 0x20b8c0c0021f0180

def z279 : W := mkw 0x97cf762de7e5dc78 0x4be7bb16f3f2ee3c 0xbe8e7e7fe3c1fcf9 0x5f473f3ff1e0fe7c

def z280 : W := mkw 0x29b1cbdc3e5f2f8e 0x14d8e5ee1f2f97c7 0xff718f9c7cfe3f1f 0xffb8c7ce3e7f1f8f

def z281 : W := mkw 0x2981516050054034 0x14c0a8b02802a01a 0xcf81f1e07807c01f 0xe7c0f8f03c03e00f

def z282 : W := mkw 0x0c1437fb78000000 0x860a1bfdbc000000 0x9c8e7ffff8000000 0x4e473ffffc000000

def z283 : W := mkw 0x4002000087a002c0 0x2001000043d00160 0x00000000030000e0 0x0000000001800070

def z284 : W := mkw 0x9068880000322000 0x4834440000191000 0x0070000000380000 0x00380000001c0000

def z285 : W := mkw 0xb9cf756057a5d2b4 0x5ce7bab02bd2e95a 0x008e70600301c0e0 0x004738300180e070

def z286 : W := mkw 0x0001400000050000 0x0000a00000028000 0x0a01f0000007c000 0x0500f8000003e000

def z287 : W := mkw 0x55feafdfafe807c0 0xaaff57efd7f403e0 0xf5fe0fff87f807e0 0x7aff07ffc3fc03f0

def z288 : W := mkw 0x060434214000d030 0x03021a10a0006818 0x000070000001c000 0x000038000000e000

def z289 : W := mkw 0x91f9ca9c2e7f2d0a 0x48fce54e173f9685 0xff718f9c7cfe3f1f 0xffb8c7ce3e7f1f8f

def z290 : W := mkw 0x1dfdfffb7812280a 0x8efefffdbc091405 0xdffffffff806381f 0xeffffffffc031c0f

def z291 : W := mkw 0x298775605785d2b4 0x14c3bab02bc2e95a 0xff8fffe07fc7ffff 0xffc7fff03fe3ffff

def z292 : W := mkw 0x0000102040004030 0x0000081020002018 0x0a0070006001c019 0x050038003000e00c

def z293 : W := mkw 0x9ffffffffff7fc78 0xcffffffffffbfe3c 0xfffffffffffffcf9 0x7ffffffffffffe7c

def z294 : W := mkw 0x2e00136df0404efc 0x170009b6f820277e 0x040001fff80007ff 0x820000fffc0003ff

def z295 : W := mkw 0x2801400010050004 0x1400a00008028002 0x0001800018060006 0x8000c0000c030003

def z296 : W := mkw 0x9024ac000012b000 0x4812560000095800 0x00000e0000003800 0x0000070000001c00

def z297 : W := mkw 0x09d951f250000000 0x04eca8f928000000 0xddfff1fff8000000 0x6efff8fffc000000

def z298 : W := mkw 0x2f81536df6454efc 0x17c0a9b6fb22a77e 0xef81f1ffff07c7ff 0xf7c0f8ffff83e3ff

def z299 : W := mkw 0x00308894005a2500 0x0018444a002d1280 0xff718f9c04fe3f00 0x7fb8c7ce027f1f80

def z300 : W := mkw 0x0010029828000000 0x0008014c14000000 0x0400019c78000000 0x020000ce3c000000

def z301 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xfffffffffc06071f 0xfffffffffe03038f

def z302 : W := mkw 0x9625fe296017f838 0x4b12ff14b00bfc1c 0x0a01fe006007f819 0x0500ff003003fc0c

def z303 : W := mkw 0x1821c80018000000 0x8c10e4000c000000 0x0001800018000000 0x0000c0000c000000

def z304 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0xffffff807fffff1f 0xffffffc03fffff8f

def z305 : W := mkw 0x69fbdbfeffff6ffe 0x34fdedff7fffb7ff 0xffffffffffffffff 0xffffffffffffffff

def z306 : W := mkw 0x167ebebfe9c0dc78 0x8b3f5f5ff4e06e3c 0xbefe7e7fe3c1fcf9 0x5f7f3f3ff1e0fe7c

def z307 : W := mkw 0x09b1dbf878000000 0x04d8edfc3c000000 0xddf1fffc78000000 0x6ef8fffe3c000000

def z308 : W := mkw 0x00308890081a2102 0x00184448040d1081 0xef7181807c3e071f 0xf7b8c0c03e1f038f

def z309 : W := mkw 0x0786376de7c0def8 0x03c31bb6f3e06f7c 0xff8e7fffe7c1fff9 0x7fc73ffff3e0fffc

def z310 : W := mkw 0x47de35f7c7e8d7f0 0x23ef1afbe3f46bf8 0xf5fe71ff87f9c7e0 0x7aff38ffc3fce3f0

def z311 : W := mkw 0x00308a9828000000 0x0018454c14000000 0xff718f9c7c06071f 0xffb8c7ce3e03038f

def z312 : W := mkw 0x906eac0001b2b000 0x4837560000d95800 0xfb7f8e0004fe3800 0x7dbfc700027f1c00

def z313 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0xfb718e1c04fe3800 0x7db8c70e027f1c00

def z314 : W := mkw 0x0981516050000000 0x04c0a8b028000000 0xef81f1e07c06071f 0xf7c0f8f03e03038f

def z315 : W := mkw 0x41da03deafe80fca 0x20ed01ef57f407e5 0xf5fe01fffff807ff 0xfaff00fffffc03ff

def z316 : W := mkw 0x11edec0000122000 0x08f6f60000091000 0xfbfffe0004fe3800 0x7dffff00027f1c00

def z317 : W := mkw 0x00308890081a2102 0x00184448040d1081 0xfb718f801cfe3b06 0xfdb8c7c00e7f1d83

def z318 : W := mkw 0x1c05742150000000 0x8e02ba10a8000000 0x0000700000000000 0x0000380000000000

def z319 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0x10fe007f83f800e0 0x087f003fc1fc0070

def z320 : W := mkw 0x41fa8bdeaffa2fca 0x20fd45ef57fd17e5 0xf5fe0fff87f83fe0 0x7aff07ffc3fc1ff0

def z321 : W := mkw 0x41fa89d687fa27c0 0x20fd44eb43fd13e0 0xffff8fff87fe3fe0 0x7fffc7ffc3ff1ff0

def z322 : W := mkw 0x5dfffffffffa2fca 0xaefffffffffd17e5 0xfffffffffffe3fff 0xffffffffffff1fff

def z323 : W := mkw 0x47ce376fe7e0def8 0x23e71bb7f3f06f7c 0xbe8e7e7fe3c1fcf9 0x5f473f3ff1e0fe7c

def z324 : W := mkw 0x91efec0001b2b000 0x48f7f60000d95800 0xd9fffe0000f83800 0x6cffff00007c1c00

def z325 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0xf5700f9c04f83f00 0x7ab807ce027c1f80

def z326 : W := mkw 0x405a01d681e807c0 0x202d00eb40f403e0 0x147e01ff80f807e0 0x0a3f00ffc07c03f0

def z327 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0xbe700e1c60f83c19 0x5f38070e307c1e0c

def z328 : W := mkw 0x461637ffe1c8dff8 0x230b1bfff0e46ffc 0xbe8e7fffe3c1fff9 0x5f473ffff1e0fffc

def z329 : W := mkw 0x20000000060542b4 0x100000000302a15a 0xef0181807f07c7ff 0xf780c0c03f83e3ff

def z330 : W := mkw 0x3dcd7563560542b4 0x9ee6bab1ab02a15a 0xef8ff1e3ff07c7ff 0xf7c7f8f1ff83e3ff

def z331 : W := mkw 0x00000004005a2d0a 0x00000002002d1685 0x0000000000f83800 0x00000000007c1c00

def z332 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0xdd718f9c78f83800 0x6eb8c7ce3c7c1c00

def z333 : W := mkw 0x91ffee9c2fffbd0a 0x48fff74e17ffde85 0xfbfffe1c07fff800 0x7dffff0e03fffc00

def z334 : W := mkw 0x93efec0487f7fc78 0x49f7f60243fbfe3c 0xfbfffe0007fffcf9 0x7dffff0003fffe7c

def z335 : W := mkw 0x1dfdffff78400c08 0x8efeffffbc200604 0xfffffffff8c03c19 0x7ffffffffc601e0c

def z336 : W := mkw 0x0600122960004838 0x03000914b000241c 0x0000000060000019 0x000000003000000c

def z337 : W := mkw 0x0036ae9c29dabd0a 0x001b574e14ed5e85 0xffffff9c7fffff1f 0xffffffce3fffff8f

def z338 : W := mkw 0x40308bdea85a2fca 0x201845ef542d17e5 0xff718ffffcfe3fff 0xffb8c7fffe7f1fff

def z339 : W := mkw 0x147cae9f285a2d0a 0x8a3e574f942d1685 0x107e0e1f80f83800 0x083f070fc07c1c00

def z340 : W := mkw 0x419001d6864807c0 0x20c800eb432403e0 0xe58001ff870007e0 0x72c000ffc38003f0

def z341 : W := mkw 0x8000000006372000 0x40000000031b9000 0x00000000043e0000 0x00000000021f0000

def z342 : W := mkw 0x02328a9ca9dafd7a 0x0119454e54ed7ebd 0xff718f9c7fffffff 0xffb8c7ce3fffffff

def z343 : W := mkw 0x0604260920009808 0x0302130490004c04 0x00000e0000003800 0x0000070000001c00

def z344 : W := mkw 0x060436296000d838 0x03021b14b0006c1c 0xae807e606301fcf9 0x57403f303180fe7c

def z345 : W := mkw 0x0180014006000280 0x00c000a003000140 0xef8181e07f0607ff 0xf7c0c0f03f8303ff

def z346 : W := mkw 0x97effe2967b7f838 0x4bf7ff14b3dbfc1c 0xfbfffe0067fff819 0x7dffff0033fffc0c

def z347 : W := mkw 0x29cb516057a542b4 0x14e5a8b02bd2a15a 0xfffff1e07fffc7ff 0xfffff8f03fffe3ff

def z348 : W := mkw 0x407a8a9ea9fa2d4a 0x203d454f54fd16a5 0xff7f8f9ffcfe3f1f 0xffbfc7cffe7f1f8f

def z349 : W := mkw 0x0020880000122000 0x0010440000091000 0xff718f807cfe3f1f 0xffb8c7c03e7f1f8f

def z350 : W := mkw 0x19edfd6050000000 0x0cf6feb028000000 0xddffffe078000000 0x6efffff03c000000

def z351 : W := mkw 0x0181400006050000 0x00c0a00003028000 0x4101800004060000 0x2080c00002030000

def z352 : W := mkw 0x5dfdfffb7e280380 0xaefefffdbf1401c0 0xddfffffffc380300 0x6efffffffe1c0180

def z353 : W := mkw 0x0202000481dafd7a 0x0101000240ed7ebd 0x2200000007ffffff 0x9100000003ffffff

def z354 : W := mkw 0x41d801d6866807c0 0x20ec00eb433403e0 0x457001ff843807e0 0x22b800ffc21c03f0

def z355 : W := mkw 0x0e1637fff9c0dc78 0x870b1bfffce06e3c 0xbe8e7ffffbc1fcf9 0x5f473ffffde0fe7c

def z356 : W := mkw 0x0181502046054030 0x00c0a8102302a018 0xef81f0606707c4f9 0x77c0f8303383e27c

def z357 : W := mkw 0x0000102040000000 0x0000081020000000 0x8c80706060000000 0x4640383030000000

def z358 : W := mkw 0x41ca014687e006c0 0x20e500a343f00360 0xb48e007f83c004e0 0x5a47003fc1e00270

def z359 : W := mkw 0x41ca014687e807c0 0x20e500a343f403e0 0x208e006387f807e0 0x10470031c3fc03f0

def z360 : W := mkw 0x3dfdffff7e5f6fbe 0x9efeffffbf2fb7df 0xffffffffffffffff 0xffffffffffffffff

def z361 : W := mkw 0x1dfdffff785a2d0a 0x8efeffffbc2d1685 0xddfffffff8f83800 0x6efffffffc7c1c00

def z362 : W := mkw 0x00000004005a2d0a 0x00000002002d1685 0xef0181807cfe3f1f 0xf780c0c03e7f1f8f

def z363 : W := mkw 0x1df9dbfb78000000 0x8efcedfdbc000000 0x457181fff8000000 0x22b8c0fffc000000

def z364 : W := mkw 0x0606362de1c09c48 0x03031b16f0e04e24 0x9c8e7e7fe0c03800 0x4e473f3ff0601c00

def z365 : W := mkw 0xbfefff6df7f7fefc 0x5ff7ffb6fbfbff7e 0xffffffffffffffff 0xffffffffffffffff

def z366 : W := mkw 0x0000020c20400c08 0x0000010610200604 0xff018f9c7cc63f1f 0xff80c7ce3e631f8f

def z367 : W := mkw 0x0000102040004030 0x0000081020002018 0x008070600301c0e0 0x004038300180e070

def z368 : W := mkw 0x00308a9c28400c08 0x0018454e14200604 0xff718f9c78c03c19 0x7fb8c7ce3c601e0c

def z369 : W := mkw 0x061636bde9c8dd7a 0x030b1b5ef4e46ebd 0xbe8e7ffffbc1ffff 0xdf473ffffde0ffff

def z370 : W := mkw 0x0002000001800000 0x0001000000c00000 0xb08e000003c00000 0x5847000001e00000

def z371 : W := mkw 0x01d801d200000000 0x00ec00e900000000 0x4170018000000000 0x20b800c000000000

def z372 : W := mkw 0x8606362de7f7fc78 0x43031b16f3fbfe3c 0xbe8e7e7fe7fffcf9 0x5f473f3ff3fffe7c

def z373 : W := mkw 0x2981414016050284 0x14c0a0a00b028142 0x0000000000000000 0x0000000000000000

def z374 : W := mkw 0x8022880007b7b000 0x4011440003dbd800 0xfb718e0007fff800 0x7db8c70003fffc00

def z375 : W := mkw 0x91ffec900fbfb102 0x48fff64807dfd881 0xfbffff801ffffb06 0xfdffffc00ffffd83

def z376 : W := mkw 0x0e1013fff8404c78 0x870809fffc20263c 0x040001fff80004f9 0x020000fffc00027c

def z377 : W := mkw 0x01ca000487e00440 0x00e5000243f00220 0xf5fe007f87f804e0 0x7aff003fc3fc0270

def z378 : W := mkw 0x0010029c28480d0a 0x0008014e14240685 0xbe000f9c78c03f1f 0xdf0007ce3c601f8f

def z379 : W := mkw 0x0180014006000280 0x00c000a003000140 0x00800060030000e0 0x0040003001800070

def z380 : W := mkw 0x401003dea8480fca 0x200801ef542407e5 0x040001fff80007ff 0x820000fffc0003ff

def z381 : W := mkw 0x8002000001b2b000 0x4001000000d95800 0x0000000000f83800 0x00000000007c1c00

def z382 : W := mkw 0x0000000000122000 0x0000000000091000 0x2200000004fe3800 0x11000000027f1c00

def z383 : W := mkw 0x2801502050054034 0x1400a8102802a01a 0xae81f0607b07c4ff 0xd740f8303d83e27f

def z384 : W := mkw 0x2801502050054034 0x1400a8102802a01a 0x000070000001c000 0x000038000000e000

def z385 : W := mkw 0x00208a0c28522c0a 0x0010450614291605 0xbe018e1c78c63c1f 0xdf00c70e3c631e0f

def z386 : W := mkw 0x0006240481c09440 0x0003120240e04a20 0xbe8e7e7f83c1fce0 0x5f473f3fc1e0fe70

def z387 : W := mkw 0x0626be2de9d2fc7a 0x03135f16f4e97e3d 0xbe8ffe7ffbc7fcff 0xdf47ff3ffde3fe7f

def z388 : W := mkw 0x0002000001809000 0x0001000000c04800 0x2200000003c1f800 0x1100000001e0fc00

def z389 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0x0a8ffe000307f800 0x0547ff000183fc00

def z390 : W := mkw 0x8202000487f7fc78 0x4101000243fbfe3c 0x2200000007fffcf9 0x1100000003fffe7c

def z391 : W := mkw 0x1dfdfdf358000000 0x8efefef9ac000000 0x41fff1e398000000 0x20fff8f1cc000000

def z392 : W := mkw 0x00308894085a2502 0x0018444a042d1281 0xf571819c1cfe0706 0xfab8c0ce0e7f0383

def z393 : W := mkw 0x0026ac000192b000 0x0013560000c95800 0xfbfffe0007fff800 0x7dffff0003fffc00

def z394 : W := mkw 0x2831dabc785f6d3e 0x1418ed5e3c2fb69f 0xff71ff9c7cffff1f 0xffb8ffce3e7fff8f

def z395 : W := mkw 0x2b835164d7c5defc 0x15c1a8b26be2ef7e 0xef81f1e07fc7ffff 0xf7c0f8f03fe3ffff

def z396 : W := mkw 0x0010029c20480d08 0x0008014e10240684 0xff700f9c64f83f19 0x7fb807ce327c1f8c

def z397 : W := mkw 0x0000000480400440 0x0000000240200220 0x0400007f800004e0 0x0200003fc0000270

def z398 : W := mkw 0x21800140060542b4 0x10c000a00302a15a 0xe78001e00707c7ff 0xf3c000f00383e3ff

def z399 : W := mkw 0x1dfffffb7fa00000 0x8efffffdbfd00000 0xfdfffffffff80000 0x7efffffffffc0000

def z400 : W := mkw 0x29815160500042b4 0x14c0a8b02800215a 0xcd81f1e0780007ff 0xe6c0f8f03c0003ff

def z401 : W := mkw 0x405a009687e807c0 0x202d004b43f403e0 0x307e001f87f807e0 0x183f000fc3fc03f0

def z402 : W := mkw 0x1c35feb978000000 0x8e1aff5cbc000000 0xdd71ff9c78000000 0x6eb8ffce3c000000

def z403 : W := mkw 0x00208a0c20522c08 0x0010450610291604 0xff718e1c64fe3c19 0x7fb8c70e327f1e0c

def z404 : W := mkw 0x9027ec0007b7b000 0x4813f60003dbd800 0x2a01fe0007fff800 0x1500ff0003fffc00

def z405 : W := mkw 0x401201d687e807c0 0x200900eb43f403e0 0x240001ff87f807e0 0x120000ffc3fc03f0

def z406 : W := mkw 0x00308a982812280a 0x0018454c14091405 0xdf718f9c7806381f 0xefb8c7ce3c031c0f

def z407 : W := mkw 0x69db51f6d7ed47f4 0x34eda8fb6bf6a3fa 0xf5fe71ff87f9c7e0 0x7aff38ffc3fce3f0

def z408 : W := mkw 0x81ca000007b7b000 0x40e5000003dbd800 0xf3fe000007fff800 0x79ff000003fffc00

def z409 : W := mkw 0x3c25fe2978054034 0x9e12ff14bc02a01a 0x0a01fe007807c01f 0x8500ff003c03e00f

def z410 : W := mkw 0x000634204180d030 0x00031a1020c06818 0xbe8e7e6063c1fcf9 0x5f473f3031e0fe7c

def z411 : W := mkw 0x9035ee9c285fbd0a 0x481af74e142fde85 0xff71ff9c7cffff1f 0xffb8ffce3e7fff8f

def z412 : W := mkw 0x0000020c205a2d0a 0x00000106102d1685 0xbe000e1c64fe3f1f 0xdf00070e327f1f8f

def z413 : W := mkw 0x91cf640007a59000 0x48e7b20003d2c800 0xeb8ff0000707c000 0x75c7f8000383e000

def z414 : W := mkw 0x167eae9fa9c09c48 0x8b3f574fd4e04e24 0x107e0e1f80c03800 0x083f070fc0601c00

def z415 : W := mkw 0x1c25fe2978000000 0x8e12ff14bc000000 0x9c8ffe7ff8000000 0x4e47ff3ffc000000

def z416 : W := mkw 0x0006260c21c09c08 0x0003130610e04e04 0xbe8e7e1c63c1fc19 0x5f473f0e31e0fe0c

def z417 : W := mkw 0x5fffffffffe8dff8 0xaffffffffff46ffc 0xfffffffffff9fff9 0x7ffffffffffcfffc

def z418 : W := mkw 0x405a009681e80540 0x202d004b40f402a0 0xf57e019f84f80700 0x7abf00cfc27c0380

def z419 : W := mkw 0x47ce3563c7a0d2f0 0x23e71ab1e3d06978 0x008e70638301c0e0 0x00473831c180e070

def z420 : W := mkw 0x0010009000000000 0x0008004800000000 0xd570019c00000000 0x6ab800ce00000000

def z421 : W := mkw 0x00208a0c285a2d0a 0x00104506142d1685 0x2a018e007cfe3f1f 0x9500c7003e7f1f8f

def z422 : W := mkw 0x547eae9fa9e80540 0xaa3f574fd4f402a0 0x107e0e1f80f80000 0x083f070fc07c0000

def z423 : W := mkw 0x39edfd60560542b4 0x1cf6feb02b02a15a 0xffffffe07f07c7ff 0xfffffff03f83e3ff

def z424 : W := mkw 0x00208a082812280a 0x0010450414091405 0xfb718e007cfe381f 0xfdb8c7003e7f1c0f

def z425 : W := mkw 0xd7ffffffe7fffff8 0x6bfffffff3fffffc 0xffffffffe7fffff9 0x7ffffffff3fffffc

def z426 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0x450181e07c0607ff 0xa280c0f03e0303ff

def z427 : W := mkw 0x2e06376df1c0defc 0x17031bb6f8e06f7e 0xbe8e7ffffbc1ffff 0xdf473ffffde0ffff

def z428 : W := mkw 0x966ebe2de1f2fc78 0x4b375f16f0f97e3c 0xbefe7e7fe3f9fcf9 0x5f7f3f3ff1fcfe7c

def z429 : W := mkw 0x1dfdfffb781a2102 0x8efefffdbc0d1081 0xddfffffffc3e0306 0xeefffffffe1f0183

def z430 : W := mkw 0x5ddf75f7d7e807c0 0xaeefbafbebf403e0 0xf5fe71ff87f807e0 0x7aff38ffc3fc03f0

def z431 : W := mkw 0x41fa8bdeafe807c0 0x20fd45ef57f403e0 0xfdff8ffffff807e0 0x7effc7fffffc03f0

def z432 : W := mkw 0x11cd640000000000 0x08e6b20000000000 0x008e700000000000 0x0047380000000000

def z433 : W := mkw 0x147cae9b28000000 0x8a3e574d94000000 0xdd7f8f9ff8000000 0x6ebfc7cffc000000

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x948e007f80000000 0x4a47003fc0000000

def z435 : W := mkw 0x01ca014007a00280 0x00e500a003d00140 0xf5fe01e007f807e0 0x7aff00f003fc03f0

def z436 : W := mkw 0x947eae9b29b2b000 0xca3f574d94d95800 0x107e0e1f80f83800 0x083f070fc07c1c00

def z437 : W := mkw 0x41c8014206200280 0x20e400a103100140 0x0000000000000000 0x0000000000000000

def z438 : W := mkw 0x0200000480404c78 0x010000024020263c 0x00000000000004f9 0x000000000000027c

def z439 : W := mkw 0x4606362de7e8dff8 0x23031b16f3f46ffc 0xbe8e7e7fe7f9fff9 0x5f473f3ff3fcfffc

def z440 : W := mkw 0x3dfdfffb7e050284 0x9efefffdbf028142 0xddfffffffc060306 0xeefffffffe030183

def z441 : W := mkw 0x147cae9f285a2d0a 0x8a3e574f942d1685 0xff7f8f9ffcfe3f1f 0xffbfc7cffe7f1f8f

def z442 : W := mkw 0x1fcf776ff1c0dc78 0x8fe7bbb7f8e06e3c 0xbe8e7e7fe3c1fcf9 0x5f473f3ff1e0fe7c

def z443 : W := mkw 0xb9cf756057a5d2b4 0x5ce7bab02bd2e95a 0xef8ff1e07f07c7ff 0xf7c7f8f03f83e3ff

def z444 : W := mkw 0x144c240300000000 0x8a26120180000000 0x000e000380000000 0x00070001c0000000

def z445 : W := mkw 0x20000000060542b4 0x100000000302a15a 0x000000000301c0e0 0x000000000180e070

def z446 : W := mkw 0x2800102050004034 0x140008102800201a 0x000000007800001f 0x800000003c00000f

def z447 : W := mkw 0x0000020820000000 0x0000010410000000 0x9c000e1c60000000 0x4e00070e30000000

def z448 : W := mkw 0x41ca000487e807c0 0x20e5000243f403e0 0xf1fe000007f807e0 0x78ff000003fc03f0

def z449 : W := mkw 0x4002000487fa2fca 0x2001000243fd17e5 0x2200000007fe3fff 0x9100000003ff1fff

def z450 : W := mkw 0x6fdf77fff7eddffc 0x37efbbfffbf6effe 0xffffffffffffffff 0xffffffffffffffff

def z451 : W := mkw 0x2981414016050284 0x14c0a0a00b028142 0xe58181e01f0607e6 0xf2c0c0f00f8303f3

def z452 : W := mkw 0x01d801d600480500 0x00ec00eb00240280 0xf5fe01ff84f80700 0x7aff00ffc27c0380

def z453 : W := mkw 0x17effe2de1c0dc78 0x0bf7ff16f0e06e3c 0xfffffe7fe3c1fcf9 0x7fffff3ff1e0fe7c

def z454 : W := mkw 0x1da5ff6978000000 0x8ed2ffb4bc000000 0xcd81ffe078000000 0x66c0fff03c000000

def z455 : W := mkw 0x20308a9c2e5f6fbe 0x1018454e172fb7df 0xff718f9c7fffffff 0xffb8c7ce3fffffff

def z456 : W := mkw 0x0000000006050000 0x0000000003028000 0x220000000707c000 0x110000000383e000

def z457 : W := mkw 0x41da01d207a80380 0x20ed00e903d401c0 0xf1fe018007f80300 0x78ff00c003fc0180

def z458 : W := mkw 0x95ffee9b2fb7b000 0xcafff74d97dbd800 0xfbfffe1f87fff800 0x7dffff0fc3fffc00

def z459 : W := mkw 0xd1feadd687fab7c0 0x68ff56eb43fd5be0 0xf5fe0fff87f83fe0 0x7aff07ffc3fc1ff0

def z460 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0x41fff000073fc000 0x20fff800039fe000

def z461 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0xae8070606301c4f9 0x574038303180e27c

def z462 : W := mkw 0x47de27dfa7e89fc8 0x23ef13efd3f44fe4 0xf5fe0fff87f83fe0 0x7aff07ffc3fc1ff0

def z463 : W := mkw 0x9027ec000197b000 0x4813f60000cbd800 0xba8ffe0003c7f800 0x5d47ff0001e3fc00

def z464 : W := mkw 0x0181400000000000 0x00c0a00000000000 0xc981f00000000000 0x64c0f80000000000

def z465 : W := mkw 0x20000000000042b4 0x100000000000215a 0x00000000000007ff 0x80000000000003ff

def z466 : W := mkw 0xb9fffffc7fffffbe 0x5cfffffe3fffffdf 0xfffffffc7fffffff 0xfffffffe3fffffff

def z467 : W := mkw 0x1ffdfffb7800d838 0x8ffefffdbc006c1c 0xdffffffff801f819 0x6ffffffffc00fc0c

def z468 : W := mkw 0x00100094005a2d0a 0x0008004a002d1685 0xf770019c04fe3f1f 0xfbb800ce027f1f8f

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0xeb01800004060000 0x7580c00002030000

def z470 : W := mkw 0x1dfdffff78480500 0x8efeffffbc240280 0xfdfffffffcf80700 0x7efffffffe7c0380

def z471 : W := mkw 0x0010009400480500 0x0008004a00240280 0xff71819c7cfe071f 0xffb8c0ce3e7f038f

def z472 : W := mkw 0x06063425c1c0d470 0x03031a12e0e06a38 0xb48e707f83c1c4e0 0x5a47383fc1e0e270

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0xe500018004000700 0x728000c002000380

def z474 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0xcd81f1e07b01c0e0 0x66c0f8f03d80e070

def z475 : W := mkw 0x01f88bde285a2d0a 0x00fc45ef142d1685 0xffff8ffffcfe3f1f 0xffffc7fffe7f1f8f

def z476 : W := mkw 0x0000000000000000 0x0000000000000000 0xae00000060000419 0x570000003000020c

def z477 : W := mkw 0x59f9c9d21e280380 0xacfce4e90f1401c0 0x417181801c380300 0x20b8c0c00e1c0180

def z478 : W := mkw 0x29a1d960561762b4 0x14d0ecb02b0bb15a 0xfff1ffe07fffffff 0xfff8fff03fffffff

def z479 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0x140e0e7fe0c03cf9 0x0a07073ff0601e7c

def z480 : W := mkw 0x91c9400006250000 0x48e4a00003128000 0x0000000000000000 0x0000000000000000

def z481 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0x4971ff8078000000 0x24b8ffc03c000000

def z482 : W := mkw 0x8183400007b7b000 0x40c1a00003dbd800 0xeb81f00007fff800 0x75c0f80003fffc00

def z483 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0x0e018f9c78063f1f 0x8700c7ce3c031f8f

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0xcd01818078000000 0x6680c0c03c000000

def z485 : W := mkw 0x11fdee9c285a2d0a 0x08fef74e142d1685 0xffffff9c7cfe3f1f 0xffffffce3e7f1f8f

def z486 : W := mkw 0x0000000000000000 0x0000000000000000 0xba000e0000c03800 0x5d00070000601c00

def z487 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0xff8fffffffc7ffff 0xffc7ffffffe3ffff

def z488 : W := mkw 0x4012009487e807c0 0x2009004a43f403e0 0xf570019c07f807e0 0x7ab800ce03fc03f0

def z489 : W := mkw 0x0000000000004030 0x0000000000002018 0x220000000301c4f9 0x110000000180e27c

def z490 : W := mkw 0x0010029c28480d0a 0x0008014e14240685 0xf570019c7cf8071f 0xfab800ce3e7c038f

def z491 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0x1a0e7e1fe0c1f819 0x0d073f0ff060fc0c

def z492 : W := mkw 0x41fa89d68ffa27c2 0x20fd44eb47fd13e1 0xf5ff81ff9ffe07e6 0xfaffc0ffcfff03f3

def z493 : W := mkw 0x1dfdfffb7e000280 0x8efefffdbf000140 0xfdffffffff0007e0 0x7effffffff8003f0

def z494 : W := mkw 0x401001d6804807c0 0x200800eb402403e0 0xf57001ff84f807e0 0x7ab800ffc27c03f0

def z495 : W := mkw 0x29801160560042b4 0x14c008b02b00215a 0xe58001e07f0007ff 0xf2c000f03f8003ff

def z496 : W := mkw 0x41da11f6c7e847f0 0x20ed08fb63f423f8 0xfffe71ffe7f9c7f9 0x7fff38fff3fce3fc

def z497 : W := mkw 0x9dfdfffb7817b000 0xcefefffdbc0bd800 0xdffffffff807f800 0x6ffffffffc03fc00

def z498 : W := mkw 0x69d941d2162d0384 0x34eca0e90b1681c2 0x417181801c3e0306 0xa0b8c0c00e1f0183

def z499 : W := mkw 0x11edec0006050000 0x08f6f60003028000 0xfbfffe000707c000 0x7dffff000383e000

def z500 : W := mkw 0x0006240001809000 0x0003120000c04800 0x100e0e0000c03800 0x0807070000601c00

def z501 : W := mkw 0x907eae9c29fabd0a 0x483f574e14fd5e85 0xff7f8f9c7cfe3f1f 0xffbfc7ce3e7f1f8f

def z502 : W := mkw 0x0624be296812f83a 0x03125f14b4097c1d 0x0a01fe007807f81f 0x8500ff003c03fc0f

def z503 : W := mkw 0x0002020ca1c00c48 0x0001010650e00624 0xbe8e0e7fe3c03cf9 0x5f47073ff1e01e7c

def z504 : W := mkw 0x69cb5162d7a542f4 0x34e5a8b16bd2a17a 0xef8ff1e3ff07c7ff 0xf7c7f8f1ff83e3ff

def z505 : W := mkw 0x1ddd77fb78000000 0x8eeebbfdbc000000 0x048e71fff8000000 0x024738fffc000000

def z506 : W := mkw 0x907eae9c29fabd0a 0x483f574e14fd5e85 0x107e0e1c00f83800 0x083f070e007c1c00

def z507 : W := mkw 0xd07eac9681fab540 0x683f564b40fd5aa0 0x107e0e1f80f83800 0x083f070fc07c1c00

def z508 : W := mkw 0x00308a98281a290a 0x0018454c140d1485 0x4b718f807c3e3b1f 0xa5b8c7c03e1f1d8f

def z509 : W := mkw 0x0604362de0404c78 0x03021b16f020263c 0x9c8e7e7fe00004f9 0x4e473f3ff000027c

def z510 : W := mkw 0x69cb5162d7a542f4 0x34e5a8b16bd2a17a 0x008e70638301c0e0 0x00473831c180e070

def z511 : W := mkw 0x0602122de1c04c78 0x03010916f0e0263c 0xb48e007fe3c004f9 0x5a47003ff1e0027c

def z512 : W := mkw 0x15edfe2960000000 0x0af6ff14b0000000 0xddfffe7fe0000000 0x6effff3ff0000000

def z513 : W := mkw 0x1025ec0000000000 0x0812f60000000000 0x0801fe0000000000 0x0400ff0000000000

def z514 : W := mkw 0x0404362d60400c08 0x02021b16b0200604 0xbe8e7e7fe0c03c19 0x5f473f3ff0601e0c

def z515 : W := mkw 0x9025ee082817b80a 0x4812f704140bdc05 0x0a01fe007807f81f 0x8500ff003c03fc0f

def z516 : W := mkw 0x0434bebd685a2d0a 0x021a5f5eb42d1685 0xfffffffffcfe3f1f 0xfffffffffe7f1f8f

def z517 : W := mkw 0x97cf7421c7a5d070 0x4be7ba10e3d2e838 0x008e70638301c0e0 0x00473831c180e070

def z518 : W := mkw 0x0981516056000280 0x04c0a8b02b000140 0xed81f1e07f0007e0 0x76c0f8f03f8003f0

def z519 : W := mkw 0x01b1ca9c2e5f2d0a 0x00d8e54e172f9685 0xfff1ff9c7fffff1f 0xfff8ffce3fffff8f

def z520 : W := mkw 0x0606260da1c09c48 0x03031306d0e04e24 0xb48e0e7f83c03ce0 0x5a47073fc1e01e70

def z521 : W := mkw 0x91ffec9407ffb500 0x48fff64a03ffda80 0xffffff9c07ffff00 0x7fffffce03ffff80

def z522 : W := mkw 0x0600122de0404c78 0x03000916f020263c 0xbe000e7fe0c03cf9 0x5f00073ff0601e7c

def z523 : W := mkw 0x91cf640007b7b000 0x48e7b20003dbd800 0x228e700007fff800 0x1147380003fffc00

def z524 : W := mkw 0x91f9c8900e3f2102 0x48fce448071f9081 0x417181801c3e0306 0xa0b8c0c00e1f0183

def z525 : W := mkw 0x91efed4007b7b280 0x48f7f6a003dbd940 0xffffffe007ffffe0 0x7ffffff003fffff0

def z526 : W := mkw 0x0000000400480d0a 0x0000000200240685 0x000000000000071f 0x800000000000038f

def z527 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0xe58071e00701c7e0 0x72c038f00380e3f0

def z528 : W := mkw 0x29814140160542b4 0x14c0a0a00b02a15a 0x630181801f07c7ff 0xb180c0c00f83e3ff

def z529 : W := mkw 0x5dcf7563d7a002c0 0xaee7bab1ebd00160 0x008e7063830000e0 0x00473831c1800070

def z530 : W := mkw 0x01c8014200000000 0x00e400a100000000 0x008e006380000000 0x00470031c0000000

def z531 : W := mkw 0x681011f6d04847f4 0x340808fb682423fa 0x040001fff80007ff 0x820000fffc0003ff

def z532 : W := mkw 0x1ffffffff9c09c48 0x8ffffffffce04e24 0xddfffffff8c03800 0x6efffffffc601c00

def z533 : W := mkw 0x91eeac0007b2b000 0x48f7560003d95800 0xf1fe0e0007f83800 0x78ff070003fc1c00

def z534 : W := mkw 0x0606260da1c09c48 0x03031306d0e04e24 0xba8e7e1f83c1f800 0x5d473f0fc1e0fc00

def z535 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0x048071e07b01c7ff 0x824038f03d80e3ff

def z536 : W := mkw 0x41da01d681e80540 0x20ed00eb40f402a0 0xd5fe01ff80f80000 0x6aff00ffc07c0000

def z537 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0x517f8e0004fe3800 0x28bfc700027f1c00

def z538 : W := mkw 0x4010009680480540 0x2008004b402402a0 0x0000001f80000000 0x0000000fc0000000

def z539 : W := mkw 0x07ce362de7e0dc78 0x03e71b16f3f06e3c 0xfffe7e7fe7f9fcf9 0x7fff3f3ff3fcfe7c

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0xa4800060030004e0 0x5240003001800270

def z541 : W := mkw 0x0636bebde9dafd7a 0x031b5f5ef4ed7ebd 0xbefe7e7fe3f9fcf9 0x5f7f3f3ff1fcfe7c

def z542 : W := mkw 0x0606240181809040 0x03031200c0c04820 0x000e000380000000 0x00070001c0000000

def z543 : W := mkw 0x06063421c180d070 0x03031a10e0c06838 0xae8e7063e301c4f9 0x57473831f180e27c

def z544 : W := mkw 0x2f877561d785d2f4 0x17c3bab0ebc2e97a 0x008e70638301c0e0 0x00473831c180e070

def z545 : W := mkw 0xd1df65d687ed97c0 0x68efb2eb43f6cbe0 0xf5fe71ff87f9c7e0 0x7aff38ffc3fce3f0

def z546 : W := mkw 0x06063421c180d070 0x03031a10e0c06838 0xba8e7e6383c1f8e0 0x5d473f31c1e0fc70

def z547 : W := mkw 0x49db51f6d7e807c0 0x24eda8fb6bf403e0 0xfdfff1fffff807e0 0x7efff8fffffc03f0

def z548 : W := mkw 0x0000000400400400 0x0000000200200200 0xb400001c00c00400 0x5a00000e00600200

def z549 : W := mkw 0x0636bebde9c0dc78 0x031b5f5ef4e06e3c 0xfffffffffbc1fcf9 0x7ffffffffde0fe7c

def z550 : W := mkw 0x9dcf756357a59000 0xcee7bab1abd2c800 0x008e70638301c000 0x00473831c180e000

def z551 : W := mkw 0x5dfdfffff84807c0 0xaefefffffc2403e0 0xddfffffff80007e0 0x6efffffffc0003f0

def z552 : W := mkw 0x0406362961809000 0x02031b14b0c04800 0xbe8e7e7fe3c1f800 0x5f473f3ff1e0fc00

def z553 : W := mkw 0x020200008180d070 0x0101000040c06838 0x000000000301c0e0 0x000000000180e070

def z554 : W := mkw 0x0606362de1dafd7a 0x03031b16f0ed7ebd 0xbe8e7e7fe7ffffff 0xdf473f3ff3ffffff

def z555 : W := mkw 0x0f87776df1c0dc78 0x07c3bbb6f8e06e3c 0xff8ffffffbc1fcf9 0x7fc7fffffde0fe7c

def z556 : W := mkw 0x0c00122978000000 0x86000914bc000000 0x0000000078000000 0x000000003c000000

def z557 : W := mkw 0x80328a9c2fffbd0a 0x4019454e17ffde85 0xff718f9c7fffff1f 0xffb8c7ce3fffff8f

def z558 : W := mkw 0x1ffdfffff8404c78 0x8ffefffffc20263c 0xddfffffff80004f9 0x6efffffffc00027c

def z559 : W := mkw 0x91ffee982fb7b000 0x48fff74c17dbd800 0xffffff9c7ffff800 0x7fffffce3ffffc00

def z560 : W := mkw 0x2981502056054034 0x14c0a8102b02a01a 0xeb81f0007f07c01f 0xf5c0f8003f83e00f

def z561 : W := mkw 0x01da009407e80500 0x00ed004a03f40280 0xf5fe019c07f80700 0x7aff00ce03fc0380

def z562 : W := mkw 0x906fec0001b7b000 0x4837f60000dbd800 0x1a7ffe0000fff800 0x0d3fff00007ffc00

def z563 : W := mkw 0x0604362d6040dc38 0x03021b16b0206e1c 0xbe007e1c60c1fc19 0x5f003f0e3060fe0c

def z564 : W := mkw 0x2800014010000284 0x140000a008000142 0x0000018018000306 0x800000c00c000183

def z565 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0x4571819c7c3e071f 0xa2b8c0ce3e1f038f

def z566 : W := mkw 0x0000000006000280 0x0000000003000140 0x20000000070007e0 0x10000000038003f0

def z567 : W := mkw 0x41ca014287a002c0 0x20e500a143d00160 0xf1fe006387f800e0 0x78ff0031c3fc0070

def z568 : W := mkw 0x28015160500542b4 0x1400a8b02802a15a 0x0e01f1e07807c7ff 0x8700f8f03c03e3ff

def z569 : W := mkw 0x1e25fe297800d838 0x8f12ff14bc006c1c 0x0a01fe007801f819 0x0500ff003c00fc0c

def z570 : W := mkw 0x2f87776df7c5defc 0x17c3bbb6fbe2ef7e 0xbe8e7e7fe3c1fcf9 0x5f473f3ff1e0fe7c

def z571 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0x51718f9c1cfe3b06 0xa8b8c7ce0e7f1d83

def z572 : W := mkw 0x91ffedd207b7b000 0x48fff6e903dbd800 0xffffffff87fff800 0x7fffffffc3fffc00

def z573 : W := mkw 0x5dfffffff9e80540 0xaefffffffcf402a0 0xddfffffff8f80000 0x6efffffffc7c0000

def z574 : W := mkw 0x11fdee9828000000 0x08fef74c14000000 0xddffff9c78000000 0x6effffce3c000000

def z575 : W := mkw 0x0000014000000280 0x000000a000000140 0x040001e0000007e0 0x020000f0000003f0

def z576 : W := mkw 0x00208a082812280a 0x0010450414091405 0x00000e0000003800 0x0000070000001c00

def z577 : W := mkw 0x2606362de7c5defc 0x13031b16f3e2ef7e 0xbe8e7e7fe7c7ffff 0xdf473f3ff3e3ffff

def z578 : W := mkw 0xa983516057b7f2b4 0x54c1a8b02bdbf95a 0xef81f1e07fffffff 0xf7c0f8f03fffffff

def z579 : W := mkw 0x00208a0828000000 0x0010450414000000 0x08018e0078000000 0x0400c7003c000000

def z580 : W := mkw 0x41ca014287a002c0 0x20e500a143d00160 0xe58e01e3870007e0 0x72c700f1c38003f0

def z581 : W := mkw 0x1dfdffff78480d0a 0x8efeffffbc240685 0xddfffffff800071f 0xeefffffffc00038f

def z582 : W := mkw 0x9dffffff7fffbd0a 0xceffffffbfffde85 0xffffffffffffff1f 0xffffffffffffff8f

def z583 : W := mkw 0x0d9153fb78000000 0x86c8a9fdbc000000 0xcd81f1fff8000000 0x66c0f8fffc000000

def z584 : W := mkw 0x29835164d7c546f4 0x14c1a8b26be2a37a 0xff8ff1ffffc7c7ff 0xffc7f8ffffe3e3ff

def z585 : W := mkw 0x2981516056050284 0x14c0a8b02b028142 0xcd81f1e07c060306 0xe6c0f8f03e030183

def z586 : W := mkw 0x966eae0da1f2bc48 0x4b375706d0f95e24 0x107e0e1f80f83800 0x083f070fc07c1c00

def z587 : W := mkw 0x4c1013fff84807c0 0xa60809fffc2403e0 0x040001fff80007e0 0x020000fffc0003f0

def z588 : W := mkw 0xb9e9d960563762b4 0x5cf4ecb02b1bb15a 0xeff1f1e07f3fc7ff 0xf7f8f8f03f9fe3ff

def z589 : W := mkw 0x2d9153fb7e0542b4 0x96c8a9fdbf02a15a 0xef81f1ffff07c7ff 0xf7c0f8ffff83e3ff

def z590 : W := mkw 0x41d801d606680780 0x20ec00eb033403c0 0xf570019c04f80700 0x7ab800ce027c0380

def z591 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0x048e01ff830007e0 0x024700ffc18003f0

def z592 : W := mkw 0x00308894085a2d0a 0x0018444a042d1685 0x637181801cfe3f1f 0xb1b8c0c00e7f1f8f

def z593 : W := mkw 0x41d801d6804807c0 0x20ec00eb402403e0 0xd5fe01ff800007e0 0x6aff00ffc00003f0

def z594 : W := mkw 0x00308a9828122000 0x0018454c14091000 0xff718f9c7cfe3800 0x7fb8c7ce3e7f1c00

def z595 : W := mkw 0x29815164565f6fbe 0x14c0a8b22b2fb7df 0xef81f1e07fffffff 0xf7c0f8f03fffffff

def z596 : W := mkw 0x1078889208000000 0x883c444904000000 0x0070000000000000 0x0038000000000000

def z597 : W := mkw 0x41db41d687ed07c0 0x20eda0eb43f683e0 0xfffff1ff87ffc7e0 0x7ffff8ffc3ffe3f0

def z598 : W := mkw 0x19f9cbde385a2d0a 0x8cfce5ef1c2d1685 0xff718f9c7cfe3f1f 0xffb8c7ce3e7f1f8f

def z599 : W := mkw 0x28001160500042b4 0x140008b02800215a 0xef0181e07c0607ff 0xf780c0f03e0303ff

def z600 : W := mkw 0x06063629e180d070 0x03031b14f0c06838 0x9c8e7e7fe301c0e0 0x4e473f3ff180e070

def z601 : W := mkw 0x2f877561d785d2f4 0x17c3bab0ebc2e97a 0xef8ff1e3ff07c7ff 0xf7c7f8f1ff83e3ff

def z602 : W := mkw 0x0606260da1c0dc78 0x03031306d0e06e3c 0x320e0e1f83c1fcf9 0x1907070fc1e0fe7c

def z603 : W := mkw 0x1dfffffff9c00440 0x8efffffffce00220 0xfdfffffffbc004e0 0x7efffffffde00270

def z604 : W := mkw 0x0010009400480500 0x0008004a00240280 0x0400019c00000700 0x020000ce00000380

def z605 : W := mkw 0x1dcd756350000000 0x8ee6bab1a8000000 0xcd8ff1e3f8000000 0x66c7f8f1fc000000

def z606 : W := mkw 0x0410029b28000000 0x8208014d94000000 0x0000001f80000000 0x0000000fc0000000

def z607 : W := mkw 0x97fffebdeffffd7a 0x4bffff5ef7fffebd 0xffffffffffffffff 0xffffffffffffffff

def z608 : W := mkw 0xb9effd6057b7f2b4 0x5cf7feb02bdbf95a 0xfbfffe6007fff8e0 0x7dffff3003fffc70

def z609 : W := mkw 0x11efec0007a00000 0x08f7f60003d00000 0xf9fffe0007f80000 0x7cffff0003fc0000

def z610 : W := mkw 0x1dedfe2978000000 0x8ef6ff14bc000000 0xd9fffe0078000000 0x6cffff003c000000

def z611 : W := mkw 0x41d801d206280380 0x20ec00e9031401c0 0xd5fe01ff84380300 0x6aff00ffc21c0180

def z612 : W := mkw 0x2f8577697605dabc 0x17c2bbb4bb02ed5e 0xef81ffe07f07ffff 0xf7c0fff03f83ffff

def z613 : W := mkw 0x0010029c28480d0a 0x0008014e14240685 0x0000001c00000000 0x0000000e00000000

def z614 : W := mkw 0x28001160500042b4 0x140008b02800215a 0x00000060000000e0 0x0000003000000070

def z615 : W := mkw 0x91e9c80006372000 0x48f4e400031b9000 0xebf1f000073fc000 0x75f8f800039fe000

def z616 : W := mkw 0x0010009008080102 0x0008004804040081 0x0000018018000306 0x800000c00c000183

def z617 : W := mkw 0x01da01d207a00000 0x00ed00e903d00000 0xf5fe01ff87f80000 0x7aff00ffc3fc0000

def z618 : W := mkw 0x0000122c60404c38 0x000009163020261c 0xbe807e7c63c1fcf9 0x5f403f3e31e0fe7c

def z619 : W := mkw 0x0180014006000280 0x00c000a003000140 0x4100018004000300 0x208000c002000180

def z620 : W := mkw 0x28001160500042b4 0x140008b02800215a 0xae8071e07b01c7ff 0xd74038f03d80e3ff

def z621 : W := mkw 0x01801160460042b0 0x00c008b023002158 0xef8071e06701c7f9 0x77c038f03380e3fc

def z622 : W := mkw 0x465e269fa1e89d48 0x232f134fd0f44ea4 0x107e0e1f80f83800 0x083f070fc07c1c00

def z623 : W := mkw 0x0020880000122000 0x0010440000091000 0x0a018e0000063800 0x0500c70000031c00

def z624 : W := mkw 0x28309bfc785a6fbe 0x14184dfe3c2d37df 0xff718ffc7cfe3fff 0xffb8c7fe3e7f1fff

def z625 : W := mkw 0x51ffedd687e807c0 0x28fff6eb43f403e0 0xfdffffff87f807e0 0x7effffffc3fc03f0

def z626 : W := mkw 0x91a5ec000617b000 0x48d2f600030bd800 0xeb81fe000707f800 0x75c0ff000383fc00

def z627 : W := mkw 0x19c9414210000000 0x8ce4a0a108000000 0x0000000000000000 0x0000000000000000

def z628 : W := mkw 0x2000000006050284 0x1000000003028142 0x0000000004060306 0x8000000002030183

def z629 : W := mkw 0xc1da01d687ffb7c0 0x60ed00eb43ffdbe0 0xf7fe01ff87ffffe0 0x7bff00ffc3fffff0

def z630 : W := mkw 0x1c35fffb78000000 0x8e1afffdbc000000 0x0c01fffff8000000 0x0600fffffc000000

def z631 : W := mkw 0x00308a9828000000 0x0018454c14000000 0x10700e1c00000000 0x0838070e00000000

def z632 : W := mkw 0x2fb7fffdffdffffe 0x17dbfffeffefffff 0xffffffffffffffff 0xffffffffffffffff

def z633 : W := mkw 0x29a1db687e176abe 0x14d0edb43f0bb55f 0xef81ffe07f07ffff 0xf7c0fff03f83ffff

def z634 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0x32700e1c04fe3f1f 0x9938070e027f1f8f

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0xf170000004f80000 0x78b80000027c0000

def z636 : W := mkw 0x0002000007a00000 0x0001000003d00000 0x2000000007f80000 0x1000000003fc0000

def z637 : W := mkw 0x0981516056050000 0x04c0a8b02b028000 0xef81f1e07f07c000 0x77c0f8f03f83e000

def z638 : W := mkw 0x21814000060542b4 0x10c0a0000302a15a 0xeb81f0000707c7ff 0xf5c0f8000383e3ff

def z639 : W := mkw 0x28001160560542b4 0x140008b02b02a15a 0x260001e07f07c7ff 0x930000f03f83e3ff

def z640 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0x1a718e1c78fe381f 0x8d38c70e3c7f1c0f

def z641 : W := mkw 0x0404362960000000 0x02021b14b0000000 0x08007e0060000000 0x04003f0030000000

def z642 : W := mkw 0x00308a9c28480d0a 0x0018454e14240685 0xdd718f9c7800071f 0xeeb8c7ce3c00038f

def z643 : W := mkw 0x00309abc685a6d3a 0x00184d5e342d369d 0xfff1fffc7fffffff 0xfff8fffe3fffffff

def z644 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0x14700f9c78f83f1f 0x8a3807ce3c7c1f8f

def z645 : W := mkw 0x01fa8a9c2ffa2d0a 0x00fd454e17fd1685 0xffff8f9c7ffe3f1f 0xffffc7ce3fff1f8f

def z646 : W := mkw 0x081001d218000000 0x840800e90c000000 0x0000018018000000 0x000000c00c000000

def z647 : W := mkw 0xd1fbc9d687ff27c0 0x68fde4eb43ff93e0 0xf5ff81ff87fe07e0 0x7affc0ffc3ff03f0

def z648 : W := mkw 0x00308890081a2102 0x00184448040d1081 0x0070000000380000 0x00380000001c0000

def z649 : W := mkw 0x9005640000059000 0x4802b2000002c800 0x000070000001c000 0x000038000000e000

def z650 : W := mkw 0x0181400006050000 0x00c0a00003028000 0xef81f1807f07c71f 0xf7c0f8c03f83e38f

def z651 : W := mkw 0x9deffe297fb7b000 0xcef7ff14bfdbd800 0xfbfffe007ffff800 0x7dffff003ffffc00

def z652 : W := mkw 0x29b1dbf87e0542b4 0x14d8edfc3f02a15a 0xfff1fffc7f07c7ff 0xfff8fffe3f83e3ff

def z653 : W := mkw 0x01da01d681c00440 0x00ed00eb40e00220 0xf5fe01ff83c004e0 0x7aff00ffc1e00270

def z654 : W := mkw 0x2981536c76454ebc 0x14c0a9b63b22a75e 0xff81fffc7fc7ffff 0xffc0fffe3fe3ffff

def z655 : W := mkw 0x904e240001a09000 0x4827120000d04800 0x000e000000000000 0x0007000000000000

def z656 : W := mkw 0x9dfffffb7fa59000 0xcefffffdbfd2c800 0xddfffffffb01c000 0x6efffffffd80e000

def z657 : W := mkw 0x29b1d9f05e1f63b6 0x14d8ecf82f0fb1db 0xeff1f1e07f3fc7ff 0xf7f8f8f03f9fe3ff

def z658 : W := mkw 0x91efec0007a59000 0x48f7f60003d2c800 0xd9fffe000301c000 0x6cffff000180e000

def z659 : W := mkw 0x00021024c1c04470 0x0001081260e02238 0xbe8e707fe3c1c4f9 0x5f47383ff1e0e27c

def z660 : W := mkw 0x019001d406480780 0x00c800ea032403c0 0xf5f001fc07f807e0 0x7af800fe03fc03f0

def z661 : W := mkw 0x69d951f2562d43b4 0x34eca8f92b16a1da 0xeff1f1e07f3fc7ff 0xf7f8f8f03f9fe3ff

def z662 : W := mkw 0x9627fe2de1d7fc78 0x4b13ff16f0ebfe3c 0xbe8ffe7fe3c7fcf9 0x5f47ff3ff1e3fe7c

def z663 : W := mkw 0x106cac0000000000 0x0836560000000000 0x107e0e0000000000 0x083f070000000000

def z664 : W := mkw 0x0636ae9da9dabd4a 0x031b574ed4ed5ea5 0xff7f8f9ffcfe3f1f 0xffbfc7cffe7f1f8f

def z665 : W := mkw 0x41da03dea7e80fc8 0x20ed01ef53f407e4 0xfffe0fffe7f83ff9 0x7fff07fff3fc1ffc

def z666 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0x517e019f84f80300 0x28bf00cfc27c0180

def z667 : W := mkw 0x020000000000d838 0x0100000000006c1c 0x020000000001f819 0x010000000000fc0c

def z668 : W := mkw 0x9021c80000172000 0x4810e400000b9000 0x0001800000060000 0x0000c00000030000

def z669 : W := mkw 0x91efec0407ffbd0a 0x48f7f60203ffde85 0xfbfffe0007ffff1f 0xfdffff0003ffff8f

def z670 : W := mkw 0x061636bde1c8dd78 0x030b1b5ef0e46ebc 0xfffe7fffe7f9fff9 0x7fff3ffff3fcfffc

def z671 : W := mkw 0x0181400006050000 0x00c0a00003028000 0x008070000301c000 0x004038000180e000

def z672 : W := mkw 0x8006240007b7b000 0x4003120003dbd800 0xba8e7e0007fff800 0x5d473f0003fffc00

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x410181801c060306 0xa080c0c00e030183

def z674 : W := mkw 0x0030889008000000 0x0018444804000000 0x4171818018000000 0x20b8c0c00c000000

def z675 : W := mkw 0x0000102040004030 0x0000081020002018 0x04000060600004f9 0x020000303000027c

def z676 : W := mkw 0x47da13ffe7e84ff8 0x23ed09fff3f427fc 0xf5fe01ffe7f807f9 0x7aff00fff3fc03fc

def z677 : W := mkw 0x99effd6057b7b000 0x4cf7feb02bdbd800 0xffffffe07ffff800 0x7ffffff03ffffc00

def z678 : W := mkw 0x91e9c80006372000 0x48f4e400031b9000 0xfb718e0004fe3800 0x7db8c700027f1c00

def z679 : W := mkw 0x06063425c1c0dc78 0x03031a12e0e06e3c 0x228e706383c1fcf9 0x11473831c1e0fe7c

def z680 : W := mkw 0x41d801d206280380 0x20ec00e9031401c0 0xe5f001e0073807e0 0x72f800f0039c03f0

def z681 : W := mkw 0x0000020c20400c08 0x0000010610200604 0x0400001c60000419 0x0200000e3000020c

def z682 : W := mkw 0x0000000400480500 0x0000000200240280 0x2000000004f80700 0x10000000027c0380

def z683 : W := mkw 0x0626be2de1d2fc78 0x03135f16f0e97e3c 0xfffffe7fe7fffcf9 0x7fffff3ff3fffe7c

def z684 : W := mkw 0x9c25fe297817b000 0xce12ff14bc0bd800 0x0a01fe007807f800 0x0500ff003c03fc00

def z685 : W := mkw 0x060636296180d838 0x03031b14b0c06c1c 0xba8e7e0063c1f819 0x5d473f0031e0fc0c

def z686 : W := mkw 0x299151f4564d47b4 0x14c8a8fa2b26a3da 0xfff1f1fc7fffc7ff 0xfff8f8fe3fffe3ff

def z687 : W := mkw 0x20001020460542b4 0x100008102302a15a 0xae8070606707c7ff 0xd74038303383e3ff

def z688 : W := mkw 0x61da01d687ed47f4 0x30ed00eb43f6a3fa 0xf7fe01ff87ffc7ff 0xfbff00ffc3ffe3ff

def z689 : W := mkw 0x0206240481c0dc78 0x0103120240e06e3c 0xba8e7e0003c1fcf9 0x5d473f0001e0fe7c

def z690 : W := mkw 0x41f88bde2e7a2f8a 0x20fc45ef173d17c5 0xff718f9c7cfe3f1f 0xffb8c7ce3e7f1f8f

def z691 : W := mkw 0x0604362de040dc78 0x03021b16f0206e3c 0x0e007e7fe001fcf9 0x07003f3ff000fe7c

def z692 : W := mkw 0x19f9cbda38000000 0x8cfce5ed1c000000 0xdd718f9c78000000 0x6eb8c7ce3c000000

def z693 : W := mkw 0x0000020c20400c08 0x0000010610200604 0x10000e1c00c03800 0x0800070e00601c00

def z694 : W := mkw 0x0020880008122002 0x0010440004091001 0x0001800018060006 0x8000c0000c030003

def z695 : W := mkw 0xb9a5fd605617f2b4 0x5cd2feb02b0bf95a 0xef81ffe07f07ffff 0xf7c0fff03f83ffff

def z696 : W := mkw 0x69da11f6d7e847f4 0x34ed08fb6bf423fa 0xf5fe01fffff807ff 0xfaff00fffffc03ff

def z697 : W := mkw 0x0000020820000808 0x0000010410000404 0x0a000e0060003819 0x0500070030001c0c

def z698 : W := mkw 0x401201d681c807c0 0x200900eb40e403e0 0xb48e01ff83c007e0 0x5a4700ffc1e003f0

def z699 : W := mkw 0x11efec0001809000 0x08f7f60000c04800 0xfbfffe0003c1f800 0x7dffff0001e0fc00

def z700 : W := mkw 0x0187640007859000 0x00c3b20003c2c800 0xfb8ffe0007c7f800 0x7dc7ff0003e3fc00

def z701 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa8070000301c000 0x554038000180e000

def z702 : W := mkw 0x91efec0487f7b440 0x48f7f60243fbda20 0xfffffe7f87fffce0 0x7fffff3fc3fffe70

def z703 : W := mkw 0x0010009000080100 0x0008004800040080 0x4170018004380300 0x20b800c0021c0180

def z704 : W := mkw 0x1fcf7563d180d070 0x8fe7bab1e8c06838 0x008e70638301c0e0 0x00473831c180e070

def z705 : W := mkw 0x1e27fe2df9c0dc78 0x8f13ff16fce06e3c 0xbe8ffe7ffbc1fcf9 0x5f47ff3ffde0fe7c

def z706 : W := mkw 0x8002000007a59000 0x4001000003d2c800 0x000000000301c000 0x000000000180e000

def z707 : W := mkw 0x1dcd776b70000000 0x8ee6bbb5b8000000 0xdd8ffffff8000000 0x6ec7fffffc000000

def z708 : W := mkw 0x97e9da2de6776c78 0x4bf4ed16f33bb63c 0x4571807fe43e04f9 0x22b8c03ff21f027c

def z709 : W := mkw 0x1dfdefdb38000000 0x8efef7ed9c000000 0xdd7f8f9ff8000000 0x6ebfc7cffc000000

def z710 : W := mkw 0x02228a0ca9d2fc7a 0x0111450654e97e3d 0x2a018e007bc7fcff 0x9500c7003de3fe7f

def z711 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xfdfffffffc000700 0x7efffffffe000380

def z712 : W := mkw 0xd1efec0087b7b2c0 0x68f7f60043dbd960 0xfbfffe0007fff8e0 0x7dffff0003fffc70

def z713 : W := mkw 0x29b1dbfc7e5f6fbe 0x14d8edfe3f2fb7df 0x10f07e7c03f9f8e0 0x08783f3e01fcfc70

def z714 : W := mkw 0x0404342140000000 0x02021a10a0000000 0x948e707f80000000 0x4a47383fc0000000

def z715 : W := mkw 0x401201d687e807c0 0x200900eb43f403e0 0x2000018007f807e0 0x100000c003fc03f0

def z716 : W := mkw 0xb9efed4017b7b284 0x5cf7f6a00bdbd942 0xffffff807fffff1f 0xffffffc03fffff8f

def z717 : W := mkw 0x28015160500542b4 0x1400a8b02802a15a 0xae81f1e07b07c7ff 0xd740f8f03d83e3ff

def z718 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0xff8ff1ffff07c7ff 0xffc7f8ffff83e3ff

def z719 : W := mkw 0x9027ec000197b000 0x4813f60000cbd800 0xfbfffe0007fff800 0x7dffff0003fffc00

def z720 : W := mkw 0x40228a0caffa2fca 0x2011450657fd17e5 0x2a018e007ffe3fff 0x9500c7003fff1fff

def z721 : W := mkw 0x0000102040000000 0x0000081020000000 0x9c8e707fe0000000 0x4e47383ff0000000

def z722 : W := mkw 0x0624be296812f83a 0x03125f14b4097c1d 0x0a007e006001f819 0x05003f003000fc0c

def z723 : W := mkw 0x41da01d681e80540 0x20ed00eb40f402a0 0xf5fe01ff83f804e0 0x7aff00ffc1fc0270

def z724 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xfffffffff8c03800 0x7ffffffffc601c00

def z725 : W := mkw 0x91df669c2fed9d0a 0x48efb34e17f6ce85 0x048e719c7b01c71f 0x824738ce3d80e38f

def z726 : W := mkw 0x05d813fb60000000 0x02ec09fdb0000000 0xd5fe01ffe0000000 0x6aff00fff0000000

def z727 : W := mkw 0x147cae9b28000000 0x8a3e574d94000000 0xff7f8f9ffc06071f 0xffbfc7cffe03038f

def z728 : W := mkw 0x1dfdfffb7e000280 0x8efefffdbf000140 0xffffffffff0607ff 0xffffffffff8303ff

def z729 : W := mkw 0x3dfdfffb7e0542b4 0x9efefffdbf02a15a 0xffffffffff07c0e0 0x7fffffffff83e070

def z730 : W := mkw 0x347cae9b2e0542b4 0x9a3e574d9702a15a 0x327e0e1f8707c7ff 0x993f070fc383e3ff

def z731 : W := mkw 0xd9f9c9d21e3f2380 0xecfce4e90f1f91c0 0x417181801c3e0300 0x20b8c0c00e1f0180

def z732 : W := mkw 0x95efec0307b7b000 0xcaf7f60183dbd800 0xfbfffe0387fff800 0x7dffff01c3fffc00

def z733 : W := mkw 0x01d801d200000000 0x00ec00e900000000 0xddff81fff8000000 0x6effc0fffc000000

def z734 : W := mkw 0x1ddd75f350000000 0x8eeebaf9a8000000 0x10fe707f80000000 0x087f383fc0000000

def z735 : W := mkw 0xddfdfffb7e3f2380 0xeefefffdbf1f91c0 0xddfffffffc3e0300 0x6efffffffe1f0180

def z736 : W := mkw 0x69f9c9d21e3f2386 0x34fce4e90f1f91c3 0x417181801c3e0306 0xa0b8c0c00e1f0183

def z737 : W := mkw 0x0404362960004030 0x02021b14b0002018 0x9c8e7e7fe301c0e0 0x4e473f3ff180e070

def z738 : W := mkw 0xc002000487ff27c0 0x6001000243ff93e0 0x2000000007fe07e0 0x1000000003ff03f0

def z739 : W := mkw 0x97efec0187b7b040 0x4bf7f600c3dbd820 0xfbfffe0387fff800 0x7dffff01c3fffc00

def z740 : W := mkw 0x1dcd7567505a2d0a 0x8ee6bab3a82d1685 0x228e706384fe3f1f 0x91473831c27f1f8f

def z741 : W := mkw 0x15fcafdb28000000 0x8afe57ed94000000 0xddff8ffff8000000 0x6effc7fffc000000

def z742 : W := mkw 0x4002000481e807c0 0x2001000240f403e0 0x0000000000f807e0 0x00000000007c03f0

def z743 : W := mkw 0x0202000481c0dc78 0x0101000240e06e3c 0xaa80700003c1fcf9 0x5540380001e0fe7c

def z744 : W := mkw 0x145c249300000000 0x8a2e124980000000 0x107e001f80000000 0x083f000fc0000000

def z745 : W := mkw 0x0002000487e00440 0x0001000243f00220 0x2000000007f804e0 0x1000000003fc0270

def z746 : W := mkw 0x00208a082812280a 0x0010450414091405 0xff718f807cfe3f1f 0xffb8c7c03e7f1f8f

def z747 : W := mkw 0xbdcf756357a5d2b4 0xdee7bab1abd2e95a 0x008e70638301c0e0 0x00473831c180e070

def z748 : W := mkw 0x4183400487ed07c0 0x20c1a00243f683e0 0xeb81f00007ffc7e0 0x75c0f80003ffe3f0

def z749 : W := mkw 0x1dfdfffb78122000 0x8efefffdbc091000 0xddfffffff8f83800 0x6efffffffc7c1c00

def z750 : W := mkw 0x0d85776970000000 0x06c2bbb4b8000000 0x9c8e7e7fe0000000 0x4e473f3ff0000000

def z751 : W := mkw 0x6002000487ed07c4 0x3001000243f683e2 0x2000000007fe07e6 0x9000000003ff03f3

def z752 : W := mkw 0xb86ebd6051b2f2b4 0x5c375eb028d9795a 0x147e0fe078f83fff 0x8a3f07f03c7c1fff

def z753 : W := mkw 0x0606362de1c8dd78 0x03031b16f0e46ebc 0xbe8e7e7fe7f9fff9 0x5f473f3ff3fcfffc

def z754 : W := mkw 0x09d951f250000000 0x04eca8f928000000 0xd5fe71ff80000000 0x6aff38ffc0000000

def z755 : W := mkw 0x41fa89d68ffa2fca 0x20fd44eb47fd17e5 0x637181801ffe3fff 0xb1b8c0c00fff1fff

def z756 : W := mkw 0x4202000487e0def8 0x2101000243f06f7c 0x2200000003c1fcf9 0x1100000001e0fe7c

def z757 : W := mkw 0xbfcf7561d7a5d2f4 0x5fe7bab0ebd2e97a 0x008e70638301c0e0 0x00473831c180e070

def z758 : W := mkw 0xf9f9c9d2163f2384 0x7cfce4e90b1f91c2 0x417181801c3e0306 0xa0b8c0c00e1f0183

def z759 : W := mkw 0x1dfdfebb78000000 0x8efeff5dbc000000 0xd9fffe1ff8000000 0x6cffff0ffc000000

def z760 : W := mkw 0x01da009487e80540 0x00ed004a43f402a0 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z761 : W := mkw 0x1dfdfffb7e172000 0x8efefffdbf0b9000 0xfffffffffffff800 0x7ffffffffffffc00

def z762 : W := mkw 0x0624be296012f838 0x03125f14b0097c1c 0x0a01fe006007f819 0x0500ff003003fc0c

def z763 : W := mkw 0x01d801d206000280 0x00ec00e903000140 0xd5fe01ff830000e0 0x6aff00ffc1800070

def z764 : W := mkw 0x2c1013ff78484fbe 0x960809ffbc2427df 0x040001fff80007ff 0x820000fffc0003ff

def z765 : W := mkw 0x0181414006050280 0x00c0a0a003028140 0xef81f1e07f07c7ff 0xf7c0f8f03f83e3ff

def z766 : W := mkw 0x3ddd77fb7e0542b4 0x9eeebbfdbf02a15a 0x048e71fffb01c7ff 0x824738fffd80e3ff

def z767 : W := mkw 0x0c04376b70000000 0x86021bb5b8000000 0x9c8e7e7fe0000000 0x4e473f3ff0000000

def z768 : W := mkw 0xbdfdfffb7e3762b4 0xdefefffdbf1bb15a 0xffffffffff3fc7ff 0xffffffffff9fe3ff

def z769 : W := mkw 0x060436296000d838 0x03021b14b0006c1c 0xbe8e7e7fe301fcf9 0x5f473f3ff180fe7c

def z770 : W := mkw 0x1dfdfffb78122002 0x8efefffdbc091001 0xddfffffff8060006 0xeefffffffc030003

def z771 : W := mkw 0x69d951f2562d43b4 0x34eca8f92b16a1da 0xfffff1ffff3fc7ff 0xfffff8ffff9fe3ff

def z772 : W := mkw 0x0202000481c8dd78 0x0101000240e46ebc 0x2200000007f9fff9 0x1100000003fcfffc

def z773 : W := mkw 0x41d801d206280380 0x20ec00e9031401c0 0xf5fe01ff873807e0 0x7aff00ffc39c03f0

def z774 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0xfffffe0067fffc19 0x7fffff0033fffe0c

def z775 : W := mkw 0x1df9dbfb78000000 0x8efcedfdbc000000 0xd5ff81fff8000000 0x6affc0fffc000000

def z776 : W := mkw 0x3dfdfffb7e176abe 0x9efefffdbf0bb55f 0xffffffffff07ffff 0xffffffffff83ffff

def z777 : W := mkw 0x0004240000000000 0x0002120000000000 0x9c8e7e7f80000000 0x4e473f3fc0000000

def z778 : W := mkw 0x11edec0000000000 0x08f6f60000000000 0xddfffe7f80000000 0x6effff3fc0000000

def z779 : W := mkw 0x9027ec0007b7b000 0x4813f60003dbd800 0xfb71fe0007fff800 0x7db8ff0003fffc00

def z780 : W := mkw 0x0202000481c0dc78 0x0101000240e06e3c 0x2200000007c7ffff 0x9100000003e3ffff

def z781 : W := mkw 0x0c1437fb78000000 0x860a1bfdbc000000 0x140e0ffff8000000 0x0a0707fffc000000

def z782 : W := mkw 0x01d941d206050000 0x00eca0e903028000 0xfffff1ff8707c000 0x7ffff8ffc383e000

def z783 : W := mkw 0xbc25fe297817f034 0xde12ff14bc0bf81a 0x0a01fe007807f81f 0x8500ff003c03fc0f

def z784 : W := mkw 0x1dedff6970000000 0x0ef6ffb4b8000000 0xddfffffff8000000 0x6efffffffc000000

def z785 : W := mkw 0x29d811f2500042b4 0x14ec08f92800215a 0xd5fe01fff80007ff 0xeaff00fffc0003ff

def z786 : W := mkw 0x05cc362960000000 0x02e61b14b0000000 0xddfe7e7fe0000000 0x6eff3f3ff0000000

def z787 : W := mkw 0x403288948ffa27c2 0x2019444a47fd13e1 0x617181801ffe07e6 0xb0b8c0c00fff03f3

def z788 : W := mkw 0x0404362960000000 0x02021b14b0000000 0x140e0e7fe0000000 0x0a07073ff0000000

def z789 : W := mkw 0x1ddd75f350000000 0x8eeebaf9a8000000 0xddfff1fff8000000 0x6efff8fffc000000

def z790 : W := mkw 0x4002000481fa2d4a 0x2001000240fd16a5 0x0000000000f83800 0x00000000007c1c00

def z791 : W := mkw 0x69da01d697e807c4 0x34ed00eb4bf403e2 0xf5fe01ff9ff807e6 0xfaff00ffcffc03f3

def z792 : W := mkw 0x0202000481c09c48 0x0101000240e04e24 0x2200000000c03c19 0x1100000000601e0c

def z793 : W := mkw 0x91efec0001b2b000 0x48f7f60000d95800 0xfbfffe0003f9f800 0x7dffff0001fcfc00

def z794 : W := mkw 0x0024ac000012b000 0x0012560000095800 0xfb71fe0004fff800 0x7db8ff00027ffc00

def z795 : W := mkw 0x281012bc78484d3e 0x1408095e3c24269f 0x0400019c7800071f 0x820000ce3c00038f

def z796 : W := mkw 0x11fdefda28000000 0x08fef7ed14000000 0xddfffffff8000000 0x6efffffffc000000

def z797 : W := mkw 0x685b50b6d1ed4574 0x342da85b68f6a2ba 0x1a7ff01ff8ffc01f 0x8d3ff80ffc7fe00f

def z798 : W := mkw 0xd035edd6805fb7c0 0x681af6eb402fdbe0 0x0e01ffff8007ffe0 0x0700ffffc003fff0

def z799 : W := mkw 0x4002000487e807c0 0x2001000243f403e0 0xf170000007f807e0 0x78b8000003fc03f0

def z800 : W := mkw 0x1bfbc9d699c0dc78 0x8dfde4eb4ce06e3c 0x637181801bc1fcf9 0x31b8c0c00de0fe7c

def z801 : W := mkw 0x41da01d687e80fca 0x20ed00eb43f407e5 0xf5fe01ff87f807ff 0xfaff00ffc3fc03ff

def z802 : W := mkw 0x28209960501262b4 0x14104cb02809315a 0xff718fe07cfe3fff 0xffb8c7f03e7f1fff

def z803 : W := mkw 0x405a009681e80540 0x202d004b40f402a0 0x0070000000f80000 0x00380000007c0000

def z804 : W := mkw 0x0636bcb1c99af172 0x031b5e58e4cd78b9 0x41fff1e39f3fc3e6 0xa0fff8f1cf9fe1f3

def z805 : W := mkw 0x0406362de1c09440 0x02031b16f0e04a20 0xbe8e7e7fe3c1fce0 0x5f473f3ff1e0fe70

def z806 : W := mkw 0x91e9c80006372000 0x48f4e400031b9000 0xfbf1fe0007fff800 0x7df8ff0003fffc00

def z807 : W := mkw 0x91efec0087b7b040 0x48f7f60043dbd820 0xfbfffe6387fff8e0 0x7dffff31c3fffc70

def z808 : W := mkw 0x0382014487c0def8 0x01c100a243e06f7c 0xe78001e007c1fff9 0x73c000f003e0fffc

def z809 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xb4fe007f83f804e0 0x5a7f003fc1fc0270

def z810 : W := mkw 0x1ddd77fb78000000 0x8eeebbfdbc000000 0x008e707f80000000 0x0047383fc0000000

def z811 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0x6b71fe0007fff800 0x35b8ff0003fffc00

def z812 : W := mkw 0x0202020ca1c0dc78 0x0101010650e06e3c 0x2a000e0063c1fcf9 0x1500070031e0fe7c

def z813 : W := mkw 0x0202000481c0dc78 0x0101000240e06e3c 0x0000000000c03cf9 0x0000000000601e7c

def z814 : W := mkw 0x1c7dfebb78000000 0x8e3eff5dbc000000 0x107e7e1f80000000 0x083f3f0fc0000000

def z815 : W := mkw 0x3dfdfffb7e0542b4 0x9efefffdbf02a15a 0xddfffffffc0607ff 0xeefffffffe0303ff

def z816 : W := mkw 0x041436bb68000000 0x820a1b5db4000000 0x9c8e7e7fe0000000 0x4e473f3ff0000000

def z817 : W := mkw 0x4202000487e8d7f0 0x2101000243f46bf8 0x2000000007f9c7e0 0x1000000003fce3f0

def z818 : W := mkw 0x2f87674db7c59ecc 0x17c3b3a6dbe2cf66 0x510f8f9f9cc63b06 0xa887c7cfce631d83

def z819 : W := mkw 0x9dfdfffb78322000 0xcefefffdbc191000 0xddfffffff8380000 0x6efffffffc1c0000

def z820 : W := mkw 0x19f9c9d218000000 0x8cfce4e90c000000 0x517f819f98000000 0x28bfc0cfcc000000

def z821 : W := mkw 0x1e25fe297812f83a 0x8f12ff14bc097c1d 0x0a01fe007807f81f 0x8500ff003c03fc0f

def z822 : W := mkw 0x0404362d60404c38 0x02021b16b020261c 0xbe8e7e7fe3c1fcf9 0x5f473f3ff1e0fe7c

def z823 : W := mkw 0x3dfdfffb78054034 0x9efefffdbc02a01a 0xfffffffffc07c71f 0xfffffffffe03e38f

def z824 : W := mkw 0x47dc37fb6628dbb8 0x23ee1bfdb3146ddc 0x4b707f806439fb19 0x25b83fc0321cfd8c

def z825 : W := mkw 0x0c5813fb78000000 0x862c09fdbc000000 0x147e01fff8000000 0x0a3f00fffc000000

def z826 : W := mkw 0x906eac0007b7b000 0x4837560003dbd800 0xbafe7e0007fff800 0x5d7f3f0003fffc00

def z827 : W := mkw 0x045c269b20000000 0x022e134d90000000 0x107e0e1f80000000 0x083f070fc0000000

def z828 : W := mkw 0x3dfdfffb7e1762b4 0x9efefffdbf0bb15a 0xffffffffffffffff 0xffffffffffffffff

def z829 : W := mkw 0x0404362960000000 0x02021b14b0000000 0xbe8e7e7fe301c000 0x5f473f3ff180e000

def z830 : W := mkw 0x4002000487e807c0 0x2001000243f403e0 0x2200000007fe07ff 0x9100000003ff03ff

def z831 : W := mkw 0x147cbebb68000000 0x8a3e5f5db4000000 0x187e7e1fe0000000 0x0c3f3f0ff0000000

def z832 : W := mkw 0x0058009200000000 0x002c004900000000 0x94fe007f80000000 0x4a7f003fc0000000

def z833 : W := mkw 0x00308a9ca85a2d4a 0x0018454e542d16a5 0xff718ffffcfe3fff 0xffb8c7fffe7f1fff

def z834 : W := mkw 0x0604362960009808 0x03021b14b0004c04 0x9c8e7e7fe0003800 0x4e473f3ff0001c00

def z835 : W := mkw 0x41db41d687ed07c0 0x20eda0eb43f683e0 0xfffff1ffffffc7ff 0xfffff8ffffffe3ff

def z836 : W := mkw 0x2d85776976050284 0x16c2bbb4bb028142 0xdd8ffffffc060306 0xeec7fffffe030183

def z837 : W := mkw 0x41da01d687e897c0 0x20ed00eb43f44be0 0xf7fe01ff87f9ffe0 0x7bff00ffc3fcfff0

def z838 : W := mkw 0x3dfdfffb7e0542b4 0x9efefffdbf02a15a 0xddfffffffb01c7ff 0xeefffffffd80e3ff

def z839 : W := mkw 0x01d803da28000000 0x00ec01ed14000000 0xd5fe01fff8000000 0x6aff00fffc000000

def z840 : W := mkw 0x28015020560542b4 0x1400a8102b02a15a 0xef01f1807f07c7ff 0xf780f8c03f83e3ff

def z841 : W := mkw 0x0000000000000000 0x0000000000000000 0x100e001f80000000 0x0807000fc0000000

def z842 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0xffff8ffffcfe3f1f 0xffffc7fffe7f1f8f

def z843 : W := mkw 0x147cbebb68000000 0x8a3e5f5db4000000 0x10fe7e7f80000000 0x087f3f3fc0000000

def z844 : W := mkw 0x0ddd77fb70000000 0x06eebbfdb8000000 0xddfffffff8000000 0x6efffffffc000000

def z845 : W := mkw 0x41da01d287a002c0 0x20ed00e943d00160 0xf5fe01ff87f800e0 0x7aff00ffc3fc0070

def z846 : W := mkw 0x6002000487ff6ffe 0x3001000243ffb7ff 0x2200000007ffffff 0x9100000003ffffff

def z847 : W := mkw 0x4182014487fa2fca 0x20c100a243fd17e5 0xef8181e07ffe3fff 0xf7c0c0f03fff1fff

def z848 : W := mkw 0x0202000481c0d470 0x0101000240e06a38 0x2000000003c1c4e0 0x1000000001e0e270

def z849 : W := mkw 0x547cae9b28280100 0xaa3e574d94140080 0x107e0e1f80380000 0x083f070fc01c0000

def z850 : W := mkw 0x0000102040004030 0x0000081020002018 0xbe8e707fe301c4f9 0x5f47383ff180e27c

def z851 : W := mkw 0x91edec000637b000 0x48f6f600031bd800 0xfb71fe0004fff800 0x7db8ff00027ffc00

def z852 : W := mkw 0x1dfdfffb7e050000 0x8efefffdbf028000 0xffffffffff07c71f 0xffffffffff83e38f

def z853 : W := mkw 0x61da01d687ed07c4 0x30ed00eb43f683e2 0xf5fe01ff87fe07e6 0xfaff00ffc3ff03f3

def z854 : W := mkw 0x11fdedd206050280 0x08fef6e903028140 0xffffffff8707c7e0 0x7fffffffc383e3f0

def z855 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0xfffffe7f87fff800 0x7fffff3fc3fffc00

def z856 : W := mkw 0x0202000487e0dc78 0x0101000243f06e3c 0x2200000007f9fcf9 0x1100000003fcfe7c

def z857 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0xae807e6063c1fcf9 0x57403f3031e0fe7c

def z858 : W := mkw 0x0434beb9681a2102 0x021a5f5cb40d1081 0xddfffffffc3e0306 0xeefffffffe1f0183

def z859 : W := mkw 0x3dcd776b760542b4 0x9ee6bbb5bb02a15a 0xff8fffffff07c7ff 0xffc7ffffff83e3ff

def z860 : W := mkw 0x3dfdfffb780042b4 0x9efefffdbc00215a 0xddfffffff80000e0 0x6efffffffc000070

def z861 : W := mkw 0x9dfdfffb7817b000 0xcefefffdbc0bd800 0xfffffffffcfff800 0x7ffffffffe7ffc00

def z862 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0xff81ffe07fc7ffff 0xffc0fff03fe3ffff

def z863 : W := mkw 0x69c95162562542b4 0x34e4a8b12b12a15a 0xef81f1e07f07c7ff 0xf7c0f8f03f83e3ff

def z864 : W := mkw 0x1dfdfffb78009000 0x8efefffdbc004800 0xdffffffff801f800 0x6ffffffffc00fc00

def z865 : W := mkw 0x91fdedd20017b000 0x48fef6e9000bd800 0xdfffffff8007f800 0x6fffffffc003fc00

def z866 : W := mkw 0x02021024c1c0dc78 0x0101081260e06e3c 0x2a00700063c1fcf9 0x1500380031e0fe7c

def z867 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0x45fff1fff8000000 0x22fff8fffc000000

def z868 : W := mkw 0x01d801d200000000 0x00ec00e900000000 0xf5fe01ff830004e0 0x7aff00ffc1800270

def z869 : W := mkw 0x146cae0920000000 0x0a36570490000000 0x107e0e1f80000000 0x083f070fc0000000

def z870 : W := mkw 0x29835164d7c546f4 0x14c1a8b26be2a37a 0xef81f1e07fc7c7ff 0xf7c0f8f03fe3e3ff

def z871 : W := mkw 0x0202000481c0dc78 0x0101000240e06e3c 0xba000e0003c1fcf9 0x5d00070001e0fe7c

def z872 : W := mkw 0x3ddd75f3560542b4 0x9eeebaf9ab02a15a 0xf5fe71ff8701c7e0 0x7aff38ffc380e3f0

def z873 : W := mkw 0x0584376960000000 0x02c21bb4b0000000 0xdd8e7fffe0000000 0x6ec73ffff0000000

def z874 : W := mkw 0x15fcae9b28000000 0x8afe574d94000000 0xd1fe0e1f80000000 0x68ff070fc0000000

def z875 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0xb48e7e7f83c1fce0 0x5a473f3fc1e0fe70

def z876 : W := mkw 0x001012bc68484d3a 0x0008095e3424269d 0x040001fc780007ff 0x820000fe3c0003ff

def z877 : W := mkw 0x147cbebb68004030 0x8a3e5f5db4002018 0xbefe7e7fe301c4f9 0x5f7f3f3ff180e27c

def z878 : W := mkw 0xe002000487fff7f4 0x7001000243fffbfa 0x2200000007ffffff 0x9100000003ffffff

def z879 : W := mkw 0x1c7dfebb78000000 0x8e3eff5dbc000000 0xdd7fff9ff8000000 0x6ebfffcffc000000

def z880 : W := mkw 0x15fdfffb60000000 0x0afefffdb0000000 0xddffffffe0000000 0x6efffffff0000000

def z881 : W := mkw 0x8202000481f2fc78 0x4101000240f97e3c 0x2200000003f9fcf9 0x1100000001fcfe7c

def z882 : W := mkw 0x1ddd77fb78000000 0x8eeebbfdbc000000 0x9c8e7ffff8000000 0x4e473ffffc000000

def z883 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0x6b01f1807f07c7ff 0xb580f8c03f83e3ff

def z884 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xfffffffffb01c000 0x7ffffffffd80e000

def z885 : W := mkw 0x1dfdefdb38000000 0x8efef7ed9c000000 0xd9ffff9f98000000 0x6cffffcfcc000000

def z886 : W := mkw 0x0404362960004030 0x02021b14b0002018 0x9e8e7e7fe001c019 0x4f473f3ff000e00c

def z887 : W := mkw 0x4002000481c807c0 0x2001000240e403e0 0x2000000003c007e0 0x1000000001e003f0

def z888 : W := mkw 0x1ffdfffb7800d838 0x8ffefffdbc006c1c 0xfffffffffb01fcf9 0x7ffffffffd80fe7c

def z889 : W := mkw 0x0202000481dabd4a 0x0101000240ed5ea5 0x0000000000f83800 0x00000000007c1c00

def z890 : W := mkw 0x0606260da1c09c48 0x03031306d0e04e24 0xbe8e7e7f83c1fce0 0x5f473f3fc1e0fe70

def z891 : W := mkw 0x2ddd77fb760542b4 0x16eebbfdbb02a15a 0xffffffffff07c7ff 0xffffffffff83e3ff

def z892 : W := mkw 0x3dfdfffb7e050284 0x9efefffdbf028142 0xfdffffffff0607e6 0xfeffffffff8303f3

def z893 : W := mkw 0x01d941d200000000 0x00eca0e900000000 0xddfff1ff80000000 0x6efff8ffc0000000

def z894 : W := mkw 0x2c05762970054034 0x1602bb14b802a01a 0x9e8ffe7ff807c01f 0xcf47ff3ffc03e00f

def z895 : W := mkw 0x004a000481e00440 0x0025000240f00220 0xb4fe007f83f804e0 0x5a7f003fc1fc0270

def z896 : W := mkw 0x5c27fe2dffe807c0 0xae13ff16fff403e0 0x2801fe007ff807e0 0x1400ff003ffc03f0

def z897 : W := mkw 0x15fdfeb968000000 0x0afeff5cb4000000 0xddfffffff8000000 0x6efffffffc000000

def z898 : W := mkw 0x0202000481d2fc7a 0x0101000240e97e3d 0x2200000003c7fcff 0x9100000001e3fe7f

def z899 : W := mkw 0x41ea8b4aafb22aca 0x20f545a557d91565 0x0a8f8e63fb0638ff 0x8547c731fd831c7f

def z900 : W := mkw 0x41d801d206280380 0x20ec00e9031401c0 0x517e019f84380300 0x28bf00cfc21c0180

def z901 : W := mkw 0x947cae9b2812b000 0xca3e574d94095800 0x107e0e1f80003800 0x083f070fc0001c00

def z902 : W := mkw 0x15dc25d300000000 0x8aee12e980000000 0xd5fe01ff80000000 0x6aff00ffc0000000

def z903 : W := mkw 0x0002122ce1c04c78 0x0001091670e0263c 0xbe8e7e7fe3c1fcf9 0x5f473f3ff1e0fe7c

def z904 : W := mkw 0x107cac9200000000 0x083e564900000000 0x107e0e1f80000000 0x083f070fc0000000

def z905 : W := mkw 0x0634beb96812f83a 0x031a5f5cb4097c1d 0xdffffffff807f81f 0xeffffffffc03fc0f

def z906 : W := mkw 0x69db51f6d7ed47f4 0x34eda8fb6bf6a3fa 0xeff1f1e07fffc7ff 0xf7f8f8f03fffe3ff

def z907 : W := mkw 0x0584376966000280 0x02c21bb4b3000140 0xfd8e7fffe70007e0 0x7ec73ffff38003f0

def z908 : W := mkw 0x24043629660542b4 0x12021b14b302a15a 0xbe8e7e7fe707c7ff 0xdf473f3ff383e3ff

def z909 : W := mkw 0x0c04362978000000 0x86021b14bc000000 0x9c8e7e7ff8000000 0x4e473f3ffc000000

def z910 : W := mkw 0x147cbebb68000000 0x8a3e5f5db4000000 0xddfffffff8000000 0x6efffffffc000000

def z911 : W := mkw 0x2801502050054034 0x1400a8102802a01a 0xef81f1e07f07c7ff 0xf7c0f8f03f83e3ff

def z912 : W := mkw 0x29c95162560542b4 0x14e4a8b12b02a15a 0xef8ff1e3ff07c7ff 0xf7c7f8f1ff83e3ff

def z913 : W := mkw 0x6b835164d7eddffc 0x35c1a8b26bf6effe 0xef81f1e07fffffff 0xf7c0f8f03fffffff

def z914 : W := mkw 0x8026ac0007b7b000 0x4013560003dbd800 0xfbfffe0007fff800 0x7dffff0003fffc00

def z915 : W := mkw 0xd1efec0287b7b040 0x68f7f60143dbd820 0xfbfffe0387fff800 0x7dffff01c3fffc00

def z916 : W := mkw 0x5dfdfffb78080380 0xaefefffdbc0401c0 0xddfffffff8000300 0x6efffffffc000180

def z917 : W := mkw 0x9dfdfffb78059000 0xcefefffdbc02c800 0xddfffffff801c000 0x6efffffffc00e000

def z918 : W := mkw 0x4606362de1e8dd78 0x23031b16f0f46ebc 0xbe8e7e7fe3f9fcf9 0x5f473f3ff1fcfe7c

def z919 : W := mkw 0x0002000481c00440 0x0001000240e00220 0xf5fe007f87f804e0 0x7aff003fc3fc0270

def z920 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xfdfffffffcf80000 0x7efffffffe7c0000

def z921 : W := mkw 0x05cc376b60000000 0x02e61bb5b0000000 0x9c8e7e7fe0000000 0x4e473f3ff0000000

def z922 : W := mkw 0xab835164d7f7fefc 0x55c1a8b26bfbff7e 0xef81f1e07fffffff 0xf7c0f8f03fffffff

def z923 : W := mkw 0x39f9c9d21e1f2386 0x9cfce4e90f0f91c3 0x417181801c3e0306 0xa0b8c0c00e1f0183

def z924 : W := mkw 0xc002000481fab540 0x6001000240fd5aa0 0x0000000000f83800 0x00000000007c1c00

def z925 : W := mkw 0x41da01d681e807c0 0x20ed00eb40f403e0 0xd5fe01ff80f807e0 0x6aff00ffc07c03f0

def z926 : W := mkw 0x91efed4007b7b000 0x48f7f6a003dbd800 0xffffffe007fff800 0x7ffffff003fffc00

def z927 : W := mkw 0x1424be2968000000 0x8a125f14b4000000 0x9c8e7e7fe0000000 0x4e473f3ff0000000

def z928 : W := mkw 0xf9cf7562d7a5d2f4 0x7ce7bab16bd2e97a 0x008e70638301c0e0 0x00473831c180e070

def z929 : W := mkw 0xc002000487fab7c0 0x6001000243fd5be0 0x2000000007f83fe0 0x1000000003fc1ff0

def z930 : W := mkw 0x3dfdfffb7e0542b4 0x9efefffdbf02a15a 0xfdffffffff01c7e0 0x7effffffff80e3f0

def z931 : W := mkw 0x01d801d606480780 0x00ec00eb032403c0 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z932 : W := mkw 0x0000000000000000 0x0000000000000000 0xb48e007f830004e0 0x5a47003fc1800270

def z933 : W := mkw 0x0202000481dabd4a 0x0101000240ed5ea5 0x2200000004fe3f1f 0x91000000027f1f8f

def z934 : W := mkw 0x5dfdfffb7e280380 0xaefefffdbf1401c0 0xfdffffffff3807e0 0x7effffffff9c03f0

def z935 : W := mkw 0x01da01d207a00280 0x00ed00e903d00140 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z936 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xffff81ff87fe07e0 0x7fffc0ffc3ff03f0

def z937 : W := mkw 0x1dfdfffb7e000280 0x8efefffdbf000140 0xddfffffffb0000e0 0x6efffffffd800070

def z938 : W := mkw 0x3dfdfffb7e0542b4 0x9efefffdbf02a15a 0xfffffffffb01c4f9 0x7ffffffffd80e27c

def z939 : W := mkw 0x29d941d216050284 0x14eca0e90b028142 0xd5ff81ff9c060306 0xeaffc0ffce030183

def z940 : W := mkw 0x19fdfdf250000000 0x0cfefef928000000 0xddfffffff8000000 0x6efffffffc000000

def z941 : W := mkw 0x0002000481c80540 0x0001000240e402a0 0x2000000007f807e0 0x1000000003fc03f0

def z942 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0xbe8e7e7fe7c7ffff 0xdf473f3ff3e3ffff

def z943 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xd9fffe7f80000000 0x6cffff3fc0000000

def z944 : W := mkw 0x49835164d7e807c0 0x24c1a8b26bf403e0 0xed81f1e07ff807e0 0x76c0f8f03ffc03f0

def z945 : W := mkw 0x0434beb968000000 0x021a5f5cb4000000 0x9cfe7e7fe0000000 0x4e7f3f3ff0000000

def z946 : W := mkw 0x2202000481c0defc 0x1101000240e06f7e 0x2200000003c1ffff 0x9100000001e0ffff

def z947 : W := mkw 0x0404260920000000 0x0202130490000000 0x9c0e0e1fe0000000 0x4e07070ff0000000

def z948 : W := mkw 0x11efec0007a09000 0x08f7f60003d04800 0xfbfffe0007f9f800 0x7dffff0003fcfc00

def z949 : W := mkw 0x8202000481d7fc78 0x4101000240ebfe3c 0x2200000003c7fcf9 0x1100000001e3fe7c

def z950 : W := mkw 0x06063629e180d878 0x03031b14f0c06c3c 0x9e8e7e7fe301f8f9 0x4f473f3ff180fc7c

def z951 : W := mkw 0x147cae9b28000000 0x8a3e574d94000000 0xd97f8e1f80000000 0x6cbfc70fc0000000

def z952 : W := mkw 0x69db41d697ed47f4 0x34eda0eb4bf6a3fa 0x637181801fffc7ff 0xb1b8c0c00fffe3ff

def z953 : W := mkw 0x3dfdfffb7e050284 0x9efefffdbf028142 0xffffffffff07c306 0xffffffffff83e183

def z954 : W := mkw 0x15fcafdb2e000280 0x8afe57ed97000140 0xf5fe0fff870007e0 0x7aff07ffc38003f0

def z955 : W := mkw 0x3dfdfffb780542b4 0x9efefffdbc02a15a 0xdffffffff807c7ff 0xeffffffffc03e3ff

def z956 : W := mkw 0x0434ae9928000000 0x021a574c94000000 0xdd7f8f9ff8000000 0x6ebfc7cffc000000

def z957 : W := mkw 0x0602122de1c0dc78 0x03010916f0e06e3c 0x2200000063c1fcf9 0x1100000031e0fe7c

def z958 : W := mkw 0x681013fef8484ffe 0x340809ff7c2427ff 0x040001fff80007ff 0x820000fffc0003ff

def z959 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xf7fe01ff87fe07ff 0xfbff00ffc3ff03ff

def z960 : W := mkw 0x0ddc37fb78000000 0x86ee1bfdbc000000 0xddfe7ffff8000000 0x6eff3ffffc000000

def z961 : W := mkw 0xb9f9c9d21e372284 0xdcfce4e90f1b9142 0x417181801c3e0306 0xa0b8c0c00e1f0183

def z962 : W := mkw 0x68021164d7e847f4 0x340108b26bf423fa 0x240001e07ff807ff 0x920000f03ffc03ff

def z963 : W := mkw 0xc002000487ffbfca 0x6001000243ffdfe5 0x2200000007ffffff 0x9100000003ffffff

def z964 : W := mkw 0xb9c95160562542b4 0x5ce4a8b02b12a15a 0xef81f1e07f07c7ff 0xf7c0f8f03f83e3ff

def z965 : W := mkw 0x0232889489dafd7a 0x0119444a44ed7ebd 0x637181801fffffff 0xb1b8c0c00fffffff

def z966 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xd5fe01ff83f800e0 0x6aff00ffc1fc0070

def z967 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xd5fe7fff80000000 0x6aff3fffc0000000

def z968 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xf5ff81ff9ffe07e6 0xfaffc0ffcfff03f3

def z969 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0x14fe01ff83f807e0 0x0a7f00ffc1fc03f0

def z970 : W := mkw 0x05d803db28000000 0x82ec01ed94000000 0xd5fe01ff80000000 0x6aff00ffc0000000

def z971 : W := mkw 0x39fdfdf2560542b4 0x1cfefef92b02a15a 0xffffffffff07c7ff 0xffffffffff83e3ff

def z972 : W := mkw 0x1dfdfffb78080102 0x8efefffdbc040081 0xddfffffff8000306 0xeefffffffc000183

def z973 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0x148e7e7fe3c1fcf9 0x0a473f3ff1e0fe7c

def z974 : W := mkw 0x95edfe2966372000 0x4af6ff14b31b9000 0xddfffe7fe43e0000 0x6effff3ff21f0000

def z975 : W := mkw 0xc202000487fffff8 0x6101000243fffffc 0x2200000007fffff9 0x1100000003fffffc

def z976 : W := mkw 0x004e240001a09000 0x0027120000d04800 0xbafe7e0003f9f800 0x5d7f3f0001fcfc00

def z977 : W := mkw 0x19f9cbda38000000 0x8cfce5ed1c000000 0xddff8ffff8000000 0x6effc7fffc000000

def z978 : W := mkw 0x0606260da1c09c48 0x03031306d0e04e24 0x00000e0000c03800 0x0000070000601c00

def z979 : W := mkw 0x005801d200000000 0x002c00e900000000 0x147e01ff80000000 0x0a3f00ffc0000000

def z980 : W := mkw 0x41f88bda2e3a2382 0x20fc45ed171d11c1 0xddff8ffffc3e0306 0xeeffc7fffe1f0183

def z981 : W := mkw 0x11efec000192b000 0x08f7f60000c95800 0xfbfffe0007fff800 0x7dffff0003fffc00

def z982 : W := mkw 0x1ffdfffb78004838 0x8ffefffdbc00241c 0xddfffffff8000019 0x6efffffffc00000c

def z983 : W := mkw 0x147cae9b28000000 0x8a3e574d94000000 0xd57e0f9f80000000 0x6abf07cfc0000000

def z984 : W := mkw 0x4002000487ed07c0 0x2001000243f683e0 0x2200000007ffc7e0 0x1100000003ffe3f0

def z985 : W := mkw 0x15fdee9b28000000 0x8afef74d94000000 0x10fe7e1f80000000 0x087f3f0fc0000000

def z986 : W := mkw 0x01f88bda28000000 0x00fc45ed14000000 0xd5fe0fff80000000 0x6aff07ffc0000000

def z987 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xddfffffffc060306 0xeefffffffe030183

def z988 : W := mkw 0x15fcbffb68000000 0x8afe5ffdb4000000 0xddfe7fffe0000000 0x6eff3ffff0000000

def z989 : W := mkw 0x01d801d206000000 0x00ec00e903000000 0xf5fe01ff87000000 0x7aff00ffc3800000

def z990 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0xbe8ffe7ffbc7fcff 0xdf47ff3ffde3fe7f

def z991 : W := mkw 0x99efed4217b7b000 0xccf7f6a10bdbd800 0xfbfffe0007fff800 0x7dffff0003fffc00

def z992 : W := mkw 0x0006240001809000 0x0003120000c04800 0xfbfe7e0007f9f800 0x7dff3f0003fcfc00

def z993 : W := mkw 0xd1efed4287b7b2c0 0x68f7f6a143dbd960 0xffffffe387ffffe0 0x7ffffff1c3fffff0

def z994 : W := mkw 0x0191429c2e4d0d0a 0x00c8a14e17268685 0xef81f19c7f07c71f 0xf7c0f8ce3f83e38f

def z995 : W := mkw 0x1dedff6b70000000 0x8ef6ffb5b8000000 0xddfffe7fe0000000 0x6effff3ff0000000

def z996 : W := mkw 0x3dfdfffb7817683e 0x9efefffdbc0bb41f 0xdffffffff807f81f 0xeffffffffc03fc0f

def z997 : W := mkw 0x1ffdfffb7812f83a 0x8ffefffdbc097c1d 0xdffffffff807f81f 0xeffffffffc03fc0f

def z998 : W := mkw 0x0404362960000000 0x02021b14b0000000 0x108e7e7f80000000 0x08473f3fc0000000

def z999 : W := mkw 0x9e25fe297817f838 0xcf12ff14bc0bfc1c 0x0a01fe007807f819 0x0500ff003c03fc0c

def z1000 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0xbafe7e0003f9f800 0x5d7f3f0001fcfc00

def z1001 : W := mkw 0x906fec0007b7b000 0x4837f60003dbd800 0x3a7ffe0007fff800 0x1d3fff0003fffc00

def z1002 : W := mkw 0x0021c80000172000 0x0010e400000b9000 0xfb71fe0004fff800 0x7db8ff00027ffc00

def z1003 : W := mkw 0x3dfdfffb7e1f2386 0x9efefffdbf0f91c3 0xddfffffffc3e0306 0xeefffffffe1f0183

def z1004 : W := mkw 0x81ce240007b7b000 0x40e7120003dbd800 0xfbfe7e0007fff800 0x7dff3f0003fffc00

def z1005 : W := mkw 0x1dfdfffb7e000280 0x8efefffdbf000140 0xddfffffffc000300 0x6efffffffe000180

def z1006 : W := mkw 0x0002000481c00440 0x0001000240e00220 0x0000000000c00000 0x0000000000600000

def z1007 : W := mkw 0x1ddd77fb78000000 0x8eeebbfdbc000000 0xcd8ff1fff8000000 0x66c7f8fffc000000

def z1008 : W := mkw 0x3dfdfffb7e0542b4 0x9efefffdbf02a15a 0xdffffffffc07c31f 0xeffffffffe03e18f

def z1009 : W := mkw 0x1dfdfffb7e054030 0x8efefffdbf02a018 0xffffffffff07c4f9 0x7fffffffff83e27c

def z1010 : W := mkw 0x01d801d200000280 0x00ec00e900000140 0xd5fe01ff800007e0 0x6aff00ffc00003f0

def z1011 : W := mkw 0x041436b960000000 0x020a1b5cb0000000 0xddfe7fffe0000000 0x6eff3ffff0000000

def z1012 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0x557f8ffff8000000 0x2abfc7fffc000000

def z1013 : W := mkw 0x00021024c1c04470 0x0001081260e02238 0xae80706063c1c4f9 0x5740383031e0e27c

def z1014 : W := mkw 0x0404362960009000 0x02021b14b0004800 0x9e8e7e7fe001f800 0x4f473f3ff000fc00

def z1015 : W := mkw 0x3dfdfffb7e0542b4 0x9efefffdbf02a15a 0x10fe7e7f8301c0e0 0x087f3f3fc180e070

def z1016 : W := mkw 0x0e06362df9c0dc78 0x87031b16fce06e3c 0xbe8e7e7ffbc1fcf9 0x5f473f3ffde0fe7c

def z1017 : W := mkw 0x4002000487fa27c2 0x2001000243fd13e1 0x2000000007fe07e6 0x9000000003ff03f3

def z1018 : W := mkw 0x405a009681e80540 0x202d004b40f402a0 0x10fe007f83f800e0 0x087f003fc1fc0070

def z1019 : W := mkw 0x2a021164d1c0defc 0x150108b268e06f7e 0x260001e07bc1ffff 0x930000f03de0ffff

def z1020 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0x4170018004f80300 0x20b800c0027c0180

def z1021 : W := mkw 0x2dd813fb7e0042b4 0x96ec09fdbf00215a 0xf5fe01ffff0007ff 0xfaff00ffff8003ff

def z1022 : W := mkw 0x4002000487e807c0 0x2001000243f403e0 0xe500018007f807e0 0x728000c003fc03f0

def z1023 : W := mkw 0xbe25fe297017f83c 0x5f12ff14b80bfc1e 0x0a01fe007807f81f 0x8500ff003c03fc0f

def z1024 : W := mkw 0x41ca000487e807c0 0x20e5000243f403e0 0xf5fe007f87f807e0 0x7aff003fc3fc03f0

def z1025 : W := mkw 0x41db41d687ed07c0 0x20eda0eb43f683e0 0xf5fe71ff87f9c7e0 0x7aff38ffc3fce3f0

def z1026 : W := mkw 0x0981516050000000 0x04c0a8b028000000 0xdd8ff1fff8000000 0x6ec7f8fffc000000

def z1027 : W := mkw 0x9425fe296017b000 0x4a12ff14b00bd800 0x9e8ffe7fe007f800 0x4f47ff3ff003fc00

def z1028 : W := mkw 0x060436296000d030 0x03021b14b0006818 0x9c8e7e7fe001c000 0x4e473f3ff000e000

def z1029 : W := mkw 0x43da01d687e89fc8 0x21ed00eb43f44fe4 0xf5fe01ff87f83fe0 0x7aff00ffc3fc1ff0

def z1030 : W := mkw 0x01801160460042b0 0x00c008b023002158 0xef81f1e07f07c7ff 0xf7c0f8f03f83e3ff

def z1031 : W := mkw 0x041436b968000000 0x020a1b5cb4000000 0x9c8e7ffff8000000 0x4e473ffffc000000

def z1032 : W := mkw 0x29c95160560542b4 0x14e4a8b02b02a15a 0xfffff1e07f07c7ff 0xfffff8f03f83e3ff

def z1033 : W := mkw 0x91cf640007a59000 0x48e7b20003d2c800 0xfbfe7e0007f9f800 0x7dff3f0003fcfc00

def z1034 : W := mkw 0x6983414497ed07c4 0x34c1a0a24bf683e2 0x610181801ffe07e6 0xb080c0c00fff03f3

def z1035 : W := mkw 0x11fcadd200000000 0x08fe56e900000000 0xd5fe0fff80000000 0x6aff07ffc0000000

def z1036 : W := mkw 0x41d801d206200280 0x20ec00e903100140 0xd5fe01ff80000000 0x6aff00ffc0000000

def z1037 : W := mkw 0x05fcbffb68000000 0x02fe5ffdb4000000 0xddfffffff8000000 0x6efffffffc000000

def z1038 : W := mkw 0x69db41d697ed07c4 0x34eda0eb4bf683e2 0xffff81fffffe07ff 0xffffc0ffffff03ff

def z1039 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0x6b718f807cfe3f1f 0xb5b8c7c03e7f1f8f

def z1040 : W := mkw 0x1dfdfffb78050000 0x8efefffdbc028000 0xdffffffff807c000 0x6ffffffffc03e000

def z1041 : W := mkw 0x5dfdfffb7e3a2382 0xaefefffdbf1d11c1 0xddfffffffc3e0306 0xeefffffffe1f0183

def z1042 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0xfff1f1e07fffc7ff 0xfff8f8f03fffe3ff

def z1043 : W := mkw 0x4202000487e89fc8 0x2101000243f44fe4 0x2000000007f83fe0 0x1000000003fc1ff0

def z1044 : W := mkw 0x00308890081a2102 0x00184448040d1081 0xff718f807cfe3f1f 0xffb8c7c03e7f1f8f

def z1045 : W := mkw 0x41d801d6866807c0 0x20ec00eb433403e0 0xd5fe01ff843807e0 0x6aff00ffc21c03f0

def z1046 : W := mkw 0x1dfdfffb7e050000 0x8efefffdbf028000 0xddfffffffb01c000 0x6efffffffd80e000

def z1047 : W := mkw 0x1dfdfffb78122000 0x8efefffdbc091000 0xdffffffff8063800 0x6ffffffffc031c00

def z1048 : W := mkw 0x01f889d200000000 0x00fc44e900000000 0xddff8fff80000000 0x6effc7ffc0000000

def z1049 : W := mkw 0x0180014006000280 0x00c000a003000140 0xf58e01ff870007e0 0x7ac700ffc38003f0

def z1050 : W := mkw 0x8c1213fb7fb7b000 0xc60909fdbfdbd800 0x260001fffffff800 0x130000fffffffc00

def z1051 : W := mkw 0x0012009481c80540 0x0009004a40e402a0 0xb4fe007f83f804e0 0x5a7f003fc1fc0270

def z1052 : W := mkw 0x0010029c20480d08 0x0008014e10240684 0xff718f9c7cfe3f1f 0xffb8c7ce3e7f1f8f

def z1053 : W := mkw 0x01c8000000000000 0x00e4000000000000 0xd5fe007f80000000 0x6aff003fc0000000

def z1054 : W := mkw 0x6002000487ed47f4 0x3001000243f6a3fa 0x2000000007f9c7e0 0x1000000003fce3f0

def z1055 : W := mkw 0x01d811f240004030 0x00ec08f920002018 0xfffe71ffe301c4f9 0x7fff38fff180e27c

def z1056 : W := mkw 0x15fdee9b2e050000 0x8afef74d97028000 0xfbfffe1f8707c000 0x7dffff0fc383e000

def z1057 : W := mkw 0x01f889d200122000 0x00fc44e900091000 0xffff8fff84fe3800 0x7fffc7ffc27f1c00

def z1058 : W := mkw 0x4002000487e847f0 0x2001000243f423f8 0x2200000007f9c7f9 0x1100000003fce3fc

def z1059 : W := mkw 0x40308a9ea85a2d4a 0x2018454f542d16a5 0xff718f9ffcfe3f1f 0xffb8c7cffe7f1f8f

def z1060 : W := mkw 0x147dee9b28000000 0x8a3ef74d94000000 0x187ffe1f80000000 0x0c3fff0fc0000000

def z1061 : W := mkw 0x11dd65d200000000 0x08eeb2e900000000 0xd5fe71ff80000000 0x6aff38ffc0000000

def z1062 : W := mkw 0x59db41d697e807c0 0xaceda0eb4bf403e0 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z1063 : W := mkw 0x93ebc80487f7fc78 0x49f5e40243fbfe3c 0x6371800007fffcf9 0x31b8c00003fffe7c

def z1064 : W := mkw 0x0202000487c5dc78 0x0101000243e2ee3c 0x2200000007c7fcf9 0x1100000003e3fe7c

def z1065 : W := mkw 0x2002000487c546f4 0x1001000243e2a37a 0x2200000007c7c7ff 0x9100000003e3e3ff

def z1066 : W := mkw 0x2b835164d7dffffe 0x15c1a8b26befffff 0xef81f1e07fffffff 0xf7c0f8f03fffffff

def z1067 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0xfbffff801ffffb06 0xfdffffc00ffffd83

def z1068 : W := mkw 0x0006260ca1c09c48 0x0003130650e04e24 0xbe8e7e7fe3c1fcf9 0x5f473f3ff1e0fe7c

def z1069 : W := mkw 0x019201d487c807c0 0x00c900ea43e403e0 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z1070 : W := mkw 0x3dfdfffb78000284 0x9efefffdbc000142 0xddfffffff8000306 0xeefffffffc000183

def z1071 : W := mkw 0x01dc25d200000000 0x00ee12e900000000 0xddfe7fff80000000 0x6eff3fffc0000000

def z1072 : W := mkw 0x1dfdfdf358000000 0x8efefef9ac000000 0xd5fff1ff98000000 0x6afff8ffcc000000

def z1073 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xddfffffff800071f 0xeefffffffc00038f

def z1074 : W := mkw 0x00208804005a2d0a 0x00104402002d1685 0xff718f807cfe3f1f 0xffb8c7c03e7f1f8f

def z1075 : W := mkw 0x405a009681e80540 0x202d004b40f402a0 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z1076 : W := mkw 0x145c269b28000000 0x8a2e134d94000000 0x000e001f80000000 0x0007000fc0000000

def z1077 : W := mkw 0x4e1013fff8484ff8 0xa70809fffc2427fc 0x040001fff80007f9 0x020000fffc0003fc

def z1078 : W := mkw 0x02021024c1dafd7a 0x0101081260ed7ebd 0xef81f1e07fffffff 0xf7c0f8f03fffffff

def z1079 : W := mkw 0x0002000481c00440 0x0001000240e00220 0xa480006003c004e0 0x5240003001e00270

def z1080 : W := mkw 0x95fdee9b2e372000 0xcafef74d971b9000 0x517f8e1f843e0000 0x28bfc70fc21f0000

def z1081 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0x32fe7e0007fff800 0x197f3f0003fffc00

def z1082 : W := mkw 0x99efec001fb7b000 0xccf7f6000fdbd800 0xfbfffe001ffff800 0x7dffff000ffffc00

def z1083 : W := mkw 0x1c7cbffb78000000 0x8e3e5ffdbc000000 0x9cfe7ffff8000000 0x4e7f3ffffc000000

def z1084 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xfffe0fff87f83fe0 0x7fff07ffc3fc1ff0

def z1085 : W := mkw 0x69835164d7ff6ffe 0x34c1a8b26bffb7ff 0xef81f1e07fffffff 0xf7c0f8f03fffffff

def z1086 : W := mkw 0x5dfdfffb78280100 0xaefefffdbc140080 0xddfffffff8380000 0x6efffffffc1c0000

def z1087 : W := mkw 0x83835024c7f7fc78 0x41c1a81263fbfe3c 0xef81f06067fffcf9 0x77c0f83033fffe7c

def z1088 : W := mkw 0x0010009000000000 0x0008004800000000 0xd5fe01ff80000000 0x6aff00ffc0000000

def z1089 : W := mkw 0x99efed4017b7b000 0x4cf7f6a00bdbd800 0xfbffff801ffff800 0x7dffffc00ffffc00

def z1090 : W := mkw 0x1c25fe2978000000 0x8e12ff14bc000000 0x180ffe1ff8000000 0x0c07ff0ffc000000

def z1091 : W := mkw 0x3ffdfffb7e05dabc 0x9ffefffdbf02ed5e 0xffffffffff07ffff 0xffffffffff83ffff

def z1092 : W := mkw 0x4182000487e807c0 0x20c1000243f403e0 0xe180000007f807e0 0x70c0000003fc03f0

def z1093 : W := mkw 0x2c043769700042b4 0x16021bb4b800215a 0x9c8e7ffff80007ff 0xce473ffffc0003ff

def z1094 : W := mkw 0x4002000487e807c0 0x2001000243f403e0 0xa480006007f807e0 0x5240003003fc03f0

def z1095 : W := mkw 0x0585762960000000 0x02c2bb14b0000000 0xdd8ffe7fe0000000 0x6ec7ff3ff0000000

def z1096 : W := mkw 0x0181502046054030 0x00c0a8102302a018 0xef81f1e07f07c7ff 0xf7c0f8f03f83e3ff

def z1097 : W := mkw 0x15fdfebb68000000 0x8afeff5db4000000 0xddfffe7fe0000000 0x6effff3ff0000000

def z1098 : W := mkw 0x0404362960000000 0x02021b14b0000000 0xbc8e7e7fe30004e0 0x5e473f3ff1800270

def z1099 : W := mkw 0x3dedff69760542b4 0x1ef6ffb4bb02a15a 0xffffffffff07c7ff 0xffffffffff83e3ff

def z1100 : W := mkw 0x01eeac0007b2b000 0x00f7560003d95800 0xfbfffe0007fff800 0x7dffff0003fffc00

def z1101 : W := mkw 0x3dfdfffb78050004 0x9efefffdbc028002 0xddfffffff8060006 0xeefffffffc030003

def z1102 : W := mkw 0x4606362de7e8dff8 0x23031b16f3f46ffc 0x2a007e0067f9fff9 0x15003f0033fcfffc

def z1103 : W := mkw 0x6e1013fff0484ffc 0x370809fff82427fe 0x040001fff80007ff 0x820000fffc0003ff

def z1104 : W := mkw 0x29f9dbfa7e0542b4 0x14fcedfd3f02a15a 0xffffffffff07c7ff 0xffffffffff83e3ff

def z1105 : W := mkw 0x09d941d210000000 0x04eca0e908000000 0xd5ff81ff98000000 0x6affc0ffcc000000

def z1106 : W := mkw 0xb9efec0017b7b004 0x5cf7f6000bdbd802 0xfbfffe001ffff806 0xfdffff000ffffc03

def z1107 : W := mkw 0x00308a98281a290a 0x0018454c140d1485 0xfb718f807cfe3b1f 0xfdb8c7c03e7f1d8f

def z1108 : W := mkw 0x0e1013fff8484d7a 0x870809fffc2426bd 0x040001fff80007ff 0x820000fffc0003ff

def z1109 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0xbe8e7ffffbc1ffff 0xdf473ffffde0ffff

def z1110 : W := mkw 0x1dfdfffb7800080a 0x8efefffdbc000405 0xddfffffff800001f 0xeefffffffc00000f

def z1111 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0x557e01ff84f807e0 0x2abf00ffc27c03f0

def z1112 : W := mkw 0x00788a9a28000000 0x003c454d14000000 0xdd7f8f9ff8000000 0x6ebfc7cffc000000

def z1113 : W := mkw 0x1dfdfffb78004030 0x8efefffdbc002018 0xddfffffff80004f9 0x6efffffffc00027c

def z1114 : W := mkw 0x061012bd68484d3a 0x0308095eb424269d 0x0400019c7800071f 0x820000ce3c00038f

def z1115 : W := mkw 0x040636296180d030 0x02031b14b0c06818 0xbe8e7e7fe3c1fcf9 0x5f473f3ff1e0fe7c

def z1116 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0x328e7e7f83c1fcf9 0x19473f3fc1e0fe7c

def z1117 : W := mkw 0x0400122960000000 0x02000914b0000000 0x948e007fe0000000 0x4a47003ff0000000

def z1118 : W := mkw 0x4002000487e897c0 0x2001000243f44be0 0x2200000007f9ffe0 0x1100000003fcfff0

def z1119 : W := mkw 0x00308a9828122000 0x0018454c14091000 0xff718f9c7cfe3f1f 0xffb8c7ce3e7f1f8f

def z1120 : W := mkw 0x02021024c1c0dc78 0x0101081260e06e3c 0x2600006063c1fcf9 0x1300003031e0fe7c

def z1121 : W := mkw 0x1c35feb978000000 0x8e1aff5cbc000000 0xddfffffff8000000 0x6efffffffc000000

def z1122 : W := mkw 0x1dcd776b70000000 0x8ee6bbb5b8000000 0x048e707fe0000000 0x0247383ff0000000

def z1123 : W := mkw 0x1dedfe2978000000 0x8ef6ff14bc000000 0xddfffe7ff8000000 0x6effff3ffc000000

def z1124 : W := mkw 0x0202000481c0dc78 0x0101000240e06e3c 0xa680006003c1fcf9 0x5340003001e0fe7c

def z1125 : W := mkw 0x147cae9b281a2102 0x8a3e574d940d1081 0x517f8f9f9c3e0306 0xa8bfc7cfce1f0183

def z1126 : W := mkw 0x4002000487fa27c0 0x2001000243fd13e0 0x2200000007fe3fe0 0x1100000003ff1ff0

def z1127 : W := mkw 0x01d801d206000280 0x00ec00e903000140 0xd5fe01ff84000300 0x6aff00ffc2000180

def z1128 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0xfffffe6007fffce0 0x7fffff3003fffe70

def z1129 : W := mkw 0x3c7cbffb780042b4 0x9e3e5ffdbc00215a 0x147e0ffff80007ff 0x8a3f07fffc0003ff

def z1130 : W := mkw 0x0606362de1c8dd7a 0x03031b16f0e46ebd 0xbe8e7e7fe3c1ffff 0xdf473f3ff1e0ffff

def z1131 : W := mkw 0x061012bde8484d7a 0x0308095ef42426bd 0x0400007fe00004f9 0x0200003ff000027c

def z1132 : W := mkw 0x01f88bda2e000280 0x00fc45ed17000140 0xffff8fffff0607ff 0xffffc7ffff8303ff

def z1133 : W := mkw 0x0b835164d1c0dc78 0x05c1a8b268e06e3c 0xef81f1e07bc1fcf9 0x77c0f8f03de0fe7c

def z1134 : W := mkw 0x0180014000000000 0x00c000a000000000 0xd58e01ff80000000 0x6ac700ffc0000000

def z1135 : W := mkw 0x041437fb60000000 0x020a1bfdb0000000 0x9c8e7fffe0000000 0x4e473ffff0000000

def z1136 : W := mkw 0x0404362960004030 0x02021b14b0002018 0x9c8e7e7fe00004f9 0x4e473f3ff000027c

def z1137 : W := mkw 0x4002000487e807c0 0x2001000243f403e0 0x00000000030007e0 0x00000000018003f0

def z1138 : W := mkw 0x3dfdfffb78054034 0x9efefffdbc02a01a 0xddfffffff801c000 0x6efffffffc00e000

def z1139 : W := mkw 0x1dfdfffb781a2102 0x8efefffdbc0d1081 0xfffffffffc3e071f 0xfffffffffe1f038f

def z1140 : W := mkw 0x3c25fe2978054034 0x9e12ff14bc02a01a 0xbe8ffe7ffb07c4ff 0xdf47ff3ffd83e27f

def z1141 : W := mkw 0x69db41d697ed07c4 0x34eda0eb4bf683e2 0xfffff1ff9fffc7e6 0xfffff8ffcfffe3f3

def z1142 : W := mkw 0x15fdee9b28000000 0x8afef74d94000000 0xddffff9ff8000000 0x6effffcffc000000

def z1143 : W := mkw 0x0404362960000000 0x02021b14b0000000 0xbe8e7e7fe0c03800 0x5f473f3ff0601c00

def z1144 : W := mkw 0x0202000481c8dd7a 0x0101000240e46ebd 0x2200000003c1ffff 0x9100000001e0ffff

def z1145 : W := mkw 0x906fec0001b7b000 0x4837f60000dbd800 0xbafffe0003fff800 0x5d7fff0001fffc00

def z1146 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0x597fff9ff8000000 0x2cbfffcffc000000

def z1147 : W := mkw 0x91efed4207b7b000 0x48f7f6a103dbd800 0xfbfffe6387fff800 0x7dffff31c3fffc00

def z1148 : W := mkw 0x2d857769760542b4 0x16c2bbb4bb02a15a 0x9c8e7e7fe301c0e0 0x4e473f3ff180e070

def z1149 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0xfffe7e7fe7f9fcf9 0x7fff3f3ff3fcfe7c

def z1150 : W := mkw 0x20001020460542b4 0x100008102302a15a 0xef81f1e07f07c7ff 0xf7c0f8f03f83e3ff

def z1151 : W := mkw 0x01d801d200000000 0x00ec00e900000000 0x10fe007f80000000 0x087f003fc0000000

def z1152 : W := mkw 0x0202000481c0dc78 0x0101000240e06e3c 0x0000000003c1f8e0 0x0000000001e0fc70

def z1153 : W := mkw 0x461012bfe0484d78 0x2308095ff02426bc 0x0400007fe00004f9 0x0200003ff000027c

def z1154 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0x9cfe7e7fe0000000 0x4e7f3f3ff0000000

def z1155 : W := mkw 0x4002000487e807c0 0x2001000243f403e0 0x0000000003f800e0 0x0000000001fc0070

def z1156 : W := mkw 0xd1ebc80487ff27c0 0x68f5e40243ff93e0 0x6171800007fe07e0 0x30b8c00003ff03f0

def z1157 : W := mkw 0x4002000481e80540 0x2001000240f402a0 0x2000000003f804e0 0x1000000001fc0270

def z1158 : W := mkw 0x91efed4007b7b280 0x48f7f6a003dbd940 0xfbfffe6007fff8e0 0x7dffff3003fffc70

def z1159 : W := mkw 0x8202000487f7bc48 0x4101000243fbde24 0x2200000007fff800 0x1100000003fffc00

def z1160 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0x51ffffff98000000 0x28ffffffcc000000

def z1161 : W := mkw 0x9227ec0481d7fc78 0x4913f60240ebfe3c 0x2a01fe0003c7fcf9 0x1500ff0001e3fe7c

def z1162 : W := mkw 0x405a009687e807c0 0x202d004b43f403e0 0xb4fe007f87f807e0 0x5a7f003fc3fc03f0

def z1163 : W := mkw 0x41da01d287a803c0 0x20ed00e943d401e0 0xd5fe01ff873803e0 0x6aff00ffc39c01f0

def z1164 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0x0e8e7e7fe301fcf9 0x07473f3ff180fe7c

def z1165 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0x0a007e0060c1f819 0x05003f003060fc0c

def z1166 : W := mkw 0x05dc27db20000000 0x02ee13ed90000000 0xd5fe0fff80000000 0x6aff07ffc0000000

def z1167 : W := mkw 0x045c36bb60000000 0x022e1b5db0000000 0x9cfe7e7fe0000000 0x4e7f3f3ff0000000

def z1168 : W := mkw 0x01d801d200000000 0x00ec00e900000000 0x517e019f80000000 0x28bf00cfc0000000

def z1169 : W := mkw 0x167cbebb6800d838 0x8b3e5f5db4006c1c 0x1a7e7e1fe001f819 0x0d3f3f0ff000fc0c

def z1170 : W := mkw 0x09d811f250000000 0x04ec08f928000000 0xd5fe01fff8000000 0x6aff00fffc000000

def z1171 : W := mkw 0x2f8577697605dabc 0x17c2bbb4bb02ed5e 0xff8fffffff07ffff 0xffc7ffffff83ffff

def z1172 : W := mkw 0x2b835164d7c5defc 0x15c1a8b26be2ef7e 0x2280706003c1fcf9 0x1140383001e0fe7c

def z1173 : W := mkw 0x0d9577fb78000000 0x86cabbfdbc000000 0xdd8ffffff8000000 0x6ec7fffffc000000

def z1174 : W := mkw 0x06308a9da85a2d4a 0x0318454ed42d16a5 0xff718f9ffcfe3f1f 0xffb8c7cffe7f1f8f

def z1175 : W := mkw 0x147cae9b28000000 0x8a3e574d94000000 0x94fe0e7f80000000 0x4a7f073fc0000000

def z1176 : W := mkw 0x01c8014200000000 0x00e400a100000000 0x948e007f80000000 0x4a47003fc0000000

def z1177 : W := mkw 0x2202000487dffffe 0x1101000243efffff 0x2200000007ffffff 0x9100000003ffffff

def z1178 : W := mkw 0x2e1013fdf8484ffe 0x170809fefc2427ff 0x040001fff80007ff 0x820000fffc0003ff

def z1179 : W := mkw 0x01d801d200000000 0x00ec00e900000000 0xf5fe01ff84f80000 0x7aff00ffc27c0000

def z1180 : W := mkw 0x00208a0c20522c08 0x0010450610291604 0xff718f9c7cfe3f1f 0xffb8c7ce3e7f1f8f

def z1181 : W := mkw 0xb9efed4017b7b284 0x5cf7f6a00bdbd942 0xffffffe01fffffe6 0xfffffff00ffffff3

def z1182 : W := mkw 0x1c35fffb78000000 0x8e1afffdbc000000 0x9c8ffffff8000000 0x4e47fffffc000000

def z1183 : W := mkw 0x1dedff6b78000000 0x8ef6ffb5bc000000 0x9c8ffe7ff8000000 0x4e47ff3ffc000000

def z1184 : W := mkw 0xa202000487f7fefc 0x5101000243fbff7e 0x2200000007ffffff 0x9100000003ffffff

def z1185 : W := mkw 0x2d815163560542b4 0x96c0a8b1ab02a15a 0xef81f1e3ff07c7ff 0xf7c0f8f1ff83e3ff

def z1186 : W := mkw 0x1424ae0928000000 0x8a12570494000000 0x100e0e1f80000000 0x0807070fc0000000

def z1187 : W := mkw 0x01f889d208000000 0x00fc44e904000000 0xd5ff81ff98000000 0x6affc0ffcc000000

def z1188 : W := mkw 0x1c7dfebb78000000 0x8e3eff5dbc000000 0x9cfffe7ff8000000 0x4e7fff3ffc000000

def z1189 : W := mkw 0x28015160560542b4 0x1400a8b02b02a15a 0x2e01f1e07f07c7ff 0x9700f8f03f83e3ff

def z1190 : W := mkw 0x1e27fe2df9c0dc78 0x8f13ff16fce06e3c 0x2a01fe007bc1fcf9 0x1500ff003de0fe7c

def z1191 : W := mkw 0x9dfdfffb78172000 0xcefefffdbc0b9000 0xddfffffff8060000 0x6efffffffc030000

def z1192 : W := mkw 0x29c95160562542b4 0x14e4a8b02b12a15a 0xeff1f1e07f3fc7ff 0xf7f8f8f03f9fe3ff

def z1193 : W := mkw 0x0434ae9928000000 0x021a574c94000000 0x107e0e1f80000000 0x083f070fc0000000

def z1194 : W := mkw 0x061012bde0484d78 0x0308095ef02426bc 0x040001ffe00007f9 0x020000fff00003fc

def z1195 : W := mkw 0x0002000481c09440 0x0001000240e04a20 0x2200000003c1fce0 0x1100000001e0fe70

def z1196 : W := mkw 0x1dfdfffb7e050280 0x8efefffdbf028140 0xffffffffff07c7e0 0x7fffffffff83e3f0

def z1197 : W := mkw 0x01d801d200000000 0x00ec00e900000000 0x048e01ff80000000 0x024700ffc0000000

def z1198 : W := mkw 0x4022880487fa27c0 0x2011440243fd13e0 0xfb718e0007fe3fe0 0x7db8c70003ff1ff0

def z1199 : W := mkw 0x4202000481e89d48 0x2101000240f44ea4 0x0000000000f83800 0x00000000007c1c00

def z1200 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0x0c8ffffff8000000 0x0647fffffc000000

def z1201 : W := mkw 0x8002000487f7b440 0x4001000243fbda20 0x2200000007fffce0 0x1100000003fffe70

def z1202 : W := mkw 0x43821164c7e8dff8 0x21c108b263f46ffc 0xef8071e067f9fff9 0x77c038f033fcfffc

def z1203 : W := mkw 0x15fdefdb28000000 0x8afef7ed94000000 0xddffffff80000000 0x6effffffc0000000

def z1204 : W := mkw 0x405a01d681e807c0 0x202d00eb40f403e0 0x107e007f80f800e0 0x083f003fc07c0070

def z1205 : W := mkw 0x1dfdfffb7e200000 0x8efefffdbf100000 0xddfffffffc380000 0x6efffffffe1c0000

def z1206 : W := mkw 0x05dc35f340000000 0x02ee1af9a0000000 0xd5fe71ff80000000 0x6aff38ffc0000000

def z1207 : W := mkw 0x947cae9b28322000 0xca3e574d94191000 0x107e0e1f80380000 0x083f070fc01c0000

def z1208 : W := mkw 0x4002000487e80540 0x2001000243f402a0 0x2000000007f80000 0x1000000003fc0000

def z1209 : W := mkw 0x9dfdfffb7e17b000 0xcefefffdbf0bd800 0xffffffffff07f800 0x7fffffffff83fc00

def z1210 : W := mkw 0x2a035024d1c5dc7c 0x1501a81268e2ee3e 0x2a01f0007bc7fcff 0x9500f8003de3fe7f

def z1211 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xfffffffffc060000 0x7ffffffffe030000

def z1212 : W := mkw 0x7dfdfffb7e2d0384 0xbefefffdbf1681c2 0xddfffffffc3e0306 0xeefffffffe1f0183

def z1213 : W := mkw 0x2202000481c5dc7c 0x1101000240e2ee3e 0x2200000003c7fcff 0x9100000001e3fe7f

def z1214 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0xf1fe7e0007f9f800 0x78ff3f0003fcfc00

def z1215 : W := mkw 0xd1f9c9d20e3f2382 0x68fce4e9071f91c1 0x417181801c3e0306 0xa0b8c0c00e1f0183

def z1216 : W := mkw 0x69db41d697ed07c4 0x34eda0eb4bf683e2 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z1217 : W := mkw 0x167cae9b28009808 0x8b3e574d94004c04 0x107e0e1f80003800 0x083f070fc0001c00

def z1218 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xfffe01ffe7f807f9 0x7fff00fff3fc03fc

def z1219 : W := mkw 0x41d801d6804807c0 0x20ec00eb402403e0 0xf5fe01ff84f807e0 0x7aff00ffc27c03f0

def z1220 : W := mkw 0x0000020820000000 0x0000010410000000 0x9c8e0e7fe0000000 0x4e47073ff0000000

def z1221 : W := mkw 0x1dfdfffb7e000000 0x8efefffdbf000000 0xfdffffffff000000 0x7effffffff800000

def z1222 : W := mkw 0x8202000487fffd7a 0x4101000243fffebd 0x2200000007ffffff 0x9100000003ffffff

def z1223 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xf1fe007f87f800e0 0x78ff003fc3fc0070

def z1224 : W := mkw 0x19d941d210000000 0x8ceca0e908000000 0xd5fe01ff80000000 0x6aff00ffc0000000

def z1225 : W := mkw 0x0404362960000000 0x02021b14b0000000 0xbe8e7e7fe0000419 0x5f473f3ff000020c

def z1226 : W := mkw 0x81a3c80007b7b000 0x40d1e40003dbd800 0xfbf1fe0007fff800 0x7df8ff0003fffc00

def z1227 : W := mkw 0x1da5ff6978000000 0x8ed2ffb4bc000000 0xdd8ffffff8000000 0x6ec7fffffc000000

def z1228 : W := mkw 0x41d801d200080380 0x20ec00e9000401c0 0xd5fe01ff80000300 0x6aff00ffc0000180

def z1229 : W := mkw 0x1dfdefdb38000000 0x8efef7ed9c000000 0x107e0e1f80000000 0x083f070fc0000000

def z1230 : W := mkw 0x3dfdfffb7e050284 0x9efefffdbf028142 0xfffffffffc06071f 0xfffffffffe03038f

def z1231 : W := mkw 0x41ca000487e807c0 0x20e5000243f403e0 0x6170000007f807e0 0x30b8000003fc03f0

def z1232 : W := mkw 0x28001160500042b4 0x140008b02800215a 0xef81f1e07f07c7ff 0xf7c0f8f03f83e3ff

def z1233 : W := mkw 0x1c7cbebb78000000 0x8e3e5f5dbc000000 0x107e0e1ff8000000 0x083f070ffc000000

def z1234 : W := mkw 0x0222880481d2fc78 0x0111440240e97e3c 0xfb718e0007fffcf9 0x7db8c70003fffe7c

def z1235 : W := mkw 0x0002000481c04470 0x0001000240e02238 0x2200000003c1c4f9 0x1100000001e0e27c

def z1236 : W := mkw 0x405a01d681e807c0 0x202d00eb40f403e0 0xb4fe01ff83f807e0 0x5a7f00ffc1fc03f0

def z1237 : W := mkw 0x6fcf7563d7a5d2f4 0x37e7bab1ebd2e97a 0x008e70638301c0e0 0x00473831c180e070

def z1238 : W := mkw 0x967eae9da9fabd4a 0x4b3f574ed4fd5ea5 0x107e0e1f80f83800 0x083f070fc07c1c00

def z1239 : W := mkw 0x07dc37fb6000d838 0x03ee1bfdb0006c1c 0xdffe7fffe001f819 0x6fff3ffff000fc0c

def z1240 : W := mkw 0x15fcafdb28000000 0x8afe57ed94000000 0x517e0f9f80000000 0x28bf07cfc0000000

def z1241 : W := mkw 0x2d9577fb7e0542b4 0x96cabbfdbf02a15a 0xff8fffffff07c7ff 0xffc7ffffff83e3ff

def z1242 : W := mkw 0x9dfdfffb7e372000 0xcefefffdbf1b9000 0xfffffffffcfe3800 0x7ffffffffe7f1c00

def z1243 : W := mkw 0xd1efed4207b7b280 0x68f7f6a103dbd940 0xfbfffe0007fff800 0x7dffff0003fffc00

def z1244 : W := mkw 0x91f9c9d206372000 0x48fce4e9031b9000 0xd5ff81ff843e0000 0x6affc0ffc21f0000

def z1245 : W := mkw 0x467eae9fa9fabd4a 0x233f574fd4fd5ea5 0x107e0e1f80f83800 0x083f070fc07c1c00

def z1246 : W := mkw 0xc1da01d687ed97c0 0x60ed00eb43f6cbe0 0xf5fe01ff87f9c7e0 0x7aff00ffc3fce3f0

def z1247 : W := mkw 0x41ca014687e807c0 0x20e500a343f403e0 0x2000000007f807e0 0x1000000003fc03f0

def z1248 : W := mkw 0x15cd762960000000 0x0ae6bb14b0000000 0x9c8e7e7fe0000000 0x4e473f3ff0000000

def z1249 : W := mkw 0x15edee0920000000 0x0af6f70490000000 0xd9fffe1f80000000 0x6cffff0fc0000000

def z1250 : W := mkw 0x0404362960000000 0x02021b14b0000000 0xff8ffffffc06071f 0xffc7fffffe03038f

def z1251 : W := mkw 0x0026ac000192b000 0x0013560000c95800 0xbafe7e0003f9f800 0x5d7f3f0001fcfc00

def z1252 : W := mkw 0x1ffdfffb78009808 0x8ffefffdbc004c04 0xddfffffff8003800 0x6efffffffc001c00

def z1253 : W := mkw 0x147cae9b2812280a 0x8a3e574d94091405 0x1a7f8e1ff806381f 0x8d3fc70ffc031c0f

def z1254 : W := mkw 0x19fdedd218000000 0x8cfef6e90c000000 0xddffffff98000000 0x6effffffcc000000

def z1255 : W := mkw 0x3dcd776b760542b4 0x9ee6bbb5bb02a15a 0xbe8e7e7fe301c4f9 0x5f473f3ff180e27c

def z1256 : W := mkw 0x405a01d681e807c0 0x202d00eb40f403e0 0xf57e01ff84f807e0 0x7abf00ffc27c03f0

def z1257 : W := mkw 0x2e06362df1c0dc7c 0x17031b16f8e06e3e 0xbe8e7e7ffbc1fcff 0xdf473f3ffde0fe7f

def z1258 : W := mkw 0x9624be296012f838 0x4b125f14b0097c1c 0x0a007e006001f819 0x05003f003000fc0c

def z1259 : W := mkw 0x91a5ec000617b000 0x48d2f600030bd800 0xfbf1fe0007fff800 0x7df8ff0003fffc00

def z1260 : W := mkw 0xc183414487ffb7c0 0x60c1a0a243ffdbe0 0xef81f1e007ffffe0 0x77c0f8f003fffff0

def z1261 : W := mkw 0x0058009200000000 0x002c004900000000 0xd57e019f80000000 0x6abf00cfc0000000

def z1262 : W := mkw 0x144c362b60000000 0x8a261b15b0000000 0x9c8e7e7fe0000000 0x4e473f3ff0000000

def z1263 : W := mkw 0x01ebc80007b72000 0x00f5e40003db9000 0xfbfffe0007fff800 0x7dffff0003fffc00

def z1264 : W := mkw 0x0202000481c09c48 0x0101000240e04e24 0x2200000003c1f800 0x1100000001e0fc00

def z1265 : W := mkw 0x147cae9b28000000 0x8a3e574d94000000 0x9c7e0e1fe0000000 0x4e3f070ff0000000

def z1266 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0x9c8e7e7fe3c1f8e0 0x4e473f3ff1e0fc70

def z1267 : W := mkw 0x05dc37fb660042b0 0x02ee1bfdb3002158 0xfffe7fffe701c7f9 0x7fff3ffff380e3fc

def z1268 : W := mkw 0x69835164d7ed47f4 0x34c1a8b26bf6a3fa 0x2080706007f9c7e0 0x1040383003fce3f0

def z1269 : W := mkw 0x147cae9b28000000 0x8a3e574d94000000 0x517f8f9f98000000 0x28bfc7cfcc000000

def z1270 : W := mkw 0x11edec0006172000 0x08f6f600030b9000 0xfbfffe0007fff800 0x7dffff0003fffc00

def z1271 : W := mkw 0x1ddd77fb78000000 0x8eeebbfdbc000000 0xd5fe71fff8000000 0x6aff38fffc000000

def z1272 : W := mkw 0x41db41d687e807c0 0x20eda0eb43f403e0 0xfdfff1ff87f807e0 0x7efff8ffc3fc03f0

def z1273 : W := mkw 0x06063629e180d070 0x03031b14f0c06838 0xbe8e7e7fe3c1f8e0 0x5f473f3ff1e0fc70

def z1274 : W := mkw 0x906fec0001b7b000 0x4837f60000dbd800 0xfb7ffe0004fff800 0x7dbfff00027ffc00

def z1275 : W := mkw 0x0404260920000000 0x0202130490000000 0x988e7e1f80000000 0x4c473f0fc0000000

def z1276 : W := mkw 0x1dfdfffb78122000 0x8efefffdbc091000 0xfffffffffcfe3f1f 0xfffffffffe7f1f8f

def z1277 : W := mkw 0x5dfdfffb7e200280 0xaefefffdbf100140 0xddfffffff8000000 0x6efffffffc000000

def z1278 : W := mkw 0x0206240481c0dc78 0x0103120240e06e3c 0x2a007e0003c1fcf9 0x15003f0001e0fe7c

def z1279 : W := mkw 0x147cae9b281a2102 0x8a3e574d940d1081 0x107e0e1f80380000 0x083f070fc01c0000

def z1280 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0xfbfffe0007ffff1f 0xfdffff0003ffff8f

def z1281 : W := mkw 0x1c7cbffb78000000 0x8e3e5ffdbc000000 0x107e0e7f80000000 0x083f073fc0000000

def z1282 : W := mkw 0x3ddd75f3560542b4 0x9eeebaf9ab02a15a 0xfffff1ffff07c7ff 0xfffff8ffff83e3ff

def z1283 : W := mkw 0x40021024c7e847f0 0x2001081263f423f8 0xae80706067f9c7f9 0x5740383033fce3fc

def z1284 : W := mkw 0x1dfdfffb78000280 0x8efefffdbc000140 0xddfffffff80007e0 0x6efffffffc0003f0

def z1285 : W := mkw 0x9dfdfffb7e250000 0xcefefffdbf128000 0xddfffffff8000000 0x6efffffffc000000

def z1286 : W := mkw 0x3c25fe297817683e 0x9e12ff14bc0bb41f 0x0a01fe007807f81f 0x8500ff003c03fc0f

def z1287 : W := mkw 0x2f87776df7c5defc 0x17c3bbb6fbe2ef7e 0xef81ffe07fc7ffff 0xf7c0fff03fe3ffff

def z1288 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xfffffffff8000419 0x7ffffffffc00020c

def z1289 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xe5f001e007f807e0 0x72f800f003fc03f0

def z1290 : W := mkw 0x3ffdfffb7805d83c 0x9ffefffdbc02ec1e 0xdffffffff807f81f 0xeffffffffc03fc0f

def z1291 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0xfbfffe007ffff81f 0xfdffff003ffffc0f

def z1292 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0x4581f1e07f07c7ff 0xa2c0f8f03f83e3ff

def z1293 : W := mkw 0x39f9c9d21e050284 0x9cfce4e90f028142 0xf5ff81ff9f0607e6 0xfaffc0ffcf8303f3

def z1294 : W := mkw 0x69d951f2562d0384 0x34eca8f92b1681c2 0xddfff1fffc3e0306 0xeefff8fffe1f0183

def z1295 : W := mkw 0x3dfdfffb7e0042b4 0x9efefffdbf00215a 0xfdffffffff0007ff 0xfeffffffff8003ff

def z1296 : W := mkw 0x0404362960000000 0x02021b14b0000000 0xdd8ffffff8000000 0x6ec7fffffc000000

def z1297 : W := mkw 0x0df89bfb78000000 0x86fc4dfdbc000000 0xddff8ffff8000000 0x6effc7fffc000000

def z1298 : W := mkw 0x0202000481c0dc78 0x0101000240e06e3c 0x0200000000c1f819 0x010000000060fc0c

def z1299 : W := mkw 0x39c95162560542b4 0x9ce4a8b12b02a15a 0xef81f1e07f07c7ff 0xf7c0f8f03f83e3ff

def z1300 : W := mkw 0x9025ec000017b000 0x4812f600000bd800 0x1a71fe0000fff800 0x0d38ff00007ffc00

def z1301 : W := mkw 0x2c1437fb780042b4 0x960a1bfdbc00215a 0xbe8e7ffffb01c7ff 0xdf473ffffd80e3ff

def z1302 : W := mkw 0x01da01d681c80540 0x00ed00eb40e402a0 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z1303 : W := mkw 0x947dee9b2817b000 0xca3ef74d940bd800 0x1a7ffe1f8007f800 0x0d3fff0fc003fc00

def z1304 : W := mkw 0x91efec0001b7b000 0x48f7f60000dbd800 0xdbfffe0000fff800 0x6dffff00007ffc00

def z1305 : W := mkw 0xbdfdfffb7817f034 0xdefefffdbc0bf81a 0xdffffffff807f81f 0xeffffffffc03fc0f

def z1306 : W := mkw 0x01f889d2081a2102 0x00fc44e9040d1081 0xd5ff81ff9c3e0306 0xeaffc0ffce1f0183

def z1307 : W := mkw 0x1ffdfffb7800d030 0x8ffefffdbc006818 0xddfffffff801c000 0x6efffffffc00e000

def z1308 : W := mkw 0xbdfdfffb7e17f2b4 0xdefefffdbf0bf95a 0xffffffffff07ffff 0xffffffffff83ffff

def z1309 : W := mkw 0x91efec0007b7b280 0x48f7f60003dbd940 0xfbfffe0007ffffe0 0x7dffff0003fffff0

def z1310 : W := mkw 0x91efed4007b7b280 0x48f7f6a003dbd940 0xfbffff8007fffb00 0x7dffffc003fffd80

def z1311 : W := mkw 0xc002000487ed97c0 0x6001000243f6cbe0 0x2000000007f9c7e0 0x1000000003fce3f0

def z1312 : W := mkw 0x001001d200000000 0x000800e900000000 0x948e01ff80000000 0x4a4700ffc0000000

def z1313 : W := mkw 0x01d801d200000000 0x00ec00e900000000 0xf5fe01ff84000700 0x7aff00ffc2000380

def z1314 : W := mkw 0x49db41d697e807c0 0x24eda0eb4bf403e0 0xf5ff81ff9ff807e0 0x7affc0ffcffc03f0

def z1315 : W := mkw 0x1dfdfffb781a290a 0x8efefffdbc0d1485 0xdffffffffc3e3b1f 0xeffffffffe1f1d8f

def z1316 : W := mkw 0x1dcd756350000000 0x8ee6bab1a8000000 0x948e707f80000000 0x4a47383fc0000000

def z1317 : W := mkw 0x01f88bda2812280a 0x00fc45ed14091405 0xdfff8ffff806381f 0xefffc7fffc031c0f

def z1318 : W := mkw 0x59fbc9d69fe807c0 0xacfde4eb4ff403e0 0x617181801ff807e0 0x30b8c0c00ffc03f0

def z1319 : W := mkw 0x1dfdfdf350000000 0x8efefef9a8000000 0xddffffff80000000 0x6effffffc0000000

def z1320 : W := mkw 0x1dfdfffb781a2102 0x8efefffdbc0d1081 0xddfffffff8380000 0x6efffffffc1c0000

def z1321 : W := mkw 0x0585762966050000 0x02c2bb14b3028000 0xff8ffe7fe707c000 0x7fc7ff3ff383e000

def z1322 : W := mkw 0x2b83414497c5defc 0x15c1a0a24be2ef7e 0x630181801fc7ffff 0xb180c0c00fe3ffff

def z1323 : W := mkw 0x0dd953fb78000000 0x86eca9fdbc000000 0xddfff1fff8000000 0x6efff8fffc000000

def z1324 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0x30fe007f87f807e0 0x187f003fc3fc03f0

def z1325 : W := mkw 0xb1efec0007b7b284 0x58f7f60003dbd942 0xfbfffe0007fffb06 0xfdffff0003fffd83

def z1326 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xfdff81fffff807e0 0x7effc0fffffc03f0

def z1327 : W := mkw 0x4002000487e80fca 0x2001000243f407e5 0x2000000007f807ff 0x9000000003fc03ff

def z1328 : W := mkw 0x2202000487c5defc 0x1101000243e2ef7e 0x2200000003c1fcf9 0x1100000001e0fe7c

def z1329 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0x1afffe0003fff800 0x0d7fff0001fffc00

def z1330 : W := mkw 0x2e07762df7c5defc 0x1703bb16fbe2ef7e 0x2a01fe007fc7ffff 0x9500ff003fe3ffff

def z1331 : W := mkw 0x1c7cafdb38000000 0x8e3e57ed9c000000 0x107e0f9f98000000 0x083f07cfcc000000

def z1332 : W := mkw 0x0202000487c0def8 0x0101000243e06f7c 0x2200000007c1fff9 0x1100000003e0fffc

def z1333 : W := mkw 0x1ddd75f350000000 0x8eeebaf9a8000000 0x048e71ff80000000 0x024738ffc0000000

def z1334 : W := mkw 0x3da5ff697e0542b4 0x9ed2ffb4bf02a15a 0xff8fffffff07c7ff 0xffc7ffffff83e3ff

def z1335 : W := mkw 0x146cbe2960000000 0x0a365f14b0000000 0x9cfe7e7fe0000000 0x4e7f3f3ff0000000

def z1336 : W := mkw 0x1dfdfffb78122000 0x8efefffdbc091000 0xddfffffffc3e0000 0x6efffffffe1f0000

def z1337 : W := mkw 0x4002000481fa2d4a 0x2001000240fd16a5 0x2200000004fe3f1f 0x91000000027f1f8f

def z1338 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0xfff18ffc7ffe3fff 0xfff8c7fe3fff1fff

def z1339 : W := mkw 0x91eeac0007b2b000 0x48f7560003d95800 0xfbfe7e0007f9f800 0x7dff3f0003fcfc00

def z1340 : W := mkw 0xe9835164d7fff7f4 0x74c1a8b26bfffbfa 0xef81f1e07fffffff 0xf7c0f8f03fffffff

def z1341 : W := mkw 0x0414269b28000000 0x820a134d94000000 0x100e0e1f80000000 0x0807070fc0000000

def z1342 : W := mkw 0x9dfdfffb7e37b000 0xcefefffdbf1bd800 0xdffffffffc3ff800 0x6ffffffffe1ffc00

def z1343 : W := mkw 0x4202000481c8dff8 0x2101000240e46ffc 0x2200000003c1fff9 0x1100000001e0fffc

def z1344 : W := mkw 0xb9efed4017b7b284 0x5cf7f6a00bdbd942 0xfbfffe0007fff800 0x7dffff0003fffc00

def z1345 : W := mkw 0x15fdee9b28000000 0x8afef74d94000000 0x517f8e1f80000000 0x28bfc70fc0000000

def z1346 : W := mkw 0x4182014487e807c0 0x20c100a243f403e0 0x6100018007f807e0 0x308000c003fc03f0

def z1347 : W := mkw 0x0383400487c5dc78 0x01c1a00243e2ee3c 0xeb81f00007c7fcf9 0x75c0f80003e3fe7c

def z1348 : W := mkw 0x4002014487e807c0 0x200100a243f403e0 0x240001e007f807e0 0x120000f003fc03f0

def z1349 : W := mkw 0x0db5fff978000000 0x06dafffcbc000000 0xddfffffff8000000 0x6efffffffc000000

def z1350 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xf5fe01fffff807ff 0xfaff00fffffc03ff

def z1351 : W := mkw 0x3dfdfffb7e1f63b6 0x9efefffdbf0fb1db 0xffffffffff3fc7ff 0xffffffffff9fe3ff

def z1352 : W := mkw 0x2e25fe297817f83e 0x1712ff14bc0bfc1f 0x0a01fe007807f81f 0x8500ff003c03fc0f

def z1353 : W := mkw 0x906fec0001b7b000 0x4837f60000dbd800 0x107e7e0000f9f800 0x083f3f00007cfc00

def z1354 : W := mkw 0x29815160560542b4 0x14c0a8b02b02a15a 0x0e81f1e07b07c7ff 0x8740f8f03d83e3ff

def z1355 : W := mkw 0x0604260920009808 0x0302130490004c04 0x100e0e1f80003800 0x0807070fc0001c00

def z1356 : W := mkw 0x9dfdfffb7812b000 0xcefefffdbc095800 0xddfffffff8003800 0x6efffffffc001c00

def z1357 : W := mkw 0x4202000487fafffa 0x2101000243fd7ffd 0x2200000007ffffff 0x9100000003ffffff

def z1358 : W := mkw 0x0626be2de9dafd7a 0x03135f16f4ed7ebd 0x2a01fe007fffffff 0x9500ff003fffffff

def z1359 : W := mkw 0x1c05762970000000 0x8e02bb14b8000000 0x9c8e7e7fe0000000 0x4e473f3ff0000000

def z1360 : W := mkw 0x45dc37fb66280380 0x22ee1bfdb31401c0 0xddfe7fffe4380300 0x6eff3ffff21c0180

def z1361 : W := mkw 0xd1fdedd2063f2380 0x68fef6e9031f91c0 0xddffffff843e0300 0x6effffffc21f0180

def z1362 : W := mkw 0x1dfdfffb7812280a 0x8efefffdbc091405 0xfffffffffc063f1f 0xfffffffffe031f8f

def z1363 : W := mkw 0x0202000481c0dc78 0x0101000240e06e3c 0x000000000301c4f9 0x000000000180e27c

def z1364 : W := mkw 0x1dfcbffb78000000 0x8efe5ffdbc000000 0xd5fe0ffff8000000 0x6aff07fffc000000

def z1365 : W := mkw 0x1dfdfffb78000808 0x8efefffdbc000404 0xdffffffff8003819 0x6ffffffffc001c0c

def z1366 : W := mkw 0x0c34bffb78000000 0x861a5ffdbc000000 0xddfffffff8000000 0x6efffffffc000000

def z1367 : W := mkw 0x0202000481c0dc78 0x0101000240e06e3c 0xae00000063c1fcf9 0x5700000031e0fe7c

def z1368 : W := mkw 0x1078889208000000 0x883c444904000000 0x107e001f80000000 0x083f000fc0000000

def z1369 : W := mkw 0xd1fbc9d687ffb7c0 0x68fde4eb43ffdbe0 0x6371818007ffffe0 0x31b8c0c003fffff0

def z1370 : W := mkw 0x3dfdefdb3e050284 0x9efef7ed9f028142 0x517f8f9f9c060306 0xa8bfc7cfce030183

def z1371 : W := mkw 0x9627fe2de7f7fc78 0x4b13ff16f3fbfe3c 0x2a01fe0067fffcf9 0x1500ff0033fffe7c

def z1372 : W := mkw 0x1dfdfffb7e050000 0x8efefffdbf028000 0xddfffffffc060000 0x6efffffffe030000

def z1373 : W := mkw 0x15edfe2966054030 0x0af6ff14b302a018 0xfffffe7fe707c4f9 0x7fffff3ff383e27c

def z1374 : W := mkw 0x0202000481d2fc78 0x0101000240e97e3c 0x2200000007fffcf9 0x1100000003fffe7c

def z1375 : W := mkw 0x3ddd77fb7e0542b4 0x9eeebbfdbf02a15a 0xef8ff1ffff07c7ff 0xf7c7f8ffff83e3ff

def z1376 : W := mkw 0x3c7dfebb78054034 0x9e3eff5dbc02a01a 0x1a7ffe1ff807c01f 0x8d3fff0ffc03e00f

def z1377 : W := mkw 0x91efed4007b7b280 0x48f7f6a003dbd940 0xffffffe07fffffff 0xfffffff03fffffff

def z1378 : W := mkw 0x0020880000122000 0x0010440000091000 0xfbf1fe0007fff800 0x7df8ff0003fffc00

def z1379 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0x5b718f9c7cfe3b1f 0xadb8c7ce3e7f1d8f

def z1380 : W := mkw 0x41db41d687ed07c0 0x20eda0eb43f683e0 0xf5ff81ff87fe07e0 0x7affc0ffc3ff03f0

def z1381 : W := mkw 0x0606260da1c0dc78 0x03031306d0e06e3c 0x22000e0003c1fcf9 0x1100070001e0fe7c

def z1382 : W := mkw 0x0002000487c006c0 0x0001000243e00360 0x2000000007c007e0 0x1000000003e003f0

def z1383 : W := mkw 0x04308a9f285a2d0a 0x8218454f942d1685 0xff718f9ffcfe3f1f 0xffb8c7cffe7f1f8f

def z1384 : W := mkw 0x21814000060542b4 0x10c0a0000302a15a 0xef81f1807f07c7ff 0xf7c0f8c03f83e3ff

def z1385 : W := mkw 0x2f8577697005d83c 0x17c2bbb4b802ec1e 0xdf8ffffff807f81f 0xefc7fffffc03fc0f

def z1386 : W := mkw 0x0434beb968004030 0x021a5f5cb4002018 0xffffffffff07c7ff 0xffffffffff83e3ff

def z1387 : W := mkw 0x0c1437fb78000000 0x860a1bfdbc000000 0x048e71fff8000000 0x024738fffc000000

def z1388 : W := mkw 0x0424be2960000000 0x02125f14b0000000 0xddfffe7fe0000000 0x6effff3ff0000000

def z1389 : W := mkw 0x0981516050004030 0x04c0a8b028002018 0xef81f1e07f07c7ff 0xf7c0f8f03f83e3ff

def z1390 : W := mkw 0x01da01d687e00440 0x00ed00eb43f00220 0xf5fe01ff87f804e0 0x7aff00ffc3fc0270

def z1391 : W := mkw 0x0404362960000000 0x02021b14b0000000 0x180e7e1fe0000000 0x0c073f0ff0000000

def z1392 : W := mkw 0x0424be2960122000 0x02125f14b0091000 0xfffffe7fe4fe3800 0x7fffff3ff27f1c00

def z1393 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0xffffff8007ffff00 0x7fffffc003ffff80

def z1394 : W := mkw 0x11fdec9200000000 0x08fef64900000000 0xd9fffe1f80000000 0x6cffff0fc0000000

def z1395 : W := mkw 0x3dfdfffb7e054034 0x9efefffdbf02a01a 0xffffffffff07c01f 0xffffffffff83e00f

def z1396 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0xff8ffe7fe7c7fcf9 0x7fc7ff3ff3e3fe7c

def z1397 : W := mkw 0x0dd813fb78000000 0x86ec09fdbc000000 0x048e01fff8000000 0x024700fffc000000

def z1398 : W := mkw 0x8202000481f2bc48 0x4101000240f95e24 0x0000000000f83800 0x00000000007c1c00

def z1399 : W := mkw 0xd07eae9ea9fabd4a 0x683f574f54fd5ea5 0x107e0e1f80f83800 0x083f070fc07c1c00

def z1400 : W := mkw 0x9dfdfffb7817b80a 0xcefefffdbc0bdc05 0xdffffffff807f81f 0xeffffffffc03fc0f

def z1401 : W := mkw 0x3dfdfffb780042b4 0x9efefffdbc00215a 0xfffffffffc0607ff 0xfffffffffe0303ff

def z1402 : W := mkw 0x4012009487e807c0 0x2009004a43f403e0 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z1403 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0xffffff807ffff800 0x7fffffc03ffffc00

def z1404 : W := mkw 0x0202000481c0dc78 0x0101000240e06e3c 0xef0181807fc7ffff 0xf780c0c03fe3ffff

def z1405 : W := mkw 0x41da01d68fe807c2 0x20ed00eb47f403e1 0xf5fe01ff9ff807e6 0xfaff00ffcffc03f3

def z1406 : W := mkw 0x147cae9b28122000 0x8a3e574d94091000 0xfb7f8e1f84fe3800 0x7dbfc70fc27f1c00

def z1407 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0x55718f9c7cfe3f1f 0xaab8c7ce3e7f1f8f

def z1408 : W := mkw 0x1dcd776b70000000 0x8ee6bbb5b8000000 0x108e7e7f80000000 0x08473f3fc0000000

def z1409 : W := mkw 0x9ffdfffb7817f838 0xcffefffdbc0bfc1c 0xdffffffff807f819 0x6ffffffffc03fc0c

def z1410 : W := mkw 0x11f9c9d200000000 0x08fce4e900000000 0xd5ff81ff80000000 0x6affc0ffc0000000

def z1411 : W := mkw 0x01d801d200080100 0x00ec00e900040080 0xd5fe01ff84380300 0x6aff00ffc21c0180

def z1412 : W := mkw 0x09d801d218000000 0x84ec00e90c000000 0xd5fe01ff98000000 0x6aff00ffcc000000

def z1413 : W := mkw 0x0424be2968000000 0x02125f14b4000000 0x9c8ffe7ff8000000 0x4e47ff3ffc000000

def z1414 : W := mkw 0x19f9d9f258000000 0x8cfcecf92c000000 0xddfff1fff8000000 0x6efff8fffc000000

def z1415 : W := mkw 0x0c1013fb78000000 0x860809fdbc000000 0x948e01fff8000000 0x4a4700fffc000000

def z1416 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0xba8e7e7f83c1f8e0 0x5d473f3fc1e0fc70

def z1417 : W := mkw 0x405a01d687e807c0 0x202d00eb43f403e0 0x347e01ff87f807e0 0x1a3f00ffc3fc03f0

def z1418 : W := mkw 0x7dfdfffb7e2d43b4 0xbefefffdbf16a1da 0xffffffffff3fc7ff 0xffffffffff9fe3ff

def z1419 : W := mkw 0x1c5c37fb78000000 0x8e2e1bfdbc000000 0x040e01fff8000000 0x020700fffc000000

def z1420 : W := mkw 0x06063425c1c0dc78 0x03031a12e0e06e3c 0x2200700003c1fcf9 0x1100380001e0fe7c

def z1421 : W := mkw 0x4182014487e807c0 0x20c100a243f403e0 0x2080006007f807e0 0x1040003003fc03f0

def z1422 : W := mkw 0x1dfdfffb78004030 0x8efefffdbc002018 0xffffffffff07c7ff 0xffffffffff83e3ff

def z1423 : W := mkw 0x147cae9b28000000 0x8a3e574d94000000 0x98fe7e1f80000000 0x4c7f3f0fc0000000

def z1424 : W := mkw 0x1dfdfffb781a2102 0x8efefffdbc0d1081 0xfffffffffcfe3b06 0xfffffffffe7f1d83

def z1425 : W := mkw 0x0c04376970000000 0x06021bb4b8000000 0x9c8e7ffff8000000 0x4e473ffffc000000

def z1426 : W := mkw 0x2dd953fb7e0542b4 0x96eca9fdbf02a15a 0xfffff1ffff07c7ff 0xfffff8ffff83e3ff

def z1427 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0xfffe71ff87f9c7e0 0x7fff38ffc3fce3f0

def z1428 : W := mkw 0x1dfdfffb78004030 0x8efefffdbc002018 0xdffffffff801c019 0x6ffffffffc00e00c

def z1429 : W := mkw 0x97edfe296017f838 0x4bf6ff14b00bfc1c 0xdffffe7fe007f819 0x6fffff3ff003fc0c

def z1430 : W := mkw 0x3dfdfffb780042b4 0x9efefffdbc00215a 0xfffffffffb01c7ff 0xfffffffffd80e3ff

def z1431 : W := mkw 0x01ca014487e006c0 0x00e500a243f00360 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z1432 : W := mkw 0x55fcafdb2e280380 0xaafe57ed971401c0 0x517e0f9f84380300 0x28bf07cfc21c0180

def z1433 : W := mkw 0x01d801d200000000 0x00ec00e900000000 0xffff81fffc06071f 0xffffc0fffe03038f

def z1434 : W := mkw 0x4002000487fa2fca 0x2001000243fd17e5 0x2000000007f83fe0 0x1000000003fc1ff0

def z1435 : W := mkw 0x4002000487e807c0 0x2001000243f403e0 0xef0181807ffe07ff 0xf780c0c03fff03ff

def z1436 : W := mkw 0x4002000487e80fc8 0x2001000243f407e4 0x2200000007f83ff9 0x1100000003fc1ffc

def z1437 : W := mkw 0x0424be296812280a 0x02125f14b4091405 0x9e8ffe7ff806381f 0xcf47ff3ffc031c0f

def z1438 : W := mkw 0x4202000487e84ff8 0x2101000243f427fc 0x2000000007f807f9 0x1000000003fc03fc

def z1439 : W := mkw 0x1dfdfffb7812280a 0x8efefffdbc091405 0xddfffffff8003800 0x6efffffffc001c00

def z1440 : W := mkw 0x0dd811f350000000 0x86ec08f9a8000000 0xd5fe01ff80000000 0x6aff00ffc0000000

def z1441 : W := mkw 0x1c7dee9b38000000 0x8e3ef74d9c000000 0x107f8e1f98000000 0x083fc70fcc000000

def z1442 : W := mkw 0x6002000487e847f4 0x3001000243f423fa 0x2000000007f807ff 0x9000000003fc03ff

def z1443 : W := mkw 0x01a7ec000797b000 0x00d3f60003cbd800 0xfbfffe0007fff800 0x7dffff0003fffc00

def z1444 : W := mkw 0x01d803da20000000 0x00ec01ed10000000 0xddfe0fffe0000000 0x6eff07fff0000000

def z1445 : W := mkw 0x91edec000017b000 0x48f6f600000bd800 0xfbfffe0004fff800 0x7dffff00027ffc00

def z1446 : W := mkw 0x1c7cbffb78000000 0x8e3e5ffdbc000000 0xdd7f8ffff8000000 0x6ebfc7fffc000000

def z1447 : W := mkw 0x405a009687e807c0 0x202d004b43f403e0 0x2070000007f807e0 0x1038000003fc03f0

def z1448 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0x18fffe7ff8000000 0x0c7fff3ffc000000

def z1449 : W := mkw 0x02021024c1c0dc78 0x0101081260e06e3c 0x2280706003c1fcf9 0x1140383001e0fe7c

def z1450 : W := mkw 0x29d951f2560542b4 0x14eca8f92b02a15a 0xd5fe71ff8301c0e0 0x6aff38ffc180e070

def z1451 : W := mkw 0x43da01d687e8dff8 0x21ed00eb43f46ffc 0x6370018007f9fff9 0x31b800c003fcfffc

def z1452 : W := mkw 0x3dfdfffb78054034 0x9efefffdbc02a01a 0xfffffffffb07c4ff 0xfffffffffd83e27f

def z1453 : W := mkw 0x9dfdfffb7e3f2102 0xcefefffdbf1f9081 0xddfffffffc3e0306 0xeefffffffe1f0183

def z1454 : W := mkw 0x9625fe296817f83a 0x4b12ff14b40bfc1d 0x0a01fe007807f81f 0x8500ff003c03fc0f

def z1455 : W := mkw 0x401201d681c807c0 0x200900eb40e403e0 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z1456 : W := mkw 0x147cae9b28000000 0x8a3e574d94000000 0x187f8e1ff8000000 0x0c3fc70ffc000000

def z1457 : W := mkw 0x8202000487e5dc78 0x4101000243f2ee3c 0x2200000003c1fcf9 0x1100000001e0fe7c

def z1458 : W := mkw 0xbdfdfffb7e372284 0xdefefffdbf1b9142 0xddfffffffc3e0306 0xeefffffffe1f0183

def z1459 : W := mkw 0x41da01d687e80fc8 0x20ed00eb43f407e4 0xf7fe01ff87f83ff9 0x7bff00ffc3fc1ffc

def z1460 : W := mkw 0x00308894005a2500 0x0018444a002d1280 0xff718f9c7cfe3f1f 0xffb8c7ce3e7f1f8f

def z1461 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0xd9fffe0003f9f800 0x6cffff0001fcfc00

def z1462 : W := mkw 0x09f9dbfa78000000 0x04fcedfd3c000000 0xddfffffff8000000 0x6efffffffc000000

def z1463 : W := mkw 0x1dfdfffb7e0042b0 0x8efefffdbf002158 0xffffffffff01c7f9 0x7fffffffff80e3fc

def z1464 : W := mkw 0x2db5fff97e0542b4 0x16dafffcbf02a15a 0xffffffffff07c7ff 0xffffffffff83e3ff

def z1465 : W := mkw 0x1dfdefdb38000000 0x8efef7ed9c000000 0xd5ff8fff98000000 0x6affc7ffcc000000

def z1466 : W := mkw 0x29d951f250054034 0x14eca8f92802a01a 0xdffff1fff807c01f 0xeffff8fffc03e00f

def z1467 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0x51fe01ff87f803e0 0x28ff00ffc3fc01f0

def z1468 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0x14fe7ffff8000000 0x0a7f3ffffc000000

def z1469 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0x5b7ffe0004fff800 0x2dbfff00027ffc00

def z1470 : W := mkw 0x4002000481e80540 0x2001000240f402a0 0x2000000004f80700 0x10000000027c0380

def z1471 : W := mkw 0x405a009681e80540 0x202d004b40f402a0 0x147e007f80f804e0 0x0a3f003fc07c0270

def z1472 : W := mkw 0x01d8009200000000 0x00ec004900000000 0xd1fe001f80000000 0x68ff000fc0000000

def z1473 : W := mkw 0x906eac0001b2b000 0x4837560000d95800 0xfbfffe0007fff800 0x7dffff0003fffc00

def z1474 : W := mkw 0x01d801d206200000 0x00ec00e903100000 0xd5fe01ff84380000 0x6aff00ffc21c0000

def z1475 : W := mkw 0x0458029b28000000 0x822c014d94000000 0x107e001f80000000 0x083f000fc0000000

def z1476 : W := mkw 0x147cae9b28000000 0x8a3e574d94000000 0x147e0f9ff8000000 0x0a3f07cffc000000

def z1477 : W := mkw 0x00063424c1c0d470 0x00031a1260e06a38 0xbe8e7e7fe3c1fcf9 0x5f473f3ff1e0fe7c

def z1478 : W := mkw 0x41da01d687e807c0 0x20ed00eb43f403e0 0x45fe01ff873807e0 0x22ff00ffc39c03f0

def z1479 : W := mkw 0x21d801d2060542b4 0x10ec00e90302a15a 0xf7fe01ff8707c7ff 0xfbff00ffc383e3ff

def z1480 : W := mkw 0x01d811f240000000 0x00ec08f920000000 0xddfe71ffe0000000 0x6eff38fff0000000

def z1481 : W := mkw 0x41d801d200280100 0x20ec00e900140080 0xd5fe01ff80380000 0x6aff00ffc01c0000

def z1482 : W := mkw 0xc002000487ffb540 0x6001000243ffdaa0 0x2200000007fff800 0x1100000003fffc00

def z1483 : W := mkw 0x906eac0001b2b000 0x4837560000d95800 0x1a7e7e0000f9f800 0x0d3f3f00007cfc00

def z1484 : W := mkw 0x00788a9a28000000 0x003c454d14000000 0x107e0e1f80000000 0x083f070fc0000000

def z1485 : W := mkw 0x0182014487c006c0 0x00c100a243e00360 0xe58001e007c007e0 0x72c000f003e003f0

def z1486 : W := mkw 0x00308a9c285a2d0a 0x0018454e142d1685 0xfff1ff9c7fffff1f 0xfff8ffce3fffff8f

def z1487 : W := mkw 0x41da009687e80540 0x20ed004b43f402a0 0xf5fe007f87f804e0 0x7aff003fc3fc0270

def z1488 : W := mkw 0x0202000481c04c78 0x0101000240e0263c 0x2000000003c004f9 0x1000000001e0027c

def z1489 : W := mkw 0x39f9d9f25e0542b4 0x9cfcecf92f02a15a 0xfffff1ffff07c7ff 0xfffff8ffff83e3ff

def z1490 : W := mkw 0x3dfdfffb7e0542b4 0x9efefffdbf02a15a 0xddffffffff07c3e6 0xeeffffffff83e1f3

def z1491 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xfdfffffffb0004e0 0x7efffffffd800270

def z1492 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0x1a8e7e7fe3c1f8f9 0x0d473f3ff1e0fc7c

def z1493 : W := mkw 0x11f889d208000000 0x88fc44e904000000 0xd5fe01ff80000000 0x6aff00ffc0000000

def z1494 : W := mkw 0x9dfdfffb7e372000 0xcefefffdbf1b9000 0xffffffffff3fc000 0x7fffffffff9fe000

def z1495 : W := mkw 0xd027ec0487ffb7c0 0x6813f60243ffdbe0 0x2a01fe0007ffffe0 0x1500ff0003fffff0

def z1496 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0xff8e7fffe7c1fff9 0x7fc73ffff3e0fffc

def z1497 : W := mkw 0x3dfdfffb78004034 0x9efefffdbc00201a 0xddfffffff800001f 0xeefffffffc00000f

def z1498 : W := mkw 0x3dfdfffb7e0542b4 0x9efefffdbf02a15a 0xdffffffffb07c0ff 0xeffffffffd83e07f

def z1499 : W := mkw 0x147cae9b2812280a 0x8a3e574d94091405 0x107e0e1f80003800 0x083f070fc0001c00

def z1500 : W := mkw 0x0002000481da2d4a 0x0001000240ed16a5 0x2200000007fe3fff 0x9100000003ff1fff

def z1501 : W := mkw 0x4202000481e8dd78 0x2101000240f46ebc 0x2200000003f9fcf9 0x1100000001fcfe7c

def z1502 : W := mkw 0x0202000481c09c48 0x0101000240e04e24 0x2000000003c03ce0 0x1000000001e01e70

def z1503 : W := mkw 0x41da01d687ed07c0 0x20ed00eb43f683e0 0xf7fe01ff87ffc7e0 0x7bff00ffc3ffe3f0

def z1504 : W := mkw 0x0206240481c0dc78 0x0103120240e06e3c 0xbe8e7e7f83c1fcf9 0x5f473f3fc1e0fe7c

def z1505 : W := mkw 0x144c260b20000000 0x8a26130590000000 0x100e0e1f80000000 0x0807070fc0000000

def z1506 : W := mkw 0x1dfdfffb78080100 0x8efefffdbc040080 0xddfffffffc380300 0x6efffffffe1c0180

def z1507 : W := mkw 0x0404362960000000 0x02021b14b0000000 0x048e707fe0000000 0x0247383ff0000000

def z1508 : W := mkw 0x167eae9fa9dabd4a 0x8b3f574fd4ed5ea5 0x107e0e1f80f83800 0x083f070fc07c1c00

def z1509 : W := mkw 0x3dfdfffb7e050284 0x9efefffdbf028142 0xddfffffff8000000 0x6efffffffc000000

def z1510 : W := mkw 0x0606362de9c0dc7a 0x03031b16f4e06e3d 0xbe8e7e7ffbc1fcff 0xdf473f3ffde0fe7f

def z1511 : W := mkw 0x6202000487eddffc 0x3101000243f6effe 0x2200000007ffffff 0x9100000003ffffff

def z1512 : W := mkw 0x1dfdfffb78004030 0x8efefffdbc002018 0xddfffffffb01c0e0 0x6efffffffd80e070

def z1513 : W := mkw 0x0c05762970000000 0x0602bb14b8000000 0x9c8ffe7ff8000000 0x4e47ff3ffc000000

def z1514 : W := mkw 0x0404260920000000 0x0202130490000000 0x948e0e7f80000000 0x4a47073fc0000000

def z1515 : W := mkw 0x1ddd77fb70000000 0x8eeebbfdb8000000 0xddfe7fffe0000000 0x6eff3ffff0000000

def z1516 : W := mkw 0x4058009200280100 0x202c004900140080 0x107e001f80380000 0x083f000fc01c0000

def z1517 : W := mkw 0x06063425c1c0d470 0x03031a12e0e06a38 0xbe8e7e7f83c1fce0 0x5f473f3fc1e0fe70

def z1518 : W := mkw 0x461013ffe8484ffa 0x230809fff42427fd 0x040001fff80007ff 0x820000fffc0003ff

def z1519 : W := mkw 0x4002000487e006c0 0x2001000243f00360 0x2000000003c004e0 0x1000000001e00270

def z1520 : W := mkw 0x0404362960000808 0x02021b14b0000404 0x9e8e7e7fe0003819 0x4f473f3ff0001c0c

def z1521 : W := mkw 0x4002000487e807c0 0x2001000243f403e0 0x0000000004f80300 0x00000000027c0180

def z1522 : W := mkw 0x91efec000fb7b002 0x48f7f60007dbd801 0xfbfffe001ffff806 0xfdffff000ffffc03

def z1523 : W := mkw 0x68035024d7ed47f4 0x3401a8126bf6a3fa 0x2a01f0007fffc7ff 0x9500f8003fffe3ff

def z1524 : W := mkw 0x147cafdb28000000 0x8a3e57ed94000000 0x147e0fff80000000 0x0a3f07ffc0000000

def z1525 : W := mkw 0x91efec0007b7b000 0x48f7f60003dbd800 0x51fffe0007fff800 0x28ffff0003fffc00

def z1526 : W := mkw 0x1dfdfffb78000000 0x8efefffdbc000000 0xdffffffff806001f 0xeffffffffc03000f

def z1527 : W := mkw 0x147cbebb68000000 0x8a3e5f5db4000000 0x147e0e7fe0000000 0x0a3f073ff0000000

def z1528 : W := mkw 0x4012009487e807c0 0x2009004a43f403e0 0x6170018007f807e0 0x30b800c003fc03f0

def z1529 : W := mkw 0x0002000481c00c48 0x0001000240e00624 0x2200000003c03cf9 0x1100000001e01e7c

def z1530 : W := mkw 0x15fcafdb28000000 0x8afe57ed94000000 0x10fe0e7f80000000 0x087f073fc0000000

def z1531 : W := mkw 0x49da01d69fe807c0 0xa4ed00eb4ff403e0 0xf5fe01ff9ff807e0 0x7aff00ffcffc03f0

def z1532 : W := mkw 0x060436296000d838 0x03021b14b0006c1c 0x1a0e7e1fe001f819 0x0d073f0ff000fc0c

def z1533 : W := mkw 0x1425fe2960000000 0x0a12ff14b0000000 0x9c8ffe7fe0000000 0x4e47ff3ff0000000

def z1534 : W := mkw 0x1c7dfffb78000000 0x8e3efffdbc000000 0x1c7ffffff8000000 0x0e3ffffffc000000

def z1535 : W := mkw 0x1dfdfffb7812280a 0x8efefffdbc091405 0xfffffffffcfe381f 0xfffffffffe7f1c0f

def z1536 : W := mkw 0x0606362de1c0dc78 0x03031b16f0e06e3c 0xff8ffffffbc1fcf9 0x7fc7fffffde0fe7c

def z1537 : W := mkw 0x0202000481dafd7a 0x0101000240ed7ebd 0x2200000003f9fcf9 0x1100000001fcfe7c

def z1538 : W := mkw 0x00308a9828000000 0x0018454c14000000 0xddff8ffff8000000 0x6effc7fffc000000

def z1539 : W := mkw 0xd1db41d687ed07c0 0x68eda0eb43f683e0 0xf5fe01ff87f807e0 0x7aff00ffc3fc03f0

def z1540 : W := mkw 0x41ca014687e006c0 0x20e500a343f00360 0xf5fe007f87f804e0 0x7aff003fc3fc0270

def z1541 : W := mkw 0x906eac0001b2b000 0x4837560000d95800 0x10fe7e0003f9f800 0x087f3f0001fcfc00

def z1542 : W := mkw 0x01cf640007a59000 0x00e7b20003d2c800 0xfbfffe0007fff800 0x7dffff0003fffc00

def z1543 : W := mkw 0x0604362960004838 0x03021b14b000241c 0x9c8e7e7fe0000019 0x4e473f3ff000000c

def z1544 : W := mkw 0x147cae9b28122000 0x8a3e574d94091000 0x107e0e1f80f83800 0x083f070fc07c1c00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5])],[(0,[z6,z0,z1,z7,z2,z4,z5]),(0,[z8,z0,z9,z1,z2,z4,z5]),(0,[z0,z1,z2,z10,z4,z4,z5])],[(0,[z0,z1,z7,z11,z2,z4,z5]),(0,[z0,z1,z7,z12,z2,z4,z5]),(0,[z0,z9,z1,z2,z13,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z14])],[(0,[z0,z1,z15,z7,z2,z4,z5]),(0,[z0,z16,z1,z2,z4,z5,z17])],[(0,[z0,z1,z7,z2,z4,z18,z5]),(0,[z0,z9,z1,z2,z4,z19,z5]),(0,[z0,z1,z20,z2,z21,z4,z5]),(0,[z0,z1,z7,z22,z4,z23,z5])],[(0,[z0,z1,z24,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z25,z5]),(0,[z0,z1,z2,z10,z4,z26,z5])],[(0,[z27,z0,z1,z7,z2,z4,z5]),(0,[z28,z0,z1,z29,z2,z4,z5]),(0,[z30,z0,z1,z31,z2,z4,z5]),(0,[z0,z1,z7,z2,z3,z4,z5]),(0,[z0,z1,z32,z7,z2,z4,z5])],[(0,[z0,z1,z7,z33,z2,z4,z5]),(0,[z0,z1,z2,z34,z21,z4,z5]),(0,[z0,z35,z1,z7,z2,z4,z5])],[(0,[z0,z36,z1,z37,z2,z4,z5])],[(0,[z38,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z39,z5]),(0,[z0,z1,z7,z2,z40,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z41]),(0,[z0,z1,z7,z2,z42,z4,z5]),(0,[z0,z43,z1,z44,z2,z4,z5])],[(1,[z0,z1,z45,z7,z4,z5]),(0,[z46,z0,z1,z7,z2,z47,z5])],[(0,[z0,z1,z7,z2,z4,z48,z5]),(0,[z0,z1,z49,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z50,z5]),(1,[z0,z16,z9,z2,z4,z5]),(0,[z0,z51,z1,z2,z21,z4,z5])],[(0,[z0,z36,z1,z52,z2,z4,z5]),(0,[z0,z1,z2,z53,z10,z4,z5])]],
   [[(0,[z0,z36,z1,z54,z2,z4,z5]),(0,[z55,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z5]),(0,[z0,z16,z1,z56,z2,z4,z5])],[],[(0,[z0,z9,z1,z2,z57,z4,z5])],[(0,[z0,z1,z7,z58,z2,z4,z5]),(0,[z0,z1,z29,z2,z4,z59,z5]),(0,[z0,z43,z1,z7,z2,z4,z60]),(1,[z0,z1,z2,z61,z4,z5])],[(0,[z0,z36,z1,z56,z2,z4,z5])],[(1,[z0,z62,z1,z2,z4,z5]),(0,[z0,z1,z2,z21,z63,z4,z5])],[(0,[z28,z1,z37,z7,z2,z4,z5]),(0,[z0,z1,z64,z7,z2,z4,z5]),(0,[z0,z65,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z66])],[(0,[z0,z1,z7,z2,z67,z4,z5]),(0,[z46,z0,z1,z7,z2,z22,z5]),(0,[z0,z68,z1,z7,z2,z4,z5])],[],[],[(1,[z0,z1,z7,z2,z4,z69]),(0,[z0,z1,z7,z2,z4,z70,z5]),(0,[z0,z1,z7,z2,z4,z5,z71]),(0,[z0,z1,z7,z72,z2,z4,z5]),(0,[z0,z73,z36,z1,z2,z4,z5]),(0,[z0,z74,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z61,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z75])],[(0,[z76,z30,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z60,z77]),(0,[z0,z9,z1,z2,z4,z5,z78]),(0,[z0,z1,z2,z4,z79,z80,z5]),(0,[z0,z1,z81,z7,z2,z4,z5]),(0,[z0,z1,z82,z83,z2,z4,z5])],[(0,[z0,z68,z1,z2,z10,z4,z5]),(0,[z0,z1,z2,z10,z4,z59,z5]),(0,[z0,z1,z84,z29,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z85])],[(0,[z0,z1,z2,z86,z21,z4,z5]),(0,[z8,z0,z1,z29,z2,z4,z5])],[(0,[z0,z16,z1,z87,z2,z4,z5]),(0,[z0,z1,z88,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z89,z80]),(0,[z0,z1,z2,z10,z4,z5,z90]),(0,[z0,z1,z7,z2,z4,z91,z5]),(0,[z0,z1,z7,z2,z4,z5,z92])],[(0,[z0,z1,z7,z87,z2,z4,z5])]],
   [[(0,[z0,z1,z93,z2,z21,z4,z5]),(1,[z0,z94,z1,z2,z4,z5]),(0,[z0,z1,z29,z95,z2,z4,z5]),(1,[z0,z1,z2,z4,z5,z96])],[],[(0,[z97,z1,z93,z7,z2,z4,z5]),(0,[z98,z1,z7,z99,z2,z4,z5]),(1,[z0,z1,z100,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z101,z5]),(0,[z0,z16,z1,z20,z2,z4,z5]),(0,[z0,z1,z7,z2,z102,z4,z5]),(0,[z0,z1,z7,z2,z57,z4,z17])],[(0,[z103,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z104,z5]),(0,[z0,z1,z7,z2,z105,z4,z106]),(1,[z0,z1,z107,z2,z4,z5]),(1,[z0,z1,z82,z2,z4,z5])],[(0,[z28,z0,z1,z2,z10,z4,z5]),(0,[z0,z108,z1,z7,z2,z4,z5]),(0,[z0,z1,z2,z21,z57,z4,z5]),(1,[z0,z1,z44,z2,z4,z5])],[(0,[z0,z1,z29,z2,z4,z60,z5])],[(0,[z109,z0,z1,z7,z2,z4,z5]),(0,[z0,z110,z9,z1,z2,z4,z5]),(0,[z0,z111,z1,z7,z2,z4,z80]),(0,[z0,z112,z1,z2,z21,z4,z5])],[(0,[z113,z0,z1,z37,z2,z4,z5]),(0,[z0,z1,z29,z99,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z96])],[(0,[z0,z1,z7,z2,z4,z114,z5])],[(0,[z0,z1,z7,z115,z2,z86,z4]),(0,[z0,z1,z7,z100,z2,z4,z5]),(0,[z0,z9,z1,z2,z4,z5,z116]),(0,[z0,z117,z1,z7,z2,z4,z5])],[(0,[z118,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z119,z4,z5])],[(0,[z0,z16,z1,z2,z4,z5,z120]),(1,[z0,z1,z121,z2,z4,z5])],[(0,[z30,z0,z1,z2,z21,z4,z5]),(0,[z0,z122,z9,z1,z2,z4,z5]),(0,[z0,z1,z29,z2,z123,z4,z5]),(0,[z0,z1,z2,z21,z4,z5,z78]),(0,[z0,z1,z29,z29,z2,z4,z5]),(0,[z0,z1,z124,z7,z2,z4,z5]),(0,[z0,z1,z7,z125,z2,z23,z5]),(0,[z0,z1,z7,z2,z4,z5,z120])],[(0,[z113,z0,z1,z54,z2,z4,z5]),(0,[z0,z126,z1,z7,z2,z4,z5]),(0,[z0,z1,z127,z7,z2,z4,z5]),(0,[z0,z128,z1,z7,z2,z4,z5]),(0,[z0,z1,z2,z10,z4,z60,z5]),(0,[z0,z1,z7,z2,z4,z5,z129])],[(1,[z0,z65,z1,z7,z2,z4]),(0,[z0,z130,z1,z7,z2,z4,z5])]],
   [[(0,[z131,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z29,z2,z132,z4,z5])],[(1,[z0,z1,z133,z7,z2,z4]),(1,[z0,z134,z1,z2,z4,z5]),(0,[z0,z94,z51,z1,z2,z4,z5])],[(0,[z46,z0,z1,z2,z21,z4,z5])],[(0,[z0,z1,z99,z2,z135,z4,z5]),(0,[z0,z1,z7,z121,z2,z4,z5]),(0,[z136,z0,z36,z1,z2,z4,z5])],[(0,[z0,z1,z84,z7,z2,z4,z5]),(0,[z0,z137,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z138,z5]),(0,[z0,z1,z139,z7,z2,z4,z5])],[(0,[z8,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z105,z4,z5]),(0,[z0,z1,z7,z2,z4,z140,z5]),(0,[z0,z16,z1,z125,z2,z4,z5])],[(0,[z113,z0,z36,z1,z2,z4,z5]),(0,[z0,z1,z141,z7,z2,z4,z5]),(0,[z0,z1,z2,z10,z123,z4,z5]),(0,[z0,z142,z1,z2,z21,z4,z5]),(0,[z0,z1,z7,z125,z2,z4,z5])],[(0,[z0,z16,z1,z2,z4,z143,z5]),(0,[z0,z144,z1,z7,z2,z22,z5])],[(0,[z0,z1,z7,z2,z4,z5,z145]),(0,[z146,z0,z1,z7,z2,z4,z5])],[(0,[z97,z147,z1,z7,z2,z4,z5]),(0,[z0,z148,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z149,z5]),(0,[z150,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z151]),(0,[z0,z1,z7,z2,z152,z4,z5]),(0,[z0,z16,z1,z1,z2,z4,z5]),(0,[z8,z0,z1,z2,z10,z4,z5])],[(0,[z0,z1,z7,z2,z153,z4,z5]),(1,[z0,z154,z1,z2,z4,z5])],[(0,[z155,z156,z1,z7,z2,z4,z5]),(0,[z0,z157,z1,z7,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z23,z5]),(0,[z0,z1,z7,z2,z4,z158,z5])],[(0,[z159,z0,z1,z7,z2,z4,z5]),(0,[z0,z9,z1,z2,z21,z4,z5]),(0,[z0,z1,z83,z2,z21,z4,z5])],[(0,[z0,z1,z160,z7,z2,z4,z5]),(0,[z161,z0,z1,z7,z2,z4,z5]),(1,[z0,z1,z2,z4,z162,z5])],[(0,[z8,z0,z16,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z163,z4,z5]),(0,[z46,z164,z0,z7,z2,z4,z5]),(0,[z0,z1,z95,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z165])]],
   [[(0,[z0,z16,z1,z2,z166,z4,z5]),(0,[z167,z0,z1,z2,z10,z4,z5])],[(0,[z168,z0,z1,z7,z20,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z169]),(0,[z0,z1,z7,z2,z4,z170,z5])],[(0,[z46,z0,z1,z7,z2,z123,z5]),(0,[z0,z36,z171,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z172])],[(0,[z0,z1,z7,z2,z173,z4,z5]),(0,[z0,z16,z1,z2,z4,z174,z5]),(0,[z0,z36,z1,z2,z166,z4,z5]),(0,[z0,z7,z2,z123,z4,z80,z5]),(0,[z0,z1,z95,z2,z10,z4,z5])],[(0,[z167,z0,z16,z1,z2,z4,z5]),(0,[z0,z1,z29,z7,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z4,z5]),(0,[z0,z1,z7,z2,z4,z162,z5])],[(0,[z0,z1,z175,z37,z2,z4,z5])],[(0,[z0,z1,z7,z20,z2,z4,z176]),(0,[z0,z1,z7,z2,z4,z5,z17])],[(0,[z0,z16,z1,z37,z2,z4,z5]),(0,[z155,z1,z7,z2,z4,z177,z5]),(0,[z0,z1,z178,z2,z166,z4,z5]),(0,[z0,z36,z1,z179,z2,z4,z5])],[(0,[z0,z180,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z83,z4,z60,z5])],[(0,[z0,z1,z7,z2,z181,z4,z5]),(0,[z0,z1,z7,z2,z4,z182,z5]),(0,[z0,z1,z29,z2,z10,z4,z5]),(1,[z0,z1,z7,z125,z22,z5])],[(0,[z0,z1,z183,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z184,z5]),(0,[z0,z1,z29,z2,z4,z185,z5]),(0,[z0,z36,z1,z186,z2,z4,z5]),(1,[z0,z1,z2,z187,z4,z5]),(0,[z0,z1,z7,z2,z57,z22,z5])],[(0,[z0,z9,z7,z87,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z188]),(1,[z46,z0,z7,z2,z80,z5]),(0,[z0,z1,z2,z4,z59,z5,z189])],[(0,[z190,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z175,z54,z2,z4,z5])],[(0,[z0,z1,z7,z191,z2,z4,z5]),(0,[z192,z0,z1,z7,z2,z4,z5]),(0,[z0,z193,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z194,z4,z5])],[(0,[z0,z16,z1,z54,z2,z4,z5]),(0,[z0,z1,z195,z7,z2,z4,z5]),(1,[z0,z1,z196,z2,z4,z5]),(0,[z0,z36,z68,z1,z2,z4,z5]),(0,[z0,z1,z2,z21,z21,z4,z5]),(0,[z0,z1,z7,z52,z2,z4,z5]),(0,[z197,z0,z1,z7,z2,z4,z5])]],
   [[(0,[z147,z0,z1,z198,z2,z4,z5]),(0,[z0,z1,z7,z2,z199,z4,z5]),(0,[z0,z36,z1,z175,z2,z4,z5]),(0,[z0,z1,z200,z7,z2,z4,z5]),(0,[z0,z201,z1,z7,z2,z4,z5])],[(0,[z0,z202,z1,z7,z2,z4,z5]),(0,[z203,z0,z1,z7,z2,z4,z5]),(1,[z0,z1,z175,z2,z4,z158])],[(0,[z204,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z205,z4,z5]),(0,[z0,z144,z1,z2,z21,z4,z5]),(0,[z0,z1,z95,z7,z2,z10,z5]),(0,[z0,z1,z7,z2,z187,z4,z5]),(0,[z0,z1,z7,z2,z4,z206,z5])],[(0,[z0,z1,z207,z7,z2,z4,z5]),(0,[z156,z0,z1,z7,z2,z4,z77]),(0,[z0,z1,z7,z208,z2,z4,z5]),(1,[z0,z1,z29,z186,z4,z5])],[(0,[z164,z0,z1,z7,z2,z4,z60]),(0,[z164,z0,z112,z1,z7,z2,z4]),(0,[z0,z1,z7,z2,z4,z5,z209])],[(0,[z0,z1,z7,z2,z4,z106,z5]),(0,[z0,z16,z1,z2,z4,z210,z5]),(0,[z0,z211,z1,z7,z2,z4,z5])],[(0,[z0,z1,z179,z7,z21,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z212])],[(1,[z0,z213,z1,z2,z4,z5]),(0,[z190,z0,z16,z1,z2,z4,z5]),(0,[z0,z1,z7,z83,z2,z4,z120])],[(1,[z0,z1,z214,z2,z4,z5])],[(0,[z0,z1,z7,z215,z2,z4,z5])],[(0,[z0,z110,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z216]),(0,[z0,z217,z1,z7,z2,z4,z5]),(0,[z46,z0,z1,z7,z2,z80,z5]),(0,[z0,z1,z218,z7,z2,z4,z5])],[(0,[z0,z36,z36,z1,z2,z4,z5])],[(0,[z0,z219,z1,z29,z2,z4,z5]),(1,[z30,z1,z7,z2,z105,z5]),(0,[z0,z9,z1,z2,z105,z4,z5]),(0,[z1,z7,z2,z4,z177,z5,z77]),(0,[z220,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z214,z20,z2,z4,z5])],[(0,[z0,z221,z1,z7,z2,z4,z5]),(0,[z222,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z223,z5]),(0,[z0,z1,z2,z4,z158,z5,z78]),(0,[z0,z224,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z225,z5])],[(0,[z0,z1,z7,z2,z4,z5,z226])]],
   [[(0,[z155,z0,z1,z2,z21,z4,z5]),(0,[z203,z0,z9,z1,z2,z4,z5]),(0,[z0,z1,z227,z7,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z59,z5]),(0,[z0,z1,z7,z2,z4,z5,z228])],[(0,[z76,z0,z229,z1,z7,z2,z5]),(0,[z0,z9,z1,z83,z2,z4,z5]),(0,[z0,z122,z1,z7,z2,z4,z5]),(0,[z0,z1,z230,z7,z2,z4,z5]),(0,[z0,z36,z1,z124,z2,z4,z5]),(0,[z0,z231,z1,z7,z2,z4,z5])],[(0,[z1,z37,z7,z54,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z5,z90]),(0,[z0,z74,z1,z2,z10,z4,z5])],[],[(0,[z0,z51,z7,z20,z2,z4,z5]),(0,[z0,z1,z7,z2,z232,z4,z5]),(1,[z0,z1,z2,z233,z4,z5]),(0,[z0,z1,z234,z7,z2,z4,z158]),(0,[z0,z1,z44,z7,z2,z4,z5])],[(0,[z0,z1,z45,z93,z7,z4,z5]),(0,[z0,z1,z7,z2,z4,z235,z5])],[(0,[z0,z1,z29,z2,z4,z5,z77]),(0,[z0,z1,z7,z20,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z236]),(0,[z237,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z2,z10,z238,z4,z5])],[(0,[z0,z1,z7,z2,z239,z4,z5]),(0,[z168,z0,z1,z2,z21,z4,z5]),(0,[z0,z240,z36,z1,z2,z4,z5])],[(0,[z0,z36,z219,z1,z2,z4,z5]),(0,[z241,z168,z0,z1,z7,z4,z5]),(1,[z0,z1,z29,z21,z4,z5])],[(1,[z76,z1,z7,z2,z143,z5])],[(0,[z1,z7,z99,z2,z86,z4,z5]),(0,[z0,z1,z7,z2,z233,z4,z5])],[(0,[z0,z1,z7,z2,z242,z4,z5])],[(0,[z0,z36,z1,z95,z2,z4,z5]),(1,[z0,z1,z7,z83,z4,z60])],[(0,[z0,z1,z243,z7,z2,z4,z5]),(0,[z0,z1,z2,z21,z105,z4,z5]),(0,[z0,z9,z1,z2,z4,z5,z17]),(0,[z0,z1,z244,z125,z2,z4,z5])],[(0,[z0,z245,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z246,z4,z5])]],
   [[(0,[z0,z1,z29,z2,z4,z177,z5]),(0,[z0,z1,z7,z20,z2,z4,z247]),(0,[z0,z1,z2,z248,z21,z4,z5]),(0,[z0,z249,z1,z29,z2,z4,z5]),(0,[z0,z144,z1,z7,z125,z4,z5])],[(0,[z0,z1,z7,z2,z250,z4,z5]),(0,[z0,z9,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z21,z4,z5,z145])],[(0,[z251,z0,z1,z93,z7,z4,z5]),(0,[z0,z1,z7,z252,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z60,z5])],[],[(0,[z0,z219,z1,z7,z2,z4,z5]),(0,[z0,z253,z1,z7,z2,z4,z5]),(0,[z0,z36,z1,z99,z2,z4,z5]),(0,[z0,z1,z56,z2,z21,z4,z5]),(0,[z0,z254,z1,z7,z2,z4,z5]),(0,[z0,z1,z125,z2,z10,z4,z5]),(0,[z0,z43,z1,z255,z2,z4,z5])],[(0,[z0,z1,z256,z7,z2,z4,z5])],[(0,[z147,z0,z1,z2,z21,z4,z5]),(0,[z0,z16,z1,z2,z86,z4,z5]),(0,[z0,z7,z20,z2,z166,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z257])],[(0,[z0,z1,z258,z7,z2,z4,z5]),(0,[z0,z68,z1,z7,z2,z4,z120]),(0,[z0,z259,z36,z1,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z260]),(0,[z261,z0,z1,z93,z7,z2,z5]),(0,[z0,z1,z7,z262,z2,z4,z5]),(0,[z0,z229,z7,z2,z123,z4,z5])],[(0,[z0,z219,z1,z2,z10,z4,z5]),(0,[z0,z1,z2,z10,z4,z177,z5]),(0,[z0,z1,z7,z2,z4,z263,z5]),(0,[z0,z1,z264,z7,z2,z4,z5])],[(0,[z28,z113,z1,z7,z2,z4,z5]),(0,[z0,z36,z1,z2,z86,z4,z5])],[(0,[z0,z1,z7,z2,z4,z143,z5]),(0,[z0,z16,z1,z2,z4,z23,z5]),(0,[z0,z43,z36,z1,z2,z4,z5])],[(0,[z0,z1,z7,z265,z2,z4,z5]),(0,[z0,z1,z266,z7,z2,z4,z5]),(0,[z0,z16,z51,z1,z2,z4,z5]),(0,[z0,z1,z267,z7,z2,z4,z5]),(0,[z0,z1,z186,z2,z10,z4,z5]),(0,[z268,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z2,z63,z10,z4,z5])],[(0,[z0,z1,z7,z2,z4,z47,z60])],[(0,[z46,z76,z0,z1,z7,z2,z5]),(0,[z0,z1,z7,z2,z4,z269,z5]),(0,[z0,z1,z7,z2,z53,z4,z5]),(0,[z0,z43,z1,z7,z4,z5,z120]),(0,[z0,z1,z139,z2,z4,z47,z5])]],
   [[(0,[z0,z1,z7,z270,z2,z4,z5]),(0,[z0,z36,z51,z1,z2,z4,z5]),(0,[z0,z1,z234,z7,z2,z4,z78]),(0,[z0,z1,z7,z2,z4,z120,z17]),(1,[z0,z1,z7,z2,z57,z47])],[(0,[z0,z229,z1,z7,z2,z23,z5]),(0,[z0,z1,z2,z63,z22,z4,z5]),(0,[z0,z271,z1,z7,z2,z4,z5])],[(0,[z272,z0,z1,z7,z2,z4,z5]),(0,[z46,z0,z229,z7,z2,z4,z5])],[(0,[z98,z0,z1,z2,z21,z4,z5]),(0,[z0,z1,z7,z2,z273,z4,z5]),(0,[z0,z1,z179,z7,z186,z4,z5]),(0,[z0,z1,z7,z2,z57,z47,z5])],[(0,[z0,z1,z7,z274,z2,z4,z5]),(0,[z0,z1,z7,z275,z2,z4,z5]),(1,[z0,z1,z2,z135,z4,z5]),(0,[z0,z1,z7,z2,z166,z4,z5]),(0,[z0,z1,z234,z29,z2,z4,z5]),(0,[z0,z1,z83,z2,z61,z4,z5])],[],[(0,[z0,z94,z1,z7,z2,z4,z5]),(0,[z164,z0,z7,z2,z4,z5,z90]),(0,[z0,z68,z1,z7,z2,z4,z59])],[(0,[z0,z16,z1,z179,z2,z4,z5]),(0,[z0,z1,z276,z7,z2,z4,z5]),(0,[z0,z1,z277,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z174,z5]),(0,[z0,z62,z1,z2,z21,z4,z5]),(0,[z0,z249,z1,z7,z2,z4,z5]),(1,[z0,z7,z2,z4,z5,z278]),(1,[z0,z1,z49,z2,z4,z5])],[(0,[z0,z9,z1,z87,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z278])],[(0,[z0,z1,z7,z2,z4,z5,z279]),(0,[z0,z16,z1,z186,z2,z4,z5]),(0,[z0,z1,z7,z2,z280,z4,z5]),(0,[z0,z229,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z281,z2,z4,z5])],[(0,[z0,z1,z7,z2,z135,z4,z5]),(0,[z0,z1,z7,z2,z143,z23,z5]),(0,[z168,z0,z1,z195,z2,z4,z5]),(1,[z0,z1,z282,z2,z4,z5]),(0,[z0,z1,z7,z186,z2,z4,z5])],[(0,[z0,z1,z7,z2,z283,z4,z5]),(0,[z272,z0,z16,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z284,z5]),(0,[z1,z7,z2,z4,z5,z285,z120])],[(0,[z0,z9,z1,z20,z2,z4,z5]),(0,[z286,z0,z1,z7,z2,z4,z5])],[(1,[z28,z1,z37,z2,z4,z5]),(0,[z0,z16,z68,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z287,z5])],[(0,[z0,z288,z1,z7,z2,z4,z5]),(0,[z0,z16,z1,z175,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z289])]],
   [[(0,[z241,z0,z36,z1,z2,z4,z5]),(0,[z0,z94,z16,z1,z2,z4,z5]),(0,[z0,z1,z29,z2,z4,z47,z5])],[(1,[z0,z1,z290,z2,z4,z5]),(0,[z0,z1,z7,z2,z291,z4,z5]),(0,[z0,z1,z29,z2,z22,z4,z5])],[(0,[z0,z9,z1,z2,z4,z114,z5]),(0,[z292,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z95,z7,z2,z185,z5]),(0,[z0,z1,z7,z2,z23,z5,z17])],[(0,[z0,z1,z7,z54,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z293]),(0,[z0,z1,z7,z2,z294,z4,z5]),(0,[z0,z1,z7,z295,z2,z4,z5]),(1,[z0,z36,z1,z2,z4,z5]),(0,[z0,z73,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z296,z5])],[(1,[z0,z1,z297,z2,z4,z5])],[(0,[z0,z1,z7,z2,z298,z4,z5]),(0,[z0,z1,z2,z10,z10,z4,z5]),(0,[z299,z0,z1,z7,z2,z4,z5])],[(0,[z300,z0,z1,z7,z2,z4,z5]),(0,[z241,z0,z1,z301,z2,z4,z5]),(0,[z0,z9,z1,z2,z4,z5,z120]),(0,[z0,z1,z7,z2,z4,z5,z302]),(0,[z0,z1,z2,z10,z4,z185,z5]),(0,[z0,z1,z175,z7,z2,z4,z158])],[(0,[z113,z0,z1,z29,z2,z4,z5]),(0,[z0,z1,z7,z290,z2,z4,z5]),(0,[z0,z1,z303,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z304]),(0,[z0,z1,z7,z2,z4,z305,z5]),(0,[z0,z1,z7,z2,z4,z210,z5]),(0,[z0,z1,z29,z306,z2,z4,z5])],[(0,[z0,z0,z1,z7,z2,z4,z5]),(0,[z28,z0,z1,z2,z21,z4,z5]),(0,[z0,z1,z307,z7,z2,z4,z5]),(0,[z308,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z2,z283,z10,z4,z5])],[(0,[z0,z1,z234,z7,z2,z4,z5]),(0,[z0,z1,z309,z7,z2,z4,z5])],[(0,[z97,z0,z36,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z310,z5])],[(1,[z147,z219,z7,z2,z4,z5]),(0,[z311,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z312,z5]),(0,[z0,z16,z1,z2,z4,z59,z5]),(0,[z313,z0,z1,z7,z2,z4,z5])]],
   [[(0,[z0,z1,z314,z7,z2,z4,z5]),(0,[z241,z0,z1,z7,z2,z223,z5]),(0,[z0,z1,z7,z2,z4,z315,z5]),(0,[z155,z0,z1,z7,z2,z4,z177]),(0,[z0,z9,z1,z125,z2,z4,z5])],[(0,[z0,z1,z316,z7,z2,z4,z5]),(0,[z0,z36,z9,z1,z2,z4,z5]),(0,[z0,z16,z1,z2,z4,z5,z90]),(0,[z317,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z318,z7,z2,z4,z5]),(0,[z0,z1,z7,z301,z2,z4,z5]),(0,[z241,z0,z1,z7,z2,z319,z5]),(0,[z0,z1,z7,z2,z4,z320,z5]),(0,[z0,z9,z1,z2,z4,z143,z5]),(0,[z0,z1,z7,z2,z4,z5,z90]),(0,[z0,z1,z7,z2,z4,z5,z285])],[(0,[z0,z1,z7,z2,z2,z4,z5]),(0,[z76,z0,z36,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z321,z5]),(1,[z0,z1,z7,z2,z70,z5])],[(0,[z0,z1,z7,z2,z4,z322,z5]),(0,[z0,z1,z7,z2,z4,z323,z5]),(0,[z0,z1,z7,z2,z4,z324,z5])],[(0,[z325,z0,z1,z7,z2,z4,z5])],[(1,[z0,z1,z7,z2,z319,z5]),(0,[z0,z9,z1,z2,z4,z158,z5]),(0,[z0,z43,z1,z7,z2,z326,z5])],[(0,[z327,z0,z1,z7,z2,z4,z5]),(1,[z0,z142,z1,z2,z4,z5])],[(0,[z0,z16,z219,z1,z2,z4,z5]),(0,[z0,z1,z306,z7,z2,z4,z5])],[(0,[z113,z1,z7,z54,z2,z4,z5]),(0,[z164,z156,z0,z1,z7,z2,z4]),(0,[z0,z1,z2,z21,z4,z5,z120]),(0,[z0,z1,z7,z2,z4,z328,z5])],[(0,[z0,z1,z7,z329,z2,z4,z5])],[],[(0,[z0,z1,z7,z2,z330,z4,z5]),(0,[z0,z16,z1,z95,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z79,z5]),(0,[z0,z112,z229,z1,z7,z2,z5]),(0,[z331,z0,z1,z2,z21,z4,z5]),(0,[z332,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z333]),(0,[z136,z0,z1,z7,z2,z4,z5])],[(0,[z1,z7,z99,z2,z4,z177,z5]),(1,[z164,z0,z7,z2,z4,z90]),(1,[z0,z144,z1,z7,z23,z5])],[(0,[z0,z16,z1,z2,z4,z5,z334]),(0,[z0,z1,z175,z234,z2,z4,z5])]],
   [[(0,[z0,z1,z7,z335,z2,z4,z5]),(0,[z113,z0,z1,z7,z2,z4,z5])],[(0,[z0,z16,z1,z2,z4,z60,z5]),(0,[z0,z336,z1,z7,z2,z4,z5]),(0,[z0,z337,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z338,z4,z5])],[(0,[z0,z1,z339,z7,z2,z4,z5]),(0,[z0,z1,z2,z10,z4,z5,z77])],[(0,[z0,z9,z1,z37,z2,z4,z5]),(0,[z0,z16,z1,z99,z2,z4,z5]),(0,[z156,z0,z36,z1,z2,z4,z5]),(1,[z0,z1,z178,z2,z4,z5]),(0,[z0,z1,z175,z7,z2,z4,z78]),(0,[z0,z1,z7,z2,z340,z4,z5])],[(0,[z0,z1,z7,z99,z2,z4,z5]),(0,[z0,z1,z2,z21,z4,z143,z5]),(0,[z0,z1,z7,z2,z4,z341,z5]),(0,[z0,z342,z1,z7,z2,z4,z5])],[(0,[z113,z0,z1,z2,z10,z4,z5]),(0,[z0,z343,z1,z7,z2,z4,z5]),(0,[z0,z229,z1,z29,z2,z4,z5]),(0,[z0,z36,z1,z234,z2,z4,z5])],[],[(0,[z0,z1,z87,z2,z10,z4,z5]),(0,[z0,z1,z175,z29,z2,z4,z5]),(0,[z0,z344,z1,z7,z2,z4,z5])],[(0,[z0,z345,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z346]),(0,[z0,z1,z2,z21,z4,z158,z5]),(0,[z0,z1,z7,z2,z347,z4,z5])],[(0,[z0,z16,z1,z2,z123,z4,z5]),(0,[z0,z1,z7,z2,z348,z4,z5])],[(0,[z113,z0,z16,z1,z2,z4,z5]),(0,[z0,z9,z1,z54,z2,z4,z5]),(0,[z0,z1,z7,z2,z86,z4,z5]),(0,[z0,z1,z7,z178,z2,z4,z5])],[(0,[z168,z98,z0,z1,z7,z4,z5]),(0,[z349,z1,z7,z2,z4,z5,z120]),(0,[z0,z1,z350,z7,z2,z4,z5])],[(0,[z0,z351,z1,z7,z2,z4,z5]),(0,[z0,z1,z2,z123,z4,z352,z5]),(0,[z164,z0,z36,z1,z2,z4,z5])],[(0,[z0,z353,z1,z7,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z177,z5]),(0,[z0,z36,z1,z2,z123,z4,z5]),(0,[z0,z1,z7,z2,z354,z4,z5]),(0,[z0,z36,z1,z29,z2,z4,z5]),(0,[z0,z1,z355,z7,z2,z4,z5])],[(0,[z0,z1,z54,z2,z10,z4,z5]),(0,[z0,z9,z1,z56,z2,z4,z5]),(1,[z0,z9,z87,z2,z4,z5]),(0,[z0,z356,z1,z7,z2,z4,z5]),(0,[z0,z1,z2,z21,z4,z170,z5]),(1,[z349,z1,z7,z2,z4,z5])],[(0,[z113,z0,z9,z1,z2,z4,z5]),(1,[z0,z171,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z23,z5]),(1,[z0,z1,z7,z2,z326,z5])]],
   [[(0,[z0,z1,z7,z2,z4,z77,z120]),(0,[z357,z0,z1,z7,z2,z4,z5])],[(0,[z0,z43,z9,z1,z2,z4,z5])],[(0,[z0,z202,z1,z93,z2,z4,z5]),(0,[z0,z1,z7,z2,z358,z4,z5]),(0,[z241,z0,z1,z7,z99,z4,z5]),(0,[z0,z1,z99,z2,z10,z4,z5])],[(0,[z0,z1,z7,z2,z359,z4,z5]),(0,[z0,z1,z7,z2,z360,z4,z5]),(0,[z0,z1,z7,z361,z2,z4,z5]),(0,[z0,z1,z2,z21,z4,z5,z17]),(0,[z362,z0,z1,z7,z2,z4,z5])],[(1,[z168,z0,z7,z166,z4,z5]),(0,[z0,z1,z363,z7,z2,z4,z5]),(0,[z0,z364,z1,z7,z2,z4,z5])],[],[(0,[z1,z7,z2,z105,z4,z143,z5]),(0,[z0,z1,z7,z2,z4,z5,z365]),(1,[z0,z1,z2,z4,z26,z5])],[(0,[z366,z0,z1,z7,z2,z4,z5])],[(0,[z219,z1,z93,z7,z2,z4,z5]),(0,[z367,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z4,z5]),(0,[z368,z0,z1,z7,z2,z4,z5]),(0,[z168,z0,z1,z121,z2,z4,z5])],[(0,[z0,z1,z369,z7,z2,z4,z5])],[],[(0,[z370,z0,z1,z7,z2,z4,z5]),(0,[z0,z371,z36,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z372,z5])],[(0,[z0,z1,z7,z373,z2,z4,z5]),(0,[z0,z1,z2,z21,z199,z4,z5]),(0,[z0,z1,z2,z102,z10,z4,z5])],[(0,[z0,z1,z7,z2,z4,z374,z5]),(0,[z0,z1,z7,z2,z4,z26,z5])],[(0,[z0,z1,z7,z2,z4,z5,z375]),(0,[z0,z1,z376,z7,z2,z4,z5]),(0,[z0,z377,z1,z7,z2,z4,z5]),(0,[z378,z0,z1,z7,z2,z4,z5])],[(0,[z357,z0,z9,z1,z2,z4,z5]),(0,[z0,z1,z175,z7,z2,z4,z5])]],
   [[(1,[z0,z1,z7,z115,z2,z4]),(0,[z0,z379,z1,z7,z2,z4,z5]),(0,[z76,z0,z1,z7,z2,z143,z5]),(0,[z0,z1,z7,z2,z380,z4,z5]),(0,[z0,z1,z7,z2,z4,z381,z5]),(1,[z0,z1,z255,z2,z4,z5])],[(0,[z382,z0,z1,z7,z2,z4,z5]),(0,[z0,z16,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z383,z2,z4,z5]),(0,[z0,z7,z2,z4,z5,z278,z17])],[(0,[z0,z229,z1,z2,z10,z4,z5]),(1,[z0,z1,z234,z2,z4,z78])],[],[(0,[z0,z1,z37,z7,z2,z4,z5]),(0,[z0,z1,z7,z384,z2,z4,z5]),(0,[z385,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z175,z2,z10,z4,z5]),(0,[z386,z0,z7,z2,z4,z5,z17])],[(0,[z0,z1,z387,z7,z2,z4,z5]),(0,[z0,z68,z1,z2,z21,z4,z5]),(0,[z0,z36,z1,z7,z2,z4,z5])],[(0,[z241,z0,z9,z1,z2,z4,z5]),(0,[z241,z0,z51,z1,z7,z4,z5])],[(0,[z241,z0,z253,z7,z2,z4,z5]),(0,[z388,z0,z1,z7,z2,z4,z5]),(0,[z0,z16,z1,z2,z4,z185,z5]),(0,[z0,z1,z7,z255,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z389,z5])],[(0,[z0,z1,z37,z2,z10,z4,z5]),(0,[z0,z1,z2,z4,z390,z5,z90]),(0,[z0,z1,z7,z125,z2,z22,z5])],[(0,[z0,z1,z391,z7,z2,z4,z5]),(0,[z0,z1,z133,z7,z2,z4,z5]),(0,[z0,z1,z2,z166,z10,z4,z5]),(0,[z392,z0,z1,z7,z2,z4,z5]),(0,[z0,z36,z1,z2,z10,z4,z5])],[(1,[z393,z0,z1,z7,z2,z4]),(1,[z0,z253,z7,z2,z4,z5]),(0,[z0,z16,z16,z1,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z185,z5]),(0,[z0,z1,z7,z394,z2,z4,z5])],[(0,[z0,z16,z1,z2,z395,z4,z5]),(0,[z0,z1,z2,z10,z4,z47,z5])],[(0,[z396,z0,z1,z7,z2,z4,z5]),(1,[z0,z1,z7,z2,z5,z302]),(0,[z0,z43,z1,z29,z2,z4,z5]),(0,[z0,z1,z2,z10,z22,z4,z5])],[(1,[z0,z1,z301,z2,z4,z5]),(1,[z98,z1,z7,z99,z4,z5]),(0,[z397,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z29,z2,z4,z80,z5])],[(0,[z0,z36,z16,z1,z2,z4,z5]),(0,[z0,z1,z7,z398,z2,z4,z5]),(0,[z0,z1,z7,z399,z2,z4,z5])]],
   [[(0,[z0,z16,z9,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z22,z5,z17])],[(0,[z388,z0,z16,z1,z2,z4,z5]),(0,[z164,z0,z7,z2,z123,z4,z5]),(0,[z0,z1,z29,z2,z4,z5,z78]),(0,[z0,z1,z7,z400,z2,z4,z5]),(0,[z0,z1,z297,z2,z4,z23,z5])],[(0,[z0,z1,z7,z2,z401,z4,z5]),(0,[z0,z240,z1,z7,z2,z4,z5])],[(0,[z97,z0,z9,z1,z2,z4,z5]),(0,[z0,z1,z402,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z59,z5]),(0,[z403,z0,z1,z7,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z404,z5]),(0,[z0,z1,z7,z2,z405,z4,z5])],[(0,[z0,z1,z7,z115,z2,z4,z5]),(0,[z406,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z234,z2,z10,z4,z5])],[(0,[z349,z0,z1,z7,z2,z4,z5])],[(1,[z97,z93,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z407,z5]),(0,[z0,z9,z1,z2,z4,z23,z5]),(0,[z0,z1,z7,z2,z4,z408,z5])],[(1,[z0,z1,z7,z2,z223,z5]),(0,[z0,z1,z2,z10,z4,z80,z5]),(0,[z0,z1,z7,z2,z409,z4,z5]),(0,[z0,z112,z1,z7,z2,z5,z17])],[(0,[z0,z9,z1,z1,z2,z4,z5]),(1,[z0,z1,z2,z4,z79,z5]),(0,[z0,z36,z1,z7,z2,z10,z5]),(0,[z410,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z411,z5])],[(0,[z412,z0,z1,z7,z2,z4,z5]),(0,[z406,z0,z1,z2,z10,z4,z5])],[(0,[z0,z1,z7,z2,z4,z413,z5]),(0,[z0,z1,z414,z7,z2,z4,z5]),(0,[z0,z1,z125,z2,z21,z4,z5]),(1,[z0,z36,z1,z2,z10,z5])],[(0,[z241,z0,z1,z24,z2,z4,z5]),(0,[z156,z0,z68,z1,z7,z2,z4]),(1,[z0,z1,z415,z2,z4,z5]),(0,[z0,z377,z1,z7,z2,z5,z90]),(0,[z0,z1,z7,z2,z238,z4,z5])],[(0,[z416,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z417,z5]),(0,[z0,z68,z1,z7,z2,z4,z90])],[(0,[z0,z1,z7,z2,z418,z4,z5]),(0,[z0,z1,z7,z2,z4,z419,z5]),(0,[z420,z0,z36,z1,z2,z4,z5])],[(0,[z0,z9,z1,z2,z166,z4,z5]),(1,[z0,z16,z56,z2,z4,z5]),(0,[z0,z1,z282,z2,z4,z59,z5]),(0,[z362,z0,z1,z29,z2,z4,z5]),(0,[z421,z0,z36,z1,z2,z4,z5]),(0,[z0,z112,z36,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z422,z5]),(0,[z0,z1,z7,z2,z423,z4,z5]),(0,[z424,z0,z1,z7,z2,z4,z5])],[(1,[z0,z1,z24,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z425]),(0,[z0,z1,z7,z426,z2,z4,z5]),(0,[z0,z1,z7,z2,z427,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z428]),(0,[z0,z1,z2,z4,z5,z96,z17])]],
   [[],[(1,[z0,z1,z429,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z430,z5]),(0,[z0,z259,z1,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z431,z5]),(0,[z241,z0,z1,z29,z2,z4,z5]),(0,[z30,z0,z1,z290,z2,z4,z5]),(0,[z0,z9,z1,z179,z2,z4,z5]),(0,[z0,z1,z186,z2,z21,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z334]),(0,[z8,z0,z1,z2,z21,z4,z5]),(0,[z0,z43,z1,z7,z83,z4,z5])],[(0,[z0,z1,z432,z7,z2,z4,z5]),(0,[z0,z1,z433,z99,z2,z4,z5]),(0,[z0,z16,z1,z234,z2,z4,z5]),(0,[z434,z0,z36,z1,z2,z4,z5]),(0,[z0,z1,z7,z125,z22,z4,z5]),(0,[z0,z435,z1,z7,z2,z4,z5])],[(0,[z0,z9,z1,z186,z2,z4,z5]),(0,[z0,z43,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z60,z5])],[(0,[z30,z0,z229,z1,z7,z2,z5]),(0,[z0,z36,z1,z2,z4,z5,z77]),(0,[z0,z1,z7,z2,z5,z302,z90]),(0,[z0,z1,z7,z2,z4,z5,z436]),(0,[z0,z1,z82,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z437,z4,z5]),(0,[z0,z438,z1,z7,z2,z4,z5]),(0,[z0,z1,z2,z10,z4,z439,z5])],[(0,[z0,z1,z7,z429,z2,z4,z5]),(0,[z0,z1,z7,z2,z440,z4,z5]),(0,[z0,z1,z2,z21,z4,z23,z5])],[(0,[z156,z0,z9,z1,z2,z4,z5]),(0,[z0,z9,z68,z1,z2,z4,z5]),(0,[z0,z1,z441,z7,z2,z4,z5])],[(0,[z0,z1,z7,z442,z2,z4,z5]),(0,[z0,z9,z1,z175,z2,z4,z5]),(0,[z46,z0,z36,z1,z2,z4,z5]),(0,[z0,z43,z1,z2,z10,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z443]),(0,[z0,z112,z1,z7,z2,z57,z5])],[(0,[z0,z16,z1,z2,z4,z177,z5]),(0,[z0,z16,z1,z29,z2,z4,z5]),(0,[z0,z1,z444,z29,z2,z4,z5])],[(0,[z0,z1,z7,z2,z123,z4,z5]),(0,[z0,z1,z95,z2,z21,z4,z5]),(1,[z0,z1,z200,z2,z4,z5])],[(0,[z0,z1,z7,z445,z2,z4,z5]),(0,[z76,z1,z7,z2,z4,z143,z5]),(0,[z0,z1,z7,z446,z2,z4,z5])],[(0,[z447,z0,z1,z7,z2,z4,z5]),(0,[z97,z0,z1,z29,z2,z4,z5]),(0,[z0,z93,z7,z2,z166,z4,z5]),(0,[z0,z43,z16,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z448,z4,z5])]],
   [[(1,[z0,z1,z2,z449,z4,z5]),(0,[z0,z1,z7,z2,z4,z450,z5]),(0,[z0,z1,z7,z2,z132,z4,z5])],[(0,[z0,z438,z16,z1,z2,z4,z5]),(0,[z0,z1,z7,z451,z2,z4,z5])],[(0,[z393,z0,z1,z7,z2,z4,z5]),(0,[z0,z452,z1,z7,z2,z4,z5]),(0,[z164,z0,z9,z1,z2,z4,z5]),(0,[z0,z371,z1,z7,z2,z4,z5])],[(0,[z0,z1,z29,z2,z21,z4,z5])],[(0,[z0,z1,z453,z7,z2,z4,z5]),(0,[z0,z1,z454,z7,z2,z4,z5])],[(0,[z76,z0,z1,z29,z2,z4,z5]),(0,[z46,z0,z7,z2,z4,z59,z5]),(0,[z0,z1,z7,z455,z2,z4,z5]),(0,[z456,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z248,z4,z5])],[(0,[z0,z1,z7,z2,z449,z4,z5])],[(0,[z0,z1,z7,z2,z457,z4,z5]),(0,[z0,z1,z29,z2,z4,z5,z458]),(0,[z0,z1,z7,z2,z4,z5,z459])],[(0,[z0,z1,z7,z2,z4,z460,z5]),(0,[z0,z1,z7,z461,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z462,z5])],[(0,[z241,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z20,z2,z194,z5]),(0,[z0,z1,z244,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z47,z5,z17])],[(0,[z156,z0,z1,z7,z83,z2,z4]),(0,[z155,z0,z1,z7,z2,z4,z77]),(0,[z0,z1,z214,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z463,z5]),(0,[z0,z464,z1,z7,z2,z4,z5])],[(0,[z156,z0,z1,z7,z2,z4,z47]),(0,[z0,z9,z1,z2,z4,z5,z90]),(0,[z0,z1,z7,z465,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z466]),(0,[z0,z229,z1,z467,z2,z4,z5]),(0,[z0,z240,z1,z29,z2,z4,z5])],[(1,[z0,z1,z7,z2,z4,z5]),(0,[z447,z0,z9,z1,z2,z4,z5]),(0,[z0,z1,z179,z29,z2,z4,z5]),(0,[z468,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z198,z7,z2,z4,z5]),(0,[z469,z0,z1,z7,z2,z4,z5]),(0,[z241,z0,z1,z2,z10,z4,z5])]],
   [[(0,[z0,z1,z7,z470,z2,z4,z5])],[(1,[z156,z1,z7,z2,z4,z77])],[(0,[z471,z0,z1,z7,z2,z4,z5]),(0,[z0,z43,z1,z7,z2,z4,z120])],[(0,[z0,z9,z219,z1,z2,z4,z5])],[(0,[z0,z1,z444,z7,z2,z4,z5]),(0,[z241,z0,z16,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z22,z143,z5]),(0,[z0,z472,z1,z7,z2,z4,z5])],[(0,[z0,z1,z7,z7,z2,z4,z5]),(0,[z473,z0,z1,z7,z2,z4,z5]),(0,[z156,z0,z1,z29,z2,z4,z5]),(0,[z0,z1,z7,z83,z2,z4,z60])],[(0,[z0,z1,z7,z474,z2,z4,z5]),(0,[z0,z475,z1,z7,z2,z4,z5])],[(0,[z97,z0,z1,z7,z2,z4,z5]),(0,[z476,z0,z1,z7,z2,z4,z5]),(0,[z0,z9,z1,z95,z2,z4,z5])],[(1,[z0,z16,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z477,z5])],[(0,[z0,z1,z7,z2,z478,z4,z5]),(1,[z0,z1,z2,z395,z4,z5]),(0,[z0,z16,z1,z2,z10,z4,z5]),(0,[z0,z479,z1,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z480,z5]),(0,[z0,z134,z1,z2,z4,z143,z5]),(0,[z0,z1,z481,z7,z2,z4,z5]),(0,[z0,z144,z36,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z10,z4,z5])],[(0,[z46,z0,z112,z1,z7,z2,z5]),(0,[z0,z1,z29,z2,z4,z482,z5]),(0,[z0,z1,z29,z2,z57,z4,z5]),(0,[z0,z1,z7,z2,z4,z185,z5]),(0,[z483,z0,z1,z7,z2,z4,z5])],[(0,[z97,z0,z1,z2,z10,z4,z5]),(0,[z484,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z69]),(0,[z0,z9,z1,z2,z4,z60,z5]),(0,[z0,z16,z1,z2,z4,z47,z5]),(0,[z0,z1,z485,z7,z2,z4,z5])],[(0,[z76,z0,z1,z7,z2,z4,z5]),(1,[z0,z9,z1,z2,z4,z5]),(0,[z0,z16,z1,z2,z22,z4,z5])],[(0,[z486,z0,z1,z7,z2,z4,z5]),(0,[z241,z0,z487,z7,z2,z4,z5]),(0,[z0,z9,z1,z99,z2,z4,z5]),(0,[z164,z0,z1,z29,z2,z4,z5]),(0,[z0,z1,z2,z21,z4,z5,z90])],[(0,[z0,z1,z7,z2,z488,z4,z5]),(0,[z489,z0,z1,z7,z2,z4,z5]),(0,[z168,z0,z7,z2,z166,z4,z5])]],
   [[(0,[z0,z1,z7,z2,z395,z4,z5]),(0,[z0,z1,z282,z7,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z47,z5])],[(0,[z97,z0,z16,z1,z2,z4,z5]),(0,[z241,z0,z1,z7,z86,z4,z5]),(0,[z0,z68,z1,z7,z2,z57,z4]),(0,[z0,z36,z1,z2,z22,z4,z5]),(0,[z490,z0,z1,z7,z2,z4,z5])],[(0,[z241,z98,z1,z7,z2,z4,z5]),(0,[z76,z0,z1,z2,z10,z4,z5]),(0,[z30,z0,z1,z7,z2,z143,z5])],[(1,[z0,z202,z1,z2,z4,z5])],[(0,[z0,z9,z1,z2,z86,z4,z5]),(0,[z0,z1,z2,z10,z57,z4,z5])],[(0,[z0,z491,z1,z7,z2,z4,z5])],[(0,[z0,z1,z179,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z492,z5]),(0,[z76,z0,z16,z1,z2,z4,z5]),(0,[z0,z1,z29,z83,z2,z4,z5]),(1,[z0,z1,z493,z2,z4,z5])],[(0,[z155,z0,z36,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z494,z4,z5]),(0,[z0,z36,z1,z7,z2,z185,z5]),(0,[z0,z1,z7,z495,z2,z4,z5])],[(0,[z489,z0,z16,z1,z2,z4,z5]),(0,[z0,z1,z20,z2,z440,z4,z5])],[(1,[z113,z1,z54,z2,z4,z5]),(0,[z241,z1,z7,z2,z86,z4,z5]),(0,[z0,z9,z51,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z496,z5]),(1,[z0,z36,z1,z2,z185,z5]),(1,[z0,z1,z2,z4,z5,z497])],[(0,[z0,z36,z1,z2,z4,z80,z5]),(0,[z0,z1,z179,z2,z10,z4,z5])],[(0,[z76,z0,z9,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z498,z5]),(0,[z0,z1,z7,z2,z4,z60,z17])],[(0,[z156,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z87,z2,z21,z4,z5]),(0,[z0,z229,z1,z7,z2,z22,z5]),(0,[z0,z1,z499,z7,z2,z4,z5]),(0,[z0,z1,z2,z10,z4,z5,z78])],[(0,[z0,z353,z1,z93,z2,z4,z5]),(0,[z0,z1,z107,z2,z166,z4,z5]),(1,[z0,z229,z7,z2,z123,z5]),(0,[z0,z1,z2,z21,z4,z60,z5]),(0,[z0,z1,z7,z493,z2,z4,z5]),(0,[z0,z240,z1,z2,z22,z4,z5])],[(0,[z434,z46,z0,z1,z2,z4,z5]),(1,[z0,z112,z1,z7,z2,z17])]],
   [[(0,[z168,z0,z36,z1,z2,z4,z5]),(0,[z500,z0,z1,z7,z2,z4,z5])],[(0,[z0,z51,z1,z7,z166,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z497])],[(0,[z0,z219,z1,z2,z21,z4,z5]),(0,[z156,z0,z1,z2,z10,z4,z5]),(1,[z0,z1,z7,z2,z4,z176]),(0,[z0,z1,z7,z2,z4,z501,z5])],[],[(1,[z0,z1,z502,z7,z2,z5]),(0,[z503,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z504,z5]),(0,[z156,z0,z1,z505,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z506,z5]),(1,[z0,z1,z2,z440,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z507])],[(0,[z0,z16,z1,z2,z4,z5,z77]),(0,[z508,z0,z1,z7,z2,z4,z5]),(0,[z0,z68,z1,z7,z2,z4,z60]),(0,[z0,z509,z1,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z77]),(0,[z164,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z510,z5]),(0,[z0,z511,z1,z7,z2,z4,z5])],[(0,[z0,z1,z2,z449,z4,z143,z5]),(0,[z156,z0,z16,z1,z2,z4,z5]),(0,[z0,z1,z512,z2,z4,z5,z90]),(0,[z0,z1,z513,z7,z2,z4,z5]),(0,[z0,z1,z297,z7,z2,z4,z5])],[(0,[z0,z514,z1,z7,z2,z4,z5]),(0,[z30,z0,z36,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z515,z5]),(0,[z0,z9,z516,z1,z2,z4,z5]),(0,[z0,z51,z1,z29,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z517]),(0,[z0,z1,z234,z2,z4,z5,z78])],[(1,[z0,z1,z29,z2,z4,z5]),(0,[z0,z1,z518,z7,z2,z4,z5]),(0,[z0,z1,z281,z2,z10,z4,z5]),(0,[z0,z519,z1,z7,z2,z4,z5])],[(0,[z261,z0,z1,z7,z2,z4,z5]),(0,[z241,z0,z1,z7,z2,z4,z104]),(0,[z0,z520,z1,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z521]),(0,[z0,z522,z1,z7,z2,z4,z5]),(0,[z164,z0,z1,z2,z10,z4,z5])],[(0,[z0,z1,z7,z2,z4,z523,z5]),(0,[z0,z1,z7,z2,z319,z4,z5]),(1,[z0,z1,z2,z132,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z524])],[(0,[z147,z0,z36,z1,z2,z4,z5]),(1,[z0,z1,z7,z2,z4,z104])],[(1,[z0,z1,z7,z2,z4,z106]),(1,[z167,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z21,z360,z4,z5]),(1,[z0,z1,z95,z2,z10,z5]),(1,[z0,z1,z7,z2,z4,z525]),(0,[z0,z1,z49,z2,z4,z5,z17])]],
   [[(0,[z526,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z177,z5]),(0,[z46,z0,z9,z1,z2,z4,z5]),(0,[z164,z0,z16,z1,z2,z4,z5])],[(0,[z0,z1,z7,z527,z2,z4,z5]),(0,[z0,z1,z7,z2,z105,z4,z69]),(0,[z0,z1,z7,z528,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z529,z5])],[(0,[z97,z0,z219,z7,z2,z4,z5])],[(0,[z0,z530,z36,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z531,z5])],[(0,[z0,z1,z7,z532,z2,z4,z5]),(0,[z0,z94,z1,z2,z21,z4,z5]),(0,[z0,z1,z7,z2,z4,z533,z5])],[],[(0,[z0,z36,z1,z93,z2,z4,z5]),(0,[z0,z534,z1,z7,z2,z4,z5])],[(0,[z156,z1,z7,z99,z2,z4,z5]),(0,[z0,z1,z7,z535,z2,z4,z5]),(0,[z164,z0,z68,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z536,z4,z5]),(0,[z0,z112,z1,z7,z2,z4,z47])],[(0,[z0,z16,z229,z1,z2,z4,z5]),(0,[z0,z229,z1,z2,z21,z4,z5])],[],[(1,[z0,z1,z244,z2,z4,z5])],[(0,[z98,z0,z36,z1,z2,z4,z5]),(0,[z0,z9,z9,z1,z2,z4,z5]),(0,[z0,z1,z20,z2,z10,z4,z5])],[(0,[z0,z1,z7,z2,z4,z537,z5]),(0,[z0,z36,z229,z1,z2,z4,z5]),(0,[z0,z1,z2,z21,z4,z381,z5]),(0,[z0,z1,z7,z2,z538,z4,z5]),(0,[z0,z1,z539,z7,z2,z4,z5])],[(0,[z30,z1,z7,z2,z105,z4,z5]),(0,[z0,z9,z1,z2,z4,z59,z5]),(0,[z540,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z541,z7,z2,z4,z5])],[(0,[z0,z1,z29,z87,z2,z4,z5]),(1,[z0,z1,z7,z2,z4,z89])]],
   [[(0,[z0,z542,z1,z7,z2,z4,z5]),(0,[z0,z51,z1,z7,z2,z4,z5]),(0,[z0,z1,z2,z166,z21,z4,z5]),(0,[z0,z112,z1,z29,z2,z4,z5])],[],[(0,[z0,z1,z1,z7,z2,z4,z5]),(0,[z0,z543,z1,z7,z2,z4,z5])],[(0,[z28,z0,z1,z37,z2,z4,z5]),(0,[z0,z1,z7,z2,z544,z4,z5]),(0,[z164,z0,z1,z7,z2,z4,z120])],[(0,[z0,z1,z7,z2,z4,z5,z545])],[(0,[z0,z1,z54,z2,z4,z5,z78]),(0,[z0,z1,z433,z7,z2,z4,z5]),(0,[z0,z546,z1,z7,z2,z4,z5]),(0,[z0,z51,z1,z2,z10,z4,z5]),(0,[z0,z1,z7,z2,z4,z547,z5])],[(1,[z0,z1,z2,z10,z4,z5])],[(0,[z548,z0,z1,z7,z2,z4,z5])],[(0,[z147,z0,z1,z429,z2,z4,z5]),(0,[z0,z1,z549,z7,z2,z4,z5]),(1,[z0,z1,z433,z2,z4,z5]),(1,[z0,z1,z505,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z550]),(0,[z0,z1,z7,z2,z4,z551,z5])],[(0,[z0,z36,z475,z1,z2,z4,z5]),(0,[z0,z552,z1,z7,z2,z4,z5]),(1,[z1,z7,z2,z4,z5,z285])],[(0,[z28,z0,z1,z54,z2,z4,z5]),(0,[z0,z1,z234,z2,z21,z4,z5])],[(0,[z0,z553,z1,z7,z2,z4,z5]),(0,[z0,z65,z1,z7,z2,z86,z4]),(1,[z0,z1,z7,z2,z4,z247])],[(0,[z0,z1,z554,z7,z2,z4,z5]),(0,[z46,z0,z1,z29,z2,z4,z5]),(0,[z0,z1,z555,z7,z2,z4,z5]),(0,[z311,z0,z1,z2,z21,z4,z5])],[(0,[z0,z1,z7,z2,z4,z177,z120]),(0,[z0,z1,z29,z2,z4,z5,z120])],[(0,[z0,z1,z556,z7,z2,z4,z5])],[(0,[z0,z9,z1,z234,z2,z4,z5]),(0,[z0,z1,z2,z21,z4,z59,z5]),(1,[z0,z1,z2,z4,z5,z189])]],
   [[(0,[z0,z1,z7,z2,z4,z557,z5]),(0,[z0,z1,z7,z2,z4,z47,z5])],[(0,[z0,z1,z7,z2,z22,z4,z5])],[(0,[z0,z1,z93,z7,z2,z4,z5]),(0,[z28,z0,z36,z1,z2,z4,z5]),(0,[z164,z0,z1,z7,z2,z4,z59])],[(0,[z156,z0,z43,z1,z7,z2,z4])],[(0,[z0,z1,z502,z93,z7,z2,z5]),(0,[z0,z1,z2,z86,z10,z4,z5]),(0,[z156,z0,z1,z7,z2,z4,z17]),(0,[z0,z1,z7,z558,z2,z4,z5])],[(1,[z0,z353,z1,z2,z4,z5]),(1,[z0,z487,z7,z2,z4,z5]),(0,[z0,z1,z29,z2,z105,z4,z5]),(0,[z0,z553,z16,z1,z2,z4,z5]),(0,[z0,z229,z1,z7,z2,z47,z5])],[(0,[z0,z1,z487,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z189]),(0,[z0,z1,z29,z125,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z404,z5])],[(0,[z420,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z559]),(0,[z0,z9,z1,z2,z4,z177,z5]),(0,[z0,z9,z1,z2,z123,z4,z5]),(0,[z0,z9,z1,z29,z2,z4,z5]),(0,[z0,z1,z7,z560,z2,z4,z5])],[(0,[z0,z36,z1,z2,z57,z4,z5]),(0,[z421,z0,z1,z7,z2,z4,z5]),(0,[z0,z112,z1,z7,z2,z4,z5])],[(0,[z0,z561,z1,z7,z2,z4,z5]),(0,[z0,z16,z342,z1,z2,z4,z5]),(0,[z0,z112,z68,z1,z7,z2,z4]),(0,[z0,z1,z125,z2,z187,z4,z5])],[(0,[z97,z0,z93,z7,z2,z4,z5]),(0,[z0,z16,z1,z2,z4,z80,z5])],[(0,[z46,z0,z1,z7,z2,z23,z5]),(1,[z0,z1,z7,z2,z4,z562])],[(0,[z0,z1,z29,z2,z4,z158,z5])],[(0,[z76,z0,z1,z7,z2,z105,z5]),(0,[z0,z563,z1,z7,z2,z4,z5]),(0,[z0,z1,z505,z7,z2,z4,z5]),(0,[z0,z16,z1,z2,z4,z5,z78])],[(0,[z113,z0,z1,z2,z21,z4,z5]),(0,[z0,z1,z2,z10,z105,z4,z5]),(0,[z434,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z564,z2,z4,z5]),(0,[z565,z0,z1,z7,z2,z4,z5])],[(0,[z30,z0,z1,z7,z2,z4,z5])]],
   [[(0,[z0,z1,z37,z2,z4,z5,z78]),(0,[z0,z229,z1,z7,z2,z80,z5])],[(0,[z566,z0,z1,z7,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z5,z78])],[(0,[z0,z1,z7,z2,z567,z4,z5]),(0,[z0,z112,z16,z1,z2,z4,z5]),(0,[z0,z1,z7,z568,z2,z4,z5])],[(0,[z0,z1,z7,z569,z2,z4,z5]),(0,[z0,z213,z51,z1,z2,z4,z5])],[(0,[z46,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z570,z4,z5]),(0,[z571,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z29,z7,z21,z4,z5]),(0,[z0,z36,z1,z2,z4,z5,z572]),(0,[z0,z1,z2,z10,z4,z158,z5])],[(0,[z566,z0,z1,z2,z10,z4,z5]),(0,[z0,z1,z7,z2,z4,z573,z5])],[(1,[z251,z0,z1,z7,z4,z5]),(0,[z0,z1,z54,z2,z21,z4,z5]),(0,[z0,z112,z9,z1,z2,z4,z5]),(0,[z0,z16,z9,z7,z2,z4,z5]),(0,[z0,z1,z29,z2,z4,z5,z17])],[(0,[z0,z1,z31,z7,z2,z4,z5]),(0,[z0,z1,z574,z7,z2,z4,z5]),(0,[z0,z16,z56,z7,z2,z4,z5]),(0,[z0,z142,z1,z7,z2,z4,z5]),(0,[z575,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z2,z21,z4,z177,z5]),(0,[z46,z0,z1,z2,z10,z4,z5]),(0,[z0,z1,z2,z21,z123,z4,z5])],[(0,[z576,z0,z1,z7,z2,z4,z5])],[(0,[z0,z51,z219,z7,z2,z4,z5]),(0,[z0,z1,z99,z2,z21,z4,z5]),(0,[z0,z1,z7,z577,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z89,z5]),(0,[z0,z1,z7,z2,z4,z5,z578])],[(0,[z98,z0,z1,z7,z99,z4,z5]),(0,[z434,z0,z9,z1,z2,z4,z5]),(0,[z0,z1,z7,z4,z60,z5,z120])],[(0,[z579,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z580,z4,z5]),(0,[z30,z0,z9,z1,z2,z4,z5]),(0,[z46,z0,z16,z1,z2,z4,z5])],[(0,[z0,z1,z7,z581,z2,z4,z5]),(0,[z0,z9,z1,z7,z2,z4,z5])]],
   [[(0,[z0,z1,z7,z2,z4,z5,z582]),(1,[z0,z74,z1,z2,z4,z5]),(0,[z0,z1,z2,z10,z4,z5,z17]),(0,[z0,z1,z583,z7,z2,z4,z5])],[(0,[z155,z0,z1,z7,z2,z4,z47]),(0,[z0,z1,z7,z2,z584,z4,z5])],[(1,[z386,z0,z7,z2,z4,z5])],[(0,[z0,z154,z1,z7,z2,z4,z5]),(0,[z0,z144,z1,z200,z2,z4,z5])],[(0,[z147,z0,z9,z1,z2,z4,z5]),(0,[z0,z9,z1,z2,z10,z4,z5]),(0,[z0,z16,z1,z585,z2,z4,z5]),(0,[z0,z1,z29,z56,z2,z4,z5]),(0,[z0,z111,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z586]),(0,[z0,z1,z7,z2,z4,z587,z5])],[(0,[z0,z16,z1,z93,z2,z4,z5]),(0,[z0,z9,z1,z2,z4,z185,z5]),(0,[z0,z1,z7,z585,z2,z4,z5])],[(0,[z0,z1,z7,z2,z34,z4,z5]),(0,[z0,z1,z2,z10,z4,z39,z5])],[],[(0,[z0,z1,z7,z2,z4,z5,z588]),(0,[z0,z1,z7,z2,z589,z4,z5])],[],[(0,[z0,z1,z7,z2,z590,z4,z5]),(0,[z155,z0,z1,z29,z2,z4,z5])],[(0,[z0,z1,z7,z2,z591,z4,z5]),(0,[z0,z144,z1,z7,z2,z23,z5])],[(0,[z0,z7,z2,z4,z59,z5,z90])],[(0,[z0,z1,z93,z29,z2,z4,z5]),(0,[z592,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z175,z2,z21,z4,z5]),(0,[z0,z1,z7,z2,z593,z4,z5])],[],[(0,[z0,z16,z1,z2,z21,z4,z5]),(0,[z594,z0,z1,z7,z2,z4,z5])]],
   [[(0,[z0,z1,z45,z7,z2,z4,z5])],[(0,[z98,z0,z9,z1,z2,z4,z5]),(0,[z98,z0,z51,z1,z7,z4,z5]),(0,[z46,z30,z0,z1,z7,z2,z5]),(1,[z0,z1,z467,z2,z4,z5])],[(0,[z147,z219,z1,z7,z2,z4,z5]),(0,[z0,z1,z37,z2,z21,z4,z5])],[(0,[z0,z1,z7,z2,z595,z4,z5]),(0,[z241,z0,z1,z7,z2,z4,z304]),(0,[z0,z36,z1,z2,z21,z4,z5])],[(0,[z0,z1,z596,z29,z2,z4,z5]),(0,[z0,z144,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z597,z5])],[(0,[z0,z1,z598,z7,z2,z4,z5]),(0,[z0,z1,z2,z4,z47,z5,z497])],[(0,[z0,z1,z7,z599,z2,z4,z5]),(0,[z0,z1,z29,z20,z2,z4,z5]),(0,[z0,z1,z2,z21,z10,z4,z5])],[(1,[z0,z1,z7,z2,z4,z304]),(0,[z0,z1,z2,z21,z4,z185,z5])],[(0,[z0,z1,z7,z467,z2,z4,z5])],[(0,[z0,z600,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z63,z4,z5])],[(0,[z30,z0,z1,z29,z2,z4,z5]),(1,[z0,z1,z139,z2,z4,z5])],[(0,[z0,z1,z7,z2,z601,z4,z5]),(0,[z0,z602,z1,z7,z2,z4,z5])],[(0,[z592,z0,z9,z1,z2,z4,z5]),(0,[z0,z1,z7,z603,z2,z4,z5]),(0,[z0,z229,z1,z7,z2,z123,z5]),(0,[z386,z0,z1,z7,z2,z4,z5])],[(0,[z251,z0,z1,z7,z2,z4,z5])],[(0,[z604,z0,z1,z7,z2,z4,z5]),(0,[z0,z144,z16,z1,z2,z4,z5])],[(0,[z0,z1,z7,z2,z57,z23,z5]),(0,[z0,z112,z1,z7,z2,z4,z17])]],
   [[(0,[z147,z0,z1,z29,z2,z4,z5]),(0,[z0,z9,z1,z2,z4,z5,z77])],[(0,[z0,z1,z605,z7,z2,z4,z5]),(0,[z0,z606,z1,z29,z2,z4,z5])],[(0,[z155,z0,z1,z7,z2,z4,z5]),(0,[z0,z56,z7,z87,z2,z4,z5]),(0,[z0,z1,z29,z7,z186,z4,z5])],[(0,[z0,z51,z93,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z607]),(0,[z155,z0,z68,z1,z7,z2,z4]),(0,[z0,z144,z9,z1,z2,z4,z5])],[(0,[z241,z156,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z608]),(0,[z0,z1,z609,z7,z2,z4,z5]),(0,[z0,z1,z610,z7,z2,z4,z5])],[],[(0,[z0,z219,z7,z2,z166,z4,z5]),(1,[z0,z1,z31,z2,z4,z5]),(0,[z0,z16,z1,z2,z611,z4,z5]),(0,[z0,z1,z7,z2,z612,z4,z5])],[(0,[z613,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z614,z2,z4,z5]),(0,[z155,z0,z1,z2,z10,z4,z5]),(0,[z0,z16,z1,z2,z57,z4,z5]),(0,[z0,z1,z7,z2,z4,z615,z5])],[(0,[z156,z0,z1,z2,z21,z4,z5]),(0,[z0,z68,z7,z2,z4,z59,z5])],[(0,[z616,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z2,z10,z4,z5,z120]),(0,[z0,z617,z1,z7,z2,z4,z5])],[(0,[z0,z1,z93,z2,z10,z4,z5]),(0,[z618,z0,z1,z7,z2,z4,z5]),(0,[z168,z0,z1,z7,z2,z4,z5]),(0,[z0,z619,z1,z7,z2,z4,z5]),(0,[z0,z1,z512,z7,z2,z4,z5])],[(0,[z0,z1,z29,z2,z4,z143,z5]),(0,[z0,z9,z1,z528,z2,z4,z5]),(0,[z0,z1,z7,z620,z2,z4,z5])],[(0,[z155,z0,z16,z1,z2,z4,z5]),(0,[z0,z1,z596,z7,z2,z4,z5]),(0,[z0,z621,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z622,z5])],[(0,[z98,z0,z1,z29,z2,z4,z5]),(0,[z0,z144,z1,z493,z2,z4,z5])],[(0,[z623,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z80,z5]),(0,[z0,z1,z7,z624,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z625,z5]),(0,[z0,z1,z7,z2,z4,z626,z5])]],
   [[(0,[z0,z1,z627,z7,z2,z4,z5]),(0,[z241,z1,z7,z2,z4,z177,z5]),(0,[z0,z1,z7,z628,z2,z4,z5]),(0,[z0,z213,z1,z29,z2,z4,z5]),(0,[z0,z112,z1,z2,z10,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z629]),(0,[z0,z144,z1,z7,z4,z23,z5]),(0,[z0,z1,z630,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z22,z105,z5]),(0,[z155,z0,z9,z1,z2,z4,z5]),(0,[z0,z1,z196,z7,z2,z4,z5]),(0,[z631,z0,z1,z29,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z78])],[(0,[z0,z1,z7,z2,z632,z4,z5]),(0,[z0,z36,z1,z2,z105,z4,z5]),(0,[z0,z1,z2,z21,z4,z5,z77])],[(0,[z0,z1,z7,z2,z633,z4,z5]),(0,[z0,z516,z1,z7,z2,z4,z5]),(0,[z0,z16,z1,z83,z2,z4,z5]),(0,[z634,z0,z1,z7,z2,z4,z5]),(0,[z0,z43,z1,z2,z21,z4,z5])],[(1,[z241,z1,z7,z86,z4,z5]),(0,[z635,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z2,z10,z4,z143,z5]),(0,[z0,z134,z1,z7,z2,z4,z5]),(0,[z0,z1,z29,z2,z166,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z572])],[(0,[z0,z1,z56,z7,z2,z4,z5]),(0,[z636,z0,z1,z7,z2,z4,z5])],[(0,[z393,z0,z1,z93,z7,z2,z4]),(0,[z30,z0,z1,z2,z10,z4,z5]),(0,[z0,z36,z1,z83,z2,z4,z5]),(0,[z0,z1,z637,z7,z2,z4,z5])],[(0,[z147,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z20,z2,z70,z5]),(0,[z0,z1,z7,z638,z2,z4,z5])],[(0,[z168,z0,z9,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z247,z5]),(0,[z167,z46,z0,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z390,z5]),(0,[z0,z606,z1,z7,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z158,z5]),(0,[z0,z1,z7,z639,z2,z4,z5])],[(1,[z0,z377,z1,z7,z2,z5]),(0,[z640,z0,z1,z7,z2,z4,z5])],[(0,[z0,z641,z9,z1,z2,z4,z5]),(0,[z0,z1,z56,z2,z10,z4,z5]),(0,[z0,z1,z29,z186,z2,z4,z5]),(0,[z8,z0,z36,z1,z2,z4,z5]),(0,[z636,z0,z1,z2,z10,z4,z5]),(0,[z642,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z29,z37,z2,z4,z5]),(0,[z30,z0,z16,z1,z2,z4,z5]),(0,[z0,z7,z2,z123,z4,z59,z5])],[(0,[z147,z0,z1,z2,z10,z4,z5]),(0,[z0,z530,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z326,z4,z5])],[(0,[z0,z643,z1,z7,z2,z4,z5]),(0,[z0,z1,z29,z2,z4,z287,z5]),(0,[z0,z1,z7,z2,z4,z439,z5])],[(0,[z30,z0,z1,z7,z2,z105,z5]),(0,[z0,z1,z7,z2,z4,z5,z116]),(0,[z0,z1,z107,z7,z2,z4,z5]),(0,[z0,z144,z1,z29,z2,z4,z5])]],
   [[(0,[z644,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z47,z120]),(0,[z0,z645,z1,z7,z2,z4,z5])],[(0,[z0,z1,z646,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z562,z5]),(0,[z0,z43,z1,z7,z2,z597,z5])],[(0,[z147,z0,z16,z1,z2,z4,z5]),(0,[z0,z1,z2,z2,z21,z4,z5]),(0,[z0,z171,z1,z7,z2,z4,z5])],[(0,[z0,z1,z29,z54,z2,z4,z5]),(0,[z155,z0,z1,z7,z83,z2,z4])],[(0,[z0,z1,z7,z2,z4,z5,z647]),(0,[z0,z36,z1,z2,z4,z5,z17]),(1,[z0,z43,z1,z7,z4,z120])],[(0,[z648,z0,z1,z7,z2,z4,z5]),(0,[z98,z0,z1,z7,z2,z4,z5]),(0,[z0,z144,z1,z7,z2,z4,z525])],[],[(0,[z0,z1,z83,z2,z10,z4,z5])],[(0,[z147,z0,z93,z7,z2,z4,z5]),(0,[z241,z0,z1,z2,z21,z4,z5]),(0,[z0,z1,z7,z2,z4,z649,z5]),(0,[z0,z650,z1,z7,z2,z4,z5]),(0,[z0,z213,z1,z7,z2,z4,z5]),(0,[z164,z0,z1,z7,z2,z4,z90])],[(0,[z631,z0,z1,z7,z2,z4,z5]),(0,[z156,z1,z7,z2,z4,z5,z77]),(0,[z0,z1,z7,z2,z4,z5,z651])],[(0,[z0,z1,z7,z2,z652,z4,z5]),(0,[z98,z0,z1,z2,z10,z4,z5]),(0,[z0,z9,z1,z2,z4,z47,z5]),(0,[z0,z653,z1,z7,z2,z4,z5]),(0,[z0,z62,z1,z7,z2,z4,z5]),(0,[z0,z1,z29,z441,z2,z4,z5]),(0,[z0,z1,z7,z2,z57,z4,z47])],[(0,[z0,z9,z1,z2,z22,z4,z5]),(0,[z0,z229,z1,z196,z2,z4,z5])],[(1,[z0,z1,z2,z21,z4,z5])],[],[(0,[z168,z0,z1,z7,z166,z4,z5]),(0,[z0,z1,z2,z409,z21,z4,z5])],[(0,[z0,z1,z7,z2,z654,z4,z5]),(0,[z0,z1,z7,z2,z4,z655,z5]),(0,[z98,z0,z16,z1,z2,z4,z5]),(1,[z0,z240,z1,z2,z4,z5])]],
   [[(0,[z0,z1,z7,z2,z4,z5,z656]),(0,[z46,z0,z7,z2,z4,z80,z5])],[(0,[z0,z1,z7,z2,z657,z4,z5]),(0,[z0,z1,z7,z2,z4,z658,z5]),(1,[z0,z68,z7,z2,z4,z59]),(0,[z659,z0,z1,z7,z2,z4,z5])],[(0,[z0,z1,z133,z93,z7,z2,z4]),(0,[z0,z660,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z661,z5]),(0,[z0,z1,z29,z2,z4,z5,z90]),(0,[z0,z1,z7,z2,z4,z5,z662])],[(0,[z0,z1,z7,z2,z21,z4,z5]),(0,[z0,z1,z29,z2,z2,z4,z5]),(0,[z0,z1,z663,z29,z2,z4,z5])],[(1,[z0,z1,z2,z13,z4,z5])],[(0,[z97,z0,z1,z2,z21,z4,z5]),(0,[z0,z9,z1,z2,z4,z80,z5]),(0,[z168,z0,z1,z29,z2,z4,z5]),(1,[z0,z1,z2,z63,z4,z5])],[(1,[z155,z1,z7,z2,z4,z177])],[(0,[z0,z213,z9,z1,z2,z4,z5]),(0,[z0,z1,z664,z7,z2,z4,z5])],[(0,[z155,z0,z43,z1,z7,z2,z4]),(0,[z0,z1,z7,z2,z4,z5,z458])],[(0,[z0,z1,z7,z2,z4,z665,z5]),(0,[z164,z155,z0,z1,z7,z2,z4]),(0,[z155,z0,z1,z7,z2,z4,z17]),(0,[z0,z154,z1,z2,z4,z80,z5])],[(1,[z434,z0,z1,z2,z4,z5]),(1,[z0,z1,z7,z2,z597,z5])],[(0,[z76,z0,z1,z2,z21,z4,z5]),(0,[z0,z1,z7,z2,z13,z4,z5]),(0,[z0,z1,z7,z2,z666,z4,z5]),(0,[z0,z1,z2,z10,z4,z5,z226])],[(0,[z28,z0,z1,z7,z2,z4,z5]),(0,[z98,z0,z1,z7,z86,z4,z5]),(0,[z0,z667,z1,z7,z2,z4,z5]),(0,[z0,z1,z2,z21,z4,z47,z5]),(0,[z0,z144,z1,z2,z10,z4,z5])],[(0,[z0,z1,z7,z2,z4,z19,z5]),(0,[z0,z1,z2,z21,z22,z4,z5])],[(0,[z0,z1,z7,z2,z4,z668,z5]),(1,[z0,z249,z1,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5,z669]),(0,[z0,z1,z670,z7,z2,z4,z5]),(0,[z0,z36,z1,z87,z2,z4,z5]),(0,[z0,z1,z415,z2,z123,z4,z5])]],
   [[(0,[z0,z671,z1,z7,z2,z4,z5]),(1,[z0,z1,z2,z4,z352,z5])],[(0,[z0,z1,z7,z2,z4,z672,z5])],[],[(0,[z0,z1,z502,z7,z2,z4,z5]),(0,[z147,z0,z219,z7,z2,z4,z5]),(1,[z0,z1,z2,z611,z4,z5]),(0,[z0,z36,z1,z20,z2,z4,z5])],[(0,[z0,z1,z179,z2,z21,z4,z5])],[(0,[z673,z0,z1,z7,z2,z4,z5])],[(0,[z674,z0,z1,z7,z2,z4,z5]),(0,[z28,z0,z16,z1,z2,z4,z5]),(0,[z0,z667,z16,z1,z2,z4,z5])],[(0,[z675,z0,z1,z7,z2,z4,z5]),(1,[z0,z51,z7,z20,z4,z5]),(0,[z0,z51,z1,z7,z20,z4,z5]),(0,[z0,z1,z2,z21,z4,z80,z5]),(0,[z0,z1,z7,z2,z4,z352,z5])],[(0,[z156,z0,z1,z7,z2,z4,z177]),(0,[z0,z36,z1,z2,z233,z4,z5])],[(1,[z0,z1,z198,z2,z4,z5]),(0,[z0,z1,z7,z2,z105,z23,z5]),(0,[z0,z1,z7,z2,z4,z676,z5]),(0,[z0,z1,z7,z2,z4,z5,z677])],[(0,[z0,z1,z7,z2,z4,z678,z5]),(0,[z0,z679,z1,z7,z2,z4,z5]),(0,[z0,z1,z29,z2,z86,z4,z5]),(0,[z0,z1,z7,z2,z611,z4,z5]),(0,[z0,z1,z7,z2,z680,z4,z5])],[(0,[z681,z0,z1,z7,z2,z4,z5]),(0,[z682,z0,z1,z7,z2,z4,z5]),(0,[z28,z0,z9,z1,z2,z4,z5]),(0,[z0,z1,z683,z7,z2,z4,z5]),(1,[z0,z111,z1,z7,z2,z4]),(0,[z0,z1,z499,z2,z21,z4,z5]),(0,[z0,z1,z663,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z482,z5]),(0,[z0,z1,z7,z2,z4,z5,z684]),(0,[z0,z1,z7,z2,z57,z4,z5])],[(0,[z168,z0,z51,z7,z2,z4,z5]),(0,[z0,z685,z1,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z686,z4,z5]),(0,[z0,z1,z7,z687,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z5,z120])],[(0,[z331,z0,z1,z7,z2,z4,z5])],[(0,[z0,z641,z1,z7,z2,z4,z5]),(1,[z0,z1,z195,z2,z4,z5]),(0,[z0,z1,z29,z2,z4,z23,z5]),(0,[z0,z1,z7,z2,z4,z688,z5]),(0,[z0,z689,z1,z7,z2,z4,z5])]],
   [[(0,[z0,z9,z1,z93,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z690,z5]),(1,[z0,z1,z512,z2,z4,z5]),(0,[z682,z0,z1,z2,z10,z4,z5]),(0,[z0,z691,z1,z7,z2,z4,z5])],[(0,[z0,z1,z692,z7,z2,z4,z5]),(0,[z0,z16,z1,z2,z105,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z176]),(0,[z0,z144,z1,z7,z2,z4,z562])],[(0,[z693,z0,z1,z7,z2,z4,z5]),(0,[z694,z0,z1,z7,z2,z4,z5]),(0,[z168,z0,z1,z2,z10,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z695])],[(0,[z0,z1,z7,z2,z4,z60,z177]),(0,[z0,z1,z7,z2,z4,z696,z5])],[(0,[z164,z0,z1,z2,z21,z4,z5]),(1,[z0,z1,z179,z21,z4,z5])],[(0,[z697,z0,z1,z7,z2,z4,z5]),(1,[z0,z1,z7,z2,z194,z5]),(1,[z0,z1,z2,z4,z390,z5])],[(0,[z0,z9,z229,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z698,z4,z5]),(0,[z0,z1,z2,z232,z21,z4,z5]),(0,[z0,z36,z1,z125,z2,z4,z5]),(0,[z0,z1,z175,z2,z4,z158,z5])],[(0,[z0,z1,z699,z7,z2,z4,z5]),(0,[z168,z0,z16,z1,z2,z4,z5]),(0,[z0,z700,z1,z7,z2,z4,z5]),(0,[z0,z1,z415,z7,z2,z4,z5]),(0,[z0,z1,z7,z83,z2,z4,z5])],[(0,[z0,z36,z1,z2,z4,z143,z5]),(0,[z167,z0,z1,z7,z2,z4,z5]),(0,[z0,z16,z1,z2,z4,z158,z5]),(0,[z701,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z2,z10,z4,z23,z5])],[],[(0,[z0,z1,z7,z2,z4,z5,z702])],[(0,[z703,z0,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z704,z2,z4,z5])],[(0,[z0,z1,z7,z705,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z706,z5]),(0,[z164,z0,z1,z7,z2,z57,z4]),(0,[z0,z1,z2,z4,z162,z23,z5])],[(1,[z261,z0,z1,z7,z2,z5]),(0,[z156,z0,z1,z100,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z5,z525])],[(0,[z0,z68,z1,z29,z2,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z707,z2,z4,z5]),(0,[z164,z0,z377,z7,z2,z5])],[(0,[z0,z9,z1,z2,z4,z5]),(0,[z0,z36,z229,z2,z123,z5]),(0,[z164,z0,z7,z2,z4,z708])],[(0,[z0,z253,z7,z2,z4,z5]),(0,[z0,z1,z709,z2,z4,z5]),(0,[z0,z710,z1,z2,z4,z5])],[(0,[z0,z1,z711,z2,z4,z5]),(0,[z0,z36,z1,z2,z401,z5]),(0,[z0,z1,z2,z10,z4,z712])],[(0,[z0,z1,z7,z713,z4,z5]),(0,[z0,z714,z1,z2,z4,z5]),(0,[z156,z9,z1,z2,z4,z77]),(0,[z0,z1,z7,z2,z5,z302]),(0,[z0,z1,z2,z715,z4,z5])],[(0,[z0,z1,z7,z2,z4,z716]),(0,[z98,z1,z7,z99,z4,z5]),(0,[z0,z1,z7,z717,z4,z5]),(0,[z0,z43,z1,z29,z4,z120]),(0,[z0,z36,z1,z718,z4,z5])],[(0,[z0,z1,z7,z2,z4,z719]),(0,[z0,z1,z2,z720,z4,z5]),(0,[z721,z0,z1,z2,z4,z5])],[(0,[z362,z1,z37,z2,z4,z5]),(0,[z0,z253,z2,z10,z4,z5]),(0,[z0,z1,z722,z7,z2,z5]),(0,[z168,z0,z9,z166,z4,z5]),(0,[z0,z1,z234,z2,z4,z116]),(0,[z0,z1,z7,z2,z723,z5])],[(0,[z0,z1,z724,z2,z4,z5]),(1,[z1,z7,z2,z4,z725]),(0,[z0,z1,z29,z687,z4,z5])],[(0,[z155,z1,z7,z2,z4,z75]),(0,[z0,z112,z1,z7,z2,z702]),(0,[z0,z1,z2,z10,z5,z302]),(0,[z0,z726,z1,z2,z4,z5])],[],[(0,[z0,z1,z2,z10,z210,z5])],[(0,[z0,z1,z727,z2,z4,z5]),(0,[z98,z1,z433,z99,z4,z5]),(0,[z0,z9,z2,z4,z5,z278])],[(0,[z1,z7,z2,z713,z4,z5]),(0,[z0,z1,z728,z2,z4,z5]),(0,[z0,z1,z2,z729,z4,z5]),(0,[z0,z1,z2,z718,z4,z5]),(0,[z0,z1,z2,z4,z79,z89]),(0,[z0,z1,z2,z730,z4,z5]),(0,[z0,z7,z2,z4,z5,z731])],[(0,[z113,z1,z54,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z732]),(0,[z0,z733,z1,z2,z223,z5]),(0,[z0,z16,z1,z2,z5,z302]),(0,[z362,z1,z444,z2,z4,z5]),(0,[z0,z36,z1,z2,z185,z5]),(0,[z0,z1,z734,z2,z4,z5]),(0,[z0,z2,z4,z5,z278,z735])],[(0,[z46,z0,z7,z2,z182,z5]),(0,[z0,z1,z175,z2,z4,z404])]],
   [[(0,[z0,z7,z2,z4,z736,z5]),(0,[z0,z737,z1,z2,z4,z5]),(0,[z0,z16,z62,z2,z4,z5]),(0,[z0,z36,z1,z2,z354,z5]),(0,[z0,z1,z2,z4,z5,z738])],[(1,[z0,z7,z2,z4,z708]),(0,[z0,z36,z1,z2,z10,z5])],[(0,[z97,z93,z2,z10,z4,z5]),(0,[z0,z1,z7,z2,z4,z739]),(0,[z268,z1,z7,z2,z4,z177]),(0,[z0,z229,z7,z2,z123,z5]),(0,[z0,z1,z200,z2,z4,z525])],[(0,[z1,z740,z7,z2,z4,z5]),(0,[z0,z9,z344,z2,z4,z5]),(0,[z0,z1,z95,z2,z13,z5]),(0,[z168,z0,z166,z21,z4,z5]),(0,[z0,z7,z2,z4,z59,z71]),(0,[z0,z112,z1,z7,z2,z17])],[(0,[z28,z1,z2,z238,z4,z5]),(0,[z0,z1,z741,z2,z4,z5]),(0,[z0,z667,z1,z2,z611,z5]),(0,[z0,z1,z2,z742,z4,z5]),(0,[z0,z743,z1,z2,z4,z5]),(0,[z0,z2,z4,z5,z96,z278])],[(0,[z0,z1,z744,z2,z4,z5]),(0,[z0,z16,z56,z2,z4,z5]),(0,[z0,z36,z51,z20,z4,z5]),(0,[z745,z0,z1,z2,z4,z5]),(0,[z746,z1,z7,z2,z4,z5]),(0,[z349,z43,z1,z7,z4,z120])],[(0,[z0,z1,z24,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z176]),(0,[z1,z7,z2,z4,z5,z747]),(0,[z0,z1,z2,z748,z4,z5])],[(0,[z0,z1,z749,z2,z4,z5]),(0,[z0,z1,z750,z2,z4,z5]),(0,[z386,z156,z0,z7,z2,z4]),(0,[z155,z0,z1,z7,z2,z597]),(0,[z46,z0,z7,z2,z206,z5]),(0,[z0,z1,z84,z2,z132,z5]),(0,[z0,z1,z2,z132,z23,z5]),(0,[z0,z1,z29,z639,z4,z5]),(0,[z0,z1,z44,z2,z597,z5])],[(0,[z0,z1,z502,z7,z2,z5]),(0,[z0,z1,z2,z440,z4,z5]),(0,[z0,z1,z2,z4,z751,z5]),(0,[z0,z68,z7,z2,z4,z328]),(0,[z0,z36,z1,z2,z4,z562]),(1,[z0,z1,z7,z4,z752])],[(0,[z0,z753,z7,z2,z4,z5]),(0,[z0,z487,z301,z2,z4,z5]),(0,[z0,z1,z754,z2,z4,z5])],[(0,[z147,z219,z198,z2,z4,z5]),(0,[z0,z1,z2,z4,z755,z5]),(0,[z0,z345,z1,z7,z23,z5]),(0,[z0,z1,z2,z4,z756,z5]),(0,[z1,z7,z2,z4,z5,z757]),(0,[z0,z1,z2,z409,z10,z5]),(0,[z0,z1,z7,z2,z23,z525])],[(0,[z46,z0,z16,z2,z80,z5]),(0,[z0,z1,z2,z10,z4,z176]),(0,[z0,z7,z2,z4,z5,z758])],[(0,[z98,z1,z7,z713,z4,z5])],[(0,[z0,z1,z29,z2,z4,z5]),(0,[z0,z51,z20,z440,z4,z5]),(0,[z0,z1,z759,z2,z4,z5])],[(0,[z0,z760,z1,z7,z2,z5]),(0,[z0,z65,z1,z761,z2,z4]),(0,[z0,z1,z762,z7,z2,z5]),(0,[z0,z1,z95,z2,z132,z5])],[(0,[z0,z763,z1,z2,z4,z5]),(0,[z0,z1,z2,z764,z21,z4]),(0,[z0,z1,z7,z2,z597,z60])]],
   [[(0,[z97,z0,z62,z2,z4,z5]),(0,[z156,z1,z29,z2,z4,z77]),(0,[z0,z16,z1,z2,z4,z176]),(0,[z0,z1,z2,z132,z4,z5]),(0,[z0,z1,z234,z2,z4,z458])],[(0,[z0,z765,z1,z7,z4,z5]),(0,[z0,z1,z2,z766,z4,z5]),(0,[z0,z1,z767,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z768]),(0,[z0,z142,z1,z2,z185,z5]),(0,[z0,z769,z2,z10,z4,z5])],[(0,[z0,z1,z770,z2,z4,z5]),(0,[z0,z1,z2,z4,z771,z5]),(0,[z0,z1,z125,z2,z611,z5]),(0,[z0,z171,z2,z123,z4,z5]),(0,[z0,z1,z2,z21,z57,z47])],[(0,[z0,z772,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z106]),(0,[z155,z1,z7,z2,z4,z725]),(0,[z0,z51,z1,z2,z773,z5]),(0,[z0,z1,z214,z2,z194,z5]),(0,[z0,z1,z95,z2,z10,z5]),(0,[z0,z1,z7,z2,z4,z525])],[(0,[z0,z1,z7,z2,z4,z774]),(0,[z0,z1,z775,z2,z4,z5])],[(0,[z0,z1,z2,z776,z4,z5]),(0,[z0,z9,z1,z2,z4,z176]),(0,[z777,z0,z1,z2,z4,z5]),(0,[z0,z249,z596,z2,z4,z5]),(0,[z0,z769,z2,z22,z4,z5])],[(0,[z0,z1,z29,z330,z4,z5]),(0,[z618,z0,z9,z2,z4,z5]),(0,[z156,z1,z7,z2,z4,z411]),(0,[z0,z68,z369,z7,z2,z4]),(0,[z0,z1,z778,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z779])],[(0,[z0,z1,z2,z449,z4,z5]),(0,[z0,z780,z487,z2,z4,z5]),(0,[z0,z1,z781,z2,z4,z5]),(0,[z0,z377,z1,z2,z10,z5]),(0,[z0,z782,z1,z2,z4,z5])],[(0,[z0,z36,z1,z502,z2,z5]),(0,[z156,z519,z1,z7,z2,z4]),(0,[z0,z1,z186,z395,z4,z5]),(0,[z0,z1,z7,z2,z5,z783])],[(0,[z0,z62,z2,z4,z80,z5]),(0,[z386,z0,z36,z2,z4,z5])],[(0,[z0,z487,z24,z2,z4,z5]),(0,[z0,z144,z1,z297,z23,z5])],[(0,[z349,z1,z7,z2,z4,z304]),(0,[z0,z1,z784,z2,z4,z5]),(0,[z0,z1,z2,z785,z4,z5]),(0,[z0,z786,z1,z2,z4,z5])],[(0,[z393,z0,z9,z1,z2,z4]),(0,[z0,z1,z2,z787,z4,z5]),(0,[z0,z788,z1,z2,z4,z5]),(0,[z0,z111,z1,z29,z2,z4])],[(0,[z0,z1,z789,z2,z4,z5]),(0,[z0,z16,z1,z2,z4,z106]),(0,[z386,z0,z112,z1,z7,z2])],[(0,[z0,z1,z2,z790,z4,z5]),(0,[z388,z0,z1,z2,z4,z334]),(0,[z0,z142,z1,z2,z22,z5])],[(0,[z0,z1,z7,z2,z791,z5])]],
   [[(0,[z251,z0,z202,z1,z4,z5]),(0,[z0,z792,z1,z2,z4,z5])],[(0,[z0,z487,z29,z2,z4,z5]),(0,[z0,z9,z1,z2,z4,z104]),(0,[z0,z1,z7,z2,z4,z793])],[(0,[z0,z253,z7,z2,z4,z104]),(0,[z0,z9,z1,z2,z4,z106]),(0,[z0,z9,z1,z2,z4,z525]),(0,[z794,z0,z1,z7,z2,z4]),(0,[z0,z68,z282,z2,z4,z59])],[(0,[z0,z1,z7,z2,z4,z89]),(0,[z0,z1,z7,z795,z2,z4])],[(0,[z0,z1,z796,z2,z4,z5]),(0,[z0,z9,z369,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z5]),(0,[z0,z733,z1,z2,z4,z5]),(0,[z0,z1,z179,z730,z4,z5]),(0,[z0,z144,z1,z7,z797,z5]),(0,[z0,z112,z1,z7,z2,z798])],[(0,[z0,z1,z2,z799,z4,z5]),(0,[z0,z800,z7,z2,z4,z5])],[(0,[z0,z1,z7,z2,z801,z5]),(0,[z0,z1,z29,z329,z4,z5]),(0,[z0,z1,z7,z802,z2,z4]),(0,[z0,z1,z2,z803,z4,z5]),(0,[z0,z1,z21,z4,z26,z5]),(0,[z0,z1,z29,z52,z4,z5])],[(0,[z97,z804,z7,z2,z4,z5]),(0,[z251,z0,z487,z7,z4,z5]),(0,[z156,z1,z7,z2,z4,z77]),(0,[z0,z1,z186,z730,z4,z5]),(0,[z0,z805,z7,z2,z4,z5]),(0,[z0,z112,z1,z2,z96,z17])],[(0,[z0,z1,z7,z2,z4,z806]),(0,[z0,z1,z7,z2,z4,z807]),(0,[z489,z0,z1,z395,z4,z5]),(0,[z0,z808,z1,z2,z4,z5]),(0,[z0,z1,z7,z560,z22,z5])],[(0,[z0,z1,z2,z10,z4,z5]),(0,[z97,z133,z93,z7,z2,z4]),(0,[z0,z1,z7,z2,z809,z5]),(0,[z164,z0,z62,z2,z4,z5]),(0,[z349,z1,z810,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z811])],[(0,[z0,z1,z433,z2,z4,z5]),(0,[z0,z812,z1,z2,z4,z5]),(0,[z30,z0,z142,z1,z2,z5]),(0,[z0,z813,z1,z2,z4,z5]),(0,[z16,z1,z2,z4,z5,z285]),(0,[z0,z142,z1,z2,z63,z5])],[(0,[z1,z7,z2,z4,z5,z285]),(0,[z156,z1,z2,z10,z4,z77]),(0,[z0,z16,z1,z2,z4,z89]),(0,[z0,z229,z29,z2,z123,z5])],[(0,[z97,z393,z93,z7,z2,z4]),(0,[z0,z1,z814,z2,z4,z5]),(0,[z203,z0,z1,z2,z4,z116]),(0,[z0,z1,z2,z815,z4,z5]),(0,[z566,z0,z1,z4,z26,z5]),(0,[z0,z1,z200,z2,z4,z562]),(0,[z0,z816,z1,z2,z4,z5])],[(0,[z0,z16,z1,z2,z4,z5]),(0,[z261,z0,z1,z29,z2,z5]),(0,[z0,z1,z2,z4,z817,z5]),(0,[z0,z1,z2,z4,z158,z334]),(0,[z0,z1,z7,z2,z4,z247]),(0,[z168,z0,z7,z818,z4,z5]),(0,[z0,z1,z2,z4,z5,z819]),(0,[z0,z51,z20,z10,z4,z5]),(0,[z0,z1,z820,z2,z4,z5])]],
   [[(0,[z147,z219,z2,z21,z4,z5]),(0,[z0,z1,z2,z395,z4,z5]),(0,[z46,z0,z1,z718,z4,z5])],[(0,[z0,z1,z7,z821,z2,z5]),(0,[z0,z822,z7,z2,z4,z5])],[(0,[z261,z393,z0,z1,z7,z2]),(0,[z0,z1,z2,z823,z4,z5]),(0,[z156,z16,z1,z2,z4,z77]),(0,[z0,z9,z137,z2,z4,z5]),(0,[z0,z9,z1,z2,z4,z89]),(0,[z46,z0,z7,z2,z824,z5]),(0,[z46,z0,z111,z1,z7,z2]),(0,[z0,z1,z825,z2,z4,z5])],[(0,[z0,z36,z1,z2,z494,z5]),(0,[z0,z1,z2,z4,z5,z189]),(0,[z0,z1,z7,z2,z4,z826])],[(0,[z592,z1,z37,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z304]),(0,[z0,z827,z1,z2,z4,z5])],[(0,[z0,z1,z2,z828,z4,z5]),(0,[z0,z1,z2,z21,z70,z5]),(0,[z0,z7,z2,z824,z80,z5])],[(0,[z0,z1,z24,z2,z4,z104]),(0,[z0,z144,z1,z2,z611,z5])],[(0,[z0,z51,z7,z262,z4,z5]),(0,[z197,z1,z7,z2,z105,z5]),(0,[z0,z36,z1,z2,z5,z545]),(0,[z0,z829,z1,z2,z4,z5])],[(0,[z97,z36,z93,z2,z4,z5]),(0,[z0,z1,z2,z830,z223,z5]),(0,[z76,z157,z1,z7,z2,z5]),(0,[z0,z74,z87,z2,z4,z5]),(0,[z0,z144,z16,z1,z23,z5]),(0,[z0,z1,z831,z2,z4,z5]),(0,[z0,z36,z1,z2,z547,z5])],[(0,[z0,z353,z1,z2,z4,z5]),(0,[z0,z487,z7,z2,z4,z5]),(0,[z357,z0,z1,z3,z4,z5]),(0,[z0,z16,z1,z2,z4,z247])],[(0,[z0,z202,z1,z2,z4,z5]),(0,[z0,z9,z1,z2,z4,z811]),(0,[z0,z16,z2,z4,z5,z278]),(0,[z0,z832,z1,z2,z194,z5]),(0,[z833,z1,z7,z2,z4,z5]),(0,[z0,z229,z2,z123,z352,z5]),(0,[z0,z834,z1,z2,z4,z5])],[(0,[z0,z1,z301,z2,z4,z304]),(0,[z0,z606,z1,z2,z4,z482]),(0,[z0,z1,z7,z2,z4,z798])],[(0,[z30,z1,z7,z2,z105,z69]),(0,[z0,z1,z7,z2,z835,z5]),(0,[z0,z641,z1,z2,z13,z5]),(0,[z0,z1,z2,z836,z4,z5]),(0,[z0,z1,z7,z2,z837,z5]),(0,[z0,z74,z20,z2,z4,z5])],[(0,[z0,z1,z45,z29,z4,z5]),(0,[z0,z1,z29,z2,z4,z104]),(0,[z0,z229,z7,z2,z5,z662]),(0,[z0,z1,z2,z390,z5,z302])],[(0,[z0,z487,z2,z10,z4,z5]),(0,[z0,z1,z29,z2,z4,z106]),(0,[z0,z1,z2,z838,z4,z5]),(0,[z0,z839,z1,z2,z4,z5]),(0,[z0,z9,z1,z2,z4,z247]),(0,[z0,z1,z493,z2,z4,z5]),(0,[z0,z1,z29,z2,z4,z525]),(0,[z386,z0,z29,z2,z4,z5]),(0,[z0,z36,z1,z840,z4,z5])],[(0,[z76,z1,z2,z21,z143,z5]),(0,[z841,z0,z1,z2,z4,z5]),(0,[z842,z36,z1,z2,z4,z5])]],
   [[(0,[z0,z1,z843,z2,z4,z5]),(0,[z0,z1,z844,z2,z4,z5])],[(0,[z0,z1,z7,z2,z845,z5]),(0,[z0,z1,z2,z4,z846,z5]),(0,[z0,z1,z2,z847,z4,z5]),(0,[z0,z848,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z849,z5]),(0,[z850,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z497])],[(0,[z0,z1,z7,z2,z4,z851]),(0,[z0,z1,z852,z2,z4,z5]),(0,[z0,z1,z7,z2,z853,z5]),(0,[z167,z46,z0,z2,z80,z5]),(0,[z0,z1,z854,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z855]),(0,[z0,z856,z1,z2,z4,z5])],[(0,[z0,z857,z1,z2,z4,z5])],[(0,[z0,z858,z1,z2,z4,z5]),(0,[z0,z1,z2,z859,z4,z5]),(0,[z0,z1,z7,z2,z223,z304]),(0,[z0,z1,z2,z860,z4,z5]),(0,[z0,z1,z2,z4,z5,z861])],[(0,[z0,z1,z7,z862,z4,z5]),(0,[z0,z1,z7,z4,z863,z5]),(0,[z0,z1,z864,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z865]),(0,[z0,z866,z1,z2,z4,z5])],[(0,[z0,z1,z867,z2,z4,z5]),(0,[z0,z1,z7,z2,z319,z304]),(0,[z156,z1,z7,z614,z2,z4]),(0,[z0,z16,z1,z2,z837,z5]),(0,[z0,z438,z1,z2,z4,z174]),(0,[z0,z868,z1,z2,z4,z5]),(0,[z0,z1,z869,z2,z4,z5])],[(0,[z0,z1,z2,z870,z4,z5])],[(0,[z393,z0,z353,z1,z2,z4]),(0,[z113,z1,z441,z2,z4,z5]),(0,[z0,z871,z1,z2,z4,z5]),(0,[z0,z51,z214,z20,z4,z5]),(0,[z0,z1,z33,z21,z4,z5]),(0,[z0,z111,z1,z2,z10,z4])],[(0,[z0,z1,z2,z872,z4,z5]),(0,[z0,z1,z7,z2,z4,z725]),(0,[z0,z873,z1,z2,z4,z5]),(0,[z0,z43,z1,z7,z326,z120]),(0,[z0,z1,z874,z2,z4,z5])],[(0,[z0,z875,z7,z2,z4,z5]),(0,[z876,z0,z1,z7,z2,z4]),(0,[z0,z1,z877,z2,z4,z5]),(0,[z0,z229,z2,z10,z123,z5]),(0,[z0,z1,z347,z21,z4,z5]),(0,[z0,z1,z2,z4,z5,z878])],[(0,[z0,z9,z51,z20,z4,z5]),(0,[z0,z224,z1,z7,z2,z17])],[(0,[z0,z1,z7,z495,z4,z60])],[(0,[z0,z1,z879,z2,z4,z5]),(0,[z0,z51,z1,z395,z4,z5]),(0,[z0,z1,z880,z2,z4,z5]),(0,[z386,z0,z7,z2,z23,z5]),(0,[z0,z1,z2,z4,z881,z5])],[(0,[z0,z1,z882,z2,z4,z5]),(0,[z434,z0,z1,z883,z4,z5]),(0,[z0,z9,z1,z2,z4,z562]),(0,[z0,z1,z884,z2,z4,z5]),(0,[z0,z1,z885,z2,z4,z5]),(0,[z0,z1,z29,z2,z4,z89]),(0,[z0,z886,z1,z2,z4,z5])],[(0,[z0,z36,z1,z2,z194,z5]),(0,[z0,z1,z2,z887,z4,z5]),(0,[z0,z1,z888,z2,z4,z5])]],
   [[(0,[z0,z889,z1,z45,z4,z5]),(0,[z308,z219,z7,z2,z4,z5]),(0,[z0,z51,z7,z20,z70,z5]),(0,[z349,z1,z2,z21,z4,z5]),(0,[z0,z1,z21,z4,z5,z436]),(0,[z0,z890,z7,z2,z4,z5])],[(0,[z251,z0,z51,z7,z4,z5]),(0,[z241,z36,z1,z86,z4,z5]),(0,[z1,z7,z99,z713,z4,z5]),(0,[z0,z753,z2,z10,z4,z5]),(0,[z0,z43,z1,z255,z4,z120])],[(1,[z804,z7,z2,z4,z5]),(0,[z147,z16,z219,z2,z4,z5]),(0,[z0,z1,z2,z891,z4,z5]),(0,[z0,z1,z2,z892,z4,z5]),(0,[z0,z377,z68,z1,z7,z2]),(0,[z0,z893,z1,z2,z597,z5])],[(0,[z0,z1,z2,z894,z4,z5]),(0,[z46,z0,z111,z7,z2,z80]),(0,[z0,z895,z1,z7,z2,z5])],[(0,[z0,z36,z1,z2,z896,z5])],[(0,[z0,z1,z897,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z104]),(0,[z0,z898,z1,z2,z4,z5]),(0,[z0,z1,z2,z440,z4,z247]),(0,[z0,z74,z2,z53,z4,z5])],[(0,[z1,z7,z2,z4,z899,z5]),(0,[z167,z0,z1,z2,z4,z5]),(0,[z386,z0,z7,z2,z4,z5]),(0,[z0,z111,z1,z2,z21,z4]),(0,[z0,z142,z1,z2,z47,z5]),(0,[z0,z1,z82,z83,z4,z60])],[(0,[z147,z9,z219,z2,z4,z5]),(0,[z0,z65,z1,z2,z21,z4]),(0,[z98,z0,z1,z233,z4,z5]),(0,[z0,z9,z124,z2,z4,z5]),(0,[z0,z1,z2,z900,z4,z5]),(0,[z0,z1,z2,z4,z5,z901])],[(0,[z241,z1,z301,z86,z4,z5]),(0,[z0,z1,z29,z423,z4,z5])],[(0,[z0,z1,z133,z2,z21,z4]),(0,[z0,z1,z902,z2,z4,z5]),(0,[z0,z213,z306,z2,z4,z5])],[(0,[z0,z1,z2,z10,z4,z104]),(0,[z903,z0,z7,z2,z4,z5]),(0,[z0,z122,z1,z2,z4,z114]),(0,[z0,z1,z175,z2,z4,z114]),(0,[z0,z1,z29,z2,z4,z247]),(0,[z0,z1,z904,z2,z4,z5])],[(0,[z261,z0,z1,z2,z10,z5]),(0,[z0,z1,z2,z10,z4,z106]),(0,[z0,z1,z2,z10,z4,z525]),(0,[z386,z0,z2,z10,z4,z5])],[(0,[z0,z1,z905,z2,z4,z5]),(0,[z0,z1,z2,z4,z906,z5]),(0,[z0,z907,z1,z2,z4,z5]),(0,[z0,z1,z908,z2,z4,z5]),(0,[z0,z94,z1,z585,z4,z5]),(0,[z0,z1,z909,z2,z4,z5])],[],[(0,[z0,z1,z2,z34,z4,z158])],[(0,[z251,z0,z36,z1,z4,z5]),(0,[z0,z1,z910,z2,z4,z5]),(0,[z0,z1,z7,z911,z4,z5]),(0,[z0,z36,z1,z133,z2,z4]),(0,[z0,z16,z1,z2,z4,z104]),(0,[z0,z377,z36,z1,z2,z5])]],
   [[(0,[z0,z65,z1,z29,z2,z4]),(0,[z0,z16,z1,z2,z4,z525]),(0,[z0,z62,z229,z2,z4,z5]),(0,[z0,z1,z125,z10,z22,z5])],[(0,[z0,z1,z7,z912,z4,z5]),(0,[z241,z1,z7,z86,z223,z5]),(0,[z76,z134,z1,z2,z143,z5]),(0,[z0,z142,z1,z2,z80,z5]),(0,[z0,z1,z2,z4,z913,z5]),(0,[z0,z1,z244,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z914]),(0,[z0,z1,z133,z29,z2,z4]),(0,[z0,z1,z7,z2,z4,z915]),(0,[z471,z1,z7,z2,z143,z5]),(0,[z0,z1,z2,z4,z916,z5])],[(0,[z241,z1,z7,z86,z319,z5]),(0,[z0,z1,z2,z4,z5,z917]),(0,[z0,z7,z2,z4,z918,z5])],[],[(0,[z393,z0,z16,z1,z2,z4]),(0,[z919,z0,z1,z7,z2,z5]),(0,[z0,z1,z2,z409,z63,z5])],[(0,[z0,z1,z920,z2,z4,z5]),(0,[z0,z921,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z922])],[(0,[z0,z1,z2,z10,z593,z5])],[(0,[z0,z7,z2,z923,z4,z5]),(0,[z0,z1,z7,z2,z773,z5]),(0,[z0,z1,z2,z4,z5,z924]),(0,[z0,z1,z7,z2,z925,z5]),(0,[z420,z475,z1,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z926])],[(0,[z261,z0,z1,z2,z21,z5]),(0,[z0,z487,z7,z2,z4,z104]),(0,[z164,z0,z2,z4,z390,z90]),(0,[z0,z240,z1,z2,z287,z5]),(0,[z0,z43,z36,z1,z4,z120]),(0,[z0,z1,z927,z2,z4,z5])],[(0,[z0,z1,z29,z2,z4,z562]),(0,[z1,z7,z2,z4,z5,z928]),(0,[z0,z1,z2,z4,z5,z929])],[(0,[z0,z1,z2,z930,z4,z5]),(0,[z434,z842,z1,z2,z4,z5]),(0,[z0,z1,z2,z10,z4,z89]),(0,[z0,z240,z1,z233,z4,z5])],[(0,[z0,z931,z1,z7,z2,z5]),(0,[z932,z0,z1,z2,z4,z5])],[(0,[z0,z9,z442,z2,z4,z5]),(0,[z164,z0,z16,z2,z4,z90]),(0,[z0,z933,z1,z2,z4,z5])],[(0,[z0,z1,z800,z2,z4,z5]),(0,[z0,z1,z2,z4,z934,z5]),(0,[z0,z935,z1,z7,z2,z5])],[(0,[z0,z1,z505,z2,z4,z5]),(0,[z0,z1,z7,z718,z4,z5]),(0,[z0,z1,z2,z102,z4,z39]),(0,[z0,z1,z493,z2,z4,z525])]],
   [[(0,[z0,z1,z7,z2,z936,z5]),(0,[z0,z1,z937,z2,z4,z5]),(0,[z0,z112,z9,z1,z2,z17]),(0,[z0,z1,z255,z2,z597,z5])],[(0,[z0,z1,z2,z938,z4,z5]),(0,[z164,z0,z377,z1,z7,z2])],[(0,[z156,z1,z505,z2,z4,z77]),(0,[z0,z16,z1,z2,z773,z5]),(0,[z0,z1,z2,z939,z4,z5]),(0,[z0,z1,z940,z2,z4,z5])],[(0,[z941,z261,z0,z1,z2,z5]),(0,[z0,z942,z7,z2,z4,z5]),(0,[z0,z1,z943,z2,z4,z5]),(0,[z155,z36,z1,z2,z4,z177]),(0,[z0,z377,z7,z2,z59,z5]),(0,[z0,z1,z2,z4,z944,z5])],[(0,[z0,z945,z1,z2,z4,z5]),(0,[z164,z0,z7,z2,z119,z4]),(0,[z0,z1,z946,z2,z4,z5])],[(0,[z0,z947,z1,z2,z4,z5]),(0,[z0,z16,z229,z2,z123,z5])],[(0,[z0,z1,z948,z7,z2,z4])],[(0,[z0,z1,z2,z10,z4,z247]),(0,[z0,z36,z1,z2,z597,z5]),(0,[z0,z1,z2,z4,z949,z5])],[(0,[z97,z93,z2,z21,z4,z5])],[(0,[z0,z950,z7,z2,z4,z5]),(0,[z0,z1,z2,z21,z223,z5]),(0,[z0,z1,z2,z611,z5,z17]),(0,[z168,z0,z195,z166,z4,z5]),(0,[z0,z1,z2,z751,z70,z5])],[(0,[z0,z1,z31,z2,z4,z5]),(0,[z0,z9,z1,z2,z4,z304]),(0,[z0,z1,z951,z2,z4,z5]),(0,[z156,z650,z1,z7,z2,z4]),(0,[z0,z9,z229,z2,z123,z5]),(0,[z0,z1,z2,z4,z952,z5]),(0,[z0,z1,z2,z953,z4,z5]),(0,[z0,z1,z954,z2,z4,z5]),(0,[z0,z435,z36,z1,z2,z5]),(0,[z0,z1,z810,z2,z4,z5]),(0,[z0,z1,z2,z955,z4,z5])],[(0,[z0,z1,z133,z502,z7,z2]),(0,[z0,z253,z7,z2,z4,z304]),(0,[z0,z1,z2,z21,z319,z5]),(0,[z0,z956,z1,z2,z4,z5])],[(0,[z113,z516,z1,z2,z4,z5]),(0,[z0,z16,z2,z4,z372,z5]),(0,[z0,z1,z7,z2,z797,z5])],[(0,[z219,z804,z7,z2,z4,z5]),(0,[z0,z780,z1,z2,z4,z5]),(0,[z0,z660,z36,z1,z2,z5]),(0,[z0,z957,z1,z2,z4,z5])],[(0,[z97,z9,z93,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z958]),(0,[z0,z9,z1,z718,z4,z5])],[(0,[z0,z1,z7,z2,z959,z5]),(0,[z0,z1,z960,z2,z4,z5]),(0,[z0,z7,z2,z4,z5,z961]),(0,[z0,z1,z2,z22,z132,z5]),(0,[z0,z1,z2,z4,z962,z5])]],
   [[(0,[z0,z1,z2,z4,z5,z963])],[(0,[z0,z1,z7,z4,z5,z964]),(0,[z0,z1,z2,z4,z896,z5])],[(0,[z0,z965,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z966,z5]),(0,[z0,z1,z967,z2,z4,z5]),(0,[z1,z2,z21,z4,z5,z747]),(0,[z0,z1,z7,z2,z4,z562])],[(0,[z0,z1,z7,z2,z968,z5]),(0,[z0,z1,z7,z2,z969,z5]),(0,[z241,z1,z7,z713,z4,z5]),(0,[z168,z0,z16,z166,z4,z5]),(0,[z164,z0,z2,z21,z4,z90]),(0,[z0,z970,z1,z2,z4,z5]),(0,[z0,z1,z2,z971,z4,z5])],[(0,[z0,z1,z972,z2,z4,z5]),(0,[z421,z1,z37,z2,z4,z5]),(0,[z0,z973,z7,z2,z4,z5]),(0,[z1,z7,z2,z4,z725,z77]),(0,[z168,z0,z1,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z974]),(0,[z0,z1,z2,z4,z5,z975]),(0,[z636,z0,z1,z2,z4,z226]),(0,[z0,z976,z1,z7,z2,z4])],[(0,[z0,z1,z977,z2,z4,z5]),(0,[z0,z1,z7,z83,z173,z4]),(0,[z0,z978,z1,z2,z4,z5]),(0,[z0,z229,z467,z2,z123,z5]),(0,[z0,z1,z2,z10,z536,z5]),(0,[z0,z1,z233,z22,z4,z5])],[(1,[z1,z740,z2,z4,z5]),(0,[z0,z16,z2,z4,z477,z5]),(0,[z0,z68,z7,z2,z4,z228]),(0,[z0,z979,z1,z2,z326,z5])],[(0,[z0,z1,z2,z4,z980,z5]),(0,[z0,z769,z2,z21,z4,z5]),(0,[z0,z1,z2,z10,z4,z562])],[(0,[z0,z1,z981,z7,z2,z4]),(0,[z0,z9,z1,z2,z4,z855]),(0,[z0,z1,z982,z2,z4,z5])],[(0,[z0,z1,z175,z2,z4,z374]),(0,[z0,z1,z983,z2,z4,z5]),(0,[z0,z650,z1,z21,z4,z5]),(0,[z0,z249,z213,z2,z4,z5]),(0,[z0,z16,z51,z20,z4,z5]),(0,[z0,z1,z2,z984,z597,z5])],[(0,[z0,z1,z985,z2,z4,z5]),(0,[z0,z1,z637,z21,z4,z5])],[(0,[z0,z986,z1,z2,z4,z5]),(0,[z0,z1,z21,z4,z422,z5])],[(0,[z0,z1,z987,z2,z4,z5]),(0,[z0,z65,z1,z2,z10,z4]),(0,[z0,z16,z1,z2,z4,z562]),(0,[z0,z1,z988,z2,z4,z5]),(0,[z0,z29,z2,z4,z5,z278])],[(0,[z0,z142,z1,z2,z123,z5]),(0,[z0,z68,z29,z2,z4,z59]),(0,[z0,z989,z1,z2,z4,z5]),(0,[z0,z112,z1,z49,z2,z17])],[(0,[z251,z0,z1,z7,z4,z5]),(0,[z0,z1,z133,z2,z10,z4]),(0,[z0,z1,z21,z4,z506,z5]),(0,[z0,z377,z1,z7,z2,z5])],[(0,[z261,z0,z1,z133,z7,z2]),(0,[z0,z1,z24,z2,z4,z304]),(0,[z0,z990,z7,z2,z4,z5]),(0,[z0,z213,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z2,z4,z779]),(0,[z349,z1,z7,z2,z4,z177]),(0,[z0,z769,z2,z63,z4,z5]),(0,[z0,z1,z281,z63,z4,z5])],[(0,[z0,z1,z7,z2,z4,z991]),(0,[z0,z1,z595,z21,z4,z5]),(0,[z592,z110,z1,z2,z4,z5]),(0,[z0,z144,z1,z21,z23,z5])],[(0,[z992,z0,z1,z7,z2,z4]),(0,[z386,z155,z0,z7,z2,z4]),(0,[z0,z36,z1,z2,z625,z5]),(0,[z0,z43,z1,z44,z4,z120])],[(0,[z0,z1,z7,z2,z4,z993]),(0,[z0,z994,z1,z7,z2,z4])],[(0,[z0,z1,z995,z2,z4,z5]),(0,[z0,z16,z600,z2,z4,z5]),(0,[z0,z1,z2,z996,z4,z5]),(0,[z0,z1,z2,z21,z326,z5])],[(0,[z0,z1,z997,z2,z4,z5]),(0,[z0,z998,z253,z2,z4,z5]),(0,[z0,z1,z7,z2,z5,z999])],[(0,[z0,z1,z7,z2,z4,z1000]),(0,[z0,z1,z29,z2,z4,z304]),(0,[z0,z1,z569,z2,z10,z5]),(0,[z0,z36,z1,z2,z4,z1001]),(0,[z1002,z0,z1,z7,z2,z4])],[(0,[z0,z36,z1,z2,z359,z5]),(0,[z241,z9,z1,z86,z4,z5]),(0,[z0,z1,z2,z1003,z4,z5]),(0,[z0,z74,z1,z2,z4,z5]),(0,[z9,z1,z2,z4,z5,z285]),(0,[z0,z1,z7,z2,z4,z1004]),(0,[z0,z1,z1005,z2,z4,z5]),(0,[z777,z386,z0,z2,z4,z5]),(0,[z0,z49,z2,z4,z5,z278])],[(0,[z0,z1,z314,z21,z4,z5]),(0,[z241,z253,z7,z86,z4,z5]),(0,[z1006,z0,z1,z2,z4,z5]),(0,[z0,z43,z1,z7,z4,z120])],[(0,[z0,z1,z1007,z2,z4,z5]),(0,[z168,z0,z74,z2,z4,z5]),(0,[z0,z1,z2,z1008,z4,z5]),(0,[z0,z1,z1009,z2,z4,z5]),(0,[z0,z1010,z1,z2,z4,z5])],[(0,[z0,z1011,z1,z2,z4,z5]),(0,[z0,z1,z1012,z2,z4,z5]),(0,[z0,z1,z29,z730,z4,z5]),(0,[z1013,z0,z1,z2,z4,z5]),(0,[z0,z1014,z1,z2,z4,z5])],[(0,[z0,z1,z2,z1015,z4,z5]),(0,[z0,z1,z493,z2,z4,z562])],[(0,[z0,z16,z1,z502,z2,z5]),(0,[z941,z0,z1,z2,z4,z5]),(0,[z0,z1016,z7,z2,z4,z5]),(0,[z0,z1,z83,z10,z4,z60])],[(0,[z0,z1,z2,z1017,z4,z5]),(0,[z0,z213,z1,z528,z4,z5]),(0,[z0,z1,z7,z818,z4,z5])],[],[(0,[z0,z1,z7,z2,z1018,z5])]],
   [[(0,[z0,z1,z2,z1019,z4,z5]),(1,[z46,z0,z111,z7,z2])],[(0,[z0,z9,z1,z502,z2,z5]),(0,[z0,z1,z2,z1020,z4,z5]),(0,[z0,z1,z2,z1021,z4,z5]),(0,[z0,z1,z7,z4,z797,z5])],[(0,[z251,z0,z7,z166,z4,z5]),(0,[z0,z1,z2,z830,z4,z5]),(0,[z1,z7,z2,z4,z177,z608])],[(0,[z0,z804,z7,z2,z4,z5]),(0,[z261,z0,z36,z1,z2,z5]),(0,[z0,z1,z2,z1022,z4,z5]),(0,[z0,z1,z7,z2,z5,z1023])],[],[(0,[z0,z1,z7,z2,z1024,z5]),(0,[z0,z51,z20,z21,z4,z5]),(0,[z0,z68,z7,z2,z4,z59])],[(0,[z0,z1,z7,z2,z1025,z5]),(0,[z0,z1,z1026,z2,z4,z5])],[(0,[z261,z0,z202,z1,z2,z5]),(0,[z0,z202,z1,z502,z2,z5]),(0,[z0,z9,z555,z2,z4,z5]),(0,[z164,z0,z512,z2,z4,z90])],[(0,[z0,z1,z2,z4,z5,z1027]),(0,[z0,z1,z467,z2,z4,z5]),(0,[z0,z7,z818,z166,z4,z5])],[(0,[z0,z1028,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z1029,z5]),(0,[z164,z0,z539,z7,z2,z4]),(0,[z0,z1,z2,z63,z4,z5]),(0,[z1,z2,z21,z4,z5,z285]),(0,[z0,z1,z95,z2,z896,z5])],[(0,[z0,z1,z7,z270,z22,z5]),(0,[z0,z1,z125,z3,z4,z5]),(0,[z0,z68,z2,z10,z4,z59])],[(0,[z0,z1030,z1,z7,z4,z5]),(0,[z0,z1031,z1,z2,z4,z5]),(0,[z0,z36,z1,z1032,z4,z5]),(0,[z0,z36,z1,z2,z448,z5])],[(0,[z241,z1,z24,z86,z4,z5]),(0,[z0,z1,z7,z599,z4,z60]),(1,[z0,z1,z2,z773,z5]),(0,[z0,z62,z51,z2,z4,z5]),(0,[z0,z1,z175,z2,z4,z482])],[(0,[z0,z1,z2,z611,z143,z5]),(0,[z168,z0,z107,z166,z4,z5])],[(0,[z0,z1,z7,z2,z4,z1033]),(0,[z0,z1,z7,z2,z4,z304]),(0,[z0,z1,z2,z4,z1034,z5]),(0,[z0,z1,z1035,z2,z4,z5])],[(0,[z0,z1,z2,z1036,z4,z5]),(0,[z0,z1037,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z1038,z5]),(0,[z1039,z36,z1,z2,z4,z5]),(0,[z0,z1,z1040,z2,z4,z5])]],
   [[(0,[z0,z253,z2,z21,z4,z5]),(0,[z0,z1,z2,z4,z1041,z5])],[(0,[z594,z1,z54,z2,z4,z5]),(0,[z1,z7,z713,z86,z4,z5]),(0,[z0,z1,z7,z1042,z4,z5]),(0,[z0,z1,z139,z2,z4,z5])],[(0,[z46,z0,z1,z2,z611,z5]),(0,[z0,z1,z2,z4,z1043,z5]),(0,[z1044,z1,z7,z2,z4,z5]),(0,[z0,z1,z2,z21,z5,z302]),(0,[z0,z377,z1,z2,z390,z5]),(0,[z0,z1,z7,z730,z4,z5])],[(0,[z0,z1,z2,z10,z4,z304]),(0,[z241,z1,z29,z86,z4,z5]),(0,[z30,z1,z290,z2,z105,z5]),(0,[z434,z1039,z1,z2,z4,z5]),(1,[z0,z1,z718,z4,z5]),(0,[z0,z16,z1,z2,z1029,z5]),(1,[z0,z1,z730,z4,z5])],[(0,[z241,z65,z1,z7,z86,z4]),(0,[z0,z1,z7,z2,z1045,z5]),(0,[z0,z1,z2,z57,z47,z497])],[(0,[z0,z1,z1046,z2,z4,z5]),(0,[z0,z1,z1047,z2,z4,z5]),(0,[z0,z1048,z1,z2,z4,z5]),(0,[z0,z1049,z1,z2,z4,z5]),(0,[z386,z0,z9,z2,z4,z5]),(1,[z0,z7,z2,z824,z5]),(0,[z0,z1,z2,z4,z158,z1050])],[(0,[z1051,z0,z1,z7,z2,z5]),(0,[z30,z36,z1,z2,z105,z5]),(0,[z156,z337,z1,z7,z2,z4]),(0,[z168,z0,z121,z166,z4,z5]),(0,[z0,z1,z7,z2,z22,z525]),(0,[z386,z0,z7,z2,z4,z120]),(0,[z0,z909,z2,z4,z5,z278])],[(0,[z0,z36,z1,z2,z4,z69]),(0,[z0,z9,z453,z2,z4,z5]),(0,[z0,z16,z2,z248,z4,z5]),(0,[z1052,z1,z7,z2,z4,z5]),(0,[z0,z1053,z1,z2,z4,z5]),(0,[z0,z7,z2,z4,z59,z708])],[(0,[z251,z0,z9,z1,z4,z5]),(0,[z0,z1,z7,z840,z4,z5]),(0,[z0,z16,z1,z2,z4,z304]),(0,[z0,z1,z2,z4,z1054,z5]),(0,[z0,z249,z51,z2,z4,z5])],[(0,[z155,z9,z1,z2,z4,z177]),(0,[z842,z1,z7,z2,z4,z5]),(0,[z0,z112,z16,z1,z2,z17]),(0,[z0,z1055,z1,z2,z4,z5]),(0,[z0,z1,z1056,z2,z4,z5])],[(0,[z0,z1,z316,z2,z4,z78]),(0,[z0,z1057,z1,z2,z4,z5])],[(0,[z0,z1,z2,z1058,z4,z5]),(0,[z0,z62,z2,z199,z4,z5]),(0,[z1,z7,z2,z1059,z4,z5]),(0,[z0,z1,z1060,z2,z4,z5])],[(0,[z0,z36,z1,z2,z665,z5]),(0,[z97,z16,z93,z2,z4,z5]),(0,[z0,z1,z1061,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z855])],[(0,[z0,z1,z198,z2,z4,z5]),(0,[z97,z45,z93,z7,z4,z5]),(0,[z0,z1,z7,z2,z1062,z5]),(0,[z0,z1,z2,z4,z5,z1063]),(0,[z0,z9,z1,z2,z597,z5]),(0,[z0,z1064,z1,z2,z4,z5])],[(0,[z0,z16,z1,z2,z1045,z5]),(0,[z0,z36,z1,z2,z680,z5]),(0,[z0,z1,z1065,z2,z4,z5])],[(0,[z0,z1,z2,z1066,z4,z5]),(0,[z0,z1,z7,z2,z4,z1067]),(0,[z1068,z0,z7,z2,z4,z5]),(0,[z46,z0,z539,z7,z2,z5]),(0,[z0,z2,z923,z21,z4,z5])]],
   [[(0,[z0,z16,z514,z2,z4,z5]),(0,[z0,z1,z270,z21,z4,z5]),(0,[z0,z36,z1,z2,z19,z5]),(0,[z0,z229,z2,z21,z123,z5]),(0,[z0,z1,z2,z34,z4,z381])],[(0,[z0,z1069,z1,z7,z2,z5]),(0,[z0,z1,z214,z2,z70,z5]),(0,[z0,z1,z2,z1070,z4,z5]),(0,[z0,z1071,z1,z2,z4,z5]),(0,[z0,z950,z2,z10,z4,z5])],[(0,[z0,z36,z1,z2,z153,z5]),(0,[z0,z487,z7,z2,z4,z304])],[(0,[z0,z1,z1072,z2,z4,z5]),(0,[z0,z1,z1073,z2,z4,z5]),(0,[z0,z9,z670,z2,z4,z5]),(0,[z0,z1,z195,z2,z4,z5]),(0,[z1074,z1,z29,z2,z4,z5])],[(0,[z366,z93,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z1075,z5]),(0,[z0,z1,z1076,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z1077]),(0,[z0,z1,z2,z21,z4,z176])],[(0,[z0,z1078,z1,z2,z4,z5]),(0,[z1079,z0,z1,z2,z4,z5]),(0,[z164,z0,z377,z7,z2,z90]),(0,[z0,z1,z2,z4,z5,z1080])],[(0,[z97,z353,z93,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z1081]),(0,[z28,z342,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z1082]),(0,[z0,z1,z1083,z2,z4,z5]),(0,[z0,z617,z1,z2,z10,z5])],[(0,[z0,z1,z7,z2,z1084,z5]),(0,[z97,z202,z93,z2,z4,z5]),(0,[z0,z36,z1,z83,z4,z60])],[(0,[z842,z9,z1,z2,z4,z5]),(0,[z0,z1,z179,z21,z4,z5])],[(0,[z0,z1,z2,z4,z1085,z5]),(0,[z0,z1,z2,z4,z390,z5]),(0,[z0,z1,z7,z2,z194,z5]),(0,[z0,z1,z2,z4,z1086,z5]),(0,[z0,z1,z2,z4,z1087,z5])],[(0,[z1088,z0,z1,z2,z4,z5]),(0,[z46,z164,z0,z112,z7,z2]),(0,[z0,z1,z281,z21,z4,z5])],[(0,[z241,z1,z7,z86,z4,z5]),(0,[z0,z1,z7,z2,z4,z1089]),(0,[z0,z249,z56,z2,z4,z5]),(0,[z0,z1,z1090,z2,z4,z5])],[(0,[z0,z1,z2,z4,z106,z861]),(0,[z0,z1,z2,z1091,z4,z5]),(0,[z0,z7,z2,z123,z5,z647]),(0,[z0,z1,z2,z1092,z4,z5])],[(0,[z804,z93,z7,z2,z4,z5]),(0,[z0,z1,z2,z1093,z4,z5]),(0,[z0,z62,z87,z2,z4,z5]),(0,[z0,z1,z2,z1094,z4,z5]),(0,[z0,z1095,z1,z2,z4,z5]),(0,[z0,z1,z7,z4,z752,z120]),(0,[z0,z1,z7,z4,z5,z752])],[(0,[z0,z1096,z1,z7,z4,z5]),(0,[z241,z0,z1,z233,z4,z5]),(0,[z0,z1,z1097,z2,z4,z5]),(0,[z0,z1,z7,z2,z896,z5])],[(0,[z0,z1,z83,z233,z4,z5]),(0,[z682,z1,z2,z238,z4,z5]),(0,[z0,z1098,z1,z2,z4,z5])]],
   [[(0,[z0,z9,z679,z2,z4,z5]),(0,[z0,z1,z2,z1099,z4,z5])],[(0,[z0,z1100,z1,z7,z2,z4]),(0,[z241,z1,z86,z10,z4,z5]),(0,[z0,z1,z21,z4,z504,z5]),(0,[z0,z1,z2,z21,z4,z106]),(0,[z0,z1,z2,z1101,z4,z5]),(0,[z0,z1,z584,z21,z4,z5]),(0,[z0,z1,z2,z4,z1102,z5]),(0,[z0,z1,z2,z21,z4,z525])],[(0,[z0,z36,z1,z2,z488,z5]),(0,[z0,z9,z602,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z1103])],[(0,[z0,z1,z2,z1104,z4,z5]),(0,[z0,z16,z1,z2,z194,z5]),(0,[z0,z1,z1105,z2,z70,z5]),(0,[z0,z111,z36,z1,z2,z4]),(0,[z0,z1,z2,z10,z896,z5]),(0,[z0,z1,z7,z2,z47,z798])],[(0,[z0,z65,z36,z1,z2,z4]),(0,[z0,z1,z7,z2,z4,z1106]),(0,[z1107,z1,z7,z2,z4,z5])],[(0,[z0,z1,z1108,z7,z2,z4]),(0,[z0,z1109,z7,z2,z4,z5]),(0,[z241,z16,z1,z86,z4,z5]),(0,[z0,z1,z1110,z2,z4,z5]),(0,[z155,z1,z29,z2,z4,z177]),(0,[z0,z1,z7,z2,z1111,z5]),(0,[z0,z979,z1,z2,z4,z5])],[(0,[z0,z1,z512,z2,z5,z302]),(0,[z0,z1,z2,z21,z5,z783]),(0,[z0,z1,z21,z4,z5,z578]),(0,[z0,z1112,z1,z2,z4,z5])],[(0,[z0,z1,z740,z2,z4,z5]),(0,[z156,z0,z1,z7,z2,z597]),(0,[z0,z1,z1113,z2,z4,z5]),(0,[z0,z1,z1114,z7,z2,z4])],[(0,[z0,z9,z1,z2,z194,z5]),(0,[z0,z1115,z7,z2,z4,z5]),(0,[z0,z2,z10,z4,z5,z278])],[(0,[z0,z1,z29,z2,z597,z5])],[(0,[z1,z7,z99,z4,z5,z443]),(0,[z190,z342,z1,z2,z4,z5])],[(0,[z0,z1116,z7,z2,z4,z5]),(0,[z0,z1117,z1,z2,z4,z5]),(0,[z0,z1,z2,z1118,z4,z5]),(0,[z1074,z1,z7,z2,z4,z5])],[(0,[z1119,z1,z7,z2,z4,z5])],[(0,[z0,z231,z9,z2,z4,z5]),(0,[z434,z46,z0,z2,z80,z5]),(0,[z0,z1120,z1,z2,z4,z5])],[(0,[z0,z1,z1121,z2,z4,z5]),(0,[z0,z1,z1122,z2,z4,z5])],[(0,[z241,z487,z7,z86,z4,z5]),(0,[z0,z51,z7,z818,z4,z5]),(0,[z0,z51,z7,z20,z4,z176]),(0,[z0,z1,z1123,z2,z4,z5]),(0,[z0,z2,z21,z4,z918,z5]),(0,[z0,z144,z1,z29,z23,z5]),(0,[z0,z1,z22,z4,z26,z5]),(0,[z0,z1124,z1,z2,z4,z5]),(0,[z0,z1,z125,z63,z22,z5])]],
   [[(0,[z0,z1,z1125,z2,z4,z5]),(0,[z28,z1,z740,z2,z4,z5]),(0,[z0,z1,z2,z1126,z4,z5]),(0,[z0,z1127,z1,z2,z4,z5]),(0,[z0,z112,z7,z2,z278,z17])],[(0,[z0,z1,z7,z2,z4,z1128]),(0,[z0,z1,z2,z21,z4,z89]),(0,[z0,z1,z2,z1129,z4,z5]),(0,[z0,z1,z518,z21,z4,z5])],[(0,[z0,z1130,z7,z2,z4,z5]),(0,[z0,z1,z1131,z7,z2,z4]),(0,[z0,z229,z1,z2,z13,z5]),(0,[z0,z1,z7,z2,z4,z926]),(0,[z0,z1,z7,z797,z23,z5])],[(0,[z0,z1,z2,z21,z4,z5]),(0,[z0,z16,z1,z133,z2,z4]),(0,[z0,z1132,z1,z2,z4,z5]),(0,[z30,z1,z7,z2,z899,z5]),(0,[z46,z0,z36,z2,z80,z5]),(0,[z0,z1,z663,z2,z4,z458])],[(0,[z251,z0,z353,z1,z4,z5]),(0,[z251,z0,z1,z10,z4,z5]),(0,[z1088,z261,z0,z1,z2,z5])],[(0,[z0,z1,z1133,z2,z4,z5]),(0,[z0,z1134,z1,z2,z4,z5]),(0,[z0,z1,z2,z896,z185,z5]),(0,[z0,z1135,z1,z2,z4,z5])],[(0,[z156,z1,z2,z21,z4,z77]),(0,[z0,z51,z29,z20,z4,z5]),(0,[z0,z240,z1,z2,z4,z5]),(0,[z0,z1136,z1,z2,z4,z5])],[(0,[z98,z1,z664,z7,z4,z5]),(0,[z0,z9,z546,z2,z4,z5]),(0,[z0,z1,z2,z61,z4,z5]),(0,[z0,z36,z1,z125,z22,z5])],[(0,[z0,z9,z1,z133,z2,z4]),(0,[z0,z229,z7,z2,z824,z5])],[(0,[z0,z353,z1,z502,z2,z5]),(0,[z0,z1,z2,z1137,z4,z5]),(0,[z0,z62,z1,z2,z4,z5]),(0,[z0,z36,z1,z2,z25,z5])],[(0,[z0,z1,z133,z45,z7,z4]),(0,[z0,z998,z1,z2,z4,z5]),(0,[z0,z1,z2,z1138,z4,z5])],[(0,[z0,z1,z339,z21,z4,z5]),(0,[z0,z1,z2,z13,z4,z5]),(0,[z0,z1,z1139,z2,z4,z5]),(0,[z0,z1,z2,z1140,z4,z5]),(0,[z0,z1,z7,z2,z1141,z5])],[(0,[z0,z1,z1142,z2,z4,z5]),(0,[z0,z1143,z1,z2,z4,z5]),(0,[z0,z1144,z1,z2,z4,z5]),(0,[z0,z1,z44,z2,z326,z5])],[(0,[z251,z261,z0,z1,z7,z5]),(0,[z155,z1,z7,z2,z4,z177]),(0,[z0,z1,z2,z21,z4,z247]),(0,[z0,z1,z7,z2,z4,z1145]),(0,[z0,z1,z7,z2,z194,z176])],[(0,[z0,z202,z1,z133,z2,z4]),(0,[z0,z1,z1146,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z1147]),(0,[z0,z43,z1,z10,z4,z120]),(0,[z386,z0,z7,z2,z47,z5])],[(0,[z0,z1,z2,z1148,z4,z5]),(0,[z0,z1149,z7,z2,z4,z5]),(0,[z1,z7,z2,z4,z177,z725]),(0,[z434,z0,z171,z2,z4,z5]),(0,[z0,z1,z2,z440,z194,z5]),(0,[z0,z822,z2,z21,z4,z5])]],
   [[(0,[z0,z1,z7,z1150,z4,z5]),(0,[z0,z1151,z1,z2,z319,z5]),(0,[z0,z36,z1,z2,z567,z5])],[(0,[z0,z1152,z253,z2,z4,z5]),(0,[z434,z0,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z597,z5]),(0,[z0,z1,z7,z2,z4,z1153])],[(0,[z0,z1,z1154,z2,z4,z5]),(0,[z0,z1,z2,z1155,z319,z5]),(0,[z155,z1,z2,z10,z4,z177]),(0,[z0,z1,z2,z4,z5,z1156]),(0,[z0,z1,z29,z589,z4,z5])],[(0,[z0,z889,z1,z2,z4,z5]),(0,[z0,z1,z2,z1157,z4,z5])],[(0,[z0,z1,z7,z2,z4,z1158]),(0,[z434,z0,z1,z2,z13,z5]),(0,[z0,z1,z29,z2,z194,z5]),(0,[z0,z240,z1,z2,z132,z5])],[(0,[z0,z1,z502,z997,z2,z5]),(0,[z241,z643,z1,z7,z4,z5]),(0,[z0,z249,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z1159,z5])],[(0,[z0,z1,z1160,z2,z4,z5]),(0,[z0,z1,z100,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1161]),(0,[z0,z1,z2,z10,z611,z5]),(0,[z0,z1,z2,z10,z597,z5])],[(0,[z0,z487,z2,z21,z4,z5]),(0,[z155,z16,z1,z2,z4,z177]),(0,[z434,z0,z1,z2,z4,z811]),(0,[z0,z1,z107,z2,z4,z5]),(0,[z0,z1,z2,z4,z352,z5]),(0,[z0,z1,z7,z2,z1162,z5]),(0,[z0,z377,z1,z512,z2,z5]),(0,[z0,z1,z82,z2,z4,z5])],[(0,[z0,z1,z7,z2,z1163,z5]),(0,[z0,z1164,z7,z2,z4,z5]),(0,[z0,z653,z1,z2,z10,z5]),(0,[z0,z1165,z1,z2,z4,z5])],[(0,[z0,z1166,z1,z2,z4,z5]),(0,[z386,z0,z7,z2,z22,z5])],[(0,[z261,z0,z1,z45,z7,z5]),(0,[z0,z1,z2,z611,z4,z5]),(0,[z0,z1167,z1,z2,z4,z5])],[(0,[z241,z1,z7,z86,z4,z104]),(0,[z349,z1,z7,z2,z4,z77]),(0,[z0,z377,z9,z1,z2,z5]),(0,[z0,z16,z1,z2,z597,z5]),(0,[z0,z1168,z1,z2,z4,z5]),(0,[z0,z249,z2,z166,z4,z5]),(0,[z0,z1,z20,z233,z4,z5]),(0,[z0,z2,z21,z4,z5,z961])],[(0,[z1,z7,z2,z899,z143,z5]),(0,[z0,z1,z179,z3,z4,z5])],[(0,[z0,z36,z1,z2,z70,z5])],[(0,[z386,z0,z16,z2,z4,z5]),(0,[z0,z51,z7,z20,z4,z5]),(0,[z0,z1,z1169,z2,z4,z5]),(0,[z0,z1,z2,z4,z39,z78]),(0,[z0,z1,z1170,z2,z4,z5])],[]],
   [[(0,[z0,z1,z121,z2,z4,z5]),(0,[z0,z240,z1,z52,z4,z5]),(0,[z0,z1,z2,z1171,z4,z5])],[(0,[z0,z1,z2,z1172,z4,z5]),(0,[z0,z1,z1173,z2,z4,z5]),(0,[z1,z1174,z7,z2,z4,z5]),(0,[z0,z1,z1175,z2,z4,z5]),(0,[z0,z36,z1,z2,z405,z5]),(0,[z0,z36,z1,z2,z5,z92])],[(0,[z0,z1176,z1,z2,z4,z5]),(0,[z0,z16,z1,z2,z1163,z5]),(0,[z0,z111,z1,z7,z2,z4])],[(0,[z0,z1,z1177,z2,z4,z5]),(0,[z0,z65,z1,z7,z2,z4]),(0,[z0,z144,z1,z493,z23,z5])],[(0,[z0,z1,z7,z2,z1178,z4]),(0,[z0,z1179,z1,z2,z4,z5])],[(0,[z0,z1,z133,z7,z2,z4]),(0,[z0,z43,z9,z1,z4,z120]),(0,[z1180,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z1181]),(0,[z0,z1,z1182,z2,z4,z5])],[(0,[z0,z1,z1183,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1184])],[(0,[z0,z1,z7,z1185,z4,z5]),(0,[z76,z36,z1,z2,z143,z5]),(0,[z0,z1,z512,z2,z4,z5]),(0,[z0,z1,z1186,z2,z4,z5])],[(0,[z0,z36,z1,z45,z4,z5]),(0,[z0,z1187,z1,z2,z4,z5]),(0,[z0,z94,z62,z2,z4,z5]),(0,[z0,z51,z7,z20,z4,z247]),(0,[z0,z1,z1188,z2,z4,z5]),(0,[z0,z36,z1,z883,z4,z5])],[(0,[z0,z36,z1,z1189,z4,z5]),(0,[z0,z1,z175,z2,z4,z1050])],[(0,[z0,z1,z1190,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1191]),(0,[z0,z1,z7,z1192,z4,z5])],[(0,[z0,z1193,z1,z45,z4,z5]),(0,[z0,z1,z1194,z7,z2,z4]),(0,[z1195,z0,z1,z2,z4,z5]),(0,[z0,z1,z1196,z2,z4,z5])],[(0,[z393,z0,z1,z29,z2,z4]),(0,[z0,z271,z1,z7,z23,z5])],[(0,[z0,z1,z29,z275,z4,z5]),(0,[z0,z1197,z1,z2,z4,z5]),(0,[z0,z1,z2,z1198,z4,z5]),(0,[z0,z1,z2,z4,z1199,z5]),(1,[z164,z0,z377,z7,z2])],[(0,[z0,z1,z63,z4,z26,z5]),(0,[z0,z1,z7,z2,z597,z120])],[(0,[z0,z1,z1200,z2,z4,z5]),(0,[z0,z1,z7,z2,z591,z47]),(0,[z0,z154,z1,z2,z4,z5]),(0,[z0,z9,z355,z2,z4,z5]),(0,[z0,z16,z800,z2,z4,z5]),(0,[z0,z1,z2,z4,z1201,z5]),(0,[z0,z1,z2,z4,z1202,z5]),(0,[z0,z1,z1203,z2,z4,z5])]],
   [[(0,[z0,z1,z7,z2,z1204,z5]),(0,[z0,z1,z7,z2,z4,z1001])],[(0,[z1,z37,z740,z2,z4,z5]),(0,[z0,z16,z364,z2,z4,z5]),(0,[z0,z1,z2,z10,z194,z5]),(0,[z0,z1,z1205,z2,z4,z5])],[(0,[z0,z1206,z1,z2,z4,z5]),(0,[z0,z1,z395,z21,z4,z5]),(0,[z0,z1,z2,z4,z5,z1207]),(1,[z0,z1,z2,z896,z5]),(0,[z0,z1,z2,z1208,z4,z5]),(0,[z0,z1,z2,z10,z5,z629]),(0,[z0,z1,z2,z4,z5,z1209])],[(0,[z0,z1,z474,z21,z4,z5]),(0,[z0,z1,z2,z21,z4,z104]),(0,[z0,z1,z2,z1210,z4,z5]),(0,[z745,z0,z377,z1,z2,z5]),(0,[z386,z0,z112,z7,z2,z4])],[(0,[z0,z1,z1211,z2,z4,z5]),(0,[z0,z9,z800,z2,z4,z5]),(0,[z386,z0,z2,z21,z4,z5]),(0,[z434,z0,z124,z2,z4,z5]),(0,[z0,z1,z2,z4,z1212,z5])],[(0,[z261,z0,z1,z7,z2,z5]),(0,[z0,z56,z800,z2,z4,z5]),(0,[z0,z1,z1213,z2,z4,z5]),(0,[z0,z1,z7,z125,z797,z5])],[(0,[z0,z1,z7,z2,z4,z1214]),(0,[z0,z1,z7,z2,z194,z247]),(0,[z0,z74,z2,z123,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z36,z1,z2,z138,z5])],[(0,[z0,z7,z2,z4,z5,z1215]),(0,[z410,z0,z9,z2,z4,z5]),(0,[z349,z36,z1,z2,z4,z5])],[(0,[z0,z1,z7,z2,z1216,z5]),(0,[z0,z1,z29,z2,z4,z69]),(0,[z0,z1,z1217,z2,z4,z5]),(0,[z0,z1,z7,z426,z4,z60]),(0,[z0,z1,z125,z21,z22,z5])],[(0,[z0,z1,z7,z2,z1218,z5]),(0,[z0,z1,z7,z2,z1219,z5]),(0,[z76,z0,z142,z1,z2,z5]),(0,[z1220,z0,z1,z2,z4,z5]),(0,[z0,z36,z68,z2,z4,z59]),(0,[z0,z1,z1221,z2,z4,z5])],[],[(0,[z0,z1,z2,z4,z1222,z5]),(0,[z0,z1,z7,z2,z1223,z5])],[(0,[z0,z1,z1224,z2,z4,z5]),(0,[z0,z1225,z1,z2,z4,z5]),(0,[z164,z0,z7,z2,z4,z702]),(0,[z0,z36,z1,z2,z57,z47])],[(0,[z168,z0,z487,z7,z4,z5]),(0,[z0,z1,z29,z2,z4,z1226])],[(0,[z0,z9,z306,z2,z4,z5]),(0,[z272,z553,z1,z2,z4,z5]),(0,[z0,z1,z1227,z2,z4,z5]),(0,[z0,z1,z2,z1228,z4,z5]),(0,[z0,z259,z1,z233,z4,z5])]],
   [[(0,[z251,z0,z1,z1229,z4,z5]),(0,[z46,z0,z7,z2,z80,z5])],[(0,[z0,z1,z2,z1230,z4,z5]),(0,[z0,z1,z2,z1231,z4,z5]),(0,[z0,z1,z400,z21,z4,z5])],[(0,[z167,z0,z1,z2,z611,z5])],[(0,[z0,z1,z45,z7,z4,z5]),(0,[z0,z1,z7,z1232,z4,z5]),(0,[z0,z435,z1,z7,z2,z17]),(0,[z0,z1,z1233,z2,z4,z5])],[(0,[z0,z1234,z1,z2,z4,z5]),(1,[z0,z1,z7,z797,z5])],[(0,[z393,z0,z1,z502,z7,z2]),(0,[z0,z16,z9,z2,z4,z5]),(0,[z0,z1,z7,z1032,z4,z5])],[(0,[z156,z1,z7,z2,z4,z725]),(0,[z1235,z0,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z1236,z5]),(0,[z0,z1,z7,z2,z4,z708]),(0,[z0,z1,z2,z21,z773,z5]),(0,[z0,z1,z7,z2,z347,z17])],[],[(0,[z146,z1,z37,z2,z4,z5]),(0,[z0,z1,z7,z2,z23,z69]),(0,[z46,z0,z111,z7,z2,z4])],[(0,[z1039,z1,z7,z2,z4,z5]),(0,[z1,z7,z2,z4,z1237,z5]),(0,[z0,z1,z29,z83,z4,z60])],[(0,[z0,z1,z7,z4,z5,z1238]),(0,[z241,z1,z7,z478,z4,z5]),(0,[z0,z36,z1,z115,z2,z4]),(0,[z0,z1,z1239,z2,z4,z5]),(0,[z0,z1,z1240,z2,z4,z5]),(0,[z0,z1,z2,z1241,z4,z5])],[(0,[z0,z1,z2,z4,z5,z1242]),(0,[z0,z213,z1,z2,z4,z5])],[(0,[z0,z111,z9,z1,z2,z4]),(0,[z0,z16,z577,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z1243]),(0,[z0,z9,z1,z125,z22,z5]),(0,[z0,z36,z1,z2,z182,z5])],[(0,[z0,z1,z3,z4,z23,z5]),(0,[z0,z1,z2,z4,z5,z1244])],[(0,[z0,z1,z7,z4,z1245,z5]),(0,[z0,z1,z7,z2,z5,z1246]),(0,[z0,z1,z2,z4,z5,z735])]],
   [[(0,[z0,z1,z2,z1247,z4,z5]),(0,[z0,z353,z1,z133,z2,z4]),(0,[z30,z1,z7,z2,z105,z5]),(0,[z76,z1,z2,z449,z143,z5]),(0,[z0,z1,z1248,z2,z4,z5]),(0,[z0,z800,z87,z2,z4,z5]),(0,[z0,z1,z1249,z2,z4,z5]),(0,[z0,z111,z1,z2,z4,z79])],[(0,[z0,z1250,z1,z2,z4,z5]),(0,[z1251,z0,z1,z7,z2,z4]),(0,[z0,z1,z7,z2,z4,z69]),(0,[z0,z16,z509,z2,z4,z5]),(0,[z0,z1,z1252,z2,z4,z5])],[(0,[z0,z62,z2,z166,z4,z5]),(0,[z0,z7,z2,z4,z708,z90]),(0,[z0,z769,z1,z2,z4,z5]),(0,[z0,z144,z1,z233,z4,z5])],[(0,[z406,z1,z54,z2,z4,z5]),(0,[z0,z1,z1253,z2,z4,z5])],[(0,[z0,z1,z29,z652,z4,z5]),(0,[z0,z51,z1,z3,z4,z5]),(0,[z0,z1,z1254,z2,z4,z5])],[(0,[z0,z1,z2,z1255,z4,z5]),(0,[z0,z1,z7,z2,z1256,z5]),(0,[z0,z7,z2,z1257,z4,z5])],[(0,[z0,z1,z45,z10,z4,z5]),(0,[z0,z1,z7,z2,z4,z1226]),(0,[z0,z1,z2,z10,z4,z69]),(0,[z0,z1,z7,z2,z5,z1258])],[(0,[z0,z94,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z96])],[(0,[z393,z0,z1,z2,z10,z4]),(0,[z0,z1,z7,z2,z4,z1259]),(0,[z1039,z9,z1,z2,z4,z5]),(0,[z0,z1,z2,z233,z4,z5]),(0,[z0,z142,z1,z2,z170,z5]),(0,[z0,z1,z2,z4,z5,z1260])],[(0,[z65,z1,z7,z99,z2,z4]),(0,[z0,z1261,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z174,z78])],[(0,[z0,z1,z1262,z2,z4,z5]),(0,[z0,z1263,z1,z7,z2,z4]),(0,[z30,z16,z1,z2,z105,z5]),(0,[z0,z1264,z1,z2,z4,z5]),(0,[z0,z1,z7,z22,z797,z5]),(0,[z0,z1,z7,z2,z57,z626])],[(0,[z0,z16,z1,z2,z4,z69]),(0,[z434,z0,z1,z718,z4,z5]),(0,[z0,z1,z44,z2,z4,z5])],[(0,[z0,z1,z1265,z2,z4,z5]),(0,[z0,z1266,z7,z2,z4,z5]),(0,[z156,z1,z100,z2,z4,z77]),(0,[z0,z1267,z1,z2,z4,z5])],[(0,[z0,z1,z29,z21,z4,z5])],[],[(0,[z261,z0,z9,z1,z2,z5]),(0,[z0,z1,z502,z1224,z2,z5]),(0,[z0,z1,z2,z4,z1268,z5]),(0,[z30,z9,z1,z2,z105,z5])]],
   [[(0,[z0,z1,z1269,z2,z4,z5]),(0,[z0,z9,z1,z2,z4,z69]),(0,[z0,z111,z229,z1,z7,z2]),(0,[z0,z1,z2,z21,z4,z562])],[(0,[z0,z36,z1,z2,z223,z5]),(0,[z0,z1,z1270,z2,z21,z4]),(0,[z0,z1,z7,z83,z4,z60])],[(0,[z46,z0,z670,z7,z2,z5]),(0,[z0,z1,z1271,z2,z4,z5]),(0,[z0,z1,z7,z2,z1272,z5])],[(0,[z0,z1273,z7,z2,z4,z5]),(0,[z0,z36,z1,z2,z319,z5]),(0,[z0,z1,z7,z2,z4,z1274]),(0,[z0,z1275,z1,z2,z4,z5]),(0,[z0,z229,z196,z2,z123,z5])],[(0,[z251,z0,z16,z1,z4,z5]),(0,[z0,z1,z2,z773,z4,z5]),(0,[z0,z377,z16,z1,z2,z5]),(0,[z349,z1,z1276,z2,z4,z5])],[(0,[z0,z1,z2,z4,z1277,z5]),(0,[z0,z36,z487,z2,z4,z5]),(0,[z434,z0,z1,z2,z4,z855]),(0,[z0,z1278,z1,z2,z4,z5])],[(0,[z393,z0,z1,z2,z21,z4]),(0,[z0,z1,z1279,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z1280]),(0,[z0,z1152,z1,z2,z4,z5]),(0,[z0,z1,z1281,z2,z4,z5]),(0,[z0,z1,z7,z72,z4,z120]),(1,[z0,z769,z2,z4,z5])],[(0,[z113,z475,z1,z2,z4,z5])],[(0,[z0,z134,z1,z2,z4,z5]),(0,[z0,z1,z301,z2,z223,z5]),(0,[z156,z1,z7,z2,z4,z304]),(0,[z0,z1,z2,z1282,z4,z5])],[(1,[z0,z800,z2,z4,z5]),(0,[z0,z1,z2,z1283,z4,z5]),(0,[z0,z1,z29,z125,z22,z5]),(0,[z0,z1,z1284,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z1285]),(0,[z0,z1,z301,z2,z319,z5]),(0,[z0,z1,z2,z1286,z21,z5]),(0,[z0,z1,z2,z1287,z4,z5])],[(0,[z0,z1,z1288,z2,z4,z5]),(0,[z0,z1,z2,z1289,z4,z5]),(0,[z0,z16,z1,z83,z4,z60]),(0,[z0,z1,z2,z1290,z4,z5]),(0,[z46,z0,z29,z2,z80,z5])],[(0,[z0,z1,z7,z2,z4,z1291]),(1,[z0,z1,z7,z2,z798])],[(0,[z0,z1,z7,z1292,z4,z5]),(0,[z76,z9,z1,z2,z143,z5]),(0,[z0,z1,z2,z611,z185,z5]),(0,[z0,z1,z2,z1293,z4,z5]),(0,[z0,z1,z2,z10,z5,z684])],[(0,[z0,z9,z1,z883,z4,z5]),(0,[z0,z1,z2,z4,z1294,z5]),(0,[z0,z43,z16,z1,z4,z120]),(0,[z0,z62,z2,z4,z59,z5])],[]],
   [[(0,[z0,z9,z1,z83,z4,z60]),(0,[z0,z1,z214,z2,z4,z176]),(0,[z0,z7,z2,z4,z824,z5]),(0,[z0,z154,z1,z2,z4,z89]),(0,[z0,z1,z29,z398,z4,z5]),(0,[z0,z1,z2,z1295,z4,z5])],[(0,[z0,z1296,z487,z2,z4,z5]),(0,[z0,z1,z1297,z2,z4,z5]),(0,[z0,z1298,z1,z2,z4,z5]),(0,[z0,z1,z2,z10,z688,z5]),(0,[z0,z1,z233,z4,z5,z120])],[(0,[z0,z1,z7,z1299,z4,z5]),(0,[z0,z1,z7,z2,z4,z1300]),(0,[z0,z1,z2,z1301,z4,z5])],[(0,[z0,z1302,z1,z7,z2,z5]),(0,[z0,z832,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1303]),(0,[z0,z144,z36,z1,z23,z5]),(0,[z167,z0,z2,z4,z439,z5])],[(0,[z1,z7,z2,z4,z177,z304]),(0,[z241,z1,z7,z86,z4,z304]),(0,[z0,z1,z7,z2,z4,z1304]),(0,[z0,z1,z2,z4,z5,z1305])],[(0,[z97,z251,z93,z7,z4,z5]),(0,[z147,z219,z429,z2,z4,z5]),(0,[z0,z1306,z1,z2,z4,z5]),(0,[z0,z1,z1307,z2,z4,z5]),(0,[z0,z1,z83,z21,z4,z60]),(0,[z0,z1,z2,z4,z162,z5]),(0,[z0,z1,z255,z2,z326,z5])],[(0,[z0,z36,z253,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1308]),(0,[z0,z1,z7,z2,z4,z1309])],[(0,[z0,z1,z7,z2,z4,z1310])],[(0,[z0,z1151,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z70,z176]),(0,[z0,z1,z730,z21,z4,z5])],[(0,[z0,z9,z549,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1311]),(0,[z1312,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z10,z4,z1304]),(0,[z0,z1,z2,z4,z1050,z78]),(0,[z386,z0,z112,z7,z2,z5])],[(0,[z251,z0,z1,z21,z4,z5]),(0,[z0,z1313,z1,z2,z4,z5]),(0,[z0,z1,z2,z1155,z4,z5]),(0,[z0,z1,z7,z2,z1314,z5]),(0,[z0,z68,z2,z4,z59,z189]),(0,[z0,z1,z244,z125,z22,z5])],[(0,[z1,z804,z7,z2,z4,z5]),(0,[z30,z1,z29,z2,z105,z5]),(0,[z168,z0,z36,z166,z4,z5]),(0,[z0,z1,z1315,z2,z4,z5]),(0,[z0,z1,z1316,z2,z4,z5])],[(0,[z0,z1,z502,z2,z21,z5]),(0,[z0,z1317,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z1318,z5]),(0,[z0,z7,z2,z4,z5,z278]),(0,[z0,z36,z1,z2,z326,z5]),(0,[z0,z1,z49,z2,z4,z5])],[(0,[z0,z1,z1319,z2,z4,z5]),(0,[z0,z1,z7,z451,z23,z5]),(0,[z1,z29,z2,z4,z5,z285])],[(0,[z0,z1,z1320,z2,z4,z5]),(0,[z1,z7,z2,z4,z725,z5]),(0,[z0,z1321,z1,z2,z4,z5])],[(0,[z0,z1,z2,z1322,z4,z5]),(0,[z0,z1,z29,z2,z70,z5]),(0,[z46,z0,z74,z2,z4,z5]),(0,[z0,z1,z1323,z2,z4,z5])]],
   [[(0,[z0,z1,z7,z2,z1324,z5]),(0,[z0,z148,z9,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z1325]),(0,[z0,z1,z179,z233,z4,z5]),(0,[z0,z112,z1,z29,z2,z17]),(0,[z0,z1,z7,z2,z4,z752]),(0,[z386,z0,z7,z2,z57,z4])],[(0,[z0,z1,z7,z2,z1326,z5]),(0,[z30,z1,z7,z2,z105,z106]),(0,[z0,z1,z2,z1327,z4,z5]),(0,[z0,z1,z7,z125,z22,z5])],[(0,[z28,z1,z37,z2,z4,z5]),(0,[z0,z1,z2,z187,z4,z5]),(0,[z43,z1,z7,z4,z285,z120])],[(0,[z0,z1,z1328,z2,z4,z5]),(0,[z0,z9,z1,z2,z57,z47]),(0,[z0,z68,z2,z21,z4,z59])],[(0,[z0,z1,z7,z2,z764,z4]),(0,[z0,z1,z7,z2,z4,z1329]),(0,[z0,z1,z2,z1330,z4,z5]),(0,[z0,z1,z1331,z2,z4,z5]),(0,[z0,z1332,z1,z2,z4,z5]),(0,[z0,z43,z1,z7,z597,z120]),(0,[z0,z1,z1333,z2,z4,z5])],[(0,[z0,z1,z502,z29,z2,z5]),(0,[z0,z1,z7,z2,z47,z346]),(0,[z0,z1,z2,z1334,z4,z5]),(0,[z0,z1,z1335,z2,z4,z5])],[(0,[z0,z1,z1336,z2,z4,z5]),(0,[z0,z1,z196,z2,z4,z5]),(0,[z0,z144,z1,z162,z23,z5]),(0,[z0,z1,z2,z1337,z4,z5])],[(0,[z1338,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z1339]),(0,[z164,z0,z377,z7,z2,z4]),(0,[z0,z1,z2,z21,z1029,z5]),(0,[z0,z1,z2,z4,z5,z1340])],[(0,[z0,z1,z7,z2,z4,z1147]),(0,[z0,z229,z1,z2,z611,z5]),(0,[z46,z0,z2,z10,z80,z5]),(0,[z0,z1341,z1,z2,z4,z5]),(0,[z0,z1,z499,z2,z4,z78]),(0,[z0,z1,z175,z2,z4,z158]),(0,[z386,z0,z2,z4,z5,z96])],[(0,[z76,z1,z29,z2,z143,z5]),(0,[z0,z171,z56,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z1342]),(0,[z0,z1,z29,z186,z4,z5]),(0,[z0,z1,z2,z4,z1343,z5])],[(0,[z97,z261,z93,z7,z2,z5]),(0,[z261,z0,z353,z1,z2,z5]),(0,[z0,z16,z1,z125,z22,z5])],[(0,[z0,z1,z7,z2,z4,z1344]),(0,[z0,z1,z2,z21,z4,z304]),(0,[z0,z1,z414,z21,z4,z5]),(0,[z0,z1,z1345,z2,z4,z5])],[(0,[z0,z1,z2,z1346,z4,z5])],[(0,[z0,z1347,z1,z2,z4,z5]),(0,[z0,z1,z2,z1348,z4,z5])],[(0,[z0,z1,z1349,z2,z4,z5]),(0,[z0,z1,z214,z2,z4,z5]),(0,[z0,z9,z705,z2,z4,z5]),(0,[z0,z16,z2,z4,z439,z5]),(0,[z406,z1,z2,z283,z4,z5])]],
   [[(0,[z0,z1,z7,z2,z1350,z5]),(0,[z0,z65,z9,z1,z2,z4]),(0,[z0,z1,z29,z638,z4,z5])],[(0,[z0,z1,z29,z3,z4,z5]),(0,[z0,z36,z1,z2,z287,z5]),(0,[z349,z1,z7,z2,z4,z47])],[(0,[z147,z219,z7,z2,z4,z5]),(0,[z0,z1,z2,z1351,z4,z5]),(0,[z0,z142,z1,z2,z23,z5]),(0,[z0,z1,z7,z2,z798,z17])],[(0,[z0,z1,z7,z2,z1352,z5]),(0,[z0,z1,z7,z2,z4,z1353])],[(0,[z0,z1,z7,z1354,z4,z5]),(0,[z0,z1355,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1356]),(0,[z386,z0,z7,z2,z4,z60])],[(0,[z0,z1,z2,z4,z1357,z5]),(0,[z0,z1,z1358,z2,z4,z5]),(0,[z113,z1,z740,z2,z4,z5]),(0,[z0,z1,z29,z42,z4,z5]),(0,[z0,z271,z1,z7,z4,z120])],[(0,[z0,z1,z1359,z2,z4,z5]),(0,[z0,z689,z9,z2,z4,z5]),(0,[z0,z1,z2,z4,z1360,z5]),(0,[z0,z1,z2,z4,z5,z1361]),(0,[z0,z1,z1362,z2,z4,z5])],[(0,[z0,z1363,z1,z2,z4,z5]),(0,[z0,z1,z7,z2,z70,z5]),(0,[z0,z1,z1364,z2,z4,z5])],[(0,[z0,z1,z1365,z2,z4,z5]),(0,[z30,z1,z2,z10,z105,z5]),(1,[z0,z7,z818,z4,z5])],[(0,[z0,z1,z1366,z2,z4,z5]),(0,[z0,z1367,z1,z2,z4,z5]),(0,[z0,z1,z214,z2,z4,z247]),(0,[z0,z1,z1368,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z1369]),(0,[z0,z94,z1,z2,z773,z5]),(0,[z0,z1,z2,z1370,z4,z5]),(0,[z0,z1,z2,z4,z5,z1371]),(0,[z0,z36,z1,z2,z5,z302]),(0,[z0,z68,z7,z2,z4,z708]),(0,[z349,z1,z29,z2,z4,z5])],[(0,[z0,z1,z1372,z2,z4,z5]),(0,[z0,z1,z1373,z2,z4,z5]),(0,[z0,z142,z1,z2,z4,z5])],[(0,[z0,z1374,z1,z2,z4,z5]),(0,[z0,z1,z2,z1375,z4,z5]),(0,[z0,z1,z2,z1376,z4,z5])],[(0,[z28,z1,z2,z232,z4,z5]),(0,[z0,z1,z7,z2,z4,z1377]),(0,[z1378,z0,z1,z7,z2,z4]),(0,[z1379,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z1380,z5]),(0,[z0,z1381,z1,z2,z4,z5])],[(0,[z1382,z0,z1,z2,z4,z5]),(0,[z164,z0,z7,z2,z302,z90]),(0,[z1383,z1,z29,z2,z4,z5])],[(0,[z0,z1,z7,z1384,z4,z5]),(0,[z0,z253,z301,z2,z4,z5]),(0,[z46,z0,z9,z2,z80,z5]),(0,[z0,z1,z29,z528,z4,z5]),(0,[z0,z1,z2,z1385,z4,z5]),(0,[z0,z1,z29,z2,z57,z47])]],
   [[(0,[z393,z0,z36,z1,z2,z4]),(0,[z0,z1386,z1,z2,z4,z5]),(0,[z0,z1,z1387,z2,z4,z5]),(0,[z0,z1388,z1,z2,z4,z5]),(0,[z168,z0,z178,z166,z4,z5])],[(0,[z0,z1,z1389,z7,z4,z5]),(0,[z1,z740,z54,z2,z4,z5]),(0,[z76,z1,z7,z2,z143,z5]),(0,[z0,z43,z1,z7,z478,z4]),(0,[z0,z16,z1,z2,z70,z5]),(0,[z0,z1,z1105,z2,z4,z5])],[(0,[z0,z1,z7,z883,z4,z5]),(0,[z0,z1390,z1,z7,z2,z5]),(0,[z0,z144,z1,z7,z23,z5])],[(0,[z251,z0,z1,z502,z7,z5]),(0,[z0,z36,z1,z2,z315,z5]),(0,[z0,z1,z7,z1189,z4,z5]),(0,[z0,z1,z7,z2,z5,z798])],[(0,[z393,z0,z202,z1,z2,z4]),(0,[z0,z1391,z1,z2,z4,z5]),(0,[z0,z1,z2,z57,z611,z5])],[(0,[z0,z1392,z1,z2,z4,z5]),(0,[z0,z213,z51,z20,z4,z5]),(0,[z0,z7,z2,z123,z824,z5])],[(0,[z76,z1,z2,z10,z143,z5]),(0,[z0,z9,z1,z2,z70,z5]),(0,[z0,z893,z1,z2,z4,z5])],[(0,[z0,z1,z7,z2,z4,z1393]),(0,[z0,z1,z2,z21,z194,z5]),(0,[z0,z1,z1394,z2,z4,z5])],[(0,[z0,z253,z7,z2,z223,z5]),(0,[z164,z0,z36,z2,z4,z90]),(0,[z0,z1,z2,z1395,z4,z5])],[(0,[z0,z1396,z7,z2,z4,z5]),(0,[z0,z1,z1397,z2,z4,z106]),(0,[z0,z1,z2,z4,z1398,z5])],[(0,[z0,z253,z7,z2,z319,z5]),(0,[z241,z1,z86,z21,z4,z5]),(0,[z0,z1,z7,z4,z5,z1399]),(0,[z0,z1,z2,z4,z5,z1400])],[(0,[z0,z51,z487,z7,z4,z5]),(0,[z0,z9,z487,z2,z4,z5]),(0,[z76,z16,z1,z2,z143,z5])],[(0,[z0,z16,z1,z45,z4,z5]),(0,[z0,z1,z115,z2,z21,z4]),(0,[z0,z1,z2,z1401,z4,z5]),(0,[z167,z0,z74,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z176]),(0,[z0,z112,z1,z2,z10,z17])],[(0,[z0,z1,z7,z2,z1402,z5]),(0,[z0,z1,z7,z2,z4,z1403]),(0,[z0,z1404,z1,z2,z4,z5]),(0,[z168,z0,z166,z10,z4,z5]),(0,[z0,z211,z1,z7,z2,z17]),(0,[z386,z0,z49,z2,z4,z5])],[(0,[z0,z1,z7,z2,z1405,z5]),(0,[z0,z1,z2,z10,z152,z5]),(0,[z0,z1,z1406,z2,z4,z5]),(0,[z1407,z1,z7,z2,z4,z5]),(0,[z0,z1,z1408,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1409]),(0,[z0,z1,z1410,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z1050])],[(0,[z0,z1411,z1,z2,z4,z5]),(0,[z0,z1,z1412,z2,z5,z302])]],
   [[],[(0,[z0,z9,z1,z45,z4,z5]),(0,[z0,z1,z502,z2,z10,z5]),(0,[z0,z452,z1,z2,z10,z5]),(0,[z0,z1413,z1,z2,z4,z5]),(0,[z0,z94,z51,z20,z4,z5]),(0,[z0,z1,z1414,z2,z4,z5]),(0,[z0,z1,z1415,z2,z4,z5])],[(0,[z349,z1,z7,z2,z4,z5]),(0,[z241,z65,z1,z7,z2,z4]),(0,[z155,z1,z7,z624,z2,z4]),(0,[z0,z111,z154,z1,z2,z4])],[(0,[z0,z1416,z7,z2,z4,z5]),(0,[z0,z171,z1,z2,z4,z5]),(0,[z46,z0,z7,z2,z668,z5]),(0,[z349,z68,z1,z7,z2,z4]),(0,[z0,z1,z7,z2,z1417,z5])],[(0,[z311,z1,z54,z2,z4,z5]),(1,[z1,z7,z2,z899,z5]),(0,[z0,z144,z1,z4,z26,z5]),(0,[z0,z1,z1276,z2,z4,z5])],[(0,[z0,z1,z2,z4,z1418,z5])],[(0,[z0,z1,z207,z2,z10,z5]),(0,[z0,z65,z1,z1419,z2,z4]),(0,[z0,z1420,z1,z2,z4,z5]),(0,[z0,z1115,z2,z21,z4,z5]),(0,[z1383,z1,z7,z2,z4,z5])],[(0,[z0,z202,z1,z45,z4,z5]),(0,[z0,z1,z2,z1421,z4,z5]),(0,[z0,z229,z7,z2,z498,z5]),(0,[z349,z1,z2,z10,z4,z5]),(0,[z0,z1,z7,z2,z57,z47])],[(0,[z251,z0,z1,z1422,z4,z5]),(0,[z0,z74,z219,z2,z4,z5]),(0,[z241,z1,z7,z115,z86,z4]),(0,[z168,z0,z7,z166,z4,z5]),(0,[z0,z1,z1423,z2,z4,z5]),(0,[z0,z1,z1424,z2,z4,z5]),(0,[z0,z1,z125,z187,z22,z5]),(0,[z0,z1,z1425,z2,z4,z5]),(0,[z0,z1,z2,z1426,z4,z5])],[(0,[z0,z36,z1,z2,z4,z106]),(0,[z155,z1,z276,z7,z2,z4]),(0,[z0,z1,z7,z2,z1427,z5])],[(0,[z0,z1,z2,z4,z26,z5]),(0,[z1119,z1,z2,z21,z4,z5]),(0,[z0,z112,z1,z2,z21,z17])],[(0,[z0,z1,z2,z135,z4,z5]),(0,[z0,z1,z1397,z2,z4,z5]),(0,[z0,z111,z7,z2,z123,z4]),(0,[z0,z1,z2,z4,z158,z226])],[(0,[z0,z1,z24,z2,z223,z5]),(0,[z349,z16,z1,z2,z4,z5]),(0,[z0,z1,z1428,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1429]),(0,[z0,z1,z2,z1430,z4,z5]),(0,[z0,z1,z2,z10,z57,z47]),(0,[z0,z1,z83,z61,z4,z60])],[(0,[z147,z219,z29,z2,z4,z5]),(0,[z168,z0,z1,z395,z4,z5]),(0,[z0,z1431,z1,z7,z2,z5]),(0,[z0,z1,z2,z440,z70,z5]),(0,[z0,z1,z2,z4,z1432,z5])],[(0,[z0,z1,z24,z2,z319,z5]),(0,[z0,z16,z68,z2,z4,z59]),(0,[z0,z1,z2,z10,z4,z1309])],[(0,[z0,z74,z93,z2,z4,z5]),(0,[z0,z1433,z1,z2,z4,z5]),(0,[z0,z1,z2,z1434,z4,z5])]],
   [[],[(0,[z0,z1,z7,z2,z567,z17]),(0,[z349,z9,z1,z2,z4,z5]),(0,[z0,z16,z1,z2,z57,z47]),(0,[z0,z1,z7,z83,z4,z752])],[(0,[z0,z1,z2,z1435,z4,z5]),(0,[z0,z51,z541,z7,z4,z5]),(0,[z0,z9,z1,z2,z326,z5]),(0,[z0,z1,z282,z2,z4,z5]),(0,[z0,z51,z7,z20,z194,z5]),(0,[z46,z0,z154,z2,z80,z5])],[(0,[z0,z1,z29,z2,z223,z5]),(1,[z1,z7,z713,z4,z5]),(0,[z0,z9,z68,z2,z4,z59]),(0,[z0,z1,z7,z2,z340,z47])],[(0,[z0,z1,z2,z1436,z4,z5]),(0,[z0,z1,z7,z115,z2,z4]),(0,[z0,z1,z255,z2,z4,z5])],[(0,[z0,z16,z15,z2,z4,z5]),(0,[z0,z1,z29,z2,z319,z5]),(0,[z0,z1437,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z1438,z5])],[(0,[z0,z1,z1439,z2,z4,z5]),(0,[z0,z1,z1440,z2,z4,z5]),(0,[z0,z1,z1441,z2,z4,z5]),(0,[z0,z1,z2,z4,z1442,z5])],[(0,[z0,z1443,z1,z7,z2,z4]),(0,[z164,z349,z1,z7,z2,z4]),(0,[z0,z43,z1,z21,z4,z120])],[(0,[z0,z1444,z1,z2,z4,z5]),(0,[z0,z1,z290,z2,z4,z5]),(0,[z0,z1,z7,z2,z4,z1445]),(0,[z0,z1,z1446,z2,z4,z5]),(0,[z0,z249,z9,z2,z4,z5]),(0,[z0,z16,z74,z2,z4,z5]),(0,[z0,z1,z2,z1447,z4,z5]),(0,[z0,z1,z233,z166,z4,z5])],[(0,[z0,z1,z1448,z2,z4,z5]),(0,[z0,z36,z1,z2,z4,z89]),(0,[z1,z2,z10,z4,z5,z285])],[(0,[z0,z1,z1422,z2,z4,z5]),(0,[z447,z516,z1,z2,z4,z5])],[(0,[z0,z36,z1,z2,z4,z5]),(0,[z0,z1449,z1,z2,z4,z5]),(0,[z155,z1,z2,z21,z4,z177])],[(0,[z0,z1,z2,z1450,z4,z5]),(0,[z0,z1,z2,z4,z1451,z5]),(0,[z0,z16,z254,z2,z4,z5]),(0,[z0,z1,z2,z1452,z4,z5]),(0,[z0,z1,z297,z2,z4,z5])],[(0,[z147,z0,z62,z2,z4,z5]),(0,[z164,z0,z29,z2,z4,z90]),(0,[z0,z1,z2,z10,z4,z1445])],[(0,[z0,z1193,z1,z2,z4,z5]),(0,[z0,z16,z1,z115,z2,z4]),(0,[z156,z36,z1,z2,z4,z77]),(0,[z0,z1,z2,z4,z5,z1453]),(0,[z0,z36,z1,z2,z13,z5]),(0,[z0,z371,z171,z2,z4,z5])],[(0,[z393,z0,z1,z7,z2,z4]),(0,[z0,z1,z1419,z2,z4,z5]),(0,[z0,z1,z2,z21,z597,z5])]],
   [[(0,[z251,z393,z0,z1,z7,z4]),(0,[z0,z1,z7,z2,z5,z1454]),(0,[z0,z1,z7,z2,z1455,z5]),(0,[z0,z1,z1456,z2,z4,z5])],[(0,[z0,z1,z2,z4,z1457,z5]),(0,[z0,z7,z20,z818,z4,z5]),(0,[z46,z0,z111,z7,z2,z5]),(0,[z0,z36,z1,z2,z4,z811]),(0,[z0,z1,z234,z2,z4,z1050]),(0,[z0,z1,z2,z4,z5,z1458])],[(0,[z0,z1,z7,z2,z1459,z5]),(0,[z0,z1,z301,z2,z4,z5]),(0,[z0,z1,z568,z21,z4,z5]),(0,[z1460,z1,z7,z2,z4,z5]),(0,[z0,z1,z7,z4,z60,z752])],[(0,[z0,z1,z2,z10,z50,z5]),(0,[z0,z9,z1,z115,z2,z4]),(0,[z631,z1,z441,z2,z4,z5]),(0,[z0,z144,z1,z7,z23,z525]),(0,[z349,z1,z7,z83,z2,z4])],[(0,[z0,z1,z7,z2,z4,z1461]),(0,[z0,z1,z1462,z2,z4,z5]),(0,[z0,z94,z1,z395,z4,z5])],[(0,[z164,z0,z683,z7,z2,z4]),(0,[z0,z36,z1,z2,z4,z247]),(0,[z0,z1,z1463,z2,z4,z5]),(0,[z0,z1,z2,z742,z326,z5])],[(0,[z0,z1,z2,z1464,z4,z5]),(0,[z0,z112,z142,z1,z2,z5]),(0,[z0,z36,z2,z4,z5,z278]),(0,[z0,z43,z1,z7,z4,z752])],[(0,[z0,z1296,z1,z2,z4,z5]),(0,[z0,z1,z1465,z2,z4,z5]),(0,[z0,z1,z2,z1466,z4,z5])],[(0,[z0,z1,z7,z2,z1467,z5]),(0,[z0,z1,z1468,z2,z4,z5]),(0,[z0,z111,z16,z1,z2,z4]),(0,[z0,z1,z2,z4,z1050,z5])],[(0,[z0,z65,z16,z1,z2,z4]),(0,[z0,z36,z1,z2,z132,z5])],[(0,[z97,z93,z7,z2,z4,z5]),(0,[z147,z219,z2,z10,z4,z5]),(0,[z0,z1,z7,z2,z4,z1469])],[(0,[z0,z1,z7,z2,z223,z5]),(0,[z0,z94,z1,z2,z1029,z5]),(0,[z0,z36,z1,z2,z181,z5])],[(0,[z97,z502,z93,z7,z2,z5]),(0,[z0,z1,z2,z1470,z4,z5]),(0,[z0,z1,z2,z4,z79,z5]),(0,[z0,z16,z1,z2,z1459,z5]),(0,[z0,z1,z7,z2,z1471,z5]),(0,[z0,z1472,z1,z2,z4,z5])],[(0,[z0,z1,z7,z2,z319,z5]),(0,[z0,z36,z1,z12,z2,z5]),(0,[z0,z1,z2,z984,z4,z5])],[(0,[z0,z1,z7,z2,z4,z1473]),(0,[z0,z1474,z1,z2,z4,z5]),(0,[z0,z1,z29,z2,z326,z5]),(0,[z0,z1475,z1,z2,z4,z5]),(0,[z136,z0,z1,z2,z4,z404])],[(0,[z0,z1,z1476,z2,z4,z5]),(0,[z0,z1,z415,z2,z4,z5]),(0,[z0,z1,z2,z10,z70,z5]),(0,[z0,z94,z2,z248,z4,z5]),(0,[z1477,z0,z7,z2,z4,z5])]],
   [[(0,[z0,z1,z7,z2,z1478,z5]),(0,[z0,z1,z2,z10,z223,z5]),(0,[z0,z9,z1,z2,z5,z302]),(0,[z0,z1,z1412,z2,z4,z5]),(0,[z0,z931,z1,z2,z21,z5]),(0,[z0,z1,z1479,z2,z4,z5])],[(0,[z0,z1,z115,z2,z10,z4]),(0,[z0,z1480,z1,z2,z4,z5])],[(0,[z0,z1,z2,z10,z319,z5]),(0,[z0,z935,z1,z2,z21,z5])],[(0,[z1,z7,z2,z105,z899,z5]),(0,[z434,z0,z1,z2,z19,z5]),(0,[z168,z0,z29,z166,z4,z5]),(0,[z0,z1,z2,z1481,z4,z5]),(0,[z0,z1,z2,z4,z5,z1482])],[(0,[z98,z1,z99,z135,z4,z5]),(0,[z0,z1,z7,z2,z70,z247]),(0,[z0,z1,z7,z2,z4,z1483]),(0,[z311,z1,z2,z360,z4,z5])],[(0,[z0,z1,z429,z2,z4,z5]),(0,[z147,z804,z7,z2,z4,z5]),(0,[z0,z16,z1,z2,z223,z5]),(0,[z0,z9,z2,z4,z206,z5]),(0,[z0,z1,z585,z21,z4,z5]),(0,[z164,z0,z7,z2,z4,z90]),(0,[z0,z1053,z377,z1,z2,z5]),(0,[z0,z1,z186,z4,z26,z5])],[(0,[z0,z1484,z1,z2,z4,z5]),(0,[z0,z1485,z1,z2,z4,z5]),(0,[z0,z112,z1,z7,z2,z182]),(0,[z0,z2,z63,z4,z918,z5])],[(0,[z0,z16,z1,z2,z319,z5]),(0,[z1486,z1,z7,z2,z4,z5])],[(0,[z30,z1,z31,z2,z105,z5]),(0,[z0,z1,z7,z2,z1487,z5]),(0,[z349,z43,z1,z7,z2,z4])],[(0,[z0,z16,z487,z2,z4,z5]),(0,[z0,z1,z761,z2,z4,z5]),(0,[z0,z1488,z1,z2,z4,z5]),(0,[z0,z1,z2,z1489,z4,z5]),(0,[z0,z769,z7,z2,z4,z5]),(0,[z349,z1,z7,z2,z4,z17])],[(0,[z0,z1,z2,z1490,z4,z5]),(0,[z251,z0,z1,z133,z7,z4]),(0,[z0,z9,z1,z2,z223,z5]),(0,[z0,z1,z178,z2,z4,z5]),(0,[z164,z0,z2,z10,z4,z90])],[(0,[z261,z0,z16,z1,z2,z5])],[(0,[z0,z9,z1,z2,z319,z5]),(0,[z0,z1,z1491,z2,z4,z5]),(1,[z386,z0,z112,z7,z2])],[(0,[z0,z1492,z7,z2,z4,z5]),(0,[z0,z1,z1493,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1494])],[(0,[z147,z36,z219,z2,z4,z5]),(0,[z0,z1,z2,z105,z611,z5]),(0,[z0,z1,z2,z4,z5,z1495]),(0,[z0,z1,z7,z2,z57,z798])],[(0,[z0,z16,z554,z2,z4,z5]),(0,[z0,z487,z7,z2,z223,z5]),(0,[z0,z1496,z7,z2,z4,z5]),(0,[z0,z1,z29,z115,z2,z4]),(0,[z164,z0,z7,z2,z4,z428]),(0,[z0,z1,z2,z1497,z4,z5])]],
   [[(0,[z0,z1,z2,z1498,z4,z5]),(0,[z1195,z386,z0,z2,z4,z5])],[(0,[z0,z487,z7,z2,z319,z5]),(0,[z76,z1,z7,z2,z899,z5]),(0,[z0,z1,z1499,z2,z4,z5]),(0,[z1500,z0,z1,z2,z4,z5]),(0,[z0,z1,z200,z2,z4,z5]),(0,[z0,z142,z1,z2,z10,z5]),(0,[z0,z1,z2,z4,z1501,z5])],[(0,[z0,z1502,z1,z2,z4,z5]),(1,[z0,z1,z2,z4,z1050])],[(0,[z0,z1,z1229,z2,z4,z5]),(0,[z0,z253,z24,z2,z4,z5]),(0,[z0,z9,z2,z4,z5,z228]),(0,[z46,z0,z7,z2,z89,z80]),(0,[z386,z0,z112,z7,z2,z17])],[(0,[z0,z36,z1,z2,z430,z5]),(0,[z0,z1,z7,z2,z22,z69]),(0,[z0,z1,z7,z2,z1503,z5]),(0,[z0,z112,z36,z1,z2,z17])],[(0,[z0,z36,z1,z2,z431,z5]),(0,[z0,z9,z87,z2,z4,z5]),(0,[z0,z1,z29,z233,z4,z5])],[(0,[z0,z112,z336,z1,z7,z2]),(0,[z0,z1,z7,z2,z326,z5])],[(0,[z393,z0,z1,z45,z7,z4]),(0,[z0,z1,z7,z2,z57,z676]),(0,[z0,z1504,z7,z2,z4,z5])],[(0,[z0,z1,z1505,z2,z4,z5]),(0,[z0,z1,z1506,z2,z4,z5]),(0,[z0,z1507,z1,z2,z4,z5]),(0,[z0,z2,z21,z4,z5,z278]),(0,[z0,z144,z1,z10,z23,z5])],[(0,[z0,z1,z1508,z7,z4,z5]),(0,[z0,z353,z1,z45,z4,z5]),(0,[z0,z1,z2,z1509,z4,z5]),(0,[z0,z1510,z7,z2,z4,z5]),(0,[z0,z1,z29,z246,z4,z5]),(0,[z0,z1,z2,z4,z1511,z5])],[(0,[z0,z1,z1512,z2,z4,z5]),(0,[z0,z253,z29,z2,z4,z5]),(0,[z0,z16,z253,z2,z4,z5]),(0,[z0,z650,z1,z7,z4,z120]),(0,[z0,z1,z2,z1157,z194,z5]),(0,[z0,z1,z7,z2,z824,z5]),(0,[z0,z1,z1513,z2,z4,z5])],[(0,[z0,z36,z1,z2,z4,z104]),(0,[z0,z9,z2,z239,z4,z5]),(0,[z0,z1514,z1,z2,z4,z5]),(0,[z0,z1,z7,z33,z22,z5]),(0,[z0,z1,z2,z10,z326,z5])],[(0,[z0,z1,z1515,z2,z4,z5]),(0,[z0,z1,z29,z2,z5,z302]),(0,[z0,z36,z1,z2,z4,z525])],[(0,[z98,z1,z29,z99,z4,z5]),(0,[z0,z1,z2,z1516,z4,z5])],[(0,[z0,z1517,z7,z2,z4,z5]),(0,[z46,z0,z2,z21,z80,z5])],[(0,[z0,z1,z7,z2,z4,z1518]),(0,[z0,z1,z2,z1519,z4,z5]),(0,[z0,z9,z253,z2,z4,z5]),(0,[z0,z1520,z1,z2,z4,z5]),(0,[z30,z1,z218,z7,z2,z5]),(0,[z0,z16,z2,z4,z5,z129]),(0,[z0,z229,z415,z2,z123,z5]),(0,[z0,z73,z1,z2,z4,z572]),(0,[z0,z2,z10,z4,z918,z5]),(0,[z0,z144,z1,z200,z23,z5]),(0,[z0,z144,z1,z7,z23,z562]),(0,[z0,z240,z1,z125,z22,z5])]],
   [[(0,[z0,z16,z552,z2,z4,z5]),(0,[z0,z16,z1,z2,z326,z5]),(0,[z0,z1,z2,z1521,z4,z5]),(0,[z0,z1,z139,z2,z57,z47])],[(0,[z0,z1,z7,z2,z4,z1522]),(0,[z164,z0,z9,z2,z4,z90])],[(0,[z0,z1,z301,z2,z4,z104]),(0,[z0,z229,z387,z7,z2,z5]),(0,[z46,z0,z2,z79,z80,z5]),(0,[z0,z377,z1,z2,z21,z5]),(0,[z0,z1,z2,z5,z302,z1409]),(0,[z0,z1,z2,z4,z1523,z5]),(0,[z0,z1,z1524,z2,z4,z5])],[(0,[z0,z1,z7,z2,z1286,z5])],[(0,[z0,z1,z7,z2,z4,z1525]),(0,[z0,z1,z1526,z2,z4,z5]),(0,[z167,z0,z1,z2,z210,z5]),(0,[z46,z0,z171,z2,z4,z5]),(0,[z0,z7,z2,z4,z5,z708]),(0,[z0,z1,z1527,z2,z4,z5])],[(0,[z97,z93,z29,z2,z4,z5]),(0,[z0,z1,z2,z1528,z4,z5]),(0,[z0,z1,z7,z2,z899,z5]),(0,[z1529,z0,z1,z2,z4,z5]),(0,[z0,z1,z1530,z2,z4,z5])],[(0,[z0,z1,z88,z21,z4,z5]),(0,[z0,z1,z29,z2,z4,z732])],[(0,[z0,z1,z7,z2,z1531,z5]),(0,[z331,z1,z2,z232,z4,z5]),(0,[z0,z1532,z1,z2,z4,z5]),(0,[z0,z36,z1,z912,z4,z5]),(0,[z0,z1,z1533,z2,z4,z5])],[],[(0,[z46,z0,z1,z2,z13,z5]),(0,[z0,z1,z2,z440,z4,z176]),(0,[z0,z1,z234,z2,z4,z78]),(0,[z0,z1,z1534,z2,z4,z5]),(0,[z0,z1,z1535,z2,z4,z5])],[(0,[z272,z1,z54,z2,z4,z5]),(0,[z0,z9,z245,z2,z4,z5])],[(0,[z251,z0,z1,z29,z4,z5]),(0,[z0,z1536,z7,z2,z4,z5]),(0,[z0,z1,z7,z2,z223,z104]),(0,[z0,z1537,z1,z2,z4,z5]),(0,[z0,z377,z1,z29,z2,z5])],[(0,[z0,z36,z1,z2,z462,z5]),(0,[z1538,z0,z1,z2,z4,z5])],[(0,[z0,z1,z502,z45,z7,z5]),(0,[z0,z1,z7,z2,z5,z1539]),(0,[z0,z1,z1270,z7,z2,z4]),(0,[z0,z1,z7,z2,z319,z104]),(0,[z36,z1,z2,z4,z5,z285]),(0,[z0,z1,z234,z2,z4,z572])],[(0,[z0,z1,z7,z2,z1540,z5]),(0,[z0,z1,z7,z2,z4,z1541]),(0,[z0,z1,z7,z2,z4,z712]),(0,[z30,z1,z2,z21,z105,z5]),(0,[z0,z7,z2,z818,z4,z5]),(0,[z0,z1542,z1,z7,z2,z4]),(0,[z0,z1,z29,z2,z4,z176]),(0,[z0,z1543,z1,z2,z4,z5])],[(0,[z0,z1,z45,z21,z4,z5]),(0,[z0,z1,z2,z21,z4,z69]),(0,[z0,z1,z1544,z2,z4,z5]),(0,[z0,z9,z171,z2,z4,z5]),(0,[z0,z144,z9,z1,z23,z5]),(0,[z0,z1,z499,z2,z4,z145]),(0,[z421,z530,z1,z2,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 490) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 490).take 496) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 986).take 490) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1476).take 76) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1552)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [490, 496, 490, 76] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 113).take 126).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 239).take 129).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 368).take 119).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 487).take 25).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [113, 126, 129, 119, 25] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

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

end PEqualNP.Outside.L_meta_37473

theorem PEqualNP.Outside.L_meta_37473 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241856 * 2 ^ 32 + 3974684864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241856 * 2 ^ 32 + 3974684864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37473.solve