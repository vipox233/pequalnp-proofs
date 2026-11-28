import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38769

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4236830856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0010904258850d59#64 ++ 0x40010904258850d5#64 ++ 0x5031f3c7d88f1fff#64 ++ 0xa5031f3c7d88f1ff#64 : BitVec 256),
   (0x00c64519203a62a2#64 ++ 0x800c64519203a62a#64 ++ 0xf1ce4d3920ffe3ff#64 ++ 0x7f1ce4d3920ffe3f#64 : BitVec 256),
   (0x160b8a2e2b0cb4c3#64 ++ 0x0160b8a2e2b0cb4c#64 ++ 0x7e0f8e3e3f0cfcce#64 ++ 0xf7e0f8e3e3f0cfcc#64 : BitVec 256),
   (0x2b700fc015d0db0c#64 ++ 0x02b700fc015d0db0#64 ++ 0xbff00fc03ff0ff0d#64 ++ 0xfbff00fc03ff0ff0#64 : BitVec 256),
   (0x8dbff0003eef0000#64 ++ 0x08dbff0003eef000#64 ++ 0xaffff0003fff000b#64 ++ 0xeaffff0003fff000#64 : BitVec 256),
   (0x4fed6fb580000000#64 ++ 0x04fed6fb58000000#64 ++ 0xcfffffffc0000007#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [9, 5]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x0031b2c6c0000000 0x80031b2c6c000000

def z1 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x5031f3c7d88f1fff 0xa5031f3c7d88f1ff

def z2 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1ce4d3920ffe3ff 0x7f1ce4d3920ffe3f

def z3 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0f8e3e3f0cfcce 0xf7e0f8e3e3f0cfcc

def z4 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbff00fc03ff0ff0d 0xfbff00fc03ff0ff0

def z5 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xcfffffffc0000007 0xfcfffffffc000000

def z6 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xaffff0003fff000b 0xeaffff0003fff000

def z7 : W := mkw 0x0010104050810918 0x4001010405081091 0x0000000000830330 0x0000000000083033

def z8 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x500f8e3e000cfcc6 0x1500f8e3e000cfcc

def z9 : W := mkw 0x42509ff7d8850d59 0x442509ff7d8850d5 0x5031ffffd88f1fff 0xb5031ffffd88f1ff

def z10 : W := mkw 0x8930300014c10000 0x08930300014c1000 0x0030300000000000 0x0003030000000000

def z11 : W := mkw 0x297005c014d04b0c 0x0297005c014d04b0 0x81f001c000f00301 0x081f001c000f0030

def z12 : W := mkw 0x0b709fc258850d59 0x40b709fc258850d5 0xdff1ffc7d88f1fff 0xfdff1ffc7d88f1ff

def z13 : W := mkw 0x0000904248050d59 0x40000904248050d5 0x5001f3c7c00f1ff6 0x05001f3c7c00f1ff

def z14 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xcfce4d3900000007 0x7cfce4d390000000

def z15 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xb1ce0d3820f0e30d 0x7b1ce0d3820f0e30

def z16 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xafce000027700000 0x4afce00002770000

def z17 : W := mkw 0x8def6519267a62a2 0x88def6519267a62a 0xffce4d3927ffe3ff 0x7ffce4d3927ffe3f

def z18 : W := mkw 0x0002000820082082 0x0000200082008208 0x700e0c38200ce0ce 0x7700e0c38200ce0c

def z19 : W := mkw 0x16cfcf3f2b3ef6e3 0x816cfcf3f2b3ef6e 0xffcfcf3f3fffffff 0xfffcfcf3f3ffffff

def z20 : W := mkw 0x7fffefffbfdcffcf 0x07fffefffbfdcffc 0xfffffffffffcffcf 0xffffffffffffcffc

def z21 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xaff000003ff00009 0xeaff000003ff0000

def z22 : W := mkw 0x49e4659180000000 0x049e465918000000 0x81f071c1c0000001 0x081f071c1c000000

def z23 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xafce400027ff000b 0x6afce400027ff000

def z24 : W := mkw 0x0000800208040441 0x0000080020804044 0x40018006000c00c2 0x040018006000c00c

def z25 : W := mkw 0x4ffd7ff5d0810918 0x44ffd7ff5d081091 0xcfffffffc0830337 0xfcfffffffc083033

def z26 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x10000000188f1ff8 0x010000000188f1ff

def z27 : W := mkw 0x448d603580000000 0x0448d60358000000 0x400ff03fc0000002 0x0400ff03fc000000

def z28 : W := mkw 0x0010900018850000 0x0001090001885000 0x0031f000188f000b 0xa0031f000188f000

def z29 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xfffff3c7ffff1fff 0xefffff3c7ffff1ff

def z30 : W := mkw 0x0dad600000000000 0x00dad60000000000 0x8fce000000000000 0x48fce00000000000

def z31 : W := mkw 0xafffffc03fffdb0c 0x0afffffc03fffdb0 0xbfffffc03fffff0f 0xfbfffffc03fffff0

def z32 : W := mkw 0x00020008203a62a2 0x800020008203a62a 0x3000000020ffe3f8 0x03000000020ffe3f

def z33 : W := mkw 0x00400519001062a2 0x800400519001062a 0x50000d390000e3f4 0x150000d390000e3f

def z34 : W := mkw 0x8d39b0001ec50000 0x08d39b0001ec5000 0x0e31b0001f000000 0x80e31b0001f00000

def z35 : W := mkw 0x0b600f8000000000 0x00b600f800000000 0x8ff00fc000000005 0xf8ff00fc00000000

def z36 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x10000fc00000ff04 0x110000fc00000ff0

def z37 : W := mkw 0x140b802e2a0c24c3 0x0140b802e2a0c24c 0x6e0f803e3f0c00ca 0xe6e0f803e3f0c00c

def z38 : W := mkw 0x801290003eef0000 0x0801290003eef000 0x200000003fff0008 0x0200000003fff000

def z39 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xfff04fc13fffffff 0xffff04fc13ffffff

def z40 : W := mkw 0x00d6d55b78bf6ffb 0xc00d6d55b78bf6ff 0xf1fffffff8ffffff 0xff1fffffff8fffff

def z41 : W := mkw 0x16098a260b049441 0x016098a260b04944 0x0e0182061f001c00 0x80e0182061f001c0

def z42 : W := mkw 0x4fed6fb580104200 0x04fed6fb58010420 0xffffffffe0f0e30f 0xfffffffffe0f0e30

def z43 : W := mkw 0x6ffd6ff595d0db0c 0x06ffd6ff595d0db0 0xfffffffffff0ff0f 0xffffffffffff0ff0

def z44 : W := mkw 0x22c64fd9213afbae 0x822c64fd9213afba 0xf1ce4ff920ffffff 0x7f1ce4ff920fffff

def z45 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x0031b2c6d8001c00 0x80031b2c6d8001c0

def z46 : W := mkw 0x048fc0002a2e0000 0x0048fc0002a2e000 0xafcfc0003fff000b 0xeafcfc0003fff000

def z47 : W := mkw 0xbfffffee3fffffcf 0x0bfffffee3fffffc 0xfffffffe3fffffcf 0xffffffffe3fffffc

def z48 : W := mkw 0x2f790fe415d0db0c 0x02f790fe415d0db0 0xffff8ffe3ff0ff0f 0xfffff8ffe3ff0ff0

def z49 : W := mkw 0x4dad603580000000 0x04dad60358000000 0xcffff03fc0000003 0xecffff03fc000000

def z50 : W := mkw 0x2b709fc25dd5df5d 0x42b709fc25dd5df5 0xfff1ffc7ffffffff 0xffff1ffc7fffffff

def z51 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0x8fce0c3800000000 0x58fce0c380000000

def z52 : W := mkw 0x4f292aa480000000 0x04f292aa48000000 0x0e31b2c6c0000000 0x80e31b2c6c000000

def z53 : W := mkw 0xabf47fc015f3db0c 0x0abf47fc015f3db0 0xbff07fc03ff3ff0d 0xfbff07fc03ff3ff0

def z54 : W := mkw 0x22509fc25995df5d 0x422509fc25995df5 0x5031ffc7d88fffff 0xb5031ffc7d88ffff

def z55 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z56 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xafce00003fff0008 0x4afce00003fff000

def z57 : W := mkw 0x22000ac00100990c 0x022000ac00100990 0x000002c000001c00 0x0000002c000001c0

def z58 : W := mkw 0x89b4700014e30000 0x089b4700014e3000 0x81f0700000f30001 0x081f0700000f3000

def z59 : W := mkw 0x848ff0002a2f0000 0x0848ff0002a2f000 0x000ff000000f0002 0x0000ff000000f000

def z60 : W := mkw 0x8d29200006400000 0x08d2920000640000 0x0e00000007000000 0x00e0000000700000

def z61 : W := mkw 0x00c4451100000000 0x000c445110000000 0xc1ce4d3900000007 0x7c1ce4d390000000

def z62 : W := mkw 0x2b700fc015c0990c 0x02b700fc015c0990 0x8ff00fc01f001c05 0xf8ff00fc01f001c0

def z63 : W := mkw 0x06cf4f3d203a62a2 0x806cf4f3d203a62a 0xffcfcf3f20ffe3ff 0xfffcfcf3f20ffe3f

def z64 : W := mkw 0x06090a2400000000 0x006090a240000000 0x4e0f8e3e00000006 0xf4e0f8e3e0000000

def z65 : W := mkw 0x5fefefbfab0cb4c3 0x05fefefbfab0cb4c 0xffffffffff0cfccf 0xfffffffffff0cfcc

def z66 : W := mkw 0x42400fb580000000 0x042400fb58000000 0x40000fffc0000004 0x140000fffc000000

def z67 : W := mkw 0xcfffffb5beef0000 0x0cfffffb5beef000 0xefffffffffff000f 0xfefffffffffff000

def z68 : W := mkw 0x0000000000000000 0x0000000000000000 0x50004101008f03ff 0x250004101008f03f

def z69 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xdfffffffc08f03ff 0xfdfffffffc08f03f

def z70 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xaffff00027700003 0xeaffff0002770000

def z71 : W := mkw 0x09b6400034ea0000 0x009b6400034ea000 0xaffe40003fff000b 0xeaffe40003fff000

def z72 : W := mkw 0x2050054015d0db0c 0x02050054015d0db0 0xb1c00d003ff0ff0d 0x7b1c00d003ff0ff0

def z73 : W := mkw 0x297095c25cd54f5d 0x4297095c25cd54f5 0xd1f1f3c7d8ff1fff 0xad1f1f3c7d8ff1ff

def z74 : W := mkw 0x69f465d194d04b0c 0x069f465d194d04b0 0x81f071c1c0f00301 0x081f071c1c0f0030

def z75 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xfffff1013fff03ff 0xefffff1013fff03f

def z76 : W := mkw 0x160b0a2c2308b082 0x0160b0a2c2308b08 0x2e0e0c382700e000 0x52e0e0c382700e00

def z77 : W := mkw 0x00400519001062a2 0x800400519001062a 0x00000c380000e000 0x100000c380000e00

def z78 : W := mkw 0x00400519001062a2 0x800400519001062a 0x50004d39008fe3ff 0x350004d39008fe3f

def z79 : W := mkw 0x0930000014c00000 0x00930000014c0000 0x0e3000001f000000 0x80e3000001f00000

def z80 : W := mkw 0x00c4451100324220 0x800c445110032422 0x81c0000000700000 0x081c000000070000

def z81 : W := mkw 0x00c4451100324220 0x800c445110032422 0xd1c0410100ff03ff 0x2d1c0410100ff03f

def z82 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x4031f2c7d80f1cf2 0x84031f2c7d80f1cf

def z83 : W := mkw 0x140b802e2a0c24c3 0x0140b802e2a0c24c 0x400f803e000c00c2 0x0400f803e000c00c

def z84 : W := mkw 0x1f6b8fae2b0cb4c3 0x01f6b8fae2b0cb4c 0xffff8ffe3f0cfccf 0xfffff8ffe3f0cfcc

def z85 : W := mkw 0x0010004010800908 0x0001000401080090 0x5031f3c7d8801f0f 0xa5031f3c7d8801f0

def z86 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xaffff2c6ffff1c0b 0xeaffff2c6ffff1c0

def z87 : W := mkw 0x160b9a2e6b0db4d3 0x4160b9a2e6b0db4d 0x7e0ffe3fff0ffcfe 0xf7e0ffe3fff0ffcf

def z88 : W := mkw 0x00c4451100324220 0x800c445110032422 0x81c0410100f30331 0x081c0410100f3033

def z89 : W := mkw 0x0040050000104200 0x0004005000010420 0xb1c00d0020f0e30d 0x7b1c00d0020f0e30

def z90 : W := mkw 0x4fef6fbda02a20a2 0x84fef6fbda02a20a 0xcfffffffc00f00f7 0xfcfffffffc00f00f

def z91 : W := mkw 0x040b80002a0c0000 0x0040b80002a0c000 0x2e0f80003f0c000a 0xe2e0f80003f0c000

def z92 : W := mkw 0x09f6451934fa62a2 0x809f6451934fa62a 0xfffe4d393fffe3ff 0xffffe4d393fffe3f

def z93 : W := mkw 0x0000900248050451 0x4000090024805045 0x4001f007c00f00f2 0x04001f007c00f00f

def z94 : W := mkw 0x22400f800110d204 0x022400f800110d20 0x00000c000000e000 0x100000c000000e00

def z95 : W := mkw 0x0084401100220020 0x8008440110022002 0x0000400100030030 0x0000040010003003

def z96 : W := mkw 0x297005c015d0db0c 0x0297005c015d0db0 0xb1f001c03ff0ff09 0x0b1f001c03ff0ff0

def z97 : W := mkw 0x4fef6fbda03a62a2 0x84fef6fbda03a62a 0xffffffffe0ffe3ff 0xfffffffffe0ffe3f

def z98 : W := mkw 0x2b600f800550d204 0x02b600f800550d20 0xafc00c002770e000 0x5afc00c002770e00

def z99 : W := mkw 0x02000a0001009000 0x002000a000100900 0x3e000e003f00fc0c 0xf3e000e003f00fc0

def z100 : W := mkw 0x0000004240000d59 0x40000004240000d5 0x500003c7c0001ff4 0x0500003c7c0001ff

def z101 : W := mkw 0x00020008203a62a2 0x800020008203a62a 0x200000002070e000 0x0200000002070e00

def z102 : W := mkw 0x0000000000000000 0x0000000000000000 0x4031f3c7c0000007 0xa4031f3c7c000000

def z103 : W := mkw 0x1002800a2b0cb4c3 0x01002800a2b0cb4c 0x300000003f0cfcc8 0x0300000003f0cfcc

def z104 : W := mkw 0x12008a2e0904b4c3 0x012008a2e0904b4c 0x50018e3e180cfcce 0xb50018e3e180cfcc

def z105 : W := mkw 0x2b708fc21dd4df4d 0x02b708fc21dd4df4 0xfff18fc63ffcffcf 0xffff18fc63ffcffc

def z106 : W := mkw 0x448d603580000000 0x0448d60358000000 0x403ff3ffc0000007 0xa403ff3ffc000000

def z107 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0x81fff00000ff0003 0x081fff00000ff000

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0x4001820600000006 0xa400182060000000

def z109 : W := mkw 0x0000800208040441 0x0000080020804044 0x50018206180c1cce 0xa50018206180c1cc

def z110 : W := mkw 0x8dbf700036eb0000 0x08dbf700036eb000 0xaffe700027f30001 0x4affe700027f3000

def z111 : W := mkw 0x0000000000000000 0x0000000000000000 0x003003c000000005 0xa003003c00000000

def z112 : W := mkw 0x140b802e2a0c24c3 0x0140b802e2a0c24c 0x500f823e180c1cce 0xa500f823e180c1cc

def z113 : W := mkw 0x4ffdfff7d8850d59 0x44ffdfff7d8850d5 0xdfffffffd88f1fff 0xfdfffffffd88f1ff

def z114 : W := mkw 0x9fafea2e2f6eb4c3 0x09fafea2e2f6eb4c 0xffcf8e3e3f7cfcce 0xfffcf8e3e3f7cfcc

def z115 : W := mkw 0x040b80022a0c0441 0x0040b80022a0c044 0x7e0f82063f0c1cce 0xe7e0f82063f0c1cc

def z116 : W := mkw 0x84cff5192a3f62a2 0x884cff5192a3f62a 0xf1cffd3920ffe3ff 0x7f1cffd3920ffe3f

def z117 : W := mkw 0x2b600f800550d204 0x02b600f800550d20 0xbfc00e003f70fc0c 0xfbfc00e003f70fc0

def z118 : W := mkw 0x4fedffb7c8050451 0x44fedffb7c805045 0xcfffffffc00f00f7 0xfcfffffffc00f00f

def z119 : W := mkw 0x3f6b8fae2f5cf6c7 0x03f6b8fae2f5cf6c 0xffcf8e3e3f7cfcce 0xfffcf8e3e3f7cfcc

def z120 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e3fffffff0cfccf 0xf7e3fffffff0cfcc

def z121 : W := mkw 0x8dfff5003eff4200 0x08dfff5003eff420 0xbffffd003fffe30f 0xfbffffd003fffe30

def z122 : W := mkw 0x0010900018850000 0x0001090001885000 0x5031f101188f03ff 0xa5031f101188f03f

def z123 : W := mkw 0x9012900a3fefb4c3 0x09012900a3fefb4c 0x300000003ffffcc8 0x0300000003ffffcc

def z124 : W := mkw 0x00c64519202a20a2 0x800c64519202a20a 0xc1ce4d39000f00f7 0x7c1ce4d39000f00f

def z125 : W := mkw 0x16098a260b049441 0x016098a260b04944 0x5e0182061f0c1cce 0xa5e0182061f0c1cc

def z126 : W := mkw 0x16199a665b859d59 0x416199a665b859d5 0x0e31b2c6df001c00 0x80e31b2c6df001c0

def z127 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xc1ce413900ff03f3 0x0c1ce413900ff03f

def z128 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0fcf3f3f8fffff 0xf7e0fcf3f3f8ffff

def z129 : W := mkw 0x849ff0003aaf0000 0x0849ff0003aaf000 0x003ff000188f000b 0xa003ff000188f000

def z130 : W := mkw 0x46cd6fb580000000 0x046cd6fb58000000 0x400fffffc0000006 0x1400fffffc000000

def z131 : W := mkw 0x8409b0000a050000 0x08409b0000a05000 0x0001b00000000000 0x00001b0000000000

def z132 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0x1e300fc01f00ff04 0x91e300fc01f00ff0

def z133 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000020018001c0c 0xa1000020018001c0

def z134 : W := mkw 0x6ffd6ff595d0db0c 0x06ffd6ff595d0db0 0xbffe0ff83ff0ff0d 0xfbffe0ff83ff0ff0

def z135 : W := mkw 0x4fad6ab580000000 0x04fad6ab58000000 0x4e3ff2ffc0000002 0x84e3ff2ffc000000

def z136 : W := mkw 0x0040050000104200 0x0004005000010420 0x10000d000000e304 0x110000d000000e30

def z137 : W := mkw 0x800290002a2f0000 0x0800290002a2f000 0x00000000000f0000 0x000000000000f000

def z138 : W := mkw 0x4f292aa480000000 0x04f292aa48000000 0x0e00000000000000 0x00e0000000000000

def z139 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xa1ce0c382070e000 0x5a1ce0c382070e00

def z140 : W := mkw 0x2bf64fd935fafbae 0x82bf64fd935fafba 0xfffe4ff93fffffff 0xffffe4ff93ffffff

def z141 : W := mkw 0x44cd653580000000 0x044cd65358000000 0xc1cffd3fc0000007 0x7c1cffd3fc000000

def z142 : W := mkw 0x8fffff803eef0000 0x08fffff803eef000 0xafffffc03fff000f 0xfafffffc03fff000

def z143 : W := mkw 0x1012904a7b8dbddb 0x41012904a7b8dbdd 0x300000003f8ffff8 0x0300000003f8ffff

def z144 : W := mkw 0x06090a2400000000 0x006090a240000000 0x0e0e0c3800000000 0x50e0e0c380000000

def z145 : W := mkw 0x42400ff7c0000d59 0x442400ff7c0000d5 0x50000fffc0001ff4 0x150000fffc0001ff

def z146 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0x8ffffc3800000003 0xf8ffffc380000000

def z147 : W := mkw 0x00864000202a0000 0x000864000202a000 0xa1ce400020ff000b 0x6a1ce400020ff000

def z148 : W := mkw 0x16098a2e0b04b4c3 0x016098a2e0b04b4c 0x5e018e3e1f00fcc4 0x95e018e3e1f00fcc

def z149 : W := mkw 0x0010004010800908 0x0001000401080090 0x003001c000800301 0x0003001c00080030

def z150 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xeffff3c7ffff000f 0xeeffff3c7ffff000

def z151 : W := mkw 0x8fbffa243eef0000 0x08fbffa243eef000 0xeffffe3e3fff000f 0xfeffffe3e3fff000

def z152 : W := mkw 0xafffffd93ffffbae 0x8afffffd93ffffba 0xfffffff93fffffff 0xffffffff93ffffff

def z153 : W := mkw 0x1002800a2b0cb4c3 0x01002800a2b0cb4c 0x700e0c383f0cfcce 0x7700e0c383f0cfcc

def z154 : W := mkw 0x0409000000000000 0x0040900000000000 0x0e0f800000000002 0xe0e0f80000000000

def z155 : W := mkw 0x0000000000000000 0x0000000000000000 0xa1c0000020f00009 0x6a1c0000020f0000

def z156 : W := mkw 0x0dad600000000000 0x00dad60000000000 0x8ffff00000000003 0xe8ffff0000000000

def z157 : W := mkw 0x3f7b0fec37d8fb8e 0x03f7b0fec37d8fb8 0xbffe0ff83ff0ff0d 0xfbffe0ff83ff0ff0

def z158 : W := mkw 0x0010004010800908 0x0001000401080090 0x103003c018801f0d 0xa103003c018801f0

def z159 : W := mkw 0x160b0a2c2308b082 0x0160b0a2c2308b08 0x3e0e0e383f00fc0c 0xf3e0e0e383f00fc0

def z160 : W := mkw 0x0010900258850451 0x4001090025885045 0x4031f007d88f00fb 0xa4031f007d88f00f

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x400003c7c0000004 0x0400003c7c000000

def z162 : W := mkw 0x4b600fb580000000 0x04b600fb58000000 0xcff00fffc0000005 0xfcff00fffc000000

def z163 : W := mkw 0x0012904a78bf6ffb 0xc0012904a78bf6ff 0x3000000038fffff8 0x03000000038fffff

def z164 : W := mkw 0x0012904a788d2ddb 0x40012904a788d2dd 0x703ffffff88fffff 0xf703ffffff88ffff

def z165 : W := mkw 0x3f7b8fee3fdcffcf 0x03f7b8fee3fdcffc 0xffff8ffe3ffcffcf 0xfffff8ffe3ffcffc

def z166 : W := mkw 0x968ffa2e2b2fb4c3 0x0968ffa2e2b2fb4c 0x7e0ffe3e3f0ffcce 0xf7e0ffe3e3f0ffcc

def z167 : W := mkw 0x2b600fc00110db0c 0x02b600fc00110db0 0x9ff00fc00000ff05 0xf9ff00fc00000ff0

def z168 : W := mkw 0x22400fc24110df5d 0x422400fc24110df5 0x50000fc7c000fff4 0x150000fc7c000fff

def z169 : W := mkw 0x8dbff0027eef0451 0x48dbff0027eef045 0xeffff007ffff00fb 0xeeffff007ffff00f

def z170 : W := mkw 0x0096d04278af0d59 0x40096d04278af0d5 0xf1fff3c7f8ff1fff 0xef1fff3c7f8ff1ff

def z171 : W := mkw 0x8dbf600036ea0000 0x08dbf600036ea000 0xaffe00003ff00009 0xeaffe00003ff0000

def z172 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x3e0e0c383f0cfcc8 0x53e0e0c383f0cfcc

def z173 : W := mkw 0x02020a082108b082 0x002020a082108b08 0x7e0e0e383f0cfcce 0xf7e0e0e383f0cfcc

def z174 : W := mkw 0x00864019202a20a2 0x800864019202a20a 0x400e4039000f00f2 0x0400e4039000f00f

def z175 : W := mkw 0x49e4659180324220 0x849e465918032422 0x81f071c1c0f30331 0x081f071c1c0f3033

def z176 : W := mkw 0x2010004015d0db0c 0x02010004015d0db0 0x300000003ff0ff08 0x0300000003ff0ff0

def z177 : W := mkw 0x0930000014c00000 0x00930000014c0000 0x81f0000000f00001 0x081f0000000f0000

def z178 : W := mkw 0x0def6519203a62a2 0x80def6519203a62a 0xfffffd3920ffe3ff 0xffffffd3920ffe3f

def z179 : W := mkw 0x161b9a6e7b8dbddb 0x4161b9a6e7b8dbdd 0x7e3fffffff8fffff 0xf7e3fffffff8ffff

def z180 : W := mkw 0x00020008202a20a2 0x800020008202a20a 0x00000000000f00f0 0x000000000000f00f

def z181 : W := mkw 0x2930004015d0db0c 0x02930004015d0db0 0xbff000003ff0ff09 0xebff000003ff0ff0

def z182 : W := mkw 0x200000000550d204 0x0200000000550d20 0x200000002770e000 0x0200000002770e00

def z183 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000000000c00ce 0x250000000000c00c

def z184 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xcfce0fffc0000004 0x5cfce0fffc000000

def z185 : W := mkw 0x0012904a78bf6ffb 0xc0012904a78bf6ff 0x7031f3c7f8ffffff 0xa7031f3c7f8fffff

def z186 : W := mkw 0x2bf44fd115f2db2c 0x82bf44fd115f2db2 0xbff04fc13ff3ff3d 0xfbff04fc13ff3ff3

def z187 : W := mkw 0x00c4451100324220 0x800c445110032422 0xb1c04d0120f3e33d 0x7b1c04d0120f3e33

def z188 : W := mkw 0x364b8fee2b1cffcf 0x0364b8fee2b1cffc 0x7e0f8ffe3f0cffce 0xf7e0f8ffe3f0cffc

def z189 : W := mkw 0x00c4451100000000 0x000c445110000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z190 : W := mkw 0x29f645d934fa6bae 0x829f645d934fa6ba 0xf1fe4df920ffe3ff 0x7f1fe4df920ffe3f

def z191 : W := mkw 0x8dfff5113eff4220 0x88dfff5113eff422 0xaffff1013fff033b 0xeaffff1013fff033

def z192 : W := mkw 0x448f603da02a20a2 0x8448f603da02a20a 0x400ff03fc00f00f2 0x0400ff03fc00f00f

def z193 : W := mkw 0x040b80002a0c0000 0x0040b80002a0c000 0x000f8000000c0002 0x0000f8000000c000

def z194 : W := mkw 0x12000a2e0100b4c3 0x012000a2e0100b4c 0x50000e3e0000fcc4 0x150000e3e0000fcc

def z195 : W := mkw 0x6fff6ffdb5fafbae 0x86fff6ffdb5fafba 0xffffffffffffffff 0xffffffffffffffff

def z196 : W := mkw 0x293000c014c0090c 0x0293000c014c0090 0x003000c000000000 0x0003000c00000000

def z197 : W := mkw 0x3b728fca3fdcffcf 0x03b728fca3fdcffc 0xbff00fc03ffcffcd 0xfbff00fc03ffcffc

def z198 : W := mkw 0x8dbd700014e30000 0x08dbd700014e3000 0x8ffff00000f30003 0xe8ffff00000f3000

def z199 : W := mkw 0x2960058004504204 0x0296005800450420 0x81c0000000700000 0x081c000000070000

def z200 : W := mkw 0x42400fb580000000 0x042400fb58000000 0x00000c3800000000 0x100000c380000000

def z201 : W := mkw 0x100080020b049441 0x0100080020b04944 0x000000001f001c00 0x0000000001f001c0

def z202 : W := mkw 0x12c64f3f213af6e3 0x812c64f3f213af6e 0xf1ce4f3f20ffffff 0x7f1ce4f3f20fffff

def z203 : W := mkw 0x2b300ac015c0990c 0x02b300ac015c0990 0x0e3002c01f001c00 0x80e3002c01f001c0

def z204 : W := mkw 0xcdfff591beef0000 0x0cdfff591beef000 0xaffff1c1ffff000b 0xeaffff1c1ffff000

def z205 : W := mkw 0x0010104050810918 0x4001010405081091 0x003071c1c0830331 0x0003071c1c083033

def z206 : W := mkw 0x12000a6e4100bddb 0x412000a6e4100bdd 0x50000fffc000fff4 0x150000fffc000fff

def z207 : W := mkw 0x8daff0002e6f0000 0x08daff0002e6f000 0xafcff000277f0002 0x4afcff000277f000

def z208 : W := mkw 0x0b600f8000000000 0x00b600f800000000 0xcff1ffc7c0000007 0xfcff1ffc7c000000

def z209 : W := mkw 0x12400f3f0110f6e3 0x812400f3f0110f6e 0x50000f3f0000fff4 0x150000f3f0000fff

def z210 : W := mkw 0x6f392ae495c0990c 0x06f392ae495c0990 0x0e31b2c6df001c00 0x80e31b2c6df001c0

def z211 : W := mkw 0x564b8fbfab0cb4c3 0x0564b8fbfab0cb4c 0x7e0f8fffff0cfcce 0xf7e0f8fffff0cfcc

def z212 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xa1ce4d3920f3e331 0x5a1ce4d3920f3e33

def z213 : W := mkw 0x8d39b0425ec50d59 0x48d39b0425ec50d5 0x0e31b2c6df001c00 0x80e31b2c6df001c0

def z214 : W := mkw 0x0be64f99203a62a2 0x80be64f99203a62a 0xfffe4ff920ffe3ff 0xffffe4ff920ffe3f

def z215 : W := mkw 0x00420519203a62a2 0x800420519203a62a 0x70000d3920ffe3fc 0x170000d3920ffe3f

def z216 : W := mkw 0x140b800a2b0cb4c3 0x0140b800a2b0cb4c 0x3e0f80003f0cfcca 0xe3e0f80003f0cfcc

def z217 : W := mkw 0x6ffdfff7ddd5df5d 0x46ffdfff7ddd5df5 0xffffffffffffffff 0xffffffffffffffff

def z218 : W := mkw 0x4ded65b580000000 0x04ded65b58000000 0xc1fff1ffc0000003 0x0c1fff1ffc000000

def z219 : W := mkw 0x2b600f800550d204 0x02b600f800550d20 0xbfc00d0027f0e30d 0x7bfc00d0027f0e30

def z220 : W := mkw 0x160b0a2e2308b4c3 0x0160b0a2e2308b4c 0x7e0e0e3e2700fcc4 0x57e0e0e3e2700fcc

def z221 : W := mkw 0x8dfff5193eff62a2 0x88dfff5193eff62a 0xfffffd393fffe3ff 0xffffffd393fffe3f

def z222 : W := mkw 0x0d3b80003ecc0000 0x00d3b80003ecc000 0xafff80003ffc000b 0xeafff80003ffc000

def z223 : W := mkw 0x801290003eef0000 0x0801290003eef000 0x2031f0003fff000b 0xa2031f0003fff000

def z224 : W := mkw 0x00d6d51938bf62a2 0x800d6d51938bf62a 0xf1fffd3938ffe3ff 0xff1fffd3938ffe3f

def z225 : W := mkw 0x2b700fc255d0df5d 0x42b700fc255d0df5 0xfff00fc7fff0fffd 0xffff00fc7fff0fff

def z226 : W := mkw 0x0000004240000d59 0x40000004240000d5 0x500043c7c08f1fff 0x2500043c7c08f1ff

def z227 : W := mkw 0xafff6fc037fadb0c 0x0afff6fc037fadb0 0xbffe0fc03ff0ff0d 0xfbffe0fc03ff0ff0

def z228 : W := mkw 0x168fca3f2b2eb4e3 0x8168fca3f2b2eb4e 0x7e0fce3f3f0ffcfe 0xf7e0fce3f3f0ffcf

def z229 : W := mkw 0x0000004040000918 0x4000000404000091 0x000001c1c0000330 0x0000001c1c000033

def z230 : W := mkw 0x093090001cc50000 0x0093090001cc5000 0xaff1f0003fff000b 0xeaff1f0003fff000

def z231 : W := mkw 0x848ff0002a2f0000 0x0848ff0002a2f000 0x2e0ff0003f0f000a 0xe2e0ff0003f0f000

def z232 : W := mkw 0x8dbff0023eef0441 0x08dbff0023eef044 0xfffff2063fff1ccf 0xefffff2063fff1cc

def z233 : W := mkw 0x16cf4f3d233af2a2 0x816cf4f3d233af2a 0xafce0c382770e000 0x5afce0c382770e00

def z234 : W := mkw 0x00d4d55358b74f79 0xc00d4d55358b74f7 0xd1f1f3c7d8ff1fff 0xad1f1f3c7d8ff1ff

def z235 : W := mkw 0x2bf44fd115d0db0c 0x02bf44fd115d0db0 0xfffe4ff93ff0ff0f 0xffffe4ff93ff0ff0

def z236 : W := mkw 0x0000000000000000 0x0000000000000000 0x2e0000003f000008 0xe2e0000003f00000

def z237 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x2e0f8e3e3f00fc00 0xd2e0f8e3e3f00fc0

def z238 : W := mkw 0x1002800a2a0c24c3 0x01002800a2a0c24c 0x00000000000c00c0 0x000000000000c00c

def z239 : W := mkw 0x0dbd600014c00000 0x00dbd600014c0000 0xaffff0003ff0000b 0xeaffff0003ff0000

def z240 : W := mkw 0x12028a2e2b0cb4c3 0x012028a2e2b0cb4c 0x70000e3e3f0cfccc 0x170000e3e3f0cfcc

def z241 : W := mkw 0x4ffdffb598850000 0x04ffdffb59885000 0xcfffffffd88f000f 0xfcfffffffd88f000

def z242 : W := mkw 0x8dbdf0001ee70000 0x08dbdf0001ee7000 0x8ff1f0001ff30001 0x88ff1f0001ff3000

def z243 : W := mkw 0x00864000202a0000 0x000864000202a000 0x000e4000000f0002 0x0000e4000000f000

def z244 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000101000003f4 0x050000101000003f

def z245 : W := mkw 0x0000100040010010 0x4000010004001001 0x00007001c0030030 0x000007001c003003

def z246 : W := mkw 0x448df037c8050451 0x4448df037c805045 0x400ff03fc00f00f2 0x0400ff03fc00f00f

def z247 : W := mkw 0x040b80082a0c2082 0x0040b80082a0c208 0x7e0f8c383f0ce0ce 0xf7e0f8c383f0ce0c

def z248 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbfc00c003ff0ff08 0x5bfc00c003ff0ff0

def z249 : W := mkw 0x1002800a2b0cb4c3 0x01002800a2b0cb4c 0x700182063f0cfcce 0xa700182063f0cfcc

def z250 : W := mkw 0x3fffcfff3ffeffef 0x83fffcfff3ffeffe 0xffffcfff3fffffff 0xfffffcfff3ffffff

def z251 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x1031b2c6d88f1ff8 0x81031b2c6d88f1ff

def z252 : W := mkw 0x62400ff58110db0c 0x062400ff58110db0 0x50000fffc000ff04 0x150000fffc000ff0

def z253 : W := mkw 0x0000800008040000 0x0000080000804000 0x00018000180c000a 0xa00018000180c000

def z254 : W := mkw 0x89b4f0001ce70000 0x089b4f0001ce7000 0x81f1f00018ff000b 0xa81f1f00018ff000

def z255 : W := mkw 0x22500fc01190db0c 0x022500fc01190db0 0x10300fc01880ff0d 0xb10300fc01880ff0

def z256 : W := mkw 0x06cd4f3500000000 0x006cd4f350000000 0xcfcfcf3f00000007 0xfcfcfcf3f0000000

def z257 : W := mkw 0x2b300ac015c0990c 0x02b300ac015c0990 0x3e300ec03f00fc0c 0xf3e300ec03f00fc0

def z258 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xafffb0003f700000 0xcafffb0003f70000

def z259 : W := mkw 0x8dafe0002e6e0000 0x08dafe0002e6e000 0xafcf80003f7c000a 0xeafcf80003f7c000

def z260 : W := mkw 0xcfef6fb5a66a0000 0x0cfef6fb5a66a000 0xefffffffe7700007 0xfefffffffe770000

def z261 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000410100830331 0x0000041010083033

def z262 : W := mkw 0x4f292aa480000000 0x04f292aa48000000 0x4e31f3c7c0000007 0xa4e31f3c7c000000

def z263 : W := mkw 0x093090425cc50d59 0x4093090425cc50d5 0xfff1f3c7ffff1fff 0xefff1f3c7ffff1ff

def z264 : W := mkw 0x148fc03f2a2e24e3 0x8148fc03f2a2e24e 0x400fc03f000f00f2 0x0400fc03f000f00f

def z265 : W := mkw 0x16098a260b049441 0x016098a260b04944 0x4e0f8e3e1f001c06 0xf4e0f8e3e1f001c0

def z266 : W := mkw 0x8dbdf0001ec50000 0x08dbdf0001ec5000 0x8ffff0001f000003 0xe8ffff0001f00000

def z267 : W := mkw 0x8d39b0001ec50000 0x08d39b0001ec5000 0xaff1b0003ff00009 0xeaff1b0003ff0000

def z268 : W := mkw 0x52400fbf8100b4c3 0x052400fbf8100b4c 0x50000fffc000fcc4 0x150000fffc000fcc

def z269 : W := mkw 0x0042050820186282 0x0004205082018628 0xf1ce0d3820fce3cf 0x7f1ce0d3820fce3c

def z270 : W := mkw 0x06090a2400000000 0x006090a240000000 0x4e3fffffc0000007 0xf4e3fffffc000000

def z271 : W := mkw 0x2b700fc014d04b0c 0x02b700fc014d04b0 0x8ff00fc000f00305 0xf8ff00fc000f0030

def z272 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0x8fffbefec0000000 0xd8fffbefec000000

def z273 : W := mkw 0x9fbffa263fef9441 0x09fbffa263fef944 0xaffff2063fff1c0b 0xeaffff2063fff1c0

def z274 : W := mkw 0x00864000202a0000 0x000864000202a000 0xa1ce000020700000 0x4a1ce00002070000

def z275 : W := mkw 0x8dbff0403eef0908 0x08dbff0403eef090 0xbffff3c03fff1f0f 0xebffff3c03fff1f0

def z276 : W := mkw 0x2b700f8015d0d204 0x02b700f8015d0d20 0xaff00c003ff0e009 0xfaff00c003ff0e00

def z277 : W := mkw 0x2f7b8fc03fdcdb0c 0x02f7b8fc03fdcdb0 0xbfff8fc03ffcff0f 0xfbfff8fc03ffcff0

def z278 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x3e000fc03f00ff0c 0xf3e000fc03f00ff0

def z279 : W := mkw 0x6fed6fb58550d204 0x06fed6fb58550d20 0xefffffffe770e007 0xfefffffffe770e00

def z280 : W := mkw 0x3f798fe61fd4df4d 0x03f798fe61fd4df4 0xbff18fc63ff0ff0d 0xfbff18fc63ff0ff0

def z281 : W := mkw 0x0b300a0015c09000 0x00b300a0015c0900 0xbff00e003ff0fc0d 0xfbff00e003ff0fc0

def z282 : W := mkw 0x9fbffa2e3fefb4c3 0x09fbffa2e3fefb4c 0xfffffe3e3ffffccf 0xffffffe3e3ffffcc

def z283 : W := mkw 0x0000000240000451 0x4000000024000045 0x40000007c00000f0 0x040000007c00000f

def z284 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xe1ce4d392070e007 0x7e1ce4d392070e00

def z285 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xa1ce4c3820ffe00b 0x7a1ce4c3820ffe00

def z286 : W := mkw 0x8dbff0083eef2082 0x08dbff0083eef208 0xfffffc383fffe0cf 0xffffffc383fffe0c

def z287 : W := mkw 0x0084400000220000 0x0008440000022000 0x81c0400000f30001 0x081c0400000f3000

def z288 : W := mkw 0x2012004835fafbae 0x82012004835fafba 0x300000003ffffff8 0x0300000003ffffff

def z289 : W := mkw 0x8096d0003eef0000 0x08096d0003eef000 0xa1ce40003fff000b 0x6a1ce40003fff000

def z290 : W := mkw 0x8084700000230000 0x0808470000023000 0x0000700000030000 0x0000070000003000

def z291 : W := mkw 0xadfff5c03eff4b0c 0x0adfff5c03eff4b0 0xaffff1c03fff030b 0xeaffff1c03fff030

def z292 : W := mkw 0x5f29aaa68b049441 0x05f29aaa68b04944 0x0e31b2c6df001c00 0x80e31b2c6df001c0

def z293 : W := mkw 0x8fbffa003fef9000 0x08fbffa003fef900 0xbffffe003ffffc0f 0xfbffffe003ffffc0

def z294 : W := mkw 0x00c4451100000000 0x000c445110000000 0x81ce0c3800000000 0x581ce0c380000000

def z295 : W := mkw 0x00c4451100000000 0x000c445110000000 0xd1ce4d39008f03ff 0x7d1ce4d39008f03f

def z296 : W := mkw 0x89b4704054e30918 0x489b4704054e3091 0x81f071c1c0f30331 0x081f071c1c0f3033

def z297 : W := mkw 0x0050954258954f59 0x40050954258954f5 0xf1f1ffc7f8ffffff 0xff1f1ffc7f8fffff

def z298 : W := mkw 0x6b700ff595d0db0c 0x06b700ff595d0db0 0xfff00ffffff0ff0d 0xffff00ffffff0ff0

def z299 : W := mkw 0x2b300ac015c0990c 0x02b300ac015c0990 0x1e3003c01f801f0d 0xa1e3003c01f801f0

def z300 : W := mkw 0x040980000a040000 0x0040980000a04000 0x0e0180001f000000 0x80e0180001f00000

def z301 : W := mkw 0x9dbff02e3eef24c3 0x09dbff02e3eef24c 0xeffff03e3fff00cb 0xeeffff03e3fff00c

def z302 : W := mkw 0x0dbdf04258850d59 0x40dbdf04258850d5 0xdffff3c7d88f1fff 0xedffff3c7d88f1ff

def z303 : W := mkw 0x49f475d1d0810918 0x449f475d1d081091 0x81f071c1c0830331 0x081f071c1c083033

def z304 : W := mkw 0x46490fb580000000 0x046490fb58000000 0x4e0f8fffc0000006 0xf4e0f8fffc000000

def z305 : W := mkw 0x160b8a2e2a0c24c3 0x0160b8a2e2a0c24c 0x4e0f8e3e000c00c6 0xf4e0f8e3e000c00c

def z306 : W := mkw 0x0000800208040441 0x0000080020804044 0x10000000180c1cc8 0x010000000180c1cc

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0x0031f00000000003 0xa0031f0000000000

def z308 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x3e0182063f0cfcc8 0x83e0182063f0cfcc

def z309 : W := mkw 0x801090001ec50000 0x0801090001ec5000 0x000000001f000000 0x0000000001f00000

def z310 : W := mkw 0x00420519201862a2 0x800420519201862a 0x700e0d39200ce3fe 0x7700e0d39200ce3f

def z311 : W := mkw 0x6fed6ff58110db0c 0x06fed6ff58110db0 0xdfffffffc000ff07 0xfdfffffffc000ff0

def z312 : W := mkw 0x961b9a2e3fefb4c3 0x0961b9a2e3fefb4c 0x7e0f8e3e3ffffcce 0xf7e0f8e3e3ffffcc

def z313 : W := mkw 0x8d39b0425ec50d59 0x48d39b0425ec50d5 0x5e31f3c7df8f1fff 0xa5e31f3c7df8f1ff

def z314 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1ffffffe0ffe3ff 0xff1ffffffe0ffe3f

def z315 : W := mkw 0x4f39bae6d8850d59 0x44f39bae6d8850d5 0x0e31b2c6d8001c00 0x80e31b2c6d8001c0

def z316 : W := mkw 0x0920000004400000 0x0092000000440000 0xafc0000027700000 0x4afc000002770000

def z317 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x50018206188f1ffe 0xa50018206188f1ff

def z318 : W := mkw 0x12020a2e2108b4c3 0x012020a2e2108b4c 0x700e0e3e200cfcce 0x7700e0e3e200cfcc

def z319 : W := mkw 0x2b600fc00550db0c 0x02b600fc00550db0 0xbfc00fc02770ff04 0x5bfc00fc02770ff0

def z320 : W := mkw 0x00000019000020a2 0x800000019000020a 0x40000039000000f0 0x040000039000000f

def z321 : W := mkw 0x2b300ac015c0990c 0x02b300ac015c0990 0xaff002c03ff01c09 0xeaff002c03ff01c0

def z322 : W := mkw 0x42400fb580000000 0x042400fb58000000 0x4031ffffc0000007 0xb4031ffffc000000

def z323 : W := mkw 0x204005c000104b0c 0x0204005c000104b0 0x000001c000000300 0x0000001c00000030

def z324 : W := mkw 0x160b0a2c2308b082 0x0160b0a2c2308b08 0x7e0e0c38270ce0ce 0x77e0e0c38270ce0c

def z325 : W := mkw 0x2b600f800550d204 0x02b600f800550d20 0xaff00fc02770e005 0xfaff00fc02770e00

def z326 : W := mkw 0x0daf6000202a0000 0x00daf6000202a000 0xaffff00020ff000b 0xeaffff00020ff000

def z327 : W := mkw 0x0920000000000000 0x0092000000000000 0x8ff0000000000001 0xe8ff000000000000

def z328 : W := mkw 0x0b700f8014c00000 0x00b700f8014c0000 0xaff00fc03ff0000d 0xfaff00fc03ff0000

def z329 : W := mkw 0x4fed6fb581009000 0x04fed6fb58100900 0xffffffffff00fc0f 0xfffffffffff00fc0

def z330 : W := mkw 0x32400fee0110ffcf 0x032400fee0110ffc 0x50000ffe0000ffc4 0x150000ffe0000ffc

def z331 : W := mkw 0x00c64500203a4200 0x000c64500203a420 0xb1ce4d0020ffe30f 0x7b1ce4d0020ffe30

def z332 : W := mkw 0x00864019202a20a2 0x800864019202a20a 0xe1ce403920ff00fb 0x6e1ce403920ff00f

def z333 : W := mkw 0x0010900018850000 0x0001090001885000 0x00000000188f0008 0x000000000188f000

def z334 : W := mkw 0x0000900248050451 0x4000090024805045 0x5001f107c08f03ff 0x25001f107c08f03f

def z335 : W := mkw 0x0040055b40106ffb 0xc0040055b40106ff 0x50000fffc000fff4 0x150000fffc000fff

def z336 : W := mkw 0x00c6455b603a6ffb 0xc00c6455b603a6ff 0xf1ce4fffe0ffffff 0x7f1ce4fffe0fffff

def z337 : W := mkw 0x02c64f19213af2a2 0x802c64f19213af2a 0xffce4f393fffffff 0xfffce4f393ffffff

def z338 : W := mkw 0x16cf4f3d233af2a2 0x816cf4f3d233af2a 0xffce4d3927ffe3ff 0x7ffce4d3927ffe3f

def z339 : W := mkw 0xcdbff035beef0000 0x0cdbff035beef000 0xeffff03fffff000b 0xeeffff03fffff000

def z340 : W := mkw 0xc48ff035aa2f0000 0x0c48ff035aa2f000 0x400ff03fc00f0002 0x0400ff03fc00f000

def z341 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xaff00dc027f0e301 0x5aff00dc027f0e30

def z342 : W := mkw 0x22400fd90110fbae 0x822400fd90110fba 0x50000ff90000fff4 0x150000ff90000fff

def z343 : W := mkw 0x0000000000000000 0x0000000000000000 0x5031f3c7c08f03ff 0xa5031f3c7c08f03f

def z344 : W := mkw 0x00400519001062a2 0x800400519001062a 0xf1c00d3920f0e3fd 0x7f1c00d3920f0e3f

def z345 : W := mkw 0x9f39ba261fc59441 0x09f39ba261fc5944 0x0e31b2061f001c00 0x80e31b2061f001c0

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0x003071c1c0000001 0x0003071c1c000000

def z347 : W := mkw 0x0000000000000000 0x0000000000000000 0x4001f007c0000002 0x04001f007c000000

def z348 : W := mkw 0x0ded651100000000 0x00ded65110000000 0xcffffd3900000007 0xfcffffd390000000

def z349 : W := mkw 0x4fefefb5aa0c0000 0x04fefefb5aa0c000 0xefffffffff0c000f 0xfefffffffff0c000

def z350 : W := mkw 0x0010104050810918 0x4001010405081091 0x003030c0c0000000 0x0003030c0c000000

def z351 : W := mkw 0x4fed6fb580324220 0x84fed6fb58032422 0xcfffffffc0f30337 0xfcfffffffc0f3033

def z352 : W := mkw 0x140b002c22082082 0x0140b002c2208208 0x000e003800000000 0x0000e00380000000

def z353 : W := mkw 0x12000a2601009441 0x012000a260100944 0x0000020600001c00 0x00000020600001c0

def z354 : W := mkw 0x160b8a2e2b3ef6e3 0x8160b8a2e2b3ef6e 0x7e0f8e3e3ffffffe 0xf7e0f8e3e3ffffff

def z355 : W := mkw 0x040b000022080000 0x0040b00002208000 0x2e0e000027000000 0x42e0e00002700000

def z356 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xfff1ffc7fff0ff0f 0xffff1ffc7fff0ff0

def z357 : W := mkw 0x9fbffa6e7fefbddb 0x49fbffa6e7fefbdd 0xffffffffffffffff 0xffffffffffffffff

def z358 : W := mkw 0x0084401100000000 0x0008440110000000 0x400e403900000002 0x0400e40390000000

def z359 : W := mkw 0x0084400000000000 0x0008440000000000 0x81ce400000000003 0x681ce40000000000

def z360 : W := mkw 0x5f2baaaeab0cb4c3 0x05f2baaaeab0cb4c 0x7e3fbefeff0cfcce 0xf7e3fbefeff0cfcc

def z361 : W := mkw 0x06090a2401009000 0x006090a240100900 0x7e0f8e3e3f00fc0e 0xf7e0f8e3e3f00fc0

def z362 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xaff00ec03f70fc00 0xdaff00ec03f70fc0

def z363 : W := mkw 0x16090a2403009000 0x016090a240300900 0x0e00000007000000 0x00e0000000700000

def z364 : W := mkw 0x00c4451100000000 0x000c445110000000 0x81c0410100000001 0x081c041010000000

def z365 : W := mkw 0x448d603580000000 0x0448d60358000000 0x000e003800000000 0x0000e00380000000

def z366 : W := mkw 0x0010904018850908 0x0001090401885090 0x1031f3c0188f1f0f 0xa1031f3c0188f1f0

def z367 : W := mkw 0x0010100010810000 0x0001010001081000 0x0030700000830001 0x0003070000083000

def z368 : W := mkw 0xcffffff7feef0d59 0x4cffffff7feef0d5 0xffffffffffff1fff 0xfffffffffffff1ff

def z369 : W := mkw 0x893290003eef0000 0x0893290003eef000 0xaff000003fff0009 0xeaff000003fff000

def z370 : W := mkw 0x4fef6fbda0082082 0x04fef6fbda008208 0xffffffffe00ce0cf 0xfffffffffe00ce0c

def z371 : W := mkw 0x1f3b8a2e3fccb4c3 0x01f3b8a2e3fccb4c 0xffff8e3e3ffcfccf 0xfffff8e3e3ffcfcc

def z372 : W := mkw 0x4ffdfff7d8850d59 0x44ffdfff7d8850d5 0xcfffffffd8001c07 0xfcfffffffd8001c0

def z373 : W := mkw 0x0010004010800908 0x0001000401080090 0x1000000018801f08 0x01000000018801f0

def z374 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xcfcffc3fc0000002 0x5cfcffc3fc000000

def z375 : W := mkw 0x4fed6ff7c0000d59 0x44fed6ff7c0000d5 0xdfffffffc0001ff7 0xfdfffffffc0001ff

def z376 : W := mkw 0x02400f000110d200 0x002400f000110d20 0xbfc00f003ff0ff0d 0xfbfc00f003ff0ff0

def z377 : W := mkw 0x0be44f9100000000 0x00be44f910000000 0xcffe4ff900000007 0xfcffe4ff90000000

def z378 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x1031b3c6d8801f0d 0xa1031b3c6d8801f0

def z379 : W := mkw 0x8dfff5113eef0000 0x08dfff5113eef000 0xeffffd393fff000f 0xfeffffd393fff000

def z380 : W := mkw 0x4084601180000000 0x0408460118000000 0x00007001c0000000 0x000007001c000000

def z381 : W := mkw 0x02000a2400000000 0x002000a240000000 0x40000e3e00000004 0x140000e3e0000000

def z382 : W := mkw 0x02400f8000000000 0x002400f800000000 0x00000fc000000004 0x100000fc00000000

def z383 : W := mkw 0x4f692fa480000000 0x04f692fa48000000 0x8ff1bfc6c0000005 0xf8ff1bfc6c000000

def z384 : W := mkw 0x8dbff0083eff62a2 0x88dbff0083eff62a 0xbffff0003fffe3fb 0xebffff0003fffe3f

def z385 : W := mkw 0x49e66599a03a62a2 0x849e66599a03a62a 0xf1fe7df9e0ffe3ff 0x7f1fe7df9e0ffe3f

def z386 : W := mkw 0x0040050000104200 0x0004005000010420 0xa1c00c002070e000 0x5a1c00c002070e00

def z387 : W := mkw 0x2b701fc055d1db1c 0x42b701fc055d1db1 0xbff07fc1fff3ff3d 0xfbff07fc1fff3ff3

def z388 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xcfcf8e3e00000006 0xfcfcf8e3e0000000

def z389 : W := mkw 0x00020008203a62a2 0x800020008203a62a 0x7000410120ffe3ff 0x27000410120ffe3f

def z390 : W := mkw 0x468d6a3580000000 0x0468d6a358000000 0x4e0ffe3fc0000006 0xf4e0ffe3fc000000

def z391 : W := mkw 0x841b90003eef0000 0x0841b90003eef000 0x2e0f80003fff000a 0xe2e0f80003fff000

def z392 : W := mkw 0x060b0a2c20082082 0x0060b0a2c2008208 0x7e0f8e3e200ce0ce 0xf7e0f8e3e200ce0c

def z393 : W := mkw 0x1fafea2e2b0cb4c3 0x01fafea2e2b0cb4c 0xfffffe3e3f0cfccf 0xffffffe3e3f0cfcc

def z394 : W := mkw 0x161b8a6e3b8cbdcb 0x0161b8a6e3b8cbdc 0x7e3f8ffe3f8cffcf 0xf7e3f8ffe3f8cffc

def z395 : W := mkw 0x297015c054d14b1c 0x4297015c054d14b1 0x81f071c1c0f30331 0x081f071c1c0f3033

def z396 : W := mkw 0x160b8a262b0c9441 0x0160b8a262b0c944 0x2e0f82063f0c1c0a 0xe2e0f82063f0c1c0

def z397 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0x8ff003c01ff01f01 0x88ff003c01ff01f0

def z398 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x0031f2c6d88f1c0b 0xa0031f2c6d88f1c0

def z399 : W := mkw 0x0010804218840d49 0x00010804218840d4 0x503183c6188c1fcf 0xa503183c6188c1fc

def z400 : W := mkw 0x0010000014c00000 0x00010000014c0000 0x200000003ff00008 0x0200000003ff0000

def z401 : W := mkw 0x12000a2e0100b4c3 0x012000a2e0100b4c 0x7e000e3e3f00fccc 0xf7e000e3e3f00fcc

def z402 : W := mkw 0x0002000820082082 0x0000200082008208 0x200e0c382000e000 0x5200e0c382000e00

def z403 : W := mkw 0x9faf6a2c276ab082 0x09faf6a2c276ab08 0xafce0c382770e000 0x5afce0c382770e00

def z404 : W := mkw 0x42c64fbda03a62a2 0x842c64fbda03a62a 0xf1ce4fffe0ffe3ff 0x7f1ce4fffe0ffe3f

def z405 : W := mkw 0x161b9a6e7b8dbddb 0x4161b9a6e7b8dbdd 0x7e0f8e3e3f8ffffe 0xf7e0f8e3e3f8ffff

def z406 : W := mkw 0x2b700fd915d0fbae 0x82b700fd915d0fba 0xfff00ff93ff0fffd 0xffff00ff93ff0fff

def z407 : W := mkw 0xadbff0403fffdb0c 0x0adbff0403fffdb0 0xbffff0003fffff0b 0xebffff0003fffff0

def z408 : W := mkw 0x42400fbd801062a2 0x842400fbd801062a 0x50000fffc000e3f4 0x150000fffc000e3f

def z409 : W := mkw 0x00d6555970bb6bba 0xc00d6555970bb6bb 0xf1fe7df9e0ffe3ff 0x7f1fe7df9e0ffe3f

def z410 : W := mkw 0x8dfff55b7eff6ffb 0xc8dfff55b7eff6ff 0xffffffffffffffff 0xffffffffffffffff

def z411 : W := mkw 0x0970050014d04200 0x00970050014d0420 0xbff00d003ff0e30d 0xfbff00d003ff0e30

def z412 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0xb1c00fc020f0ff0d 0x7b1c00fc020f0ff0

def z413 : W := mkw 0x449df077d8850d59 0x4449df077d8850d5 0x503ff3ffd88f1fff 0xa503ff3ffd88f1ff

def z414 : W := mkw 0xcfef6fb5a66a0000 0x0cfef6fb5a66a000 0xafce0c3827700000 0x5afce0c382770000

def z415 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0x0e3ff0001f0f0002 0x80e3ff0001f0f000

def z416 : W := mkw 0x060b8a242a0c0000 0x0060b8a242a0c000 0x6e0f8e3e3f0c000e 0xf6e0f8e3e3f0c000

def z417 : W := mkw 0x848ff0192a2f20a2 0x8848ff0192a2f20a 0x400ff039000f00f2 0x0400ff039000f00f

def z418 : W := mkw 0x0b600f8001009000 0x00b600f800100900 0xbff00fc03f00fc0d 0xfbff00fc03f00fc0

def z419 : W := mkw 0x4ded659180000000 0x04ded65918000000 0x8ffff1c1c0000003 0xe8ffff1c1c000000

def z420 : W := mkw 0xcfefffb5aa2f0000 0x0cfefffb5aa2f000 0xcfffffffc00f0007 0xfcfffffffc00f000

def z421 : W := mkw 0x0086d01b682f24f3 0xc0086d01b682f24f 0x400ff03fc00f00f2 0x0400ff03fc00f00f

def z422 : W := mkw 0xafbffac03fef990c 0x0afbffac03fef990 0xaffff2c03fff1c0b 0xeaffff2c03fff1c0

def z423 : W := mkw 0x4fed6fbd801062a2 0x84fed6fbd801062a 0xdfffffffc000e3f7 0xfdfffffffc000e3f

def z424 : W := mkw 0x49f4f5d3d8850d59 0x449f4f5d3d8850d5 0xd1f1f3c7d88f1fff 0xad1f1f3c7d88f1ff

def z425 : W := mkw 0x0dad600000000000 0x00dad60000000000 0xcffff3c7c0000007 0xecffff3c7c000000

def z426 : W := mkw 0x06090a2400000000 0x006090a240000000 0x0e01820600000000 0x80e0182060000000

def z427 : W := mkw 0x8dbff0193eef20a2 0x88dbff0193eef20a 0xeffff0393fff00fb 0xeeffff0393fff00f

def z428 : W := mkw 0x3f398ae61fc49d4d 0x03f398ae61fc49d4 0x0e3182c61f001c00 0x80e3182c61f001c0

def z429 : W := mkw 0x8010100014e30000 0x08010100014e3000 0x0000000000f30000 0x00000000000f3000

def z430 : W := mkw 0x00c4451100104200 0x000c445110010420 0xf1ce4d3920f0e30f 0x7f1ce4d3920f0e30

def z431 : W := mkw 0x2b309ac25dc59d5d 0x42b309ac25dc59d5 0x0e31b2c6df001c00 0x80e31b2c6df001c0

def z432 : W := mkw 0x2b709fc01dd5db0c 0x02b709fc01dd5db0 0xbff1ffc03fffff0f 0xfbff1ffc03fffff0

def z433 : W := mkw 0x0930004014c00908 0x00930004014c0090 0xbff003c03ff01f0d 0xebff003c03ff01f0

def z434 : W := mkw 0x4fef6fbda03a62a2 0x84fef6fbda03a62a 0xafce0c382070e000 0x5afce0c382070e00

def z435 : W := mkw 0x06199a6658850d59 0x406199a6658850d5 0x5e3fffffd88f1fff 0xf5e3fffffd88f1ff

def z436 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0x500e4d39000fe3f6 0x1500e4d39000fe3f

def z437 : W := mkw 0x849ff0003eef0000 0x0849ff0003eef000 0x200ff0003fff000a 0x0200ff0003fff000

def z438 : W := mkw 0x2b709fc25dd5df5d 0x42b709fc25dd5df5 0xbff1bfc6fff0ff0d 0xfbff1bfc6fff0ff0

def z439 : W := mkw 0x848f6000222a0000 0x0848f6000222a000 0x000e000000000000 0x0000e00000000000

def z440 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xbffff0003fff1ffb 0xebffff0003fff1ff

def z441 : W := mkw 0x000280002a0c0000 0x0000280002a0c000 0x200000003f0c0008 0x0200000003f0c000

def z442 : W := mkw 0x2ffd6fc015d0db0c 0x02ffd6fc015d0db0 0xbfffffc03ff0ff0f 0xfbfffffc03ff0ff0

def z443 : W := mkw 0x160b8a6e6b0cbddb 0x4160b8a6e6b0cbdd 0x7e0f8fffff0cfffe 0xf7e0f8fffff0cfff

def z444 : W := mkw 0x2be64f99257af2a6 0x82be64f99257af2a 0xffce4d3927ffe3ff 0x7ffce4d3927ffe3f

def z445 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x0031f3c7d8831f31 0x80031f3c7d8831f3

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x40004001000f00f2 0x040004001000f00f

def z447 : W := mkw 0x5fefefbfab3ef6e3 0x85fefefbfab3ef6e 0xffffffffffffffff 0xffffffffffffffff

def z448 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xb1ce0c3820ffe3f8 0x5b1ce0c3820ffe3f

def z449 : W := mkw 0x4f292aa480000000 0x04f292aa48000000 0x4e3fbefec0000006 0xf4e3fbefec000000

def z450 : W := mkw 0x0000900248050451 0x4000090024805045 0x4031f3c7c00f00f7 0xa4031f3c7c00f00f

def z451 : W := mkw 0x02100a4011809908 0x002100a401180990 0x3e300fc03f80ff0d 0xf3e300fc03f80ff0

def z452 : W := mkw 0x5fefefbfab0cb4c3 0x05fefefbfab0cb4c 0xffcf8e3e3f0cfcce 0xfffcf8e3e3f0cfcc

def z453 : W := mkw 0x12000a2c0100b082 0x012000a2c0100b08 0x00000c380000e000 0x100000c380000e00

def z454 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1ce0d392070e3f4 0x5f1ce0d392070e3f

def z455 : W := mkw 0x00864000202a0000 0x000864000202a000 0xf1ce410120ff03ff 0x6f1ce410120ff03f

def z456 : W := mkw 0x16cfcf3f2b0cb4c3 0x016cfcf3f2b0cb4c 0xffcfcf3f3f0cfccf 0xfffcfcf3f3f0cfcc

def z457 : W := mkw 0x02000a0001009000 0x002000a000100900 0x2e000c002700e000 0x52e000c002700e00

def z458 : W := mkw 0x29f445d114f24b2c 0x829f445d114f24b2 0x81f041c100f30331 0x081f041c100f3033

def z459 : W := mkw 0xcfffffbdbeff62a2 0x8cfffffbdbeff62a 0xffffffffffffe3ff 0xfffffffffffffe3f

def z460 : W := mkw 0x8def6519267a62a2 0x88def6519267a62a 0xafce0c382770e000 0x5afce0c382770e00

def z461 : W := mkw 0x0000804248040d59 0x40000804248040d5 0x500183c7d80c1ffe 0xa500183c7d80c1ff

def z462 : W := mkw 0x4fef6fbda03a62a2 0x84fef6fbda03a62a 0xefffffffe070e007 0xfefffffffe070e00

def z463 : W := mkw 0x00c44519003262a2 0x800c44519003262a 0xd1c04d3900f3e3f5 0x1d1c04d3900f3e3f

def z464 : W := mkw 0x80d6d5193eff62a2 0x880d6d5193eff62a 0xf1ce4d393fffe3ff 0x7f1ce4d393fffe3f

def z465 : W := mkw 0x4040059180000000 0x0404005918000000 0x000001c1c0000000 0x0000001c1c000000

def z466 : W := mkw 0xafffffc27fffdf5d 0x4afffffc27fffdf5 0xffffffc7ffffffff 0xfffffffc7fffffff

def z467 : W := mkw 0x4fef6fb5a02a0000 0x04fef6fb5a02a000 0xefffffffe0ff000f 0xfefffffffe0ff000

def z468 : W := mkw 0x89b4700014e30000 0x089b4700014e3000 0xaff070003ff30009 0xeaff070003ff3000

def z469 : W := mkw 0x0000900248050451 0x4000090024805045 0x5001f207d80f1cfe 0xa5001f207d80f1cf

def z470 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0x91f00fc000f0ff05 0x191f00fc000f0ff0

def z471 : W := mkw 0x4ffd6ff590800908 0x04ffd6ff59080090 0xdfffffffd8801f0f 0xfdfffffffd8801f0

def z472 : W := mkw 0x0000800208040441 0x0000080020804044 0x5001c307188f1fff 0xa5001c307188f1ff

def z473 : W := mkw 0xaf39bac01fc5990c 0x0af39bac01fc5990 0x0e31b2c01f001c00 0x80e31b2c01f001c0

def z474 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x4031f1c7c08f03f3 0x04031f1c7c08f03f

def z475 : W := mkw 0xeffffff5bfffdb0c 0x0effffff5bfffdb0 0xffffffffffffff0f 0xfffffffffffffff0

def z476 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x103003c0188f1ffd 0xa103003c0188f1ff

def z477 : W := mkw 0x00d6d55b78bf6ffb 0xc00d6d55b78bf6ff 0xf1ce4d3938ffffff 0x7f1ce4d3938fffff

def z478 : W := mkw 0x801290427eef0d59 0x4801290427eef0d5 0x300000003fff1ff8 0x0300000003fff1ff

def z479 : W := mkw 0x20d6455935fafbae 0x820d6455935fafba 0xf1ce4d393fffffff 0x7f1ce4d393ffffff

def z480 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x0000000018001c00 0x00000000018001c0

def z481 : W := mkw 0x8dbff0407eef0918 0x48dbff0407eef091 0xaffff1c1ffff033b 0xeaffff1c1ffff033

def z482 : W := mkw 0xc9f4759194e30000 0x0c9f4759194e3000 0x81f071c1c0f30001 0x081f071c1c0f3000

def z483 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0x8ffe7df9c0000001 0x58ffe7df9c000000

def z484 : W := mkw 0x0000004240000d59 0x40000004240000d5 0x000002c6c0001c00 0x0000002c6c0001c0

def z485 : W := mkw 0x160b8a2c2b0cb082 0x0160b8a2c2b0cb08 0x2e0f8c383f0ce00a 0xf2e0f8c383f0ce00

def z486 : W := mkw 0x2010004015c0990c 0x02010004015c0990 0x000000001f001c00 0x0000000001f001c0

def z487 : W := mkw 0x0010004010800908 0x0001000401080090 0x003002c018001c00 0x8003002c018001c0

def z488 : W := mkw 0x4fef6fbda03a62a2 0x84fef6fbda03a62a 0xffce4d3920ffe3ff 0x7ffce4d3920ffe3f

def z489 : W := mkw 0x0000004240000d59 0x40000004240000d5 0x5031f3c7c0001ff7 0xa5031f3c7c0001ff

def z490 : W := mkw 0x201090425dd5df5d 0x4201090425dd5df5 0x300000003ffffff8 0x0300000003ffffff

def z491 : W := mkw 0x42c44fb580000000 0x042c44fb58000000 0xc1ce4fffc0000007 0x7c1ce4fffc000000

def z492 : W := mkw 0x02000a0001009000 0x002000a000100900 0x10000e000000fc04 0x110000e000000fc0

def z493 : W := mkw 0x948ff02e2a2f24c3 0x0948ff02e2a2f24c 0x400ff03e000f00c2 0x0400ff03e000f00c

def z494 : W := mkw 0x848ff0026a2f0451 0x4848ff0026a2f045 0x400ff007c00f00f2 0x0400ff007c00f00f

def z495 : W := mkw 0x0d29200000000000 0x00d2920000000000 0x0e31b00000000000 0x80e31b0000000000

def z496 : W := mkw 0x0b700fc010800908 0x00b700fc01080090 0x9ff00fc018801f0d 0xf9ff00fc018801f0

def z497 : W := mkw 0x00c4451100324220 0x800c445110032422 0xc1ce4d3900f30337 0x7c1ce4d3900f3033

def z498 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1ce0c38207ce0ce 0x7f1ce0c38207ce0c

def z499 : W := mkw 0x9fbffa2c3fefb082 0x09fbffa2c3fefb08 0xaffffc383fffe00b 0xfaffffc383fffe00

def z500 : W := mkw 0x2b309ac25dc59d5d 0x42b309ac25dc59d5 0x5e31f3c7df8f1fff 0xa5e31f3c7df8f1ff

def z501 : W := mkw 0x8d39b0001ec50000 0x08d39b0001ec5000 0x0e31f0001f8f000b 0xa0e31f0001f8f000

def z502 : W := mkw 0x0b600f8000000000 0x00b600f800000000 0x8fc00c0000000000 0x58fc00c000000000

def z503 : W := mkw 0x80020000266a0000 0x080020000266a000 0x2000000027700000 0x0200000002770000

def z504 : W := mkw 0x297005c014d04b0c 0x0297005c014d04b0 0xb1f00dc020f0e30d 0x7b1f00dc020f0e30

def z505 : W := mkw 0x16098a260b049441 0x016098a260b04944 0x3e018e063f00fc0c 0xf3e018e063f00fc0

def z506 : W := mkw 0xafef6f80277ad204 0x0afef6f80277ad20 0xafce0c002770e000 0x5afce0c002770e00

def z507 : W := mkw 0x0000000000104200 0x0000000000010420 0x3000000020f0e308 0x03000000020f0e30

def z508 : W := mkw 0x00864019202a20a2 0x800864019202a20a 0x700e4c39200fe0fe 0x7700e4c39200fe0f

def z509 : W := mkw 0x548fe03faa0c24c3 0x0548fe03faa0c24c 0x400ff03fc00c00c2 0x0400ff03fc00c00c

def z510 : W := mkw 0x4fedefb788040441 0x04fedefb78804044 0xdfffffffd80c1ccf 0xfdfffffffd80c1cc

def z511 : W := mkw 0x2bf64fc035fadb0c 0x02bf64fc035fadb0 0xbffe4fc03fffff0f 0xfbffe4fc03fffff0

def z512 : W := mkw 0x22100a4015d0db0c 0x022100a4015d0db0 0x3e000e003ff0ff0c 0xf3e000e003ff0ff0

def z513 : W := mkw 0x00864008203a62a2 0x800864008203a62a 0xb1ce400020ffe3fb 0x6b1ce400020ffe3f

def z514 : W := mkw 0x0dbdf00018850000 0x00dbdf0001885000 0x8ffff000188f000b 0xe8ffff000188f000

def z515 : W := mkw 0xcfffffb5beef0000 0x0cfffffb5beef000 0xaffffc383fff000b 0xfaffffc383fff000

def z516 : W := mkw 0x4fad6aa480000000 0x04fad6aa48000000 0x8ffff2c6c0000003 0xe8ffff2c6c000000

def z517 : W := mkw 0xcffdffb59ec50000 0x0cffdffb59ec5000 0xcfffffffdf000007 0xfcfffffffdf00000

def z518 : W := mkw 0x0409002400000000 0x0040900240000000 0x400f803e00000002 0x0400f803e0000000

def z519 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xb1c0410120ffe3f9 0x0b1c0410120ffe3f

def z520 : W := mkw 0x0010104050810918 0x4001010405081091 0x4031f3c7c0830337 0xa4031f3c7c083033

def z521 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x500003c7d88f1ffc 0x0500003c7d88f1ff

def z522 : W := mkw 0x0002000020080000 0x0000200002008000 0x200e0000200c000a 0x6200e0000200c000

def z523 : W := mkw 0x00c44519001062a2 0x800c44519001062a 0xd1ce4d390000e3f7 0x7d1ce4d390000e3f

def z524 : W := mkw 0x2be64f99257af2a6 0x82be64f99257af2a 0xafce0c382770e000 0x5afce0c382770e00

def z525 : W := mkw 0x2b300ac015d0db0c 0x02b300ac015d0db0 0x3e3002c03ff0ff08 0x83e3002c03ff0ff0

def z526 : W := mkw 0x161b9a6e7b8dbddb 0x4161b9a6e7b8dbdd 0x7e3fbefeff0cfcce 0xf7e3fbefeff0cfcc

def z527 : W := mkw 0x0b200a8000000000 0x00b200a800000000 0x0e3002c000000000 0x80e3002c00000000

def z528 : W := mkw 0x060b8a002b0c9000 0x0060b8a002b0c900 0x3e0f8e003f0cfc0e 0xf3e0f8e003f0cfc0

def z529 : W := mkw 0x00020000202a0000 0x000020000202a000 0x2000000020ff0008 0x02000000020ff000

def z530 : W := mkw 0x0000000001009000 0x0000000000100900 0x300000003f00fc08 0x0300000003f00fc0

def z531 : W := mkw 0x0000004000000908 0x0000000400000090 0x100003c000001f04 0x0100003c000001f0

def z532 : W := mkw 0x4920208080000000 0x0492020808000000 0x003030c0c0000000 0x0003030c0c000000

def z533 : W := mkw 0x49e4659180000000 0x049e465918000000 0x81c0000000000000 0x081c000000000000

def z534 : W := mkw 0x0010000010800000 0x0001000001080000 0x0030000018800009 0xa003000001880000

def z535 : W := mkw 0x14cfc53f2a3e66e3 0x814cfc53f2a3e66e 0xf1cfcd3f20ffe3ff 0x7f1cfcd3f20ffe3f

def z536 : W := mkw 0xa9f475c014f34b0c 0x0a9f475c014f34b0 0x81f071c000f30301 0x081f071c000f3030

def z537 : W := mkw 0x4ffd6fb594c00000 0x04ffd6fb594c0000 0xeffffffffff0000f 0xfeffffffffff0000

def z538 : W := mkw 0x0040050000104200 0x0004005000010420 0xf1c04d0120ffe3ff 0x7f1c04d0120ffe3f

def z539 : W := mkw 0x00c6d51b683f66f3 0xc00c6d51b683f66f 0xf1cffd3fe0ffe3ff 0x7f1cffd3fe0ffe3f

def z540 : W := mkw 0x2010004015d0db0c 0x02010004015d0db0 0x303003c03ff0ff0d 0xa303003c03ff0ff0

def z541 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x5031b2c6d80c1cce 0xa5031b2c6d80c1cc

def z542 : W := mkw 0x0040050000000000 0x0004005000000000 0x81c00d0000000005 0x781c00d000000000

def z543 : W := mkw 0x1000002e000024c3 0x01000002e000024c 0x4000003e000000c0 0x04000003e000000c

def z544 : W := mkw 0x22500fc015d0db0c 0x022500fc015d0db0 0x30000fc03ff0ff0c 0x130000fc03ff0ff0

def z545 : W := mkw 0x0040050000104200 0x0004005000010420 0x81c0010000f00301 0x081c0010000f0030

def z546 : W := mkw 0x8d3bb0003eef0000 0x08d3bb0003eef000 0x2e31b0003fff0008 0x82e31b0003fff000

def z547 : W := mkw 0x9f3bba2e3fcdb4c3 0x09f3bba2e3fcdb4c 0x7e3fbe3e3f0cfcce 0xf7e3fbe3e3f0cfcc

def z548 : W := mkw 0x0010104250810d59 0x40010104250810d5 0x503073c7c0831ff5 0x0503073c7c0831ff

def z549 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000410100000007 0x2400041010000000

def z550 : W := mkw 0x164b8f2e2b1cf6c3 0x0164b8f2e2b1cf6c 0xffcf8f3e3ffcffcf 0xfffcf8f3e3ffcffc

def z551 : W := mkw 0x200000400110db0c 0x0200000400110db0 0x100000000000ff00 0x0100000000000ff0

def z552 : W := mkw 0x44cf653da03a62a2 0x844cf653da03a62a 0xf1cffd3fe0ffe3ff 0x7f1cffd3fe0ffe3f

def z553 : W := mkw 0x8dfff5193eff62a2 0x88dfff5193eff62a 0xaffffc383fffe00b 0xfaffffc383fffe00

def z554 : W := mkw 0x42000aa480000000 0x042000aa48000000 0x000002c6c0000000 0x0000002c6c000000

def z555 : W := mkw 0x3f7b9fee7fddffdf 0x43f7b9fee7fddffd 0xffffffffffffffff 0xffffffffffffffff

def z556 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000000008f03f8 0x010000000008f03f

def z557 : W := mkw 0x297005c014d04b0c 0x0297005c014d04b0 0x91f003c018f01f0d 0xa91f003c018f01f0

def z558 : W := mkw 0x3012804a3fdcffcf 0x03012804a3fdcffc 0x300000003ffcffc8 0x0300000003ffcffc

def z559 : W := mkw 0x140b802e2b0cb4c3 0x0140b802e2b0cb4c 0x700f803e3f0cfcca 0x0700f803e3f0cfcc

def z560 : W := mkw 0x12028a0a2b0cb4c3 0x012028a0a2b0cb4c 0x3e000e003f0cfccc 0xf3e000e003f0cfcc

def z561 : W := mkw 0x89b6700034eb0000 0x089b6700034eb000 0xa1fe700020ff000b 0x6a1fe700020ff000

def z562 : W := mkw 0x0010900218850441 0x0001090021885044 0x5031f206188f1ccf 0xa5031f206188f1cc

def z563 : W := mkw 0x2bf6dfdb7dffffff 0xc2bf6dfdb7dfffff 0xffffffffffffffff 0xffffffffffffffff

def z564 : W := mkw 0x0000900248050451 0x4000090024805045 0x0001b006c0000000 0x00001b006c000000

def z565 : W := mkw 0x361b8a6e3fdcffcf 0x0361b8a6e3fdcffc 0x7e0f8e3e3ffcffce 0xf7e0f8e3e3ffcffc

def z566 : W := mkw 0x0010900018850000 0x0001090001885000 0x0031b00018000000 0x80031b0001800000

def z567 : W := mkw 0x00d4d55358850d59 0x400d4d55358850d5 0xd1ffffffd88f1fff 0xfd1ffffffd88f1ff

def z568 : W := mkw 0x0960058000000000 0x0096005800000000 0x81f001c000000001 0x081f001c00000000

def z569 : W := mkw 0x10c6c51b2b3ef6e3 0x810c6c51b2b3ef6e 0xf1ce4d393fffffff 0x7f1ce4d393ffffff

def z570 : W := mkw 0xa01290403fffdb0c 0x0a01290403fffdb0 0x300000003fffff08 0x0300000003fffff0

def z571 : W := mkw 0x0040051100104220 0x8004005110010422 0x0000010100000330 0x0000001010000033

def z572 : W := mkw 0x09a4600000000000 0x009a460000000000 0x81f0700000000001 0x081f070000000000

def z573 : W := mkw 0x201090425dd5df5d 0x4201090425dd5df5 0x7031f3c7ffffffff 0xa7031f3c7fffffff

def z574 : W := mkw 0x89a4600004620000 0x089a460000462000 0x81c0000000700000 0x081c000000070000

def z575 : W := mkw 0x3f3b8aee3fccbdcf 0x03f3b8aee3fccbdc 0x7e3f8efe3f0cfcce 0xf7e3f8efe3f0cfcc

def z576 : W := mkw 0x141b906e7a8d2ddb 0x4141b906e7a8d2dd 0x503ff3ffd88f1fff 0xa503ff3ffd88f1ff

def z577 : W := mkw 0x568fea3fab0cb4c3 0x0568fea3fab0cb4c 0x7e0ffe3fff0cfcce 0xf7e0ffe3fff0cfcc

def z578 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x5031b3c7d8001ff4 0x85031b3c7d8001ff

def z579 : W := mkw 0x041b90427a8d0d59 0x4041b90427a8d0d5 0x7e3ff3c7ff8f1fff 0xe7e3ff3c7ff8f1ff

def z580 : W := mkw 0x2b200a8005409004 0x02b200a800540900 0x0e00000007000000 0x00e0000000700000

def z581 : W := mkw 0x4ffffffff8bf6ffb 0xc4ffffffff8bf6ff 0xfffffffff8ffffff 0xffffffffff8fffff

def z582 : W := mkw 0x140b902e6a0d24d3 0x4140b902e6a0d24d 0x400ff03fc00f00f2 0x0400ff03fc00f00f

def z583 : W := mkw 0x0096d05b78af2dfb 0xc0096d05b78af2df 0x503ff3ffd88f1fff 0xa503ff3ffd88f1ff

def z584 : W := mkw 0x297005c014d04b0c 0x0297005c014d04b0 0xaff001c03ff00309 0xeaff001c03ff0030

def z585 : W := mkw 0x0002800a280c24c3 0x00002800a280c24c 0x700f8e3e380cfcce 0xf700f8e3e380cfcc

def z586 : W := mkw 0x0002000820082082 0x0000200082008208 0x400e0038000c00c2 0x0400e0038000c00c

def z587 : W := mkw 0x168fca2e2b2eb4c3 0x0168fca2e2b2eb4c 0xffcfce3e3ffffccf 0xfffcfce3e3ffffcc

def z588 : W := mkw 0x849ff0427aaf0d59 0x4849ff0427aaf0d5 0x503ff3c7d88f1fff 0xa503ff3c7d88f1ff

def z589 : W := mkw 0xafffff803fffd204 0x0afffff803fffd20 0xaffffc003fffe00b 0xfaffffc003fffe00

def z590 : W := mkw 0x00d4555150b34b38 0xc00d4555150b34b3 0x81f071c1c0f30331 0x081f071c1c0f3033

def z591 : W := mkw 0x048d600000000000 0x0048d60000000000 0x000ff00000000002 0x0000ff0000000000

def z592 : W := mkw 0x0dafe0002a0c0000 0x00dafe0002a0c000 0xaffff0003f0c000b 0xeaffff0003f0c000

def z593 : W := mkw 0x8daff0002a2f0000 0x08daff0002a2f000 0x8ffff000000f0003 0xe8ffff000000f000

def z594 : W := mkw 0x6f792fe495d0db0c 0x06f792fe495d0db0 0xbff1bfc6fff0ff0d 0xfbff1bfc6fff0ff0

def z595 : W := mkw 0x0f690fa400000000 0x00f690fa40000000 0xcfff8ffe00000007 0xfcfff8ffe0000000

def z596 : W := mkw 0x00020008203a62a2 0x800020008203a62a 0x700e0c3820ffe3fe 0x7700e0c3820ffe3f

def z597 : W := mkw 0x0002000820082082 0x0000200082008208 0x30000000200ce0c8 0x030000000200ce0c

def z598 : W := mkw 0x02000a0001009000 0x002000a000100900 0x0e0002001f001c00 0x80e0002001f001c0

def z599 : W := mkw 0x100200082308b082 0x0100200082308b08 0x200000002700e000 0x0200000002700e00

def z600 : W := mkw 0x0fad6a2400000000 0x00fad6a240000000 0xcffffe3e00000007 0xfcffffe3e0000000

def z601 : W := mkw 0x0010904058850918 0x4001090405885091 0x0031f1c1d88f033b 0xa0031f1c1d88f033

def z602 : W := mkw 0xcffd7fb594e30000 0x0cffd7fb594e3000 0xcfffffffc0f30007 0xfcfffffffc0f3000

def z603 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x1031f000188f1ffb 0xa1031f000188f1ff

def z604 : W := mkw 0x0002000820082082 0x0000200082008208 0x700e4d39208fe3ff 0x7700e4d39208fe3f

def z605 : W := mkw 0x06098a2608040441 0x006098a260804044 0x5e0f8e3e180c1cce 0xf5e0f8e3e180c1cc

def z606 : W := mkw 0x9dbff00a3fefb4c3 0x09dbff00a3fefb4c 0xbffff0003ffffccb 0xebffff0003ffffcc

def z607 : W := mkw 0x16dfdf7f7bbffffb 0xc16dfdf7f7bbffff 0xffffffffffffffff 0xffffffffffffffff

def z608 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xe1ce4c39207fe0f2 0x5e1ce4c39207fe0f

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0x400e0c3800000006 0x7400e0c380000000

def z610 : W := mkw 0x140b802e2a0c24c3 0x0140b802e2a0c24c 0x700f8c3e200ce0ce 0x7700f8c3e200ce0c

def z611 : W := mkw 0x89b6f0003eef0000 0x089b6f0003eef000 0xa1f070003fff0009 0x0a1f070003fff000

def z612 : W := mkw 0x49e4659180000000 0x049e465918000000 0xc1f1f3c7c0000007 0xac1f1f3c7c000000

def z613 : W := mkw 0x848ff0002a2f0000 0x0848ff0002a2f000 0xa1cff00020ff000b 0x6a1cff00020ff000

def z614 : W := mkw 0x0b600f8000104200 0x00b600f800010420 0xbff00fc020f0e30d 0xfbff00fc020f0e30

def z615 : W := mkw 0x16cfcf3f2b3ef6e3 0x816cfcf3f2b3ef6e 0xffcf8e3e3f7cfcce 0xfffcf8e3e3f7cfcc

def z616 : W := mkw 0x6ffd6ff595c0990c 0x06ffd6ff595c0990 0xcfffffffdf001c07 0xfcfffffffdf001c0

def z617 : W := mkw 0x00c6c51b283e66e3 0x800c6c51b283e66e 0xf1cfcf3f38ffffff 0xff1cfcf3f38fffff

def z618 : W := mkw 0x49e4659180000000 0x049e465918000000 0xc1fe7df9c0000007 0x7c1fe7df9c000000

def z619 : W := mkw 0x2010004014d04b0c 0x02010004014d04b0 0x0000000000f00300 0x00000000000f0030

def z620 : W := mkw 0x04cfc5192a3e62a2 0x804cfc5192a3e62a 0xffcfcd393fffe3ff 0xfffcfcd393fffe3f

def z621 : W := mkw 0x041b90003a8d0000 0x0041b90003a8d000 0x2e3ff0003f8f000b 0xe2e3ff0003f8f000

def z622 : W := mkw 0x0000000000000000 0x0000000000000000 0x30000c002000e00c 0x730000c002000e00

def z623 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0x8ff1f3c7c0000001 0x88ff1f3c7c000000

def z624 : W := mkw 0x0096d00038af0000 0x00096d00038af000 0xa1fff00038ff000b 0xea1fff00038ff000

def z625 : W := mkw 0x6ffd6ff594d04b0c 0x06ffd6ff594d04b0 0xcfffffffc0f00307 0xfcfffffffc0f0030

def z626 : W := mkw 0x00864008202a2082 0x000864008202a208 0xf1ce4c3820ffe0cf 0x7f1ce4c3820ffe0c

def z627 : W := mkw 0x00000008001062a2 0x800000008001062a 0x100000000000e3f0 0x0100000000000e3f

def z628 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0x8ffe0ff800000005 0xf8ffe0ff80000000

def z629 : W := mkw 0x2b720fc835fafbae 0x82b720fc835fafba 0xbff00fc03ffffffd 0xfbff00fc03ffffff

def z630 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x103071c1d88f1ff9 0x0103071c1d88f1ff

def z631 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x5001f007d88f1ffa 0x05001f007d88f1ff

def z632 : W := mkw 0xab729fc03fffdb0c 0x0ab729fc03fffdb0 0xbff00fc03fffff0d 0xfbff00fc03fffff0

def z633 : W := mkw 0x0000000200000441 0x0000000020000044 0x5000020600001cc4 0x05000020600001cc

def z634 : W := mkw 0x00d6455930ba6baa 0x800d6455930ba6ba 0xf1fe4ff938ffffff 0xff1fe4ff938fffff

def z635 : W := mkw 0x140980260a040441 0x0140980260a04044 0x0001800600000000 0x0000180060000000

def z636 : W := mkw 0x160b0a2c2308b082 0x0160b0a2c2308b08 0x6e0f8e3e2700e006 0xf6e0f8e3e2700e00

def z637 : W := mkw 0x89f4751114f34220 0x889f4751114f3422 0x81f0710100f30331 0x081f0710100f3033

def z638 : W := mkw 0x164b8f3f2b1cf6e3 0x8164b8f3f2b1cf6e 0x7e0f8f3f3f0cfffe 0xf7e0f8f3f3f0cfff

def z639 : W := mkw 0x1000000a0100b4c3 0x01000000a0100b4c 0x100000000000fcc0 0x0100000000000fcc

def z640 : W := mkw 0x2bf64fd935fafbae 0x82bf64fd935fafba 0xbffe0ff83ff0ff0d 0xfbffe0ff83ff0ff0

def z641 : W := mkw 0x5fefefbfaa0c24c3 0x05fefefbfaa0c24c 0xcfffffffc00c00c7 0xfcfffffffc00c00c

def z642 : W := mkw 0x4be46f9180000000 0x04be46f918000000 0x8ff07fc1c0000005 0xf8ff07fc1c000000

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x100001000080030d 0x2100001000080030

def z644 : W := mkw 0x0000900248050451 0x4000090024805045 0x00000000000f00f0 0x000000000000f00f

def z645 : W := mkw 0x4f692fb580000000 0x04f692fb58000000 0x4e31bfffc0000004 0x94e31bfffc000000

def z646 : W := mkw 0x00864019203a62a2 0x800864019203a62a 0x700e403920ffe3fa 0x0700e403920ffe3f

def z647 : W := mkw 0x3f6b0fac2758f286 0x03f6b0fac2758f28 0xafce0c382770e000 0x5afce0c382770e00

def z648 : W := mkw 0x5fef6fbda308b082 0x05fef6fbda308b08 0xafce0c382700e000 0x5afce0c382700e00

def z649 : W := mkw 0x801290427eef0d59 0x4801290427eef0d5 0x7031f3c7ffff1fff 0xa7031f3c7ffff1ff

def z650 : W := mkw 0x00864019202a20a2 0x800864019202a20a 0x000e003800000000 0x0000e00380000000

def z651 : W := mkw 0x00864019202a20a2 0x800864019202a20a 0x500e4139008f03ff 0x2500e4139008f03f

def z652 : W := mkw 0xcfbffaa4beef0000 0x0cfbffaa4beef000 0xaffff2c6ffff000b 0xeaffff2c6ffff000

def z653 : W := mkw 0x02000a0000000000 0x002000a000000000 0x0e000e0000000004 0xf0e000e000000000

def z654 : W := mkw 0x5ffffffffb8dbddb 0x45ffffffffb8dbdd 0xffffffffff8fffff 0xfffffffffff8ffff

def z655 : W := mkw 0x5fedefb78b049441 0x05fedefb78b04944 0xcfffffffdf001c07 0xfcfffffffdf001c0

def z656 : W := mkw 0x9fffff3f3ffff6e3 0x89fffff3f3ffff6e 0xffffff3f3fffffff 0xfffffff3f3ffffff

def z657 : W := mkw 0x6bf46fd195d0db0c 0x06bf46fd195d0db0 0xbff07fc1fff0ff0d 0xfbff07fc1fff0ff0

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x00004000008f000b 0x200004000008f000

def z659 : W := mkw 0x0050955b58956ffb 0xc0050955b58956ff 0x5031ffffd88fffff 0xb5031ffffd88ffff

def z660 : W := mkw 0x12109a6e5985bddb 0x412109a6e5985bdd 0x5031ffffd88fffff 0xb5031ffffd88ffff

def z661 : W := mkw 0x4f39bae6d8850d59 0x44f39bae6d8850d5 0x5e31f3c7d88f1fff 0xa5e31f3c7d88f1ff

def z662 : W := mkw 0x801290083eff62a2 0x8801290083eff62a 0x300000003fffe3f8 0x0300000003fffe3f

def z663 : W := mkw 0x02109a4259859d59 0x402109a4259859d5 0x7e31ffc7ff8fffff 0xf7e31ffc7ff8ffff

def z664 : W := mkw 0x2b720fc835d8fb8e 0x02b720fc835d8fb8 0xfffe0ff83ffcffcf 0xffffe0ff83ffcffc

def z665 : W := mkw 0x1012904a7b8dbddb 0x41012904a7b8dbdd 0x7031f3c7ff8fffff 0xa7031f3c7ff8ffff

def z666 : W := mkw 0x2b709fc25dd5df5d 0x42b709fc25dd5df5 0xbff00fc03ffffffd 0xfbff00fc03ffffff

def z667 : W := mkw 0x0010104050810918 0x4001010405081091 0x103073c1d8831f3d 0xa103073c1d8831f3

def z668 : W := mkw 0x3b700fee15d0ffcf 0x03b700fee15d0ffc 0xfff00ffe3ff0ffcd 0xffff00ffe3ff0ffc

def z669 : W := mkw 0x89b4f0425ce70d59 0x489b4f0425ce70d5 0xd1f1f3c7d8ff1fff 0xad1f1f3c7d8ff1ff

def z670 : W := mkw 0x4000003580000000 0x0400000358000000 0x4000003fc0000000 0x04000003fc000000

def z671 : W := mkw 0x00c64511202a0000 0x000c64511202a000 0xe1ce4d3920ff000f 0x7e1ce4d3920ff000

def z672 : W := mkw 0xdfffffbfbfefb4c3 0x0dfffffbfbfefb4c 0xfffffffffffffccf 0xffffffffffffffcc

def z673 : W := mkw 0x4be46fb580000000 0x04be46fb58000000 0xc1f07fffc0000005 0x1c1f07fffc000000

def z674 : W := mkw 0x6fed6fb58550d204 0x06fed6fb58550d20 0xafce0c382770e000 0x5afce0c382770e00

def z675 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x6e0f8c3e270ce0c2 0x56e0f8c3e270ce0c

def z676 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x4e0f823e1f0c1cc2 0x84e0f823e1f0c1cc

def z677 : W := mkw 0x8d3bb0003ecd0000 0x08d3bb0003ecd000 0x2e3fb0003f0c000a 0xe2e3fb0003f0c000

def z678 : W := mkw 0x00420508203a62a2 0x800420508203a62a 0xb1c00d0020ffe3fd 0x7b1c00d0020ffe3f

def z679 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x50004101188f1fff 0x250004101188f1ff

def z680 : W := mkw 0x0000800208040441 0x0000080020804044 0x5031f3c7d80c1ccf 0xa5031f3c7d80c1cc

def z681 : W := mkw 0x5fef6fbda308b082 0x05fef6fbda308b08 0xefffffffe700e007 0xfefffffffe700e00

def z682 : W := mkw 0x16199a665b859d59 0x416199a665b859d5 0x5e31f3c7df8f1fff 0xa5e31f3c7df8f1ff

def z683 : W := mkw 0x4409202480000000 0x0440920248000000 0x0001b006c0000000 0x00001b006c000000

def z684 : W := mkw 0x5fed6fbf8100b4c3 0x05fed6fbf8100b4c 0xdfffffffc000fcc7 0xfdfffffffc000fcc

def z685 : W := mkw 0x0fed6f8000000000 0x00fed6f800000000 0x8fffffc000000007 0xf8fffffc00000000

def z686 : W := mkw 0x16090a2e0100b4c3 0x016090a2e0100b4c 0x5e0f8e3e0000fcc6 0xf5e0f8e3e0000fcc

def z687 : W := mkw 0x0000800208040441 0x0000080020804044 0x0001820618001c00 0x80001820618001c0

def z688 : W := mkw 0x0010004010800908 0x0001000401080090 0x503043c1188f1fff 0xa503043c1188f1ff

def z689 : W := mkw 0x0040051100000000 0x0004005110000000 0x40000d3900000004 0x140000d390000000

def z690 : W := mkw 0x0000004240000d59 0x40000004240000d5 0x1000000000001ff0 0x01000000000001ff

def z691 : W := mkw 0x00c6451920082082 0x000c645192008208 0xf1ce4d39200ce0cf 0x7f1ce4d39200ce0c

def z692 : W := mkw 0x0050054010904b08 0x00050054010904b0 0xb1f00fc038f0ff0d 0xfb1f00fc038f0ff0

def z693 : W := mkw 0x0000900008050000 0x0000090000805000 0x0001f000000f0002 0x00001f000000f000

def z694 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x4031f3c7d8001c07 0xa4031f3c7d8001c0

def z695 : W := mkw 0x0000000800002082 0x0000000080000208 0x50000c380000e0c4 0x150000c380000e0c

def z696 : W := mkw 0x00c64511203a4220 0x800c64511203a422 0xa1ce410120ff033b 0x6a1ce410120ff033

def z697 : W := mkw 0x02008a0209049441 0x002008a020904944 0x7e018e063f0cfcce 0xf7e018e063f0cfcc

def z698 : W := mkw 0x1002800a2b3ef6e3 0x81002800a2b3ef6e 0x300000003ffffff8 0x0300000003ffffff

def z699 : W := mkw 0x0010004250800d59 0x40010004250800d5 0x503003c7d8801ffd 0xa503003c7d8801ff

def z700 : W := mkw 0x161b9a2e3b8db4c3 0x0161b9a2e3b8db4c 0x7e3ffe3e3f8ffccf 0xf7e3ffe3e3f8ffcc

def z701 : W := mkw 0x0000000000324220 0x8000000000032422 0x0000000000f30330 0x00000000000f3033

def z702 : W := mkw 0x89f6751934fb62a2 0x889f6751934fb62a 0xf1fe7d3920ffe3ff 0x7f1fe7d3920ffe3f

def z703 : W := mkw 0x0010900018850000 0x0001090001885000 0x4031f3c7d88f000f 0xa4031f3c7d88f000

def z704 : W := mkw 0x0010104050810918 0x4001010405081091 0x503071c1c08f03ff 0x2503071c1c08f03f

def z705 : W := mkw 0xaf79bfc01fd5db0c 0x0af79bfc01fd5db0 0xbff1bfc03ff0ff0d 0xfbff1bfc03ff0ff0

def z706 : W := mkw 0xcf39baa49ec50000 0x0cf39baa49ec5000 0x0e31b2c6df000000 0x80e31b2c6df00000

def z707 : W := mkw 0x00d6d55b78bf6ffb 0xc00d6d55b78bf6ff 0xa1ffbefef870fc00 0xda1ffbefef870fc0

def z708 : W := mkw 0x12400f7f4110fffb 0xc12400f7f4110fff 0x50000fffc000fff4 0x150000fffc000fff

def z709 : W := mkw 0x89f4755154f34b38 0xc89f4755154f34b3 0x81f071c1c0f30331 0x081f071c1c0f3033

def z710 : W := mkw 0xc2529fb5beef0000 0x0c2529fb5beef000 0x60000fffffff000c 0x160000fffffff000

def z711 : W := mkw 0x32400fac0110f286 0x032400fac0110f28 0x00000c380000e000 0x100000c380000e00

def z712 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xfffe0ff83ff0ff0f 0xffffe0ff83ff0ff0

def z713 : W := mkw 0xcdbff080beef0000 0x0cdbff080beef000 0xaffff0c0ffff000b 0xeaffff0c0ffff000

def z714 : W := mkw 0x12509f7f5995fffb 0xc12509f7f5995fff 0x5031ffffd88fffff 0xb5031ffffd88ffff

def z715 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xaff1f0003fff0009 0x8aff1f0003fff000

def z716 : W := mkw 0x32509fee5995ffdf 0x432509fee5995ffd 0x5031ffffd88fffff 0xb5031ffffd88ffff

def z717 : W := mkw 0x8dbff0407eef0918 0x48dbff0407eef091 0xeffff3c7ffff033f 0xeeffff3c7ffff033

def z718 : W := mkw 0x4f2b2aaca03a62a2 0x84f2b2aaca03a62a 0x3e31b2c6e0ffe3f8 0x83e31b2c6e0ffe3f

def z719 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xfff00fc7fff0ff0d 0xffff00fc7fff0ff0

def z720 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x2e0f8e3e3f0cfc0a 0xf2e0f8e3e3f0cfc0

def z721 : W := mkw 0x8d39b0001ec50000 0x08d39b0001ec5000 0x8ff1b0001ff00001 0x88ff1b0001ff0000

def z722 : W := mkw 0x22400f800110d204 0x022400f800110d20 0x10000e000000fc04 0x110000e000000fc0

def z723 : W := mkw 0x4fad6ab580000000 0x04fad6ab58000000 0xcffff2ffc0000003 0xecffff2ffc000000

def z724 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0f8e3e3f8ffffe 0xf7e0f8e3e3f8ffff

def z725 : W := mkw 0x62500ff59190db0c 0x062500ff59190db0 0x5031ffffd880ff0f 0xb5031ffffd880ff0

def z726 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbff00dc03ff0ff09 0x5bff00dc03ff0ff0

def z727 : W := mkw 0x2b609f824d55d655 0x42b609f824d55d65 0xefc1fc07e77fe0f2 0x5efc1fc07e77fe0f

def z728 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x30000fc02000ff0c 0x730000fc02000ff0

def z729 : W := mkw 0x4ded65b580000000 0x04ded65b58000000 0xcffff1ffc0000003 0xecffff1ffc000000

def z730 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbfc00fc03ff0ff0c 0x5bfc00fc03ff0ff0

def z731 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1cfcf3f20ffe3ff 0xff1cfcf3f20ffe3f

def z732 : W := mkw 0x06098a2609049441 0x006098a260904944 0x7e0f8e3e3f0cfcce 0xf7e0f8e3e3f0cfcc

def z733 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xaff0000027f00001 0x4aff0000027f0000

def z734 : W := mkw 0x89b4700014e30000 0x089b4700014e3000 0x8ff070001ff30001 0x88ff070001ff3000

def z735 : W := mkw 0x548fe03faa2e24e3 0x8548fe03faa2e24e 0x400ff03fc00f00f2 0x0400ff03fc00f00f

def z736 : W := mkw 0x8012904a7eff6ffb 0xc8012904a7eff6ff 0x300000003ffffff8 0x0300000003ffffff

def z737 : W := mkw 0x8dbf600036ea0000 0x08dbf600036ea000 0xaffe00003f700000 0xcaffe00003f70000

def z738 : W := mkw 0x001090425cc50d59 0x4001090425cc50d5 0x7031f3c7ffff1fff 0xa7031f3c7ffff1ff

def z739 : W := mkw 0x12864a2e212ab4c3 0x012864a2e212ab4c 0xf1ce4e3e20fffccf 0x7f1ce4e3e20fffcc

def z740 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xaff000003f700000 0xcaff000003f70000

def z741 : W := mkw 0x8dbff0403eef0908 0x08dbff0403eef090 0xaffff2c03fff1c0b 0xeaffff2c03fff1c0

def z742 : W := mkw 0x060b0a2c2108b082 0x0060b0a2c2108b08 0x7e0f8e3e3f0cfcce 0xf7e0f8e3e3f0cfcc

def z743 : W := mkw 0x8930300014c10000 0x08930300014c1000 0xaff030003ff00009 0xeaff030003ff0000

def z744 : W := mkw 0x801090425ec50d59 0x4801090425ec50d5 0x5031f3c7df8f1fff 0xa5031f3c7df8f1ff

def z745 : W := mkw 0x12400f3f0110f6e3 0x812400f3f0110f6e 0x50000e3e0000fcc4 0x150000e3e0000fcc

def z746 : W := mkw 0x22c64fd9213afbae 0x822c64fd9213afba 0x500e4ff9000ffff6 0x1500e4ff9000ffff

def z747 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xfffff1013fff1fff 0xefffff1013fff1ff

def z748 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xbffff1c1ffff1ffb 0xebffff1c1ffff1ff

def z749 : W := mkw 0x0dbdf0425cc50d59 0x40dbdf0425cc50d5 0xfffff3c7ffff1fff 0xefffff3c7ffff1ff

def z750 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0x4e3fffffc0000006 0x94e3fffffc000000

def z751 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x5e0f8e3e1f0cfcc6 0x95e0f8e3e1f0cfcc

def z752 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1ce0d3920ffe3fc 0x5f1ce0d3920ffe3f

def z753 : W := mkw 0x6fed6fb58550d204 0x06fed6fb58550d20 0xffffffffff70fc0f 0xfffffffffff70fc0

def z754 : W := mkw 0x9dbff06e7eef2ddb 0x49dbff06e7eef2dd 0xfffff3ffffff1fff 0xefffff3ffffff1ff

def z755 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xeffff1c7ffff03fb 0xeeffff1c7ffff03f

def z756 : W := mkw 0x448d603580000000 0x0448d60358000000 0x403ff2ffc0000002 0x8403ff2ffc000000

def z757 : W := mkw 0x0ded651100000000 0x00ded65110000000 0xcfffffffc0000007 0xfcfffffffc000000

def z758 : W := mkw 0x2930004015d0db0c 0x02930004015d0db0 0xbfc000003ff0ff08 0x4bfc000003ff0ff0

def z759 : W := mkw 0x8daf6042666a0d59 0x48daf6042666a0d5 0xffce03c7e7701ff4 0x4ffce03c7e7701ff

def z760 : W := mkw 0x0010004010800908 0x0001000401080090 0x5031f3c7d88f1fff 0xa5031f3c7d88f1ff

def z761 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x2e0e0c383f00fc00 0x52e0e0c383f00fc0

def z762 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x00000ec00000fc00 0x100000ec00000fc0

def z763 : W := mkw 0x8dbdf0001ee70000 0x08dbdf0001ee7000 0x8ff1f0001fff000b 0xa8ff1f0001fff000

def z764 : W := mkw 0x8d79b5191ed562a2 0x88d79b5191ed562a 0x5e31bd391f00e3f4 0x95e31bd391f00e3f

def z765 : W := mkw 0x8dbd700014e30000 0x08dbd700014e3000 0xaffff0003ff3000b 0xeaffff0003ff3000

def z766 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x503fffffd88f1fff 0xf503fffffd88f1ff

def z767 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xcfffbefec0000006 0xfcfffbefec000000

def z768 : W := mkw 0x8dbff05b7eef2dfb 0xc8dbff05b7eef2df 0xfffff3ffffff1fff 0xefffff3ffffff1ff

def z769 : W := mkw 0x2b300ac015d0db0c 0x02b300ac015d0db0 0xbff002c03ff0ff09 0xebff002c03ff0ff0

def z770 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xfff041013fff03ff 0xefff041013fff03f

def z771 : W := mkw 0x72400fff8110ffcf 0x072400fff8110ffc 0x50000fffc000ffc4 0x150000fffc000ffc

def z772 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0fcf3f3f0cfccf 0xf7e0fcf3f3f0cfcc

def z773 : W := mkw 0x00864008202a2082 0x000864008202a208 0xf1ce4d3920ffe3ff 0x7f1ce4d3920ffe3f

def z774 : W := mkw 0x9012904a7fefbddb 0x49012904a7fefbdd 0x300000003ffffff8 0x0300000003ffffff

def z775 : W := mkw 0x8dbff0423eef0d49 0x08dbff0423eef0d4 0xfffff3c63fff1fcf 0xefffff3c63fff1fc

def z776 : W := mkw 0x093280003ecc0000 0x0093280003ecc000 0xaff000003ffc0009 0xeaff000003ffc000

def z777 : W := mkw 0x4f292aa480000000 0x04f292aa48000000 0x4e3fffffc0000007 0xf4e3fffffc000000

def z778 : W := mkw 0x12408f3f0914f6e3 0x812408f3f0914f6e 0x5001cf3f188fffff 0xb5001cf3f188ffff

def z779 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xeffffc383fff000f 0xfeffffc383fff000

def z780 : W := mkw 0x893290427eef0d59 0x4893290427eef0d5 0xbff003c03fff1ffd 0xebff003c03fff1ff

def z781 : W := mkw 0x6b700fd195d0db0c 0x06b700fd195d0db0 0xbff00fc1fff0ff0d 0xfbff00fc1fff0ff0

def z782 : W := mkw 0x8dbff0403eef0908 0x08dbff0403eef090 0xfffff3c7ffff1f0f 0xefffff3c7ffff1f0

def z783 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e3fbefeff0cfcce 0xf7e3fbefeff0cfcc

def z784 : W := mkw 0x22400fc24110df5d 0x422400fc24110df5 0x10000fc6c000ff04 0x110000fc6c000ff0

def z785 : W := mkw 0x8dbff0403eef0908 0x08dbff0403eef090 0xfffff3c13fff1fff 0xefffff3c13fff1ff

def z786 : W := mkw 0x948fe02e2a2e24c3 0x0948fe02e2a2e24c 0x400f803e000c00c2 0x0400f803e000c00c

def z787 : W := mkw 0x00420508203a62a2 0x800420508203a62a 0xf1ce0d3820ffe3ff 0x7f1ce0d3820ffe3f

def z788 : W := mkw 0x8dbf600036ea0000 0x08dbf600036ea000 0xaffe000027f00001 0x4affe000027f0000

def z789 : W := mkw 0x22509fc25995df5d 0x422509fc25995df5 0x1031bfc6d800ff04 0x91031bfc6d800ff0

def z790 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbff003c03ff0ff09 0x8bff003c03ff0ff0

def z791 : W := mkw 0x649d607595d0db0c 0x0649d607595d0db0 0x700ff03ffff0ff0a 0x0700ff03ffff0ff0

def z792 : W := mkw 0x16cdcf370b36d661 0x816cdcf370b36d66 0x8fc1c3071ff31f31 0x88fc1c3071ff31f3

def z793 : W := mkw 0x4dad603580000000 0x04dad60358000000 0xcffff3ffc0000007 0xecffff3ffc000000

def z794 : W := mkw 0x62400ffd8110fbae 0x862400ffd8110fba 0x50000fffc000fff4 0x150000fffc000fff

def z795 : W := mkw 0x22400fd10110db0c 0x022400fd10110db0 0x50000ff90000ff04 0x150000ff90000ff0

def z796 : W := mkw 0x6fed6fb584504204 0x06fed6fb58450420 0xcfffffffc0700007 0xfcfffffffc070000

def z797 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xaff1f0003ff0000b 0xeaff1f0003ff0000

def z798 : W := mkw 0x32400fca0110ffcf 0x032400fca0110ffc 0x10000fc00000ffc4 0x110000fc00000ffc

def z799 : W := mkw 0x8dad600006620000 0x08dad60000662000 0x8fc0000007700000 0x08fc000000770000

def z800 : W := mkw 0x4fed6fb581009000 0x04fed6fb58100900 0xdfffffffc000fc07 0xfdfffffffc000fc0

def z801 : W := mkw 0x0930000015c09000 0x00930000015c0900 0xbff000003ff0fc09 0xebff000003ff0fc0

def z802 : W := mkw 0x02500f401190db08 0x002500f401190db0 0xbff00fc03ff0ff0d 0xfbff00fc03ff0ff0

def z803 : W := mkw 0x160b0a2c2308b082 0x0160b0a2c2308b08 0x2e0e0e383f00fc00 0xd2e0e0e383f00fc0

def z804 : W := mkw 0x4ded65b580000000 0x04ded65b58000000 0xc1fff3ffc0000007 0xac1fff3ffc000000

def z805 : W := mkw 0x8dbff0407eef0918 0x48dbff0407eef091 0xaffff0003fff033b 0xeaffff0003fff033

def z806 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1ce4c3920ffe3fa 0x5f1ce4c3920ffe3f

def z807 : W := mkw 0x6b700ff595d0db0c 0x06b700ff595d0db0 0xbff00ff83ff0ff0d 0xfbff00ff83ff0ff0

def z808 : W := mkw 0x22400fd10110db2c 0x822400fd10110db2 0x10000fc10000ff34 0x110000fc10000ff3

def z809 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xbffffc003fffe00f 0xfbffffc003fffe00

def z810 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xafffb2c6ff701c00 0xcafffb2c6ff701c0

def z811 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1fe4ff920ffe3ff 0xff1fe4ff920ffe3f

def z812 : W := mkw 0x0930004014c00908 0x00930004014c0090 0xaff001c03ff00309 0xeaff001c03ff0030

def z813 : W := mkw 0xcdbff035beef0000 0x0cdbff035beef000 0xeffff3ffffff000f 0xeeffff3ffffff000

def z814 : W := mkw 0x9dbff03f3eef24e3 0x89dbff03f3eef24e 0xeffff03f3fff00fb 0xeeffff03f3fff00f

def z815 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xbfce00003fff1ff8 0x4bfce00003fff1ff

def z816 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xfffff2c6ffff1ccf 0xefffff2c6ffff1cc

def z817 : W := mkw 0x0930004014c00908 0x00930004014c0090 0xaff002c03ff01c09 0xeaff002c03ff01c0

def z818 : W := mkw 0x8dbff0083eef2082 0x08dbff0083eef208 0xaffffc383fffe00b 0xfaffffc383fffe00

def z819 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xaffe00003fff0009 0xeaffe00003fff000

def z820 : W := mkw 0x89b4700014e30000 0x089b4700014e3000 0xaff0700027f30001 0x4aff0700027f3000

def z821 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0f8fffff0cfcce 0xf7e0f8fffff0cfcc

def z822 : W := mkw 0x62400fb58110d204 0x062400fb58110d20 0x40000fffc000e004 0x140000fffc000e00

def z823 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xaffff3c03fff000f 0xeaffff3c03fff000

def z824 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0f8f3f3f0cfffe 0xf7e0f8f3f3f0cfff

def z825 : W := mkw 0x02400f000110d200 0x002400f000110d20 0x10000f000000ff04 0x110000f000000ff0

def z826 : W := mkw 0x093090425cc50d59 0x4093090425cc50d5 0xbff000003fff1ff9 0xebff000003fff1ff

def z827 : W := mkw 0x29f445d114d04b0c 0x029f445d114d04b0 0x81f041c100f00301 0x081f041c100f0030

def z828 : W := mkw 0x8dbf700036eb0000 0x08dbf700036eb000 0xafce000027f30000 0x4afce000027f3000

def z829 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0f8e3e3f00fcc4 0xd7e0f8e3e3f00fcc

def z830 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xb1ce4d3920ffe3f9 0x5b1ce4d3920ffe3f

def z831 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0e0e3e3f0cfccc 0x57e0e0e3e3f0cfcc

def z832 : W := mkw 0x22400fc20110df4d 0x022400fc20110df4 0x50000fc60000ffc4 0x150000fc60000ffc

def z833 : W := mkw 0x0d3b80423ecc0d49 0x00d3b80423ecc0d4 0xffff83c63ffc1fcf 0xeffff83c63ffc1fc

def z834 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0x8fffbffec0000005 0xf8fffbffec000000

def z835 : W := mkw 0x6b700fe495d0db0c 0x06b700fe495d0db0 0xbff00fc6fff0ff0d 0xfbff00fc6fff0ff0

def z836 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x10000fc01800ff0c 0xb10000fc01800ff0

def z837 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x4031f3c7d88f1ff3 0x84031f3c7d88f1ff

def z838 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xfffff2063fff1fff 0xefffff2063fff1ff

def z839 : W := mkw 0x0000904248050d59 0x40000904248050d5 0x5031f3c7c00f1ff7 0xa5031f3c7c00f1ff

def z840 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x5031f3c7c08f1ff7 0x05031f3c7c08f1ff

def z841 : W := mkw 0x060b8a082b0cb082 0x0060b8a082b0cb08 0x7e0f8e383f0cfcce 0xf7e0f8e383f0cfcc

def z842 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xbffff2c6ffff1ffb 0xebffff2c6ffff1ff

def z843 : W := mkw 0x160b8a2e2b2eb4e3 0x8160b8a2e2b2eb4e 0x7e0f8e3e3f0ffcfe 0xf7e0f8e3e3f0ffcf

def z844 : W := mkw 0x4f292aa480000000 0x04f292aa48000000 0x4e3fb2fec0000002 0x84e3fb2fec000000

def z845 : W := mkw 0x69f465d194f24b2c 0x869f465d194f24b2 0x81f071c1c0f30331 0x081f071c1c0f3033

def z846 : W := mkw 0x8d3bb0003eef0000 0x08d3bb0003eef000 0xaff1b0003fff0009 0xeaff1b0003fff000

def z847 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbff00fc03ffffffd 0xfbff00fc03ffffff

def z848 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbfc00d003ff0ff0d 0x7bfc00d003ff0ff0

def z849 : W := mkw 0x161b1a6c7389b99a 0x4161b1a6c7389b99 0x2e3e7df9e783e331 0x52e3e7df9e783e33

def z850 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x10000c000000ff00 0x110000c000000ff0

def z851 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xafce400027f30001 0x4afce400027f3000

def z852 : W := mkw 0x22400fe40110db0c 0x022400fe40110db0 0x50000ffe0000ff04 0x150000ffe0000ff0

def z853 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1fe7df9e0ffe3ff 0x7f1fe7df9e0ffe3f

def z854 : W := mkw 0x32400fae0110f6c7 0x032400fae0110f6c 0x50000e3e0000fcc4 0x150000e3e0000fcc

def z855 : W := mkw 0x040b800a2a0c24c3 0x0040b800a2a0c24c 0x7e0f8e3e3f0cfcce 0xf7e0f8e3e3f0cfcc

def z856 : W := mkw 0x8dbf700036eb0000 0x08dbf700036eb000 0xaffff00027f30003 0xeaffff00027f3000

def z857 : W := mkw 0x8daf6008266a2082 0x08daf6008266a208 0xafce0c382770e000 0x5afce0c382770e00

def z858 : W := mkw 0xd48ff03faa2f24c3 0x0d48ff03faa2f24c 0x400ff03fc00f00c2 0x0400ff03fc00f00c

def z859 : W := mkw 0x49e4659180000000 0x049e465918000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z860 : W := mkw 0x89a4600004620000 0x089a460000462000 0xafc0000027700000 0x4afc000002770000

def z861 : W := mkw 0x00864000202a0000 0x000864000202a000 0xafce40003fff000b 0xeafce40003fff000

def z862 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xcfffbfffc0000004 0xdcfffbfffc000000

def z863 : W := mkw 0x4fed6fb58110d200 0x04fed6fb58110d20 0xfffffffffff0ff0f 0xffffffffffff0ff0

def z864 : W := mkw 0x148fc02e2a2e24c3 0x0148fc02e2a2e24c 0x400fc03e000f00c2 0x0400fc03e000f00c

def z865 : W := mkw 0x848ff01b6a2f24f3 0xc848ff01b6a2f24f 0x400ff03fc00f00f2 0x0400ff03fc00f00f

def z866 : W := mkw 0x22400f990110f2a6 0x822400f990110f2a 0x50000d390000e3f4 0x150000d390000e3f

def z867 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e3fffffff8fffff 0xf7e3fffffff8ffff

def z868 : W := mkw 0x2bb64ad935eab9ae 0x82bb64ad935eab9a 0x4e3e42f91f0f1cf2 0x84e3e42f91f0f1cf

def z869 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xafce4000277f0002 0x4afce4000277f000

def z870 : W := mkw 0x8930100014e30000 0x08930100014e3000 0xaff000003ff30009 0xeaff000003ff3000

def z871 : W := mkw 0x948ff00a2a2f24c3 0x0948ff00a2a2f24c 0x000ff000000f00c2 0x0000ff000000f00c

def z872 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xafc000003ff00008 0x4afc000003ff0000

def z873 : W := mkw 0x02400f000110d200 0x002400f000110d20 0xbfc00e003f70fc0c 0xfbfc00e003f70fc0

def z874 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xcffffdffc0000003 0x5cffffdffc000000

def z875 : W := mkw 0x0920000004400000 0x0092000000440000 0xafc0000027f00009 0x6afc0000027f0000

def z876 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xeffff1013fff000f 0xeeffff1013fff000

def z877 : W := mkw 0x09b6d0427cef0d59 0x409b6d0427cef0d5 0xfffff3c7ffff1fff 0xefffff3c7ffff1ff

def z878 : W := mkw 0xcfed6fb584620000 0x0cfed6fb58462000 0xcfffffffc0700007 0xfcfffffffc070000

def z879 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xaffff1c1ffff000b 0xeaffff1c1ffff000

def z880 : W := mkw 0x6f39bae6ddc59d5d 0x46f39bae6ddc59d5 0x0e31b2c6df001c00 0x80e31b2c6df001c0

def z881 : W := mkw 0x2b600f800550d204 0x02b600f800550d20 0xafc00e003f70fc00 0xdafc00e003f70fc0

def z882 : W := mkw 0x22509fc25995df5d 0x422509fc25995df5 0x10000fc0188ffffc 0x110000fc0188ffff

def z883 : W := mkw 0x40c64599a03a62a2 0x840c64599a03a62a 0xf1ce4df9e0ffe3ff 0x7f1ce4df9e0ffe3f

def z884 : W := mkw 0x8dbdf0001ee70000 0x08dbdf0001ee7000 0xaff1f0003ff30009 0xeaff1f0003ff3000

def z885 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xaffe000027700001 0xeaffe00002770000

def z886 : W := mkw 0x8dbff0083eef2082 0x08dbff0083eef208 0xfffffd393fffe3ff 0xffffffd393fffe3f

def z887 : W := mkw 0x0920000004400000 0x0092000000440000 0xafc000003f700008 0xeafc000003f70000

def z888 : W := mkw 0x9bb47a2e15e3b4c3 0x09bb47a2e15e3b4c 0xd1f07e3e00f3fcc5 0x1d1f07e3e00f3fcc

def z889 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xbffff1003fff030f 0xebffff1003fff030

def z890 : W := mkw 0x22400fc04110db1c 0x422400fc04110db1 0x10000fc1c000ff34 0x110000fc1c000ff3

def z891 : W := mkw 0x4fed6fb580220020 0x84fed6fb58022002 0xcfffffffc0030037 0xfcfffffffc003003

def z892 : W := mkw 0x8dbff0403eef0908 0x08dbff0403eef090 0xbffff0003fff1f0b 0xebffff0003fff1f0

def z893 : W := mkw 0x59e6e59bab0cb4c3 0x059e6e59bab0cb4c 0xb1f071c1ff0cfcc9 0x0b1f071c1ff0cfcc

def z894 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xe1ce4d3920ffe3f3 0x5e1ce4d3920ffe3f

def z895 : W := mkw 0x8dbfe0003eee0000 0x08dbfe0003eee000 0xafff80003ffc000b 0xeafff80003ffc000

def z896 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1ce0c3820ffe3fe 0x7f1ce0c3820ffe3f

def z897 : W := mkw 0x6fed6fb58110d204 0x06fed6fb58110d20 0xcfffffffc000e007 0xfcfffffffc000e00

def z898 : W := mkw 0x849fd0003eef0000 0x0849fd0003eef000 0xafcfc0003fff000b 0xeafcfc0003fff000

def z899 : W := mkw 0x049fd0427aaf0d59 0x4049fd0427aaf0d5 0xfffff3c7ffff1fff 0xefffff3c7ffff1ff

def z900 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xafce400027700003 0x6afce40002770000

def z901 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0xffcf8e3e3ffcfccf 0xfffcf8e3e3ffcfcc

def z902 : W := mkw 0x0d3b90427ecd0d59 0x40d3b90427ecd0d5 0xfffff3c7ffff1fff 0xefffff3c7ffff1ff

def z903 : W := mkw 0x8dbdf0001ee70000 0x08dbdf0001ee7000 0x8ff1b0001f700000 0x88ff1b0001f70000

def z904 : W := mkw 0x160b8a2e2b2eb4c3 0x0160b8a2e2b2eb4c 0x7e0f8e3e3ffffcce 0xf7e0f8e3e3ffffcc

def z905 : W := mkw 0x09b6401934ea20a2 0x809b6401934ea20a 0xeffe40393fff00fb 0xeeffe40393fff00f

def z906 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x7031ffc7f88fffff 0xf7031ffc7f88ffff

def z907 : W := mkw 0x4fed6fb580104200 0x04fed6fb58010420 0xdfffffffc000e307 0xfdfffffffc000e30

def z908 : W := mkw 0x22500f4015d0db0c 0x022500f4015d0db0 0xbfc00f003ff0ff0d 0xfbfc00f003ff0ff0

def z909 : W := mkw 0x0dbfe0003ecc0000 0x00dbfe0003ecc000 0xaffff0003ffc000b 0xeaffff0003ffc000

def z910 : W := mkw 0x4ffdfff7d8850d59 0x44ffdfff7d8850d5 0x9fce0c38188f1ff8 0x59fce0c38188f1ff

def z911 : W := mkw 0x0930004254c00d59 0x40930004254c00d5 0xfff003c7fff01ffd 0xefff003c7fff01ff

def z912 : W := mkw 0x89b4f0001ce70000 0x089b4f0001ce7000 0xaff1f0003fff000b 0xeaff1f0003fff000

def z913 : W := mkw 0xcdbff035beef0000 0x0cdbff035beef000 0xaffff0383fff000b 0xeaffff0383fff000

def z914 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xb1ce0d3820ffe3fd 0x7b1ce0d3820ffe3f

def z915 : W := mkw 0x12400f2e0110f6c3 0x012400f2e0110f6c 0x50000f3e0000ffc4 0x150000f3e0000ffc

def z916 : W := mkw 0x8dbff0027eef0451 0x48dbff0027eef045 0xeffff3c7ffff00ff 0xeeffff3c7ffff00f

def z917 : W := mkw 0x448d603580000000 0x0448d60358000000 0x403ff1ffc0000003 0x0403ff1ffc000000

def z918 : W := mkw 0x160b8a2e6b0cb4d3 0x4160b8a2e6b0cb4d 0x7e0f8e3fff0cfcfe 0xf7e0f8e3fff0cfcf

def z919 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xeffff2c7ffff1cfb 0xeeffff2c7ffff1cf

def z920 : W := mkw 0x22500fc01190db0c 0x022500fc01190db0 0x10000fc01880ff0c 0x110000fc01880ff0

def z921 : W := mkw 0x8daf6008266a2082 0x08daf6008266a208 0xffce0c38277ce0ce 0x7ffce0c38277ce0c

def z922 : W := mkw 0x948ff02e6a2f24d3 0x4948ff02e6a2f24d 0x400ff03fc00f00f2 0x0400ff03fc00f00f

def z923 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xafcf80003fff000a 0xeafcf80003fff000

def z924 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xeffff3c7e7700007 0xeeffff3c7e770000

def z925 : W := mkw 0x4fed6fb584400000 0x04fed6fb58440000 0xefffffffe7700007 0xfefffffffe770000

def z926 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xafce40003fff000b 0x6afce40003fff000

def z927 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xaffff00027ff0003 0x4affff00027ff000

def z928 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0x8ffff0001fff0003 0x88ffff0001fff000

def z929 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xffce410127ff03ff 0x6ffce410127ff03f

def z930 : W := mkw 0x4fed6fb580324220 0x84fed6fb58032422 0xffffffffe0f3e33f 0xfffffffffe0f3e33

def z931 : W := mkw 0xcdbff024beef0000 0x0cdbff024beef000 0xaffff006ffff000b 0xeaffff006ffff000

def z932 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x7e31f3c7ff8f1fff 0xe7e31f3c7ff8f1ff

def z933 : W := mkw 0x22501fc05191db1c 0x422501fc05191db1 0x10307fc1c083ff35 0x110307fc1c083ff3

def z934 : W := mkw 0x093080021cc40441 0x0093080021cc4044 0xfff182063ffc1ccf 0xefff182063ffc1cc

def z935 : W := mkw 0x044b85192a1c62a2 0x8044b85192a1c62a 0x7e0f8d393f0ce3fe 0xf7e0f8d393f0ce3f

def z936 : W := mkw 0x46cd6fb580000000 0x046cd6fb58000000 0x403fffffc0000007 0xb403fffffc000000

def z937 : W := mkw 0x8d3bb0003ecd0000 0x08d3bb0003ecd000 0xafffb0003ffc000b 0xeafffb0003ffc000

def z938 : W := mkw 0x8dbff00a3eef24c3 0x08dbff00a3eef24c 0xfffffe3e3ffffccf 0xffffffe3e3ffffcc

def z939 : W := mkw 0x2b701fc015d1db0c 0x02b701fc015d1db0 0xbff07fc03ff3ff0d 0xfbff07fc03ff3ff0

def z940 : W := mkw 0x32400fee4110ffdf 0x432400fee4110ffd 0x50000fffc000fff4 0x150000fffc000fff

def z941 : W := mkw 0x66cd6ff58110db0c 0x066cd6ff58110db0 0x500fffffc000ff06 0x1500fffffc000ff0

def z942 : W := mkw 0x468d6a3580000000 0x0468d6a358000000 0x4e3fffffc0000007 0xf4e3fffffc000000

def z943 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x3e0f8c383f0cfcca 0xf3e0f8c383f0cfcc

def z944 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xaffff0003ff30001 0xcaffff0003ff3000

def z945 : W := mkw 0x8dafe0002e6e0000 0x08dafe0002e6e000 0xafcfc0003fff000b 0xeafcfc0003fff000

def z946 : W := mkw 0x42c44fb580000000 0x042c44fb58000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z947 : W := mkw 0xcdaf6035a66a0000 0x0cdaf6035a66a000 0xafce003827700000 0x4afce00382770000

def z948 : W := mkw 0x22400f990110f2a6 0x822400f990110f2a 0x00000c380000e000 0x100000c380000e00

def z949 : W := mkw 0xcdbff011beef0000 0x0cdbff011beef000 0xaffff001ffff000b 0xeaffff001ffff000

def z950 : W := mkw 0x0b700f0015d0d200 0x00b700f0015d0d20 0xbff00f003ff0ff0d 0xfbff00f003ff0ff0

def z951 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xaff003c03ff0000d 0xeaff003c03ff0000

def z952 : W := mkw 0x6b702fc095d0db0c 0x06b702fc095d0db0 0xbff03fc0fff0ff0d 0xfbff03fc0fff0ff0

def z953 : W := mkw 0x0012904a78af2dfb 0xc0012904a78af2df 0x10000000188f1ff8 0x010000000188f1ff

def z954 : W := mkw 0x22409fc24915df5d 0x422409fc24915df5 0x5001ffc7c00ffff6 0x15001ffc7c00ffff

def z955 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xc1ffffffc0000007 0x1c1ffffffc000000

def z956 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xaff040003fff000b 0xeaff040003fff000

def z957 : W := mkw 0x148fc03f2a2e24e3 0x8148fc03f2a2e24e 0xefcfc03f3fff00fb 0xeefcfc03f3fff00f

def z958 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xdfffffffd8001c0f 0xfdfffffffd8001c0

def z959 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xbffff2003fff1c0f 0xebffff2003fff1c0

def z960 : W := mkw 0x9dbff02e3eef24c3 0x09dbff02e3eef24c 0xfffffc3e3fffe0cf 0xffffffc3e3fffe0c

def z961 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xaffff0003f7f0002 0xcaffff0003f7f000

def z962 : W := mkw 0x40c66519a03a62a2 0x840c66519a03a62a 0xf1ce7d39e0ffe3ff 0x7f1ce7d39e0ffe3f

def z963 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xefffffffe0f0000f 0xfefffffffe0f0000

def z964 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e3f8ffe3f0cfccf 0xf7e3f8ffe3f0cfcc

def z965 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbff1ffc03ff0ff0f 0xfbff1ffc03ff0ff0

def z966 : W := mkw 0x3d7b85ee3edc6fcf 0x03d7b85ee3edc6fc 0xc1ff81fe00fc03c3 0x0c1ff81fe00fc03c

def z967 : W := mkw 0x0d39200014c00000 0x00d39200014c0000 0xaff1b0003ff00009 0xeaff1b0003ff0000

def z968 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xefffffffff00000f 0xfefffffffff00000

def z969 : W := mkw 0x1012904a7bbffffb 0xc1012904a7bbffff 0x300000003ffffff8 0x0300000003ffffff

def z970 : W := mkw 0x5fef6fbda33af2a2 0x85fef6fbda33af2a 0xafce0c382770e000 0x5afce0c382770e00

def z971 : W := mkw 0x560baa2eab0cb4c3 0x0560baa2eab0cb4c 0x7e0fbe3eff0cfcce 0xf7e0fbe3eff0cfcc

def z972 : W := mkw 0x8dbdf0001ec50000 0x08dbdf0001ec5000 0xaffff0003ff0000b 0xeaffff0003ff0000

def z973 : W := mkw 0x2b701fc055d1db1c 0x42b701fc055d1db1 0xbff03fc0fff0ff0d 0xfbff03fc0fff0ff0

def z974 : W := mkw 0x0930104054c10918 0x40930104054c1091 0xaff071c1fff30339 0xeaff071c1fff3033

def z975 : W := mkw 0x160b9a2e6b0db4d3 0x4160b9a2e6b0db4d 0x7e0f8e3e3f0ffcfe 0xf7e0f8e3e3f0ffcf

def z976 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xafce00003f700000 0x4afce00003f70000

def z977 : W := mkw 0x2930004015d0db0c 0x02930004015d0db0 0xbff003c03ff0ff0d 0xebff003c03ff0ff0

def z978 : W := mkw 0xe9f475d194f34b0c 0x0e9f475d194f34b0 0x81f071c1c0f30301 0x081f071c1c0f3030

def z979 : W := mkw 0x048fc0022a2e0441 0x0048fc0022a2e044 0xffcfc3073fff1fff 0xeffcfc3073fff1ff

def z980 : W := mkw 0x8dbff0027eef0451 0x48dbff0027eef045 0xfffff107ffff03ff 0xefffff107ffff03f

def z981 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xb1ce4c3820ffe3fb 0x7b1ce4c3820ffe3f

def z982 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xfffff007ffff1ffb 0xefffff007ffff1ff

def z983 : W := mkw 0x9f39ba665fc59d59 0x49f39ba665fc59d5 0x0e31b2c6df001c00 0x80e31b2c6df001c0

def z984 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xafcf800027700002 0xeafcf80002770000

def z985 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xaffff1013fff033b 0xeaffff1013fff033

def z986 : W := mkw 0xa6cfffc02b3fdb0c 0x0a6cfffc02b3fdb0 0x100fffc0000fff06 0x1100fffc0000fff0

def z987 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xfff00fc13ff0fffd 0xffff00fc13ff0fff

def z988 : W := mkw 0x160b9a2e6b0db4d3 0x4160b9a2e6b0db4d 0x7e0fbe3eff0cfcce 0xf7e0fbe3eff0cfcc

def z989 : W := mkw 0x8daff0002e6f0000 0x08daff0002e6f000 0xafce0000277f0000 0x4afce0000277f000

def z990 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xaffff0003f700003 0xeaffff0003f70000

def z991 : W := mkw 0x8dbf700036eb0000 0x08dbf700036eb000 0xaffe700027ff000b 0x6affe700027ff000

def z992 : W := mkw 0x22400f800110d204 0x022400f800110d20 0x00000fc00000e004 0x100000fc00000e00

def z993 : W := mkw 0x6fef6fbda57af2a6 0x86fef6fbda57af2a 0xafce0c382770e000 0x5afce0c382770e00

def z994 : W := mkw 0x8d39b0425ec50d59 0x48d39b0425ec50d5 0xfff1f3c7ffff1fff 0xefff1f3c7ffff1ff

def z995 : W := mkw 0x16090a2e0100b4c3 0x016090a2e0100b4c 0x7e0f8e3e3f00fcce 0xf7e0f8e3e3f00fcc

def z996 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xffce4d393fffe3ff 0xfffce4d393fffe3f

def z997 : W := mkw 0x4fad6ab580000000 0x04fad6ab58000000 0x4e3ffeffc0000006 0xf4e3ffeffc000000

def z998 : W := mkw 0x8dbff0193eef20a2 0x88dbff0193eef20a 0xfffffc393fffe0ff 0xffffffc393fffe0f

def z999 : W := mkw 0x8dbff0023eef0441 0x08dbff0023eef044 0xfffff3c7ffff1ccf 0xefffff3c7ffff1cc

def z1000 : W := mkw 0x0970054014d04b08 0x00970054014d04b0 0xbff00fc03ff0ff0d 0xfbff00fc03ff0ff0

def z1001 : W := mkw 0x16cfcf3f2b3ef6e3 0x816cfcf3f2b3ef6e 0x500fcf3f000ffff6 0x1500fcf3f000ffff

def z1002 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0f8f3e3f8cffcf 0xf7e0f8f3e3f8cffc

def z1003 : W := mkw 0x893290003eef0000 0x0893290003eef000 0xafc000003fff0008 0x4afc000003fff000

def z1004 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x10300fc00000ff05 0xb10300fc00000ff0

def z1005 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbff04fc13ff3ff3d 0xfbff04fc13ff3ff3

def z1006 : W := mkw 0x8dbf700036eb0000 0x08dbf700036eb000 0xaffe70003ff30009 0xeaffe70003ff3000

def z1007 : W := mkw 0x0930100014c10000 0x00930100014c1000 0xaff070003ff30009 0xeaff070003ff3000

def z1008 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xffffffffe000e00f 0xfffffffffe000e00

def z1009 : W := mkw 0x948ff03f2a2f24e3 0x8948ff03f2a2f24e 0x400ff03f000f00f2 0x0400ff03f000f00f

def z1010 : W := mkw 0x2b701fc055d1db1c 0x42b701fc055d1db1 0xfff1ffc7fff3ff3f 0xffff1ffc7fff3ff3

def z1011 : W := mkw 0x2b300a4015d0db0c 0x02b300a4015d0db0 0xbff00e003ff0ff0d 0xfbff00e003ff0ff0

def z1012 : W := mkw 0x06cd4f3500000000 0x006cd4f350000000 0xcfffffffc0000007 0xfcfffffffc000000

def z1013 : W := mkw 0x8dbff0027eef0451 0x48dbff0027eef045 0xaffff006ffff000b 0xeaffff006ffff000

def z1014 : W := mkw 0xcdbff037feef0451 0x4cdbff037feef045 0xeffff03fffff00fb 0xeeffff03fffff00f

def z1015 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x5031f3c7d80f1ff6 0x85031f3c7d80f1ff

def z1016 : W := mkw 0x8daff0002e6f0000 0x08daff0002e6f000 0xaffff000277f0003 0xeaffff000277f000

def z1017 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1ce4fffe0ffe3ff 0x7f1ce4fffe0ffe3f

def z1018 : W := mkw 0x69f465d194d04b0c 0x069f465d194d04b0 0x81f001c000f00301 0x081f001c000f0030

def z1019 : W := mkw 0x62400fb58110d204 0x062400fb58110d20 0x00000c380000e000 0x100000c380000e00

def z1020 : W := mkw 0x140b800a2b0cb4c3 0x0140b800a2b0cb4c 0x7e0f8c383f0cfcce 0xf7e0f8c383f0cfcc

def z1021 : W := mkw 0x8dbff0027eef0451 0x48dbff0027eef045 0xaffff0003fff00fb 0xeaffff0003fff00f

def z1022 : W := mkw 0xab703fc015d1db0c 0x0ab703fc015d1db0 0xbff03fc03ff0ff0d 0xfbff03fc03ff0ff0

def z1023 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x6e0f8e3e3f00fc06 0xf6e0f8e3e3f00fc0

def z1024 : W := mkw 0x5fed6fb583009000 0x05fed6fb58300900 0xcfffffffc7000007 0xfcfffffffc700000

def z1025 : W := mkw 0x22420fc82118fb8e 0x022420fc82118fb8 0x700e0ff8200cffce 0x7700e0ff8200cffc

def z1026 : W := mkw 0x8dbff0007eef0010 0x48dbff0007eef001 0xaffff001ffff003b 0xeaffff001ffff003

def z1027 : W := mkw 0x0b300a4015c09908 0x00b300a4015c0990 0xbff00fc03ff0ff0d 0xfbff00fc03ff0ff0

def z1028 : W := mkw 0x2b300ac015c0990c 0x02b300ac015c0990 0xbff00ec03ff0fc0d 0xfbff00ec03ff0fc0

def z1029 : W := mkw 0x4fed6fb581009000 0x04fed6fb58100900 0xefffffffe700e007 0xfefffffffe700e00

def z1030 : W := mkw 0x0920000004400000 0x0092000000440000 0xaff0000027700001 0xeaff000002770000

def z1031 : W := mkw 0x0dbfc0003eee0000 0x00dbfc0003eee000 0xafffc0003fff000b 0xeafffc0003fff000

def z1032 : W := mkw 0xcfed6fb586400000 0x0cfed6fb58640000 0xcfffffffc7000007 0xfcfffffffc700000

def z1033 : W := mkw 0x02020a082108b082 0x002020a082108b08 0x3e0e0e383f00fc0c 0xf3e0e0e383f00fc0

def z1034 : W := mkw 0x2b700f8015d0d204 0x02b700f8015d0d20 0xbff00e003ff0fc0d 0xfbff00e003ff0fc0

def z1035 : W := mkw 0x4fad6ab580000000 0x04fad6ab58000000 0x0e3fb2fec0000000 0x80e3fb2fec000000

def z1036 : W := mkw 0x0010904258850d59 0x40010904258850d5 0xf1f1f3c7f8ff1fff 0xef1f1f3c7f8ff1ff

def z1037 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbff00ec03ff0ff08 0xdbff00ec03ff0ff0

def z1038 : W := mkw 0x2b700fc055d0db1c 0x42b700fc055d0db1 0xbff00fc1fff0ff3d 0xfbff00fc1fff0ff3

def z1039 : W := mkw 0x093090001cc50000 0x0093090001cc5000 0xaff1b0003ff00009 0xeaff1b0003ff0000

def z1040 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xd1ce4d3900ffe3f7 0x1d1ce4d3900ffe3f

def z1041 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xcffffeffc0000002 0xdcffffeffc000000

def z1042 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xafc00c003f70fc00 0x5afc00c003f70fc0

def z1043 : W := mkw 0x0930000014c00000 0x00930000014c0000 0x8ff000001ff00001 0x88ff000001ff0000

def z1044 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x3e0f8e3e3f00fc0c 0xf3e0f8e3e3f00fc0

def z1045 : W := mkw 0x0042050820186282 0x0004205082018628 0xf1ce4d3920ffe3ff 0x7f1ce4d3920ffe3f

def z1046 : W := mkw 0x3012904a7fddffdf 0x43012904a7fddffd 0x300000003ffffff8 0x0300000003ffffff

def z1047 : W := mkw 0x89b6700034eb0000 0x089b6700034eb000 0xaffe70003fff000b 0xeaffe70003fff000

def z1048 : W := mkw 0x00c4451100104200 0x000c445110010420 0xf1ce4d3920ffe3ff 0x7f1ce4d3920ffe3f

def z1049 : W := mkw 0x8daf6019266a20a2 0x88daf6019266a20a 0xefce4039277f00f2 0x4efce4039277f00f

def z1050 : W := mkw 0x040b80002a0c0000 0x0040b80002a0c000 0xafcf80003ffc000b 0xeafcf80003ffc000

def z1051 : W := mkw 0x8dbff0023eef0441 0x08dbff0023eef044 0xaffff2063fff1c0b 0xeaffff2063fff1c0

def z1052 : W := mkw 0x1012904a7b8dbddb 0x41012904a7b8dbdd 0x300000003f0cfcc8 0x0300000003f0cfcc

def z1053 : W := mkw 0x2b600f800550d204 0x02b600f800550d20 0xbfc00c003f70fc08 0x5bfc00c003f70fc0

def z1054 : W := mkw 0x6b700ff595d0db0c 0x06b700ff595d0db0 0xfff1fffffff0ff0f 0xffff1fffffff0ff0

def z1055 : W := mkw 0x8dbf600036ea0000 0x08dbf600036ea000 0xafce00003ff00008 0x4afce00003ff0000

def z1056 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x50000fc10000fff4 0x150000fc10000fff

def z1057 : W := mkw 0x0000800208040441 0x0000080020804044 0x5031f3c7d88f1fff 0xa5031f3c7d88f1ff

def z1058 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xeffff2063fff000f 0xeeffff2063fff000

def z1059 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xaffff2c6ffff000b 0xeaffff2c6ffff000

def z1060 : W := mkw 0x8dafe0002e6e0000 0x08dafe0002e6e000 0xafcf8000277c0002 0x4afcf8000277c000

def z1061 : W := mkw 0x060b8a242b0c9000 0x0060b8a242b0c900 0x7e0f8e3e3f0cfc0e 0xf7e0f8e3e3f0cfc0

def z1062 : W := mkw 0x0b600f800110d200 0x00b600f800110d20 0xbff00fc03ff0ff0d 0xfbff00fc03ff0ff0

def z1063 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xfff18fc63ff0ff0f 0xffff18fc63ff0ff0

def z1064 : W := mkw 0x9dbff0263eef0441 0x09dbff0263eef044 0xaffff0063fff000b 0xeaffff0063fff000

def z1065 : W := mkw 0x4fed6fb581009000 0x04fed6fb58100900 0xcfffffffdf001c07 0xfcfffffffdf001c0

def z1066 : W := mkw 0x8d3b90003eef0000 0x08d3b90003eef000 0xafff80003fff000b 0xeafff80003fff000

def z1067 : W := mkw 0x00864008203a62a2 0x800864008203a62a 0xf1ce4c3820ffe3ff 0x7f1ce4c3820ffe3f

def z1068 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbff00ec03f70fc0c 0xfbff00ec03f70fc0

def z1069 : W := mkw 0x02400f190110f2a2 0x802400f190110f2a 0x50000f390000fff4 0x150000f390000fff

def z1070 : W := mkw 0x160b0a2c2308b082 0x0160b0a2c2308b08 0x3e0e0c383f00fc08 0x53e0e0c383f00fc0

def z1071 : W := mkw 0x8dbff0243eef0000 0x08dbff0243eef000 0xeffff03e3fff000b 0xeeffff03e3fff000

def z1072 : W := mkw 0x22400f800110d204 0x022400f800110d20 0x10000d000000e304 0x110000d000000e30

def z1073 : W := mkw 0x9dbff02c3eef2082 0x09dbff02c3eef208 0xaffff0383fff000b 0xeaffff0383fff000

def z1074 : W := mkw 0x4fad6aa480000000 0x04fad6aa48000000 0xcffffefec0000007 0xfcffffefec000000

def z1075 : W := mkw 0x893290427eef0d59 0x4893290427eef0d5 0xfff1f3c7ffff1fff 0xefff1f3c7ffff1ff

def z1076 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xaff00ec03ff0fc09 0xfaff00ec03ff0fc0

def z1077 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xeff1f3c7fff0000f 0xeeff1f3c7fff0000

def z1078 : W := mkw 0x4fed6fb580104200 0x04fed6fb58010420 0xcfffffffc0f00307 0xfcfffffffc0f0030

def z1079 : W := mkw 0x8dafe0002e6e0000 0x08dafe0002e6e000 0xafcf80003f700000 0xcafcf80003f70000

def z1080 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xafce000027ff0008 0x4afce000027ff000

def z1081 : W := mkw 0x8dbf600036ea0000 0x08dbf600036ea000 0xaffff0003ff0000b 0xeaffff0003ff0000

def z1082 : W := mkw 0x8d39b0425ec50d59 0x48d39b0425ec50d5 0xbff1b3c6fff01f0d 0xebff1b3c6fff01f0

def z1083 : W := mkw 0x8dbdf0425ee70d59 0x48dbdf0425ee70d5 0x8ff1f3c7dff31f31 0x88ff1f3c7dff31f3

def z1084 : W := mkw 0x22500fd91190fbae 0x822500fd91190fba 0x50304ff9188fffff 0xb50304ff9188ffff

def z1085 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xaffe70003fff0009 0x4affe70003fff000

def z1086 : W := mkw 0x4dad60b580000000 0x04dad60b58000000 0x403ff0ffc0000002 0x0403ff0ffc000000

def z1087 : W := mkw 0x0000000000000000 0x0000000000000000 0xafc000003ff00009 0xeafc000003ff0000

def z1088 : W := mkw 0x22500fc01190db0c 0x022500fc01190db0 0x10300fc00080ff05 0x110300fc00080ff0

def z1089 : W := mkw 0x0b700f8015c09000 0x00b700f8015c0900 0xbff00fc03ff0fc0d 0xfbff00fc03ff0fc0

def z1090 : W := mkw 0x22400fc80110fb8e 0x022400fc80110fb8 0x50000ff80000ffc4 0x150000ff80000ffc

def z1091 : W := mkw 0x02000a0001009000 0x002000a000100900 0xbfc00e003ff0fc0d 0xfbfc00e003ff0fc0

def z1092 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbff04fc03fffff0f 0xfbff04fc03fffff0

def z1093 : W := mkw 0x8dbff0023eef0441 0x08dbff0023eef044 0xbffff0003fff1ccb 0xebffff0003fff1cc

def z1094 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x3e0e0e383f0cfccc 0xf3e0e0e383f0cfcc

def z1095 : W := mkw 0x848ff0002a2f0000 0x0848ff0002a2f000 0xafcff0003fff000b 0xeafcff0003fff000

def z1096 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0x8fffffffc0000001 0xd8fffffffc000000

def z1097 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xaffff00027ff000b 0xeaffff00027ff000

def z1098 : W := mkw 0x8dbff0193eef20a2 0x88dbff0193eef20a 0xaffff0383fff000b 0xeaffff0383fff000

def z1099 : W := mkw 0x8dbdf0001ee70000 0x08dbdf0001ee7000 0x8ffff0001ff30003 0xe8ffff0001ff3000

def z1100 : W := mkw 0x148fc03f2a2e24e3 0x8148fc03f2a2e24e 0x400f803e000c00c2 0x0400f803e000c00c

def z1101 : W := mkw 0x8dbff0113eef0020 0x88dbff0113eef002 0xaffff0013fff003b 0xeaffff0013fff003

def z1102 : W := mkw 0x22400fc80110fbae 0x822400fc80110fba 0x10000fc00000fff4 0x110000fc00000fff

def z1103 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0x8ffffefec0000003 0xf8ffffefec000000

def z1104 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x50000fc7c000ff04 0x150000fc7c000ff0

def z1105 : W := mkw 0x89b4704054e30918 0x489b4704054e3091 0xbff073c1fff31f3d 0xebff073c1fff31f3

def z1106 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xfffff0003fff00cf 0xefffff0003fff00c

def z1107 : W := mkw 0x8dbff0023eef0441 0x08dbff0023eef044 0xfffff3073fff1fff 0xefffff3073fff1ff

def z1108 : W := mkw 0x9dbff00a3eef24c3 0x09dbff00a3eef24c 0xaffff0003fff00cb 0xeaffff0003fff00c

def z1109 : W := mkw 0x4fed6fb580324220 0x84fed6fb58032422 0xdfffffffc0ff03ff 0xfdfffffffc0ff03f

def z1110 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xafce000027f00009 0x6afce000027f0000

def z1111 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xeffff007ffff000b 0xeeffff007ffff000

def z1112 : W := mkw 0x9daf602c266a2082 0x09daf602c266a208 0xafce003827700000 0x4afce00382770000

def z1113 : W := mkw 0x2b701fc055d1db1c 0x42b701fc055d1db1 0xfff07fc1ffffffff 0xffff07fc1fffffff

def z1114 : W := mkw 0x093090001cc50000 0x0093090001cc5000 0xaff000003fff0009 0xeaff000003fff000

def z1115 : W := mkw 0x00d4d55358850d59 0x400d4d55358850d5 0xd1ce4d39188f1fff 0x7d1ce4d39188f1ff

def z1116 : W := mkw 0x8dbff0083eef2082 0x08dbff0083eef208 0xeffff0383fff00cb 0xeeffff0383fff00c

def z1117 : W := mkw 0x160b9a2e6b0db4d3 0x4160b9a2e6b0db4d 0x7e3fffffff0ffcff 0xf7e3fffffff0ffcf

def z1118 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x6e0f8e3e3f0cfcc2 0xd6e0f8e3e3f0cfcc

def z1119 : W := mkw 0x06090a2401009000 0x006090a240100900 0x3e0e0e383f00fc0c 0xf3e0e0e383f00fc0

def z1120 : W := mkw 0xcdbff03dbeef20a2 0x8cdbff03dbeef20a 0xeffff03fffff00fb 0xeeffff03fffff00f

def z1121 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xfffff3c7ffff03ff 0xefffff3c7ffff03f

def z1122 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xafce0000277c000a 0x6afce0000277c000

def z1123 : W := mkw 0x8dbf700036eb0000 0x08dbf700036eb000 0xaffe300027700000 0x4affe30002770000

def z1124 : W := mkw 0xa9f475d114f34b2c 0x8a9f475d114f34b2 0x81f071c100f30331 0x081f071c100f3033

def z1125 : W := mkw 0x960bba2e2b0db4c3 0x0960bba2e2b0db4c 0x7e0fbe3e3f0cfcce 0xf7e0fbe3e3f0cfcc

def z1126 : W := mkw 0x0d39000014c00000 0x00d39000014c0000 0xafff80003ff0000b 0xeafff80003ff0000

def z1127 : W := mkw 0x297005c015d0db0c 0x0297005c015d0db0 0xbff001c03ff0ff09 0xebff001c03ff0ff0

def z1128 : W := mkw 0x093090425cc50d59 0x4093090425cc50d5 0xaff1b2c6fff01c09 0xeaff1b2c6fff01c0

def z1129 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x00000dc00000e300 0x100000dc00000e30

def z1130 : W := mkw 0x0fad6a2400000000 0x00fad6a240000000 0xcfffffffc0000007 0xfcfffffffc000000

def z1131 : W := mkw 0x8dbff0083eef20a2 0x88dbff0083eef20a 0xaffff0003fff00fb 0xeaffff0003fff00f

def z1132 : W := mkw 0x1d3b802e3ecc24c3 0x01d3b802e3ecc24c 0xefff803e3ffc00cb 0xeefff803e3ffc00c

def z1133 : W := mkw 0x8daf6019266a20a2 0x88daf6019266a20a 0xafce003827700000 0x4afce00382770000

def z1134 : W := mkw 0x09b4600014c00000 0x009b4600014c0000 0xaff070003ff00009 0xeaff070003ff0000

def z1135 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xafffb00027700000 0xcafffb0002770000

def z1136 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xafce00003f700008 0xeafce00003f70000

def z1137 : W := mkw 0x0409002400000000 0x0040900240000000 0x403ff3ffc0000007 0xa403ff3ffc000000

def z1138 : W := mkw 0x6fed6fb585409004 0x06fed6fb58540900 0xcfffffffc7000007 0xfcfffffffc700000

def z1139 : W := mkw 0xadbff0c03eef090c 0x0adbff0c03eef090 0xaffff0c03fff000b 0xeaffff0c03fff000

def z1140 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xaffe700027700001 0x4affe70002770000

def z1141 : W := mkw 0x8dbff0083eef2082 0x08dbff0083eef208 0xbffff0003fffe0cb 0xebffff0003fffe0c

def z1142 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbff1bfc6fff0ff0d 0xfbff1bfc6fff0ff0

def z1143 : W := mkw 0x8dbff0027eef0451 0x48dbff0027eef045 0xfffff207ffff1cff 0xefffff207ffff1cf

def z1144 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbff00fc03f70ff04 0xdbff00fc03f70ff0

def z1145 : W := mkw 0x0dbd600014c00000 0x00dbd600014c0000 0xaffe00003ff00009 0xeaffe00003ff0000

def z1146 : W := mkw 0x4ded65b580000000 0x04ded65b58000000 0xc1fffdffc0000007 0x7c1fffdffc000000

def z1147 : W := mkw 0x89b6f0003eef0000 0x089b6f0003eef000 0xaff070003fff0009 0xeaff070003fff000

def z1148 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xaff00fc03ff0ff01 0xdaff00fc03ff0ff0

def z1149 : W := mkw 0x893090001ec50000 0x0893090001ec5000 0xaff000003ff00009 0xeaff000003ff0000

def z1150 : W := mkw 0x22400fc24110df5d 0x422400fc24110df5 0x10000fc00000fff4 0x110000fc00000fff

def z1151 : W := mkw 0x160b9a2e6b0db4d3 0x4160b9a2e6b0db4d 0x7e0fff3fff8fffff 0xf7e0fff3fff8ffff

def z1152 : W := mkw 0x0dad600004400000 0x00dad60000440000 0xaffff00027700003 0xeaffff0002770000

def z1153 : W := mkw 0x8dbff0193eef20a2 0x88dbff0193eef20a 0xfffff1393fff03ff 0xefffff1393fff03f

def z1154 : W := mkw 0x960b9a2e2b2fb4c3 0x0960b9a2e2b2fb4c 0x7e0f8e3e3f0ffcce 0xf7e0f8e3e3f0ffcc

def z1155 : W := mkw 0x0010904258850d59 0x40010904258850d5 0x1031f3c7d88f1ff9 0x81031f3c7d88f1ff

def z1156 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbff00c003ff0ff09 0xfbff00c003ff0ff0

def z1157 : W := mkw 0x2b700fe415d0db0c 0x02b700fe415d0db0 0xfff00ffe3ff0ff0d 0xffff00ffe3ff0ff0

def z1158 : W := mkw 0x148fd03f6a2f24f3 0xc148fd03f6a2f24f 0x400ff03fc00f00f2 0x0400ff03fc00f00f

def z1159 : W := mkw 0x9dbff02e7eef24d3 0x49dbff02e7eef24d 0xeffff03fffff00fb 0xeeffff03fffff00f

def z1160 : W := mkw 0x0932000034ea0000 0x00932000034ea000 0xaff000003fff0009 0xeaff000003fff000

def z1161 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xfff00fc03ffcffcf 0xffff00fc03ffcffc

def z1162 : W := mkw 0x160b0a2e2308b4c3 0x0160b0a2e2308b4c 0x7e0e0e3e3f00fccc 0xf7e0e0e3e3f00fcc

def z1163 : W := mkw 0x8932000036ea0000 0x08932000036ea000 0xaff000003ff00009 0xeaff000003ff0000

def z1164 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xafffb0003fff0008 0xcafffb0003fff000

def z1165 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1fffd3920ffe3ff 0xff1fffd3920ffe3f

def z1166 : W := mkw 0x69f475d1d4d14b1c 0x469f475d1d4d14b1 0x81f071c1c0f30331 0x081f071c1c0f3033

def z1167 : W := mkw 0x093090025cc50451 0x4093090025cc5045 0xeff1f007ffff00fb 0xeeff1f007ffff00f

def z1168 : W := mkw 0x8daf7000266b0000 0x08daf7000266b000 0xafce700027730000 0x4afce70002773000

def z1169 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xdfffffffc00003f7 0xfdfffffffc00003f

def z1170 : W := mkw 0x29f445d114f24b2c 0x829f445d114f24b2 0x81f001c000f00301 0x081f001c000f0030

def z1171 : W := mkw 0x8d39200016c00000 0x08d39200016c0000 0xaff000003ff00009 0xeaff000003ff0000

def z1172 : W := mkw 0x12020a2e2108b4c3 0x012020a2e2108b4c 0x7e0e0e3e3f0cfcce 0xf7e0e0e3e3f0cfcc

def z1173 : W := mkw 0x09b6400034ea0000 0x009b6400034ea000 0xaffe00003ff00009 0xeaffe00003ff0000

def z1174 : W := mkw 0x8dbff0113eef0000 0x08dbff0113eef000 0xeffff0393fff000b 0xeeffff0393fff000

def z1175 : W := mkw 0x4fad6ab580000000 0x04fad6ab58000000 0x4e3ff3ffc0000007 0xa4e3ff3ffc000000

def z1176 : W := mkw 0x560b8aaeab0cb4c3 0x0560b8aaeab0cb4c 0x7e0f8efeff0cfcce 0xf7e0f8efeff0cfcc

def z1177 : W := mkw 0x6fed6fb58550d204 0x06fed6fb58550d20 0xffffffffe7f0e30f 0xfffffffffe7f0e30

def z1178 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xaff00fc03f70fc05 0xfaff00fc03f70fc0

def z1179 : W := mkw 0x0930004014c00908 0x00930004014c0090 0xbff000003ff01f09 0xebff000003ff01f0

def z1180 : W := mkw 0xddbff03fbeef24c3 0x0ddbff03fbeef24c 0xeffff03fffff00cb 0xeeffff03fffff00c

def z1181 : W := mkw 0x22408fc20914df4d 0x022408fc20914df4 0x50018fc6180cffce 0xb50018fc6180cffc

def z1182 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xafcff0003fff000a 0x4afcff0003fff000

def z1183 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0x10300fc00000ff04 0x110300fc00000ff0

def z1184 : W := mkw 0x8dbff01b7eef24f3 0xc8dbff01b7eef24f 0xeffff03fffff00fb 0xeeffff03fffff00f

def z1185 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xfff1ffc7ffffffff 0xffff1ffc7fffffff

def z1186 : W := mkw 0x32400fec0110fb8e 0x032400fec0110fb8 0x10000ff80000ff04 0x110000ff80000ff0

def z1187 : W := mkw 0x0dbd604014c00908 0x00dbd604014c0090 0xfffff3c7fff01f0f 0xefffff3c7fff01f0

def z1188 : W := mkw 0x8dbff0023eef0441 0x08dbff0023eef044 0xeffff0063fff00cb 0xeeffff0063fff00c

def z1189 : W := mkw 0x9dbff02e3eef24c3 0x09dbff02e3eef24c 0xfffff23e3fff1ccf 0xefffff23e3fff1cc

def z1190 : W := mkw 0x52400fbf8110f6e3 0x852400fbf8110f6e 0x50000fffc000fff4 0x150000fffc000fff

def z1191 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0fce3f3f0ffcfe 0xf7e0fce3f3f0ffcf

def z1192 : W := mkw 0x8dbff04a7eef2ddb 0x48dbff04a7eef2dd 0xffffffffffffffff 0xffffffffffffffff

def z1193 : W := mkw 0x2b600f800550d204 0x02b600f800550d20 0xbff00fc03f70fc0d 0xfbff00fc03f70fc0

def z1194 : W := mkw 0x12400f3d0110f2a2 0x812400f3d0110f2a 0x00000c380000e000 0x100000c380000e00

def z1195 : W := mkw 0x2b700fd115d0db0c 0x02b700fd115d0db0 0xfff00ff93ff0ff0d 0xffff00ff93ff0ff0

def z1196 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xafffb0003ff00009 0xeafffb0003ff0000

def z1197 : W := mkw 0x09a64000246a0000 0x009a64000246a000 0xafce400027ff000b 0x6afce400027ff000

def z1198 : W := mkw 0x9dafe02e2e6e24c3 0x09dafe02e2e6e24c 0xefcf803e277c00c2 0x4efcf803e277c00c

def z1199 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xeffff0013fff00fb 0xeeffff0013fff00f

def z1200 : W := mkw 0x2b700fd115d0db2c 0x82b700fd115d0db2 0xbff00fc13ff0ff3d 0xfbff00fc13ff0ff3

def z1201 : W := mkw 0x02000a0001009000 0x002000a000100900 0x7e0e0e383f00fc0e 0xf7e0e0e383f00fc0

def z1202 : W := mkw 0x4dbd603594c00000 0x04dbd603594c0000 0xeffff03ffff0000b 0xeeffff03ffff0000

def z1203 : W := mkw 0x8dbf604036ea0908 0x08dbf604036ea090 0xbffe03c03ff01f0d 0xebffe03c03ff01f0

def z1204 : W := mkw 0x8dafe0002e6e0000 0x08dafe0002e6e000 0xafce00003f7c0008 0x4afce00003f7c000

def z1205 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xcfffffffc00f00f7 0xfcfffffffc00f00f

def z1206 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xafffb0003f7c000a 0xeafffb0003f7c000

def z1207 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0ffe3fff0cfcce 0xf7e0ffe3fff0cfcc

def z1208 : W := mkw 0x0932000034c80000 0x00932000034c8000 0xaffe00003ffc000b 0xeaffe00003ffc000

def z1209 : W := mkw 0x8dbff0003eef0000 0x08dbff0003eef000 0xbffff0003fff03fb 0xebffff0003fff03f

def z1210 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1ce4f3938ffffff 0xff1ce4f3938fffff

def z1211 : W := mkw 0x8dafe0022e6e0441 0x08dafe0022e6e044 0xffcf82063f7c1cce 0xeffcf82063f7c1cc

def z1212 : W := mkw 0x8dbf704076eb0918 0x48dbf704076eb091 0xaffe71c1e7f30331 0x4affe71c1e7f3033

def z1213 : W := mkw 0x22400fd90110fbae 0x822400fd90110fba 0x10000ff80000ff04 0x110000ff80000ff0

def z1214 : W := mkw 0x62400fe48110db0c 0x062400fe48110db0 0x10000fc6c000ff04 0x110000fc6c000ff0

def z1215 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xcffff3ffc0000003 0x8cffff3ffc000000

def z1216 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x3e0f8e3e3f0cfcc8 0xd3e0f8e3e3f0cfcc

def z1217 : W := mkw 0x048f4000222a0000 0x0048f4000222a000 0xafce400027ff000b 0x6afce400027ff000

def z1218 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xfff04fc13ff0ff0f 0xffff04fc13ff0ff0

def z1219 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0xbfc00fc03ff0ff0d 0xfbfc00fc03ff0ff0

def z1220 : W := mkw 0x8dafe0002e6e0000 0x08dafe0002e6e000 0xaffff0003f7c000b 0xeaffff0003f7c000

def z1221 : W := mkw 0x22509fdb5995ffff 0xc22509fdb5995fff 0x5031ffffd88fffff 0xb5031ffffd88ffff

def z1222 : W := mkw 0x0dad600004400000 0x00dad60000440000 0xafce000027700000 0x4afce00002770000

def z1223 : W := mkw 0xcdaf6035a66a0000 0x0cdaf6035a66a000 0xefcff03fe7700002 0x4efcff03fe770000

def z1224 : W := mkw 0x0932000834c82082 0x00932000834c8208 0xfffe0c383ffce0cf 0xffffe0c383ffce0c

def z1225 : W := mkw 0x364b8fee2b1cffcf 0x0364b8fee2b1cffc 0x500f8ffe000cffc6 0x1500f8ffe000cffc

def z1226 : W := mkw 0x8dbdf0425ee70d59 0x48dbdf0425ee70d5 0xdff1f3c7dfff1fff 0xadff1f3c7dfff1ff

def z1227 : W := mkw 0x0dbdf0001cc50000 0x00dbdf0001cc5000 0xaffff0003fff000b 0xeaffff0003fff000

def z1228 : W := mkw 0x0084401100000000 0x0008440110000000 0x403ff3ffc0000007 0xa403ff3ffc000000

def z1229 : W := mkw 0x0012904a788d2ddb 0x40012904a788d2dd 0x30000000388ffff8 0x030000000388ffff

def z1230 : W := mkw 0x09b4400014e20000 0x009b4400014e2000 0xaff040003ff30009 0xeaff040003ff3000

def z1231 : W := mkw 0x8daf6000266a0000 0x08daf6000266a000 0xafcff00027700002 0x4afcff0002770000

def z1232 : W := mkw 0x32508fee1994ffcf 0x032508fee1994ffc 0x50318ffe188cffcf 0xb50318ffe188cffc

def z1233 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x5031ffc7c000ff07 0xb5031ffc7c000ff0

def z1234 : W := mkw 0x2012904a7dffffff 0xc2012904a7dfffff 0x300000003ffffff8 0x0300000003ffffff

def z1235 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbfc00e003ff0ff0c 0xfbfc00e003ff0ff0

def z1236 : W := mkw 0x8d29200006400000 0x08d2920000640000 0xafc0000027700000 0x4afc000002770000

def z1237 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xbff00c003ff0e00d 0xfbff00c003ff0e00

def z1238 : W := mkw 0x4fed6fb580104200 0x04fed6fb58010420 0xffffffffe0ffe3ff 0xfffffffffe0ffe3f

def z1239 : W := mkw 0x160b9a2e2b0db4c3 0x0160b9a2e2b0db4c 0x7e0ffe3e3f0ffcce 0xf7e0ffe3e3f0ffcc

def z1240 : W := mkw 0x44cd653580000000 0x044cd65358000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z1241 : W := mkw 0x048fc0002a2e0000 0x0048fc0002a2e000 0xafcf80003f7c000a 0xeafcf80003f7c000

def z1242 : W := mkw 0x09b6404034ea0908 0x009b6404034ea090 0xfffe43c13fff1fff 0xefffe43c13fff1ff

def z1243 : W := mkw 0x0f690fa400000000 0x00f690fa40000000 0xcfffffffc0000007 0xfcfffffffc000000

def z1244 : W := mkw 0x0d2b80002e4c0000 0x00d2b80002e4c000 0xafcf80003f7c000a 0xeafcf80003f7c000

def z1245 : W := mkw 0x293000c014c0090c 0x0293000c014c0090 0xaff000c03ff00009 0xeaff000c03ff0000

def z1246 : W := mkw 0x8daff0002e6f0000 0x08daff0002e6f000 0xafcff0003f7f000a 0xeafcff0003f7f000

def z1247 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xdfffffffc00c00cf 0xfdfffffffc00c00c

def z1248 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x000003c000001f00 0x0000003c000001f0

def z1249 : W := mkw 0x46490fb580000000 0x046490fb58000000 0x4e3fffffc0000007 0xf4e3fffffc000000

def z1250 : W := mkw 0x4f692fb580000000 0x04f692fb58000000 0x4e3fbfffc0000006 0xf4e3fbfffc000000

def z1251 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x10000fc00080ff0d 0x310000fc00080ff0

def z1252 : W := mkw 0x12028a0a2b0cb4c3 0x012028a0a2b0cb4c 0x7e0e0e383f0cfcce 0xf7e0e0e383f0cfcc

def z1253 : W := mkw 0x16098a2e0b04b4c3 0x016098a2e0b04b4c 0x5e0f8e3e1f00fcc6 0xf5e0f8e3e1f00fcc

def z1254 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xeffff3c7ffff1c0f 0xeeffff3c7ffff1c0

def z1255 : W := mkw 0x4fed6fb580220000 0x04fed6fb58022000 0xcfffffffc0f30007 0xfcfffffffc0f3000

def z1256 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xbffff3c6ffff1f0f 0xebffff3c6ffff1f0

def z1257 : W := mkw 0x89b4f0425ce70d59 0x489b4f0425ce70d5 0xfff1f3c7ffff1fff 0xefff1f3c7ffff1ff

def z1258 : W := mkw 0x0000000000000000 0x0000000000000000 0x403fffffc0000007 0xf403fffffc000000

def z1259 : W := mkw 0x0d3b000036c80000 0x00d3b000036c8000 0xaffe00003ff00009 0xeaffe00003ff0000

def z1260 : W := mkw 0x62400ff58110db0c 0x062400ff58110db0 0x10000ff80000ff04 0x110000ff80000ff0

def z1261 : W := mkw 0x0dbf600034ea0000 0x00dbf600034ea000 0xaffff0003fff000b 0xeaffff0003fff000

def z1262 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xbffff3c03fff1fff 0xebffff3c03fff1ff

def z1263 : W := mkw 0x0000004240000d59 0x40000004240000d5 0x5031f3c7c08f1fff 0xa5031f3c7c08f1ff

def z1264 : W := mkw 0x8dbff0407eef0918 0x48dbff0407eef091 0xbffff3c1ffff1f3f 0xebffff3c1ffff1f3

def z1265 : W := mkw 0x2b700fc015d0db0c 0x02b700fc015d0db0 0xbff07fc1fff0ff0d 0xfbff07fc1fff0ff0

def z1266 : W := mkw 0x12400f3d0110f2a2 0x812400f3d0110f2a 0x50000d390000e3f4 0x150000d390000e3f

def z1267 : W := mkw 0x8d39b0001ec50000 0x08d39b0001ec5000 0xaff1f0003fff000b 0xeaff1f0003fff000

def z1268 : W := mkw 0x0b200a0005409000 0x00b200a000540900 0xbfc00e003f70fc0c 0xfbfc00e003f70fc0

def z1269 : W := mkw 0x16098a260b049441 0x016098a260b04944 0x7e0f8e3e3f00fc0e 0xf7e0f8e3e3f00fc0

def z1270 : W := mkw 0x32400fff0110ffef 0x832400fff0110ffe 0x50000fff0000fff4 0x150000fff0000fff

def z1271 : W := mkw 0x4fed6fb580324220 0x84fed6fb58032422 0xcfffffffc0700007 0xfcfffffffc070000

def z1272 : W := mkw 0x00020008203a62a2 0x800020008203a62a 0x7031f3c7e0ffe3ff 0xa7031f3c7e0ffe3f

def z1273 : W := mkw 0x22509fc01995db0c 0x022509fc01995db0 0x1031ffc0188fff0f 0xb1031ffc0188fff0

def z1274 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xbff001003ff0030d 0xebff001003ff0030

def z1275 : W := mkw 0x4f292aa480000000 0x04f292aa48000000 0x0e3fbefec0000000 0xd0e3fbefec000000

def z1276 : W := mkw 0x8daff0026e6f0451 0x48daff0026e6f045 0xefcff007e77f00f2 0x4efcff007e77f00f

def z1277 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xbff002003ff01c0d 0xebff002003ff01c0

def z1278 : W := mkw 0x160b0a2c2308b082 0x0160b0a2c2308b08 0x7e0f8e3e3f00fc0e 0xf7e0f8e3e3f00fc0

def z1279 : W := mkw 0x22400fc00110db0c 0x022400fc00110db0 0x50004fc1008fffff 0x350004fc1008ffff

def z1280 : W := mkw 0x29f455d154f34b3c 0xc29f455d154f34b3 0x81f071c1c0f30331 0x081f071c1c0f3033

def z1281 : W := mkw 0x8daff0002e6f0000 0x08daff0002e6f000 0xafcff00027ff000b 0x6afcff00027ff000

def z1282 : W := mkw 0x62400fd18110db0c 0x062400fd18110db0 0x10000fc1c000ff04 0x110000fc1c000ff0

def z1283 : W := mkw 0x02028a0a290cb4c3 0x002028a0a290cb4c 0x7e0f8e3e3f0cfcce 0xf7e0f8e3e3f0cfcc

def z1284 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xcfffffffc0830337 0xfcfffffffc083033

def z1285 : W := mkw 0x2b600fc00550db0c 0x02b600fc00550db0 0xbfc00fc03f70ff0c 0xfbfc00fc03f70ff0

def z1286 : W := mkw 0x89220000266a0000 0x089220000266a000 0xafc0000027700000 0x4afc000002770000

def z1287 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0e0c383f0cfcce 0x77e0e0c383f0cfcc

def z1288 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xcfffffffc08f000f 0xfcfffffffc08f000

def z1289 : W := mkw 0x22500fc01190db0c 0x022500fc01190db0 0x10300fc01800ff04 0x910300fc01800ff0

def z1290 : W := mkw 0x1012904a7a8d2ddb 0x41012904a7a8d2dd 0x10000000188f1ff8 0x010000000188f1ff

def z1291 : W := mkw 0x160b8a2c2b0cb082 0x0160b8a2c2b0cb08 0x3e0f8e383f0cfc0e 0xf3e0f8e383f0cfc0

def z1292 : W := mkw 0x8d39b0001ec50000 0x08d39b0001ec5000 0xaff1b0003f700000 0xcaff1b0003f70000

def z1293 : W := mkw 0x2970054015d0db0c 0x02970054015d0db0 0xbff00d003ff0ff0d 0xfbff00d003ff0ff0

def z1294 : W := mkw 0x32400fe60110df4d 0x032400fe60110df4 0x10000fc60000ff04 0x110000fc60000ff0

def z1295 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e3ffe3e3f0cfccf 0xf7e3ffe3e3f0cfcc

def z1296 : W := mkw 0x4f692fa480000000 0x04f692fa48000000 0xcfffbffec0000007 0xfcfffbffec000000

def z1297 : W := mkw 0x62509ff7d995df5d 0x462509ff7d995df5 0x5031ffffd88fffff 0xb5031ffffd88ffff

def z1298 : W := mkw 0x8dbff0403eef0908 0x08dbff0403eef090 0xaffff1c03fff030b 0xeaffff1c03fff030

def z1299 : W := mkw 0x8dbff0407eef0918 0x48dbff0407eef091 0xfffff1c1ffff03ff 0xefffff1c1ffff03f

def z1300 : W := mkw 0x2b701fc055d1db1c 0x42b701fc055d1db1 0xbff00fc03ff3ff3d 0xfbff00fc03ff3ff3

def z1301 : W := mkw 0x09a64000246a0000 0x009a64000246a000 0xafce000027700000 0x4afce00002770000

def z1302 : W := mkw 0x0be44f9100000000 0x00be44f910000000 0xcfffffffc0000007 0xfcfffffffc000000

def z1303 : W := mkw 0x89b6d0003eef0000 0x089b6d0003eef000 0xaffe40003fff000b 0xeaffe40003fff000

def z1304 : W := mkw 0x22400fdb4110ffff 0xc22400fdb4110fff 0x50000fffc000fff4 0x150000fffc000fff

def z1305 : W := mkw 0x09b6d0003cef0000 0x009b6d0003cef000 0xaffff0003fff000b 0xeaffff0003fff000

def z1306 : W := mkw 0x00c64519203a62a2 0x800c64519203a62a 0xf1cffd3fe0ffe3ff 0x7f1cffd3fe0ffe3f

def z1307 : W := mkw 0x4fed6fb580104220 0x84fed6fb58010422 0xcfffffffc0000337 0xfcfffffffc000033

def z1308 : W := mkw 0x8daff0002e6f0000 0x08daff0002e6f000 0xafcfb00027700000 0x4afcfb0002770000

def z1309 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0fce3e3f8ffccf 0xf7e0fce3e3f8ffcc

def z1310 : W := mkw 0x8dbd700016e30000 0x08dbd700016e3000 0x8ff0700007f30001 0x08ff0700007f3000

def z1311 : W := mkw 0x160b0a2c2308b082 0x0160b0a2c2308b08 0x7e0e0e383f0cfcce 0xf7e0e0e383f0cfcc

def z1312 : W := mkw 0x160b8a2e2b0cb4c3 0x0160b8a2e2b0cb4c 0x7e0f8c3e3f0cfcca 0x57e0f8c3e3f0cfcc

def z1313 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xaffff0003fff1c0b 0xeaffff0003fff1c0

def z1314 : W := mkw 0x09b4400014c00000 0x009b4400014c0000 0xaffe40003ff0000b 0xeaffe40003ff0000

def z1315 : W := mkw 0x2b600f800550d204 0x02b600f800550d20 0xbfc00f003ff0ff0d 0xfbfc00f003ff0ff0

def z1316 : W := mkw 0x4fed6fb580104200 0x04fed6fb58010420 0xefffffffe070e007 0xfefffffffe070e00

def z1317 : W := mkw 0xcdbff077feef0d59 0x4cdbff077feef0d5 0xfffff3ffffff1fff 0xefffff3ffffff1ff

def z1318 : W := mkw 0x06090a2400000000 0x006090a240000000 0x4e3fbefec0000006 0xf4e3fbefec000000

def z1319 : W := mkw 0x0dafe0002a2e0000 0x00dafe0002a2e000 0xaffff0003fff000b 0xeaffff0003fff000

def z1320 : W := mkw 0x0d3980001ec40000 0x00d3980001ec4000 0xaff180003ff00009 0xeaff180003ff0000

def z1321 : W := mkw 0x89b4600014e20000 0x089b4600014e2000 0xaff000003ff00009 0xeaff000003ff0000

def z1322 : W := mkw 0x048f4000222a0000 0x0048f4000222a000 0xafce000027700000 0x4afce00002770000

def z1323 : W := mkw 0x0d2b000026480000 0x00d2b00002648000 0xafce000027700000 0x4afce00002770000

def z1324 : W := mkw 0x62400ff7c110df5d 0x462400ff7c110df5 0x50000fffc000fff4 0x150000fffc000fff

def z1325 : W := mkw 0x049fd0003aaf0000 0x0049fd0003aaf000 0xaffff0003fff000b 0xeaffff0003fff000

def z1326 : W := mkw 0x3f399ae65fc59d5d 0x43f399ae65fc59d5 0x0e31b2c6df001c00 0x80e31b2c6df001c0

def z1327 : W := mkw 0x8dbf600036ea0000 0x08dbf600036ea000 0xaffe40003fff000b 0xeaffe40003fff000

def z1328 : W := mkw 0x0d3b90003ecd0000 0x00d3b90003ecd000 0xaffff0003fff000b 0xeaffff0003fff000

def z1329 : W := mkw 0x4fed6fb580000000 0x04fed6fb58000000 0xdfffffffc080030f 0xfdfffffffc080030

def z1330 : W := mkw 0x893290003eef0000 0x0893290003eef000 0xaff1f0003fff000b 0xeaff1f0003fff000

def z1331 : W := mkw 0x8dbff0407eef0918 0x48dbff0407eef091 0xaffff0c0ffff000b 0xeaffff0c0ffff000

def z1332 : W := mkw 0x093080001cc40000 0x0093080001cc4000 0xaff180003ffc000b 0xeaff180003ffc000

def z1333 : W := mkw 0x8dbff0427eef0d59 0x48dbff0427eef0d5 0xaffff3c7ffff1f3b 0xeaffff3c7ffff1f3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z9,z5,z6])],[(0,[z1,z2,z3,z4,z5,z10,z6]),(0,[z1,z2,z3,z11,z4,z5,z6]),(0,[z1,z2,z12,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z14,z5,z6]),(0,[z1,z15,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z16,z17]),(0,[z18,z1,z2,z19,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z20,z6]),(0,[z1,z2,z21,z3,z4,z22,z5])],[(0,[z1,z1,z2,z3,z4,z5,z16])],[(0,[z1,z2,z3,z4,z5,z23,z6]),(0,[z24,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z25,z6]),(0,[z26,z1,z2,z3,z4,z27,z6]),(0,[z28,z2,z3,z4,z5,z6,z29]),(0,[z1,z2,z30,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z16,z31]),(0,[z32,z1,z2,z21,z3,z4,z5]),(0,[z1,z33,z3,z4,z5,z34,z6]),(0,[z1,z2,z35,z3,z36,z4,z5]),(0,[z1,z2,z37,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z38,z6])],[(1,[z1,z2,z3,z39,z5,z6]),(0,[z1,z2,z40,z3,z4,z5,z6]),(0,[z18,z1,z2,z41,z4,z5,z6]),(1,[z1,z2,z3,z4,z42,z6]),(0,[z1,z2,z35,z3,z4,z43,z6]),(0,[z1,z2,z3,z44,z4,z5,z6])],[(0,[z45,z1,z2,z3,z4,z5,z23]),(0,[z1,z2,z41,z3,z4,z5,z29]),(0,[z1,z2,z46,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z47]),(0,[z1,z2,z3,z4,z48,z5,z6]),(0,[z1,z2,z3,z36,z4,z49,z5])],[(0,[z1,z2,z3,z50,z5,z43,z6]),(0,[z1,z2,z21,z3,z4,z51,z5]),(0,[z1,z2,z3,z4,z52,z5,z29]),(0,[z1,z2,z3,z4,z5,z6,z53]),(1,[z1,z2,z3,z54,z4,z5])]],
   [[(0,[z55,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z56,z6]),(0,[z1,z2,z3,z57,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z58,z6]),(0,[z1,z2,z3,z36,z5,z59,z6])],[(0,[z45,z1,z40,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z60,z6]),(0,[z1,z61,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z62,z4,z5,z6]),(0,[z1,z2,z63,z3,z4,z5,z6]),(1,[z1,z2,z64,z4,z65,z6]),(0,[z1,z2,z21,z21,z3,z4,z5]),(0,[z1,z2,z3,z4,z66,z5,z67])],[(0,[z68,z1,z2,z3,z4,z69,z6]),(1,[z1,z2,z3,z4,z5,z70]),(0,[z1,z2,z3,z19,z4,z5,z6]),(0,[z1,z2,z71,z3,z4,z5,z6]),(0,[z1,z2,z3,z72,z4,z5,z6]),(0,[z1,z2,z3,z73,z4,z5,z6]),(1,[z1,z2,z4,z5,z74,z6])],[(1,[z1,z2,z3,z4,z5,z75]),(0,[z1,z2,z76,z4,z5,z65,z6]),(0,[z1,z2,z3,z36,z4,z5,z38])],[(0,[z1,z2,z3,z4,z5,z43,z29]),(0,[z1,z2,z21,z3,z4,z5,z38])],[(0,[z1,z77,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z29]),(0,[z1,z78,z2,z3,z4,z5,z6]),(0,[z1,z2,z79,z3,z4,z5,z6])],[(0,[z1,z80,z2,z3,z4,z5,z6]),(0,[z1,z81,z2,z3,z4,z5,z6]),(0,[z82,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z83,z11,z5,z6]),(0,[z1,z2,z3,z84,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z86]),(0,[z1,z2,z3,z87,z4,z5,z6]),(0,[z1,z88,z2,z3,z4,z5,z29]),(0,[z1,z2,z41,z3,z36,z4,z5]),(0,[z1,z89,z2,z83,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z90,z6]),(0,[z1,z2,z91,z3,z4,z5,z6]),(0,[z1,z2,z91,z21,z3,z4,z5]),(0,[z1,z2,z21,z92,z3,z4,z5])]],
   [[(0,[z93,z1,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z94,z4,z5,z29]),(0,[z1,z95,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z11,z4,z5]),(0,[z1,z2,z3,z96,z4,z5,z6])],[(0,[z1,z40,z3,z4,z5,z97,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z2,z3,z98,z4,z50,z5,z6]),(0,[z1,z2,z99,z3,z50,z5,z6]),(0,[z100,z1,z2,z3,z4,z5,z6])],[(0,[z101,z1,z2,z3,z4,z5,z6]),(0,[z102,z1,z2,z103,z3,z4,z6]),(0,[z1,z2,z104,z3,z4,z5,z16]),(0,[z1,z2,z64,z21,z3,z4,z5])],[(0,[z1,z2,z3,z4,z105,z5,z6]),(1,[z1,z2,z3,z4,z106,z6]),(0,[z1,z2,z3,z4,z5,z107,z6])],[(0,[z108,z1,z2,z3,z4,z5,z6]),(0,[z109,z1,z2,z3,z4,z5,z110]),(0,[z111,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z112,z3,z4,z5,z6]),(0,[z2,z3,z4,z51,z5,z113,z6]),(0,[z1,z2,z3,z4,z5,z6,z114])],[(0,[z1,z2,z115,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z116,z6])],[(1,[z1,z2,z3,z117,z5,z6]),(0,[z1,z2,z3,z4,z5,z118,z6]),(0,[z1,z2,z3,z4,z119,z5,z6]),(0,[z102,z1,z2,z120,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z34,z16]),(0,[z1,z2,z3,z4,z5,z6,z121]),(0,[z122,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z123]),(0,[z1,z124,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z66,z38,z6])],[(0,[z1,z2,z125,z3,z4,z5,z6]),(0,[z1,z2,z3,z126,z4,z5,z6]),(0,[z1,z127,z2,z3,z4,z5,z6]),(1,[z1,z2,z35,z3,z43,z6]),(1,[z1,z2,z3,z36,z5,z59]),(0,[z1,z2,z3,z4,z5,z6,z67])]],
   [[(1,[z1,z2,z128,z4,z5,z6])],[(0,[z1,z2,z3,z128,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z129,z6]),(0,[z32,z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z130,z5,z6])],[(0,[z1,z2,z40,z3,z4,z5,z29]),(0,[z1,z2,z3,z11,z4,z5,z16]),(1,[z1,z2,z71,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z131,z6]),(0,[z1,z2,z3,z132,z4,z5,z6])],[(0,[z133,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z134,z6]),(0,[z1,z2,z3,z4,z135,z5,z6]),(0,[z1,z136,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z137,z6])],[(0,[z1,z2,z3,z4,z138,z5,z6]),(0,[z93,z2,z3,z98,z4,z5,z6]),(0,[z1,z2,z83,z3,z11,z5,z6])],[(0,[z32,z1,z139,z3,z4,z5,z6]),(0,[z55,z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z58,z29]),(0,[z1,z2,z3,z4,z5,z38,z16]),(0,[z1,z89,z2,z3,z140,z5,z6]),(0,[z1,z2,z3,z4,z141,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z142])],[(0,[z1,z2,z40,z3,z4,z5,z16]),(1,[z1,z2,z143,z3,z4,z6]),(0,[z1,z2,z144,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z145,z5,z6]),(0,[z1,z2,z3,z4,z146,z5,z6]),(0,[z1,z147,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z58,z34])],[(0,[z1,z2,z148,z3,z4,z5,z6]),(0,[z1,z2,z3,z36,z4,z66,z5])]],
   [[(0,[z68,z1,z40,z3,z4,z5,z6]),(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z102,z1,z2,z3,z4,z5,z150]),(0,[z1,z2,z3,z4,z140,z5,z16]),(0,[z1,z2,z3,z4,z5,z6,z151]),(0,[z1,z2,z21,z3,z4,z66,z5])],[(0,[z1,z2,z3,z4,z5,z6,z152]),(0,[z32,z1,z2,z3,z4,z52,z6]),(0,[z1,z2,z153,z3,z4,z5,z6]),(0,[z1,z2,z154,z3,z4,z5,z6]),(0,[z155,z1,z2,z21,z3,z4,z5]),(0,[z1,z2,z156,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z75]),(0,[z1,z2,z3,z4,z157,z5,z6]),(1,[z158,z2,z3,z50,z5,z6]),(0,[z1,z2,z159,z3,z4,z5,z6]),(0,[z26,z1,z61,z2,z3,z4,z6]),(0,[z1,z61,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z60,z16]),(0,[z1,z88,z2,z19,z4,z5,z6]),(0,[z1,z2,z83,z3,z4,z5,z6]),(0,[z160,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z40,z3,z36,z4,z5]),(0,[z161,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z4,z5,z16]),(0,[z1,z147,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z4,z162,z5,z6])],[(0,[z1,z163,z2,z40,z3,z4,z6]),(0,[z1,z2,z91,z3,z4,z5,z29]),(0,[z1,z164,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z165,z5,z6]),(1,[z1,z2,z21,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z166]),(0,[z1,z2,z3,z167,z4,z5,z6])],[(1,[z1,z2,z3,z168,z4,z5]),(1,[z1,z2,z3,z4,z5,z169]),(0,[z1,z170,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z86]),(0,[z1,z2,z3,z4,z5,z171,z6]),(1,[z1,z2,z172,z4,z5,z6]),(0,[z100,z1,z2,z3,z4,z5,z29]),(0,[z1,z78,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z57,z36,z4,z5])],[(0,[z1,z2,z64,z3,z4,z5,z29]),(0,[z1,z89,z2,z3,z4,z5,z6]),(0,[z1,z2,z173,z4,z140,z5,z6]),(0,[z1,z174,z2,z99,z3,z5,z6]),(0,[z1,z61,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z4,z175,z5,z6]),(0,[z1,z2,z3,z176,z5,z59,z6]),(0,[z1,z2,z177,z21,z3,z4,z5]),(0,[z1,z2,z178,z3,z4,z5,z6])]],
   [[(1,[z109,z2,z179,z4,z5,z6]),(0,[z1,z2,z3,z19,z36,z4,z5]),(0,[z180,z1,z2,z3,z4,z5,z6]),(0,[z32,z1,z3,z4,z52,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z67]),(1,[z1,z2,z3,z181,z5,z6])],[(0,[z1,z2,z3,z182,z4,z5,z6])],[(0,[z183,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z184,z5,z6]),(0,[z1,z2,z115,z3,z4,z5,z29]),(0,[z100,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z64,z3,z4,z97,z6]),(0,[z1,z185,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z36,z4,z5,z58])],[(0,[z1,z2,z3,z4,z186,z5,z6]),(0,[z1,z2,z103,z3,z4,z97,z6]),(0,[z1,z187,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z58]),(0,[z1,z2,z3,z5,z59,z6,z31]),(0,[z1,z2,z3,z36,z4,z188,z5])],[(1,[z1,z189,z2,z3,z4,z6]),(0,[z1,z2,z3,z190,z4,z5,z6]),(0,[z1,z2,z3,z36,z4,z5,z43])],[(0,[z1,z2,z3,z4,z5,z6,z191]),(0,[z1,z2,z3,z4,z192,z5,z6]),(0,[z1,z2,z193,z3,z4,z5,z6]),(0,[z1,z2,z21,z194,z3,z4,z5]),(0,[z1,z2,z21,z3,z4,z5,z43])],[(0,[z1,z2,z3,z4,z5,z195,z6]),(0,[z1,z2,z91,z194,z4,z5,z6])],[(0,[z100,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z196,z4,z5,z6]),(0,[z1,z2,z64,z3,z4,z52,z6]),(0,[z1,z2,z3,z4,z197,z5,z6]),(0,[z1,z2,z3,z4,z5,z198,z6])]],
   [[(0,[z1,z2,z76,z3,z4,z5,z6]),(0,[z109,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z199,z4,z5,z6]),(0,[z1,z2,z3,z4,z200,z5,z6]),(0,[z1,z2,z201,z3,z4,z5,z6]),(0,[z1,z2,z3,z36,z4,z52,z5]),(0,[z1,z2,z202,z3,z4,z5,z6])],[(0,[z158,z2,z3,z4,z50,z5,z6]),(0,[z1,z2,z172,z3,z4,z5,z6]),(1,[z1,z174,z3,z203,z5,z6]),(0,[z1,z2,z64,z11,z4,z5,z6])],[(0,[z1,z2,z21,z76,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z204])],[(0,[z1,z139,z3,z4,z5,z97,z6]),(0,[z109,z205,z2,z3,z4,z5,z6]),(0,[z1,z2,z206,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z207,z6]),(0,[z1,z2,z208,z3,z4,z5,z6]),(0,[z1,z2,z209,z3,z4,z5,z6]),(0,[z1,z2,z3,z36,z4,z140,z5]),(0,[z1,z2,z3,z4,z5,z97,z6]),(0,[z1,z2,z3,z36,z4,z5,z65]),(0,[z1,z2,z3,z4,z5,z210,z6]),(0,[z1,z2,z3,z4,z5,z211,z6])],[(0,[z1,z212,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z203,z50,z5,z6]),(0,[z1,z2,z3,z4,z5,z213,z6]),(0,[z1,z2,z21,z3,z4,z140,z5]),(0,[z1,z2,z214,z3,z4,z5,z6]),(0,[z1,z215,z2,z3,z4,z5,z6]),(0,[z1,z2,z216,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z39,z5,z6]),(0,[z109,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z4,z5,z217,z6]),(0,[z1,z2,z99,z3,z4,z218,z6]),(0,[z1,z2,z83,z3,z165,z5,z6])],[(0,[z1,z2,z3,z219,z4,z5,z6]),(0,[z1,z2,z220,z3,z4,z5,z6]),(0,[z1,z33,z2,z3,z4,z5,z221]),(0,[z1,z2,z222,z3,z4,z5,z6])],[(0,[z1,z2,z103,z76,z4,z5,z6]),(1,[z1,z2,z3,z94,z4,z5]),(0,[z1,z2,z3,z4,z5,z223,z6]),(0,[z1,z2,z224,z3,z4,z5,z6]),(0,[z1,z2,z83,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z225,z5,z6]),(0,[z226,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z227]),(0,[z1,z2,z3,z228,z4,z5,z6])],[(0,[z229,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z230,z3,z4,z5,z6]),(0,[z26,z1,z2,z3,z4,z51,z6]),(1,[z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z165,z5,z29]),(0,[z1,z2,z21,z41,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z231,z6]),(0,[z1,z136,z2,z3,z36,z4,z5])],[(1,[z1,z2,z3,z4,z5,z232]),(0,[z158,z1,z2,z3,z98,z5,z6]),(0,[z1,z2,z156,z3,z4,z5,z16]),(0,[z1,z2,z3,z233,z4,z5,z6]),(0,[z1,z2,z234,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z235,z5,z6]),(0,[z236,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z237,z4,z5,z6]),(0,[z1,z2,z83,z3,z4,z5,z16]),(0,[z1,z2,z238,z3,z4,z5,z6]),(0,[z1,z2,z239,z3,z4,z5,z43]),(0,[z1,z2,z240,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z69,z6]),(0,[z139,z2,z40,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z169]),(0,[z1,z2,z3,z4,z5,z241,z6]),(0,[z1,z89,z2,z3,z4,z5,z29]),(0,[z1,z2,z104,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z242]),(0,[z1,z243,z2,z3,z4,z5,z6])],[(0,[z244,z1,z2,z3,z4,z5,z6]),(0,[z245,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z246,z5,z6]),(0,[z1,z2,z247,z3,z4,z5,z6]),(1,[z1,z33,z3,z4,z5,z34])],[(0,[z102,z1,z2,z3,z248,z5,z6]),(0,[z1,z2,z249,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z250,z5,z6]),(0,[z251,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z252,z43])],[(0,[z253,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z254,z6]),(0,[z1,z2,z3,z255,z4,z5,z6]),(0,[z1,z2,z256,z3,z4,z5,z6]),(0,[z1,z2,z3,z257,z4,z5,z6]),(0,[z1,z2,z156,z3,z36,z4,z5])]],
   [[(1,[z1,z2,z3,z4,z5,z258]),(0,[z1,z2,z3,z117,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z259]),(0,[z93,z1,z2,z3,z98,z5,z6]),(0,[z26,z1,z2,z64,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z260]),(1,[z1,z2,z222,z3,z4,z5]),(0,[z1,z2,z83,z3,z36,z4,z5]),(0,[z160,z1,z2,z3,z36,z4,z5])],[(0,[z261,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z262,z5,z6]),(0,[z1,z2,z99,z3,z98,z5,z6]),(1,[z1,z2,z263,z3,z4,z5])],[(0,[z1,z2,z264,z3,z4,z5,z6]),(0,[z1,z2,z265,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z266,z6])],[(1,[z1,z2,z3,z4,z5,z267]),(0,[z1,z2,z3,z4,z5,z268,z6]),(0,[z1,z2,z3,z181,z4,z5,z6])],[(0,[z1,z269,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z74,z43,z6]),(0,[z13,z1,z2,z21,z3,z4,z5])],[(1,[z1,z2,z270,z3,z4,z6]),(0,[z1,z2,z76,z3,z4,z5,z29]),(0,[z1,z2,z3,z248,z4,z5,z6]),(0,[z102,z1,z61,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z200,z5,z29]),(0,[z1,z89,z2,z3,z36,z4,z5]),(0,[z1,z2,z11,z4,z165,z5,z6]),(0,[z1,z2,z3,z4,z27,z65,z6]),(0,[z1,z2,z3,z271,z4,z5,z6])],[(0,[z1,z2,z3,z4,z272,z5,z6]),(0,[z102,z26,z2,z3,z4,z5,z6]),(0,[z26,z1,z2,z3,z4,z5,z6]),(0,[z102,z32,z1,z2,z3,z4,z6]),(0,[z1,z2,z21,z3,z19,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z273]),(0,[z1,z2,z3,z36,z44,z4,z5])],[(0,[z1,z274,z2,z3,z4,z5,z6]),(0,[z158,z1,z2,z3,z4,z5,z275]),(0,[z1,z2,z3,z276,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z242,z6]),(0,[z1,z2,z3,z4,z277,z5,z6]),(0,[z1,z2,z3,z278,z4,z5,z6])]],
   [[(0,[z1,z139,z2,z3,z4,z5,z6]),(0,[z1,z2,z40,z21,z3,z4,z5]),(1,[z1,z2,z3,z4,z279,z6]),(0,[z1,z2,z3,z36,z4,z5,z113]),(0,[z1,z2,z3,z4,z5,z97,z29]),(0,[z1,z2,z3,z4,z5,z16,z221]),(0,[z1,z2,z3,z4,z280,z5,z6]),(0,[z1,z147,z2,z3,z4,z5,z6]),(0,[z1,z147,z2,z21,z3,z4,z5]),(0,[z1,z2,z281,z3,z5,z6,z282])],[(0,[z1,z2,z76,z3,z4,z5,z16]),(0,[z283,z1,z2,z3,z4,z5,z6]),(0,[z1,z284,z2,z3,z4,z5,z6]),(0,[z1,z285,z2,z3,z4,z5,z6]),(0,[z18,z1,z2,z3,z4,z5,z286]),(0,[z1,z287,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z288,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z289,z6]),(0,[z1,z2,z3,z4,z5,z290,z6]),(0,[z1,z2,z3,z4,z5,z6,z291]),(0,[z1,z2,z3,z4,z5,z292,z6]),(0,[z1,z2,z21,z8,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z29,z31]),(0,[z1,z2,z3,z4,z140,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z293])],[(0,[z1,z294,z2,z3,z4,z5,z6]),(0,[z1,z2,z270,z3,z179,z4,z6]),(1,[z1,z2,z120,z4,z5,z6]),(0,[z1,z295,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z29,z221]),(0,[z1,z2,z3,z4,z5,z296,z6]),(0,[z1,z297,z2,z3,z4,z5,z6]),(0,[z1,z89,z2,z3,z4,z42,z6]),(0,[z1,z2,z3,z36,z203,z4,z5]),(0,[z55,z1,z2,z21,z3,z4,z5]),(1,[z1,z2,z3,z5,z298,z6])],[(0,[z45,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z299,z4,z5,z6]),(0,[z1,z2,z3,z120,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z97,z16]),(0,[z1,z2,z300,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z203,z4,z5]),(0,[z1,z61,z2,z21,z3,z4,z5]),(1,[z1,z2,z3,z4,z5,z301]),(0,[z1,z2,z302,z3,z4,z5,z6])],[(0,[z158,z1,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z4,z303,z5,z6]),(0,[z1,z2,z194,z3,z4,z5,z282]),(0,[z1,z2,z3,z4,z304,z5,z6]),(0,[z1,z2,z305,z3,z4,z5,z6])],[(0,[z306,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z76,z3,z36,z4,z5]),(0,[z307,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z308,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z309,z6]),(0,[z1,z2,z4,z22,z5,z65,z6]),(0,[z1,z2,z3,z4,z27,z22,z6]),(0,[z1,z310,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z176,z5,z6]),(0,[z1,z2,z3,z36,z4,z5,z311]),(0,[z1,z2,z3,z4,z5,z6,z312])],[(0,[z1,z33,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z313,z6])]],
   [[(0,[z109,z2,z3,z179,z4,z5,z6]),(1,[z1,z314,z3,z4,z5,z6]),(0,[z1,z2,z79,z21,z3,z4,z5]),(0,[z1,z2,z21,z3,z5,z6,z31])],[(0,[z1,z2,z3,z4,z5,z6,z232]),(1,[z1,z2,z87,z4,z5,z6]),(0,[z1,z2,z3,z4,z315,z5,z6])],[(0,[z93,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z316,z3,z98,z4,z5]),(0,[z317,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z99,z3,z4,z5,z16]),(0,[z1,z2,z318,z3,z4,z5,z6])],[(0,[z1,z2,z3,z319,z4,z5,z6]),(0,[z100,z1,z2,z21,z3,z4,z5]),(0,[z320,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z321,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z59,z6])],[(0,[z1,z2,z3,z4,z5,z258,z6]),(0,[z1,z2,z3,z4,z5,z34,z29]),(0,[z1,z2,z3,z4,z322,z5,z6]),(0,[z1,z2,z3,z323,z36,z4,z5])],[(0,[z1,z2,z324,z3,z4,z5,z6]),(0,[z1,z2,z3,z325,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z17]),(0,[z18,z1,z2,z99,z4,z5,z6]),(0,[z1,z2,z326,z3,z4,z5,z6]),(0,[z1,z2,z327,z3,z4,z5,z6]),(0,[z1,z2,z328,z3,z4,z5,z6])],[(0,[z93,z1,z2,z3,z36,z4,z5]),(0,[z2,z3,z4,z5,z16,z6,z29]),(0,[z1,z2,z99,z3,z4,z329,z6]),(1,[z1,z2,z3,z4,z330,z5]),(0,[z1,z331,z2,z3,z4,z5,z6]),(0,[z1,z332,z2,z3,z36,z4,z5])]],
   [[(0,[z109,z1,z2,z179,z4,z5,z6]),(0,[z1,z2,z41,z76,z4,z5,z6]),(0,[z333,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z255,z4,z5,z16]),(0,[z334,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z99,z3,z36,z4,z5])],[(0,[z1,z335,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z11,z4,z5,z29]),(0,[z1,z2,z336,z3,z4,z5,z6]),(0,[z18,z1,z3,z19,z4,z5,z6]),(0,[z1,z147,z3,z4,z5,z6,z221]),(0,[z1,z2,z337,z3,z4,z5,z6])],[(0,[z109,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z338,z4,z5,z6]),(0,[z1,z2,z3,z50,z140,z5,z6]),(0,[z1,z2,z3,z4,z27,z5,z339]),(0,[z1,z2,z3,z4,z5,z6,z340])],[(0,[z1,z2,z3,z341,z4,z5,z6]),(0,[z1,z2,z3,z342,z4,z5,z6]),(0,[z343,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z222,z3,z4,z165,z5]),(0,[z1,z2,z21,z3,z176,z4,z5]),(0,[z1,z344,z2,z3,z4,z5,z6])],[(0,[z102,z1,z2,z3,z4,z51,z6]),(0,[z1,z2,z3,z4,z5,z38,z29]),(0,[z1,z88,z2,z11,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z345])],[(0,[z346,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z207]),(0,[z347,z1,z2,z3,z4,z5,z6]),(1,[z93,z2,z3,z98,z5,z6]),(0,[z1,z147,z2,z3,z4,z5,z29]),(0,[z1,z2,z348,z3,z4,z5,z6])],[(1,[z1,z88,z41,z4,z5,z6]),(0,[z1,z147,z2,z3,z4,z5,z34]),(0,[z1,z2,z3,z4,z5,z349,z6]),(0,[z1,z2,z3,z4,z188,z5,z6])],[(0,[z350,z1,z2,z3,z4,z5,z6]),(1,[z102,z2,z3,z4,z113,z6]),(0,[z26,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z140,z5,z29]),(0,[z1,z2,z3,z4,z5,z351,z6]),(0,[z32,z1,z2,z3,z4,z97,z6]),(0,[z1,z2,z3,z176,z4,z27,z6])]],
   [[(0,[z1,z2,z230,z3,z4,z50,z5]),(0,[z1,z2,z3,z4,z5,z296,z29]),(0,[z1,z274,z2,z3,z4,z5,z16]),(0,[z1,z88,z41,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z27,z5,z6])],[(0,[z1,z139,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z16,z6]),(0,[z1,z61,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z16,z282])],[(0,[z1,z2,z352,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z4,z5,z29]),(1,[z1,z2,z264,z3,z5,z6]),(0,[z1,z2,z353,z3,z4,z5,z6]),(0,[z1,z2,z3,z354,z4,z5,z6]),(1,[z1,z2,z281,z3,z5,z6])],[(0,[z68,z1,z2,z3,z4,z5,z6]),(0,[z68,z45,z2,z3,z4,z5,z6]),(0,[z1,z2,z355,z3,z4,z5,z6]),(0,[z102,z1,z2,z3,z356,z5,z6]),(0,[z102,z1,z2,z64,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z29,z357]),(0,[z1,z358,z2,z3,z4,z5,z6]),(0,[z1,z359,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z301])],[(1,[z205,z2,z76,z4,z5,z6]),(0,[z1,z2,z3,z203,z98,z5,z6]),(0,[z26,z1,z2,z3,z36,z4,z5]),(0,[z1,z33,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z29,z282]),(1,[z1,z2,z3,z342,z4,z5]),(0,[z1,z2,z3,z4,z5,z360,z6]),(0,[z1,z2,z361,z3,z4,z5,z6])],[(0,[z1,z2,z3,z362,z4,z5,z6]),(0,[z1,z2,z363,z3,z4,z5,z6]),(0,[z45,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z176,z98,z5,z6]),(0,[z1,z2,z3,z4,z97,z113,z6]),(0,[z26,z1,z2,z3,z4,z43,z6]),(0,[z1,z77,z2,z3,z4,z5,z29]),(0,[z1,z364,z2,z3,z4,z5,z6]),(0,[z1,z33,z2,z3,z4,z5,z34]),(0,[z1,z2,z83,z3,z5,z59,z6])],[(0,[z1,z139,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z4,z365,z5,z6]),(0,[z366,z1,z2,z3,z4,z5,z6])],[(0,[z367,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z316,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z29,z368]),(1,[z1,z2,z3,z4,z5,z369])]],
   [[(1,[z100,z2,z3,z4,z5,z16]),(0,[z1,z33,z2,z3,z4,z5,z16]),(0,[z1,z88,z2,z41,z4,z5,z6]),(0,[z1,z2,z3,z36,z4,z5,z31]),(1,[z1,z2,z156,z3,z4,z67])],[(0,[z1,z2,z3,z4,z5,z370,z6]),(0,[z1,z61,z2,z3,z4,z52,z6]),(0,[z1,z2,z3,z36,z4,z5,z221]),(0,[z1,z2,z3,z371,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z31])],[(1,[z1,z2,z3,z362,z5,z6]),(0,[z1,z2,z3,z4,z5,z372,z6]),(0,[z45,z1,z2,z3,z36,z4,z5]),(0,[z373,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z374,z5,z6]),(0,[z102,z1,z2,z3,z4,z27,z6]),(0,[z1,z2,z3,z4,z5,z375,z6]),(1,[z1,z2,z376,z3,z5,z6]),(0,[z1,z2,z376,z3,z19,z5,z6]),(0,[z1,z89,z2,z21,z3,z4,z5]),(0,[z1,z2,z377,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z221]),(1,[z1,z2,z3,z176,z27,z6])],[(1,[z1,z2,z3,z4,z135,z6]),(0,[z378,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z379]),(0,[z1,z2,z3,z4,z380,z5,z6]),(0,[z1,z2,z381,z3,z4,z5,z6]),(0,[z1,z2,z382,z3,z36,z4,z5])],[(0,[z1,z2,z179,z4,z5,z65,z6]),(0,[z1,z2,z3,z4,z383,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z384]),(0,[z1,z147,z2,z194,z3,z4,z5]),(0,[z1,z2,z3,z4,z385,z5,z6])],[(1,[z1,z2,z3,z4,z272,z6]),(0,[z1,z386,z2,z3,z4,z5,z6]),(0,[z205,z1,z2,z3,z387,z5,z6]),(0,[z1,z2,z3,z4,z388,z5,z6]),(0,[z389,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z59,z16]),(0,[z1,z33,z2,z3,z36,z4,z5]),(0,[z1,z2,z99,z83,z4,z5,z6])],[(0,[z1,z189,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z322,z5,z16]),(0,[z1,z89,z2,z3,z4,z135,z6]),(0,[z1,z2,z3,z4,z390,z5,z6]),(0,[z1,z2,z3,z4,z5,z391,z6]),(0,[z1,z2,z35,z3,z176,z5,z6])],[(0,[z109,z1,z2,z3,z4,z5,z29]),(0,[z26,z1,z2,z3,z4,z5,z70]),(0,[z1,z2,z392,z3,z4,z5,z6]),(0,[z1,z2,z3,z393,z4,z5,z6])]],
   [[(0,[z109,z1,z2,z3,z4,z5,z232]),(0,[z1,z2,z3,z394,z4,z5,z6]),(0,[z1,z2,z3,z98,z5,z43,z6]),(0,[z1,z2,z3,z4,z51,z5,z6]),(0,[z1,z41,z3,z19,z4,z5,z6]),(0,[z1,z174,z2,z3,z4,z5,z6]),(0,[z1,z2,z99,z4,z22,z5,z6]),(0,[z1,z2,z156,z3,z4,z66,z6])],[(0,[z1,z2,z3,z395,z4,z5,z6]),(0,[z1,z2,z396,z3,z4,z5,z6]),(1,[z1,z2,z91,z4,z5,z282])],[(0,[z1,z2,z3,z397,z4,z5,z6]),(1,[z1,z61,z3,z4,z97,z6]),(0,[z398,z1,z2,z3,z4,z5,z6]),(0,[z399,z1,z2,z3,z4,z5,z6]),(0,[z400,z1,z2,z3,z4,z5,z6]),(0,[z400,z1,z2,z21,z3,z4,z5]),(0,[z1,z2,z401,z3,z4,z5,z6])],[(1,[z1,z2,z3,z248,z5,z6]),(1,[z1,z2,z3,z255,z4,z5]),(0,[z1,z2,z4,z5,z58,z6,z282])],[(0,[z1,z2,z21,z3,z4,z52,z5]),(0,[z1,z2,z91,z3,z4,z5,z58])],[(0,[z402,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z27,z5,z29]),(0,[z1,z2,z3,z4,z5,z6,z403]),(0,[z1,z2,z3,z4,z404,z5,z6])],[(0,[z158,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z405,z4,z5,z6]),(0,[z1,z2,z3,z4,z406,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z407]),(1,[z1,z2,z3,z4,z66,z38])],[(0,[z1,z2,z3,z4,z408,z5,z6]),(0,[z1,z2,z99,z3,z11,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z65])]],
   [[(0,[z1,z2,z3,z176,z50,z5,z6]),(0,[z1,z2,z71,z3,z4,z140,z5]),(1,[z32,z1,z3,z4,z52,z6])],[(0,[z1,z2,z237,z3,z4,z5,z6]),(0,[z1,z2,z409,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z29,z410]),(0,[z1,z2,z156,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z27,z5,z16]),(0,[z1,z2,z411,z3,z4,z5,z6]),(0,[z1,z2,z3,z412,z4,z5,z6]),(0,[z1,z2,z361,z4,z5,z43,z6]),(0,[z1,z2,z3,z4,z413,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z414])],[(0,[z45,z1,z2,z3,z4,z5,z86]),(0,[z1,z2,z3,z4,z5,z16,z16]),(0,[z1,z2,z3,z4,z5,z415,z6]),(0,[z1,z2,z3,z323,z4,z5,z6]),(0,[z1,z2,z21,z103,z3,z4,z5]),(0,[z1,z2,z416,z3,z4,z5,z6])],[(0,[z1,z2,z99,z179,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z267,z6]),(0,[z1,z2,z3,z4,z5,z417,z6]),(0,[z1,z2,z418,z3,z4,z5,z6]),(0,[z1,z2,z103,z3,z4,z22,z6]),(0,[z1,z2,z3,z4,z419,z5,z6]),(0,[z1,z2,z3,z4,z5,z298,z6])],[(0,[z68,z1,z2,z3,z4,z5,z16]),(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z93,z1,z2,z21,z3,z4,z5]),(0,[z1,z2,z355,z3,z4,z5,z16]),(0,[z1,z2,z173,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z369,z6]),(0,[z1,z2,z21,z156,z3,z4,z5]),(0,[z1,z332,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z420])],[(0,[z1,z421,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z16,z114]),(0,[z1,z2,z3,z4,z5,z6,z422]),(0,[z1,z2,z3,z4,z5,z423,z6]),(0,[z1,z2,z99,z3,z4,z5,z6]),(0,[z1,z2,z99,z64,z4,z5,z6]),(0,[z1,z2,z3,z4,z424,z5,z6]),(0,[z236,z1,z2,z21,z3,z4,z5])],[(0,[z68,z2,z40,z3,z4,z5,z6]),(0,[z32,z1,z40,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z171]),(0,[z1,z2,z425,z3,z4,z5,z6]),(0,[z1,z2,z426,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z427]),(0,[z1,z33,z147,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z428,z5,z6]),(0,[z1,z2,z64,z103,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z429,z6]),(1,[z1,z2,z103,z4,z22,z6]),(0,[z1,z430,z2,z3,z4,z5,z6]),(1,[z1,z2,z21,z3,z5,z43])],[(0,[z1,z2,z3,z431,z4,z5,z6]),(0,[z26,z1,z2,z3,z4,z113,z6]),(0,[z1,z2,z3,z4,z432,z5,z6]),(0,[z1,z2,z433,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z434,z6]),(0,[z1,z2,z435,z3,z4,z5,z6]),(0,[z1,z436,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z437,z6]),(1,[z1,z2,z21,z3,z36,z5])],[(0,[z68,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z4,z438,z5,z6]),(0,[z1,z2,z316,z3,z4,z5,z6]),(0,[z1,z88,z2,z3,z4,z351,z6])],[(0,[z1,z2,z3,z4,z5,z439,z6]),(0,[z102,z1,z2,z3,z4,z5,z16]),(1,[z1,z2,z3,z4,z5,z440]),(0,[z1,z2,z3,z36,z4,z5,z282])],[(0,[z441,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z282]),(0,[z1,z2,z3,z4,z442,z5,z6]),(0,[z1,z2,z156,z3,z4,z5,z67])],[(0,[z1,z2,z3,z443,z4,z5,z6]),(0,[z1,z2,z83,z11,z4,z5,z6]),(1,[z1,z2,z239,z3,z4,z5])],[(0,[z2,z76,z3,z179,z4,z5,z6]),(0,[z1,z2,z3,z4,z444,z5,z6]),(0,[z1,z174,z2,z3,z4,z5,z29]),(0,[z445,z1,z2,z3,z4,z5,z6]),(0,[z1,z174,z3,z203,z4,z5,z6])],[],[(0,[z446,z1,z2,z3,z4,z5,z6]),(0,[z102,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z4,z5,z447,z6])]],
   [[(1,[z1,z2,z3,z4,z69,z6]),(0,[z102,z1,z448,z3,z4,z5,z6]),(0,[z102,z1,z2,z3,z4,z43,z6]),(0,[z100,z2,z3,z4,z5,z16,z6]),(1,[z1,z2,z3,z4,z449,z6]),(0,[z1,z2,z3,z27,z5,z43,z6]),(0,[z450,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z451,z3,z4,z5,z6]),(0,[z26,z1,z2,z21,z3,z4,z5]),(0,[z1,z2,z3,z4,z51,z5,z16]),(0,[z1,z2,z3,z4,z5,z452,z6]),(0,[z1,z174,z2,z3,z4,z5,z16])],[(0,[z205,z1,z2,z3,z117,z5,z6]),(0,[z1,z2,z453,z3,z4,z5,z6]),(0,[z1,z2,z3,z98,z4,z5,z6]),(0,[z1,z448,z2,z3,z4,z5,z6]),(0,[z1,z454,z2,z3,z4,z5,z6]),(0,[z1,z455,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z456,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z139,z2,z21,z3,z4,z5]),(0,[z1,z2,z457,z3,z4,z5,z6]),(0,[z158,z1,z2,z3,z4,z5,z29]),(1,[z1,z2,z209,z3,z4,z5]),(0,[z1,z2,z458,z4,z140,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z459]),(0,[z1,z2,z3,z4,z5,z6,z460]),(0,[z461,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z462,z6]),(0,[z1,z2,z21,z3,z4,z5,z113]),(0,[z1,z2,z3,z4,z5,z213,z29]),(0,[z1,z463,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z464,z6])],[(0,[z68,z1,z2,z3,z4,z5,z75]),(0,[z1,z2,z83,z3,z4,z5,z301]),(0,[z1,z2,z103,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z465,z5,z6])],[(0,[z1,z2,z3,z4,z5,z29,z466]),(0,[z1,z174,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z4,z97,z43,z6]),(0,[z1,z2,z3,z4,z5,z467,z6]),(0,[z1,z2,z83,z3,z4,z5,z468])],[(0,[z45,z1,z2,z21,z3,z4,z5]),(0,[z158,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z168,z4,z5,z6]),(0,[z469,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z470,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z471,z6]),(0,[z102,z2,z3,z4,z5,z113,z6]),(0,[z1,z2,z99,z3,z165,z5,z6]),(1,[z1,z2,z3,z4,z5,z468]),(0,[z1,z2,z194,z3,z4,z5,z6]),(0,[z1,z2,z382,z3,z4,z5,z6])],[(0,[z93,z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z21,z3,z371,z4,z5])],[(0,[z1,z2,z76,z11,z4,z5,z6]),(0,[z1,z2,z99,z3,z4,z5,z29]),(1,[z18,z1,z19,z4,z5,z6]),(0,[z1,z33,z2,z21,z3,z4,z5]),(0,[z1,z2,z3,z54,z4,z5,z6])],[(0,[z1,z2,z425,z3,z4,z5,z29]),(1,[z1,z2,z3,z4,z5,z286]),(0,[z472,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z173,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z473])],[(0,[z158,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z4,z5,z70,z6]),(0,[z474,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z475]),(0,[z476,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z36,z98,z4,z5]),(0,[z1,z2,z477,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z478,z6]),(0,[z1,z2,z3,z479,z4,z5,z6])],[(0,[z480,z1,z2,z3,z4,z5,z6]),(0,[z205,z1,z2,z3,z4,z5,z481]),(0,[z1,z2,z21,z3,z98,z4,z5]),(0,[z18,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z99,z21,z3,z5]),(0,[z1,z2,z3,z4,z5,z6,z482])]],
   [[(0,[z205,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z483,z5,z6]),(1,[z1,z2,z3,z4,z5,z150])],[(0,[z484,z1,z2,z3,z4,z5,z6]),(0,[z93,z1,z2,z159,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z440]),(0,[z1,z2,z485,z3,z4,z5,z6]),(0,[z1,z2,z3,z486,z4,z5,z6]),(0,[z1,z2,z327,z21,z3,z4,z5])],[(0,[z487,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z488,z6]),(0,[z1,z2,z316,z3,z4,z5,z16]),(0,[z1,z2,z3,z458,z4,z5,z6]),(0,[z489,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z23]),(1,[z1,z2,z3,z4,z5,z110]),(0,[z1,z2,z76,z19,z4,z5,z6]),(0,[z1,z2,z3,z490,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z439,z16]),(0,[z1,z2,z3,z36,z4,z5,z16]),(0,[z1,z174,z2,z83,z3,z5,z6]),(0,[z1,z2,z3,z4,z491,z5,z6]),(0,[z1,z2,z492,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z6,z493]),(0,[z1,z2,z3,z4,z5,z6,z31])],[(0,[z102,z1,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z5,z494,z6]),(0,[z1,z2,z495,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z221]),(0,[z1,z2,z21,z3,z4,z130,z5])],[(0,[z109,z1,z2,z21,z3,z4,z5]),(0,[z1,z2,z143,z3,z4,z5,z6])],[(0,[z1,z2,z496,z3,z4,z5,z6]),(0,[z26,z1,z2,z3,z4,z5,z29]),(1,[z1,z2,z46,z3,z4,z5]),(0,[z1,z497,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z498,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z499]),(0,[z1,z455,z2,z3,z4,z5,z29]),(0,[z1,z2,z453,z3,z4,z5,z29]),(0,[z1,z2,z3,z500,z4,z5,z6])]],
   [[(0,[z1,z139,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z501,z6]),(0,[z1,z2,z502,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z503,z6]),(0,[z1,z2,z3,z504,z4,z5,z6]),(0,[z1,z89,z2,z3,z203,z5,z6]),(0,[z1,z2,z3,z203,z4,z5,z6]),(0,[z1,z2,z505,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z506]),(0,[z1,z2,z3,z36,z36,z4,z5])],[(0,[z1,z2,z3,z4,z5,z16,z227]),(0,[z1,z88,z2,z3,z4,z449,z6]),(0,[z507,z1,z2,z3,z4,z5,z6]),(0,[z1,z508,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z509,z6]),(0,[z1,z2,z3,z176,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z510,z6]),(0,[z102,z1,z2,z3,z4,z113,z6]),(0,[z1,z2,z3,z4,z52,z51,z6]),(0,[z1,z2,z3,z4,z511,z5,z6]),(0,[z1,z2,z3,z512,z4,z5,z6]),(0,[z1,z513,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z98,z4,z5,z16]),(0,[z1,z2,z514,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z515]),(0,[z1,z2,z3,z4,z516,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z517]),(0,[z1,z2,z3,z4,z27,z5,z369]),(0,[z1,z2,z156,z3,z4,z6,z67])],[(0,[z45,z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z518,z3,z4,z5,z6]),(0,[z1,z519,z2,z3,z4,z5,z6]),(0,[z520,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z281,z3,z4,z5,z6]),(0,[z1,z2,z35,z3,z4,z27,z6]),(0,[z521,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z50,z5,z6]),(0,[z1,z2,z3,z4,z52,z113,z6]),(0,[z1,z2,z194,z3,z4,z5,z29])],[(0,[z68,z1,z2,z21,z3,z4,z5]),(0,[z1,z2,z103,z3,z4,z5,z16]),(0,[z522,z1,z2,z3,z4,z5,z6]),(0,[z1,z523,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z524,z5,z6]),(0,[z1,z61,z2,z3,z4,z97,z6]),(0,[z1,z2,z3,z4,z66,z5,z6]),(0,[z1,z2,z3,z4,z38,z6,z67])]],
   [[(0,[z45,z1,z139,z3,z4,z5,z6]),(0,[z1,z2,z3,z525,z4,z5,z6]),(1,[z1,z2,z194,z4,z5,z58])],[(0,[z1,z2,z3,z526,z4,z5,z6]),(0,[z93,z1,z2,z87,z4,z5,z6]),(0,[z1,z2,z194,z3,z4,z5,z16]),(0,[z1,z174,z2,z3,z140,z5,z6]),(0,[z1,z2,z527,z3,z4,z5,z6])],[(1,[z28,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z6,z286]),(1,[z1,z2,z3,z4,z5,z427]),(0,[z1,z2,z528,z3,z4,z5,z6]),(0,[z1,z2,z156,z3,z4,z5,z38])],[(0,[z1,z2,z3,z4,z22,z5,z16]),(1,[z1,z2,z3,z4,z351,z6]),(0,[z529,z1,z2,z3,z4,z5,z6]),(0,[z530,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z103,z3,z36,z4,z5]),(0,[z531,z1,z2,z3,z36,z4,z5])],[(0,[z102,z1,z2,z3,z4,z5,z6]),(0,[z102,z1,z2,z21,z3,z4,z5]),(0,[z26,z1,z2,z103,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z59,z29]),(0,[z1,z2,z3,z4,z532,z5,z6]),(0,[z1,z2,z3,z4,z5,z58,z221]),(0,[z1,z2,z21,z3,z5,z43,z6])],[(0,[z1,z2,z3,z4,z533,z5,z6]),(0,[z205,z1,z2,z3,z4,z5,z29]),(1,[z1,z2,z230,z3,z4,z5])],[(0,[z1,z2,z21,z3,z179,z4,z5]),(0,[z534,z1,z2,z3,z4,z5,z6]),(0,[z102,z1,z2,z172,z4,z5,z6]),(0,[z1,z2,z535,z3,z4,z5,z6]),(0,[z1,z2,z194,z3,z36,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z536])],[(0,[z1,z2,z3,z4,z5,z6,z150]),(0,[z1,z2,z3,z4,z449,z5,z6]),(0,[z1,z2,z3,z4,z52,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z537])]],
   [[(0,[z1,z538,z2,z3,z4,z5,z6]),(0,[z1,z2,z539,z3,z4,z5,z6]),(0,[z1,z2,z3,z540,z4,z5,z6]),(1,[z2,z3,z4,z5,z16,z29]),(0,[z18,z1,z2,z3,z4,z5,z16])],[(0,[z1,z2,z270,z3,z4,z5,z6]),(0,[z205,z1,z2,z3,z4,z5,z16]),(1,[z26,z2,z3,z4,z51,z6]),(0,[z541,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z275]),(0,[z1,z542,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z329,z6]),(0,[z1,z2,z543,z3,z4,z5,z6]),(0,[z1,z2,z3,z544,z4,z5,z6])],[(0,[z1,z2,z209,z3,z19,z4,z5]),(0,[z1,z545,z2,z3,z4,z5,z6]),(0,[z1,z174,z2,z21,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z546,z6]),(0,[z1,z2,z3,z4,z5,z6,z547]),(1,[z1,z2,z99,z165,z5,z6]),(0,[z1,z2,z99,z21,z3,z5,z6]),(0,[z548,z1,z2,z3,z4,z5,z6])],[(0,[z549,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z357]),(0,[z1,z2,z3,z550,z4,z5,z6]),(0,[z1,z2,z64,z3,z4,z65,z6]),(0,[z1,z2,z3,z4,z5,z43,z6]),(0,[z1,z2,z3,z551,z4,z5,z6]),(0,[z1,z2,z3,z4,z552,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z553]),(0,[z1,z2,z3,z203,z4,z5,z29]),(0,[z18,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z264,z3,z19,z5,z6]),(0,[z1,z2,z3,z4,z554,z5,z6]),(0,[z1,z2,z103,z3,z4,z65,z6]),(0,[z1,z2,z3,z4,z5,z6,z282])],[(0,[z1,z2,z3,z4,z555,z5,z6]),(1,[z1,z2,z3,z387,z5,z6]),(0,[z205,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z83,z3,z50,z5,z6]),(0,[z1,z2,z3,z168,z4,z50,z5]),(0,[z1,z3,z203,z4,z140,z5,z6]),(0,[z1,z33,z2,z194,z3,z4,z5]),(0,[z1,z2,z194,z4,z5,z58,z6])],[(0,[z556,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z557,z4,z5,z6]),(0,[z1,z2,z314,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z558,z5,z6]),(0,[z1,z2,z559,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z368]),(1,[z1,z89,z3,z140,z5,z6]),(0,[z1,z2,z560,z3,z4,z5,z6])],[(0,[z1,z2,z179,z19,z4,z5,z6]),(0,[z158,z1,z2,z21,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z16,z29]),(0,[z1,z2,z3,z203,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z503,z16]),(0,[z1,z88,z2,z99,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z561,z6]),(0,[z1,z2,z3,z4,z5,z42,z6]),(0,[z562,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z492,z3,z36,z4,z5])],[(0,[z1,z2,z3,z4,z563,z5,z6]),(0,[z564,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z176,z4,z5,z16]),(0,[z1,z2,z3,z4,z565,z5,z6]),(1,[z1,z2,z21,z3,z5,z31])],[(0,[z68,z1,z2,z3,z4,z5,z29]),(0,[z566,z1,z2,z3,z4,z5,z6]),(0,[z1,z89,z174,z3,z4,z5,z6]),(0,[z1,z2,z567,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z27,z97,z6]),(1,[z1,z2,z3,z4,z329,z6]),(0,[z1,z2,z568,z3,z4,z5,z6]),(0,[z1,z2,z569,z3,z4,z5,z6])],[(0,[z1,z2,z3,z98,z4,z106,z6]),(0,[z28,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z4,z5,z29,z29]),(0,[z1,z2,z3,z4,z330,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z570])],[(0,[z68,z1,z2,z237,z4,z5,z6]),(1,[z1,z448,z3,z4,z5,z6]),(0,[z1,z571,z2,z3,z4,z5,z6]),(0,[z1,z2,z64,z3,z4,z22,z6]),(0,[z1,z2,z3,z4,z5,z65,z6]),(0,[z1,z2,z572,z3,z4,z5,z6]),(0,[z1,z2,z3,z66,z5,z298,z6])],[(0,[z1,z2,z3,z4,z50,z5,z16]),(0,[z1,z2,z3,z36,z4,z22,z5])],[(0,[z68,z1,z139,z3,z4,z5,z6]),(0,[z1,z3,z4,z52,z5,z97,z6]),(0,[z1,z2,z99,z4,z165,z5,z6]),(0,[z1,z2,z3,z176,z36,z4,z5])]],
   [[(1,[z68,z40,z3,z4,z5,z6]),(0,[z93,z1,z2,z3,z4,z5,z169]),(0,[z1,z2,z3,z4,z66,z5,z16]),(0,[z1,z2,z3,z4,z27,z52,z6]),(0,[z1,z2,z99,z21,z3,z4,z5]),(0,[z1,z2,z99,z3,z5,z59,z6]),(0,[z1,z2,z3,z176,z4,z43,z6]),(0,[z1,z2,z3,z573,z4,z5,z6])],[(0,[z109,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z110,z6]),(0,[z102,z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z574,z16]),(0,[z32,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z537,z6])],[(0,[z68,z1,z2,z3,z4,z5,z258]),(0,[z1,z436,z2,z21,z3,z4,z5])],[(0,[z1,z2,z3,z98,z140,z5,z6]),(0,[z1,z2,z3,z36,z4,z51,z5]),(0,[z1,z2,z3,z4,z5,z16,z67]),(0,[z1,z2,z3,z4,z575,z5,z6]),(0,[z1,z2,z576,z3,z4,z5,z6]),(0,[z1,z2,z103,z4,z22,z5,z6]),(0,[z1,z2,z3,z4,z5,z577,z6])],[(0,[z1,z163,z2,z3,z4,z5,z6]),(0,[z578,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z579,z3,z4,z5,z6]),(0,[z1,z2,z316,z21,z3,z4,z5])],[(0,[z1,z2,z3,z580,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z581,z6]),(0,[z1,z2,z582,z3,z4,z5,z6]),(0,[z100,z28,z2,z3,z4,z5,z6]),(0,[z1,z583,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z36,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z29,z67]),(0,[z1,z2,z3,z584,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z6])],[(0,[z585,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z41,z3,z4,z5,z16]),(0,[z586,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z587,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z356,z5,z6]),(0,[z1,z2,z3,z4,z51,z5,z29]),(0,[z1,z2,z3,z4,z52,z5,z16]),(0,[z1,z2,z3,z4,z5,z74,z6]),(0,[z1,z2,z3,z4,z5,z588,z6])],[(0,[z1,z2,z3,z4,z5,z6,z275]),(0,[z1,z2,z46,z3,z19,z4,z5]),(0,[z1,z2,z3,z342,z4,z140,z5])],[(0,[z68,z1,z2,z3,z39,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z410]),(0,[z1,z2,z3,z4,z5,z6,z589]),(0,[z1,z2,z3,z4,z218,z5,z6]),(0,[z1,z2,z3,z4,z65,z43,z6])],[(0,[z1,z2,z590,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z51,z97,z6]),(0,[z1,z2,z3,z4,z5,z6,z493]),(0,[z1,z2,z591,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z311,z6])],[(0,[z1,z2,z3,z94,z98,z4,z5]),(0,[z26,z2,z3,z4,z51,z5,z6]),(0,[z1,z2,z3,z36,z11,z4,z5]),(0,[z1,z2,z592,z3,z4,z5,z6]),(0,[z1,z2,z91,z3,z4,z5,z282]),(0,[z1,z2,z35,z3,z5,z43,z6]),(0,[z1,z2,z3,z4,z5,z593,z6])],[(0,[z1,z2,z3,z4,z5,z43,z16]),(0,[z1,z2,z3,z4,z5,z594,z6]),(0,[z1,z2,z595,z3,z4,z5,z6]),(0,[z596,z1,z2,z3,z4,z5,z6])],[(0,[z1,z189,z2,z40,z3,z4,z6]),(0,[z1,z2,z103,z179,z4,z5,z6]),(0,[z1,z2,z3,z4,z106,z5,z6]),(0,[z1,z2,z3,z4,z5,z113,z6]),(0,[z597,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z598,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z52,z43,z6])],[(0,[z1,z2,z599,z3,z4,z5,z6]),(0,[z1,z2,z64,z3,z4,z5,z6]),(0,[z1,z2,z600,z3,z4,z5,z6]),(0,[z601,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z602]),(0,[z603,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z604,z1,z2,z3,z4,z5,z6]),(0,[z531,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z605,z3,z4,z5,z6]),(0,[z1,z88,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z6,z606])],[(0,[z1,z2,z3,z607,z4,z5,z6]),(1,[z1,z163,z2,z3,z4,z6]),(0,[z1,z608,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z56]),(0,[z609,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z610,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z611,z6]),(0,[z1,z2,z3,z36,z4,z27,z5])],[(0,[z1,z2,z3,z4,z612,z5,z6]),(0,[z1,z2,z3,z4,z5,z65,z29]),(0,[z1,z174,z2,z3,z4,z5,z267]),(0,[z1,z2,z3,z4,z5,z613,z6]),(0,[z1,z2,z614,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z27,z5]),(0,[z1,z2,z3,z36,z4,z4,z5]),(0,[z1,z2,z3,z551,z36,z4,z5])],[(0,[z1,z2,z3,z615,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z616,z6]),(0,[z1,z2,z21,z3,z4,z4,z5])],[(0,[z1,z2,z617,z3,z4,z5,z6]),(0,[z1,z2,z239,z3,z4,z5,z6])],[(0,[z1,z88,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z4,z618,z5,z6]),(0,[z1,z2,z3,z619,z4,z5,z6]),(0,[z1,z2,z3,z4,z22,z5,z6])],[(0,[z93,z1,z2,z3,z4,z5,z171]),(0,[z1,z2,z3,z4,z5,z65,z16]),(0,[z1,z2,z3,z94,z36,z4,z5])],[(0,[z32,z26,z1,z2,z3,z4,z6]),(0,[z1,z2,z433,z3,z4,z5,z29]),(0,[z1,z2,z620,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z252,z6]),(0,[z1,z2,z21,z3,z36,z5,z6])]],
   [[(0,[z1,z2,z621,z3,z4,z5,z6]),(0,[z102,z1,z314,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z622,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z623,z5,z6])],[(0,[z1,z624,z2,z3,z4,z5,z6]),(0,[z205,z1,z2,z179,z4,z5,z6]),(0,[z1,z2,z3,z181,z66,z5,z6])],[(0,[z1,z2,z3,z36,z4,z5,z29]),(0,[z32,z1,z2,z3,z4,z5,z16]),(0,[z18,z1,z2,z21,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z625,z6]),(0,[z1,z626,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z259,z6]),(0,[z205,z1,z2,z21,z3,z4,z5]),(1,[z1,z2,z3,z356,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z29]),(0,[z627,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z36,z4,z5,z34]),(1,[z1,z2,z3,z4,z5,z339]),(0,[z1,z2,z92,z3,z4,z5,z6])],[(1,[z1,z2,z458,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z34]),(1,[z1,z2,z3,z4,z218,z6]),(0,[z1,z2,z3,z4,z49,z5,z6])],[(0,[z68,z1,z2,z128,z4,z5,z6]),(0,[z1,z147,z2,z91,z3,z4,z5])],[(0,[z205,z2,z76,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z628,z5,z6]),(0,[z55,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z58,z16]),(0,[z155,z1,z2,z3,z4,z5,z6]),(0,[z1,z89,z2,z99,z3,z5,z6]),(0,[z1,z2,z3,z4,z629,z5,z6]),(0,[z630,z1,z2,z3,z4,z5,z6]),(0,[z631,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z632])],[(0,[z1,z2,z3,z4,z5,z6,z466]),(0,[z1,z2,z21,z3,z4,z5,z16]),(0,[z32,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z37,z3,z36,z4,z5])]],
   [[(0,[z633,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z179,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z481]),(0,[z1,z2,z634,z3,z4,z5,z6]),(0,[z1,z2,z635,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z493,z282])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z636,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z21,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z637,z6]),(0,[z1,z2,z3,z4,z330,z165,z5])],[(0,[z1,z2,z3,z98,z4,z5,z29]),(0,[z1,z2,z3,z638,z4,z5,z6]),(0,[z1,z2,z639,z3,z4,z5,z6]),(0,[z1,z2,z91,z4,z5,z6,z282]),(1,[z1,z2,z21,z3,z176,z5]),(0,[z1,z2,z263,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z640,z5,z6]),(0,[z1,z2,z3,z4,z5,z113,z29]),(0,[z1,z2,z3,z4,z5,z641,z6]),(0,[z1,z2,z3,z4,z642,z5,z6]),(0,[z1,z2,z21,z263,z3,z4,z5]),(0,[z55,z1,z2,z3,z36,z4,z5])],[(0,[z643,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z99,z76,z4,z5,z6]),(0,[z644,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z645,z5,z6]),(0,[z1,z33,z2,z91,z3,z4,z5]),(0,[z1,z2,z177,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z36,z4,z5]),(0,[z1,z2,z3,z36,z4,z5,z67])],[(0,[z1,z2,z103,z3,z4,z5,z29]),(0,[z1,z2,z91,z3,z4,z5,z16]),(0,[z1,z646,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z387,z5,z6]),(0,[z93,z158,z2,z3,z4,z5,z6]),(0,[z1,z2,z83,z3,z98,z5,z6]),(0,[z1,z89,z3,z4,z140,z5,z6]),(0,[z1,z2,z3,z4,z647,z5,z6]),(0,[z1,z2,z3,z4,z5,z648,z6]),(0,[z1,z2,z35,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z649,z6])],[(0,[z1,z650,z2,z3,z4,z5,z6]),(0,[z1,z651,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z113,z16]),(0,[z26,z1,z2,z3,z4,z5,z440]),(0,[z1,z2,z3,z4,z5,z6,z652])]],
   [[(0,[z1,z2,z64,z3,z4,z5,z16]),(0,[z1,z2,z653,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z654,z6]),(0,[z18,z1,z88,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z655,z6]),(0,[z1,z174,z2,z3,z203,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z22,z5,z29]),(0,[z1,z2,z3,z4,z5,z6,z656]),(0,[z1,z2,z3,z36,z4,z165,z5]),(0,[z1,z2,z3,z4,z5,z657,z6]),(0,[z1,z2,z91,z3,z36,z4,z5]),(0,[z1,z2,z21,z35,z3,z4,z5]),(0,[z1,z2,z3,z36,z4,z5,z59])],[(0,[z658,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z574,z6]),(0,[z1,z2,z30,z3,z4,z5,z6]),(0,[z1,z659,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z165,z5]),(0,[z1,z2,z660,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z59]),(0,[z1,z2,z3,z36,z54,z4,z5])],[(0,[z68,z1,z2,z3,z362,z5,z6]),(0,[z1,z2,z3,z36,z4,z50,z5]),(0,[z1,z2,z3,z4,z5,z16,z260]),(0,[z1,z2,z3,z4,z661,z5,z6]),(0,[z1,z147,z2,z3,z4,z5,z221]),(0,[z1,z2,z3,z4,z5,z662,z6]),(0,[z1,z2,z663,z3,z4,z5,z6])],[(0,[z45,z139,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z50,z5]),(0,[z1,z2,z3,z4,z664,z5,z6]),(0,[z1,z2,z103,z3,z4,z52,z6]),(0,[z1,z2,z3,z4,z5,z468,z6]),(0,[z1,z2,z64,z4,z5,z65,z6]),(0,[z1,z2,z64,z3,z36,z4,z5]),(0,[z1,z2,z665,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z66,z5,z38])],[(0,[z1,z2,z3,z4,z666,z5,z6]),(1,[z1,z2,z433,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z478,z29]),(0,[z667,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z668,z5,z6]),(0,[z1,z2,z3,z4,z5,z669,z6]),(0,[z1,z2,z3,z4,z670,z5,z6]),(0,[z1,z671,z2,z3,z4,z5,z6])],[(0,[z68,z1,z2,z3,z4,z272,z6]),(0,[z1,z2,z41,z179,z4,z5,z6]),(0,[z18,z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z6,z672]),(0,[z1,z2,z3,z4,z673,z5,z6]),(0,[z1,z2,z3,z4,z5,z674,z6])]],
   [[(0,[z1,z2,z675,z3,z4,z5,z6]),(0,[z1,z2,z676,z3,z4,z5,z6]),(1,[z1,z2,z361,z4,z5,z6]),(0,[z1,z2,z3,z176,z27,z5,z6])],[(0,[z1,z2,z3,z98,z4,z279,z6]),(0,[z1,z2,z41,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z677,z6]),(0,[z1,z2,z21,z83,z3,z5,z6]),(0,[z1,z678,z2,z3,z4,z5,z6]),(0,[z534,z1,z2,z21,z3,z4,z5])],[(0,[z158,z1,z2,z3,z4,z5,z207]),(0,[z18,z1,z2,z3,z4,z5,z242]),(0,[z679,z1,z2,z3,z4,z5,z6]),(0,[z680,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z339])],[(0,[z1,z2,z179,z11,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z681,z6]),(1,[z1,z2,z3,z4,z5,z252])],[(0,[z1,z2,z143,z3,z179,z4,z6]),(0,[z1,z2,z3,z4,z5,z494,z29]),(0,[z1,z2,z3,z682,z4,z5,z6]),(0,[z1,z2,z3,z4,z683,z5,z6]),(0,[z1,z61,z3,z4,z5,z97,z6]),(0,[z1,z2,z3,z4,z22,z43,z6]),(0,[z1,z2,z3,z4,z5,z684,z6]),(0,[z1,z2,z685,z3,z4,z5,z6]),(0,[z1,z2,z686,z3,z4,z5,z6])],[(0,[z687,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z179,z4,z5,z29]),(0,[z688,z1,z2,z3,z4,z5,z6]),(0,[z1,z689,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z34,z6,z221]),(0,[z1,z2,z194,z3,z4,z5,z58])],[(0,[z690,z1,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z29]),(0,[z1,z174,z2,z3,z4,z5,z427]),(0,[z1,z2,z11,z4,z22,z5,z6]),(0,[z1,z691,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z481]),(0,[z205,z1,z2,z3,z4,z5,z259]),(0,[z1,z2,z376,z3,z4,z5,z6]),(0,[z32,z1,z61,z3,z4,z5,z6]),(1,[z1,z147,z3,z4,z5,z221]),(1,[z1,z2,z21,z83,z3,z5])]],
   [[(0,[z1,z692,z2,z3,z4,z5,z6]),(0,[z693,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z694,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z221,z282])],[(0,[z1,z2,z3,z179,z4,z5,z16]),(0,[z1,z2,z3,z176,z4,z5,z29]),(0,[z695,z1,z2,z3,z4,z5,z6]),(0,[z18,z1,z2,z11,z4,z5,z6]),(0,[z1,z696,z2,z3,z4,z5,z6])],[(1,[z45,z139,z3,z4,z5,z6]),(0,[z1,z2,z697,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z165,z5,z16]),(0,[z1,z88,z2,z3,z4,z5,z6]),(0,[z1,z2,z698,z3,z4,z5,z6]),(0,[z1,z88,z2,z21,z3,z4,z5]),(0,[z699,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z94,z4,z5,z6]),(0,[z1,z2,z3,z700,z4,z5,z6]),(0,[z1,z2,z35,z3,z4,z5,z29]),(0,[z701,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z36,z4,z5,z97])],[(0,[z1,z2,z3,z4,z5,z279,z6]),(0,[z1,z2,z21,z3,z4,z5,z97]),(0,[z1,z2,z3,z4,z5,z702,z6]),(0,[z703,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z50,z5,z29]),(0,[z1,z89,z2,z3,z4,z5,z16]),(0,[z704,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z34,z6]),(0,[z1,z2,z3,z4,z5,z34,z282]),(0,[z1,z2,z3,z4,z5,z6,z705]),(0,[z1,z2,z3,z4,z5,z6,z706])],[(0,[z1,z2,z3,z179,z36,z4,z5]),(1,[z1,z2,z159,z4,z5,z6]),(0,[z1,z2,z21,z83,z3,z4,z5]),(0,[z1,z2,z3,z5,z43,z59,z6])],[(0,[z205,z1,z2,z76,z4,z5,z6]),(0,[z1,z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z66,z5,z29]),(0,[z1,z2,z35,z3,z4,z5,z16]),(1,[z1,z2,z3,z36,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z68,z707,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z5,z705]),(0,[z1,z2,z11,z5,z657,z6]),(0,[z1,z2,z91,z281,z5,z282])],[(0,[z1,z2,z708,z3,z4,z5]),(0,[z1,z2,z4,z5,z709,z6]),(0,[z1,z2,z3,z4,z710,z67])],[(0,[z1,z2,z143,z3,z4,z6]),(0,[z1,z2,z3,z4,z711,z5])],[(0,[z1,z2,z3,z712,z5,z6])],[(0,[z1,z163,z2,z3,z36,z4]),(0,[z26,z2,z665,z3,z4,z6]),(0,[z1,z2,z115,z4,z5,z282]),(0,[z1,z2,z3,z4,z5,z713]),(0,[z1,z2,z714,z3,z4,z5]),(0,[z1,z147,z620,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z715]),(0,[z1,z2,z3,z4,z716,z5]),(0,[z1,z2,z3,z4,z5,z717]),(0,[z1,z2,z3,z551,z4,z49])],[(0,[z1,z3,z4,z718,z5,z6])],[(0,[z1,z89,z21,z3,z140,z5])],[(1,[z707,z3,z4,z5,z6]),(0,[z1,z189,z3,z4,z97,z6]),(0,[z102,z2,z21,z3,z4,z113]),(0,[z1,z2,z382,z3,z4,z311])],[(0,[z109,z2,z179,z4,z5,z110]),(0,[z1,z2,z3,z719,z5,z6]),(0,[z1,z626,z3,z4,z5,z221]),(0,[z1,z2,z21,z3,z176,z5])],[(0,[z1,z2,z720,z4,z5,z6]),(0,[z1,z2,z433,z3,z94,z5]),(0,[z1,z2,z3,z36,z406,z5]),(0,[z1,z2,z3,z4,z5,z721]),(0,[z1,z2,z418,z3,z43,z6])],[(0,[z1,z2,z3,z722,z4,z5]),(0,[z1,z2,z83,z11,z5,z16]),(0,[z1,z2,z3,z36,z4,z723])],[(0,[z1,z2,z724,z4,z5,z6]),(0,[z1,z61,z314,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z725]),(0,[z1,z2,z3,z255,z5,z439]),(0,[z18,z1,z21,z19,z4,z5])],[(0,[z1,z2,z3,z726,z5,z6]),(0,[z158,z2,z3,z727,z5,z6]),(0,[z1,z2,z3,z728,z4,z5]),(0,[z1,z2,z21,z3,z5,z252])],[(0,[z1,z2,z270,z21,z3,z4]),(0,[z1,z2,z3,z4,z729,z6])],[(0,[z1,z2,z3,z36,z4,z329])]],
   [[(0,[z1,z189,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z106,z16]),(0,[z1,z2,z3,z730,z5,z6]),(0,[z1,z2,z21,z103,z4,z22]),(0,[z534,z2,z263,z3,z4,z5])],[(0,[z1,z731,z3,z4,z5,z6]),(0,[z1,z89,z2,z433,z3,z5]),(0,[z1,z2,z11,z4,z449,z6])],[(0,[z1,z2,z732,z4,z5,z6]),(0,[z155,z1,z92,z3,z4,z5])],[(0,[z1,z2,z733,z3,z4,z5]),(0,[z1,z2,z3,z117,z5,z16]),(0,[z1,z89,z2,z173,z5,z6])],[(0,[z1,z2,z21,z3,z4,z351]),(0,[z1,z2,z3,z4,z5,z734])],[(0,[z1,z2,z433,z3,z4,z5]),(0,[z1,z2,z3,z5,z735,z6])],[(0,[z1,z2,z3,z325,z43,z6])],[(0,[z1,z2,z3,z4,z736,z6]),(0,[z1,z2,z3,z4,z5,z737])],[(0,[z738,z2,z3,z4,z5,z6])],[(0,[z520,z2,z76,z4,z5,z6]),(0,[z170,z2,z3,z4,z5,z16]),(0,[z1,z2,z739,z3,z4,z5]),(0,[z1,z2,z3,z36,z181,z5])],[(0,[z1,z2,z740,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z741]),(0,[z1,z2,z742,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z252]),(0,[z1,z2,z177,z8,z4,z5])],[(0,[z1,z2,z143,z3,z4,z16]),(0,[z1,z2,z3,z4,z5,z743]),(0,[z2,z3,z4,z5,z744,z6])],[(0,[z1,z2,z745,z3,z4,z5]),(0,[z1,z2,z376,z209,z3,z5]),(0,[z1,z2,z3,z746,z4,z5])],[(0,[z1,z2,z3,z4,z5,z29]),(0,[z205,z2,z76,z387,z5,z6]),(0,[z1,z2,z316,z3,z4,z106])],[(0,[z659,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z747])],[(0,[z158,z2,z3,z50,z5,z16]),(0,[z2,z663,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z748]),(0,[z1,z2,z21,z3,z167,z5])]],
   [[(0,[z102,z2,z567,z3,z4,z6]),(0,[z578,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z242]),(0,[z1,z2,z91,z371,z4,z5]),(0,[z1,z2,z749,z3,z4,z5])],[(0,[z1,z2,z3,z4,z750,z6]),(0,[z1,z2,z411,z3,z36,z5]),(0,[z1,z2,z21,z751,z4,z5])],[(0,[z1,z752,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z176,z43])],[(0,[z1,z2,z3,z4,z753,z6]),(0,[z1,z2,z172,z4,z5,z16]),(0,[z1,z2,z21,z83,z11,z5])],[],[(0,[z45,z2,z263,z3,z4,z5]),(0,[z1,z2,z159,z4,z5,z6]),(0,[z109,z2,z179,z4,z5,z16]),(0,[z400,z1,z2,z3,z4,z130])],[(0,[z1,z2,z3,z4,z5,z754]),(0,[z1,z89,z3,z140,z135,z6]),(0,[z1,z2,z3,z4,z5,z755])],[(0,[z703,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z267])],[(0,[z1,z2,z3,z4,z756,z6])],[(0,[z1,z189,z2,z3,z4,z16]),(0,[z450,z2,z3,z98,z5,z6]),(0,[z1,z2,z120,z356,z5,z6])],[(0,[z1,z2,z757,z3,z4,z6]),(0,[z1,z174,z3,z203,z5,z29])],[],[(0,[z1,z2,z3,z4,z279,z6]),(0,[z1,z2,z361,z4,z5,z29])],[(0,[z1,z2,z3,z758,z5,z16])],[(0,[z1,z2,z3,z54,z4,z5]),(0,[z1,z314,z3,z356,z5,z6]),(0,[z2,z3,z4,z5,z759,z6]),(0,[z760,z2,z3,z4,z5,z6]),(0,[z1,z2,z761,z4,z5,z6])],[(0,[z1,z2,z3,z5,z298,z6])]],
   [[(0,[z1,z2,z3,z762,z4,z5]),(0,[z68,z40,z3,z4,z272,z6])],[],[(0,[z1,z2,z3,z4,z5,z763]),(0,[z1,z2,z21,z3,z235,z5])],[],[(0,[z1,z2,z425,z3,z4,z67]),(0,[z1,z2,z376,z46,z3,z5]),(0,[z1,z147,z3,z4,z5,z764]),(0,[z1,z2,z3,z4,z5,z765])],[(0,[z766,z2,z3,z4,z5,z6]),(0,[z1,z2,z83,z11,z5,z6]),(0,[z1,z2,z361,z21,z4,z5])],[(0,[z45,z139,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z759]),(0,[z1,z2,z3,z4,z723,z6])],[],[(0,[z1,z2,z3,z4,z767,z6]),(0,[z1,z2,z3,z4,z5,z768]),(0,[z1,z2,z21,z264,z3,z5]),(0,[z1,z2,z3,z769,z5,z6]),(0,[z1,z2,z21,z418,z3,z5])],[],[(0,[z1,z2,z770,z3,z4,z5]),(0,[z1,z2,z222,z83,z3,z5]),(0,[z1,z2,z3,z4,z5,z771])],[(0,[z1,z2,z772,z4,z5,z6]),(0,[z1,z2,z179,z117,z5,z6]),(0,[z1,z773,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z29,z774]),(0,[z1,z2,z21,z3,z5,z227]),(0,[z1,z2,z3,z4,z5,z775]),(0,[z1,z2,z776,z3,z4,z5])],[(0,[z139,z707,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z777,z6])],[(0,[z1,z2,z237,z36,z4,z5]),(0,[z1,z2,z172,z4,z5,z56]),(0,[z102,z2,z3,z356,z113,z6]),(0,[z1,z2,z778,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z779])],[(0,[z1,z2,z21,z237,z4,z5]),(0,[z1,z2,z3,z4,z5,z780]),(0,[z1,z2,z3,z5,z781,z6]),(0,[z1,z2,z3,z4,z5,z782]),(0,[z1,z2,z21,z3,z181,z5])],[(0,[z1,z2,z783,z4,z5,z6]),(0,[z45,z139,z3,z36,z4,z5])]],
   [[(0,[z2,z40,z263,z3,z4,z5]),(0,[z1,z2,z3,z784,z4,z5]),(0,[z2,z302,z3,z4,z5,z16])],[(0,[z1,z2,z3,z39,z5,z29]),(0,[z1,z2,z3,z4,z42,z29])],[(0,[z1,z2,z99,z371,z5,z6])],[(0,[z2,z3,z4,z5,z313,z16]),(0,[z1,z2,z3,z329,z59,z6]),(0,[z1,z2,z4,z5,z252,z74])],[(0,[z1,z2,z3,z4,z5,z785])],[(0,[z1,z2,z3,z4,z279,z16]),(0,[z1,z2,z64,z4,z65,z29]),(0,[z1,z2,z3,z5,z6,z786]),(0,[z1,z787,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z788])],[(0,[z1,z2,z3,z789,z4,z5]),(0,[z1,z2,z4,z5,z74,z29]),(0,[z2,z3,z4,z5,z29,z414]),(0,[z1,z2,z3,z790,z5,z6]),(1,[z1,z2,z3,z791,z6])],[(0,[z1,z41,z792,z4,z5,z6])],[(0,[z205,z2,z76,z4,z5,z6]),(0,[z1,z2,z3,z94,z4,z793]),(0,[z1,z2,z3,z5,z298,z16]),(0,[z1,z2,z3,z4,z5,z794]),(0,[z1,z2,z3,z795,z4,z5])],[(0,[z1,z2,z3,z4,z796,z6]),(0,[z1,z2,z76,z4,z329,z6]),(0,[z158,z2,z3,z50,z5,z6]),(0,[z1,z2,z797,z3,z356,z5]),(0,[z1,z2,z3,z36,z4,z729])],[(0,[z1,z2,z99,z316,z3,z5]),(0,[z1,z174,z2,z433,z3,z5]),(0,[z1,z2,z3,z4,z798,z5])],[(0,[z1,z2,z21,z3,z4,z5]),(0,[z68,z40,z3,z4,z69,z6]),(0,[z1,z2,z3,z4,z5,z799]),(0,[z1,z2,z3,z4,z800,z6]),(0,[z1,z2,z801,z3,z5,z6])],[(0,[z1,z2,z802,z3,z5,z6]),(0,[z1,z2,z3,z168,z4,z5]),(0,[z1,z2,z316,z3,z176,z5]),(0,[z1,z174,z2,z173,z5,z6]),(0,[z1,z2,z803,z4,z5,z6])],[(0,[z1,z2,z172,z4,z5,z6]),(0,[z1,z2,z3,z4,z804,z6]),(0,[z226,z2,z3,z4,z5,z16]),(0,[z1,z2,z83,z228,z5,z6]),(0,[z1,z2,z21,z3,z5,z53])],[(0,[z1,z2,z3,z4,z5,z805]),(0,[z1,z448,z120,z4,z5,z6])],[(0,[z45,z139,z3,z4,z5,z86]),(0,[z109,z2,z179,z4,z5,z6]),(0,[z1,z806,z3,z4,z5,z6]),(0,[z1,z2,z230,z3,z176,z5]),(0,[z1,z2,z3,z5,z807,z6]),(0,[z1,z33,z3,z4,z5,z213]),(0,[z1,z2,z3,z808,z4,z5]),(0,[z1,z88,z41,z4,z351,z6]),(0,[z1,z2,z36,z458,z4,z5])]],
   [[(0,[z366,z2,z3,z4,z5,z29])],[(0,[z1,z2,z143,z3,z36,z4]),(0,[z1,z2,z3,z248,z5,z150]),(0,[z1,z2,z3,z4,z5,z809])],[(0,[z1,z2,z3,z4,z5,z810]),(0,[z1,z811,z3,z4,z5,z6]),(0,[z1,z314,z3,z36,z4,z5]),(0,[z18,z1,z376,z19,z5,z6]),(0,[z1,z2,z83,z3,z5,z267]),(0,[z1,z2,z3,z181,z5,z38])],[(0,[z1,z2,z87,z36,z4,z5]),(0,[z1,z314,z3,z4,z43,z6]),(0,[z679,z2,z3,z4,z51,z6]),(0,[z1,z2,z35,z3,z43,z29])],[(0,[z1,z2,z128,z4,z5,z29]),(0,[z1,z2,z812,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z813]),(0,[z1,z2,z264,z3,z5,z814])],[],[(0,[z93,z2,z3,z98,z5,z29]),(0,[z1,z2,z3,z4,z5,z815]),(0,[z1,z2,z3,z4,z5,z816])],[(0,[z1,z163,z2,z21,z3,z4]),(0,[z1,z2,z817,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z818]),(0,[z1,z2,z3,z4,z5,z819]),(0,[z1,z2,z3,z4,z5,z820]),(0,[z1,z2,z821,z4,z5,z6]),(0,[z1,z2,z3,z758,z5,z6])],[(0,[z158,z2,z230,z3,z50,z5]),(0,[z1,z2,z3,z4,z5,z822]),(0,[z1,z2,z3,z248,z27,z6])],[(0,[z1,z2,z3,z117,z5,z259])],[(0,[z1,z2,z3,z4,z5,z823])],[(0,[z1,z2,z824,z4,z5,z6])],[],[(0,[z1,z2,z128,z36,z4,z5]),(0,[z32,z1,z189,z3,z4,z6]),(0,[z389,z1,z3,z4,z52,z6]),(0,[z1,z2,z825,z376,z3,z5])],[(0,[z93,z2,z159,z98,z5,z6]),(0,[z1,z2,z826,z3,z4,z5]),(0,[z1,z2,z827,z4,z5,z6])],[(0,[z1,z189,z2,z3,z36,z4]),(0,[z1,z33,z202,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z828])]],
   [[(0,[z1,z2,z829,z4,z5,z6]),(0,[z1,z830,z3,z4,z5,z6]),(0,[z1,z2,z831,z4,z5,z6]),(1,[z2,z3,z4,z5,z759]),(0,[z1,z2,z3,z551,z181,z5])],[(0,[z205,z2,z76,z4,z5,z16]),(0,[z1,z2,z376,z76,z5,z6]),(0,[z474,z2,z3,z4,z5,z29])],[(0,[z1,z2,z3,z832,z4,z5]),(0,[z604,z1,z19,z4,z5,z6]),(0,[z1,z2,z582,z11,z5,z6]),(0,[z1,z2,z3,z4,z5,z171]),(0,[z102,z448,z3,z4,z113,z6]),(0,[z1,z2,z833,z3,z4,z5])],[(0,[z1,z2,z3,z4,z834,z6]),(0,[z82,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z176,z27,z29]),(0,[z1,z2,z3,z5,z835,z6])],[(0,[z45,z139,z21,z3,z4,z5]),(0,[z1,z2,z3,z836,z4,z5]),(0,[z1,z2,z3,z4,z135,z29]),(0,[z1,z2,z3,z181,z5,z29]),(0,[z837,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z838]),(0,[z839,z2,z3,z4,z5,z6]),(0,[z840,z2,z21,z3,z4,z5])],[(0,[z109,z2,z179,z4,z5,z232]),(0,[z1,z2,z841,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z842]),(0,[z1,z436,z3,z4,z5,z34])],[(0,[z1,z2,z3,z4,z5,z440])],[(0,[z1,z2,z21,z458,z4,z5])],[(0,[z1,z2,z433,z3,z5,z31]),(0,[z1,z2,z239,z3,z4,z5]),(0,[z1,z2,z492,z4,z188,z5])],[(0,[z1,z2,z159,z4,z5,z169]),(0,[z1,z2,z173,z71,z4,z5]),(0,[z1,z2,z3,z5,z791,z6])],[(0,[z1,z2,z3,z4,z272,z16]),(0,[z1,z2,z843,z4,z5,z6]),(0,[z1,z2,z3,z4,z844,z6])],[(0,[z1,z2,z4,z5,z845,z6])],[(0,[z1,z2,z3,z4,z69,z6]),(0,[z1,z2,z3,z4,z5,z846])],[(0,[z1,z2,z3,z847,z5,z6]),(0,[z1,z2,z3,z848,z5,z6]),(0,[z1,z2,z849,z4,z5,z6]),(0,[z1,z2,z3,z850,z4,z5]),(0,[z2,z3,z4,z5,z29,z506]),(0,[z1,z2,z3,z4,z5,z851]),(0,[z1,z2,z3,z852,z4,z5]),(0,[z1,z2,z3,z176,z791,z6]),(0,[z1,z2,z3,z4,z5,z710])],[(0,[z1,z2,z270,z11,z4,z6]),(0,[z1,z853,z3,z4,z5,z6]),(0,[z1,z2,z3,z255,z98,z5]),(0,[z1,z2,z3,z4,z854,z5]),(0,[z1,z2,z855,z4,z5,z29]),(0,[z1,z2,z21,z3,z5,z594]),(0,[z1,z136,z3,z44,z4,z5])],[(0,[z1,z2,z3,z4,z5,z856])]],
   [[(0,[z1,z2,z3,z248,z5,z16]),(0,[z1,z2,z3,z4,z5,z857])],[(0,[z1,z2,z3,z255,z50,z5]),(0,[z32,z1,z3,z4,z52,z29]),(0,[z1,z2,z3,z5,z6,z858])],[(0,[z1,z2,z3,z4,z859,z6]),(0,[z1,z2,z361,z4,z97,z6])],[(0,[z93,z2,z3,z98,z106,z6]),(0,[z1,z2,z21,z120,z4,z5]),(0,[z1,z2,z3,z4,z5,z860]),(0,[z1,z861,z2,z3,z4,z5])],[(0,[z32,z1,z3,z36,z4,z52]),(0,[z1,z2,z3,z4,z5,z468])],[(0,[z1,z2,z3,z4,z862,z6]),(0,[z1,z294,z3,z4,z97,z6]),(0,[z102,z2,z3,z4,z413,z6]),(0,[z1,z2,z376,z3,z863,z6]),(0,[z1,z2,z864,z3,z5,z6]),(0,[z1,z2,z328,z3,z36,z5])],[(0,[z1,z2,z3,z5,z865,z6]),(0,[z1,z2,z3,z866,z4,z5]),(0,[z1,z2,z104,z4,z5,z58]),(0,[z1,z2,z867,z4,z5,z6])],[(0,[z1,z2,z237,z4,z5,z29]),(0,[z1,z314,z21,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z286]),(1,[z1,z3,z868,z5,z6]),(0,[z1,z2,z3,z868,z5,z6]),(0,[z1,z2,z3,z4,z5,z869]),(0,[z1,z174,z3,z203,z5,z267]),(0,[z1,z3,z4,z5,z34,z764]),(0,[z1,z2,z21,z3,z4,z329]),(0,[z1,z2,z3,z4,z5,z870]),(0,[z1,z2,z3,z5,z6,z871])],[(0,[z1,z2,z3,z5,z252,z298])],[(0,[z1,z314,z172,z4,z5,z6]),(0,[z1,z2,z872,z3,z248,z5]),(0,[z1,z2,z99,z48,z5,z6]),(0,[z1,z2,z21,z3,z5,z407])],[(0,[z1,z2,z37,z4,z5,z282])],[(0,[z1,z2,z3,z4,z272,z75]),(0,[z1,z189,z314,z3,z4,z6]),(0,[z1,z2,z873,z3,z5,z6]),(0,[z1,z2,z3,z4,z874,z6])],[(0,[z1,z2,z875,z3,z4,z5]),(0,[z1,z2,z3,z36,z276,z5])],[(0,[z1,z2,z3,z4,z5,z876]),(0,[z1,z2,z877,z3,z4,z5])],[(0,[z1,z2,z3,z4,z6,z878]),(0,[z1,z2,z3,z4,z5,z879]),(0,[z1,z2,z103,z4,z612,z6]),(0,[z1,z3,z4,z5,z880,z6]),(0,[z1,z2,z173,z98,z5,z6]),(0,[z1,z2,z3,z881,z5,z6]),(0,[z1,z2,z3,z4,z330,z5])],[(0,[z1,z2,z3,z882,z4,z5]),(0,[z1,z2,z3,z5,z6,z493]),(0,[z1,z3,z4,z883,z5,z6]),(0,[z1,z2,z263,z3,z5,z43])]],
   [[(0,[z1,z2,z3,z4,z5,z884]),(1,[z1,z3,z4,z718,z6]),(0,[z1,z147,z92,z3,z4,z5]),(0,[z1,z2,z21,z3,z5,z641]),(0,[z1,z2,z3,z4,z5,z885])],[(0,[z1,z2,z270,z3,z4,z29]),(0,[z1,z2,z3,z4,z5,z886])],[(0,[z1,z2,z46,z3,z4,z5])],[(0,[z1,z2,z887,z3,z4,z5]),(0,[z1,z2,z4,z5,z6,z888])],[(0,[z1,z2,z3,z4,z5,z889]),(0,[z85,z2,z3,z50,z5,z6]),(0,[z1,z2,z11,z186,z5,z6]),(0,[z1,z2,z21,z3,z442,z5])],[(0,[z1,z2,z3,z4,z69,z16]),(0,[z1,z2,z3,z890,z387,z5]),(0,[z1,z88,z41,z4,z5,z6]),(0,[z1,z2,z3,z4,z891,z6]),(0,[z1,z2,z35,z3,z252,z43])],[(0,[z1,z2,z21,z3,z319,z5]),(0,[z1,z2,z99,z433,z3,z5]),(0,[z18,z1,z46,z19,z4,z5])],[(0,[z1,z2,z3,z4,z5,z892]),(0,[z1,z2,z120,z4,z5,z29]),(1,[z1,z2,z4,z893,z6]),(0,[z1,z2,z3,z66,z298,z38])],[(0,[z102,z2,z172,z4,z113,z6])],[(0,[z1,z2,z3,z36,z4,z69]),(0,[z205,z2,z849,z4,z5,z6]),(0,[z1,z2,z64,z21,z4,z65]),(0,[z1,z2,z64,z36,z4,z65])],[(0,[z1,z894,z3,z4,z5,z6]),(0,[z1,z2,z3,z248,z5,z56]),(0,[z1,z2,z21,z3,z65,z43]),(0,[z1,z2,z103,z4,z893,z6]),(0,[z1,z2,z281,z194,z3,z5])],[(0,[z1,z2,z3,z4,z5,z895])],[(0,[z1,z896,z3,z4,z5,z6]),(0,[z1,z314,z3,z4,z5,z29]),(0,[z1,z33,z3,z44,z4,z5]),(0,[z1,z2,z194,z4,z5,z58]),(0,[z1,z2,z194,z4,z5,z888]),(0,[z1,z2,z21,z3,z278,z5])],[(0,[z1,z2,z87,z4,z5,z29])],[(0,[z1,z2,z316,z3,z4,z5]),(0,[z1,z2,z3,z4,z897,z6]),(0,[z1,z2,z3,z4,z5,z898]),(0,[z1,z2,z899,z3,z4,z5]),(0,[z1,z174,z535,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z900]),(0,[z1,z2,z21,z901,z4,z5])],[(0,[z2,z3,z727,z50,z5,z6]),(0,[z1,z2,z21,z3,z5,z134]),(0,[z1,z2,z3,z4,z351,z6]),(0,[z1,z2,z902,z3,z4,z5]),(0,[z1,z2,z156,z3,z4,z67])]],
   [[(0,[z1,z2,z3,z39,z69,z6]),(0,[z1,z2,z120,z36,z4,z5]),(0,[z1,z2,z3,z4,z793,z29]),(0,[z1,z2,z21,z3,z5,z293])],[(0,[z68,z163,z40,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z903]),(0,[z1,z2,z230,z3,z4,z5]),(0,[z1,z2,z120,z4,z43,z6]),(0,[z1,z2,z376,z3,z5,z6]),(0,[z1,z2,z904,z4,z5,z6])],[(0,[z1,z2,z21,z3,z525,z5]),(0,[z1,z2,z99,z165,z218,z6])],[(0,[z1,z2,z492,z281,z3,z5]),(0,[z1,z2,z4,z5,z58,z888])],[(0,[z1,z2,z3,z4,z272,z6]),(0,[z2,z3,z4,z5,z16,z29]),(0,[z18,z1,z19,z36,z4,z5]),(0,[z1,z2,z905,z3,z4,z5]),(1,[z1,z2,z21,z3,z329]),(0,[z1,z2,z21,z281,z3,z5])],[(0,[z906,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z907,z6])],[(0,[z1,z2,z3,z4,z69,z75]),(0,[z1,z2,z103,z120,z4,z6])],[(0,[z1,z89,z458,z140,z5,z6])],[(0,[z158,z2,z3,z54,z4,z5]),(0,[z1,z2,z361,z98,z5,z6])],[(0,[z1,z2,z3,z908,z5,z6]),(0,[z32,z1,z21,z3,z4,z52])],[(0,[z1,z2,z3,z387,z5,z6]),(0,[z1,z2,z3,z248,z5,z6])],[(0,[z45,z707,z3,z4,z5,z6]),(0,[z1,z2,z3,z36,z387,z5]),(0,[z1,z2,z3,z36,z4,z279]),(0,[z1,z448,z3,z356,z5,z6]),(0,[z102,z2,z3,z4,z113,z29]),(0,[z1,z2,z909,z3,z4,z5]),(1,[z1,z2,z361,z21,z5])],[(0,[z2,z3,z4,z5,z910,z6]),(0,[z1,z2,z911,z3,z4,z5]),(0,[z100,z2,z3,z54,z4,z5]),(0,[z1,z2,z99,z21,z83,z5]),(0,[z1,z2,z99,z647,z5,z6])],[(0,[z1,z2,z3,z4,z5,z912]),(0,[z1,z2,z3,z4,z5,z913]),(0,[z1,z914,z3,z4,z5,z6]),(0,[z1,z2,z103,z36,z4,z22])],[(0,[z1,z692,z2,z21,z3,z5]),(0,[z1,z2,z264,z3,z5,z29]),(0,[z1,z2,z281,z3,z5,z29]),(0,[z160,z2,z3,z4,z5,z29]),(1,[z1,z792,z4,z5,z6]),(0,[z1,z2,z792,z4,z5,z6]),(0,[z1,z2,z915,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z916]),(0,[z1,z2,z21,z3,z5,z31])],[(0,[z1,z2,z3,z117,z917,z6]),(0,[z704,z2,z76,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z822,z279]),(0,[z1,z2,z83,z11,z5,z301])],[(0,[z1,z2,z918,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z919]),(0,[z1,z678,z3,z4,z52,z6])],[(0,[z1,z2,z3,z920,z4,z5]),(0,[z1,z2,z3,z4,z5,z921])],[(0,[z1,z2,z128,z4,z69,z6])],[(0,[z68,z40,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z922]),(0,[z343,z2,z3,z4,z5,z29]),(0,[z100,z2,z3,z4,z5,z759]),(0,[z1,z88,z190,z4,z5,z6]),(0,[z1,z3,z4,z5,z764,z221]),(0,[z1,z2,z21,z3,z176,z27]),(0,[z1,z2,z21,z3,z176,z537])],[(0,[z1,z2,z3,z4,z5,z923]),(0,[z1,z2,z3,z4,z5,z924]),(0,[z1,z2,z91,z5,z493,z282])],[(0,[z1,z2,z3,z362,z5,z29]),(0,[z1,z2,z3,z98,z329,z6]),(0,[z1,z2,z3,z4,z925,z6]),(0,[z1,z2,z560,z4,z22,z6])],[(0,[z205,z2,z76,z4,z5,z259]),(0,[z93,z2,z3,z94,z98,z5]),(0,[z28,z2,z3,z4,z5,z759])],[(0,[z1,z2,z3,z4,z5,z926]),(0,[z1,z2,z3,z4,z5,z927]),(0,[z93,z2,z3,z98,z279,z6]),(0,[z1,z2,z3,z4,z351,z16]),(0,[z1,z2,z3,z4,z5,z928])],[(0,[z1,z2,z3,z4,z5,z929]),(0,[z1,z2,z3,z4,z930,z6]),(0,[z1,z2,z35,z239,z3,z43])],[(0,[z26,z2,z3,z4,z51,z29]),(0,[z1,z2,z376,z3,z5,z16]),(0,[z1,z2,z3,z4,z5,z931]),(0,[z932,z2,z21,z3,z4,z5])],[(0,[z1,z2,z237,z4,z272,z6]),(0,[z1,z2,z3,z933,z4,z5]),(0,[z1,z81,z41,z4,z5,z6])],[(0,[z1,z2,z934,z3,z4,z5])],[(0,[z2,z3,z4,z5,z16,z759]),(0,[z1,z2,z21,z3,z186,z5]),(0,[z1,z2,z935,z3,z4,z5]),(0,[z1,z2,z21,z3,z4,z936])],[(0,[z1,z2,z21,z3,z4,z69]),(0,[z1,z61,z3,z4,z97,z29]),(0,[z1,z2,z3,z5,z16,z786])],[(0,[z1,z2,z3,z4,z5,z937])]],
   [[(0,[z1,z2,z3,z4,z272,z258]),(0,[z1,z2,z3,z4,z5,z938]),(0,[z1,z2,z3,z939,z5,z6])],[(0,[z1,z2,z3,z4,z940,z5]),(0,[z1,z2,z3,z5,z941,z43])],[(0,[z1,z189,z2,z21,z3,z4]),(0,[z1,z2,z3,z4,z942,z6]),(0,[z1,z2,z3,z36,z248,z5]),(0,[z1,z2,z943,z4,z5,z6]),(0,[z1,z2,z3,z255,z5,z59]),(0,[z1,z2,z46,z264,z3,z5])],[(0,[z1,z2,z3,z4,z5,z944]),(0,[z1,z2,z3,z4,z5,z945]),(0,[z1,z2,z3,z387,z5,z16]),(0,[z2,z76,z849,z4,z5,z6]),(0,[z474,z2,z76,z4,z5,z6])],[],[],[(0,[z1,z2,z3,z4,z946,z6]),(0,[z1,z455,z3,z4,z5,z221]),(0,[z1,z2,z3,z4,z5,z947])],[(0,[z1,z2,z3,z948,z4,z5]),(0,[z32,z1,z3,z4,z718,z6]),(0,[z1,z2,z3,z4,z5,z949])],[(0,[z1,z2,z3,z39,z272,z6]),(0,[z1,z2,z156,z3,z4,z260]),(0,[z1,z2,z950,z3,z5,z6]),(0,[z1,z2,z3,z36,z4,z449])],[(0,[z1,z2,z159,z50,z5,z6]),(0,[z1,z2,z951,z3,z4,z5]),(0,[z1,z2,z3,z5,z952,z6]),(0,[z1,z953,z2,z3,z4,z6])],[(0,[z1,z2,z3,z954,z4,z5]),(0,[z1,z2,z103,z4,z22,z29]),(0,[z1,z2,z3,z94,z5,z494]),(0,[z1,z2,z173,z4,z5,z6]),(0,[z1,z2,z3,z4,z955,z6])],[(0,[z1,z2,z956,z3,z39,z5]),(0,[z1,z2,z957,z3,z4,z5])],[(0,[z1,z2,z3,z4,z958,z6]),(0,[z1,z2,z3,z4,z5,z959]),(0,[z2,z3,z4,z5,z588,z16]),(0,[z1,z2,z3,z4,z5,z960])],[(0,[z1,z2,z3,z4,z5,z961]),(0,[z68,z40,z3,z4,z5,z16]),(0,[z1,z3,z4,z5,z764,z6]),(0,[z1,z3,z4,z962,z5,z6]),(0,[z1,z2,z21,z3,z4,z963])],[(0,[z1,z2,z3,z36,z4,z272]),(0,[z707,z40,z3,z4,z5,z6]),(0,[z1,z2,z964,z4,z5,z6]),(0,[z1,z651,z3,z203,z5,z6]),(0,[z1,z2,z3,z965,z5,z6]),(0,[z1,z2,z966,z165,z5,z6])],[(0,[z1,z2,z3,z4,z5,z150]),(0,[z1,z2,z3,z36,z356,z5]),(0,[z1,z2,z3,z4,z925,z16]),(0,[z1,z2,z967,z3,z4,z5]),(0,[z1,z2,z21,z3,z4,z968])]],
   [[(0,[z1,z2,z21,z3,z387,z5]),(0,[z1,z2,z21,z3,z4,z279])],[(0,[z1,z2,z969,z3,z4,z6]),(0,[z1,z2,z316,z3,z5,z227]),(0,[z2,z3,z4,z5,z970,z6]),(0,[z1,z2,z4,z5,z971,z6]),(0,[z1,z2,z21,z3,z4,z925])],[(0,[z1,z2,z3,z4,z5,z23]),(0,[z1,z2,z3,z4,z5,z110]),(0,[z1,z2,z3,z176,z106,z6]),(1,[z1,z3,z4,z5,z764]),(0,[z1,z2,z3,z4,z5,z764]),(0,[z1,z2,z361,z4,z22,z6])],[(0,[z1,z2,z3,z4,z5,z972]),(0,[z1,z2,z3,z4,z718,z6]),(0,[z1,z2,z3,z5,z493,z301])],[(0,[z1,z2,z3,z973,z5,z6]),(0,[z1,z2,z974,z3,z4,z5]),(0,[z1,z2,z975,z4,z5,z6]),(0,[z1,z2,z3,z4,z449,z29]),(0,[z1,z2,z3,z4,z5,z976])],[(0,[z158,z2,z3,z50,z5,z207]),(0,[z1,z2,z3,z977,z5,z6]),(0,[z13,z2,z316,z3,z4,z5])],[(0,[z1,z2,z237,z4,z69,z6]),(0,[z1,z2,z4,z5,z6,z978])],[(0,[z1,z2,z979,z3,z4,z5]),(0,[z603,z2,z3,z4,z5,z29]),(0,[z1,z2,z21,z3,z5,z311])],[(0,[z68,z40,z3,z39,z5,z6]),(0,[z1,z2,z3,z4,z5,z980])],[(0,[z1,z2,z21,z3,z176,z130])],[(0,[z1,z981,z3,z4,z5,z6])],[(0,[z1,z2,z128,z4,z272,z6]),(0,[z1,z2,z3,z4,z69,z258]),(0,[z1,z2,z3,z4,z5,z982])],[(0,[z1,z2,z99,z119,z5,z6])],[(0,[z474,z2,z3,z98,z5,z6]),(0,[z1,z2,z21,z3,z132,z5])],[(0,[z68,z40,z3,z4,z5,z75]),(0,[z1,z3,z4,z5,z6,z983]),(0,[z18,z1,z19,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z984]),(0,[z1,z2,z4,z22,z893,z6])],[(0,[z1,z2,z3,z4,z5,z985]),(0,[z1,z2,z3,z4,z946,z16]),(0,[z531,z2,z3,z54,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z986]),(0,[z1,z2,z3,z4,z6,z710])],[(0,[z1,z2,z3,z987,z5,z6]),(0,[z1,z2,z988,z4,z5,z6]),(0,[z2,z263,z3,z98,z4,z5]),(0,[z28,z2,z3,z4,z5,z29]),(0,[z18,z1,z19,z4,z5,z242]),(0,[z1,z2,z99,z21,z22,z5]),(0,[z1,z2,z4,z5,z893,z6])],[(0,[z1,z2,z87,z4,z5,z171])],[(0,[z1,z2,z173,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z989])],[(0,[z1,z2,z3,z4,z5,z990]),(0,[z1,z2,z3,z4,z5,z991]),(0,[z1,z2,z3,z992,z4,z5]),(0,[z2,z3,z4,z5,z993,z6]),(0,[z1,z2,z99,z966,z5,z6])],[(0,[z102,z2,z3,z248,z113,z6]),(0,[z1,z2,z3,z4,z218,z29]),(0,[z1,z2,z104,z4,z5,z574]),(0,[z1,z2,z3,z4,z5,z994]),(0,[z1,z2,z995,z4,z5,z6])],[(0,[z1,z567,z3,z4,z97,z6]),(0,[z1,z996,z21,z3,z4,z5])],[(0,[z1,z2,z21,z3,z248,z5]),(0,[z1,z2,z3,z4,z997,z6]),(0,[z1,z2,z3,z4,z5,z998]),(0,[z1,z2,z3,z4,z5,z999]),(0,[z1,z2,z3,z176,z36,z27])],[(0,[z1,z2,z99,z157,z5,z6]),(0,[z1,z2,z99,z21,z76,z5])],[(0,[z1,z2,z1000,z3,z5,z29]),(0,[z1,z2,z3,z1001,z4,z5]),(0,[z1,z2,z99,z21,z8,z5])],[(1,[z2,z849,z4,z5,z6]),(0,[z1,z538,z3,z140,z5,z6]),(0,[z2,z3,z4,z5,z649,z16]),(0,[z1,z2,z528,z21,z3,z5])],[(0,[z68,z40,z128,z4,z5,z6]),(0,[z1,z2,z1002,z4,z5,z6]),(0,[z45,z139,z3,z4,z5,z23]),(0,[z1,z2,z99,z21,z179,z5]),(0,[z1,z2,z3,z4,z106,z1003]),(0,[z1,z2,z3,z1004,z4,z5]),(0,[z1,z2,z64,z4,z893,z6]),(0,[z1,z2,z21,z3,z5,z475])],[(0,[z1,z2,z453,z4,z5,z296])],[(0,[z1,z2,z3,z36,z362,z5]),(0,[z1,z314,z103,z3,z4,z6]),(0,[z1,z2,z21,z3,z4,z449]),(0,[z1,z2,z99,z550,z5,z6])],[(0,[z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z1005,z5,z6]),(0,[z93,z2,z3,z98,z5,z171]),(0,[z1,z2,z3,z4,z200,z478])],[(0,[z1,z2,z3,z4,z5,z1006]),(0,[z1,z2,z1007,z3,z4,z5]),(0,[z102,z1,z2,z21,z3,z43]),(0,[z1,z2,z3,z4,z1008,z6]),(0,[z1,z2,z264,z3,z5,z743]),(0,[z1,z2,z3,z5,z6,z1009]),(0,[z1,z2,z3,z1010,z5,z6]),(0,[z1,z2,z3,z1011,z5,z6])]],
   [[(0,[z1,z2,z179,z4,z329,z6])],[(0,[z1,z2,z1012,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1013]),(0,[z1,z2,z3,z4,z5,z1014]),(0,[z1,z2,z3,z36,z5,z986])],[(0,[z1,z3,z868,z140,z5,z6]),(0,[z1,z2,z3,z4,z329,z6]),(0,[z1015,z2,z21,z3,z4,z5])],[(0,[z1,z2,z21,z3,z4,z272]),(0,[z1,z2,z3,z4,z5,z1016]),(0,[z1,z2,z263,z3,z176,z5])],[(0,[z1,z2,z21,z3,z356,z5]),(0,[z1,z1017,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z1018,z6]),(0,[z1,z2,z3,z4,z5,z1019]),(0,[z1,z2,z1020,z4,z5,z6]),(0,[z1,z310,z3,z4,z5,z34]),(0,[z1,z2,z35,z3,z36,z43])],[(0,[z1,z2,z361,z21,z5,z6])],[(0,[z1,z2,z103,z405,z4,z6]),(0,[z1,z2,z91,z281,z3,z5])],[(0,[z1,z2,z3,z4,z5,z1021]),(0,[z1,z78,z3,z4,z5,z60]),(0,[z1,z2,z3,z4,z16,z878])],[(0,[z1,z2,z433,z83,z3,z5]),(0,[z1,z2,z3,z5,z6,z1022])],[(0,[z1,z2,z1023,z4,z5,z6]),(0,[z1,z2,z3,z4,z1024,z6]),(0,[z1,z2,z433,z3,z98,z5]),(0,[z1,z2,z3,z1025,z4,z5]),(0,[z1,z2,z3,z4,z42,z6])],[(0,[z1,z2,z3,z4,z5,z1026]),(0,[z1,z2,z1027,z3,z5,z29]),(0,[z1,z2,z3,z1028,z5,z6])],[(0,[z1,z2,z3,z4,z1029,z6]),(0,[z1,z314,z3,z4,z5,z150])],[(0,[z68,z189,z40,z3,z4,z6]),(0,[z1,z2,z433,z3,z50,z5]),(0,[z1,z2,z1030,z3,z4,z5]),(0,[z1,z2,z3,z4,z863,z6]),(0,[z1,z2,z1031,z3,z4,z5])],[(0,[z1,z2,z3,z4,z6,z1032]),(0,[z1,z2,z1033,z4,z5,z6]),(0,[z1,z2,z3,z1034,z5,z6]),(0,[z1,z2,z3,z4,z1035,z6]),(0,[z1,z2,z3,z94,z4,z106]),(0,[z1,z2,z361,z4,z5,z16]),(0,[z1,z2,z64,z4,z65,z6])],[(0,[z1,z2,z3,z4,z5,z70]),(0,[z1,z2,z4,z5,z74,z6]),(0,[z1,z2,z36,z4,z5,z74]),(0,[z1036,z2,z21,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z75]),(0,[z1,z2,z99,z165,z5,z29]),(0,[z1,z2,z433,z3,z5,z466])]],
   [[(0,[z1,z2,z316,z3,z4,z936]),(0,[z1,z88,z792,z4,z5,z6]),(0,[z1,z2,z3,z36,z668,z5])],[(0,[z1,z2,z3,z4,z910,z6]),(0,[z32,z1,z477,z3,z4,z6]),(0,[z1,z2,z361,z4,z329,z6]),(0,[z1,z2,z3,z27,z791,z6])],[(0,[z1,z2,z3,z1037,z5,z6]),(0,[z1,z2,z3,z1038,z5,z6])],[(0,[z1,z2,z1039,z3,z4,z5]),(0,[z1,z2,z21,z582,z3,z5])],[(0,[z1,z89,z3,z140,z5,z29]),(0,[z1,z2,z99,z222,z3,z5]),(0,[z1,z2,z83,z36,z11,z5]),(0,[z1,z1040,z21,z3,z4,z5])],[(0,[z1,z2,z3,z362,z69,z6]),(0,[z1,z2,z30,z3,z4,z260])],[(0,[z1,z2,z3,z4,z1041,z6]),(0,[z1,z2,z3,z1042,z5,z6]),(0,[z1,z2,z4,z893,z65,z6])],[(0,[z1,z2,z1043,z3,z4,z5])],[(0,[z1,z2,z3,z36,z39,z5]),(0,[z1,z2,z1044,z4,z5,z6]),(0,[z472,z2,z179,z4,z5,z6]),(0,[z1,z1045,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z56]),(0,[z1,z88,z2,z99,z21,z5])],[(0,[z1,z2,z3,z387,z5,z259]),(0,[z1,z2,z3,z117,z5,z481]),(0,[z1,z448,z3,z4,z5,z29]),(0,[z1,z2,z3,z850,z248,z5]),(0,[z1,z2,z99,z64,z21,z5]),(0,[z1,z2,z327,z3,z4,z537])],[(0,[z102,z2,z3,z4,z113,z150]),(0,[z1,z2,z376,z3,z36,z5])],[(0,[z2,z849,z179,z4,z5,z6]),(0,[z1,z2,z3,z4,z1046,z6]),(0,[z1,z2,z21,z143,z3,z4]),(0,[z334,z2,z3,z98,z5,z6]),(0,[z1,z2,z3,z4,z66,z478]),(0,[z1,z2,z3,z4,z329,z16])],[(0,[z2,z3,z94,z54,z4,z5]),(0,[z26,z2,z3,z4,z674,z6]),(0,[z1,z2,z3,z4,z5,z1047]),(0,[z1,z2,z35,z3,z791,z6])],[(0,[z1,z1048,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1049]),(0,[z1,z2,z1050,z3,z4,z5]),(0,[z1,z89,z71,z3,z140,z5])],[(0,[z68,z40,z237,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1051]),(0,[z1,z2,z1052,z3,z4,z6]),(0,[z205,z2,z263,z3,z4,z5]),(0,[z1,z2,z71,z3,z4,z5])],[(0,[z1,z2,z3,z1053,z5,z6])]],
   [[(0,[z1,z2,z159,z36,z4,z5]),(0,[z2,z3,z98,z727,z5,z6]),(0,[z1,z2,z21,z3,z97,z43])],[(0,[z1,z2,z3,z5,z1054,z16]),(0,[z1,z61,z3,z36,z4,z97])],[(0,[z1,z448,z3,z36,z4,z5]),(0,[z1,z2,z3,z4,z42,z16]),(0,[z1,z2,z3,z4,z5,z339])],[(0,[z68,z40,z3,z4,z5,z258]),(0,[z1,z2,z316,z3,z4,z279]),(0,[z1,z2,z115,z4,z5,z357]),(0,[z1,z2,z614,z3,z43,z6]),(0,[z1,z2,z21,z3,z96,z5]),(0,[z1,z2,z3,z4,z5,z1055])],[(0,[z1,z2,z3,z1056,z39,z5]),(0,[z1,z2,z120,z248,z5,z6]),(0,[z1,z2,z172,z356,z5,z6])],[(0,[z1057,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1058]),(0,[z1,z2,z64,z4,z65,z16]),(0,[z1,z2,z21,z3,z5,z986])],[(0,[z1,z2,z3,z4,z5,z1059]),(0,[z1,z2,z4,z5,z74,z16]),(0,[z1,z2,z3,z4,z5,z1060]),(0,[z1,z2,z1061,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z33,z3,z4,z5,z764])],[(0,[z343,z40,z3,z4,z5,z6]),(0,[z1,z314,z3,z248,z5,z6]),(0,[z1,z88,z2,z376,z5,z6]),(0,[z1,z2,z1062,z3,z5,z6])],[(0,[z1,z2,z3,z1063,z5,z6]),(0,[z1,z2,z3,z4,z5,z1064])],[(0,[z1,z2,z21,z172,z4,z5]),(0,[z1,z2,z3,z4,z1065,z6]),(0,[z1,z2,z3,z72,z27,z6]),(0,[z1,z2,z3,z4,z5,z1066]),(0,[z1,z2,z83,z5,z6,z166]),(0,[z1,z1067,z3,z4,z5,z6])],[(0,[z1,z2,z3,z181,z5,z6])],[(0,[z1,z2,z3,z1068,z5,z6]),(0,[z1,z163,z2,z3,z4,z29]),(0,[z32,z1,z314,z3,z4,z6])],[(0,[z1,z2,z21,z3,z512,z5])],[(0,[z1,z2,z3,z117,z5,z29]),(0,[z1,z2,z1069,z3,z4,z5]),(0,[z1,z2,z1070,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1071]),(0,[z1,z2,z3,z36,z4,z793])],[(0,[z1,z2,z3,z1072,z4,z5]),(0,[z1,z2,z3,z4,z5,z1073]),(0,[z562,z2,z3,z4,z5,z29]),(0,[z521,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z1074,z6]),(0,[z1,z2,z3,z4,z5,z1075])],[(0,[z1,z2,z3,z1076,z5,z6]),(0,[z1,z2,z1077,z3,z4,z5]),(0,[z1,z2,z3,z4,z1078,z6]),(0,[z1,z2,z3,z4,z5,z1079]),(0,[z1,z2,z3,z4,z5,z1080])],[(0,[z1,z2,z3,z4,z5,z1081]),(0,[z122,z2,z3,z4,z5,z29])],[(0,[z1,z2,z740,z3,z362,z5]),(0,[z1,z2,z3,z4,z5,z1082]),(0,[z1,z2,z35,z3,z43,z16])],[(0,[z1,z2,z3,z117,z753,z6]),(0,[z1,z2,z3,z4,z5,z1083]),(0,[z13,z2,z3,z4,z5,z16]),(0,[z1,z88,z21,z41,z4,z5]),(0,[z1,z174,z3,z203,z5,z6]),(0,[z1,z89,z3,z868,z5,z6]),(0,[z1,z2,z3,z966,z5,z6]),(0,[z1,z2,z21,z3,z48,z5])],[(0,[z1,z2,z855,z4,z5,z6]),(0,[z1,z2,z4,z5,z709,z29]),(0,[z1,z332,z3,z57,z4,z5])],[(0,[z1,z2,z3,z356,z5,z29]),(0,[z1,z2,z3,z1084,z4,z5]),(0,[z1,z2,z361,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1085]),(0,[z1,z2,z458,z4,z5,z29]),(0,[z1,z2,z376,z3,z1086,z6]),(0,[z1087,z1,z2,z3,z4,z5]),(0,[z1,z2,z21,z3,z329,z6]),(0,[z1,z2,z3,z176,z130,z6])],[(0,[z1,z2,z3,z1088,z4,z5]),(0,[z1,z295,z3,z4,z97,z6]),(0,[z1,z2,z1089,z3,z5,z6])],[(0,[z158,z2,z3,z50,z5,z275]),(0,[z1,z2,z3,z94,z4,z897]),(0,[z1,z2,z99,z263,z3,z5])],[(0,[z1,z2,z3,z94,z4,z5]),(1,[z2,z3,z4,z910,z6])],[],[(0,[z1,z2,z21,z3,z39,z5]),(0,[z1,z2,z3,z362,z272,z6])],[(0,[z1,z2,z3,z4,z5,z232]),(0,[z2,z660,z3,z4,z5,z29]),(0,[z1,z2,z21,z83,z3,z5])],[(0,[z1,z2,z3,z1090,z4,z5]),(0,[z1,z2,z1091,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z1092,z5,z6]),(0,[z1,z2,z3,z4,z5,z1093]),(0,[z1,z2,z3,z722,z117,z5]),(0,[z1,z2,z1094,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1095]),(0,[z1,z174,z3,z36,z203,z5])],[(0,[z45,z139,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1096,z6]),(0,[z1,z33,z3,z4,z5,z34]),(0,[z1,z2,z21,z5,z74,z43])],[(0,[z1,z2,z3,z4,z5,z1097]),(0,[z1,z2,z247,z4,z5,z282])],[(0,[z1,z2,z3,z4,z5,z1098]),(0,[z102,z2,z435,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1099])],[(0,[z1,z2,z3,z4,z5,z258]),(0,[z1,z2,z3,z4,z5,z259]),(0,[z1,z2,z21,z3,z5,z632])],[(0,[z1,z189,z2,z3,z4,z29]),(0,[z1,z2,z1100,z3,z5,z6]),(0,[z1,z2,z263,z3,z4,z5]),(0,[z1,z2,z3,z181,z5,z16]),(0,[z1,z2,z3,z4,z5,z1101]),(0,[z1,z2,z21,z3,z412,z5])],[(0,[z1,z61,z21,z3,z4,z97]),(0,[z1,z2,z3,z1102,z4,z5])],[(0,[z1,z2,z3,z4,z1103,z6]),(0,[z1,z314,z3,z4,z51,z6]),(0,[z1,z448,z21,z3,z4,z5]),(0,[z1,z2,z3,z1104,z4,z5]),(0,[z1,z2,z3,z4,z5,z1105]),(0,[z18,z1,z792,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1106]),(0,[z1,z2,z172,z36,z4,z5]),(0,[z18,z1,z19,z4,z5,z286]),(0,[z1,z2,z3,z4,z5,z1107]),(0,[z1,z2,z3,z4,z5,z1108])],[(0,[z1,z2,z3,z4,z1109,z6]),(0,[z1,z448,z172,z4,z5,z6]),(0,[z1,z2,z120,z4,z5,z150]),(0,[z1,z2,z3,z4,z5,z1110]),(0,[z1,z2,z21,z238,z3,z5]),(0,[z1,z2,z3,z36,z4,z907])],[(0,[z1,z2,z3,z762,z362,z5]),(0,[z109,z2,z179,z36,z4,z5]),(0,[z1,z2,z3,z4,z5,z1111]),(0,[z1,z2,z64,z120,z4,z6]),(0,[z1,z2,z3,z4,z5,z1112]),(0,[z1,z2,z3,z4,z5,z888])],[(0,[z1,z2,z3,z36,z225,z5]),(0,[z1,z2,z3,z5,z16,z493]),(0,[z1,z2,z3,z5,z1054,z6]),(0,[z1,z2,z3,z1113,z5,z6])],[(0,[z1,z2,z3,z39,z5,z6]),(0,[z1,z2,z1114,z3,z4,z5]),(0,[z1,z2,z3,z4,z736,z29]),(0,[z1,z88,z41,z4,z449,z6]),(0,[z1,z2,z103,z4,z175,z6]),(0,[z1,z2,z21,z305,z3,z5])],[(0,[z68,z40,z3,z362,z5,z6]),(0,[z1,z2,z1115,z3,z4,z6]),(0,[z1,z78,z3,z4,z5,z34]),(0,[z1,z2,z281,z3,z5,z221])],[(0,[z1,z314,z64,z3,z4,z6]),(0,[z1,z2,z3,z5,z29,z493]),(0,[z1,z174,z3,z203,z5,z16]),(0,[z1,z2,z3,z4,z5,z1116]),(0,[z1,z95,z2,z99,z5,z6]),(0,[z1,z2,z1117,z4,z5,z6])],[(0,[z1,z2,z1118,z4,z5,z6]),(0,[z2,z3,z4,z910,z113,z6]),(0,[z1,z2,z1119,z4,z5,z6]),(0,[z18,z1,z2,z99,z21,z5])]],
   [[(0,[z1,z2,z120,z4,z27,z6]),(0,[z1,z2,z3,z4,z5,z1120])],[(0,[z1,z2,z376,z179,z5,z6]),(0,[z1,z2,z3,z4,z5,z1121]),(0,[z1,z2,z3,z5,z43,z369])],[],[(0,[z102,z2,z3,z4,z113,z56]),(0,[z2,z3,z4,z9,z5,z29]),(0,[z461,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z1122]),(0,[z1,z2,z3,z4,z5,z1123]),(0,[z1,z2,z99,z222,z165,z5])],[(0,[z26,z1,z2,z21,z3,z43]),(0,[z1,z2,z4,z5,z6,z1124]),(0,[z1,z2,z4,z5,z6,z1125]),(0,[z1,z2,z361,z4,z52,z6]),(0,[z1,z2,z1126,z3,z4,z5])],[(0,[z1,z2,z87,z4,z5,z6]),(0,[z1,z314,z3,z4,z27,z6]),(0,[z1,z2,z3,z1127,z5,z6]),(0,[z1,z2,z4,z5,z888,z282])],[(0,[z1,z2,z1128,z3,z4,z5]),(0,[z1,z2,z3,z1129,z4,z5]),(0,[z102,z2,z3,z4,z910,z6]),(0,[z26,z2,z3,z4,z51,z440]),(0,[z1,z2,z1130,z3,z4,z29]),(0,[z1,z2,z3,z4,z5,z1131])],[(0,[z236,z1,z2,z371,z4,z5])],[(0,[z1,z2,z237,z4,z5,z16]),(0,[z1,z2,z3,z4,z793,z6]),(0,[z1,z2,z3,z36,z5,z340])],[(0,[z1,z2,z3,z1132,z4,z5]),(0,[z1,z2,z3,z162,z43,z6])],[(0,[z45,z139,z3,z4,z5,z16]),(0,[z1,z2,z159,z4,z5,z29]),(0,[z1,z2,z21,z3,z540,z5]),(0,[z548,z2,z3,z4,z5,z16]),(0,[z1,z2,z99,z21,z371,z5])],[(0,[z1,z2,z3,z36,z117,z5])],[(0,[z2,z707,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1133]),(0,[z1,z2,z1134,z3,z4,z5])],[(0,[z1,z2,z173,z342,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1135]),(0,[z1,z2,z3,z4,z5,z1136]),(0,[z1,z2,z1137,z3,z4,z6]),(0,[z1,z2,z35,z3,z43,z6]),(0,[z1,z2,z3,z36,z5,z59])],[(0,[z1,z2,z128,z4,z5,z6]),(0,[z1,z2,z3,z4,z1138,z6]),(0,[z1,z2,z757,z3,z4,z29])]],
   [[(0,[z18,z1,z2,z376,z5,z6]),(0,[z1,z2,z4,z22,z625,z6])],[(0,[z93,z2,z3,z98,z5,z6]),(0,[z1,z2,z3,z4,z5,z1139]),(0,[z1,z2,z3,z4,z5,z1140]),(0,[z1,z2,z37,z323,z4,z5])],[(0,[z1,z2,z270,z3,z4,z16]),(0,[z2,z3,z4,z5,z29,z403]),(0,[z1,z2,z3,z4,z5,z1141])],[(0,[z1,z2,z3,z1142,z5,z6]),(0,[z102,z2,z3,z4,z113,z6]),(0,[z2,z3,z4,z5,z759,z29]),(0,[z1,z2,z3,z4,z5,z1143])],[(0,[z1,z2,z3,z1144,z5,z6]),(0,[z1,z2,z4,z966,z5,z6])],[(0,[z1,z2,z3,z39,z5,z16]),(0,[z1,z2,z21,z3,z362,z5]),(0,[z1,z174,z21,z3,z203,z5])],[(0,[z1,z2,z1145,z3,z4,z5])],[(0,[z205,z2,z76,z4,z5,z481]),(0,[z1,z2,z316,z3,z4,z925]),(0,[z530,z1,z2,z21,z3,z5])],[(0,[z1,z2,z120,z4,z5,z16]),(0,[z1,z2,z3,z4,z1146,z6]),(0,[z1,z2,z3,z4,z5,z1147]),(0,[z1,z2,z83,z966,z5,z6]),(0,[z1,z2,z3,z176,z27,z339])],[(0,[z1,z2,z3,z1148,z5,z6]),(0,[z1,z2,z237,z4,z5,z75]),(0,[z1,z2,z21,z159,z4,z5]),(0,[z1,z2,z3,z4,z5,z1149]),(0,[z1,z2,z21,z4,z5,z74])],[(0,[z1,z2,z83,z11,z5,z29]),(0,[z1,z2,z3,z4,z322,z38]),(0,[z18,z1,z264,z19,z5,z6])],[(0,[z1,z2,z3,z1150,z4,z5]),(0,[z1,z2,z1151,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z369])],[(0,[z1,z2,z451,z21,z3,z5]),(0,[z1,z2,z3,z4,z5,z169]),(0,[z1,z2,z1152,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1153]),(0,[z1,z314,z3,z4,z5,z16]),(0,[z1,z2,z4,z5,z6,z1154])],[(0,[z1,z2,z173,z50,z5,z6]),(0,[z1,z2,z87,z4,z5,z16]),(0,[z1155,z2,z3,z4,z5,z6]),(0,[z1,z89,z173,z140,z5,z6]),(0,[z1,z174,z3,z868,z5,z6]),(0,[z1,z2,z99,z21,z3,z218]),(0,[z1,z2,z3,z176,z27,z6])],[(0,[z1,z2,z3,z4,z106,z29]),(0,[z1,z2,z3,z1156,z5,z6]),(0,[z1,z2,z3,z4,z135,z6]),(0,[z1,z2,z3,z1157,z5,z6])]],
   [[(0,[z1,z2,z21,z3,z22,z43])],[(0,[z1,z2,z318,z4,z5,z58])],[(0,[z1,z2,z1158,z3,z5,z6])],[(0,[z1,z2,z3,z5,z29,z922])],[],[(0,[z109,z2,z270,z179,z4,z6]),(0,[z1,z2,z3,z4,z5,z1159]),(0,[z1,z2,z1160,z3,z4,z5]),(0,[z1,z2,z91,z4,z5,z282])],[(0,[z1,z2,z3,z1161,z5,z6]),(0,[z1,z2,z3,z39,z5,z75]),(0,[z1,z2,z1162,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1163]),(0,[z1,z2,z3,z4,z16,z1032]),(0,[z1,z2,z21,z3,z277,z5]),(0,[z1,z2,z3,z5,z59,z986])],[(0,[z1,z2,z3,z255,z4,z5])],[(0,[z1,z2,z128,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z1164]),(0,[z1,z1165,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z29,z460]),(0,[z699,z2,z3,z4,z5,z16]),(0,[z1,z2,z83,z3,z1132,z5])],[(0,[z1,z2,z4,z5,z1166,z6]),(0,[z1,z2,z156,z3,z4,z537])],[(0,[z1,z2,z143,z3,z4,z29]),(0,[z93,z2,z3,z98,z5,z16]),(0,[z1,z2,z361,z5,z59,z6]),(0,[z1,z2,z3,z4,z66,z38])],[(0,[z1,z2,z1167,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1168]),(0,[z738,z2,z21,z3,z4,z5])],[(0,[z1,z2,z3,z4,z1169,z6]),(0,[z1,z2,z1170,z4,z5,z6]),(0,[z102,z2,z3,z4,z113,z16]),(0,[z489,z2,z3,z4,z5,z16]),(0,[z32,z1,z3,z4,z52,z6]),(0,[z1,z2,z3,z4,z968,z6]),(0,[z1,z2,z3,z512,z27,z6])],[(0,[z1,z2,z3,z4,z5,z1171]),(0,[z1,z2,z71,z458,z4,z5]),(0,[z1,z2,z1172,z4,z5,z6]),(0,[z1,z2,z3,z4,z49,z67])],[(0,[z158,z2,z3,z50,z5,z29]),(0,[z1,z2,z21,z3,z5,z509])],[(0,[z1,z2,z281,z3,z5,z16])]],
   [[(0,[z1,z2,z1173,z3,z4,z5]),(0,[z1,z2,z21,z3,z117,z5]),(0,[z1,z2,z3,z727,z5,z6]),(0,[z1,z2,z3,z4,z5,z1174])],[(0,[z1,z2,z3,z4,z1175,z6]),(0,[z1,z2,z76,z117,z5,z6]),(0,[z1,z2,z316,z83,z3,z5]),(0,[z1,z3,z4,z718,z97,z6])],[(0,[z1,z2,z237,z4,z5,z6]),(0,[z1,z2,z120,z4,z5,z56]),(0,[z1,z2,z172,z4,z5,z29]),(0,[z1,z2,z4,z5,z1176,z6]),(0,[z1,z2,z103,z4,z22,z6]),(0,[z1,z2,z21,z3,z5,z43])],[(0,[z1,z2,z128,z39,z5,z6]),(0,[z1,z2,z3,z4,z1177,z6]),(0,[z1,z2,z21,z3,z1132,z5])],[(0,[z1,z2,z3,z1178,z5,z6]),(0,[z109,z2,z179,z4,z5,z29]),(0,[z1,z2,z230,z83,z3,z5]),(0,[z1,z2,z1179,z3,z4,z5]),(0,[z1,z2,z3,z5,z807,z29]),(0,[z840,z2,z3,z4,z5,z6])],[(0,[z2,z3,z849,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1180])],[(0,[z1,z2,z3,z1181,z4,z5]),(0,[z205,z2,z76,z36,z4,z5]),(0,[z1,z2,z3,z4,z5,z1182]),(0,[z1,z2,z3,z1183,z4,z5]),(0,[z1,z2,z21,z3,z470,z5])],[(0,[z1,z2,z3,z362,z5,z16]),(0,[z1,z2,z3,z4,z5,z1184]),(0,[z1,z314,z3,z4,z5,z56]),(0,[z1,z2,z3,z176,z27,z16]),(0,[z1,z2,z3,z1185,z5,z6]),(0,[z932,z2,z3,z4,z5,z6]),(0,[z1,z2,z222,z3,z4,z5])],[(0,[z102,z1,z2,z361,z4,z6]),(0,[z1,z2,z3,z4,z135,z16]),(0,[z1,z2,z901,z4,z5,z6])],[(0,[z1,z2,z128,z4,z5,z75]),(0,[z1,z2,z270,z103,z4,z6]),(0,[z1,z2,z3,z4,z1186,z5]),(0,[z1,z2,z1187,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1188]),(0,[z1,z2,z3,z4,z5,z1189]),(0,[z102,z2,z263,z3,z4,z5])],[(0,[z18,z1,z337,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1190])],[(0,[z1,z2,z1191,z4,z5,z6]),(0,[z1,z2,z270,z3,z4,z6]),(0,[z1,z2,z99,z555,z5,z6]),(0,[z1,z2,z3,z4,z5,z1192]),(0,[z1,z2,z21,z3,z255,z5])],[(0,[z1,z2,z3,z1193,z5,z6]),(0,[z1,z314,z3,z4,z113,z6]),(0,[z1,z2,z797,z3,z4,z5]),(0,[z1,z2,z1194,z3,z4,z5]),(0,[z1,z2,z3,z1195,z5,z6])],[(0,[z1,z2,z99,z4,z449,z6]),(0,[z1,z2,z3,z181,z5,z67])],[(0,[z1,z2,z3,z4,z5,z1196]),(0,[z93,z2,z3,z36,z98,z5]),(0,[z1,z2,z433,z3,z5,z43]),(0,[z1,z61,z3,z4,z97,z16]),(0,[z1,z2,z209,z3,z4,z5])]],
   [[],[(0,[z1,z2,z433,z3,z36,z5]),(0,[z1,z2,z21,z3,z4,z750])],[(0,[z1,z2,z120,z4,z5,z6]),(0,[z1,z2,z1197,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1198])],[(0,[z1,z2,z3,z4,z5,z1199]),(0,[z1,z2,z3,z4,z322,z503]),(0,[z1,z792,z19,z4,z5,z6]),(0,[z18,z1,z209,z19,z4,z5]),(0,[z1,z2,z3,z4,z5,z301])],[(0,[z667,z2,z3,z50,z5,z6]),(0,[z1,z77,z3,z4,z5,z213]),(0,[z1,z2,z3,z1200,z5,z6]),(0,[z1,z2,z3,z36,z4,z135]),(0,[z1,z2,z1201,z4,z5,z6]),(1,[z1,z2,z3,z5,z986])],[(0,[z32,z1,z3,z4,z52,z16]),(0,[z1,z2,z21,z3,z5,z329]),(0,[z1,z2,z3,z4,z1202,z5])],[(0,[z1,z2,z3,z4,z5,z1203]),(0,[z1,z2,z3,z50,z329,z6]),(0,[z1,z448,z3,z248,z5,z6]),(0,[z1,z2,z3,z356,z5,z150]),(0,[z1,z2,z3,z248,z43,z6])],[(0,[z1,z314,z3,z4,z5,z6]),(0,[z2,z3,z4,z51,z910,z6]),(0,[z1,z2,z11,z966,z5,z6]),(0,[z1,z2,z3,z4,z5,z1204])],[(0,[z1,z2,z3,z4,z1205,z6]),(0,[z1,z2,z3,z362,z5,z75]),(0,[z1,z2,z270,z3,z36,z4])],[(0,[z1,z2,z3,z4,z5,z1206]),(0,[z1,z2,z87,z4,z5,z169]),(0,[z1,z2,z1207,z4,z5,z6]),(0,[z1,z2,z1208,z3,z4,z5]),(0,[z1,z2,z825,z3,z4,z5]),(0,[z1,z269,z2,z99,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1209]),(0,[z469,z2,z179,z4,z5,z6]),(0,[z450,z2,z3,z4,z5,z29])],[(0,[z1,z2,z103,z4,z22,z16]),(0,[z1,z2,z99,z21,z3,z5])],[(0,[z1,z1210,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1211]),(0,[z205,z2,z76,z117,z5,z6]),(0,[z1,z3,z4,z5,z29,z983])],[(0,[z1,z2,z237,z4,z5,z258]),(0,[z1,z2,z3,z4,z5,z1212]),(0,[z297,z2,z3,z4,z5,z29])],[(0,[z1,z2,z3,z1213,z4,z5]),(0,[z1,z2,z159,z4,z5,z171]),(0,[z1,z2,z3,z4,z5,z1214]),(0,[z1,z2,z21,z3,z72,z5])]],
   [[(0,[z1,z2,z3,z4,z1215,z6])],[(0,[z1,z2,z1216,z4,z5,z6]),(0,[z2,z3,z54,z98,z4,z5])],[(0,[z1,z2,z3,z36,z5,z494])],[(0,[z1,z2,z1217,z3,z4,z5])],[(0,[z1,z2,z3,z1218,z5,z6]),(0,[z1,z2,z3,z4,z5,z207]),(0,[z1,z2,z3,z4,z279,z29])],[(0,[z93,z2,z3,z98,z5,z169]),(0,[z343,z2,z3,z4,z113,z6]),(0,[z1,z2,z3,z1219,z5,z6]),(0,[z1,z430,z3,z4,z97,z6]),(0,[z1,z2,z21,z3,z511,z5])],[(0,[z1,z2,z237,z39,z5,z6]),(0,[z1,z2,z3,z4,z106,z813])],[(0,[z1,z2,z3,z4,z5,z1220]),(0,[z1,z2,z3,z5,z298,z29]),(0,[z1,z2,z3,z1221,z4,z5])],[],[(0,[z1,z2,z3,z248,z106,z6]),(0,[z1,z2,z1222,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1223]),(0,[z1,z2,z1224,z3,z4,z5]),(0,[z1,z2,z264,z3,z5,z6]),(0,[z1,z2,z281,z3,z5,z6]),(0,[z1,z2,z3,z4,z1225,z5])],[(1,[z2,z3,z727,z5,z6]),(0,[z1,z2,z3,z4,z5,z1226]),(0,[z1,z89,z3,z342,z140,z5]),(0,[z1,z2,z21,z37,z3,z5])],[(0,[z1,z2,z3,z39,z5,z258]),(0,[z26,z2,z3,z4,z910,z6]),(0,[z1,z2,z3,z5,z865,z29]),(0,[z1,z2,z194,z4,z5,z296]),(0,[z1,z2,z3,z342,z4,z5])],[(0,[z1,z2,z3,z4,z6,z774]),(0,[z1,z2,z1227,z3,z4,z5]),(0,[z1,z1228,z2,z3,z4,z6]),(0,[z1,z3,z203,z868,z5,z6])],[(0,[z1,z1229,z2,z3,z4,z6]),(0,[z1,z2,z1230,z3,z4,z5]),(0,[z1,z2,z194,z4,z188,z5]),(0,[z1,z2,z361,z35,z43,z6])],[(0,[z1,z2,z3,z4,z5,z427]),(0,[z1,z2,z91,z587,z4,z5])],[(0,[z688,z2,z3,z50,z5,z6]),(0,[z100,z2,z3,z4,z5,z16]),(0,[z18,z1,z19,z4,z5,z16]),(0,[z1,z2,z3,z4,z1086,z6]),(0,[z1,z2,z361,z21,z5,z43]),(0,[z1,z2,z3,z4,z5,z1231])]],
   [[(0,[z1,z2,z3,z4,z1232,z5]),(0,[z1,z2,z376,z21,z3,z5])],[(0,[z1,z2,z3,z362,z5,z6]),(0,[z1,z2,z3,z176,z27,z369])],[(0,[z1,z2,z1027,z3,z5,z6]),(0,[z1,z2,z3,z1233,z4,z5]),(0,[z1,z2,z425,z3,z4,z368])],[(0,[z1,z773,z3,z4,z5,z29]),(0,[z1,z996,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1234,z4,z6]),(0,[z1,z2,z270,z120,z4,z6]),(0,[z93,z2,z21,z3,z98,z5]),(0,[z1,z2,z3,z4,z5,z941])],[(0,[z1,z2,z3,z1235,z5,z6]),(0,[z26,z2,z3,z4,z51,z6]),(0,[z1,z147,z3,z4,z5,z17])],[(0,[z1,z2,z3,z4,z5,z1236]),(0,[z1,z2,z1237,z3,z4,z5])],[(0,[z1,z2,z1007,z3,z387,z5]),(0,[z1,z2,z208,z3,z43,z6]),(0,[z1,z2,z99,z165,z5,z6]),(0,[z1,z2,z99,z330,z165,z5])],[],[(0,[z1,z2,z3,z387,z5,z481]),(0,[z1,z2,z21,z3,z4,z135]),(0,[z1,z61,z3,z4,z97,z6])],[(0,[z1,z2,z270,z4,z65,z6]),(0,[z1,z2,z21,z3,z5,z657])],[(0,[z1,z448,z3,z4,z5,z150]),(0,[z1,z2,z3,z36,z4,z42]),(0,[z1,z174,z3,z203,z5,z427]),(0,[z1,z436,z79,z3,z4,z5]),(0,[z1,z2,z3,z36,z4,z800])],[(0,[z1,z2,z3,z4,z1238,z6]),(0,[z1,z2,z1239,z4,z5,z6]),(0,[z1,z89,z3,z140,z5,z6]),(0,[z1,z2,z21,z35,z3,z43]),(0,[z160,z2,z3,z94,z4,z5])],[],[(0,[z1,z2,z128,z4,z5,z258]),(0,[z1,z2,z3,z4,z1240,z6]),(0,[z1,z2,z1241,z3,z4,z5]),(0,[z1,z2,z1242,z3,z4,z5])],[(0,[z1,z2,z1243,z3,z4,z6]),(0,[z1,z2,z1244,z3,z4,z5]),(0,[z1,z2,z209,z264,z3,z5]),(0,[z1015,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z963,z6]),(0,[z1,z2,z281,z3,z5,z34])]],
   [[(0,[z205,z2,z76,z4,z5,z29]),(0,[z1,z2,z3,z1245,z4,z5])],[(0,[z680,z2,z179,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1246]),(0,[z1,z2,z3,z106,z43,z6]),(0,[z1,z2,z83,z11,z5,z468]),(0,[z1,z2,z3,z181,z66,z38])],[(0,[z1,z2,z3,z4,z1247,z6]),(0,[z1,z2,z264,z3,z5,z16]),(0,[z1,z2,z3,z4,z791,z6])],[(0,[z1,z2,z3,z4,z897,z29]),(0,[z1,z2,z99,z664,z5,z6]),(0,[z1,z88,z41,z36,z4,z5])],[(0,[z1,z2,z3,z1248,z4,z5])],[(0,[z2,z263,z3,z179,z4,z5])],[(0,[z1,z2,z3,z4,z1249,z6]),(0,[z1,z2,z376,z3,z5,z29]),(0,[z1,z2,z3,z4,z1250,z6])],[(0,[z1,z2,z3,z1251,z4,z5]),(0,[z1,z421,z2,z21,z3,z5]),(0,[z1,z2,z361,z239,z4,z5]),(0,[z1,z2,z21,z3,z36,z5]),(0,[z839,z2,z21,z3,z4,z5])],[(0,[z1,z2,z237,z362,z5,z6]),(0,[z1,z2,z1252,z4,z5,z6])],[(0,[z1,z2,z3,z4,z272,z29]),(0,[z1,z2,z21,z3,z5,z301]),(0,[z1,z2,z3,z36,z5,z493]),(0,[z1,z2,z239,z4,z5,z74])],[(0,[z158,z2,z3,z36,z50,z5]),(0,[z1,z2,z1253,z4,z5,z6])],[(0,[z1,z2,z361,z50,z5,z6]),(0,[z1036,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1254]),(0,[z1,z2,z3,z5,z986,z31])],[],[(0,[z1,z2,z3,z362,z5,z258]),(0,[z1,z2,z3,z4,z917,z6]),(0,[z1,z2,z3,z4,z1255,z6])],[],[(0,[z1,z2,z316,z3,z255,z5]),(0,[z1,z2,z3,z356,z5,z56]),(0,[z1,z2,z3,z248,z5,z29]),(0,[z1,z2,z3,z4,z449,z6])]],
   [[(0,[z1,z2,z99,z165,z5,z16])],[(0,[z93,z2,z87,z98,z5,z6]),(0,[z1,z1040,z3,z4,z5,z6])],[(0,[z102,z314,z3,z4,z113,z6]),(0,[z2,z3,z4,z5,z434,z29]),(0,[z1,z2,z3,z4,z5,z1256]),(0,[z1,z2,z3,z4,z5,z1257])],[(0,[z1258,z1,z2,z3,z4,z6])],[(0,[z1,z2,z91,z4,z5,z114]),(0,[z1,z2,z751,z4,z5,z6]),(0,[z1,z2,z99,z165,z329,z6])],[(0,[z1,z163,z2,z3,z4,z6]),(0,[z1,z2,z1259,z3,z4,z5]),(0,[z1,z2,z3,z36,z4,z106]),(0,[z1,z2,z3,z4,z5,z1260]),(0,[z1,z89,z3,z140,z5,z16]),(0,[z1,z2,z1261,z3,z4,z5])],[(0,[z109,z2,z849,z4,z5,z6]),(0,[z1,z2,z194,z638,z4,z5]),(0,[z1,z2,z3,z36,z4,z218]),(0,[z1,z2,z3,z5,z59,z301])],[(0,[z1,z2,z3,z5,z6,z986])],[(0,[z2,z3,z727,z4,z5,z6]),(0,[z2,z579,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z1262]),(0,[z1,z2,z21,z3,z4,z955])],[(0,[z18,z1,z19,z4,z5,z6]),(0,[z1263,z2,z3,z4,z5,z6])],[(0,[z1,z2,z99,z21,z165,z5]),(0,[z1,z2,z99,z36,z165,z5]),(0,[z1,z2,z91,z4,z5,z888])],[(0,[z1,z89,z337,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z1264]),(0,[z1,z2,z35,z74,z43,z6])],[(0,[z2,z316,z263,z3,z4,z5]),(0,[z1,z2,z3,z4,z66,z710])],[(0,[z1,z2,z3,z1265,z5,z6]),(0,[z26,z1,z2,z361,z4,z6])],[(0,[z1,z2,z1266,z3,z4,z5]),(0,[z26,z2,z3,z4,z51,z70])],[(0,[z1,z2,z3,z356,z5,z6]),(0,[z1,z2,z3,z4,z1249,z16]),(0,[z1,z2,z21,z3,z5,z570])]],
   [[(0,[z1,z2,z3,z4,z5,z1267]),(0,[z1,z2,z3,z1104,z356,z5]),(0,[z1,z2,z458,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z42]),(0,[z1,z89,z3,z140,z42,z6]),(0,[z1,z2,z3,z4,z218,z6])],[(0,[z1,z2,z1152,z3,z4,z279]),(0,[z1,z2,z172,z4,z5,z150]),(0,[z1,z2,z1268,z3,z5,z6]),(1,[z1,z2,z966,z5,z6])],[(0,[z68,z40,z3,z36,z4,z5]),(0,[z1,z2,z1269,z4,z5,z6]),(0,[z1,z2,z21,z3,z52,z43])],[(0,[z1,z2,z3,z4,z1270,z5]),(0,[z1,z497,z3,z4,z97,z6]),(0,[z1,z2,z3,z36,z5,z298])],[(0,[z1,z2,z3,z4,z69,z29]),(0,[z1,z2,z1000,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z481]),(0,[z1,z2,z3,z36,z5,z417])],[(0,[z1,z2,z3,z4,z1271,z6]),(0,[z1272,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z1273,z4,z5]),(0,[z2,z3,z54,z4,z5,z29])],[(0,[z1,z2,z1274,z3,z4,z5])],[(0,[z1,z2,z83,z395,z5,z6]),(0,[z1,z2,z3,z4,z936,z6]),(0,[z1,z2,z3,z36,z321,z5])],[(0,[z1,z139,z3,z4,z69,z6]),(0,[z1,z2,z128,z362,z5,z6]),(0,[z1,z2,z3,z4,z1275,z6]),(0,[z1,z2,z3,z4,z5,z1276]),(0,[z1,z2,z3,z4,z449,z16])],[(0,[z1,z2,z1277,z3,z4,z5])],[(0,[z1,z2,z1278,z4,z5,z6]),(0,[z1,z2,z355,z4,z5,z114]),(0,[z1,z2,z21,z3,z5,z941])],[(0,[z1,z2,z3,z1279,z4,z5]),(0,[z1,z2,z361,z21,z3,z5])],[(0,[z1,z2,z1280,z4,z5,z6]),(0,[z1,z274,z3,z4,z5,z17])],[(0,[z1,z2,z3,z890,z4,z5]),(0,[z1,z2,z21,z3,z257,z5])],[(0,[z1,z163,z2,z3,z4,z16]),(0,[z1,z2,z21,z3,z5,z493])],[(0,[z1,z2,z3,z4,z5,z1281]),(0,[z158,z2,z21,z3,z50,z5]),(0,[z1,z2,z173,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z1282])]],
   [[(0,[z1,z2,z1283,z4,z5,z6]),(0,[z32,z1,z3,z4,z262,z6]),(0,[z158,z2,z3,z168,z50,z5]),(1,[z1,z2,z3,z4,z710])],[],[(0,[z1,z2,z3,z4,z1284,z6]),(0,[z1,z2,z3,z1285,z5,z6]),(0,[z158,z2,z263,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1286])],[(0,[z1,z2,z99,z270,z4,z6]),(0,[z1,z2,z3,z94,z4,z279]),(0,[z1,z2,z433,z3,z176,z5]),(0,[z1,z2,z3,z4,z5,z814]),(0,[z1,z2,z3,z176,z5,z369]),(0,[z1,z2,z21,z3,z544,z5])],[(0,[z1,z2,z1287,z4,z5,z6]),(0,[z1,z448,z3,z4,z5,z56]),(0,[z1,z519,z3,z4,z52,z6])],[(0,[z1,z2,z3,z4,z1288,z6]),(0,[z93,z2,z3,z727,z5,z6]),(0,[z1,z2,z4,z22,z329,z6]),(0,[z1,z2,z156,z3,z4,z710])],[(0,[z1,z2,z3,z1289,z4,z5]),(0,[z2,z263,z3,z4,z5,z16]),(0,[z1,z2,z1290,z3,z4,z6]),(1,[z1,z2,z4,z5,z888]),(0,[z1,z2,z3,z4,z130,z38])],[(0,[z1,z2,z1291,z4,z5,z6]),(0,[z93,z2,z316,z3,z98,z5]),(0,[z1,z2,z64,z4,z360,z6])],[(0,[z1,z2,z3,z356,z5,z16]),(0,[z1,z2,z173,z21,z4,z5]),(0,[z1,z2,z173,z36,z4,z5])],[(0,[z1,z2,z21,z128,z4,z5]),(0,[z1,z2,z3,z4,z5,z275]),(0,[z28,z2,z263,z3,z4,z5]),(0,[z1,z2,z458,z4,z5,z16]),(0,[z1,z2,z3,z4,z218,z16])],[(0,[z1,z2,z21,z3,z4,z106]),(0,[z1,z2,z21,z3,z432,z5]),(0,[z1,z2,z3,z977,z5,z29]),(0,[z1,z2,z1268,z3,z5,z16])],[(0,[z1,z2,z887,z3,z117,z5]),(0,[z398,z2,z3,z4,z5,z29]),(0,[z1,z147,z3,z4,z5,z221]),(0,[z1,z2,z21,z3,z4,z218]),(0,[z1,z2,z3,z4,z893,z6])],[(0,[z1,z2,z3,z4,z5,z1292]),(0,[z1,z2,z3,z1293,z5,z6]),(0,[z1,z2,z3,z791,z43,z6]),(0,[z1,z2,z3,z4,z38,z710])],[(0,[z1,z2,z21,z87,z4,z5]),(0,[z601,z2,z3,z4,z5,z29]),(0,[z1,z2,z21,z3,z551,z5])],[(0,[z1,z707,z3,z4,z5,z6]),(0,[z1,z2,z1130,z3,z4,z6]),(0,[z1,z2,z99,z3,z5,z267])],[(0,[z694,z139,z3,z4,z5,z6]),(0,[z1,z2,z172,z248,z5,z6]),(0,[z1,z2,z3,z4,z1294,z5])]],
   [[(0,[z1,z2,z1295,z4,z5,z6]),(0,[z1,z2,z3,z4,z936,z16]),(0,[z1,z2,z3,z4,z1296,z6]),(0,[z1,z2,z3,z4,z5,z1297]),(0,[z1,z2,z3,z4,z66,z311])],[(0,[z1,z314,z120,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1298]),(0,[z26,z185,z2,z3,z4,z6]),(0,[z2,z3,z4,z5,z669,z16]),(0,[z1,z89,z3,z36,z140,z5]),(0,[z1,z2,z64,z4,z329,z6]),(0,[z1,z2,z3,z36,z4,z897])],[(0,[z1,z2,z3,z36,z4,z5]),(0,[z102,z2,z3,z36,z4,z113])],[(0,[z1,z448,z3,z4,z5,z6]),(0,[z1,z455,z3,z4,z5,z410]),(0,[z1,z2,z3,z4,z5,z1299])],[(0,[z1,z2,z3,z1300,z5,z6]),(0,[z1,z2,z342,z458,z4,z5])],[(0,[z1,z40,z3,z4,z69,z6]),(0,[z1,z2,z1301,z3,z4,z5]),(0,[z1,z2,z361,z4,z5,z252])],[(0,[z68,z40,z21,z3,z4,z5]),(0,[z1,z2,z1302,z3,z4,z6]),(0,[z1,z2,z3,z4,z351,z29]),(0,[z1,z2,z3,z4,z5,z1303]),(0,[z1,z3,z4,z52,z718,z6])],[(0,[z1,z2,z3,z1304,z4,z5]),(0,[z1,z2,z316,z3,z5,z43]),(0,[z1,z2,z21,z543,z3,z5]),(0,[z1,z2,z21,z3,z5,z298])],[(0,[z1,z2,z956,z3,z4,z5]),(0,[z1,z2,z1305,z3,z4,z5]),(0,[z1,z2,z99,z230,z3,z5]),(0,[z1,z2,z159,z98,z5,z6]),(0,[z1,z2,z3,z36,z584,z5])],[(0,[z1,z1306,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1307,z6]),(0,[z1,z2,z99,z21,z3,z329])],[(0,[z109,z2,z143,z179,z4,z6]),(0,[z1,z2,z230,z3,z5,z43]),(0,[z1,z2,z3,z4,z5,z1308]),(0,[z1,z2,z8,z4,z5,z58])],[(0,[z1,z2,z1309,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1310]),(0,[z1,z2,z3,z4,z5,z1003])],[(0,[z1,z2,z872,z3,z4,z5])],[],[(0,[z1,z2,z3,z1056,z4,z5]),(0,[z1,z2,z3,z36,z4,z351])]],
   [[(0,[z102,z2,z120,z4,z113,z6])],[(0,[z109,z2,z21,z179,z4,z5])],[(0,[z1,z2,z1311,z4,z5,z6]),(0,[z1,z2,z3,z387,z5,z29]),(0,[z1,z2,z1312,z4,z5,z6]),(0,[z1,z2,z264,z3,z36,z5]),(0,[z1,z2,z281,z3,z36,z5]),(0,[z1,z2,z361,z36,z4,z5])],[(0,[z1,z2,z3,z4,z5,z86]),(0,[z2,z3,z573,z4,z5,z29]),(0,[z1,z2,z3,z5,z252,z59])],[(0,[z1,z2,z3,z4,z5,z1313]),(0,[z205,z2,z21,z76,z4,z5]),(0,[z1,z2,z1314,z3,z4,z5])],[(0,[z1,z2,z3,z1315,z5,z6]),(0,[z1,z2,z3,z4,z1316,z6]),(0,[z1,z2,z3,z4,z5,z1317]),(0,[z1,z3,z792,z4,z5,z6])],[(0,[z1,z2,z1318,z3,z4,z6]),(0,[z1,z2,z1319,z3,z4,z5]),(0,[z1,z2,z1320,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1321]),(0,[z1,z2,z3,z4,z106,z6]),(0,[z1,z2,z3,z4,z329,z29]),(0,[z1,z2,z1322,z3,z4,z5])],[(0,[z1,z2,z1323,z3,z4,z5]),(0,[z1,z2,z263,z83,z3,z5])],[(0,[z1,z2,z3,z4,z5,z1324]),(0,[z1,z61,z3,z4,z718,z6]),(0,[z1,z332,z3,z4,z5,z221]),(0,[z1,z2,z492,z21,z3,z5])],[(0,[z1,z2,z1325,z3,z4,z5]),(0,[z1,z2,z3,z117,z5,z6]),(0,[z1,z3,z4,z1326,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1327]),(0,[z1,z2,z1328,z3,z4,z5]),(0,[z1,z2,z159,z4,z5,z16])],[(0,[z1,z2,z3,z4,z1329,z6]),(0,[z68,z40,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z1330]),(0,[z1087,z1,z2,z376,z3,z5]),(0,[z1,z2,z361,z4,z65,z6])],[(0,[z1,z2,z3,z4,z5,z1331]),(0,[z1,z2,z1332,z3,z4,z5]),(0,[z1,z448,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z1333]),(0,[z1,z3,z4,z868,z5,z6])],[(0,[z2,z263,z3,z4,z51,z5])],[]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 511) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 511).take 501) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1012).take 390) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1402)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [511, 501, 390] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 153).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 153).take 136).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 289).take 149).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 438).take 74).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [153, 136, 149, 74] = true :=
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

end PEqualNP.Outside.L_meta_38769

theorem PEqualNP.Outside.L_meta_38769 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4236830856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4236830856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38769.solve