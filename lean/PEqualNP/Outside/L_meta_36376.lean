import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36376

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
  Nat.testBit (4278124202 * 2 ^ 32 + 4276813448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0xa02800002401282a#64 ++ 0x5014000012009415#64 ++ 0xdff64041fc23e87f#64 ++ 0xeffb2020fe11f43f#64 : BitVec 256),
   (0x469021a2904c9095#64 ++ 0x234810d14826484a#64 ++ 0xbb6ea3a690dc919f#64 ++ 0xddb751d3486e48cf#64 : BitVec 256),
   (0x84202c28e1171a18#64 ++ 0x42101614708b8d0c#64 ++ 0x76dd3c38e31f1e19#64 ++ 0xbb6e9e1c718f8f0c#64 : BitVec 256),
   (0x0141c01502a00540#64 ++ 0x80a0e00a815002a0#64 ++ 0xfe3fc03f03e01fe1#64 ++ 0x7f1fe01f81f00ff0#64 : BitVec 256),
   (0x0981d6c003fac001#64 ++ 0x04c0eb6001fd6000#64 ++ 0xf1fdffc003ffe000#64 ++ 0xf8feffe001fff000#64 : BitVec 256),
   (0x0e01fb7fd8000000#64 ++ 0x0700fdbfec000000#64 ++ 0x0ffdfffffc000000#64 ++ 0x07fefffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [8, 6]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [8, 6]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [3, 13]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf1fdffc003ffe000 0xf8feffe001fff000

def z1 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xffffffff03ffffe1 0xffffffff81fffff0

def z2 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0ffdfffffc000000 0x07fefffffe000000

def z3 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xffffffffffe01fe1 0x7ffffffffff00ff0

def z4 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbb6ea3a690dc919f 0xddb751d3486e48cf

def z5 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x76dd3c38e31f1e19 0xbb6e9e1c718f8f0c

def z6 : W := mkw 0xa02800002401282a 0x5014000012009415 0xdff64041fc23e87f 0xeffb2020fe11f43f

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0x9b6600009000801f 0xcdb300004800400f

def z8 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfe3fc03f03e01fe1 0x7f1fe01f81f00ff0

def z9 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x6099ffc003ff6000 0x304cffe001ffb000

def z10 : W := mkw 0x84202828e0051a18 0x4210141470028d0c 0x00000000e0000018 0x000000007000000c

def z11 : W := mkw 0xa02800002401282a 0x5014000012009415 0x0e020001fc00087f 0x07010000fe00043f

def z12 : W := mkw 0x0080008000488001 0x0040004000244000 0x2008a38000dc0000 0x100451c0006e0000

def z13 : W := mkw 0x80200c0861171a18 0x40100604308b8d0c 0x74911c18631f1e19 0xba488e0c318f8f0c

def z14 : W := mkw 0x469021a290488085 0x234810d148244042 0x8b6ea3a690c08186 0x45b751d3486040c3

def z15 : W := mkw 0x0101c00002a00000 0x0080e00001500000 0x4011400003200000 0x2008a00001900000

def z16 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x2008a3a600dc1180 0x100451d3006e08c0

def z17 : W := mkw 0x0401e83dc0000000 0x0200f41ee0000000 0x0efdfc3fe0000000 0x077efe1ff0000000

def z18 : W := mkw 0xa02800002401282a 0x5014000012009415 0x01c00040fc03e01e 0x80e000207e01f00f

def z19 : W := mkw 0xa02800002401282a 0x5014000012009415 0x449040416c236860 0x22482020b611b430

def z20 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x2009bf8003dc0000 0x1004dfc001ee0000

def z21 : W := mkw 0x0f81ffffdbfac001 0x07c0ffffedfd6000 0xfffdffffffffe000 0xfffefffffffff000

def z22 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x20093c38031c1600 0x10049e1c018e0b00

def z23 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x01c03fc0001fe000 0x80e01fe0000ff000

def z24 : W := mkw 0x0901d64003b24000 0x0480eb2001d92000 0x40915c4003236000 0x2048ae200191b000

def z25 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x09e0ffc7fc000000 0x04f07fe3fe000000

def z26 : W := mkw 0x0d81fee8c3fac001 0x06c0ff7461fd6000 0xf7fdfff8e3ffe000 0xfbfefffc71fff000

def z27 : W := mkw 0x0400202080041010 0x0200101040020808 0x20082020001c1000 0x10041010000e0800

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e000001fc000000 0x07000000fe000000

def z29 : W := mkw 0xa028040025173a3a 0x50140200128b9d1d 0xf0020000033ffe7f 0xf8010000019fff3f

def z30 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x00003f80001c0000 0x00001fc0000e0000

def z31 : W := mkw 0x0400202080041010 0x0200101040020808 0x324c2020801c1019 0x99261010400e080c

def z32 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x01c03fc0fc000000 0x00e01fe07e000000

def z33 : W := mkw 0x0000000000000000 0x0000000000000000 0xde36400100200861 0x6f1b200080100430

def z34 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x01c9bffefc000000 0x00e4dfff7e000000

def z35 : W := mkw 0x0000000000000000 0x0000000000000000 0x092040411c000000 0x049020208e000000

def z36 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xde37401903200e61 0x6f1ba00c81900730

def z37 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xffff7c79ff3ffe7f 0xffffbe3cff9fff3f

def z38 : W := mkw 0x0000000000000000 0x0000000000000000 0x014000009000801e 0x80a000004800400f

def z39 : W := mkw 0x4e91fbffd84c9095 0x2748fdffec26484a 0xbffffffffcdc919f 0xdffffffffe6e48cf

def z40 : W := mkw 0xe6b821a2b44db8bf 0x735c10d15a26dc5f 0xfffee3e7fcfff9ff 0xffff71f3fe7ffcff

def z41 : W := mkw 0xa169c01526a12d6a 0xd0b4e00a935096b5 0xfe3fc03f03e3ffff 0xff1fe01f81f1ffff

def z42 : W := mkw 0x8620293ff8051a18 0x4310149ffc028d0c 0x0e00003ffc001e19 0x0700001ffe000f0c

def z43 : W := mkw 0x8561ec3de3b71f58 0xc2b0f61ef1db8fac 0xfefffc3fe3ff1ff9 0xff7ffe1ff1ff8ffc

def z44 : W := mkw 0x8da1fee8e3ffda19 0x46d0ff7471ffed0c 0xf1fdffc0e3ffe018 0xf8feffe071fff00c

def z45 : W := mkw 0x0801d24000000000 0x0400e92000000000 0x01fdffc000000000 0x00feffe000000000

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z47 : W := mkw 0x47d1e1b792ec95d5 0xa3e8f0dbc9764aea 0xff7fe3bf93fc9fff 0xffbff1dfc9fe4fff

def z48 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x32cc3c20e01f1019 0x99661e10700f880c

def z49 : W := mkw 0x0180048003fac001 0x00c0024001fd6000 0xf000000003ffe000 0xf800000001fff000

def z50 : W := mkw 0x0040001500000540 0x8020000a800002a0 0x0400001900000e60 0x0200000c80000730

def z51 : W := mkw 0x0f81ffeadbfac001 0x07c0fff56dfd6000 0xf1fdffc0ffffe000 0xf8feffe07ffff000

def z52 : W := mkw 0x0101c00002a00000 0x0080e00001500000 0xf03dc00003e00000 0x781ee00001f00000

def z53 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x00c03c00e01f0018 0x80601e00700f800c

def z54 : W := mkw 0x0000081d48000000 0x0000040ea4000000 0x040000196c000000 0x0200000cb6000000

def z55 : W := mkw 0x8c21fe7de9171a18 0x4610ff3ef48b8d0c 0x76dd7c79ef1f1e19 0xbb6ebe3cf78f8f0c

def z56 : W := mkw 0x0000000000000000 0x0000000000000000 0x06d40000e0000000 0x036a000070000000

def z57 : W := mkw 0xa4282828e4053a3a 0x5214141472029d1d 0x0e020039fc001e7f 0x0701001cfe000f3f

def z58 : W := mkw 0x8020000020010808 0x4010000010008404 0x56d40000e0030819 0xab6a00007001840c

def z59 : W := mkw 0x8161cc1d63b30f48 0xc0b0e60eb1d987a4 0x44915c1963230e60 0x2248ae0cb1918730

def z60 : W := mkw 0x8e21ff7ff9171a18 0x4710ffbffc8b8d0c 0x7ffdffffff1f1e19 0xbffeffffff8f8f0c

def z61 : W := mkw 0xc6b02daaf15f9a9d 0x635816d578afcd4e 0xffffbfbef3df9f9f 0xffffdfdf79efcfcf

def z62 : W := mkw 0x0400242081161010 0x02001210408b0808 0x72dd3c20831f1019 0xb96e9e10418f880c

def z63 : W := mkw 0x8421ec3de1171a18 0x4210f61ef08b8d0c 0x7efdfc3fe31f1e19 0xbf7efe1ff18f8f0c

def z64 : W := mkw 0x0600293fd8000000 0x0300149fec000000 0x0ff4407ffc000000 0x07fa203ffe000000

def z65 : W := mkw 0x8020000020010808 0x4010000010008404 0x5000000000030819 0xa80000000001840c

def z66 : W := mkw 0x2008000004002022 0x1004000002001011 0x8ff64041fc20e066 0x47fb2020fe107033

def z67 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x2009803e03c01780 0x1004c01f01e00bc0

def z68 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xff7fa3be93dc9f9f 0xffbfd1df49ee4fcf

def z69 : W := mkw 0x0881d2c000488001 0x0440e96000244000 0xb1fdffc000dc8000 0xd8feffe0006e4000

def z70 : W := mkw 0x0000000000000000 0x0000000000000000 0x761d003803001e01 0x3b0e801c01800f00

def z71 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0f20c3fffc000000 0x079061fffe000000

def z72 : W := mkw 0xa0280c0865132a2a 0x5014060432899515 0x44915c596f236e60 0x2248ae2cb791b730

def z73 : W := mkw 0x0000040001161210 0x00000200008b0908 0x20000000031c1600 0x10000000018e0b00

def z74 : W := mkw 0x0040000000000540 0x80200000000002a0 0x0002000000001fe1 0x0001000000000ff0

def z75 : W := mkw 0x8020000020010808 0x4010000010008404 0x5ff44041fc030819 0xaffa2020fe01840c

def z76 : W := mkw 0x449020a0804c9095 0x224810504026484a 0xb24e202080dc919f 0xd9271010406e48cf

def z77 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x7ffd7c79ff1f1e19 0xbffebe3cff8f8f0c

def z78 : W := mkw 0x098016c003fac001 0x04c00b6001fd6000 0xf1c03fc003ffe000 0xf8e01fe001fff000

def z79 : W := mkw 0x4691e1b7904c9095 0x2348f0dbc826484a 0xbf7fe3bf90dc919f 0xdfbff1dfc86e48cf

def z80 : W := mkw 0xa02800002401282a 0x5014000012009415 0xdeb640416c236861 0x6f5b2020b611b430

def z81 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xa82bc03f03e017e0 0x5415e01f81f00bf0

def z82 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x70c03c00e31f1e19 0xb8601e00718f8f0c

def z83 : W := mkw 0x0000040001120000 0x0000020000890000 0xf1fd7c40033fe000 0xf8febe20019ff000

def z84 : W := mkw 0x0000000000000000 0x0000000000000000 0xd1f440400023e000 0xe8fa20200011f000

def z85 : W := mkw 0xc7f1edbff3ff9fdd 0xe3f8f6dff9ffcfee 0xffffffbff3ff9fff 0xffffffdff9ffcfff

def z86 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf1fdfffe03fff780 0xf8feffff01fffbc0

def z87 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x4e3dc03f03200e60 0x271ee01f81900730

def z88 : W := mkw 0x0000000000000000 0x0000000000000000 0x1244000080000019 0x892200004000000c

def z89 : W := mkw 0x4290018210488085 0x214800c108244042 0x8922838610c08186 0x449141c3086040c3

def z90 : W := mkw 0x8e203f6af9171a18 0x47101fb57c8b8d0c 0x77dd3ff8ff1f1e19 0xbbee9ffc7f8f8f0c

def z91 : W := mkw 0xa02800002401282a 0x5014000012009415 0xfffec067fce3f9ff 0xffff6033fe71fcff

def z92 : W := mkw 0x0400202080041010 0x0200101040020808 0x765d2038831c1e19 0xbb2e901c418e0f0c

def z93 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf5fdffd903ffee60 0xfafeffec81fff730

def z94 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0499ffff6c000000 0x024cffffb6000000

def z95 : W := mkw 0x0080008000488001 0x0040004000244000 0xb16ca38000dc8000 0xd8b651c0006e4000

def z96 : W := mkw 0x2008000004002022 0x1004000002001011 0x892240411c20e066 0x449120208e107033

def z97 : W := mkw 0x8020040021171a18 0x40100200108b8d0c 0x70000000031f1e19 0xb8000000018f8f0c

def z98 : W := mkw 0x0000000000000000 0x0000000000000000 0x0ff44041fc000000 0x07fa2020fe000000

def z99 : W := mkw 0xae29fb7ffc01282a 0x5714fdbffe009415 0xdffffffffc23e87f 0xeffffffffe11f43f

def z100 : W := mkw 0x0600212290000000 0x0300109148000000 0x0b6ca3a690000000 0x05b651d348000000

def z101 : W := mkw 0x0801da5d48000000 0x0400ed2ea4000000 0x04915c596c000000 0x0248ae2cb6000000

def z102 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0009bfbe00000000 0x0004dfdf00000000

def z103 : W := mkw 0x0a01d35718000000 0x0500e9ab8c000000 0x0920c3c71c000000 0x049061e38e000000

def z104 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x0ff47fc1fc000000 0x07fa3fe0fe000000

def z105 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xb00aa3a600dc919f 0xd80551d3006e48cf

def z106 : W := mkw 0xa02800002401282a 0x5014000012009415 0x000200000000087f 0x000100000000043f

def z107 : W := mkw 0xa02800002401282a 0x5014000012009415 0x9f660001fc00887f 0xcfb30000fe00443f

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0x9ff64041fc00801f 0xcffb2020fe00400f

def z109 : W := mkw 0x0000040001120000 0x0000020000890000 0x70dd3c00031f0000 0xb86e9e00018f8000

def z110 : W := mkw 0x0981d2c002e8c001 0x04c0e96001746000 0x8120c3c000e0e000 0x409061e000707000

def z111 : W := mkw 0x8020000020010808 0x4010000010008404 0x06000000e0000819 0x030000007000040c

def z112 : W := mkw 0x0000000000000000 0x0000000000000000 0x049040416c000000 0x02482020b6000000

def z113 : W := mkw 0x4190048003fed095 0x20c8024001ff684a 0xf002000003fff19f 0xf801000001fff8cf

def z114 : W := mkw 0x80200c0861130a08 0x4010060430898504 0x56d51c18e3030e19 0xab6a8e0c7181870c

def z115 : W := mkw 0x0600292ad8000000 0x030014956c000000 0x00000000fc000000 0x000000007e000000

def z116 : W := mkw 0x0000000000000000 0x0000000000000000 0xba2e802600c01181 0x5d174013006008c0

def z117 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x41d17fc0033fe000 0xa0e8bfe0019ff000

def z118 : W := mkw 0xa068001524012d6a 0xd034000a920096b5 0xdff6407ffc23ffff 0xeffb203ffe11ffff

def z119 : W := mkw 0x8020000020051a18 0x4010000010028d0c 0x0000000000001e19 0x0000000000000f0c

def z120 : W := mkw 0x0000000000000000 0x0000000000000000 0x01c00040fc000000 0x00e000207e000000

def z121 : W := mkw 0x0801d24000000000 0x0400e92000000000 0x0ffdffc1fc000000 0x07feffe0fe000000

def z122 : W := mkw 0x0001c01500000000 0x0000e00a80000000 0xde3fc03f00200861 0x6f1fe01f80100430

def z123 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x324d3c38831c1619 0x99269e1c418e0b0c

def z124 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x4411401903200e60 0x2208a00c81900730

def z125 : W := mkw 0xa169c01526a12d6a 0xd0b4e00a935096b5 0xffffc07fffe3ffff 0xffffe03ffff1ffff

def z126 : W := mkw 0x4f91f7e293fed095 0x27c8fbf149ff684a 0xbb6fbfa693dc919f 0xddb7dfd349ee48cf

def z127 : W := mkw 0x0981d2c002e8c001 0x04c0e96001746000 0xb16ce3c000fce000 0xd8b671e0007e7000

def z128 : W := mkw 0xa02800002401282a 0x5014000012009415 0x57d40040fc03e81f 0xabea00207e01f40f

def z129 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x2ffdffffffc01780 0x17feffffffe00bc0

def z130 : W := mkw 0x0000000000000000 0x0000000000000000 0x50d4000000030000 0xa86a000000018000

def z131 : W := mkw 0x04002828c0000000 0x0200141460000000 0x06dd3c38e0000000 0x036e9e1c70000000

def z132 : W := mkw 0xc6b021a2b04d989d 0x635810d15826cc4e 0xfffea3a6f0df999f 0xffff51d3786fcccf

def z133 : W := mkw 0xada9fee8e7fffa3b 0x56d4ff7473fffd1d 0xfffffff9fffffe7f 0xfffffffcffffff3f

def z134 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x71dd3fc0031fe000 0xb8ee9fe0018ff000

def z135 : W := mkw 0xaf69fb7ffea12d6a 0xd7b4fdbfff5096b5 0xffffffffffe3ffff 0xfffffffffff1ffff

def z136 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xf83fc00703e001e0 0x7c1fe00381f000f0

def z137 : W := mkw 0x4610212290041094 0x230810914802084a 0xba2e802690c0119f 0x5d174013486008cf

def z138 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xfbfee3e690fff19f 0xfdff71f3487ff8cf

def z139 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x7edf3c39ff1f1e7f 0xbf6f9e1cff8f8f3f

def z140 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe3f403903201e61 0x7f1fa01c81900f30

def z141 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x0001001803000600 0x0000800c01800300

def z142 : W := mkw 0x0941d65503b24540 0x84a0eb2a81d922a0 0xfebfdc7f03e37fe1 0x7f5fee3f81f1bff0

def z143 : W := mkw 0x80200c0861130a08 0x4010060430898504 0x44911c1863030e00 0x22488e0c31818700

def z144 : W := mkw 0xa02800002401282a 0x5014000012009415 0xd00200000023e87f 0xe80100000011f43f

def z145 : W := mkw 0x08001a4848000000 0x04000d2424000000 0x00801c406c000000 0x00400e2036000000

def z146 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x01402380901c801e 0x80a011c0480e400f

def z147 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x8ffffffffce001e0 0x47fffffffe7000f0

def z148 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x26dd3c38e31c1600 0x136e9e1c718e0b00

def z149 : W := mkw 0x0e01fb6ad8000000 0x0700fdb56c000000 0x01fdffc0fc000000 0x00feffe07e000000

def z150 : W := mkw 0xefb9f7e2b7fff8bf 0x77dcfbf15bfffc5f 0xffffffe7fffff9ff 0xfffffff3fffffcff

def z151 : W := mkw 0x0000000000000000 0x0000000000000000 0xdbf640409023e01f 0xedfb20204811f00f

def z152 : W := mkw 0x8de1fefde3ffdf59 0xc6f0ff7ef1ffefac 0xffffffffe3fffff9 0xfffffffff1fffffc

def z153 : W := mkw 0x8d21fe68e3b75a18 0x4690ff3471dbad0c 0x76dd7c78e33f7e19 0xbb6ebe3c719fbf0c

def z154 : W := mkw 0x0000000000000000 0x0000000000000000 0x4090404000236000 0x204820200011b000

def z155 : W := mkw 0x86202d2af1171a18 0x43101695788b8d0c 0x7ffdbfbef31f1e19 0xbffedfdf798f8f0c

def z156 : W := mkw 0x43d1c19712e885c5 0xa1e8e0cb897442e2 0x8922c38710e081e6 0x449161c3887040f3

def z157 : W := mkw 0x0f01fb7fdaa00000 0x0780fdbfed500000 0xfffdffffffe00000 0x7ffefffffff00000

def z158 : W := mkw 0x0000040001120000 0x0000020000890000 0x76dd3c38031f1e01 0xbb6e9e1c018f8f00

def z159 : W := mkw 0x0181c08002e88001 0x00c0e04001744000 0xf17de38003fc8000 0xf8bef1c001fe4000

def z160 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x0becbfe6fc000000 0x05f65ff37e000000

def z161 : W := mkw 0x0101c00002a00000 0x0080e00001500000 0xf63dc03803e01e01 0x7b1ee01c01f00f00

def z162 : W := mkw 0x8ca03ee8e15fda19 0x46501f7470afed0c 0x01c03fc0e01fe018 0x80e01fe0700ff00c

def z163 : W := mkw 0x8da1fee8e3ffda19 0x46d0ff7471ffed0c 0xf7fdfff8e3fffe19 0xfbfefffc71ffff0c

def z164 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x00003c00001c0000 0x00001e00000e0000

def z165 : W := mkw 0x8561e83de2a51f58 0xc2b0f41ef1528fac 0xfe3fc03fe3e01ff9 0x7f1fe01ff1f00ffc

def z166 : W := mkw 0x0080008000488001 0x0040004000244000 0xbb6ea38090dc801f 0xddb751c0486e400f

def z167 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xf00b803e03e01fe1 0x7805c01f01f00ff0

def z168 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbffee3e7fcdc919f 0xdfff71f3fe6e48cf

def z169 : W := mkw 0x4b91d7c213fac085 0x25c8ebe109fd6042 0xf9ffffc613ffe186 0xfcffffe309fff0c3

def z170 : W := mkw 0xa169c01526a12d6a 0xd0b4e00a935096b5 0xfebfc07f6fe37fe1 0x7f5fe03fb7f1bff0

def z171 : W := mkw 0x4fd1fbffdaec95d5 0xa7e8fdffed764aea 0xfffffffffffc9fff 0xfffffffffffe4fff

def z172 : W := mkw 0x2008000004002022 0x1004000002001011 0x080200011c000066 0x040100008e000033

def z173 : W := mkw 0xae283b6afc01282a 0x57141db57e009415 0xdff67fc1fc23e87f 0xeffb3fe0fe11f43f

def z174 : W := mkw 0x0941da5d4aa00540 0x84a0ed2ea55002a0 0xfebfdc7f6fe01fe1 0x7f5fee3fb7f00ff0

def z175 : W := mkw 0x0101c40003b20000 0x0080e20001d90000 0xf0fdfc0003ff0000 0xf87efe0001ff8000

def z176 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x8822c00700e001e0 0x44116003807000f0

def z177 : W := mkw 0xa1a8048027fbe82b 0x50d4024013fdf415 0xfff64041ffffe87f 0xfffb2020fffff43f

def z178 : W := mkw 0x4f91f7e293fed095 0x27c8fbf149ff684a 0xfbffffe693fff19f 0xfdfffff349fff8cf

def z179 : W := mkw 0x84202828e0051a18 0x4210141470028d0c 0x06000038e0001e19 0x0300001c70000f0c

def z180 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xf822c00703e01fe1 0x7c11600381f00ff0

def z181 : W := mkw 0x4e91fbffd8488085 0x2748fdffec244042 0x8ffffffffcc08186 0x47fffffffe6040c3

def z182 : W := mkw 0x0600293fd8000000 0x0300149fec000000 0x0e00003ffc000000 0x0700001ffe000000

def z183 : W := mkw 0x40900080004c9095 0x204800400026484a 0xb002000000dc919f 0xd8010000006e48cf

def z184 : W := mkw 0x0981d2c002e8c001 0x04c0e96001746000 0xd1f4c3c000e3e000 0xe8fa61e00071f000

def z185 : W := mkw 0x8521ec28e3b71a18 0x4290f61471db8d0c 0xf6fdfc38e3ff1e19 0xfb7efe1c71ff8f0c

def z186 : W := mkw 0x0140000002a00540 0x80a00000015002a0 0xf002000003e01fe1 0x7801000001f00ff0

def z187 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x2148a3a690dc919e 0x90a451d3486e48cf

def z188 : W := mkw 0x04002c28c1120000 0x0200161460890000 0x76dd3c38e31f0000 0xbb6e9e1c718f8000

def z189 : W := mkw 0x09c1d2d502e8c541 0x84e0e96a817462a0 0x8922c3c700e0e1e0 0x449161e3807070f0

def z190 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x05d17fd9fc000000 0x02e8bfecfe000000

def z191 : W := mkw 0x0040001500000540 0x8020000a800002a0 0x0e02003f00001fe1 0x0701001f80000ff0

def z192 : W := mkw 0xa168000026a12d6a 0xd0b40000135096b5 0xf002000003e3ffff 0xf801000001f1ffff

def z193 : W := mkw 0xa9a9d6c027fbe82b 0x54d4eb6013fdf415 0xffffffc1ffffe87f 0xffffffe0fffff43f

def z194 : W := mkw 0x8e21ff7ff9171a18 0x4710ffbffc8b8d0c 0x0ffdfffffc1f0018 0x87fefffffe0f800c

def z195 : W := mkw 0x0000000000000000 0x0000000000000000 0x00dd3c0000000000 0x006e9e0000000000

def z196 : W := mkw 0xa169c01526a12d6a 0xd0b4e00a935096b5 0xfe3fc03fffe01fff 0x7f1fe01ffff00fff

def z197 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x9ffffffffc00801f 0xcffffffffe00400f

def z198 : W := mkw 0x0400202080041010 0x0200101040020808 0xba6ea02680dc1199 0xdd375013406e08cc

def z199 : W := mkw 0x0741e93fdaa00540 0x83a0f49fed5002a0 0xfe3fc03fffe01fe1 0x7f1fe01ffff00ff0

def z200 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x76dd7c79ef3f7e79 0xbb6ebe3cf79fbf3c

def z201 : W := mkw 0x8020040021171a18 0x40100200108b8d0c 0x761d0038031f1e19 0xbb0e801c018f8f0c

def z202 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf9ffffc703ffe1e0 0xfcffffe381fff0f0

def z203 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xfbffffe603fff181 0xfdfffff301fff8c0

def z204 : W := mkw 0x0001c01500000000 0x0000e00a80000000 0x7e3dc03f03001e01 0x3f1ee01f81800f00

def z205 : W := mkw 0x0000040001120000 0x0000020000890000 0x00c03c00001f0000 0x80601e00000f8000

def z206 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xffffffc103ffe861 0xffffffe081fff430

def z207 : W := mkw 0x0981d2c002e8c001 0x04c0e96001746000 0x0000838000c00000 0x000041c000600000

def z208 : W := mkw 0x01c1c49503fac541 0x80e0e24a81fd62a0 0xfe3fc03f03ffffe1 0xff1fe01f81fffff0

def z209 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x00003f8000000000 0x00001fc000000000

def z210 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xfbffffc093ffe01f 0xfdffffe049fff00f

def z211 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0xb1ecbfc000dfe000 0xd8f65fe0006ff000

def z212 : W := mkw 0x0a01d35718000000 0x0500e9ab8c000000 0x09fdffc71c000000 0x04feffe38e000000

def z213 : W := mkw 0xc6b02daaf15f9a9d 0x635816d578afcd4e 0x77dd3fb8f31f9e1f 0xbbee9fdc798fcf0f

def z214 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xff7ee3a790fc99ff 0xffbf71d3c87e4cff

def z215 : W := mkw 0xc4b02ca8e15f9a9d 0x6258165470afcd4e 0xf6df3c38e3df9f9f 0xfb6f9e1c71efcfcf

def z216 : W := mkw 0x47d1e1b792ec95d5 0xa3e8f0dbc9764aea 0xbb6fa3be93dc979f 0xddb7d1df49ee4bcf

def z217 : W := mkw 0xa0a800802449a82b 0x505400401224d415 0xfffee3c1fcffe87f 0xffff71e0fe7ff43f

def z218 : W := mkw 0x4610212290041094 0x230810914802084a 0x0a0200269000119f 0x05010013480008cf

def z219 : W := mkw 0x47d1e1b792ec95d5 0xa3e8f0dbc9764aea 0xbb6ee3a790fc91ff 0xddb771d3c87e48ff

def z220 : W := mkw 0x0200010210000000 0x0100008108000000 0x0920838610000000 0x049041c308000000

def z221 : W := mkw 0xa1a8048027fbe82b 0x50d4024013fdf415 0xf002000003ffe87f 0xf801000001fff43f

def z222 : W := mkw 0x0801da5d48000000 0x0400ed2ea4000000 0x0ff55c59fc000000 0x07faae2cfe000000

def z223 : W := mkw 0x0001c01500000000 0x0000e00a80000000 0x0009803e00000000 0x0004c01f00000000

def z224 : W := mkw 0xa569ec3de7b73f7a 0xd2b4f61ef3db9fbd 0xfffffc7fffffffff 0xfffffe3fffffffff

def z225 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf120c3c003ffe000 0xf89061e001fff000

def z226 : W := mkw 0x0080008000488001 0x0040004000244000 0xbb6ea3a600dc9181 0xddb751d3006e48c0

def z227 : W := mkw 0x0801da5d48000000 0x0400ed2ea4000000 0x05fdffd96c000000 0x02feffecb6000000

def z228 : W := mkw 0x8160040023b71f58 0xc0b0020011db8fac 0xf002000003ff1ff9 0xf801000001ff8ffc

def z229 : W := mkw 0xe2b801823449a8af 0x715c00c11a24d457 0xdff6c3c7fce3e9ff 0xeffb61e3fe71f4ff

def z230 : W := mkw 0x0901d64003b24000 0x0480eb2001d92000 0x00011c0003000000 0x00008e0001800000

def z231 : W := mkw 0x0e01ff7fd9161210 0x0700ffbfec8b0908 0x2ffdffffff1c1600 0x17feffffff8e0b00

def z232 : W := mkw 0x0000000000000000 0x0000000000000000 0x8822400100200060 0x4411200080100030

def z233 : W := mkw 0x4f91ffffdbfed095 0x27c8ffffedff684a 0xfffffffffffff19f 0xfffffffffffff8cf

def z234 : W := mkw 0x4f91f7e293fed095 0x27c8fbf149ff684a 0xf1fdffe603fff180 0xf8fefff301fff8c0

def z235 : W := mkw 0x84202828e0051a18 0x4210141470028d0c 0x56d40038e0031e19 0xab6a001c70018f0c

def z236 : W := mkw 0xa02800002401282a 0x5014000012009415 0xd92240411c23e87f 0xec9120208e11f43f

def z237 : W := mkw 0x0001c01500000000 0x0000e00a80000000 0x0e3dc03f00000000 0x071ee01f80000000

def z238 : W := mkw 0x068021a290488001 0x034010d148244000 0xbb6ca3a690dc8000 0xddb651d3486e4000

def z239 : W := mkw 0x0fc1ffffdbfac541 0x87e0ffffedfd62a0 0xffffffffffffffe1 0xfffffffffffffff0

def z240 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xf6df3c38e33ffe7f 0xfb6f9e1c719fff3f

def z241 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x0b4223a6901c919f 0x85a111d3480e48cf

def z242 : W := mkw 0x0981d6d503fac001 0x04c0eb6a81fd6000 0xfffdffff03ffe000 0xfffeffff81fff000

def z243 : W := mkw 0x0600212290000000 0x0300109148000000 0x0008a3a600000000 0x000451d300000000

def z244 : W := mkw 0x84202420a1171a18 0x42101210508b8d0c 0x724c2020831f1e19 0xb9261010418f8f0c

def z245 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x7ffdffffff001e01 0x3ffeffffff800f00

def z246 : W := mkw 0xa02800002401282a 0x5014000012009415 0x000000000003e01e 0x800000000001f00f

def z247 : W := mkw 0x0f81fbffdae8c001 0x07c0fdffed746000 0x8ffdfffffce0e000 0x47fefffffe707000

def z248 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x2a0aa3a690dc119f 0x150551d3486e08cf

def z249 : W := mkw 0x0140001502a00540 0x80a0000a815002a0 0xfe02003f03e01fe1 0x7f01001f81f00ff0

def z250 : W := mkw 0x0801d24000000000 0x0400e92000000000 0x0009bf8000000000 0x0004dfc000000000

def z251 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xf7fd7c78e33ffe19 0xfbfebe3c719fff0c

def z252 : W := mkw 0x04002828c0000000 0x0200141460000000 0x00093c3800000000 0x00049e1c00000000

def z253 : W := mkw 0x0e41fb7fd8000540 0x8720fdbfec0002a0 0x0ffffffffc001fe1 0x07fffffffe000ff0

def z254 : W := mkw 0x84202828e0051a18 0x4210141470028d0c 0x761d0038e3001e19 0x3b0e801c71800f0c

def z255 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0xd1f47fc0003fe000 0xe8fa3fe0001ff000

def z256 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x761d803e03c01f81 0x3b0ec01f01e00fc0

def z257 : W := mkw 0xe7f9e1b7b6edbdff 0xf3fcf0dbdb76deff 0xffffe3ffffffffff 0xfffff1ffffffffff

def z258 : W := mkw 0x0600212290041010 0x0300109148020808 0x3b6ca3a6901c1019 0x9db651d3480e080c

def z259 : W := mkw 0xa02800002401282a 0x5014000012009415 0xffff4079ff23fe7f 0xffffa03cff91ff3f

def z260 : W := mkw 0x8161c01522a10d48 0xc0b0e00a915086a4 0xfeffc03fe3e31ff9 0xff7fe01ff1f18ffc

def z261 : W := mkw 0x8460283de0051f58 0xc230141ef0028fac 0x0e02003fe0001ff9 0x0701001ff0000ffc

def z262 : W := mkw 0x40900080004c9095 0x204800400026484a 0x00000000001c801e 0x80000000000e400f

def z263 : W := mkw 0x04002828c0000000 0x0200141460000000 0x00c03c00e0000000 0x00601e0070000000

def z264 : W := mkw 0x4610293fd8041094 0x2308149fec02084a 0x0e02003ffc00119f 0x0701001ffe0008cf

def z265 : W := mkw 0x4f91f7e293fed095 0x27c8fbf149ff684a 0xf1fdffc093ffe01e 0xf8feffe049fff00f

def z266 : W := mkw 0x0140000002a00540 0x80a00000015002a0 0xfe36400103e01fe1 0x7f1b200081f00ff0

def z267 : W := mkw 0x2989d6c007fae023 0x14c4eb6003fd7011 0xf9ffffc11fffe066 0xfcffffe08ffff033

def z268 : W := mkw 0x85a02ca8e3ffda19 0x42d0165471ffed0c 0xf6dd3c38e3fffe19 0xfb6e9e1c71ffff0c

def z269 : W := mkw 0xa628293ffc01282a 0x5314149ffe009415 0x0e02003ffc00087f 0x0701001ffe00043f

def z270 : W := mkw 0x40900080004c9095 0x204800400026484a 0xbb66000090dc919f 0xddb30000486e48cf

def z271 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x06dd3c38e01f0018 0x836e9e1c700f800c

def z272 : W := mkw 0x0400202080041010 0x0200101040020808 0x0200002080001019 0x010000104000080c

def z273 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x20c93c38e31f1618 0x90649e1c718f8b0c

def z274 : W := mkw 0x4090008000488085 0x2048004000244042 0x8002000000c08186 0x40010000006040c3

def z275 : W := mkw 0x8020040021171a18 0x40100200108b8d0c 0x76d40000e31f1e19 0xbb6a0000718f8f0c

def z276 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xb142238090dc919f 0xd8a111c0486e48cf

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0x9164000000008000 0xc8b2000000004000

def z278 : W := mkw 0xe6b821a2b44db8bf 0x735c10d15a26dc5f 0xdff663c1fc3fe87f 0xeffb31e0fe1ff43f

def z279 : W := mkw 0x89a1d6c023ffda19 0x44d0eb6011ffed0c 0xf1fdffc003fffe19 0xf8feffe001ffff0c

def z280 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xc1b1dfc003e3e000 0x60d8efe001f1f000

def z281 : W := mkw 0x0801d25500000000 0x0400e92a80000000 0x0ffdffff00000000 0x07feffff80000000

def z282 : W := mkw 0xc6b02daaf15f9a9d 0x635816d578afcd4e 0xbbeebfa6f0df919f 0xddf75fd3786fc8cf

def z283 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x9b662380901c801f 0xcdb311c0480e400f

def z284 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0e09bfbffc000000 0x0704dfdffe000000

def z285 : W := mkw 0x0140000002a00540 0x80a00000015002a0 0x8002000000e001e0 0x40010000007000f0

def z286 : W := mkw 0x80200c0861130a08 0x4010060430898504 0x00801c0060030000 0x00400e0030018000

def z287 : W := mkw 0x4610212290041094 0x230810914802084a 0x9b6600269000919f 0xcdb30013480048cf

def z288 : W := mkw 0x4fd1f7f793fed5d5 0xa7e8fbfbc9ff6aea 0xffffffff93ffffff 0xffffffffc9ffffff

def z289 : W := mkw 0x088012c00048c001 0x0440096000246000 0x010003c00000e000 0x008001e000007000

def z290 : W := mkw 0xa9e9d6d527fbed6b 0xd4f4eb6a93fdf6b5 0xffffffffffffffff 0xffffffffffffffff

def z291 : W := mkw 0x0000000000000000 0x0000000000000000 0x812040400020e000 0x4090202000107000

def z292 : W := mkw 0x00800480015a8001 0x0040024000ad4000 0xf1fdbf8003df8000 0xf8fedfc001efc000

def z293 : W := mkw 0x0a01d35718000000 0x0500e9ab8c000000 0x0f3dc3ff1c000000 0x079ee1ff8e000000

def z294 : W := mkw 0x0f01ff7fdbb24000 0x0780ffbfedd92000 0x4ffdffffff236000 0x27feffffff91b000

def z295 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xffffc07f03e3ffe1 0xffffe03f81f1fff0

def z296 : W := mkw 0x0601e13790000000 0x0300f09bc8000000 0x0f7de3bf90000000 0x07bef1dfc8000000

def z297 : W := mkw 0x8561ec3de3b71f58 0xc2b0f61ef1db8fac 0x76dd7c39e33f1e79 0xbb6ebe1cf19f8f3c

def z298 : W := mkw 0xcfb1ffeaf3ffda9d 0x67d8fff579ffed4e 0xfffffffef3ffff9f 0xffffffff79ffffcf

def z299 : W := mkw 0x0d81f6e083fed011 0x06c0fb7041ff6808 0xf3fdffe083fff019 0xf9fefff041fff80c

def z300 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xba02002690dc919f 0xdd010013486e48cf

def z301 : W := mkw 0x8c21fe68e1171a18 0x4610ff34708b8d0c 0x77fdfff8e31f1e19 0xbbfefffc718f8f0c

def z302 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0b6dbfbe90000000 0x05b6dfdf48000000

def z303 : W := mkw 0xeeb9fbfffc4db8bf 0x775cfdfffe26dc5f 0xfffffffffcfff9ff 0xfffffffffe7ffcff

def z304 : W := mkw 0x0801d64001120000 0x0400eb2000890000 0x71fdffc0031f0000 0xb8feffe0018f8000

def z305 : W := mkw 0x0000000000000000 0x0000000000000000 0x061d003800000000 0x030e801c00000000

def z306 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xffff3c38f31f9e1f 0xffff9e1c798fcf0f

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0x016ca38000000000 0x00b651c000000000

def z308 : W := mkw 0xe6b821a2b44db8bf 0x735c10d15a26dc5f 0xbf6ea3a7fcdc99ff 0xdfb751d3fe6e4cff

def z309 : W := mkw 0xc6302d2af1171a9c 0x63181695788b8d4e 0x7edf3c3ef31f1f9f 0xbf6f9e1f798f8fcf

def z310 : W := mkw 0x0000080840000000 0x0000040420000000 0x04911c1860000000 0x02488e0c30000000

def z311 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xa92aa3a610dc9186 0x549551d3086e48c3

def z312 : W := mkw 0x47d021a292ec95d5 0xa3e810d149764aea 0xfb6ea3a693fc9fff 0xfdb751d349fe4fff

def z313 : W := mkw 0x0040001500000540 0x8020000a800002a0 0x08020007000001e0 0x04010003800000f0

def z314 : W := mkw 0x46502137900415d4 0xa328109bc8020aea 0x0e02003f90001fff 0x0701001fc8000fff

def z315 : W := mkw 0x0000000000000000 0x0000000000000000 0x304c2000001c0000 0x98261000000e0000

def z316 : W := mkw 0x0981dedd4bfac001 0x04c0ef6ea5fd6000 0xf5fdffd96fffe000 0xfafeffecb7fff000

def z317 : W := mkw 0x0981d2c002e8c001 0x04c0e96001746000 0x81fdffc000e0e000 0x40feffe000707000

def z318 : W := mkw 0xa8a816c0255be82b 0x54540b6012adf415 0x01c03fc0fc1fe01e 0x80e01fe07e0ff00f

def z319 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x77dd3c78ff1ffe1f 0xbbee9e3c7f8fff0f

def z320 : W := mkw 0x80200c0861130a08 0x4010060430898504 0x74dd3c18631f0e00 0xba6e9e0c318f8700

def z321 : W := mkw 0xe6b821a2b44db8bf 0x735c10d15a26dc5f 0xfb6ea3a690fff9ff 0xfdb751d3487ffcff

def z322 : W := mkw 0x8fa1fffffbffda19 0x47d0fffffdffed0c 0xfffdfffffffffe19 0xfffeffffffffff0c

def z323 : W := mkw 0x0541ec3dc3b61750 0x82a0f61ee1db0ba8 0xfe3ffc3f03fc1fe1 0x7f1ffe1f81fe0ff0

def z324 : W := mkw 0xa02800002401282a 0x5014000012009415 0x45d04041fc23e87e 0xa2e82020fe11f43f

def z325 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x26093c38e31c1e19 0x13049e1c718e0f0c

def z326 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0929ffff1c000000 0x0494ffff8e000000

def z327 : W := mkw 0x0941d25502a00540 0x84a0e92a815002a0 0xffffffff03e01fe1 0x7fffffff81f00ff0

def z328 : W := mkw 0x0180048003fac001 0x00c0024001fd6000 0xf16ca38003ffe000 0xf8b651c001fff000

def z329 : W := mkw 0xa02800002401282a 0x5014000012009415 0xcdb240417c23e866 0x66d92020be11f433

def z330 : W := mkw 0x40900080004c9095 0x204800400026484a 0xba2e802600dc919f 0xdd174013006e48cf

def z331 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf0915c4003ffe000 0xf848ae2001fff000

def z332 : W := mkw 0x4e91fbffd84c9095 0x2748fdffec26484a 0xbb6fbfbe90dc919f 0xddb7dfdf486e48cf

def z333 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe3ec02700e019e1 0x7f1f601380700cf0

def z334 : W := mkw 0x8561ec3de3b71f58 0xc2b0f61ef1db8fac 0x76ddbc3ee3df1f99 0xbb6ede1f71ef8fcc

def z335 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x761d3c38031c1e01 0x3b0e9e1c018e0f00

def z336 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600003800001e01 0x0300001c00000f00

def z337 : W := mkw 0x0f81f7e293fac001 0x07c0fbf149fd6000 0xfbfdffe693ffe000 0xfdfefff349fff000

def z338 : W := mkw 0x04002828c0000000 0x0200141460000000 0x0ffd7c79fc000000 0x07febe3cfe000000

def z339 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x6419c03f03e01fe0 0x320ce01f81f00ff0

def z340 : W := mkw 0xa02800002401282a 0x5014000012009415 0xde364001fc20087f 0x6f1b2000fe10043f

def z341 : W := mkw 0x4610212290041094 0x230810914802084a 0x0b6ea3a69000119f 0x05b751d3480008cf

def z342 : W := mkw 0xa02800002401282a 0x5014000012009415 0xdb6600009023e87f 0xedb300004811f43f

def z343 : W := mkw 0x2008000004002022 0x1004000002001011 0xdf3640411c20e867 0x6f9b20208e107433

def z344 : W := mkw 0xe0b80080244db8bf 0x705c00401226dc5f 0xf002000000fff9ff 0xf8010000007ffcff

def z345 : W := mkw 0x0140000002a00540 0x80a00000015002a0 0x2000000003c01780 0x1000000001e00bc0

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00000000023e000 0xe80000000011f000

def z347 : W := mkw 0x0400202080041010 0x0200101040020808 0xbb6e2020901c901f 0xddb71010480e480f

def z348 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf7fdfff803fffe01 0xfbfefffc01ffff00

def z349 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xdff67c41fc3fe87f 0xeffb3e20fe1ff43f

def z350 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x01fdfffe00000000 0x00feffff00000000

def z351 : W := mkw 0x0141c41503b20540 0x80a0e20a81d902a0 0xfefffc3f03ff1fe1 0xff7ffe1f81ff8ff0

def z352 : W := mkw 0x2008000004002022 0x1004000002001011 0x000040410c206060 0x0000202086103030

def z353 : W := mkw 0x4290018210488085 0x214800c108244042 0x9b66838690c0819f 0xcdb341c3486040cf

def z354 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x70ddbf8003df0000 0xb86edfc001ef8000

def z355 : W := mkw 0x4e903bead84c9095 0x27481df56c26484a 0xbbeebfe6fcdc919f 0xddf75ff37e6e48cf

def z356 : W := mkw 0x0000000000000000 0x0000000000000000 0x2009003803001600 0x1004801c01800b00

def z357 : W := mkw 0x2149c01506a02562 0x90a4e00a835012b1 0xff3fc07f1fe0ffe7 0x7f9fe03f8ff07ff3

def z358 : W := mkw 0x8020000020010808 0x4010000010008404 0xdff60000f003881f 0xeffb00007801c40f

def z359 : W := mkw 0x8e21ff7ff9130a08 0x4710ffbffc898504 0x4ffdffffff030e00 0x27feffffff818700

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0xb002000000c01181 0x58010000006008c0

def z361 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x8962a38690dc819e 0xc4b151c3486e40cf

def z362 : W := mkw 0x479025a293fed095 0x23c812d149ff684a 0xfb6ea3a693fff19f 0xfdb751d349fff8cf

def z363 : W := mkw 0x0000000000000000 0x0000000000000000 0x5614000000000801 0x2b0a000000000400

def z364 : W := mkw 0x4e9037e2915ed095 0x27481bf148af684a 0xbbeebfe690dff19f 0xddf75ff3486ff8cf

def z365 : W := mkw 0x4e11fb7fd8041094 0x2708fdbfec02084a 0x0ffffffffc00119f 0x07fffffffe0008cf

def z366 : W := mkw 0x0101c01502a00000 0x0080e00a81500000 0xfe3dc03f03e00000 0x7f1ee01f81f00000

def z367 : W := mkw 0x0e01f37798000000 0x0700f9bbcc000000 0x0b6ce3e79c000000 0x05b671f3ce000000

def z368 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x0000800600c00180 0x00004003006000c0

def z369 : W := mkw 0x0e81ffffd95ac001 0x0740ffffecad6000 0x0ffdfffffc1fe000 0x87fefffffe0ff000

def z370 : W := mkw 0xa068001524012d6a 0xd034000a920096b5 0x0e02003ffc001fff 0x0701001ffe000fff

def z371 : W := mkw 0x8020040021171a18 0x40100200108b8d0c 0x00000000001f0018 0x80000000000f800c

def z372 : W := mkw 0xa02800002401282a 0x5014000012009415 0x0ff44041fc03e01e 0x87fa2020fe01f00f

def z373 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0xbffffffffcc01181 0x5ffffffffe6008c0

def z374 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x21c9bfc003dfe000 0x90e4dfe001eff000

def z375 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x01c03c40fc1fe01e 0x80e01e207e0ff00f

def z376 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xff7fc03f93e09fff 0xffbfe01fc9f04fff

def z377 : W := mkw 0x8ca03ee8e15fda19 0x46501f7470afed0c 0x77dd3ff8e31ffe19 0xbbee9ffc718fff0c

def z378 : W := mkw 0xa02800002401282a 0x5014000012009415 0x008000406c036000 0x004000203601b000

def z379 : W := mkw 0x46902daad15e9295 0x234816d568af494a 0xbb6fbfbe93dc979f 0xddb7dfdf49ee4bcf

def z380 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x64993c38631f1e00 0x324c9e1c318f8f00

def z381 : W := mkw 0x0901d64003b24000 0x0480eb2001d92000 0xf0bddc4003e36000 0x785eee2001f1b000

def z382 : W := mkw 0x0541e83dc2a00540 0x82a0f41ee15002a0 0xfefffc3fe3e01fe1 0x7f7ffe1ff1f00ff0

def z383 : W := mkw 0x04002828c0000000 0x0200141460000000 0x76dd3c38e3001e01 0x3b6e9e1c71800f00

def z384 : W := mkw 0x8e21fb7ff8051a18 0x4710fdbffc028d0c 0x0ffdfffffc001e19 0x07fefffffe000f0c

def z385 : W := mkw 0x0200011718000000 0x0100008b8c000000 0x080000071c000000 0x040000038e000000

def z386 : W := mkw 0xa129c00026a1282a 0x5094e00013509415 0xffffc041ffe3e87f 0xffffe020fff1f43f

def z387 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xfeff7c39e33f1e79 0xff7fbe1cf19f8f3c

def z388 : W := mkw 0x01c0048003fac541 0x80e0024001fd62a0 0xf002000003ffffe1 0xf801000001fffff0

def z389 : W := mkw 0x0101c00002a00000 0x0080e00001500000 0xfa3fc02603e01181 0x7d1fe01301f008c0

def z390 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xfffdffc1ffffe000 0xfffeffe0fffff000

def z391 : W := mkw 0x4f91f3e292ecd095 0x27c8f9f14976684a 0xbb6ee3e690fcf19f 0xddb771f3487e78cf

def z392 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x334c23a0901c901f 0x99a611d0480e480f

def z393 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x4ffdffffff200e60 0x27feffffff900730

def z394 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a0200009000001f 0x050100004800000f

def z395 : W := mkw 0x0a01d35718000000 0x0500e9ab8c000000 0x0000838600000000 0x000041c300000000

def z396 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x44d13c18e31f0e18 0xa2689e0c718f870c

def z397 : W := mkw 0xa8a816c0255be82b 0x54540b6012adf415 0xdff67fc1fc3fe87f 0xeffb3fe0fe1ff43f

def z398 : W := mkw 0xa02800002401282a 0x5014000012009415 0xde3640010023e87f 0xef1b20008011f43f

def z399 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xf03dc03e03e01780 0x781ee01f01f00bc0

def z400 : W := mkw 0x0000000000000000 0x0000000000000000 0x2008802600c01180 0x10044013006008c0

def z401 : W := mkw 0x84a02ca8e15f9a19 0x4250165470afcd0c 0xf7fdbfb8e3df9e19 0xfbfedfdc71efcf0c

def z402 : W := mkw 0x4290018210488085 0x214800c108244042 0xbb2e83a610c09187 0x5d9741d3086048c3

def z403 : W := mkw 0x40900080004c9095 0x204800400026484a 0xb16ea38000dc919f 0xd8b751c0006e48cf

def z404 : W := mkw 0xa9a9d2c026e9e82b 0x54d4e9601374f415 0xdff6c3c1fce3e87f 0xeffb61e0fe71f43f

def z405 : W := mkw 0x42900182104c9095 0x214800c10826484a 0xb922838610dc919f 0xdc9141c3086e48cf

def z406 : W := mkw 0xa929d64027b3682a 0x5494eb2013d9b415 0x44915c416f236860 0x2248ae20b791b430

def z407 : W := mkw 0xaa29d3573c01282a 0x5514e9ab9e009415 0xdff6c3c7fc23e87f 0xeffb61e3fe11f43f

def z408 : W := mkw 0xafa9fffffffbe82b 0x57d4fffffffdf415 0xffffffffffffe87f 0xfffffffffffff43f

def z409 : W := mkw 0x0040001500000540 0x8020000a800002a0 0xbe2e803f00c01fe1 0x5f17401f80600ff0

def z410 : W := mkw 0x09c1d6c003fac541 0x84e0eb6001fd62a0 0xf1ffffc003ffffe1 0xf8ffffe001fffff0

def z411 : W := mkw 0x4e91f3f7984c9095 0x2748f9fbcc26484a 0xbb6ee3e79cdc919f 0xddb771f3ce6e48cf

def z412 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0x2009bfbe03dc1780 0x1004dfdf01ee0bc0

def z413 : W := mkw 0xe6b821a2b44db8bf 0x735c10d15a26dc5f 0xbbeea3e6fcdff19f 0xddf751f37e6ff8cf

def z414 : W := mkw 0x469029aad04c9095 0x234814d56826484a 0xbfffbfbef0dc919f 0xdfffdfdf786e48cf

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0x4411001803000e00 0x2208800c01800700

def z416 : W := mkw 0x4610212290041094 0x230810914802084a 0x000000009000001e 0x000000004800000f

def z417 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xba2ea3a600dc1181 0x5d1751d3006e08c0

def z418 : W := mkw 0xae29fb7ffc01282a 0x5714fdbffe009415 0x4ffdfffffc236860 0x27fefffffe11b430

def z419 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xde36c00700e009e1 0x6f1b6003807004f0

def z420 : W := mkw 0x0001c01500000000 0x0000e00a80000000 0x0411401900000000 0x0208a00c80000000

def z421 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x81e0ffc000ffe000 0xc0f07fe0007ff000

def z422 : W := mkw 0x8e203f6af9171a18 0x47101fb57c8b8d0c 0x01c03fc0fc1f0018 0x80e01fe07e0f800c

def z423 : W := mkw 0x0180048003fac001 0x00c0024001fd6000 0xf0dd3c0003ffe000 0xf86e9e0001fff000

def z424 : W := mkw 0x4290018210488085 0x214800c108244042 0x0000838600c00180 0x000041c3006000c0

def z425 : W := mkw 0x8f61ff7ffbb71f58 0xc7b0ffbffddb8fac 0xffffffffffff1ff9 0xffffffffffff8ffc

def z426 : W := mkw 0x0181c48003fac001 0x00c0e24001fd6000 0xf03dc00003ffe000 0xf81ee00001fff000

def z427 : W := mkw 0x0a01d35718000000 0x0500e9ab8c000000 0x0ff4c3c7fc000000 0x07fa61e3fe000000

def z428 : W := mkw 0x04002828c0041210 0x0200141460020908 0x0000003800001600 0x0000001c00000b00

def z429 : W := mkw 0xae29fb7ffc01282a 0x5714fdbffe009415 0x0ffdfffffc03e01e 0x87fefffffe01f00f

def z430 : W := mkw 0x0f81ffffdbfac001 0x07c0ffffedfd6000 0x2009bfbe03dc0000 0x1004dfdf01ee0000

def z431 : W := mkw 0x8020040021130a08 0x4010020010898504 0x4000000003030e00 0x2000000001818700

def z432 : W := mkw 0x0800124000000000 0x0400092000000000 0x01c03fc000000000 0x00e01fe000000000

def z433 : W := mkw 0x86202d3ff9171a18 0x4310169ffc8b8d0c 0x7edd3c3fff1f1e19 0xbf6e9e1fff8f8f0c

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0xb02c800000c00000 0x5816400000600000

def z435 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x0000400100200060 0x0000200080100030

def z436 : W := mkw 0xa02800002401282a 0x5014000012009415 0xd1c20040fc23e87f 0xe8e100207e11f43f

def z437 : W := mkw 0xc6b029aaf04d9a9d 0x635814d57826cd4e 0xbf6ea3bef0dc9f9f 0xdfb751df786e4fcf

def z438 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0xdffffffffc200861 0x6ffffffffe100430

def z439 : W := mkw 0x0901d64003b24000 0x0480eb2001d92000 0x70dd7c40033f6000 0xb86ebe20019fb000

def z440 : W := mkw 0x0600212290000000 0x0300109148000000 0x0ffce3e7fc000000 0x07fe71f3fe000000

def z441 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xb16dbf8003dc8000 0xd8b6dfc001ee4000

def z442 : W := mkw 0xceb1fffff95f9a9d 0x6758fffffcafcd4e 0xffffffffffdf9f9f 0xffffffffffefcfcf

def z443 : W := mkw 0x0e01fb7fd8041010 0x0700fdbfec020808 0x3ffdfffffc1c1019 0x9ffefffffe0e080c

def z444 : W := mkw 0x8020000020010808 0x4010000010008404 0x00c00000e0030018 0x806000007001800c

def z445 : W := mkw 0x0101c00002a00000 0x0080e00001500000 0xf1fdc04003e3e000 0xf8fee02001f1f000

def z446 : W := mkw 0x04002828c0000000 0x0200141460000000 0x06000038e0000000 0x0300001c70000000

def z447 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf03dff8003fc0000 0x781effc001fe0000

def z448 : W := mkw 0x469025a2915e9095 0x234812d148af484a 0xfbffbfa693df919f 0xfdffdfd349efc8cf

def z449 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x70dd3c38031f1600 0xb86e9e1c018f8b00

def z450 : W := mkw 0x0e003b7fd8000000 0x07001dbfec000000 0x0fc03ffffc000000 0x07e01ffffe000000

def z451 : W := mkw 0xa4282828e4053a3a 0x5214141472029d1d 0xdff64079fc23fe7f 0xeffb203cfe11ff3f

def z452 : W := mkw 0x81a0048023ffda19 0x40d0024011ffed0c 0xf000000003fffe19 0xf800000001ffff0c

def z453 : W := mkw 0x0400202080000000 0x0200101040000000 0x024c202080000000 0x0126101040000000

def z454 : W := mkw 0xc6b025a2b15f9a9d 0x635812d158afcd4e 0xfb6ea3a693df9f9f 0xfdb751d349efcfcf

def z455 : W := mkw 0x0b81d7d71bfac001 0x05c0ebeb8dfd6000 0xf9fdffc71fffe000 0xfcfeffe38ffff000

def z456 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xba2f803e03c01781 0x5d17c01f01e00bc0

def z457 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x21fdffc003dc0000 0x10feffe001ee0000

def z458 : W := mkw 0x84202828e0010808 0x4210141470008404 0x56dd3c38e0030819 0xab6e9e1c7001840c

def z459 : W := mkw 0x80200c0861130a08 0x4010060430898504 0x769d1c3863031e01 0x3b4e8e1c31818f00

def z460 : W := mkw 0xe6382122b40538be 0x731c10915a029c5f 0xdff64067fc23f9ff 0xeffb2033fe11fcff

def z461 : W := mkw 0x4e903bead84c9095 0x27481df56c26484a 0x01c03fc0fc1c801e 0x80e01fe07e0e400f

def z462 : W := mkw 0x8e21fb7ff8010808 0x4710fdbffc008404 0x5ffdfffffc030819 0xaffefffffe01840c

def z463 : W := mkw 0xa4282828e401282a 0x5214141472009415 0xdfff7c79fc23e87f 0xefffbe3cfe11f43f

def z464 : W := mkw 0x4791e1a292ec9095 0x23c8f0d14976484a 0xfb7fe3a693fc919f 0xfdbff1d349fe48cf

def z465 : W := mkw 0x0040001500000540 0x8020000a800002a0 0xde36403f00201fe1 0x6f1b201f80100ff0

def z466 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x0b6ca3a6901c801e 0x85b651d3480e400f

def z467 : W := mkw 0x0600212290000000 0x0300109148000000 0x0140238090000000 0x00a011c048000000

def z468 : W := mkw 0x0000000000000000 0x0000000000000000 0x8822800600c00180 0x44114003006000c0

def z469 : W := mkw 0x0041c01500000540 0x8020e00a800002a0 0x0e3fc03f00001fe1 0x071fe01f80000ff0

def z470 : W := mkw 0x4e9037e2915ed095 0x27481bf148af684a 0x01c03fc0901fe01e 0x80e01fe0480ff00f

def z471 : W := mkw 0x2008000004002022 0x1004000002001011 0x800200000020e066 0x4001000000107033

def z472 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xffffc07fffe01fe1 0x7fffe03ffff00ff0

def z473 : W := mkw 0x2008000004002022 0x1004000002001011 0x010000401c00e006 0x008000200e007003

def z474 : W := mkw 0x048020a0804c9011 0x0240105040264808 0xb36ca3a080dc9019 0xd9b651d0406e480c

def z475 : W := mkw 0x8161c41523b71f58 0xc0b0e20a91db8fac 0xfe3fc03f03ff1ff9 0xff1fe01f81ff8ffc

def z476 : W := mkw 0xc0b00480215f9a9d 0x6058024010afcd4e 0xf002000003df9f9f 0xf801000001efcfcf

def z477 : W := mkw 0xa02800002401282a 0x5014000012009415 0x4e924041fc23687f 0x27492020fe11b43f

def z478 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x06c03c38e01f1e19 0x83601e1c700f8f0c

def z479 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xfeffbc3ee3df1f99 0xff7fde1f71ef8fcc

def z480 : W := mkw 0xa169c01526a12d6a 0xd0b4e00a935096b5 0x449140596f236e60 0x2248a02cb791b730

def z481 : W := mkw 0x0000000000000000 0x0000000000000000 0xbb6e802690c0919f 0xddb74013486048cf

def z482 : W := mkw 0x0000000000000000 0x0000000000000000 0x320c002000001001 0x1906001000000800

def z483 : W := mkw 0x0541ec3dc3b61750 0x82a0f61ee1db0ba8 0x2009bc3e03dc1780 0x1004de1f01ee0bc0

def z484 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x2e0b803f03c01fe1 0x1705c01f81e00ff0

def z485 : W := mkw 0xa02800002401282a 0x5014000012009415 0xd49240416c23e87f 0xea492020b611f43f

def z486 : W := mkw 0x0901d64003b24000 0x0480eb2001d92000 0x41fdffc003236000 0x20feffe00191b000

def z487 : W := mkw 0xa02800002401282a 0x5014000012009415 0xd6d60000e023e87f 0xeb6b00007011f43f

def z488 : W := mkw 0x0600292ad0000000 0x0300149568000000 0x0ffdbfbef0000000 0x07fedfdf78000000

def z489 : W := mkw 0x8020000020010808 0x4010000010008404 0xdef64001e0230879 0xef7b2000f011843c

def z490 : W := mkw 0x0e01ff7fd9161210 0x0700ffbfec8b0908 0x2009bfbe031c1600 0x1004dfdf018e0b00

def z491 : W := mkw 0x84202828e0051a18 0x4210141470028d0c 0x06dd3c38e0001e19 0x036e9e1c70000f0c

def z492 : W := mkw 0x41d0008002ec95d5 0xa0e8004001764aea 0xf002000003fc9fff 0xf801000001fe4fff

def z493 : W := mkw 0x0000000000000000 0x0000000000000000 0xd034400000200000 0x681a200000100000

def z494 : W := mkw 0x8020040021130808 0x4010020010898404 0x76dd3c00e31f0819 0xbb6e9e00718f840c

def z495 : W := mkw 0x0001c01500000000 0x0000e00a80000000 0x0ffdc07ffc000000 0x07fee03ffe000000

def z496 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xb16ca38090dc801e 0xd8b651c0486e400f

def z497 : W := mkw 0x0001c00000000000 0x0000e00000000000 0x003dc00000000000 0x001ee00000000000

def z498 : W := mkw 0xa0280c0865132a2a 0x5014060432899515 0xdff75c59ff23ee7f 0xeffbae2cff91f73f

def z499 : W := mkw 0x00000c0841120200 0x0000060420890100 0x00011c1803000600 0x00008e0c01800300

def z500 : W := mkw 0x0e81fbffd8488001 0x0740fdffec244000 0xbffdfffffcdc8000 0xdffefffffe6e4000

def z501 : W := mkw 0x43d1c19712e885c5 0xa1e8e0cb897442e2 0xff3fc3bf13e09fe7 0x7f9fe1df89f04ff3

def z502 : W := mkw 0x00800480015ac001 0x0040024000ad6000 0x00000000001fe000 0x80000000000ff000

def z503 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf009bf8003ffe000 0xf804dfc001fff000

def z504 : W := mkw 0x0000001500000000 0x0000000a80000000 0x0e00003f00000000 0x0700001f80000000

def z505 : W := mkw 0x0140000002a00540 0x80a00000015002a0 0xf61f003803e01fe1 0x7b0f801c01f00ff0

def z506 : W := mkw 0x0d81fee8c3fed211 0x06c0ff7461ff6908 0xf1fdfff803fff600 0xf8fefffc01fffb00

def z507 : W := mkw 0x4010000000041094 0x200800000002084a 0x000200000000119f 0x00010000000008cf

def z508 : W := mkw 0x84202828e0051a18 0x4210141470028d0c 0x364c2038e01c1e19 0x9b26101c700e0f0c

def z509 : W := mkw 0x0140000002a00540 0x80a00000015002a0 0x4000000003200e60 0x2000000001900730

def z510 : W := mkw 0x0a00134218000000 0x050009a10c000000 0x010003c01c000000 0x008001e00e000000

def z511 : W := mkw 0x0000000000000000 0x0000000000000000 0xdff640410023e861 0xeffb20208011f430

def z512 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0xdffdfffffc23e000 0xeffefffffe11f000

def z513 : W := mkw 0x0100040003b24000 0x0080020001d92000 0x4000000003236000 0x200000000191b000

def z514 : W := mkw 0xa829da5d6c01282a 0x5414ed2eb6009415 0x44915c596c236860 0x2248ae2cb611b430

def z515 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a02002600001181 0x05010013000008c0

def z516 : W := mkw 0x41d1c09502ec95d5 0xa0e8e04a81764aea 0xfe3fc03f03fc9fff 0xff1fe01f81fe4fff

def z517 : W := mkw 0x0000000000000000 0x0000000000000000 0x8922000010008006 0x4491000008004003

def z518 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x8e3fc03f00e001e0 0x471fe01f807000f0

def z519 : W := mkw 0x0040001500000540 0x8020000a800002a0 0x0000003e00001780 0x0000001f00000bc0

def z520 : W := mkw 0x0040001500000540 0x8020000a800002a0 0x7e1f003f03001fe1 0x3f0f801f81800ff0

def z521 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x07dd3ff8fc000000 0x03ee9ffc7e000000

def z522 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x46911c38e3031e19 0x23488e1c71818f0c

def z523 : W := mkw 0x0000000000000000 0x0000000000000000 0xd002000000200861 0x6801000000100430

def z524 : W := mkw 0x0080008000488001 0x0040004000244000 0x01402380001c8000 0x80a011c0000e4000

def z525 : W := mkw 0x8020000020010808 0x4010000010008404 0xd7f44040e023e819 0xebfa20207011f40c

def z526 : W := mkw 0xa02800002401282a 0x5014000012009415 0x4ff44041fc236860 0x27fa2020fe11b430

def z527 : W := mkw 0xa4282020a405383a 0x5214101052029c1d 0xfffe6061fc3ff87f 0xffff3030fe1ffc3f

def z528 : W := mkw 0xc6b02daaf15f9a9d 0x635816d578afcd4e 0x76ddbfbee3df1f99 0xbb6edfdf71ef8fcc

def z529 : W := mkw 0x0e01ff7fd9120000 0x0700ffbfec890000 0x7ffdffffff1f0000 0xbffeffffff8f8000

def z530 : W := mkw 0x0600293fd8000000 0x0300149fec000000 0x0f6ca3bffc000000 0x07b651dffe000000

def z531 : W := mkw 0x0801d24000000000 0x0400e92000000000 0x0120c3c000000000 0x009061e000000000

def z532 : W := mkw 0x4610212290041094 0x230810914802084a 0x3a4e2026901c119f 0x9d271013480e08cf

def z533 : W := mkw 0x0640293fd8000540 0x8320149fec0002a0 0x0e02003ffc001fe1 0x0701001ffe000ff0

def z534 : W := mkw 0xa02800002401282a 0x5014000012009415 0xd5f440416c23e860 0xeafa2020b611f430

def z535 : W := mkw 0xa169c01526a12d6a 0xd0b4e00a935096b5 0xdff6c047fce3e9ff 0xeffb6023fe71f4ff

def z536 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x76000038e31f1e19 0xbb00001c718f8f0c

def z537 : W := mkw 0x0000040001120000 0x0000020000890000 0x20093c00031c0000 0x10049e00018e0000

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0x01c000400003e000 0x80e000200001f000

def z539 : W := mkw 0x4b91d3c212e8c085 0x25c8e9e109746042 0x8922c3c610e0e186 0x449161e3087070c3

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0x9a26000000000001 0x4d13000000000000

def z541 : W := mkw 0x4e91f3e2904c9095 0x2748f9f14826484a 0xbbffffe690dc919f 0xddfffff3486e48cf

def z542 : W := mkw 0x4f91f7e293fed095 0x27c8fbf149ff684a 0x2009bfa603dc1180 0x1004dfd301ee08c0

def z543 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x70093c38031f1e19 0xb8049e1c018f8f0c

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x701d000003000000 0x380e800001800000

def z545 : W := mkw 0x0881d6c0015ac001 0x0440eb6000ad6000 0x01fdffc0001fe000 0x80feffe0000ff000

def z546 : W := mkw 0xae29fb7ffc01282a 0x5714fdbffe009415 0x0ffffffffc00087f 0x07fffffffe00043f

def z547 : W := mkw 0x4290018210488085 0x214800c108244042 0xb96ea38610dc8186 0xdcb751c3086e40c3

def z548 : W := mkw 0x0741e13792a00540 0x83a0f09bc95002a0 0xff7fe3bf93e01fe1 0x7fbff1dfc9f00ff0

def z549 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xfe3fffbf03e01fe1 0x7f1fffdf81f00ff0

def z550 : W := mkw 0xa029c0152401282a 0x5014e00a92009415 0xdfffc07ffc23e87f 0xefffe03ffe11f43f

def z551 : W := mkw 0x4a91d3d718488085 0x2548e9eb8c244042 0x8922c3c71cc08186 0x449161e38e6040c3

def z552 : W := mkw 0xc6b02daaf15f9a9d 0x635816d578afcd4e 0x01c03f80f01f801e 0x80e01fc0780fc00f

def z553 : W := mkw 0x0c01fa68c0000000 0x0600fd3460000000 0x07fdfff8e0000000 0x03fefffc70000000

def z554 : W := mkw 0xa028040025173a3a 0x50140200128b9d1d 0xfff64041ff3ffe7f 0xfffb2020ff9fff3f

def z555 : W := mkw 0x84602c3de1171f58 0xc230161ef08b8fac 0x7edf3c3fe31f1ff9 0xbf6f9e1ff18f8ffc

def z556 : W := mkw 0x84202020a0051818 0x4210101050028c0c 0x76dc2020e01f1819 0xbb6e1010700f8c0c

def z557 : W := mkw 0xa168000026a12d6a 0xd0b40000135096b5 0xfff64041ffe3ffff 0xfffb2020fff1ffff

def z558 : W := mkw 0x0a01db5f58000000 0x0500edafac000000 0x0db1dfdf7c000000 0x06d8efefbe000000

def z559 : W := mkw 0xa02800002401282a 0x5014000012009415 0x00000000fc00001e 0x000000007e00000f

def z560 : W := mkw 0x0000040001120000 0x0000020000890000 0x40911c0003030000 0x20488e0001818000

def z561 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a2c802600000000 0x0516401300000000

def z562 : W := mkw 0xa02804002513282a 0x5014020012899415 0xffff7c41ff3fe87f 0xffffbe20ff9ff43f

def z563 : W := mkw 0x8020040021171a18 0x40100200108b8d0c 0x70dd3c00031f1e19 0xb86e9e00018f8f0c

def z564 : W := mkw 0x0000000000000000 0x0000000000000000 0x900200000000801f 0xc80100000000400f

def z565 : W := mkw 0x0600212290000000 0x0300109148000000 0x9b6ea3a69000801f 0xcdb751d34800400f

def z566 : W := mkw 0x0080008000488001 0x0040004000244000 0xf1fce3c000ffe000 0xf8fe71e0007ff000

def z567 : W := mkw 0x46d021b7904c95d5 0xa36810dbc8264aea 0xbf6ea3bf90dc9fff 0xdfb751dfc86e4fff

def z568 : W := mkw 0x4e91fbffd84c9095 0x2748fdffec26484a 0x0ffdfffffc1c801e 0x87fefffffe0e400f

def z569 : W := mkw 0x0000000000000000 0x0000000000000000 0xdff44041fc23e000 0xeffa2020fe11f000

def z570 : W := mkw 0x2989d2c006e8e023 0x14c4e96003747011 0x8922c3c11ce0e066 0x449161e08e707033

def z571 : W := mkw 0xae283b6afc01282a 0x57141db57e009415 0x01c03fc0fc03e01e 0x80e01fe07e01f00f

def z572 : W := mkw 0x8821de5d69130a08 0x4410ef2eb4898504 0x44915c596f030e00 0x2248ae2cb7818700

def z573 : W := mkw 0x0601e93fd8000000 0x0300f49fec000000 0x0e3dc03ffc000000 0x071ee01ffe000000

def z574 : W := mkw 0x0941da5d4aa00540 0x84a0ed2ea55002a0 0x44915c596f200e60 0x2248ae2cb7900730

def z575 : W := mkw 0x8da1fee8e3ffda19 0x46d0ff7471ffed0c 0x76ddbfb8e3df1e19 0xbb6edfdc71ef8f0c

def z576 : W := mkw 0x0180048003fac001 0x00c0024001fd6000 0xf1f4404003ffe000 0xf8fa202001fff000

def z577 : W := mkw 0xa02800002401282a 0x5014000012009415 0x040000016c000860 0x02000000b6000430

def z578 : W := mkw 0xa02800002401282a 0x5014000012009415 0x9be60040fc03e01f 0xcdf300207e01f00f

def z579 : W := mkw 0xa02800002401282a 0x5014000012009415 0x89e24041fc23e07e 0xc4f12020fe11f03f

def z580 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xf413401903e01fe1 0x7a09a00c81f00ff0

def z581 : W := mkw 0x4290018210488085 0x214800c108244042 0x0100038010008006 0x008001c008004003

def z582 : W := mkw 0x2008000004002022 0x1004000002001011 0x9b6640419c20e07f 0xcdb32020ce10703f

def z583 : W := mkw 0x47d1e1b792ec95d5 0xa3e8f0dbc9764aea 0x2009a3be03dc1780 0x1004d1df01ee0bc0

def z584 : W := mkw 0x2008000004002022 0x1004000002001011 0xd9f640411c23e066 0xecfb20208e11f033

def z585 : W := mkw 0xe6b82daaf55fbabf 0x735c16d57aafdd5f 0xffffffffffffffff 0xffffffffffffffff

def z586 : W := mkw 0x0901de5d4bb24000 0x0480ef2ea5d92000 0x44915c596f236000 0x2248ae2cb791b000

def z587 : W := mkw 0x0981d2c002e8c001 0x04c0e96001746000 0xf13dc3c003e0e000 0x789ee1e001f07000

def z588 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x2b6ca3a690dc1180 0x15b651d3486e08c0

def z589 : W := mkw 0x0c01fa7dc8000000 0x0600fd3ee4000000 0x06dd7c79ec000000 0x036ebe3cf6000000

def z590 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0e915c7ffc000000 0x0748ae3ffe000000

def z591 : W := mkw 0x0600212290000000 0x0300109148000000 0xbb6ea3a690c01181 0x5db751d3486008c0

def z592 : W := mkw 0x0600293fd8000000 0x0300149fec000000 0x0edd3c3ffc000000 0x076e9e1ffe000000

def z593 : W := mkw 0x0801d24000000000 0x0400e92000000000 0x00915c4000000000 0x0048ae2000000000

def z594 : W := mkw 0xa02800002401282a 0x5014000012009415 0xde020001fc23e87f 0xef010000fe11f43f

def z595 : W := mkw 0x469029bfd84c9095 0x234814dfec26484a 0xbf6ea3bffcdc919f 0xdfb751dffe6e48cf

def z596 : W := mkw 0x669821a2944cb0b7 0x334c10d14a26585b 0xbb6ee3e79cfcf1ff 0xddb771f3ce7e78ff

def z597 : W := mkw 0x0e803fead95ac001 0x07401ff56cad6000 0x01c03fc0fc1fe000 0x80e01fe07e0ff000

def z598 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x8e22c03f00e01fe1 0x4711601f80700ff0

def z599 : W := mkw 0x09c1d2d502e8c541 0x84e0e96a817462a0 0xff3fc3ff03e0ffe1 0x7f9fe1ff81f07ff0

def z600 : W := mkw 0x0600293fd8000000 0x0300149fec000000 0x0000003e00000000 0x0000001f00000000

def z601 : W := mkw 0xa9a9d6c027fbe82b 0x54d4eb6013fdf415 0xf5fdffc16fffe860 0xfafeffe0b7fff430

def z602 : W := mkw 0x85602c28e3b71f58 0xc2b0161471db8fac 0xf6df3c38e3ff1ff9 0xfb6f9e1c71ff8ffc

def z603 : W := mkw 0x0941d65503b24540 0x84a0eb2a81d922a0 0x44915c5903236e60 0x2248ae2c8191b730

def z604 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x324ca3a680dc1199 0x992651d3406e08cc

def z605 : W := mkw 0x0801da5d48000000 0x0400ed2ea4000000 0x00011c1800000000 0x00008e0c00000000

def z606 : W := mkw 0x0180008002e8c001 0x00c0004001746000 0x8000000000e0e000 0x4000000000707000

def z607 : W := mkw 0xa02800002401282a 0x5014000012009415 0x5ed60001fc03087f 0xaf6b0000fe01843f

def z608 : W := mkw 0x2e09fb7fdc002022 0x1704fdbfee001011 0x8ffffffffc20e066 0x47fffffffe107033

def z609 : W := mkw 0x04002828c0041010 0x0200141460020808 0x36dd3c38e01c1019 0x9b6e9e1c700e080c

def z610 : W := mkw 0x2a09d3571c002022 0x1504e9ab8e001011 0x8922c3c71c20e066 0x449161e38e107033

def z611 : W := mkw 0x47d1e1b792ec95d5 0xa3e8f0dbc9764aea 0xfe3fe3bf03fc1fe1 0x7f1ff1df81fe0ff0

def z612 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x2009bfbe03c01780 0x1004dfdf01e00bc0

def z613 : W := mkw 0x0000000000041010 0x0000000000020808 0x30000000001c1019 0x98000000000e080c

def z614 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x2e3dc03f03c01780 0x171ee01f81e00bc0

def z615 : W := mkw 0x0101c00002a00000 0x0080e00001500000 0x8020c00000e00000 0x4010600000700000

def z616 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0e3dffbf00000000 0x071effdf80000000

def z617 : W := mkw 0x0901d24002a04000 0x0480e92001502000 0x0000404000206000 0x0000202000103000

def z618 : W := mkw 0xa02800002401282a 0x5014000012009415 0x8f224041fc20e87f 0x47912020fe10743f

def z619 : W := mkw 0x0101c00002a00000 0x0080e00001500000 0xfe3fc00103e00861 0x7f1fe00081f00430

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0x7000000003001e01 0x3800000001800f00

def z621 : W := mkw 0xa6282122b401282a 0x531410915a009415 0xdffee3e7fc23e87f 0xefff71f3fe11f43f

def z622 : W := mkw 0xa628293ffc01282a 0x5314149ffe009415 0xdff6407ffc23e87f 0xeffb203ffe11f43f

def z623 : W := mkw 0x8020080860010a08 0x4010040430008504 0x0400001860000e00 0x0200000c30000700

def z624 : W := mkw 0x8e21ff7ff9171a18 0x4710ffbffc8b8d0c 0x76ddbfbee31f1e19 0xbb6edfdf718f8f0c

def z625 : W := mkw 0x0400202080041010 0x0200101040020808 0x00402000801c0018 0x80201000400e000c

def z626 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xf43dc01903e00e60 0x7a1ee00c81f00730

def z627 : W := mkw 0x4210010210000084 0x2108008108000042 0x0802000610000186 0x04010003080000c3

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe3f803e03c01f81 0x7f1fc01f01e00fc0

def z629 : W := mkw 0xa02800002401282a 0x5014000012009415 0x0fc20041fc03e87f 0x87e10020fe01f43f

def z630 : W := mkw 0x0000040001120000 0x0000020000890000 0x70000000031f0000 0xb8000000018f8000

def z631 : W := mkw 0xa02800002401282a 0x5014000012009415 0x0ff64041fc00087f 0x07fb2020fe00043f

def z632 : W := mkw 0x01c1c09502e88541 0x80e0e04a817442a0 0xff7fe3bf03fc9fe1 0xffbff1df81fe4ff0

def z633 : W := mkw 0x0001c01500000000 0x0000e00a80000000 0xbe3fc03f00c01181 0x5f1fe01f806008c0

def z634 : W := mkw 0xe6b821a2b44db8bf 0x735c10d15a26dc5f 0x01c023c0fc1fe01e 0x80e011e07e0ff00f

def z635 : W := mkw 0x0001c01500000000 0x0000e00a80000000 0x0820c00700000000 0x0410600380000000

def z636 : W := mkw 0x0801d25508000000 0x0400e92a84000000 0x000040410c000000 0x0000202086000000

def z637 : W := mkw 0x0541e03582a41550 0x82a0f01ac1520aa8 0xfe7fe03f83fc1ff9 0xff3ff01fc1fe0ffc

def z638 : W := mkw 0x0141c00002a00540 0x80a0e000015002a0 0xf03fc00003e01fe1 0x781fe00001f00ff0

def z639 : W := mkw 0x0901d24002a00000 0x0480e92001500000 0xf1fdffc003e00000 0x78feffe001f00000

def z640 : W := mkw 0xa02800002401282a 0x5014000012009415 0x56d44041ec236879 0xab6a2020f611b43c

def z641 : W := mkw 0xa02800002401282a 0x5014000012009415 0x4000000000236860 0x200000000011b430

def z642 : W := mkw 0x8020000020010808 0x4010000010008404 0x76dd0038e3031e19 0xbb6e801c71818f0c

def z643 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xb16ca3a600dc9180 0xd8b651d3006e48c0

def z644 : W := mkw 0x89a1dec863fbca09 0x44d0ef6431fde504 0xf5fdffd863ffee00 0xfafeffec31fff700

def z645 : W := mkw 0xe0b80080244db8bf 0x705c00401226dc5f 0xfff64041fcfff9ff 0xfffb2020fe7ffcff

def z646 : W := mkw 0x40900080004c9095 0x204800400026484a 0x2000000000dc1180 0x10000000006e08c0

def z647 : W := mkw 0x0801da5d48000000 0x0400ed2ea4000000 0x0ebddc7f6c000000 0x075eee3fb6000000

def z648 : W := mkw 0xa02800002401282a 0x5014000012009415 0xd1f44040fc23e01e 0xe8fa20207e11f00f

def z649 : W := mkw 0x4e91fbffd84c9095 0x2748fdffec26484a 0x2009bfbe00dc1180 0x1004dfdf006e08c0

def z650 : W := mkw 0x0b41d3571aa00540 0x85a0e9ab8d5002a0 0xff3fc3ff1fe01fe1 0x7f9fe1ff8ff00ff0

def z651 : W := mkw 0x0e01f36290000000 0x0700f9b148000000 0x0bfdffe690000000 0x05fefff348000000

def z652 : W := mkw 0x629801821448a0a7 0x314c00c10a245053 0x8922c3c71ce0e1e6 0x449161e38e7070f3

def z653 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e02000100000861 0x0701000080000430

def z654 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xcc33c01f03e00fe0 0x6619e00f81f007f0

def z655 : W := mkw 0x8161cc1d63b30f48 0xc0b0e60eb1d987a4 0xfebfdc3f63e31fe1 0x7f5fee1fb1f18ff0

def z656 : W := mkw 0x4e91fbffd84c9095 0x2748fdffec26484a 0x2ffdfffffcdc1180 0x17fefffffe6e08c0

def z657 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x00002380001c0000 0x000011c0000e0000

def z658 : W := mkw 0xa9a9d6c027fbe82b 0x54d4eb6013fdf415 0xf1ffffc003ffe87f 0xf8ffffe001fff43f

def z659 : W := mkw 0x4610212290041094 0x230810914802084a 0x0000002600001180 0x00000013000008c0

def z660 : W := mkw 0x0b41d3571aa00540 0x85a0e9ab8d5002a0 0x8922c3c71ce001e0 0x449161e38e7000f0

def z661 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x70dd3c00e31f0018 0xb86e9e00718f800c

def z662 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x56d43c00e01f0819 0xab6a1e00700f840c

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x01f4404000000000 0x00fa202000000000

def z664 : W := mkw 0x0100000002a00000 0x0080000001500000 0xf000000003e00000 0x7800000001f00000

def z665 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x761d403903201e61 0x3b0ea01c81900f30

def z666 : W := mkw 0x0101c00002a00000 0x0080e00001500000 0x2009800003c00000 0x1004c00001e00000

def z667 : W := mkw 0x0000000000000000 0x0000000000000000 0xdff64041fc200861 0x6ffb2020fe100430

def z668 : W := mkw 0x2149c01506a02562 0x90a4e00a835012b1 0x8922c0471ce0e1e6 0x449160238e7070f3

def z669 : W := mkw 0x0800164001124000 0x04000b2000892000 0x00801c4000036000 0x00400e200001b000

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0xdf7640019020887f 0xefbb2000c810443f

def z671 : W := mkw 0x4991d6c003fed095 0x24c8eb6001ff684a 0xf1ffffc003fff19f 0xf8ffffe001fff8cf

def z672 : W := mkw 0x84202c28e1130a08 0x4210161470898504 0x46dd3c38e3030e00 0x236e9e1c71818700

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x4410400100200860 0x2208200080100430

def z674 : W := mkw 0x0600212290000000 0x0300109148000000 0x0a00002690000000 0x0500001348000000

def z675 : W := mkw 0x8020000020010808 0x4010000010008404 0x4490000060030800 0x2248000030018400

def z676 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xa129ffc003fce000 0x5094ffe001fe7000

def z677 : W := mkw 0xa169c01526a12d6a 0xd0b4e00a935096b5 0xdff74059ff23ee7f 0xeffba02cff91f73f

def z678 : W := mkw 0x0901d64003b24000 0x0480eb2001d92000 0xd1f55c400323e000 0xe8faae200191f000

def z679 : W := mkw 0x0f81ffffdbfac001 0x07c0ffffedfd6000 0xf1fdfffe03ffe000 0xf8feffff01fff000

def z680 : W := mkw 0xe6382122b40538be 0x731c10915a029c5f 0x0e020027fc0019ff 0x07010013fe000cff

def z681 : W := mkw 0xa929d64027b3682a 0x5494eb2013d9b415 0xdff75c41ff23e87f 0xeffbae20ff91f43f

def z682 : W := mkw 0x4751e13792a415d4 0xa3a8f09bc9520aea 0xfe3fc03f93e01fff 0x7f1fe01fc9f00fff

def z683 : W := mkw 0x8921de4863b34a08 0x4490ef2431d9a504 0x44915c5863236e00 0x2248ae2c3191b700

def z684 : W := mkw 0xa9a9d6c027fbe82b 0x54d4eb6013fdf415 0xf1fdffc0ffffe01e 0xf8feffe07ffff00f

def z685 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x06ddbfbee0000000 0x036edfdf70000000

def z686 : W := mkw 0x46902daad15e9295 0x234816d568af494a 0x2009bfbe03dc1780 0x1004dfdf01ee0bc0

def z687 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e34400100000000 0x071a200080000000

def z688 : W := mkw 0x0080008000488001 0x0040004000244000 0x8120838000c08000 0x409041c000604000

def z689 : W := mkw 0x0801d24000000000 0x0400e92000000000 0xd1fdffc00023e000 0xe8feffe00011f000

def z690 : W := mkw 0x0080008000488001 0x0040004000244000 0xb000000000dc8000 0xd8000000006e4000

def z691 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x4e13403f03201fe1 0x2709a01f81900ff0

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x0b64000090000000 0x05b2000048000000

def z693 : W := mkw 0xae29ff7ffd173a3a 0x5714ffbffe8b9d1d 0xffffffffff3ffe7f 0xffffffffff9fff3f

def z694 : W := mkw 0x0f81ffffdbfac001 0x07c0ffffedfd6000 0x2ffdffffffdc0000 0x17feffffffee0000

def z695 : W := mkw 0x0d81fee8c3fed211 0x06c0ff7461ff6908 0x2009bfb803dc1600 0x1004dfdc01ee0b00

def z696 : W := mkw 0xc630292af0051a9c 0x6318149578028d4e 0x0e02003ef0001f9f 0x0701001f78000fcf

def z697 : W := mkw 0xa02800002401282a 0x5014000012009415 0xd1f640400023e87f 0xe8fb20200011f43f

def z698 : W := mkw 0xa829d2402401282a 0x5414e92012009415 0xdfffffc1fc23e87f 0xefffffe0fe11f43f

def z699 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xfe3fffbf03fc1fe1 0x7f1fffdf81fe0ff0

def z700 : W := mkw 0x0140000002a00540 0x80a00000015002a0 0xfa2e802603e01fe1 0x7d17401301f00ff0

def z701 : W := mkw 0xa829da5d6c01282a 0x5414ed2eb6009415 0xdff75c59fc23e87f 0xeffbae2cfe11f43f

def z702 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x8b2283a690c0919f 0x459141d3486048cf

def z703 : W := mkw 0x89a1d6c023fbc809 0x44d0eb6011fde404 0xf7fdffc0e3ffe819 0xfbfeffe071fff40c

def z704 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xba2ec02700e011e1 0x5d176013807008f0

def z705 : W := mkw 0x0b81d3d71ae8c001 0x05c0e9eb8d746000 0x8920c3c71ce0e000 0x449061e38e707000

def z706 : W := mkw 0x0180048003fac001 0x00c0024001fd6000 0x2000000003dc0000 0x1000000001ee0000

def z707 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x8ffffffffc200060 0x47fffffffe100030

def z708 : W := mkw 0x08c016d5015ac541 0x84600b6a80ad62a0 0x0fc23fff001fffe1 0x87e11fff800ffff0

def z709 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x761d3c38031f1e19 0xbb0e9e1c018f8f0c

def z710 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xae2bc03f03e01fe1 0x5715e01f81f00ff0

def z711 : W := mkw 0x42900182104c9095 0x214800c10826484a 0x8922838610dc819e 0xc49141c3086e40cf

def z712 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf5fdffc16fffe000 0xfafeffe0b7fff000

def z713 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x320d3c38031c1601 0x19069e1c018e0b00

def z714 : W := mkw 0xa02800002401282a 0x5014000012009415 0xcdf24041fc23e87e 0xe6f92020fe11f43f

def z715 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x9ffdfffffc008000 0xcffefffffe004000

def z716 : W := mkw 0x8da1fae8e2edda19 0x46d0fd747176ed0c 0x8720c3f8e0e0fe19 0x439061fc70707f0c

def z717 : W := mkw 0xa969d65527b36d6a 0xd4b4eb2a93d9b6b5 0x44915c596f236e60 0x2248ae2cb791b730

def z718 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x2b6ca3a690dc919e 0x95b651d3486e48cf

def z719 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xfffffc7fffffffff 0xfffffe3fffffffff

def z720 : W := mkw 0x0800124000000000 0x0400092000000000 0x01c03fc0fc000000 0x00e01fe07e000000

def z721 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x8ffffffffcc00180 0x47fffffffe6000c0

def z722 : W := mkw 0x0e01fb7fd8041210 0x0700fdbfec020908 0x0ffdfffffc001600 0x07fefffffe000b00

def z723 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0ffdfffffc03e000 0x87fefffffe01f000

def z724 : W := mkw 0xa1a9c48027fbe82b 0x50d4e24013fdf415 0xfe3fc00103ffe87f 0xff1fe00081fff43f

def z725 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x7fff7c79ff1f1e7f 0xbfffbe3cff8f8f3f

def z726 : W := mkw 0x4290018210488085 0x214800c108244042 0xbb6ea38690dc819f 0xddb751c3486e40cf

def z727 : W := mkw 0x0801da5d48000000 0x0400ed2ea4000000 0x0499ffd96c000000 0x024cffecb6000000

def z728 : W := mkw 0xc2b00d8a715b8a8d 0x615806c538adc546 0xcdb39f9e73c38f86 0x66d9cfcf39e1c7c3

def z729 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xf6fd7c38e33f1e19 0xfb7ebe1c719f8f0c

def z730 : W := mkw 0x0a01d35718000000 0x0500e9ab8c000000 0x0ffdffc7fc000000 0x07feffe3fe000000

def z731 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf5fdffff03ffffe0 0xfafeffff81fffff0

def z732 : W := mkw 0x07802dbfdbfac001 0x03c016dfedfd6000 0xfe00003fffffe000 0xff00001ffffff000

def z733 : W := mkw 0x469029aad04c9295 0x234814d56826494a 0xbb6ea3be90dc979f 0xddb751df486e4bcf

def z734 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0xbbeebfe600dff181 0xddf75ff3006ff8c0

def z735 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xe1b9ffc003ffe000 0x70dcffe001fff000

def z736 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x200aa3a600dc119f 0x100551d3006e08cf

def z737 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xfb7fa3a693dc919f 0xfdbfd1d349ee48cf

def z738 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x00003f80fc000000 0x00001fc07e000000

def z739 : W := mkw 0x0e01fb7fd8041010 0x0700fdbfec020808 0x7ffdffffff1c1e19 0xbffeffffff8e0f0c

def z740 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xfffee3e7fcfff19f 0xffff71f3fe7ff8cf

def z741 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x01f47fc0001fe000 0x80fa3fe0000ff000

def z742 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0xbbeebfe6fcc01181 0x5df75ff37e6008c0

def z743 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf9ffffc703ffffe1 0xfcffffe381fffff0

def z744 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x77dd3c78e31ffe19 0xbbee9e3c718fff0c

def z745 : W := mkw 0x0e003b6ad8041010 0x07001db56c020808 0x33cc3fe0fc1c1019 0x99e61ff07e0e080c

def z746 : W := mkw 0xa1e8048027fbed6b 0xd0f4024013fdf6b5 0xf002000003ffffff 0xf801000001ffffff

def z747 : W := mkw 0xa02800002401282a 0x5014000012009415 0xdff64067fc23f9ff 0xeffb2033fe11fcff

def z748 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf7fdfffe03ffff81 0xfbfeffff01ffffc0

def z749 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0fd17ffffc000000 0x07e8bffffe000000

def z750 : W := mkw 0x0140001502a00540 0x80a0000a815002a0 0xf002003e03e01fe1 0x7801001f01f00ff0

def z751 : W := mkw 0x8a21d75739171a18 0x4510ebab9c8b8d0c 0x7920c3c71f1f1e19 0xbc9061e38f8f8f0c

def z752 : W := mkw 0xe6b821a2b44db8bf 0x735c10d15a26dc5f 0x6498e3e76cff79e0 0x324c71f3b67fbcf0

def z753 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0ffdfffffc001e01 0x07fefffffe000f00

def z754 : W := mkw 0x46102d2ad1161294 0x23081695688b094a 0x20093c3e031c1780 0x10049e1f018e0bc0

def z755 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0409bfbf6c000000 0x0204dfdfb6000000

def z756 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xffffffe703fff9e1 0xfffffff381fffcf0

def z757 : W := mkw 0x09c1d2d502e8c541 0x84e0e96a817462a0 0x0000838600c00180 0x000041c3006000c0

def z758 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0xdff67fc1003fe861 0xeffb3fe0801ff430

def z759 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf7fdffc003ffe801 0xfbfeffe001fff400

def z760 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xfbffffe693fff19f 0xfdfffff349fff8cf

def z761 : W := mkw 0xc4302c28e1171a9c 0x62181614708b8d4e 0x76df3c38e31f1f9f 0xbb6f9e1c718f8fcf

def z762 : W := mkw 0x4f11f76293b65094 0x2788fbb149db284a 0x4a935c669323719f 0x2549ae334991b8cf

def z763 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xffff3c39ff1f9e7f 0xffff9e1cff8fcf3f

def z764 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbbfee3e690dc919f 0xddff71f3486e48cf

def z765 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x05fdffd9fc000000 0x02feffecfe000000

def z766 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xba2ea3a600dc919f 0xdd1751d3006e48cf

def z767 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xf03fc03e03e01fe1 0x781fe01f01f00ff0

def z768 : W := mkw 0x4891dadd484c9095 0x2448ed6ea426484a 0xb4935c596cdc919f 0xda49ae2cb66e48cf

def z769 : W := mkw 0x42900182104c9095 0x214800c10826484a 0xbb2e83a610dc919f 0xdd9741d3086e48cf

def z770 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfe0b803f03e01fe1 0x7f05c01f81f00ff0

def z771 : W := mkw 0x0b41db5f5aa00540 0x85a0edafad5002a0 0xffbfdfff7fe01fe1 0x7fdfefffbff00ff0

def z772 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x05d07fc1fc000000 0x02e83fe0fe000000

def z773 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0e3dffbffc000000 0x071effdffe000000

def z774 : W := mkw 0x469029aad04c9095 0x234814d56826484a 0xbb6fbfbe90dc919f 0xddb7dfdf486e48cf

def z775 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x21c93fc0031fe000 0x90e49fe0018ff000

def z776 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xfefffc3fe3ff1ff9 0xff7ffe1ff1ff8ffc

def z777 : W := mkw 0xa02800002401282a 0x5014000012009415 0x4ff44041fc23e87e 0xa7fa2020fe11f43f

def z778 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xbffffffffce011e1 0x5ffffffffe7008f0

def z779 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x76dd3c38e31ffe1f 0xbb6e9e1c718fff0f

def z780 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xd1f57fc0033fe000 0xe8fabfe0019ff000

def z781 : W := mkw 0x46102d2ad1161294 0x23081695688b094a 0x2a0b3c3e931c179f 0x15059e1f498e0bcf

def z782 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x01dd3fc0fc000000 0x00ee9fe07e000000

def z783 : W := mkw 0x0881d6c0015ac001 0x0440eb6000ad6000 0x01c9bfc0001fe000 0x80e4dfe0000ff000

def z784 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x20c93c38e31c1600 0x10649e1c718e0b00

def z785 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x76dd3c38ff1f1e1f 0xbb6e9e1c7f8f8f0f

def z786 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xfdffffdf03ffefe0 0xfeffffef81fff7f0

def z787 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf9ffffc013ffe006 0xfcffffe009fff003

def z788 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbbeea3e690dff19f 0xddf751f3486ff8cf

def z789 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0xffffffffff201e61 0x7fffffffff900f30

def z790 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x2b4aa3a690dc919f 0x95a551d3486e48cf

def z791 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x04917fd96c000000 0x0248bfecb6000000

def z792 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x00003f80001fe000 0x80001fc0000ff000

def z793 : W := mkw 0x0600292ad0000000 0x0300149568000000 0x0ffdfffffc000000 0x07fefffffe000000

def z794 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xffffffc1ffffe01f 0xffffffe0fffff00f

def z795 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x701d3c38031c1600 0x380e9e1c018e0b00

def z796 : W := mkw 0x0bc1d3d71ae8c541 0x85e0e9eb8d7462a0 0x8922c3c71ce0e1e0 0x449161e38e7070f0

def z797 : W := mkw 0xa02800002401282a 0x5014000012009415 0xd5d24041fc23e87f 0xeae92020fe11f43f

def z798 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x7edd3c39ff1f1e19 0xbf6e9e1cff8f8f0c

def z799 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xff3fc07f03e0ffe1 0x7f9fe03f81f07ff0

def z800 : W := mkw 0x86202d2af1171a18 0x43101695788b8d0c 0x7ffdffffff1f1e19 0xbffeffffff8f8f0c

def z801 : W := mkw 0x04002c28c1120000 0x0200161460890000 0x76dd3c38e31f1e01 0xbb6e9e1c718f8f00

def z802 : W := mkw 0x0e01fb7fd8041010 0x0700fdbfec020808 0x2ffdfffffc1c1000 0x17fefffffe0e0800

def z803 : W := mkw 0x0881d6d5015ac001 0x0440eb6a80ad6000 0x0ffdffff001fe000 0x87feffff800ff000

def z804 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x6e1bc03f03e01fe1 0x370de01f81f00ff0

def z805 : W := mkw 0x4e11fb7fd8041094 0x2708fdbfec02084a 0x0ffdfffffc00001e 0x07fefffffe00000f

def z806 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x71dd7fc0033fe000 0xb8eebfe0019ff000

def z807 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x70ddffc003ff6000 0xb86effe001ffb000

def z808 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x7ffdffffff000000 0x3ffeffffff800000

def z809 : W := mkw 0x0000040001120000 0x0000020000890000 0xffff7c79033ffe61 0xffffbe3c819fff30

def z810 : W := mkw 0x0f01fb7fdaa00000 0x0780fdbfed500000 0xfffdffffffe3e000 0xfffefffffff1f000

def z811 : W := mkw 0x0f01fb7fdaa00000 0x0780fdbfed500000 0xfffdffffffe01e01 0x7ffefffffff00f00

def z812 : W := mkw 0xa02800002401282a 0x5014000012009415 0xd5f44041fc23e87e 0xeafa2020fe11f43f

def z813 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x20c93c38031f1600 0x90649e1c018f8b00

def z814 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xf7fd7c79ef3ffe79 0xfbfebe3cf79fff3c

def z815 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xba2ea3a690dc119f 0x5d1751d3486e08cf

def z816 : W := mkw 0x09c1d2d502e8c541 0x84e0e96a817462a0 0x8120c3c600e0e180 0x409061e3007070c0

def z817 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x01c93ff8fc000000 0x00e49ffc7e000000

def z818 : W := mkw 0x0000040001120000 0x0000020000890000 0x20093c38031c1600 0x10049e1c018e0b00

def z819 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x0fc03fc1fc000000 0x07e01fe0fe000000

def z820 : W := mkw 0x0c01fa68c0000000 0x0600fd3460000000 0x0ffdfff9fc000000 0x07fefffcfe000000

def z821 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf1fffffe03ffffe1 0xf8ffffff01fffff0

def z822 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x77dd3ff8031ffe01 0xbbee9ffc018fff00

def z823 : W := mkw 0xa02800002401282a 0x5014000012009415 0xdfff7c41fc23e87f 0xefffbe20fe11f43f

def z824 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xffff7c79ff1f9e1f 0xffffbe3cff8fcf0f

def z825 : W := mkw 0x80200c0861130a08 0x4010060430898504 0x76dd3c18e31f0e19 0xbb6e9e0c718f870c

def z826 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xffff7c79e33ffe79 0xffffbe3cf19fff3c

def z827 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf1fdffc103ffe060 0xf8feffe081fff030

def z828 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0xfe3f7c39033c1e61 0x7f1fbe1c819e0f30

def z829 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x01c13fd8fc000000 0x00e09fec7e000000

def z830 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0fb1dffffc000000 0x07d8effffe000000

def z831 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x74dd3c38631f1e00 0xba6e9e1c318f8f00

def z832 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf1ffffc003ffe861 0xf8ffffe001fff430

def z833 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x01c03fc0fc03e000 0x80e01fe07e01f000

def z834 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf1d17fc003ffe000 0xf8e8bfe001fff000

def z835 : W := mkw 0x00800480015a8001 0x0040024000ad4000 0xf1fdffc003ffe000 0xf8feffe001fff000

def z836 : W := mkw 0x0e01fb7fd8041010 0x0700fdbfec020808 0xbffffffffc1c901f 0xdffffffffe0e480f

def z837 : W := mkw 0x0400242081161010 0x02001210408b0808 0x76dd3c38831f1e19 0xbb6e9e1c418f8f0c

def z838 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x21fdffc003dfe000 0x90feffe001eff000

def z839 : W := mkw 0x8561ec3de3b71f58 0xc2b0f61ef1db8fac 0x88e2fc07e0ff01f8 0xc4717e03f07f80fc

def z840 : W := mkw 0x0981d6d503fac001 0x04c0eb6a81fd6000 0xfffdffffffffe000 0xfffefffffffff000

def z841 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfeffc03fe3e01fe1 0x7f7fe01ff1f00ff0

def z842 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfeffc03f03e31fe1 0xff7fe01f81f18ff0

def z843 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x00803fc06c000000 0x00401fe036000000

def z844 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0xdff67fc1fc200861 0x6ffb3fe0fe100430

def z845 : W := mkw 0xae29fb7ffc01282a 0x5714fdbffe009415 0xd00bbfbe0023e87f 0xe805dfdf0011f43f

def z846 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x2e0b3c39ff1c1e7f 0x17059e1cff8e0f3f

def z847 : W := mkw 0x8020040021171a18 0x40100200108b8d0c 0x76dd3c38031f1e19 0xbb6e9e1c018f8f0c

def z848 : W := mkw 0x0a01db5f58000000 0x0500edafac000000 0x0fbddfff7c000000 0x07deefffbe000000

def z849 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x07ddbffefc000000 0x03eedfff7e000000

def z850 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfebfc07f6fe01fe1 0x7f5fe03fb7f00ff0

def z851 : W := mkw 0x0801da5d48000000 0x0400ed2ea4000000 0x0ffdffd9fc000000 0x07feffecfe000000

def z852 : W := mkw 0x0e01f36290000000 0x0700f9b148000000 0x0ffdffe7fc000000 0x07fefff3fe000000

def z853 : W := mkw 0x0e01fb6ad8000000 0x0700fdb56c000000 0x01c9bfc0fc000000 0x00e4dfe07e000000

def z854 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x70093c38031c1e01 0x38049e1c018e0f00

def z855 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0ffffffffc001181 0x07fffffffe0008c0

def z856 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfe3fc03fffe01fe1 0x7f1fe01ffff00ff0

def z857 : W := mkw 0xa02800002401282a 0x5014000012009415 0x57d44041fc23e87f 0xabea2020fe11f43f

def z858 : W := mkw 0xa02800002401282a 0x5014000012009415 0xfffe6041fc3fe87f 0xffff3020fe1ff43f

def z859 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xf6df7c79ef3ffe7f 0xfb6fbe3cf79fff3f

def z860 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf16dbf8003ffe000 0xf8b6dfc001fff000

def z861 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xff7fe3bf93fc9fff 0xffbff1dfc9fe4fff

def z862 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xffffffff93ffffff 0xffffffffc9ffffff

def z863 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x09fdffc7fc000000 0x04feffe3fe000000

def z864 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x769d3c38631f1e01 0x3b4e9e1c318f8f00

def z865 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xb962a38690dc919f 0xdcb151c3486e48cf

def z866 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x5ffdfffffc000801 0x2ffefffffe000400

def z867 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xa1e9ffc003ffe000 0xd0f4ffe001fff000

def z868 : W := mkw 0xa169c01526a12d6a 0xd0b4e00a935096b5 0x21c9807effc3f79e 0x90e4c03f7fe1fbcf

def z869 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf1fdfff803fff600 0xf8fefffc01fffb00

def z870 : W := mkw 0x0801d24000000000 0x0400e92000000000 0x01fdffc0fc000000 0x00feffe07e000000

def z871 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbb6ee3e79cdc919f 0xddb771f3ce6e48cf

def z872 : W := mkw 0x00000c0841120200 0x0000060420890100 0x20093c18031c0600 0x10049e0c018e0300

def z873 : W := mkw 0x40900080004c9095 0x204800400026484a 0xbb6ea3a600dc919f 0xddb751d3006e48cf

def z874 : W := mkw 0x0140001502a00540 0x80a0000a815002a0 0xfe2e803f03e01fe1 0x7f17401f81f00ff0

def z875 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xf00b3c38033ffe7f 0xf8059e1c019fff3f

def z876 : W := mkw 0xa02800002401282a 0x5014000012009415 0x01c04041fc23e07e 0x80e02020fe11f03f

def z877 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xffffffc193ffe87f 0xffffffe0c9fff43f

def z878 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0ff4ffc7fc000000 0x07fa7fe3fe000000

def z879 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x77fdbfb8e31f1e19 0xbbfedfdc718f8f0c

def z880 : W := mkw 0xa02800002401282a 0x5014000012009415 0x4fd24041fc23e87f 0xa7e92020fe11f43f

def z881 : W := mkw 0x08001a4848000000 0x04000d2424000000 0x01c03fc06c000000 0x00e01fe036000000

def z882 : W := mkw 0x0000040001120000 0x0000020000890000 0x74dd3c18031f0e00 0xba6e9e0c018f8700

def z883 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xffff3c38f33ffe7f 0xffff9e1c799fff3f

def z884 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x00c13c18e31f0618 0x80609e0c718f830c

def z885 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xffffffffffe09fff 0xfffffffffff04fff

def z886 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xff7fe3bf03e01fe1 0x7fbff1df81f00ff0

def z887 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x765d3c38831c1e19 0xbb2e9e1c418e0f0c

def z888 : W := mkw 0x098016c003fac001 0x04c00b6001fd6000 0xf0003f8003ffe000 0xf8001fc001fff000

def z889 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x2fffffffffc01fe1 0x17ffffffffe00ff0

def z890 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0089bffe6c000000 0x0044dfff36000000

def z891 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xd1f4ffc000ffe000 0xe8fa7fe0007ff000

def z892 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x77fd7c78e31f1e19 0xbbfebe3c718f8f0c

def z893 : W := mkw 0xa02800002401282a 0x5014000012009415 0xffff4041ff23e87f 0xffffa020ff91f43f

def z894 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x45d17c59ff3fee7e 0xa2e8be2cff9ff73f

def z895 : W := mkw 0x098016c003fac001 0x04c00b6001fd6000 0xf1ecbfc003ffe000 0xf8f65fe001fff000

def z896 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0xba2fbc3e03dc1781 0x5d17de1f01ee0bc0

def z897 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x2409803f03c01fe0 0x1204c01f81e00ff0

def z898 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbb6fa3be93dc979f 0xddb7d1df49ee4bcf

def z899 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xf6fdbc38e3df1e19 0xfb7ede1c71ef8f0c

def z900 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x1ffdfffffc000019 0x8ffefffffe00000c

def z901 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x36dd3c38e31c1619 0x9b6e9e1c718e0b0c

def z902 : W := mkw 0x0f403b6adaa00540 0x87a01db56d5002a0 0xf1c23fc0ffe01fe1 0x78e11fe07ff00ff0

def z903 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xb1edbfc003dfe000 0xd8f6dfe001eff000

def z904 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfefffc3f03e01fe1 0x7f7ffe1f81f00ff0

def z905 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xffff7c78f33ffe1f 0xffffbe3c799fff0f

def z906 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xfbffffe703fff1e1 0xfdfffff381fff8f0

def z907 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x00803fc0001f6000 0x00401fe0000fb000

def z908 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x2008a3a600dc919e 0x900451d3006e48cf

def z909 : W := mkw 0x0f01fb7fdaa00000 0x0780fdbfed500000 0xffffffffffe01181 0x7ffffffffff008c0

def z910 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xfffdffff03ffee60 0xfffeffff81fff730

def z911 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfa2f803e03e01fe1 0x7d17c01f01f00ff0

def z912 : W := mkw 0xc6302d2af1171a9c 0x63181695788b8d4e 0x7fffbfbef31f1f9f 0xbfffdfdf798f8fcf

def z913 : W := mkw 0x0801d25500000000 0x0400e92a80000000 0x0ffdfffffc000000 0x07fefffffe000000

def z914 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x01c0bfc000dfe000 0x80e05fe0006ff000

def z915 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xfbfdffe603ffe000 0xfdfefff301fff000

def z916 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xfeff7c79ef3f7e79 0xff7fbe3cf79fbf3c

def z917 : W := mkw 0xa829d2402401282a 0x5414e92012009415 0xd1ffffc00023e87f 0xe8ffffe00011f43f

def z918 : W := mkw 0x0a001b4a58000000 0x05000da52c000000 0x01801fc07c000000 0x00c00fe03e000000

def z919 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xffffc07f03e01fe1 0x7fffe03f81f00ff0

def z920 : W := mkw 0x0e41fb7fd8000540 0x8720fdbfec0002a0 0xdffffffffc201fe1 0x6ffffffffe100ff0

def z921 : W := mkw 0x09c1d2d502e8c541 0x84e0e96a817462a0 0x8120c3c100e0e060 0x409061e080707030

def z922 : W := mkw 0x24082c28c5163232 0x12041614628b1919 0xa92b7c791f3cf666 0x5495be3c8f9e7b33

def z923 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x76dd3c38e31c1e01 0x3b6e9e1c718e0f00

def z924 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xff3fc03f13e09fe7 0x7f9fe01f89f04ff3

def z925 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x03cc3fe0fc000000 0x01e61ff07e000000

def z926 : W := mkw 0xc6302d2af1171a9c 0x63181695788b8d4e 0xffff3c3ef31f9f9f 0xffff9e1f798fcfcf

def z927 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xff7fc03f93e01fe1 0x7fbfe01fc9f00ff0

def z928 : W := mkw 0x4991d6c003fac085 0x24c8eb6001fd6042 0xf1ffffc003ffe186 0xf8ffffe001fff0c3

def z929 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xbfffffffffc01781 0x5fffffffffe00bc0

def z930 : W := mkw 0xa02800002401282a 0x5014000012009415 0x8fe24041fc23e87f 0xc7f12020fe11f43f

def z931 : W := mkw 0x0941d25502a00540 0x84a0e92a815002a0 0xffffffffffe01fe1 0x7ffffffffff00ff0

def z932 : W := mkw 0x80200c0861130a08 0x4010060430898504 0x64993c18631f0e00 0x324c9e0c318f8700

def z933 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x224d3c38831c1600 0x11269e1c418e0b00

def z934 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x20093c38031f1618 0x90049e1c018f8b0c

def z935 : W := mkw 0x09c1d6c003fac541 0x84e0eb6001fd62a0 0xf1fdffc003fff780 0xf8feffe001fffbc0

def z936 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x304d3c38031c1600 0x98269e1c018e0b00

def z937 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf0bdffc003ff6000 0x785effe001ffb000

def z938 : W := mkw 0xa02804002513282a 0x5014020012899415 0xffff7c79ff3ffe7f 0xffffbe3cff9fff3f

def z939 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x6499ffff6fe01fe0 0x324cffffb7f00ff0

def z940 : W := mkw 0x47d1e1b792ec95d5 0xa3e8f0dbc9764aea 0x45516399933c8e7e 0xa2a8b1ccc99e473f

def z941 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xff3fc07f1fe01fe1 0x7f9fe03f8ff00ff0

def z942 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x05d13fd8fc000000 0x02e89fec7e000000

def z943 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x7efdbc3ee31f1e19 0xbf7ede1f718f8f0c

def z944 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x41d07fc0003fe000 0xa0e83fe0001ff000

def z945 : W := mkw 0x0901d24002a00000 0x0480e92001500000 0xffffffc1ffe00861 0x7fffffe0fff00430

def z946 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xf6df3c38e33f1e79 0xfb6f9e1c719f8f3c

def z947 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xffffffff03ffe1e0 0xffffffff81fff0f0

def z948 : W := mkw 0x0e003b7fd8000000 0x07001dbfec000000 0x0fecbffffc000000 0x07f65ffffe000000

def z949 : W := mkw 0xa02800002401282a 0x5014000012009415 0xdfff4079fc23e87f 0xefffa03cfe11f43f

def z950 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x334ca3a690dc919f 0x99a651d3486e48cf

def z951 : W := mkw 0x80200c0861130a08 0x4010060430898504 0x44d13c18631f0e00 0xa2689e0c318f8700

def z952 : W := mkw 0x469029aad04c9095 0x234814d56826484a 0xbbeebfa6f0dc919f 0xddf75fd3786e48cf

def z953 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xbe2f803f03c01fe1 0x5f17c01f81e00ff0

def z954 : W := mkw 0x0881d6c0015ac001 0x0440eb6000ad6000 0x01d17fc0001fe000 0x80e8bfe0000ff000

def z955 : W := mkw 0xa628293ffc053a3a 0x5314149ffe029d1d 0x0e02003ffc001e7f 0x0701001ffe000f3f

def z956 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xfffdffffffe00e60 0x7ffefffffff00730

def z957 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf099ffc003ffe000 0xf84cffe001fff000

def z958 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x0140a38690dc819e 0x80a051c3486e40cf

def z959 : W := mkw 0x4e51fb7fd80415d4 0xa728fdbfec020aea 0x0ffffffffc001fff 0x07fffffffe000fff

def z960 : W := mkw 0x42900182104c9095 0x214800c10826484a 0xb96ea38610dc919f 0xdcb751c3086e48cf

def z961 : W := mkw 0xa9a9d6c027fbe82b 0x54d4eb6013fdf415 0x2e0bbf81ffdc087f 0x1705dfc0ffee043f

def z962 : W := mkw 0x0e003b7fd8000000 0x07001dbfec000000 0x01c03ffefc000000 0x00e01fff7e000000

def z963 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x6009803e03e01fe0 0x3004c01f01f00ff0

def z964 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x8b62a3a690dc919f 0xc5b151d3486e48cf

def z965 : W := mkw 0x0981d6d503fac001 0x04c0eb6a81fd6000 0xf9fdffc703ffe000 0xfcfeffe381fff000

def z966 : W := mkw 0x29c9d2d506e8e563 0x94e4e96a837472b1 0x8922c3c71ce0e1e6 0x449161e38e7070f3

def z967 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x7fdf3c79ff1ffe7f 0xbfef9e3cff8fff3f

def z968 : W := mkw 0x0f01fb6adaa00000 0x0780fdb56d500000 0xf1fdffc0ffe00000 0x78feffe07ff00000

def z969 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x0ff47fc1fc1fe000 0x87fa3fe0fe0ff000

def z970 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xec3bc03f03e01fe0 0x761de01f81f00ff0

def z971 : W := mkw 0x0140001502a00540 0x80a0000a815002a0 0xfe1f003f03e01fe1 0x7f0f801f81f00ff0

def z972 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xf7fd3c38e31f9e19 0xfbfe9e1c718fcf0c

def z973 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xffffc07f93e3ffff 0xffffe03fc9f1ffff

def z974 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x51d43fc0001fe000 0xa8ea1fe0000ff000

def z975 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe3fc03f03e01fe1 0x7f1fe01f81f00ff0

def z976 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x2e3fc03f03c01fe1 0x171fe01f81e00ff0

def z977 : W := mkw 0x0941d25502a04540 0x84a0e92a815022a0 0xfe3fc07f03e07fe1 0x7f1fe03f81f03ff0

def z978 : W := mkw 0x4e11fb7fd8041094 0x2708fdbfec02084a 0x3ffffffffc1c119f 0x9ffffffffe0e08cf

def z979 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x761d3c38e31c1e19 0x3b0e9e1c718e0f0c

def z980 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x21c93c78ff1ff61e 0x90e49e3c7f8ffb0f

def z981 : W := mkw 0x0801d64001120000 0x0400eb2000890000 0xf1fdffc0033fe000 0xf8feffe0019ff000

def z982 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0xf1fd7fc0033fe000 0xf8febfe0019ff000

def z983 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x77dd3c38f31f9e1f 0xbbee9e1c798fcf0f

def z984 : W := mkw 0xa0280c0865132a2a 0x5014060432899515 0xf5fd7c596f3fee60 0xfafebe2cb79ff730

def z985 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x01c8bfe6fc000000 0x00e45ff37e000000

def z986 : W := mkw 0x0e01fb6ad8000000 0x0700fdb56c000000 0x0ffdffc1fc000000 0x07feffe0fe000000

def z987 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x4ffdfffffc200860 0x27fefffffe100430

def z988 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x20493c38831c1618 0x90249e1c418e0b0c

def z989 : W := mkw 0x0881d2c000488001 0x0440e96000244000 0xf1fdffc000ffe000 0xf8feffe0007ff000

def z990 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xb92aa3a610dc919f 0xdc9551d3086e48cf

def z991 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbb6ee3a790fc91ff 0xddb771d3c87e48ff

def z992 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfe22c03f03e01fe1 0x7f11601f81f00ff0

def z993 : W := mkw 0xa0280c0865132a2a 0x5014060432899515 0xffff7c59ff3fee7f 0xffffbe2cff9ff73f

def z994 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0f29fffffc000000 0x0794fffffe000000

def z995 : W := mkw 0xa02800002401282a 0x5014000012009415 0xdff6c047fce3e9ff 0xeffb6023fe71f4ff

def z996 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf1ffffc003ffe01f 0xf8ffffe001fff00f

def z997 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbf6ea3a790dc99ff 0xdfb751d3c86e4cff

def z998 : W := mkw 0x0a01db5f58000000 0x0500edafac000000 0x09a0dfc77c000000 0x04d06fe3be000000

def z999 : W := mkw 0x00000c0841120200 0x0000060420890100 0x70dd3c18031f0600 0xb86e9e0c018f8300

def z1000 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x01c0bfc6fc000000 0x00e05fe37e000000

def z1001 : W := mkw 0x0f01fb7fdaa00000 0x0780fdbfed500000 0x2ffdffffffc00000 0x17feffffffe00000

def z1002 : W := mkw 0x0981d6d50bfac001 0x04c0eb6a85fd6000 0xf1fdffc10fffe000 0xf8feffe087fff000

def z1003 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x64997c796f3f7e60 0x324cbe3cb79fbf30

def z1004 : W := mkw 0x42900182104c9095 0x214800c10826484a 0xbb66838690dc919f 0xddb341c3486e48cf

def z1005 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0xd1c03fc0003fe000 0xe8e01fe0001ff000

def z1006 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x09e9fffffc000000 0x04f4fffffe000000

def z1007 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0becffe7fc000000 0x05f67ff3fe000000

def z1008 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x01ecbfc0001fe000 0x80f65fe0000ff000

def z1009 : W := mkw 0x09c1d6c003fac541 0x84e0eb6001fd62a0 0xffffffc103ffffe1 0xffffffe081fffff0

def z1010 : W := mkw 0x42900182104c9095 0x214800c10826484a 0xb002838600dc919f 0xd80141c3006e48cf

def z1011 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xfeff7c39ff3f1e7f 0xff7fbe1cff9f8f3f

def z1012 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x76dd3c39ef1f1e79 0xbb6e9e1cf78f8f3c

def z1013 : W := mkw 0x0e41fb7fd8000540 0x8720fdbfec0002a0 0x0ffdfffffc000e60 0x07fefffffe000730

def z1014 : W := mkw 0x0941da5d4aa00540 0x84a0ed2ea55002a0 0xf5fdffd96fe00e60 0x7afeffecb7f00730

def z1015 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x2e0bbfbfffc01fe1 0x1705dfdfffe00ff0

def z1016 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0df1ffdffc000000 0x06f8ffeffe000000

def z1017 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0xdffffffffc20887f 0xeffffffffe10443f

def z1018 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbbeea3e6fcdc919f 0xddf751f37e6e48cf

def z1019 : W := mkw 0x0941d25502a00540 0x84a0e92a815002a0 0xffffffff03e3ffe1 0xffffffff81f1fff0

def z1020 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x7ffd7c79ff1ffe1f 0xbffebe3cff8fff0f

def z1021 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x4ffdffffff000e00 0x27feffffff800700

def z1022 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xb96ea38690dc819e 0xdcb751c3486e40cf

def z1023 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xff7fc03f03e09fe1 0xffbfe01f81f04ff0

def z1024 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xf82bc03f03e01fe1 0x7c15e01f81f00ff0

def z1025 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0xdffdfffffc200000 0x6ffefffffe100000

def z1026 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x26093c38e31c1600 0x13049e1c718e0b00

def z1027 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x21c9bffeffc01780 0x10e4dfff7fe00bc0

def z1028 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x20093c38031c1e19 0x10049e1c018e0f0c

def z1029 : W := mkw 0x04002828c0041010 0x0200141460020808 0x76dd3c38e31c1e19 0xbb6e9e1c718e0f0c

def z1030 : W := mkw 0xa02800002401282a 0x5014000012009415 0xfff64041fce3f9ff 0xfffb2020fe71fcff

def z1031 : W := mkw 0x469029aad04c9095 0x234814d56826484a 0xbffffffffcdc919f 0xdffffffffe6e48cf

def z1032 : W := mkw 0xa0a80480255be82b 0x5054024012adf415 0xd0020000003fe87f 0xe8010000001ff43f

def z1033 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x81e0bfc000dfe000 0xc0f05fe0006ff000

def z1034 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x7e1f803f03c01fe1 0x3f0fc01f81e00ff0

def z1035 : W := mkw 0x0981d6d503fac001 0x04c0eb6a81fd6000 0xf1fdfffe03ffe000 0xf8feffff01fff000

def z1036 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0f6dbfbffc000000 0x07b6dfdffe000000

def z1037 : W := mkw 0x0801da5d48000000 0x0400ed2ea4000000 0x05b1dfd96c000000 0x02d8efecb6000000

def z1038 : W := mkw 0x8020040021130808 0x4010020010898404 0x76dd3c38e31f1e19 0xbb6e9e1c718f8f0c

def z1039 : W := mkw 0xa0a80480255be82b 0x5054024012adf415 0x00000000001fe01e 0x80000000000ff00f

def z1040 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xf6df3c38e3df1f99 0xfb6f9e1c71ef8fcc

def z1041 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xffffffffffe001e0 0x7ffffffffff000f0

def z1042 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xafffffffffe017e0 0x57fffffffff00bf0

def z1043 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbf7fa3be90dc919f 0xdfbfd1df486e48cf

def z1044 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x07d43fc0fc000000 0x03ea1fe07e000000

def z1045 : W := mkw 0xa1a8048027fffa3b 0x50d4024013fffd1d 0xf002000003fffe7f 0xf801000001ffff3f

def z1046 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x0ffd7ff9fc000000 0x07febffcfe000000

def z1047 : W := mkw 0x098016c003fac001 0x04c00b6001fd6000 0xf1f47fc003ffe000 0xf8fa3fe001fff000

def z1048 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xffff7c39f33f9e7f 0xffffbe1cf99fcf3f

def z1049 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf1fdffc603ffe180 0xf8feffe301fff0c0

def z1050 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x00013c18031c0600 0x00009e0c018e0300

def z1051 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x76dd3c38e31f1600 0xbb6e9e1c718f8b00

def z1052 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x0ffdfffffcc00180 0x07fefffffe6000c0

def z1053 : W := mkw 0x0801da5d48000000 0x0400ed2ea4000000 0x0ffdffff6c000000 0x07feffffb6000000

def z1054 : W := mkw 0x0800124000000000 0x0400092000000000 0x0ff47fc1fc000000 0x07fa3fe0fe000000

def z1055 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xfbfdffc093ffe000 0xfdfeffe049fff000

def z1056 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xfebfffff6fe01fe1 0x7f5fffffb7f00ff0

def z1057 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x70dd3c38e31f1618 0xb86e9e1c718f8b0c

def z1058 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xab2aa3a690dc919f 0x559551d3486e48cf

def z1059 : W := mkw 0x0140001502a00540 0x80a0000a815002a0 0x2e02003f03c01fe1 0x1701001f81e00ff0

def z1060 : W := mkw 0xa02800002401282a 0x5014000012009415 0xd9f64041fc23e07e 0xecfb2020fe11f03f

def z1061 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x4ffdfffffc236000 0x27fefffffe11b000

def z1062 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x22093c38831c1619 0x11049e1c418e0b0c

def z1063 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x761dc03f03e01fe1 0x3b0ee01f81f00ff0

def z1064 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0ff57fd9fc000000 0x07fabfecfe000000

def z1065 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x30093c38031c1619 0x98049e1c018e0b0c

def z1066 : W := mkw 0xe0b80480255fbabf 0x705c024012afdd5f 0xf002000003ffffff 0xf801000001ffffff

def z1067 : W := mkw 0xa1a8048027fbe82b 0x50d4024013fdf415 0xf000000003ffe860 0xf800000001fff430

def z1068 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x77dd7c79ff3ffe7f 0xbbeebe3cff9fff3f

def z1069 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xffffffffffe3ffe1 0xfffffffffff1fff0

def z1070 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xffffffc703ffe9e1 0xffffffe381fff4f0

def z1071 : W := mkw 0xa02800002401282a 0x5014000012009415 0xfffe4061fc23f87f 0xffff2030fe11fc3f

def z1072 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x2009bc3e03dc1780 0x1004de1f01ee0bc0

def z1073 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0e99fffffc000000 0x074cfffffe000000

def z1074 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x76dd3c38031f1e01 0xbb6e9e1c018f8f00

def z1075 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x7ffdffffff201e61 0x3ffeffffff900f30

def z1076 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xb16ea3a600dc919f 0xd8b751d3006e48cf

def z1077 : W := mkw 0x0941da5d4aa00540 0x84a0ed2ea55002a0 0xffffffff6fe01fe1 0x7fffffffb7f00ff0

def z1078 : W := mkw 0xe638293ffc0538be 0x731c149ffe029c5f 0x0e02003ffc0019ff 0x0701001ffe000cff

def z1079 : W := mkw 0x0f41fb7fdaa41550 0x87a0fdbfed520aa8 0xfffffffffffc1ff9 0xfffffffffffe0ffc

def z1080 : W := mkw 0x0e003b7fd8000000 0x07001dbfec000000 0x0ff47ffffc000000 0x07fa3ffffe000000

def z1081 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xffffbc3ef3df9f9f 0xffffde1f79efcfcf

def z1082 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfe13403f03e01fe1 0x7f09a01f81f00ff0

def z1083 : W := mkw 0xa02800002401282a 0x5014000012009415 0xdffee3c1fc23e87f 0xefff71e0fe11f43f

def z1084 : W := mkw 0x86202d2af1171a18 0x43101695788b8d0c 0x76ddbfbee31f1e19 0xbb6edfdf718f8f0c

def z1085 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xfffffff903fffe61 0xfffffffc81ffff30

def z1086 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x7ffdffffffc01f81 0x3ffeffffffe00fc0

def z1087 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x26dd3c38e31f1618 0x936e9e1c718f8b0c

def z1088 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0xdffffffffc23e01f 0xeffffffffe11f00f

def z1089 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x72dd3c38831f1619 0xb96e9e1c418f8b0c

def z1090 : W := mkw 0xa9e9d2d526e9ed6b 0xd4f4e96a9374f6b5 0xdff6c3c7fce3e9ff 0xeffb61e3fe71f4ff

def z1091 : W := mkw 0x0a01db5f58000000 0x0500edafac000000 0x0491dfdf6c000000 0x0248efefb6000000

def z1092 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf03dff8003ffe000 0xf81effc001fff000

def z1093 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xfebfffff03ff7fe1 0x7f5fffff81ffbff0

def z1094 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0xfffffffffce019e1 0x7ffffffffe700cf0

def z1095 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xfffee3e790fff9ff 0xffff71f3c87ffcff

def z1096 : W := mkw 0x0e41fb7fd8000540 0x8720fdbfec0002a0 0x0ffffffffc0001e0 0x07fffffffe0000f0

def z1097 : W := mkw 0x0e01fb6ad8000000 0x0700fdb56c000000 0x01d17fc0fc000000 0x00e8bfe07e000000

def z1098 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x8ffffffffce01fe1 0x47fffffffe700ff0

def z1099 : W := mkw 0xa6282d2af5173a3a 0x531416957a8b9d1d 0xffffffffff3ffe7f 0xffffffffff9fff3f

def z1100 : W := mkw 0x06002d2ad1161210 0x03001695688b0908 0x2009bfbe031c1600 0x1004dfdf018e0b00

def z1101 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x2008a3a690dc119e 0x100451d3486e08cf

def z1102 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x06ddffffec000000 0x036efffff6000000

def z1103 : W := mkw 0x06002d2ad1161210 0x03001695688b0908 0x2b6dbfbe931c1600 0x15b6dfdf498e0b00

def z1104 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x0ffcffe7fc000000 0x07fe7ff3fe000000

def z1105 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xf6df3c38e31f9e1f 0xfb6f9e1c718fcf0f

def z1106 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x8b6ea3a690dc819e 0xc5b751d3486e40cf

def z1107 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x32cd3c38e31f1619 0x99669e1c718f8b0c

def z1108 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x8ffffffffc008006 0x47fffffffe004003

def z1109 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x7efd7c39e31f1e19 0xbf7ebe1cf18f8f0c

def z1110 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x76dd3c38e33f7e79 0xbb6e9e1c719fbf3c

def z1111 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xfb6ea3a690fc99ff 0xfdb751d3487e4cff

def z1112 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xf43dc03f03e01fe0 0x7a1ee01f81f00ff0

def z1113 : W := mkw 0x469029aad04c9095 0x234814d56826484a 0xffffbfbef3dc9f9f 0xffffdfdf79ee4fcf

def z1114 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xfffd7c79ff3ffe19 0xfffebe3cff9fff0c

def z1115 : W := mkw 0xa0280c0865173a3a 0x50140604328b9d1d 0xf4935c596f3ffe7f 0xfa49ae2cb79fff3f

def z1116 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0ebdffff6c000000 0x075effffb6000000

def z1117 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x26dd3c38e31c1e19 0x136e9e1c718e0f0c

def z1118 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x45d17fd9ff200e60 0x22e8bfecff900730

def z1119 : W := mkw 0x0e41fb7fd8000540 0x8720fdbfec0002a0 0xbffffffffcc01fe1 0x5ffffffffe600ff0

def z1120 : W := mkw 0x098016c003fac001 0x04c00b6001fd6000 0x41c03fc0033fe000 0xa0e01fe0019ff000

def z1121 : W := mkw 0x0801da4848000000 0x0400ed2424000000 0x01fdffc06c000000 0x00feffe036000000

def z1122 : W := mkw 0x0040001500000540 0x8020000a800002a0 0xfe3f803f03c01fe1 0x7f1fc01f81e00ff0

def z1123 : W := mkw 0x0e01fb7fd8041010 0x0700fdbfec020808 0x0ffdfffffc001019 0x07fefffffe00080c

def z1124 : W := mkw 0x0801d24000000000 0x0400e92000000000 0x05fdffc16c000000 0x02feffe0b6000000

def z1125 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xfb6ea3a693dc9f9f 0xfdb751d349ee4fcf

def z1126 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf1ffffc003fff181 0xf8ffffe001fff8c0

def z1127 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xba0aa3a690dc919f 0xdd0551d3486e48cf

def z1128 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0xbb6f3c38931c961f 0xddb79e1c498e4b0f

def z1129 : W := mkw 0x0a01db5f58000000 0x0500edafac000000 0x0dfdffdf7c000000 0x06feffefbe000000

def z1130 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xffff3c78ff1ffe1f 0xffff9e3c7f8fff0f

def z1131 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x66993c38e31f1e19 0x334c9e1c718f8f0c

def z1132 : W := mkw 0xa02800002401282a 0x5014000012009415 0xdffec067fc23e87f 0xefff6033fe11f43f

def z1133 : W := mkw 0x4f51fb7fdaa415d4 0xa7a8fdbfed520aea 0xffffffffffe01fff 0x7ffffffffff00fff

def z1134 : W := mkw 0x0881d6c0015ac001 0x0440eb6000ad6000 0xd1fdffc0003fe000 0xe8feffe0001ff000

def z1135 : W := mkw 0x00000c0841161210 0x00000604208b0908 0x20011c18031c1600 0x10008e0c018e0b00

def z1136 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x9b66a38690dc819f 0xcdb351c3486e40cf

def z1137 : W := mkw 0x0e01fb7fd8041010 0x0700fdbfec020808 0x0ffdfffffc1c0018 0x87fefffffe0e000c

def z1138 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x6ffdffffffe01fe0 0x37fefffffff00ff0

def z1139 : W := mkw 0x80200c0861171a18 0x40100604308b8d0c 0x44911c18631f0e18 0xa2488e0c318f870c

def z1140 : W := mkw 0xc6302d2af1171a9c 0x63181695788b8d4e 0x76dd3c38f31f1e1f 0xbb6e9e1c798f8f0f

def z1141 : W := mkw 0x80200c0861130a08 0x4010060430898504 0x74911c18631f0e00 0xba488e0c318f8700

def z1142 : W := mkw 0xc6302d2af1171a9c 0x63181695788b8d4e 0x76dd3c3ee31f1f99 0xbb6e9e1f718f8fcc

def z1143 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x21c8bfc000dfe000 0x90e45fe0006ff000

def z1144 : W := mkw 0x0080008000488001 0x0040004000244000 0xbb6ea3a690dc919f 0xddb751d3486e48cf

def z1145 : W := mkw 0xa02800002401282a 0x5014000012009415 0x9be64041fc23e07f 0xcdf32020fe11f03f

def z1146 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x0bc03fe6fc000000 0x05e01ff37e000000

def z1147 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xb1ecffc000ffe000 0xd8f67fe0007ff000

def z1148 : W := mkw 0x098016c003fac001 0x04c00b6001fd6000 0x81c03fc000ffe000 0xc0e01fe0007ff000

def z1149 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbf7ee3a790dc919f 0xdfbf71d3c86e48cf

def z1150 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x91e43fc0001fe000 0xc8f21fe0000ff000

def z1151 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x74d13c18e31f1e19 0xba689e0c718f8f0c

def z1152 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x64193c38031c1e00 0x320c9e1c018e0f00

def z1153 : W := mkw 0x0000040001120000 0x0000020000890000 0x70dd3c38031f1600 0xb86e9e1c018f8b00

def z1154 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x01ecbfc0fc000000 0x00f65fe07e000000

def z1155 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x07c03ff8fc000000 0x03e01ffc7e000000

def z1156 : W := mkw 0x0140001502a00540 0x80a0000a815002a0 0xfe36403f03e01fe1 0x7f1b201f81f00ff0

def z1157 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x2ffdffffff001600 0x17feffffff800b00

def z1158 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0x89e2ffc700ffe1e0 0xc4f17fe3807ff0f0

def z1159 : W := mkw 0x09c1d6c003fac541 0x84e0eb6001fd62a0 0xf7fffff803ffffe1 0xfbfffffc01fffff0

def z1160 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x5ffdfffffc030000 0xaffefffffe018000

def z1161 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x7edf3c3ee31f1f99 0xbf6f9e1f718f8fcc

def z1162 : W := mkw 0x0941d2550aa00540 0x84a0e92a855002a0 0xfe3fc07f0fe01fe1 0x7f1fe03f87f00ff0

def z1163 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x81e07fc0003fe000 0xc0f03fe0001ff000

def z1164 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x20dd3c38031c1600 0x106e9e1c018e0b00

def z1165 : W := mkw 0x80200c0861171a18 0x40100604308b8d0c 0x76d51c18e31f1e19 0xbb6a8e0c718f8f0c

def z1166 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xfe3fffbf03ffffe1 0xff1fffdf81fffff0

def z1167 : W := mkw 0x0e41fb7fd8000540 0x8720fdbfec0002a0 0x0ffdfffffc001780 0x07fefffffe000bc0

def z1168 : W := mkw 0x0f01fb7fdaa04000 0x0780fdbfed502000 0x0ffdfffffc206000 0x07fefffffe103000

def z1169 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x01f47fc0fc000000 0x00fa3fe07e000000

def z1170 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x09e07fc1fc000000 0x04f03fe0fe000000

def z1171 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf1fdffc003fffe01 0xf8feffe001ffff00

def z1172 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xfeff7c39e33ffe7f 0xff7fbe1cf19fff3f

def z1173 : W := mkw 0x80200c0861171a18 0x40100604308b8d0c 0x70011c18031f1e19 0xb8008e0c018f8f0c

def z1174 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xdffffffffce009e1 0x6ffffffffe7004f0

def z1175 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x64d93c38e31f1e18 0xb26c9e1c718f8f0c

def z1176 : W := mkw 0x0f01fb7fdaa00000 0x0780fdbfed500000 0x8ffdfffffce00000 0x47fefffffe700000

def z1177 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x20893c38631f1600 0x10449e1c318f8b00

def z1178 : W := mkw 0x4e11fb7fd8041094 0x2708fdbfec02084a 0x9ffffffffc00919f 0xcffffffffe0048cf

def z1179 : W := mkw 0x0981d6d503fac001 0x04c0eb6a81fd6000 0xffffffff03ffe861 0xffffffff81fff430

def z1180 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xfffdffc103ffe000 0xfffeffe081fff000

def z1181 : W := mkw 0x0e003b6ad8041010 0x07001db56c020808 0x01c03fc0fc1c0018 0x80e01fe07e0e000c

def z1182 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0eddbfbffc000000 0x076edfdffe000000

def z1183 : W := mkw 0x0801da5d48000000 0x0400ed2ea4000000 0x05d17fd96c000000 0x02e8bfecb6000000

def z1184 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x70093c38031f1600 0xb8049e1c018f8b00

def z1185 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf7fdffc0e3ffe000 0xfbfeffe071fff000

def z1186 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xb24ea3a680dc919f 0xd92751d3406e48cf

def z1187 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x01fdfffefc000000 0x00feffff7e000000

def z1188 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xffffc07fffe3ffe1 0xffffe03ffff1fff0

def z1189 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xdfffffffff200e61 0x6fffffffff900730

def z1190 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x70c93c38e31f1e19 0xb8649e1c718f8f0c

def z1191 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x24093c38631c1e00 0x12049e1c318e0f00

def z1192 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf0ddbf8003ffe000 0xf86edfc001fff000

def z1193 : W := mkw 0xe1b8048027fff8bf 0x70dc024013fffc5f 0xf002000003fff9ff 0xf801000001fffcff

def z1194 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf5ffffd903ffffe1 0xfaffffec81fffff0

def z1195 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x364d3c38e31c1e19 0x9b269e1c718e0f0c

def z1196 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xffffffffffffffe1 0xfffffffffffffff0

def z1197 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0xbffdfffffcc00000 0x5ffefffffe600000

def z1198 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0xd1f47fc0fc23e000 0xe8fa3fe07e11f000

def z1199 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x01c03fc0fc1fe000 0x80e01fe07e0ff000

def z1200 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x01c13fc0031fe000 0x80e09fe0018ff000

def z1201 : W := mkw 0x4bd1d3d71ae885c5 0xa5e8e9eb8d7442e2 0x8922c3c71ce081e6 0x449161e38e7040f3

def z1202 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf5fdffd803ffee00 0xfafeffec01fff700

def z1203 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0xffffffffffc01f81 0x7fffffffffe00fc0

def z1204 : W := mkw 0x0b41db5f5aa00540 0x85a0edafad5002a0 0xcdb3dfdf7fe00fe0 0x66d9efefbff007f0

def z1205 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xfffdffffffe01780 0x7ffefffffff00bc0

def z1206 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x7ffd3c38f31f1e19 0xbffe9e1c798f8f0c

def z1207 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x6009bf8003ff6000 0x3004dfc001ffb000

def z1208 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbffea3a6f0dc919f 0xdfff51d3786e48cf

def z1209 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x31cc3fc0001fe000 0x98e61fe0000ff000

def z1210 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0xf1fdbfc003dfe000 0xf8fedfe001eff000

def z1211 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x76093c38e31f1e19 0xbb049e1c718f8f0c

def z1212 : W := mkw 0xe6382d2af5173abe 0x731c16957a8b9d5f 0xffff7c7fff3fffff 0xffffbe3fff9fffff

def z1213 : W := mkw 0x4bd1d3d712e8c5c5 0xa5e8e9eb897462e2 0x8922c3c710e0e1e6 0x449161e3887070f3

def z1214 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x76dd7c79ef1f1e19 0xbb6ebe3cf78f8f0c

def z1215 : W := mkw 0x0e003b7fd8000000 0x07001dbfec000000 0x0fdd3ffffc000000 0x07ee9ffffe000000

def z1216 : W := mkw 0x469029aad84c9095 0x234814d56c26484a 0xbb6ea3a6fcdc919f 0xddb751d37e6e48cf

def z1217 : W := mkw 0x80200c0861171a18 0x40100604308b8d0c 0x74dd3c18631f1e19 0xba6e9e0c318f8f0c

def z1218 : W := mkw 0x09c1d2d502e8c541 0x84e0e96a817462a0 0xdff6c3c700e3e9e1 0xeffb61e38071f4f0

def z1219 : W := mkw 0xc6302d2af1171a9c 0x63181695788b8d4e 0xfeffbc3ef3df1f9f 0xff7fde1f79ef8fcf

def z1220 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0fe0fffffc000000 0x07f07ffffe000000

def z1221 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x26c93c38e31f1e19 0x93649e1c718f8f0c

def z1222 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf1e0ffc003ffe000 0xf8f07fe001fff000

def z1223 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x724d3c38831f1e19 0xb9269e1c418f8f0c

def z1224 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf3fdffc083ffe019 0xf9feffe041fff00c

def z1225 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x74dd3c18e31f0e18 0xba6e9e0c718f870c

def z1226 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x76dd3c78ef1f7e19 0xbb6e9e3c778fbf0c

def z1227 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0x45d17fd9033fee60 0xa2e8bfec819ff730

def z1228 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0bedbffefc000000 0x05f6dfff7e000000

def z1229 : W := mkw 0x0881d6c0015ac001 0x0440eb6000ad6000 0x01e0ffc0001fe000 0x80f07fe0000ff000

def z1230 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x0ffdbffefc000000 0x07fedfff7e000000

def z1231 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x01c03fc0fc00801e 0x80e01fe07e00400f

def z1232 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf9ffffff03fff7e0 0xfcffffff81fffbf0

def z1233 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf1fdffc0ffffe000 0xf8feffe07ffff000

def z1234 : W := mkw 0x0a01db5f58000000 0x0500edafac000000 0x0ff5dfdffc000000 0x07faefeffe000000

def z1235 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf1fdffd803ffe600 0xf8feffec01fff300

def z1236 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x40917fc0033f6000 0x2048bfe0019fb000

def z1237 : W := mkw 0xa02800002401282a 0x5014000012009415 0xdf224041fc23e87f 0xef912020fe11f43f

def z1238 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0xb1c03fc000dfe000 0xd8e01fe0006ff000

def z1239 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0x6499ffff03ff7fe0 0x324cffff81ffbff0

def z1240 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xffffffc1ffffe861 0xffffffe0fffff430

def z1241 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf9ffffc103ffe060 0xfcffffe081fff030

def z1242 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfe7fe03f03fc1fe1 0xff3ff01f81fe0ff0

def z1243 : W := mkw 0x86202d2af9171a18 0x431016957c8b8d0c 0x76dd3c38ff1f1e19 0xbb6e9e1c7f8f8f0c

def z1244 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xdff77c59ff3fee7f 0xeffbbe2cff9ff73f

def z1245 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x7ffd7c79ff3f7e79 0xbffebe3cff9fbf3c

def z1246 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0ffffffffc00001f 0x07fffffffe00000f

def z1247 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xf7ff7c78e33ffe7f 0xfbffbe3c719fff3f

def z1248 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0xdffffffffc23e861 0xeffffffffe11f430

def z1249 : W := mkw 0x86202d2af1171a18 0x43101695788b8d0c 0x77dd3fb8f31f1e19 0xbbee9fdc798f8f0c

def z1250 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xfb7ee3a690fc919f 0xfdbf71d3487e48cf

def z1251 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x46d13c38e31f1e19 0xa3689e1c718f8f0c

def z1252 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xa96aa3a690dc919e 0xd4b551d3486e48cf

def z1253 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x24993c38631c1600 0x124c9e1c318e0b00

def z1254 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xff7ea3a690dc999f 0xffbf51d3486e4ccf

def z1255 : W := mkw 0xa1a8048027fbe82b 0x50d4024013fdf415 0xf000000003ffe01e 0xf800000001fff00f

def z1256 : W := mkw 0x80200c0861171a18 0x40100604308b8d0c 0x64911c18631f1e00 0x32488e0c318f8f00

def z1257 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xfffee3e7fcfc99ff 0xffff71f3fe7e4cff

def z1258 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x9be63fc0901fe01f 0xcdf31fe0480ff00f

def z1259 : W := mkw 0x09c1d2d502e8c541 0x84e0e96a817462a0 0x8822c38700e001e0 0x441161c3807000f0

def z1260 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xffffc07fffe09fff 0xffffe03ffff04fff

def z1261 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0ffdfffffc00801e 0x87fefffffe00400f

def z1262 : W := mkw 0xa02800002401282a 0x5014000012009415 0xfffec041fce3e87f 0xffff6020fe71f43f

def z1263 : W := mkw 0xa02800002401282a 0x5014000012009415 0x8ff64041fc23e07e 0xc7fb2020fe11f03f

def z1264 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xfb6ea3a690fff19f 0xfdb751d3487ff8cf

def z1265 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xfffdffff03fff780 0xfffeffff81fffbc0

def z1266 : W := mkw 0x80200c0861130a08 0x4010060430898504 0x76dd3c38631f1e01 0xbb6e9e1c318f8f00

def z1267 : W := mkw 0xa02800002401282a 0x5014000012009415 0xde924041fc23e87f 0xef492020fe11f43f

def z1268 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbbffbfa690dc919f 0xddffdfd3486e48cf

def z1269 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x2b6ea3a690dc119f 0x15b751d3486e08cf

def z1270 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xfffffffe03ffff81 0xffffffff01ffffc0

def z1271 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x7edf3c39e31f1e79 0xbf6f9e1cf18f8f3c

def z1272 : W := mkw 0x0e003b7fd8000000 0x07001dbfec000000 0x05c03fd9fc000000 0x02e01fecfe000000

def z1273 : W := mkw 0x84202c28e1130a08 0x4210161470898504 0x76dd3c38e31f0e00 0xbb6e9e1c718f8700

def z1274 : W := mkw 0x0e003b7fd8000000 0x07001dbfec000000 0x0e003fbffc000000 0x07001fdffe000000

def z1275 : W := mkw 0x0140000002a00540 0x80a00000015002a0 0xfe3f803e03e01fe1 0x7f1fc01f01f00ff0

def z1276 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfebfc07f03e37fe1 0x7f5fe03f81f1bff0

def z1277 : W := mkw 0x0a01db5f58000000 0x0500edafac000000 0x05915fd97c000000 0x02c8afecbe000000

def z1278 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x261d3c38031c1600 0x130e9e1c018e0b00

def z1279 : W := mkw 0xa02800002401282a 0x5014000012009415 0xdff74059ff23ee7f 0xeffba02cff91f73f

def z1280 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x76dd7c78e33f7e19 0xbb6ebe3c719fbf0c

def z1281 : W := mkw 0x86202d2af1171a18 0x43101695788b8d0c 0xffffbfbef3df1f99 0xffffdfdf79ef8fcc

def z1282 : W := mkw 0x09c1d6c003fac541 0x84e0eb6001fd62a0 0xf1fdffc003ffee60 0xf8feffe001fff730

def z1283 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x07dd7ff9fc000000 0x03eebffcfe000000

def z1284 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0xf1fd7c78033ff600 0xf8febe3c019ffb00

def z1285 : W := mkw 0x4e103b6ad8041094 0x27081db56c02084a 0x0bc23fe6fc00119f 0x05e11ff37e0008cf

def z1286 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x7edf7c79ff3f7e7f 0xbf6fbe3cff9fbf3f

def z1287 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x05fdffff6c000000 0x02feffffb6000000

def z1288 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x71c03fc0031fe000 0xb8e01fe0018ff000

def z1289 : W := mkw 0x0e01fb6ad8000000 0x0700fdb56c000000 0x07fdfff8fc000000 0x03fefffc7e000000

def z1290 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf7fdfff903fffe61 0xfbfefffc81ffff30

def z1291 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xfbfffffe03fff781 0xfdffffff01fffbc0

def z1292 : W := mkw 0x0180048003fac001 0x00c0024001fd6000 0xfff44041ffffe000 0xfffa2020fffff000

def z1293 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xffffffd903ffee61 0xffffffec81fff730

def z1294 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x56d53c18e31f0e19 0xab6a9e0c718f870c

def z1295 : W := mkw 0x4e103b6ad8041094 0x27081db56c02084a 0x01c03fc0fc00001e 0x00e01fe07e00000f

def z1296 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xf61f803e03e01fe1 0x7b0fc01f01f00ff0

def z1297 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x77dd3c78ff1f1e19 0xbbee9e3c7f8f8f0c

def z1298 : W := mkw 0xa1e9c49527fbed6b 0xd0f4e24a93fdf6b5 0xfe3fc03f03ffffff 0xff1fe01f81ffffff

def z1299 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf3fdffe003fff001 0xf9fefff001fff800

def z1300 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xf7df3c78ff3ffe7f 0xfbef9e3c7f9fff3f

def z1301 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xfbffffc003ffe001 0xfdffffe001fff000

def z1302 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0009bfbefc000000 0x0004dfdf7e000000

def z1303 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x66dd3c38e31f1e00 0x336e9e1c718f8f00

def z1304 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xf41bc03f03e01fe1 0x7a0de01f81f00ff0

def z1305 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xcfffffffffe00fe0 0x67fffffffff007f0

def z1306 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x3ffdfffffc001001 0x1ffefffffe000800

def z1307 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x200b803e03c01fe1 0x1005c01f01e00ff0

def z1308 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x60093c38031f1e00 0x30049e1c018f8f00

def z1309 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf9fdffc11fffe000 0xfcfeffe08ffff000

def z1310 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x77dd3ff8ff001e01 0x3bee9ffc7f800f00

def z1311 : W := mkw 0x09c1d6c003fac541 0x84e0eb6001fd62a0 0xf1ffffc003ffe1e0 0xf8ffffe001fff0f0

def z1312 : W := mkw 0x0e01fb7fd8041010 0x0700fdbfec020808 0xbffffffffcdc1199 0xdffffffffe6e08cc

def z1313 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0x76df3c38e31f1e7f 0xbb6f9e1c718f8f3f

def z1314 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x41fdffc0033fe000 0xa0feffe0019ff000

def z1315 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xfedf3c39ff3ffe7f 0xff6f9e1cff9fff3f

def z1316 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xfeff3c38e31f1e19 0xff7f9e1c718f8f0c

def z1317 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x3ffdfffffc1c0000 0x9ffefffffe0e0000

def z1318 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x4fffffffff201fe1 0x27ffffffff900ff0

def z1319 : W := mkw 0x0000040001120000 0x0000020000890000 0x761d3c38031c1e01 0x3b0e9e1c018e0f00

def z1320 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x26093c38031c1e01 0x13049e1c018e0f00

def z1321 : W := mkw 0x098016c003fac001 0x04c00b6001fd6000 0xf1dd3fc003ffe000 0xf8ee9fe001fff000

def z1322 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x46dd3c38e31f0e18 0xa36e9e1c718f870c

def z1323 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x2089bfc003df6000 0x1044dfe001efb000

def z1324 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x7edf3c38f31f1e1f 0xbf6f9e1c798f8f0f

def z1325 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0x3a4ea3a690dc119f 0x9d2751d3486e08cf

def z1326 : W := mkw 0x09c016c003fac541 0x84e00b6001fd62a0 0xf1c23fc003ffffe1 0xf8e11fe001fffff0

def z1327 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x05d9fffffc000000 0x02ecfffffe000000

def z1328 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf129ffc003ffe000 0xf894ffe001fff000

def z1329 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x9be63fc0fc00801f 0xcdf31fe07e00400f

def z1330 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf7fdfff803ffe000 0xfbfefffc01fff000

def z1331 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xfbfea3a690df919f 0xfdff51d3486fc8cf

def z1332 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xffff7c79ff3f1e79 0xffffbe3cff9f8f3c

def z1333 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xc1f1ffc003ffe000 0xe0f8ffe001fff000

def z1334 : W := mkw 0x09c1d6c003fac541 0x84e0eb6001fd62a0 0xfbffffe603ffffe1 0xfdfffff301fffff0

def z1335 : W := mkw 0x4e11fb7fd8041094 0x2708fdbfec02084a 0xbffffffffcc0119f 0x5ffffffffe6008cf

def z1336 : W := mkw 0xa0280c0865173a3a 0x50140604328b9d1d 0xfff75c59ff3ffe7f 0xfffbae2cff9fff3f

def z1337 : W := mkw 0x0e003b7fd8000000 0x07001dbfec000000 0x09c03fc7fc000000 0x04e01fe3fe000000

def z1338 : W := mkw 0xa4282c28e5173a3a 0x52141614728b9d1d 0xf7fd7c78ff3ffe1f 0xfbfebe3c7f9fff0f

def z1339 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0xf6dd3c38e33ffe19 0xfb6e9e1c719fff0c

def z1340 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfe3fc03f93e01fff 0x7f1fe01fc9f00fff

def z1341 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x61fdffc003ff6000 0x30feffe001ffb000

def z1342 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0db9ffff7c000000 0x06dcffffbe000000

def z1343 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x8ffdfffffc20e000 0x47fefffffe107000

def z1344 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x0be43fc0fc000000 0x05f21fe07e000000

def z1345 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x81fdffc000ffe000 0xc0feffe0007ff000

def z1346 : W := mkw 0x0f01fb7fdaa00000 0x0780fdbfed500000 0xffffffffffe00861 0x7ffffffffff00430

def z1347 : W := mkw 0xa02800002401282a 0x5014000012009415 0xffffc07fffe3ffff 0xffffe03ffff1ffff

def z1348 : W := mkw 0x0e003b6ad8000000 0x07001db56c000000 0x09e0bfc6fc000000 0x04f05fe37e000000

def z1349 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x2009bf8003dfe000 0x9004dfc001eff000

def z1350 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0xbffffffffcc0919f 0xdffffffffe6048cf

def z1351 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0xfe3fffbfffe01fe1 0x7f1fffdffff00ff0

def z1352 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x89e2ffc7fce001e0 0x44f17fe3fe7000f0

def z1353 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x61d9ffc003ffe000 0xb0ecffe001fff000

def z1354 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x74993c38631f1e19 0xba4c9e1c318f8f0c

def z1355 : W := mkw 0x4e11fb7fd8041094 0x2708fdbfec02084a 0x0ffdfffffc001180 0x07fefffffe0008c0

def z1356 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0fc9bffffc000000 0x07e4dffffe000000

def z1357 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfe3fc03f03e3ffe1 0xff1fe01f81f1fff0

def z1358 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xce33c03f03e01fe1 0x6719e01f81f00ff0

def z1359 : W := mkw 0x0e01fb6ad8000000 0x0700fdb56c000000 0x0bfdffe6fc000000 0x05fefff37e000000

def z1360 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbf6ea3be90dc9f9f 0xdfb751df486e4fcf

def z1361 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x70dd3c38031f1e19 0xb86e9e1c018f8f0c

def z1362 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xb16ca3a690dc919e 0xd8b651d3486e48cf

def z1363 : W := mkw 0xe6382d2af5173abe 0x731c16957a8b9d5f 0x7edf3c3fff1f1fff 0xbf6f9e1fff8f8fff

def z1364 : W := mkw 0x0981d6d503fac001 0x04c0eb6a81fd6000 0xf5fdffd903ffe000 0xfafeffec81fff000

def z1365 : W := mkw 0x0180048003fac001 0x00c0024001fd6000 0xf1fdbf8003ffe000 0xf8fedfc001fff000

def z1366 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x44913c18631f0e00 0x22489e0c318f8700

def z1367 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbf6ea3a7fcdc919f 0xdfb751d3fe6e48cf

def z1368 : W := mkw 0x80200c0861171a18 0x40100604308b8d0c 0x769d1c38631f1e19 0xbb4e8e1c318f8f0c

def z1369 : W := mkw 0x0c01fa7dc8000000 0x0600fd3ee4000000 0x07fdfff9ec000000 0x03fefffcf6000000

def z1370 : W := mkw 0x0600293fd8000000 0x0300149fec000000 0x0ffdbfbffc000000 0x07fedfdffe000000

def z1371 : W := mkw 0xe638292af4053abe 0x731c14957a029d5f 0x0e02003ffc001fff 0x0701001ffe000fff

def z1372 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x71ddbfc003dfe000 0xb8eedfe001eff000

def z1373 : W := mkw 0x86202d2af1171a18 0x43101695788b8d0c 0x7edd3c3ef31f1e19 0xbf6e9e1f798f8f0c

def z1374 : W := mkw 0xa02800002401282a 0x5014000012009415 0xfff64041ff23fe7f 0xfffb2020ff91ff3f

def z1375 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x20093c38e31c1618 0x10049e1c718e0b0c

def z1376 : W := mkw 0x0941d25502a00540 0x84a0e92a815002a0 0xfe3fffbf03e01fe1 0x7f1fffdf81f00ff0

def z1377 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0xf00bbfbe03ffffe1 0xf805dfdf01fffff0

def z1378 : W := mkw 0x86202d2af1171a18 0x43101695788b8d0c 0xffffbfbef31f9e1f 0xffffdfdf798fcf0f

def z1379 : W := mkw 0x0e403b7fd8000540 0x87201dbfec0002a0 0x0fc23ffffc001fe1 0x07e11ffffe000ff0

def z1380 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x76911c38e31f1e19 0xbb488e1c718f8f0c

def z1381 : W := mkw 0x0941d25502a00540 0x84a0e92a815002a0 0xff3fc3ff03e01fe1 0x7f9fe1ff81f00ff0

def z1382 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x0ffffffffc000861 0x07fffffffe000430

def z1383 : W := mkw 0x0981d6d503fac001 0x04c0eb6a81fd6000 0xfffdffff03fffe01 0xfffeffff81ffff00

def z1384 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x0ffdfffffc200060 0x07fefffffe100030

def z1385 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x01c03fc0901fe01e 0x80e01fe0480ff00f

def z1386 : W := mkw 0x0901d64003b24000 0x0480eb2001d92000 0x71fdffc0033f6000 0xb8feffe0019fb000

def z1387 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0x6e3dc03f03e01fe0 0x371ee01f81f00ff0

def z1388 : W := mkw 0x0881d6c0015ac001 0x0440eb6000ad6000 0x71fdffc0031fe000 0xb8feffe0018ff000

def z1389 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x01c07fc1fc000000 0x00e03fe0fe000000

def z1390 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x41d13fc0031fe000 0xa0e89fe0018ff000

def z1391 : W := mkw 0x09c1d6d503fac541 0x84e0eb6a81fd62a0 0x21c9bffe03dff780 0x90e4dfff01effbc0

def z1392 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf1c9bfc003ffe000 0xf8e4dfe001fff000

def z1393 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x76dd7c39e33f1e79 0xbb6ebe1cf19f8f3c

def z1394 : W := mkw 0x0f01fb7fdaa00000 0x0780fdbfed500000 0x4ffdffffff200000 0x27feffffff900000

def z1395 : W := mkw 0x0941d25502a00540 0x84a0e92a815002a0 0xfebfdc7f03e01fe1 0x7f5fee3f81f00ff0

def z1396 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x60993c38031f1600 0x304c9e1c018f8b00

def z1397 : W := mkw 0xa02800002401282a 0x5014000012009415 0xd9e24041fc23e87f 0xecf12020fe11f43f

def z1398 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x2ffdfffffcc01180 0x17fefffffe6008c0

def z1399 : W := mkw 0x0e01fb6ad8000000 0x0700fdb56c000000 0x01e0ffc0fc000000 0x00f07fe07e000000

def z1400 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0x01dd3fc0001fe000 0x80ee9fe0000ff000

def z1401 : W := mkw 0x4e11fb7fd8000084 0x2708fdbfec000042 0x0ffffffffc000186 0x07fffffffe0000c3

def z1402 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbb6ee3e690fcf19f 0xddb771f3487e78cf

def z1403 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf1fdffe603fff180 0xf8fefff301fff8c0

def z1404 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf9ffffc603ffe180 0xfcffffe301fff0c0

def z1405 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf5fdffc103ffe860 0xfafeffe081fff430

def z1406 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfe3fc03f03e09fff 0xff1fe01f81f04fff

def z1407 : W := mkw 0xe6b82daaf55fbabf 0x735c16d57aafdd5f 0x01c03fc0fc1fe01e 0x80e01fe07e0ff00f

def z1408 : W := mkw 0x098016c003fac001 0x04c00b6001fd6000 0x21c03fc003dfe000 0x90e01fe001eff000

def z1409 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0x01c07fc0003fe000 0x80e03fe0001ff000

def z1410 : W := mkw 0xa02800002401282a 0x5014000012009415 0xdff64079fc23fe7f 0xeffb203cfe11ff3f

def z1411 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xb14aa3a690dc919f 0xd8a551d3486e48cf

def z1412 : W := mkw 0x469021a2904c9095 0x234810d14826484a 0xbb2283a690dc919f 0xdd9141d3486e48cf

def z1413 : W := mkw 0x0981d6c003fac001 0x04c0eb6001fd6000 0xf1fdffc093ffe01e 0xf8feffe049fff00f

def z1414 : W := mkw 0x0e41fb7fd8000540 0x8720fdbfec0002a0 0x7fffffffff001fe1 0x3fffffffff800ff0

def z1415 : W := mkw 0x0141c01502a00540 0x80a0e00a815002a0 0xfe7fc03f83e01ff9 0xff3fe01fc1f00ffc

def z1416 : W := mkw 0x088016c0015ac001 0x04400b6000ad6000 0xf1fcffc000ffe000 0xf8fe7fe0007ff000

def z1417 : W := mkw 0x0f41fb7fdaa00540 0x87a0fdbfed5002a0 0x0ffdffffff000600 0x07feffffff800300

def z1418 : W := mkw 0x04002c28c1161210 0x02001614608b0908 0x2ffd7c79ff1c1600 0x17febe3cff8e0b00

def z1419 : W := mkw 0x0e01fb7fd8000000 0x0700fdbfec000000 0x9ffffffffc000001 0x4ffffffffe000000

def z1420 : W := mkw 0x84202c28e1171a18 0x42101614708b8d0c 0x76ddbc3ee3df1f99 0xbb6ede1f71ef8fcc

def z1421 : W := mkw 0x0981d6d503fac001 0x04c0eb6a81fd6000 0xffffffff03fff181 0xffffffff81fff8c0

def z1422 : W := mkw 0x0881d6c0015ac001 0x0440eb6000ad6000 0xb1fdffc000dfe000 0xd8feffe0006ff000

def z1423 : W := mkw 0x469029aad04c9095 0x234814d56826484a 0xbf6ea3bef0dc919f 0xdfb751df786e48cf

def z1424 : W := mkw 0xa02800002401282a 0x5014000012009415 0xcfb24041fc23e87f 0x67d92020fe11f43f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z8,z9,z2,z4,z5,z6])],[],[(0,[z8,z1,z2,z4,z10,z5,z6]),(0,[z8,z1,z2,z4,z5,z11,z6]),(0,[z12,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z13,z5,z6])],[(0,[z8,z0,z2,z14,z4,z5,z6])],[(0,[z15,z8,z0,z2,z4,z5,z6]),(0,[z8,z1,z2,z16,z4,z5,z6]),(0,[z8,z17,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z18,z19]),(0,[z8,z20,z2,z21,z4,z5,z6]),(0,[z8,z22,z20,z0,z2,z4,z6])],[(0,[z8,z23,z24,z2,z4,z5,z6]),(1,[z8,z0,z25,z4,z5,z6]),(0,[z8,z0,z26,z2,z4,z5,z6]),(0,[z8,z27,z22,z0,z2,z4,z6])],[(0,[z28,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z29])],[(0,[z8,z30,z23,z2,z4,z5,z6]),(0,[z8,z31,z0,z32,z4,z5,z6]),(0,[z33,z8,z0,z34,z4,z5,z6]),(0,[z35,z8,z0,z2,z4,z5,z6]),(0,[z36,z8,z0,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z5,z37])],[(0,[z38,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z39,z5,z6,z40]),(0,[z8,z0,z2,z4,z5,z6,z41])],[(0,[z8,z0,z2,z4,z5,z42,z6])],[(0,[z8,z0,z3,z4,z5,z43,z6]),(0,[z8,z0,z2,z4,z5,z44,z6]),(0,[z8,z45,z0,z21,z4,z5,z6]),(0,[z7,z8,z22,z0,z2,z4,z6])],[],[(1,[z8,z22,z1,z2,z4,z6]),(0,[z46,z8,z22,z0,z2,z4,z6])],[(0,[z8,z0,z2,z4,z47,z6,z37]),(0,[z8,z0,z2,z4,z48,z5,z6]),(0,[z8,z49,z0,z2,z4,z6,z37])],[(0,[z50,z8,z0,z2,z4,z5,z6])]],
   [[(0,[z8,z0,z2,z3,z4,z5,z6]),(0,[z8,z0,z2,z51,z4,z5,z6])],[(0,[z52,z8,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z53,z5,z6]),(0,[z54,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z55,z6]),(0,[z56,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z57,z37])],[(0,[z8,z23,z20,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z58,z5,z37])],[(0,[z8,z0,z2,z4,z59,z5,z6])],[(0,[z8,z23,z2,z4,z5,z60,z6]),(0,[z8,z23,z2,z4,z5,z6,z61]),(0,[z8,z62,z0,z2,z4,z5,z6])],[],[(0,[z8,z0,z2,z4,z5,z63,z6])],[(0,[z8,z64,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z65,z5,z6]),(0,[z8,z0,z2,z66,z4,z5,z6])],[(0,[z67,z8,z0,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z68,z5,z6])],[(0,[z8,z69,z0,z2,z4,z5,z6])],[(1,[z0,z32,z3,z4,z5,z6]),(1,[z70,z0,z2,z4,z43,z6]),(0,[z8,z0,z71,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z72])],[(0,[z73,z8,z22,z0,z2,z4,z6])],[(0,[z74,z8,z0,z2,z4,z5,z6]),(0,[z8,z23,z2,z4,z58,z5,z6]),(0,[z8,z0,z2,z4,z75,z5,z6]),(0,[z8,z0,z2,z76,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z77,z6])],[(0,[z8,z78,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z79,z5,z6]),(0,[z8,z0,z2,z4,z5,z80,z6]),(0,[z8,z24,z20,z2,z4,z5,z6]),(0,[z81,z8,z0,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z61]),(0,[z8,z0,z2,z4,z82,z5,z6]),(0,[z8,z31,z0,z2,z4,z5,z6]),(0,[z83,z8,z0,z2,z4,z6,z37])]],
   [[(0,[z84,z8,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z85]),(0,[z8,z0,z86,z2,z4,z5,z6]),(0,[z87,z8,z0,z2,z4,z5,z6]),(0,[z88,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z89,z4,z6,z61])],[(0,[z8,z23,z2,z4,z5,z6,z40]),(0,[z8,z0,z32,z4,z5,z90,z6]),(1,[z8,z0,z2,z4,z5,z91]),(0,[z8,z92,z0,z2,z4,z5,z6]),(0,[z8,z0,z93,z2,z4,z5,z6]),(0,[z8,z49,z0,z21,z4,z5,z6]),(0,[z7,z8,z0,z94,z4,z5,z6])],[(0,[z95,z8,z1,z2,z4,z5,z6]),(0,[z8,z23,z2,z96,z4,z5,z6]),(0,[z8,z0,z4,z97,z5,z60,z6]),(0,[z98,z8,z0,z2,z4,z5,z99])],[(0,[z8,z100,z101,z0,z4,z5,z6])],[(0,[z8,z0,z102,z3,z4,z5,z6]),(0,[z8,z0,z103,z32,z4,z5,z6])],[(0,[z8,z0,z1,z3,z4,z5,z6]),(1,[z8,z0,z104,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z18,z37]),(0,[z8,z101,z0,z102,z4,z5,z6]),(0,[z98,z8,z0,z2,z105,z5,z6])],[],[(0,[z8,z0,z0,z2,z4,z5,z6]),(0,[z8,z0,z3,z4,z5,z60,z6]),(0,[z8,z0,z2,z4,z5,z106,z6]),(0,[z8,z0,z2,z4,z5,z107,z6])],[(0,[z8,z22,z0,z2,z4,z53,z6]),(0,[z108,z8,z0,z2,z4,z5,z6])],[(0,[z109,z8,z110,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z111,z5,z6])],[(0,[z112,z8,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z113,z4,z5,z6]),(0,[z8,z0,z2,z4,z114,z5,z6])],[],[(0,[z8,z1,z2,z96,z4,z5,z6]),(0,[z67,z8,z23,z2,z4,z5,z6]),(0,[z8,z115,z0,z32,z4,z5,z6]),(0,[z116,z8,z117,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z6,z118]),(0,[z8,z22,z0,z2,z4,z47,z6]),(0,[z8,z0,z2,z4,z119,z5,z6]),(0,[z8,z0,z2,z4,z39,z6,z37])],[(0,[z8,z23,z2,z4,z5,z18,z6]),(0,[z8,z0,z3,z4,z58,z5,z6]),(0,[z120,z8,z0,z2,z4,z5,z6])]],
   [[(1,[z8,z121,z0,z4,z5,z6]),(0,[z8,z101,z0,z4,z5,z6,z99]),(0,[z122,z8,z0,z2,z4,z5,z6]),(1,[z8,z123,z0,z2,z4,z6]),(0,[z8,z22,z22,z0,z2,z4,z6])],[(0,[z33,z8,z0,z3,z4,z5,z6]),(0,[z70,z8,z0,z2,z68,z5,z6])],[(0,[z8,z0,z32,z21,z4,z5,z6]),(0,[z124,z8,z0,z2,z4,z6,z37]),(0,[z67,z8,z0,z2,z4,z5,z125]),(0,[z8,z0,z2,z4,z126,z5,z6]),(0,[z8,z127,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z128,z6]),(0,[z8,z0,z2,z4,z53,z6,z61]),(1,[z8,z0,z129,z4,z5,z6])],[(0,[z8,z0,z3,z4,z5,z6,z40]),(0,[z130,z8,z0,z2,z4,z5,z6]),(1,[z8,z131,z0,z4,z60,z6]),(0,[z7,z8,z0,z2,z5,z6,z40]),(0,[z8,z0,z2,z4,z5,z6,z132]),(0,[z8,z0,z2,z4,z6,z37,z133])],[(0,[z8,z23,z0,z2,z4,z6,z37]),(0,[z70,z0,z2,z4,z5,z43,z6]),(0,[z8,z134,z0,z2,z4,z5,z6]),(0,[z8,z0,z94,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z6,z135]),(0,[z8,z0,z2,z4,z5,z125,z40]),(0,[z136,z8,z0,z2,z4,z5,z6])],[(0,[z8,z23,z2,z137,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z97,z6])],[(0,[z84,z8,z0,z2,z138,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z139]),(0,[z140,z8,z0,z2,z4,z6,z37])],[(0,[z8,z0,z2,z2,z4,z5,z6]),(0,[z141,z8,z0,z2,z4,z5,z6]),(0,[z8,z142,z0,z2,z4,z5,z6]),(0,[z8,z110,z0,z2,z4,z143,z6]),(0,[z98,z8,z0,z2,z4,z5,z144])],[(0,[z8,z145,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z146,z4,z5,z6]),(0,[z70,z109,z8,z0,z2,z4,z6]),(1,[z8,z0,z147,z4,z5,z6]),(0,[z8,z148,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z143,z6,z37])],[(1,[z8,z0,z149,z4,z5,z6]),(0,[z8,z23,z2,z4,z5,z43,z6]),(1,[z8,z117,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z150]),(0,[z8,z0,z103,z2,z4,z5,z6])],[(0,[z8,z8,z0,z32,z4,z5,z6]),(0,[z151,z8,z0,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z152,z6]),(0,[z8,z0,z2,z4,z5,z153,z6])],[(0,[z8,z0,z3,z4,z143,z5,z6]),(0,[z154,z8,z0,z2,z4,z5,z6]),(0,[z8,z100,z0,z2,z4,z155,z6]),(1,[z8,z0,z2,z105,z5,z6])],[(0,[z8,z23,z2,z4,z5,z144,z6])]],
   [[(0,[z8,z0,z2,z156,z4,z5,z6]),(1,[z8,z22,z0,z2,z4,z37])],[(0,[z52,z8,z0,z157,z4,z5,z6]),(1,[z158,z8,z0,z2,z4,z6]),(0,[z67,z0,z2,z3,z4,z5,z6]),(0,[z8,z159,z0,z2,z4,z5,z6]),(0,[z67,z8,z0,z2,z4,z5,z6]),(0,[z8,z31,z0,z2,z4,z6,z61])],[(0,[z8,z23,z2,z4,z47,z5,z6]),(0,[z8,z0,z3,z4,z5,z18,z6]),(0,[z124,z8,z0,z160,z4,z5,z6]),(0,[z161,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z162,z6]),(0,[z8,z0,z2,z4,z5,z163,z6]),(0,[z98,z8,z0,z102,z4,z5,z6]),(0,[z8,z164,z22,z0,z2,z4,z6])],[(0,[z8,z0,z2,z4,z5,z165,z6]),(0,[z166,z8,z0,z2,z4,z5,z6]),(0,[z98,z167,z0,z2,z4,z5,z6]),(1,[z8,z0,z2,z168,z5,z6]),(0,[z8,z0,z2,z4,z169,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z170])],[(0,[z8,z115,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z171,z5,z6]),(0,[z8,z0,z104,z2,z4,z5,z6]),(0,[z8,z0,z2,z172,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z125]),(0,[z8,z0,z2,z4,z5,z6,z173]),(0,[z8,z174,z0,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z43,z6]),(0,[z8,z31,z1,z2,z4,z5,z6]),(0,[z33,z8,z23,z2,z4,z5,z6]),(0,[z175,z8,z0,z2,z4,z5,z6]),(0,[z176,z8,z0,z147,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z177]),(1,[z95,z8,z2,z178,z5,z6]),(0,[z8,z110,z2,z4,z179,z5,z6])],[(0,[z8,z110,z0,z2,z4,z163,z6]),(0,[z180,z8,z0,z2,z4,z5,z6])],[],[(0,[z8,z100,z0,z2,z4,z6,z37]),(0,[z8,z131,z0,z2,z4,z97,z6]),(0,[z8,z0,z2,z4,z181,z5,z6]),(0,[z8,z123,z0,z2,z4,z5,z6])],[(0,[z8,z49,z182,z0,z4,z5,z6]),(0,[z95,z8,z2,z4,z178,z5,z6]),(0,[z8,z22,z0,z2,z183,z4,z6]),(0,[z8,z22,z184,z0,z2,z4,z6])],[(0,[z8,z0,z2,z4,z5,z185,z6]),(1,[z186,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z89,z146,z5,z6]),(1,[z8,z0,z2,z187,z5,z6]),(0,[z33,z8,z0,z2,z4,z5,z125]),(0,[z8,z188,z0,z2,z4,z5,z6])],[(1,[z8,z0,z189,z2,z4,z6]),(0,[z8,z0,z190,z2,z4,z5,z6])],[(0,[z191,z8,z0,z3,z4,z5,z6]),(0,[z8,z0,z32,z4,z179,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z192]),(0,[z8,z0,z102,z2,z4,z5,z6]),(0,[z98,z8,z0,z4,z5,z6,z99])],[(0,[z8,z0,z1,z2,z4,z5,z6]),(0,[z186,z8,z0,z2,z4,z6,z37]),(0,[z8,z0,z32,z4,z5,z6,z193]),(0,[z8,z0,z2,z4,z5,z194,z6]),(0,[z195,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z196]),(0,[z8,z0,z2,z197,z4,z5,z6])],[(0,[z8,z198,z0,z2,z4,z5,z6]),(0,[z8,z199,z0,z2,z4,z5,z6])]],
   [[(0,[z98,z8,z45,z0,z4,z5,z6]),(0,[z8,z0,z2,z183,z89,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z200])],[(0,[z52,z8,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z201,z5,z6])],[(0,[z8,z0,z3,z4,z5,z144,z6]),(0,[z176,z8,z202,z2,z4,z5,z6])],[(0,[z8,z8,z0,z2,z4,z5,z6]),(0,[z8,z23,z32,z2,z4,z5,z6]),(0,[z8,z22,z101,z0,z2,z4,z6])],[(0,[z8,z131,z0,z3,z4,z5,z6]),(0,[z8,z0,z203,z2,z4,z5,z6]),(0,[z204,z8,z0,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z143,z6])],[(0,[z8,z0,z2,z157,z4,z5,z6]),(0,[z205,z8,z23,z2,z4,z5,z6]),(0,[z8,z0,z3,z4,z47,z5,z6]),(0,[z8,z0,z32,z4,z97,z5,z6]),(0,[z8,z0,z206,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z125])],[(0,[z8,z207,z0,z2,z4,z6,z37])],[(0,[z8,z208,z0,z2,z4,z5,z6])],[(0,[z8,z0,z209,z2,z4,z5,z6]),(0,[z8,z31,z0,z2,z89,z5,z6]),(0,[z8,z0,z210,z2,z4,z5,z6])],[],[(0,[z124,z8,z211,z2,z4,z5,z6]),(0,[z33,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z212,z2,z4,z5,z6])],[(0,[z120,z8,z0,z32,z4,z5,z6]),(0,[z70,z8,z0,z2,z4,z6,z37])],[(0,[z8,z23,z2,z4,z5,z6,z99]),(0,[z8,z0,z2,z4,z5,z6,z213]),(0,[z8,z0,z2,z4,z214,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z215]),(1,[z167,z0,z2,z4,z5,z6])],[(0,[z0,z2,z146,z4,z47,z5,z6]),(0,[z176,z8,z0,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z216,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z217]),(0,[z8,z0,z103,z2,z4,z60,z6])],[(0,[z8,z1,z32,z2,z4,z5,z6]),(0,[z84,z8,z1,z2,z4,z5,z6]),(0,[z8,z0,z32,z218,z4,z5,z6]),(0,[z8,z0,z2,z4,z219,z5,z6]),(0,[z8,z220,z0,z2,z4,z5,z6]),(0,[z8,z101,z0,z2,z4,z6,z37])],[(0,[z8,z30,z0,z2,z4,z5,z6]),(0,[z109,z8,z0,z2,z4,z6,z37]),(1,[z8,z0,z4,z5,z6,z221])]],
   [[(0,[z8,z22,z0,z2,z3,z4,z6]),(0,[z8,z45,z2,z21,z4,z5,z6]),(0,[z8,z49,z22,z0,z2,z4,z6]),(0,[z8,z222,z0,z2,z4,z5,z6])],[(0,[z223,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z16,z47,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z224]),(0,[z8,z225,z0,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z60,z6]),(0,[z226,z8,z0,z2,z4,z5,z6]),(0,[z8,z22,z0,z1,z2,z4,z6]),(0,[z191,z8,z23,z2,z4,z5,z6]),(0,[z8,z23,z2,z4,z39,z5,z6]),(1,[z8,z22,z23,z2,z4,z6]),(0,[z46,z8,z0,z3,z4,z5,z6]),(0,[z98,z8,z49,z0,z4,z5,z6]),(0,[z8,z227,z0,z218,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z163,z6]),(0,[z8,z0,z2,z4,z60,z6,z37])],[(0,[z52,z0,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z37,z224])],[(0,[z8,z100,z0,z4,z39,z5,z6])],[(0,[z8,z0,z2,z4,z228,z5,z6]),(0,[z33,z67,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z229])],[(0,[z8,z145,z0,z32,z4,z5,z6]),(0,[z8,z230,z0,z2,z4,z5,z6])],[(0,[z116,z0,z2,z4,z47,z5,z6]),(0,[z8,z0,z2,z231,z4,z5,z6])],[(0,[z52,z8,z0,z2,z4,z5,z6]),(0,[z232,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z233,z5,z6]),(0,[z8,z0,z2,z4,z234,z5,z6])],[(0,[z8,z131,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z21,z4,z6,z37]),(0,[z8,z0,z2,z4,z235,z5,z6]),(0,[z8,z0,z2,z4,z5,z236,z6])],[(0,[z8,z1,z2,z4,z58,z5,z6]),(0,[z237,z8,z0,z2,z4,z6,z37]),(0,[z8,z110,z0,z3,z4,z5,z6]),(0,[z8,z0,z32,z4,z5,z19,z6]),(1,[z8,z0,z2,z68,z5,z6]),(0,[z8,z238,z0,z2,z4,z5,z6])],[(0,[z8,z115,z1,z2,z4,z5,z6]),(0,[z8,z0,z3,z239,z4,z5,z6]),(1,[z8,z0,z3,z4,z6,z37]),(1,[z8,z0,z2,z214,z5,z6])],[(1,[z8,z0,z2,z4,z6,z240])],[(0,[z8,z0,z2,z241,z4,z5,z6]),(0,[z237,z8,z242,z2,z4,z5,z6]),(0,[z67,z8,z0,z32,z4,z5,z6]),(0,[z8,z243,z0,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z89,z4,z6])],[(0,[z8,z23,z2,z4,z143,z5,z6]),(0,[z8,z0,z2,z4,z244,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z40]),(0,[z8,z0,z3,z4,z5,z6,z99]),(0,[z70,z8,z0,z245,z4,z5,z6])]],
   [[(0,[z8,z0,z3,z4,z5,z246,z6])],[],[(0,[z8,z0,z2,z247,z4,z5,z6]),(0,[z8,z0,z2,z248,z4,z5,z6])],[(0,[z249,z45,z0,z2,z4,z5,z6]),(0,[z8,z250,z0,z2,z4,z5,z6]),(1,[z8,z0,z2,z4,z251,z6]),(0,[z8,z252,z22,z0,z2,z4,z6])],[(0,[z191,z8,z0,z253,z4,z5,z6]),(0,[z8,z23,z2,z4,z254,z5,z6]),(0,[z8,z0,z32,z4,z5,z6,z37]),(1,[z8,z255,z2,z4,z5,z6])],[(0,[z7,z8,z23,z2,z4,z5,z6]),(0,[z8,z0,z3,z4,z39,z5,z6]),(0,[z8,z22,z0,z2,z4,z6,z125]),(0,[z8,z24,z0,z2,z178,z5,z6])],[(0,[z191,z8,z0,z2,z4,z5,z6]),(0,[z191,z0,z2,z3,z4,z5,z6]),(0,[z95,z8,z24,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z178,z5,z6]),(0,[z8,z0,z2,z4,z6,z72,z37]),(0,[z256,z8,z0,z2,z4,z5,z6])],[(0,[z46,z8,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z257]),(0,[z8,z49,z45,z2,z4,z5,z6])],[(0,[z8,z258,z0,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z143,z5,z6]),(0,[z70,z8,z0,z2,z4,z5,z259]),(0,[z8,z0,z2,z4,z260,z5,z6])],[(0,[z8,z8,z1,z2,z4,z5,z6]),(0,[z8,z0,z1,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z261,z6])],[(0,[z8,z0,z3,z262,z4,z5,z6]),(0,[z8,z211,z0,z2,z4,z5,z6]),(0,[z98,z8,z0,z2,z4,z6,z37])],[(0,[z8,z263,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z264,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z18,z6]),(0,[z8,z0,z2,z4,z265,z5,z6]),(0,[z8,z0,z2,z4,z43,z6,z37]),(0,[z67,z8,z86,z2,z4,z5,z6]),(0,[z266,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z267,z4,z5,z6])],[(1,[z8,z22,z0,z32,z4,z6]),(0,[z8,z0,z4,z5,z6,z221,z193])],[(0,[z67,z0,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z268,z6]),(0,[z8,z0,z2,z4,z5,z6,z269]),(0,[z8,z0,z2,z270,z4,z5,z6])]],
   [[(1,[z8,z23,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z271,z5,z6]),(0,[z109,z176,z8,z0,z2,z4,z6]),(0,[z8,z272,z0,z2,z4,z5,z6]),(0,[z8,z131,z0,z103,z4,z5,z6])],[(0,[z191,z67,z0,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z146,z4,z6]),(0,[z8,z182,z0,z4,z5,z6,z99]),(0,[z8,z0,z2,z16,z39,z5,z6])],[(1,[z8,z0,z2,z4,z273,z6]),(0,[z8,z0,z2,z274,z4,z5,z6])],[(0,[z8,z0,z4,z5,z144,z6,z99]),(0,[z8,z0,z2,z4,z275,z5,z6]),(0,[z8,z22,z0,z102,z2,z4,z6])],[(0,[z8,z0,z2,z276,z4,z5,z6]),(0,[z8,z0,z209,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z143,z53,z6]),(0,[z277,z8,z0,z2,z4,z5,z6]),(0,[z8,z24,z0,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z179,z6,z37]),(0,[z8,z0,z2,z4,z11,z6,z37]),(1,[z8,z101,z0,z183,z5,z6]),(0,[z8,z27,z0,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z6,z6])],[(0,[z8,z22,z0,z3,z4,z5,z6]),(0,[z116,z8,z0,z190,z4,z5,z6])],[(0,[z33,z8,z0,z32,z4,z5,z6]),(0,[z116,z8,z0,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z5,z6,z278]),(0,[z8,z0,z2,z4,z5,z279,z6])],[(0,[z8,z20,z0,z3,z4,z5,z6])],[(0,[z8,z280,z0,z2,z4,z5,z6])],[(1,[z186,z1,z2,z4,z5,z6]),(0,[z8,z281,z0,z2,z4,z5,z6]),(1,[z8,z202,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z282]),(0,[z8,z0,z2,z283,z4,z5,z6]),(0,[z84,z8,z0,z284,z4,z5,z6]),(1,[z8,z0,z2,z4,z155,z6])],[(0,[z285,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z32,z183,z4,z5,z6]),(0,[z8,z0,z2,z4,z286,z5,z6]),(0,[z8,z22,z0,z2,z4,z58,z6])],[(0,[z46,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z287,z4,z5,z6])],[],[(0,[z8,z1,z2,z4,z5,z144,z6]),(0,[z8,z0,z2,z4,z288,z5,z6]),(0,[z8,z289,z23,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z290]),(0,[z291,z8,z0,z2,z4,z5,z6]),(0,[z292,z8,z0,z2,z4,z5,z6])],[(0,[z52,z8,z1,z2,z4,z5,z6]),(0,[z8,z0,z293,z2,z4,z5,z6]),(0,[z109,z8,z0,z2,z4,z179,z6])]],
   [[(0,[z8,z1,z2,z4,z47,z5,z6]),(0,[z8,z0,z2,z294,z4,z5,z6]),(1,[z295,z0,z2,z4,z5,z6])],[(0,[z8,z22,z45,z0,z2,z4,z6])],[(0,[z8,z49,z2,z4,z5,z6,z193])],[(0,[z8,z0,z2,z4,z10,z5,z6]),(0,[z8,z296,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z297,z6]),(0,[z8,z0,z2,z4,z5,z6,z298]),(0,[z8,z110,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z11,z6]),(0,[z8,z0,z299,z2,z4,z5,z6])],[(0,[z8,z0,z2,z300,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z301,z6]),(0,[z8,z0,z302,z2,z4,z5,z6]),(1,[z8,z0,z2,z4,z6,z37])],[(0,[z8,z0,z2,z218,z4,z6,z37]),(0,[z8,z0,z2,z16,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z6,z303]),(0,[z8,z304,z0,z2,z4,z5,z6])],[(1,[z8,z242,z2,z4,z5,z6]),(0,[z305,z8,z0,z2,z4,z5,z6]),(1,[z8,z0,z2,z4,z306,z6])],[(0,[z307,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z308])],[(0,[z8,z20,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z309]),(0,[z310,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z311,z4,z5,z6])],[(0,[z8,z22,z23,z2,z4,z5,z6]),(1,[z8,z0,z2,z4,z58,z37])],[(0,[z8,z0,z2,z4,z312,z5,z6]),(1,[z67,z0,z2,z4,z5,z18]),(0,[z8,z49,z182,z2,z4,z5,z6])],[(0,[z313,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z314,z4,z5,z6]),(0,[z315,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z316,z2,z4,z5,z6]),(0,[z8,z317,z0,z2,z4,z5,z6])],[(0,[z8,z23,z2,z21,z4,z5,z6]),(0,[z8,z0,z2,z4,z163,z6,z37]),(0,[z8,z0,z2,z4,z5,z6,z318]),(0,[z8,z121,z0,z4,z5,z6,z193])],[(0,[z8,z189,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z18,z6,z319]),(0,[z8,z0,z2,z4,z320,z5,z6])],[(1,[z191,z0,z3,z4,z5,z6]),(0,[z33,z0,z2,z4,z5,z6,z125]),(0,[z8,z24,z0,z2,z218,z5,z6])]],
   [[(0,[z186,z8,z22,z0,z2,z4,z6]),(0,[z8,z0,z2,z4,z5,z6,z321])],[(0,[z8,z289,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z322,z6]),(0,[z8,z22,z0,z2,z21,z4,z6]),(0,[z8,z22,z323,z0,z2,z4,z6])],[(1,[z52,z1,z2,z4,z5,z6]),(0,[z191,z8,z0,z32,z4,z5,z6]),(0,[z116,z8,z0,z2,z4,z5,z324]),(1,[z8,z0,z2,z4,z325,z6]),(0,[z8,z0,z326,z2,z4,z5,z6])],[(0,[z7,z8,z0,z3,z4,z5,z6]),(1,[z327,z0,z2,z4,z5,z6]),(0,[z8,z328,z0,z2,z4,z5,z6])],[(1,[z8,z0,z160,z4,z5,z6]),(0,[z0,z2,z4,z5,z18,z6,z125]),(0,[z8,z0,z2,z4,z5,z329,z6])],[(0,[z8,z0,z2,z330,z4,z5,z6]),(0,[z8,z331,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z332,z5,z6]),(0,[z333,z8,z0,z2,z4,z5,z6])],[(0,[z8,z1,z2,z239,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z334,z6])],[(0,[z8,z0,z2,z4,z5,z6,z6]),(1,[z8,z335,z0,z2,z4,z6])],[(0,[z336,z8,z0,z2,z4,z5,z6]),(0,[z8,z263,z0,z32,z4,z5,z6]),(1,[z8,z0,z245,z4,z5,z6]),(0,[z8,z0,z2,z337,z4,z5,z6])],[(0,[z8,z131,z0,z32,z4,z5,z6]),(1,[z176,z0,z2,z4,z53,z6]),(0,[z8,z338,z0,z2,z4,z6,z37])],[(0,[z8,z1,z2,z4,z5,z6,z99]),(0,[z8,z0,z2,z105,z4,z5,z6])],[(0,[z67,z8,z1,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z125]),(0,[z7,z339,z0,z2,z4,z5,z6])],[(0,[z8,z23,z2,z4,z5,z340,z6]),(0,[z205,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z341,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z342,z6])],[(0,[z8,z0,z32,z146,z4,z5,z6]),(0,[z70,z8,z22,z0,z2,z4,z6]),(0,[z8,z0,z2,z343,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z344])],[(0,[z345,z8,z0,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z178,z6]),(0,[z8,z22,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z96,z4,z5,z125]),(0,[z8,z182,z0,z2,z4,z6,z37])]],
   [[(0,[z8,z1,z2,z4,z39,z5,z6]),(0,[z8,z0,z3,z21,z4,z5,z6]),(0,[z346,z8,z0,z2,z4,z5,z6]),(0,[z8,z20,z0,z2,z4,z5,z6])],[(0,[z109,z8,z22,z0,z2,z4,z6]),(0,[z8,z2,z4,z5,z11,z6,z193])],[(1,[z8,z0,z2,z4,z5,z259]),(0,[z70,z8,z110,z0,z2,z4,z6]),(0,[z8,z347,z0,z2,z4,z6,z37])],[(0,[z70,z8,z348,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z349]),(0,[z8,z22,z0,z2,z4,z11,z6])],[(1,[z191,z23,z2,z4,z5,z6]),(0,[z8,z45,z23,z2,z4,z5,z6]),(0,[z8,z0,z32,z89,z4,z5,z6]),(0,[z176,z8,z110,z0,z2,z4,z6])],[(0,[z8,z49,z0,z3,z4,z5,z6]),(0,[z7,z8,z0,z32,z4,z5,z6]),(0,[z8,z110,z0,z2,z4,z6,z61]),(0,[z8,z0,z350,z2,z4,z5,z6])],[],[(0,[z46,z8,z0,z32,z4,z5,z6]),(0,[z8,z351,z0,z2,z4,z5,z6])],[(1,[z237,z0,z3,z4,z5,z6])],[(0,[z8,z182,z0,z102,z4,z5,z6])],[(0,[z8,z0,z2,z352,z4,z5,z6]),(0,[z8,z0,z2,z4,z19,z6,z37]),(0,[z8,z0,z2,z353,z4,z5,z6]),(0,[z8,z354,z0,z2,z4,z5,z6])],[(0,[z191,z0,z2,z4,z5,z6,z125]),(0,[z8,z0,z2,z4,z355,z5,z6]),(0,[z8,z2,z4,z178,z5,z6,z193]),(0,[z356,z8,z22,z0,z2,z4,z6]),(0,[z8,z0,z2,z357,z4,z5,z6])],[(1,[z8,z211,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z358,z5,z6])],[(0,[z8,z0,z2,z4,z5,z359,z6])],[(0,[z360,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z361,z4,z5,z6]),(0,[z84,z8,z20,z2,z4,z5,z6]),(0,[z8,z0,z2,z96,z4,z5,z6])],[(0,[z8,z110,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z362,z5,z6])]],
   [[(1,[z8,z0,z32,z4,z6,z37]),(0,[z363,z8,z0,z2,z4,z5,z6]),(0,[z84,z8,z0,z2,z4,z251,z6]),(0,[z8,z131,z0,z2,z4,z5,z6]),(1,[z8,z148,z0,z2,z4,z6])],[(0,[z8,z0,z2,z4,z364,z5,z6]),(1,[z8,z0,z4,z365,z5,z6]),(0,[z8,z0,z2,z183,z4,z6,z37])],[(0,[z366,z8,z0,z2,z4,z5,z6])],[(0,[z8,z0,z367,z2,z4,z5,z6]),(0,[z368,z8,z0,z2,z4,z6,z37])],[(0,[z33,z8,z1,z2,z4,z5,z6]),(0,[z8,z23,z2,z369,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z370])],[(0,[z8,z0,z3,z4,z371,z5,z6]),(0,[z8,z0,z2,z4,z5,z372,z6]),(0,[z8,z0,z2,z129,z4,z5,z6])],[(0,[z8,z0,z32,z3,z4,z5,z6]),(0,[z8,z0,z32,z51,z4,z5,z6]),(0,[z8,z0,z2,z373,z4,z5,z6]),(0,[z0,z2,z4,z53,z5,z43,z6]),(1,[z8,z374,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z375,z37])],[(0,[z8,z0,z32,z4,z53,z5,z6]),(0,[z124,z8,z22,z0,z2,z4,z6]),(0,[z8,z182,z45,z0,z4,z5,z6]),(1,[z376,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z377,z6]),(0,[z8,z0,z2,z4,z5,z378,z6]),(0,[z8,z0,z2,z4,z379,z5,z6])],[(0,[z7,z8,z0,z2,z4,z380,z6]),(1,[z8,z22,z0,z2,z96,z4])],[(0,[z8,z49,z23,z2,z4,z5,z6]),(0,[z8,z381,z0,z2,z4,z5,z6]),(0,[z8,z382,z0,z2,z4,z5,z6]),(0,[z8,z148,z0,z2,z4,z144,z6])],[(0,[z8,z0,z3,z4,z179,z5,z6]),(0,[z8,z383,z0,z3,z4,z5,z6]),(0,[z33,z8,z206,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z384,z6])],[(0,[z226,z8,z1,z2,z4,z5,z6]),(0,[z8,z0,z3,z4,z5,z6,z193]),(0,[z7,z8,z0,z2,z4,z5,z6])],[(0,[z8,z385,z0,z2,z4,z5,z6]),(0,[z84,z8,z0,z2,z4,z5,z11]),(0,[z98,z8,z22,z0,z2,z4,z6]),(0,[z8,z22,z0,z2,z96,z4,z5])],[(0,[z8,z0,z2,z4,z5,z6,z386]),(0,[z8,z0,z2,z4,z5,z152,z6]),(0,[z33,z8,z0,z2,z4,z387,z6])],[(0,[z8,z388,z0,z2,z4,z5,z6]),(0,[z389,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z97,z6,z37]),(0,[z98,z8,z390,z2,z4,z5,z6])]],
   [[(0,[z8,z0,z2,z4,z273,z5,z6]),(0,[z8,z0,z2,z4,z391,z5,z6]),(0,[z8,z22,z0,z2,z4,z60,z6]),(0,[z8,z22,z0,z2,z4,z6,z61])],[(2,[z1,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z5,z6]),(0,[z8,z0,z2,z392,z4,z5,z6])],[(0,[z124,z8,z0,z393,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z125,z37])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z8,z0,z2,z137,z4,z5,z6]),(0,[z8,z0,z3,z4,z97,z5,z6]),(0,[z394,z8,z0,z2,z4,z5,z6]),(1,[z8,z0,z2,z248,z5,z6]),(0,[z8,z0,z395,z2,z4,z6,z37])],[(0,[z8,z0,z2,z4,z396,z5,z6])],[(0,[z8,z23,z2,z4,z5,z6,z397]),(0,[z8,z0,z2,z4,z5,z398,z6]),(0,[z109,z8,z0,z2,z4,z143,z6]),(0,[z399,z8,z0,z2,z4,z5,z6])],[(1,[z8,z0,z190,z4,z5,z6]),(0,[z400,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z401,z6])],[(0,[z8,z20,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z43,z6])],[(0,[z116,z8,z22,z0,z2,z4,z6]),(0,[z8,z0,z2,z402,z4,z5,z6]),(0,[z8,z0,z2,z403,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z404]),(1,[z8,z0,z2,z405,z5,z6])],[(0,[z95,z8,z0,z2,z178,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z406]),(0,[z8,z0,z2,z4,z5,z6,z407]),(0,[z98,z8,z0,z2,z4,z77,z6])],[(0,[z8,z22,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z408]),(0,[z409,z8,z0,z2,z4,z5,z6])],[(0,[z186,z8,z410,z2,z4,z5,z6]),(1,[z8,z9,z2,z4,z5,z6])],[(0,[z8,z0,z3,z218,z4,z5,z6]),(0,[z8,z0,z160,z2,z4,z5,z6]),(0,[z73,z8,z0,z2,z4,z5,z6])],[(1,[z0,z3,z4,z5,z6,z125]),(0,[z84,z295,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z6,z91]),(0,[z8,z0,z2,z4,z411,z5,z6])],[(0,[z8,z412,z1,z2,z4,z5,z6]),(0,[z8,z23,z2,z4,z5,z6,z37])]],
   [[(0,[z191,z8,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z413]),(0,[z8,z0,z2,z4,z5,z6,z319]),(0,[z8,z131,z0,z2,z414,z5,z6]),(0,[z8,z184,z0,z2,z4,z5,z6])],[(0,[z415,z8,z0,z2,z4,z5,z6]),(0,[z84,z8,z0,z2,z4,z6,z37]),(0,[z7,z8,z0,z197,z4,z5,z6])],[(0,[z8,z45,z0,z3,z4,z5,z6]),(0,[z8,z131,z0,z2,z4,z60,z6])],[(0,[z109,z8,z0,z2,z4,z163,z6])],[(0,[z8,z1,z2,z416,z4,z5,z6]),(0,[z8,z0,z34,z2,z4,z5,z6]),(0,[z8,z0,z2,z417,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z418]),(0,[z419,z8,z22,z0,z2,z4,z6])],[(0,[z420,z8,z0,z2,z4,z5,z6]),(0,[z70,z8,z421,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z422,z6])],[],[(0,[z8,z131,z1,z2,z4,z5,z6]),(0,[z8,z423,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z424,z4,z6,z37])],[(0,[z8,z0,z3,z4,z5,z425,z6]),(0,[z8,z0,z3,z4,z5,z19,z6]),(0,[z8,z426,z0,z2,z4,z5,z6]),(0,[z70,z8,z0,z2,z4,z53,z6]),(0,[z95,z8,z0,z2,z4,z6,z37]),(0,[z8,z22,z0,z427,z2,z4,z6])],[(0,[z8,z428,z22,z0,z2,z4,z6])],[(0,[z8,z0,z412,z2,z4,z5,z6]),(0,[z176,z8,z0,z2,z4,z53,z6]),(0,[z8,z0,z2,z4,z5,z6,z429]),(0,[z8,z0,z2,z430,z4,z5,z6]),(0,[z8,z0,z2,z4,z431,z5,z6])],[(0,[z8,z1,z2,z21,z4,z5,z6]),(0,[z8,z0,z2,z89,z4,z6,z37])],[(1,[z8,z348,z2,z4,z5,z6])],[(0,[z8,z432,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z433,z6])],[(0,[z191,z186,z0,z2,z4,z5,z6])],[(0,[z434,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z32,z2,z4,z5,z6]),(0,[z435,z8,z0,z2,z4,z5,z6]),(0,[z84,z8,z0,z2,z4,z325,z6])]],
   [[(0,[z8,z0,z2,z4,z5,z436,z6]),(0,[z8,z0,z2,z4,z5,z6,z437])],[(1,[z8,z0,z393,z4,z5,z6]),(0,[z8,z252,z0,z2,z4,z5,z6])],[(0,[z8,z0,z3,z4,z5,z6,z37]),(0,[z176,z8,z22,z0,z2,z4,z6]),(1,[z8,z0,z438,z4,z5,z6]),(0,[z8,z0,z2,z183,z16,z5,z6]),(1,[z8,z0,z2,z4,z77,z6])],[(0,[z8,z281,z1,z2,z4,z5,z6]),(0,[z7,z8,z1,z2,z4,z5,z6]),(0,[z116,z124,z0,z2,z4,z5,z6]),(1,[z8,z0,z2,z4,z5,z324]),(0,[z8,z227,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z60,z6]),(0,[z8,z0,z2,z4,z5,z6,z61]),(0,[z8,z439,z0,z2,z4,z5,z6])],[(1,[z8,z189,z1,z2,z4,z6]),(0,[z8,z383,z0,z2,z4,z5,z6]),(0,[z8,z117,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z125,z37]),(0,[z167,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z16,z5,z19,z6])],[(0,[z46,z8,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z37,z61]),(0,[z8,z440,z0,z2,z4,z5,z6])],[(0,[z70,z176,z0,z2,z4,z5,z6]),(0,[z8,z441,z0,z2,z4,z5,z6])],[(0,[z8,z22,z0,z2,z4,z43,z6])],[(0,[z8,z0,z32,z4,z5,z163,z6]),(0,[z8,z22,z182,z0,z2,z4,z6])],[(0,[z8,z0,z2,z4,z5,z6,z442]),(1,[z8,z0,z443,z4,z5,z6])],[(0,[z8,z0,z2,z4,z444,z5,z6]),(0,[z445,z8,z0,z2,z4,z5,z6]),(0,[z8,z446,z0,z2,z4,z5,z6]),(1,[z8,z100,z0,z39,z5,z6])],[(0,[z8,z23,z2,z4,z179,z5,z6]),(0,[z8,z0,z32,z4,z5,z6,z173]),(0,[z8,z447,z0,z2,z4,z5,z6]),(1,[z8,z0,z2,z4,z18,z37]),(0,[z8,z0,z2,z4,z448,z5,z6]),(0,[z8,z449,z0,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z144,z6]),(0,[z8,z0,z2,z4,z58,z5,z6])],[(1,[z8,z0,z450,z4,z5,z6]),(0,[z8,z23,z2,z4,z5,z6,z193]),(1,[z8,z0,z94,z4,z5,z6])],[(0,[z8,z110,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z3,z4,z6,z37]),(0,[z7,z8,z210,z2,z4,z5,z6])],[(1,[z8,z1,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z53,z6,z37]),(0,[z8,z0,z2,z4,z5,z6,z451]),(0,[z8,z0,z2,z4,z11,z6,z139])],[(0,[z237,z8,z22,z0,z2,z4,z6]),(0,[z8,z20,z2,z4,z178,z5,z6])]],
   [[(0,[z158,z8,z0,z1,z2,z4,z6]),(0,[z8,z0,z2,z4,z452,z5,z6]),(0,[z8,z449,z0,z2,z4,z11,z6]),(0,[z8,z0,z103,z4,z39,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z40])],[(0,[z8,z432,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z387,z6]),(0,[z67,z8,z0,z104,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z37,z40])],[(0,[z8,z23,z2,z4,z97,z5,z6]),(0,[z8,z164,z0,z2,z4,z5,z6]),(0,[z95,z8,z0,z2,z218,z5,z6]),(0,[z8,z453,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z454])],[(0,[z8,z0,z455,z2,z4,z5,z6]),(0,[z456,z8,z0,z2,z4,z5,z6])],[(0,[z8,z101,z0,z3,z4,z5,z6]),(0,[z8,z100,z0,z2,z39,z5,z6]),(0,[z8,z457,z0,z2,z4,z5,z6])],[(1,[z23,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z179,z5,z6]),(0,[z109,z8,z0,z3,z4,z5,z6]),(0,[z8,z0,z2,z187,z4,z5,z6]),(0,[z8,z0,z2,z4,z458,z5,z6])],[(0,[z191,z52,z0,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z193]),(0,[z8,z0,z32,z4,z201,z5,z6]),(0,[z8,z0,z2,z4,z459,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z460]),(1,[z8,z20,z2,z4,z5,z11])],[(0,[z8,z0,z3,z183,z4,z5,z6]),(0,[z116,z8,z0,z2,z4,z396,z6]),(0,[z8,z24,z2,z4,z5,z6,z193]),(0,[z8,z0,z2,z4,z461,z5,z6]),(0,[z8,z0,z2,z4,z5,z462,z6])],[(0,[z8,z0,z202,z2,z4,z5,z6]),(0,[z8,z0,z2,z218,z16,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z463])],[(0,[z8,z0,z2,z4,z464,z5,z6]),(0,[z186,z8,z23,z2,z4,z5,z6]),(0,[z8,z49,z0,z32,z4,z5,z6]),(0,[z465,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z143,z5,z6])],[(0,[z8,z0,z2,z466,z4,z5,z6]),(0,[z8,z0,z32,z4,z5,z6,z125]),(0,[z8,z467,z0,z2,z4,z5,z6]),(0,[z8,z45,z0,z2,z4,z5,z6])],[(0,[z8,z23,z2,z218,z4,z5,z6]),(0,[z468,z8,z0,z2,z4,z5,z6]),(0,[z8,z101,z0,z183,z4,z5,z6]),(0,[z8,z31,z0,z2,z4,z6,z37])],[],[(0,[z8,z1,z2,z4,z97,z5,z6]),(0,[z8,z0,z2,z4,z5,z18,z6]),(0,[z67,z8,z255,z2,z4,z5,z6]),(0,[z469,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z470,z5,z6]),(1,[z8,z0,z2,z4,z6,z139]),(0,[z8,z0,z2,z471,z4,z5,z6]),(0,[z98,z472,z0,z2,z4,z5,z6]),(0,[z8,z323,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z147,z4,z5,z6])]],
   [[(0,[z8,z0,z2,z473,z4,z5,z6]),(0,[z67,z8,z0,z129,z4,z5,z6]),(0,[z8,z474,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z475,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z476])],[(0,[z124,z8,z0,z2,z47,z5,z6])],[(1,[z8,z0,z34,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z477,z6])],[(0,[z8,z426,z0,z32,z4,z5,z6])],[(0,[z8,z0,z2,z4,z478,z5,z6]),(0,[z8,z0,z2,z4,z5,z479,z6]),(0,[z8,z0,z2,z4,z5,z6,z480]),(0,[z8,z0,z2,z143,z5,z6,z61])],[(1,[z8,z0,z2,z4,z396,z6])],[(0,[z8,z1,z2,z218,z4,z5,z6]),(0,[z70,z8,z23,z2,z4,z5,z6]),(0,[z8,z0,z242,z2,z4,z5,z6]),(0,[z481,z8,z0,z2,z4,z5,z6]),(0,[z8,z182,z2,z21,z4,z5,z6])],[(1,[z1,z2,z4,z5,z6,z125]),(0,[z8,z22,z1,z2,z4,z5,z6]),(0,[z8,z23,z2,z4,z5,z19,z6]),(0,[z482,z8,z0,z2,z4,z5,z6]),(0,[z8,z24,z2,z218,z4,z5,z6])],[(0,[z8,z483,z0,z2,z4,z5,z6]),(1,[z484,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z485,z6]),(0,[z8,z486,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z487,z6]),(0,[z8,z488,z0,z2,z4,z5,z6])],[(0,[z8,z101,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z489,z5,z6]),(0,[z8,z101,z0,z2,z39,z5,z6])],[(0,[z109,z8,z23,z2,z4,z5,z6]),(0,[z8,z0,z32,z32,z4,z5,z6]),(0,[z8,z0,z2,z490,z4,z5,z6])],[(0,[z124,z8,z0,z3,z4,z5,z6]),(0,[z8,z20,z2,z4,z5,z11,z6]),(1,[z8,z31,z0,z2,z6,z61])],[(0,[z8,z0,z2,z4,z491,z5,z6])],[(0,[z8,z0,z2,z492,z4,z5,z6]),(1,[z8,z421,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z144,z6])],[(0,[z493,z8,z0,z2,z4,z5,z6]),(0,[z8,z23,z2,z89,z4,z5,z6]),(0,[z8,z23,z0,z3,z4,z5,z6])]],
   [[(0,[z84,z8,z0,z2,z248,z5,z6]),(0,[z8,z0,z2,z4,z494,z5,z6]),(0,[z8,z22,z0,z2,z4,z6,z40])],[(1,[z8,z410,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z47,z5,z6]),(0,[z495,z8,z0,z2,z4,z5,z6]),(0,[z8,z49,z0,z2,z4,z5,z6]),(1,[z8,z227,z0,z4,z5,z6])],[(0,[z8,z0,z2,z496,z4,z5,z6]),(0,[z98,z8,z0,z3,z4,z5,z6]),(0,[z116,z8,z0,z2,z47,z5,z6]),(1,[z8,z0,z2,z4,z320,z6])],[(0,[z497,z8,z0,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z19,z6]),(0,[z237,z8,z78,z2,z4,z5,z6]),(0,[z8,z0,z2,z218,z4,z320,z6]),(0,[z8,z0,z2,z4,z5,z6,z498]),(0,[z499,z8,z22,z0,z2,z4,z6])],[(0,[z8,z0,z102,z2,z4,z5,z99])],[(0,[z8,z0,z2,z500,z4,z5,z6]),(0,[z8,z0,z2,z501,z4,z5,z6]),(0,[z7,z8,z0,z2,z4,z5,z40])],[(0,[z502,z8,z0,z3,z4,z5,z6]),(0,[z8,z2,z21,z4,z5,z6,z193]),(0,[z98,z8,z503,z2,z4,z5,z6]),(1,[z8,z0,z2,z4,z6,z200])],[(1,[z8,z23,z3,z4,z5,z6]),(0,[z8,z22,z23,z0,z2,z4,z6]),(0,[z8,z0,z2,z146,z4,z6,z37]),(1,[z472,z0,z2,z4,z5,z6])],[(0,[z504,z8,z0,z2,z4,z5,z6]),(0,[z84,z8,z0,z2,z4,z5,z193]),(0,[z8,z0,z103,z2,z4,z6,z37])],[(0,[z186,z67,z0,z2,z4,z5,z6]),(1,[z8,z22,z0,z2,z4,z6])],[(0,[z505,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z506,z2,z4,z5,z6])],[(0,[z8,z0,z3,z146,z4,z5,z6]),(0,[z8,z0,z2,z507,z4,z5,z6]),(0,[z8,z0,z2,z4,z508,z5,z6]),(1,[z8,z390,z2,z4,z5,z6])],[(0,[z8,z0,z32,z4,z178,z5,z6]),(0,[z124,z0,z2,z146,z4,z5,z6]),(0,[z8,z0,z2,z4,z143,z60,z6]),(0,[z8,z123,z0,z2,z4,z19,z6])],[(0,[z8,z1,z2,z4,z5,z6,z37]),(0,[z116,z8,z0,z3,z4,z5,z6]),(0,[z8,z432,z0,z32,z4,z5,z6])],[(0,[z509,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z355,z5,z6]),(0,[z8,z0,z510,z32,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z18,z6])],[(0,[z511,z8,z0,z2,z4,z5,z6]),(0,[z109,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z183,z5,z6,z61])]],
   [[(1,[z8,z0,z512,z4,z5,z6])],[(0,[z8,z23,z2,z3,z4,z5,z6]),(0,[z124,z8,z23,z2,z4,z5,z6]),(0,[z513,z8,z0,z2,z4,z5,z6]),(0,[z8,z101,z0,z103,z4,z5,z6]),(0,[z8,z0,z2,z16,z4,z5,z40])],[(0,[z8,z23,z2,z4,z53,z5,z6]),(0,[z8,z0,z3,z89,z4,z5,z6]),(0,[z8,z0,z102,z4,z5,z144,z6]),(0,[z83,z8,z0,z2,z4,z5,z6])],[(0,[z8,z100,z0,z3,z4,z5,z6]),(1,[z8,z0,z103,z4,z97,z6])],[(0,[z8,z23,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z221]),(0,[z8,z0,z2,z4,z5,z6,z514])],[(0,[z23,z0,z1,z2,z4,z5,z6]),(0,[z515,z8,z0,z2,z4,z5,z6]),(0,[z33,z8,z0,z2,z4,z273,z6]),(0,[z8,z0,z2,z516,z4,z5,z6])],[(0,[z8,z22,z100,z0,z2,z4,z6])],[(0,[z8,z0,z2,z239,z4,z5,z6]),(0,[z98,z8,z23,z2,z4,z5,z6]),(0,[z8,z467,z0,z32,z4,z5,z6]),(0,[z8,z45,z0,z32,z4,z5,z6]),(0,[z8,z131,z0,z4,z5,z60,z6]),(0,[z517,z8,z0,z2,z4,z5,z6])],[(0,[z8,z23,z2,z183,z4,z5,z6]),(0,[z186,z8,z0,z3,z4,z5,z6]),(0,[z8,z100,z0,z2,z4,z13,z6])],[(0,[z8,z388,z1,z2,z4,z5,z6]),(0,[z518,z8,z0,z2,z4,z5,z6])],[(0,[z8,z421,z0,z2,z4,z5,z6]),(0,[z95,z8,z22,z0,z2,z4,z6])],[(0,[z8,z0,z1,z2,z4,z6,z37]),(0,[z519,z8,z0,z2,z4,z5,z6]),(0,[z502,z8,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z99]),(0,[z8,z0,z102,z2,z4,z5,z144])],[(0,[z8,z0,z2,z4,z5,z246,z6]),(0,[z8,z22,z0,z2,z218,z4,z6]),(0,[z520,z8,z0,z2,z4,z5,z6]),(0,[z8,z295,z0,z2,z4,z5,z6])],[(0,[z176,z8,z0,z521,z4,z5,z6]),(0,[z8,z0,z2,z4,z522,z5,z6]),(0,[z8,z0,z2,z4,z6,z37,z99])],[(0,[z523,z8,z0,z2,z4,z5,z6]),(0,[z8,z121,z0,z2,z4,z5,z6]),(1,[z8,z449,z0,z2,z4,z6])],[(1,[z33,z0,z2,z4,z5,z125]),(0,[z67,z0,z2,z4,z5,z18,z6]),(1,[z8,z503,z2,z4,z5,z6])]],
   [[(0,[z524,z8,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z47,z5,z6,z61]),(1,[z84,z8,z2,z4,z5,z193]),(1,[z8,z0,z2,z4,z13,z6])],[(0,[z33,z8,z0,z2,z187,z5,z6]),(0,[z8,z0,z2,z4,z525,z5,z6]),(0,[z8,z0,z2,z4,z39,z5,z6])],[(0,[z116,z8,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z526,z6]),(0,[z8,z0,z2,z4,z5,z6,z527]),(0,[z8,z0,z2,z4,z5,z6,z528])],[(0,[z8,z1,z2,z183,z4,z5,z6]),(0,[z8,z0,z521,z2,z4,z5,z6]),(0,[z8,z0,z2,z529,z4,z5,z6])],[(0,[z8,z0,z3,z3,z4,z5,z6]),(0,[z8,z530,z0,z2,z4,z5,z6])],[(0,[z70,z8,z0,z3,z4,z5,z6]),(0,[z8,z0,z3,z4,z53,z5,z6]),(0,[z8,z0,z510,z2,z4,z5,z6]),(0,[z124,z8,z0,z2,z4,z5,z6]),(0,[z8,z531,z0,z2,z4,z5,z6]),(0,[z8,z2,z4,z179,z5,z163,z6]),(0,[z8,z0,z2,z532,z4,z5,z6]),(0,[z8,z0,z2,z4,z97,z143,z6])],[(1,[z67,z0,z3,z4,z5,z6]),(0,[z8,z20,z0,z2,z4,z5,z11])],[(0,[z176,z8,z0,z3,z4,z5,z6]),(0,[z8,z533,z0,z3,z4,z5,z6])],[(0,[z8,z23,z0,z2,z4,z5,z6]),(0,[z8,z49,z1,z2,z4,z5,z6]),(0,[z8,z100,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z534,z6])],[(0,[z8,z0,z149,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z5,z11,z6]),(1,[z8,z0,z102,z4,z5,z144])],[(0,[z186,z8,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z535])],[(0,[z8,z0,z32,z16,z4,z5,z6]),(0,[z8,z0,z2,z4,z536,z5,z6]),(0,[z140,z8,z0,z2,z4,z5,z6]),(0,[z537,z8,z22,z0,z2,z4,z6])],[(0,[z158,z8,z0,z2,z4,z5,z6]),(0,[z538,z8,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z539,z5,z6]),(0,[z8,z0,z2,z4,z19,z6,z200])],[(0,[z191,z8,z0,z149,z4,z5,z6]),(1,[z8,z78,z2,z4,z5,z6]),(0,[z8,z0,z2,z47,z5,z6,z40])],[(0,[z540,z8,z0,z2,z4,z5,z6]),(1,[z124,z0,z2,z146,z5,z6])],[(0,[z502,z8,z0,z2,z4,z5,z6]),(0,[z8,z327,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z541,z5,z6])]],
   [[(1,[z8,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z542,z5,z6]),(0,[z8,z0,z2,z405,z4,z5,z6]),(0,[z98,z8,z0,z2,z4,z543,z6])],[(0,[z544,z8,z0,z2,z4,z5,z6]),(0,[z109,z8,z0,z2,z4,z6,z61])],[(0,[z8,z545,z0,z2,z4,z5,z6]),(0,[z67,z0,z2,z4,z47,z5,z6]),(0,[z8,z22,z0,z2,z16,z4,z6])],[(0,[z8,z0,z2,z4,z254,z5,z6]),(0,[z8,z0,z2,z4,z143,z43,z6]),(0,[z8,z0,z2,z218,z5,z6,z40]),(0,[z8,z0,z2,z4,z5,z6,z240])],[(0,[z237,z8,z0,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z60,z6,z61])],[(0,[z52,z8,z0,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z4,z5,z6]),(0,[z8,z0,z102,z4,z39,z5,z6])],[],[(0,[z70,z8,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z546]),(0,[z8,z22,z0,z2,z231,z4,z6])],[(0,[z8,z0,z2,z146,z16,z5,z6]),(0,[z8,z0,z2,z547,z4,z5,z6])],[(0,[z8,z548,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z549,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z6,z550]),(0,[z8,z101,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z551,z5,z6])],[(0,[z8,z23,z2,z146,z4,z5,z6]),(0,[z109,z8,z0,z32,z4,z5,z6]),(0,[z8,z0,z32,z330,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z6,z99]),(0,[z8,z0,z2,z4,z5,z6,z552])],[(0,[z176,z8,z23,z2,z4,z5,z6]),(0,[z8,z23,z103,z2,z4,z5,z6]),(0,[z8,z0,z553,z2,z4,z5,z6]),(0,[z8,z100,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z554])],[(0,[z8,z0,z2,z4,z5,z555,z6])],[(0,[z8,z0,z410,z2,z4,z5,z6]),(0,[z8,z31,z22,z0,z2,z4,z6]),(0,[z8,z0,z2,z4,z556,z5,z6])],[(0,[z8,z0,z2,z4,z5,z6,z557]),(1,[z8,z0,z558,z4,z5,z6])]],
   [[(0,[z8,z0,z2,z369,z4,z5,z6]),(0,[z538,z8,z0,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z559,z6]),(0,[z186,z8,z0,z2,z4,z5,z6]),(0,[z33,z8,z0,z2,z214,z5,z6]),(0,[z560,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z89,z4,z143,z6])],[(0,[z8,z0,z2,z4,z5,z6,z290]),(1,[z8,z0,z253,z4,z5,z6]),(0,[z419,z8,z0,z2,z4,z5,z6])],[(0,[z186,z0,z2,z4,z5,z6,z125]),(0,[z8,z0,z2,z4,z178,z6,z37])],[],[],[(0,[z8,z1,z2,z146,z4,z5,z6]),(0,[z561,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z5,z6,z61]),(0,[z84,z484,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z18,z40]),(0,[z8,z0,z2,z4,z5,z6,z562])],[(1,[z158,z8,z1,z2,z4,z6]),(0,[z8,z0,z2,z4,z563,z5,z6]),(0,[z564,z8,z0,z2,z4,z5,z6])],[(0,[z237,z8,z23,z2,z4,z5,z6]),(0,[z8,z207,z0,z2,z4,z5,z6]),(1,[z8,z0,z2,z4,z543,z6])],[(0,[z8,z0,z3,z4,z5,z6,z135])],[(0,[z8,z182,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z90,z6]),(0,[z8,z565,z0,z2,z4,z5,z6]),(0,[z566,z8,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z567,z5,z6]),(0,[z8,z0,z348,z2,z4,z5,z6])],[(0,[z8,z1,z2,z89,z4,z5,z6]),(0,[z67,z8,z0,z2,z4,z5,z18]),(1,[z8,z24,z2,z218,z5,z6])],[(0,[z8,z24,z0,z3,z4,z5,z6]),(0,[z70,z8,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z43,z6,z61]),(1,[z8,z0,z2,z4,z6,z309]),(0,[z8,z0,z2,z4,z144,z6,z240])]],
   [[(0,[z8,z533,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z568,z5,z6]),(0,[z176,z8,z0,z2,z4,z5,z6]),(0,[z569,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z218,z4,z6,z309]),(0,[z8,z0,z2,z570,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z6,z397]),(0,[z124,z8,z0,z32,z4,z5,z6]),(0,[z70,z8,z0,z2,z361,z5,z6]),(0,[z176,z0,z2,z4,z53,z5,z6]),(0,[z67,z8,z0,z2,z4,z6,z37]),(0,[z8,z101,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z571]),(0,[z8,z31,z0,z443,z4,z5,z6])],[(0,[z8,z100,z0,z2,z183,z5,z6])],[(0,[z8,z376,z0,z2,z4,z5,z6])],[(0,[z8,z0,z189,z1,z2,z4,z6]),(0,[z8,z23,z0,z32,z4,z5,z6]),(0,[z8,z0,z32,z96,z4,z5,z6]),(1,[z8,z0,z521,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z572,z6])],[(0,[z8,z45,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z416,z4,z5,z6]),(0,[z8,z573,z23,z2,z4,z5,z6])],[(0,[z8,z23,z2,z4,z5,z6,z125]),(0,[z8,z0,z3,z4,z5,z163,z6]),(0,[z8,z574,z0,z3,z4,z5,z6]),(0,[z84,z8,z22,z0,z2,z4,z6]),(0,[z8,z0,z2,z4,z5,z575,z6]),(0,[z8,z576,z0,z2,z4,z5,z6])],[(0,[z98,z8,z0,z32,z4,z5,z6]),(0,[z0,z2,z4,z47,z5,z6,z125]),(0,[z8,z0,z2,z4,z5,z577,z6])],[(0,[z8,z0,z3,z4,z171,z5,z6]),(0,[z8,z0,z2,z4,z5,z578,z6]),(0,[z70,z8,z0,z2,z4,z5,z579]),(0,[z580,z8,z0,z2,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z33,z8,z374,z2,z4,z5,z6]),(1,[z7,z8,z0,z2,z5,z40])],[(0,[z8,z0,z2,z581,z4,z5,z6]),(0,[z8,z31,z0,z2,z5,z6,z61]),(0,[z8,z0,z2,z582,z4,z5,z6]),(0,[z8,z22,z0,z506,z2,z4,z6])],[(0,[z8,z0,z2,z4,z583,z5,z6]),(0,[z8,z335,z0,z2,z4,z5,z6]),(1,[z8,z110,z2,z4,z179,z6]),(0,[z8,z0,z2,z584,z4,z5,z6])],[(1,[z8,z23,z32,z4,z5,z6]),(0,[z356,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z18,z6,z37]),(0,[z8,z0,z2,z21,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z585])],[(0,[z237,z8,z0,z2,z4,z5,z6]),(0,[z237,z0,z2,z3,z4,z5,z6]),(0,[z8,z0,z2,z245,z4,z5,z6]),(0,[z84,z8,z0,z512,z4,z5,z6]),(0,[z8,z0,z102,z2,z4,z6,z37])],[(1,[z8,z0,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z306,z6]),(0,[z8,z0,z2,z4,z6,z37,z585])],[(0,[z8,z1,z2,z3,z4,z5,z6]),(0,[z8,z586,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z183,z5,z6,z40])]],
   [[(1,[z8,z0,z157,z4,z5,z6]),(0,[z8,z1,z2,z4,z53,z5,z6]),(0,[z8,z24,z0,z32,z4,z5,z6]),(0,[z8,z587,z0,z2,z4,z5,z6])],[],[(0,[z116,z8,z0,z32,z4,z5,z6]),(0,[z124,z8,z93,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z579,z6]),(0,[z8,z31,z0,z2,z4,z143,z6])],[(0,[z8,z0,z2,z393,z4,z5,z6]),(0,[z8,z0,z2,z588,z4,z5,z6])],[(0,[z8,z0,z2,z438,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z39,z6]),(0,[z8,z0,z589,z2,z4,z5,z6])],[],[(0,[z33,z8,z0,z2,z4,z5,z18]),(0,[z8,z0,z590,z2,z4,z5,z6]),(1,[z8,z0,z2,z89,z143,z6])],[(0,[z8,z0,z2,z89,z47,z5,z6]),(0,[z8,z101,z0,z2,z183,z5,z6])],[(0,[z186,z8,z1,z2,z4,z5,z6]),(0,[z8,z591,z0,z3,z4,z5,z6]),(0,[z8,z100,z0,z32,z4,z5,z6]),(0,[z8,z2,z218,z4,z178,z5,z6]),(0,[z8,z592,z0,z2,z4,z5,z6])],[(0,[z8,z573,z0,z2,z4,z5,z6]),(0,[z8,z0,z3,z4,z5,z6,z125]),(0,[z8,z593,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z262,z4,z5,z6]),(0,[z124,z0,z2,z4,z5,z6,z125]),(0,[z33,z8,z0,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z5,z594,z6]),(0,[z8,z0,z2,z4,z595,z5,z6])],[(0,[z8,z0,z2,z4,z5,z340,z6]),(0,[z8,z0,z32,z4,z5,z398,z6]),(0,[z8,z0,z2,z4,z596,z5,z6])],[(0,[z8,z0,z2,z597,z4,z5,z6]),(0,[z8,z0,z2,z178,z5,z6,z40])],[(0,[z8,z0,z32,z4,z5,z43,z6]),(0,[z598,z8,z0,z2,z4,z5,z6]),(0,[z109,z8,z2,z4,z5,z163,z6])],[(0,[z8,z0,z599,z2,z4,z5,z6]),(0,[z98,z8,z0,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z353,z4,z6])],[(0,[z95,z8,z0,z3,z4,z5,z6]),(0,[z8,z600,z0,z2,z4,z5,z6]),(0,[z8,z22,z0,z103,z2,z4,z6]),(0,[z8,z503,z0,z2,z4,z5,z6])]],
   [[(0,[z8,z0,z102,z21,z4,z5,z6]),(0,[z339,z8,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z371,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z601])],[(0,[z8,z0,z2,z4,z5,z602,z6]),(0,[z124,z8,z0,z2,z146,z5,z6])],[(0,[z8,z603,z0,z2,z4,z5,z6]),(0,[z368,z8,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z6,z57]),(0,[z8,z0,z2,z604,z4,z5,z6])],[(0,[z70,z8,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z146,z5,z6,z61]),(0,[z8,z605,z0,z2,z4,z5,z6])],[(0,[z8,z606,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z365,z5,z6])],[(0,[z524,z8,z0,z2,z4,z5,z6]),(0,[z8,z23,z2,z4,z178,z5,z6]),(0,[z8,z24,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z179,z5,z6]),(0,[z8,z0,z2,z4,z144,z6,z37])],[(0,[z8,z101,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z607,z6]),(0,[z8,z0,z2,z4,z5,z6,z193]),(0,[z8,z0,z2,z608,z4,z5,z6])],[(0,[z511,z8,z1,z2,z4,z5,z6]),(0,[z109,z8,z1,z2,z4,z5,z6]),(0,[z8,z182,z0,z3,z4,z5,z6]),(0,[z116,z8,z0,z2,z4,z5,z6]),(0,[z8,z374,z0,z2,z4,z5,z6]),(0,[z8,z609,z0,z2,z4,z5,z6])],[(1,[z109,z8,z2,z4,z163,z6])],[(0,[z8,z0,z2,z610,z4,z5,z6]),(0,[z8,z0,z2,z4,z611,z5,z6]),(0,[z8,z22,z0,z2,z4,z6,z37])],[(0,[z176,z8,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z6,z37]),(0,[z8,z0,z2,z4,z5,z6,z375])],[(1,[z249,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z251,z6]),(0,[z8,z20,z0,z2,z4,z6,z37])],[(0,[z8,z0,z612,z3,z4,z5,z6]),(0,[z8,z9,z0,z2,z4,z5,z6])],[(0,[z186,z0,z1,z2,z4,z5,z6])]],
   [[(1,[z8,z86,z2,z4,z5,z6]),(0,[z613,z8,z0,z2,z4,z5,z6]),(0,[z614,z8,z0,z2,z4,z5,z6])],[(1,[z8,z93,z2,z4,z5,z6]),(0,[z8,z0,z103,z4,z97,z5,z6]),(0,[z499,z8,z0,z2,z4,z5,z6])],[(0,[z615,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z146,z5,z6,z40]),(0,[z176,z8,z134,z2,z4,z5,z6]),(0,[z8,z0,z616,z2,z4,z5,z6]),(0,[z8,z617,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z618,z6])],[(0,[z619,z8,z0,z2,z4,z5,z6]),(1,[z98,z8,z0,z4,z5,z99])],[(0,[z95,z8,z23,z2,z4,z5,z6])],[(1,[z8,z1,z3,z4,z5,z6]),(0,[z620,z8,z0,z2,z4,z5,z6]),(0,[z33,z8,z0,z438,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z19,z125]),(0,[z8,z49,z101,z0,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z621])],[(0,[z191,z8,z0,z2,z4,z6,z37]),(0,[z8,z23,z2,z4,z5,z163,z6]),(0,[z8,z0,z2,z4,z5,z6,z622])],[(1,[z8,z0,z2,z4,z5,z6]),(0,[z52,z8,z22,z0,z2,z4,z6]),(0,[z186,z8,z545,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z623,z5,z6]),(0,[z8,z0,z2,z89,z39,z5,z6])],[(0,[z8,z49,z20,z2,z4,z5,z6]),(0,[z8,z0,z2,z218,z4,z5,z6]),(0,[z84,z8,z2,z4,z5,z6,z193]),(0,[z8,z0,z2,z4,z5,z624,z6])],[(0,[z237,z8,z0,z32,z4,z5,z6]),(0,[z8,z0,z32,z4,z5,z60,z6]),(0,[z8,z625,z0,z2,z4,z5,z6]),(0,[z626,z8,z0,z2,z4,z5,z6])],[(0,[z8,z1,z103,z2,z4,z5,z6]),(0,[z8,z0,z3,z4,z178,z5,z6]),(0,[z0,z32,z2,z3,z4,z5,z6]),(1,[z8,z0,z2,z361,z5,z6]),(0,[z8,z428,z0,z2,z4,z5,z6])],[(0,[z8,z182,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z627,z4,z5,z6]),(0,[z8,z0,z390,z2,z4,z5,z6])],[(0,[z628,z8,z0,z2,z4,z5,z6])],[(0,[z8,z131,z0,z2,z4,z6,z37]),(0,[z8,z22,z0,z2,z96,z4,z6])],[(0,[z191,z23,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z629,z6]),(0,[z124,z8,z1,z2,z4,z5,z6]),(0,[z630,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z4,z39,z5,z60,z6])]],
   [[(0,[z8,z0,z2,z4,z5,z631,z6]),(0,[z8,z632,z0,z2,z4,z5,z6]),(0,[z633,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z380,z5,z6])],[(0,[z8,z1,z2,z4,z5,z163,z6]),(0,[z8,z23,z102,z2,z4,z5,z6]),(0,[z8,z591,z0,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z58,z5,z6]),(1,[z8,z0,z2,z4,z5,z579]),(0,[z8,z0,z558,z2,z4,z5,z6])],[(0,[z8,z23,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z259]),(0,[z8,z0,z2,z4,z5,z6,z634])],[(0,[z8,z0,z2,z4,z5,z155,z6]),(0,[z8,z0,z2,z89,z143,z5,z6])],[(0,[z635,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z425,z6]),(0,[z8,z0,z32,z4,z39,z5,z6]),(0,[z8,z636,z0,z2,z4,z5,z6]),(0,[z8,z637,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z19,z6])],[(0,[z98,z8,z1,z2,z4,z5,z6])],[(0,[z158,z8,z1,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z5,z6,z40]),(1,[z8,z0,z2,z4,z6,z319]),(0,[z638,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z16,z178,z5,z6])],[(0,[z8,z639,z0,z3,z4,z5,z6]),(0,[z70,z8,z0,z2,z4,z43,z6]),(0,[z8,z0,z183,z4,z39,z5,z6]),(0,[z8,z0,z2,z4,z5,z640,z6])],[(0,[z8,z22,z0,z32,z2,z4,z6]),(0,[z8,z335,z0,z2,z4,z18,z6]),(0,[z8,z22,z0,z2,z4,z6,z193]),(0,[z8,z0,z2,z4,z414,z5,z6])],[(0,[z176,z8,z0,z2,z4,z43,z6]),(0,[z8,z0,z2,z4,z5,z641,z6]),(0,[z7,z8,z0,z2,z4,z6,z37])],[(0,[z8,z603,z1,z2,z4,z5,z6]),(1,[z8,z22,z0,z3,z4,z6]),(0,[z8,z0,z2,z4,z642,z5,z6]),(0,[z8,z0,z2,z96,z4,z58,z5])],[(0,[z249,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z643,z4,z5,z6]),(0,[z46,z8,z0,z2,z4,z6,z37])],[(0,[z8,z1,z102,z2,z4,z5,z6]),(0,[z8,z0,z2,z612,z4,z5,z6]),(1,[z8,z0,z197,z4,z5,z6]),(0,[z7,z8,z0,z2,z4,z306,z6]),(0,[z8,z338,z0,z2,z4,z5,z6])],[(0,[z52,z8,z0,z450,z4,z5,z6]),(0,[z8,z1,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z644,z6])],[(0,[z8,z24,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z37]),(0,[z8,z22,z0,z2,z4,z379,z6])],[(0,[z484,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z645]),(0,[z8,z0,z2,z646,z4,z5,z6])]],
   [[(0,[z116,z8,z1,z2,z4,z5,z6]),(0,[z8,z0,z189,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z143,z5,z6]),(0,[z8,z0,z2,z4,z6,z37,z37])],[(0,[z8,z0,z2,z4,z97,z6,z61])],[(0,[z8,z647,z0,z2,z4,z5,z6]),(0,[z8,z182,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z512,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z648,z6]),(0,[z67,z8,z22,z0,z2,z4,z6]),(0,[z8,z49,z0,z4,z5,z144,z6]),(0,[z8,z110,z0,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z649,z5,z6]),(0,[z8,z0,z650,z2,z4,z5,z6]),(0,[z7,z8,z0,z2,z4,z5,z19])],[(0,[z8,z1,z2,z4,z5,z6,z125]),(0,[z8,z0,z32,z4,z5,z18,z6]),(0,[z8,z0,z651,z2,z4,z5,z6]),(0,[z8,z0,z218,z4,z365,z5,z6]),(0,[z8,z0,z103,z2,z4,z97,z6]),(0,[z8,z0,z2,z4,z652,z5,z6])],[(0,[z8,z0,z2,z16,z4,z6,z37]),(0,[z8,z347,z0,z2,z4,z5,z6])],[(0,[z8,z100,z1,z2,z4,z5,z6]),(0,[z653,z8,z0,z2,z4,z5,z6]),(0,[z116,z8,z203,z2,z4,z5,z6]),(0,[z654,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z655,z5,z6])],[(0,[z8,z0,z3,z4,z5,z11,z6]),(0,[z45,z327,z0,z2,z4,z5,z6]),(1,[z8,z0,z2,z414,z5,z6])],[(0,[z8,z31,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z656,z5,z6])],[(0,[z8,z0,z3,z16,z4,z5,z6]),(0,[z8,z0,z2,z657,z4,z5,z6]),(0,[z537,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z658]),(1,[z339,z0,z2,z4,z5,z6])],[(1,[z8,z0,z2,z4,z125,z37])],[(0,[z84,z8,z0,z3,z4,z5,z6]),(1,[z116,z0,z2,z47,z5,z6]),(0,[z8,z0,z2,z659,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z179,z6])],[(0,[z8,z0,z660,z3,z4,z5,z6])],[(0,[z8,z0,z2,z4,z661,z5,z6]),(0,[z70,z8,z0,z25,z4,z5,z6])],[(1,[z8,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z443,z4,z5,z6])],[(0,[z8,z0,z103,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z662,z5,z6]),(0,[z663,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z16,z4,z5,z19])]],
   [[(0,[z664,z8,z0,z2,z4,z5,z6]),(0,[z116,z8,z0,z2,z4,z5,z91]),(0,[z8,z45,z0,z4,z39,z5,z6])],[(0,[z8,z0,z284,z2,z4,z5,z6])],[(0,[z8,z45,z101,z0,z4,z5,z6]),(0,[z665,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z427,z2,z4,z5,z6])],[(1,[z8,z0,z32,z4,z5,z6]),(0,[z8,z472,z0,z2,z4,z5,z6])],[(0,[z666,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z5,z144,z6]),(1,[z8,z203,z2,z4,z5,z6]),(0,[z8,z0,z2,z183,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z19,z6])],[(0,[z667,z8,z0,z3,z4,z5,z6]),(1,[z8,z206,z2,z4,z5,z6])],[(0,[z8,z0,z2,z668,z4,z5,z6]),(0,[z8,z255,z0,z2,z4,z5,z6]),(1,[z8,z49,z182,z4,z5,z6])],[(0,[z8,z669,z23,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z47,z5,z6]),(0,[z8,z31,z0,z558,z4,z5,z6])],[(0,[z670,z8,z0,z2,z4,z5,z6]),(1,[z8,z0,z2,z4,z387,z6]),(1,[z8,z210,z2,z4,z5,z6])],[(1,[z67,z1,z2,z4,z5,z6]),(1,[z8,z134,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z671,z5,z6]),(0,[z8,z0,z2,z4,z672,z5,z6])],[(0,[z176,z8,z1,z2,z4,z5,z6]),(0,[z673,z8,z0,z2,z4,z5,z6]),(0,[z8,z674,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z675,z5,z6]),(0,[z8,z676,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z6,z677])],[(0,[z8,z0,z32,z2,z4,z6,z37]),(0,[z33,z8,z22,z0,z2,z4,z6]),(0,[z8,z0,z2,z4,z138,z5,z6])],[(0,[z116,z8,z0,z2,z4,z479,z6]),(0,[z8,z0,z2,z4,z6,z37,z193]),(0,[z8,z678,z0,z2,z4,z5,z6])],[(0,[z67,z124,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z679,z4,z5,z6])],[(0,[z8,z0,z450,z2,z4,z5,z6])]],
   [[(0,[z84,z8,z23,z2,z4,z5,z6]),(0,[z8,z639,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z680])],[],[(0,[z8,z23,z2,z4,z364,z5,z6]),(0,[z8,z574,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z681]),(0,[z8,z0,z2,z4,z97,z5,z6])],[(0,[z116,z8,z0,z373,z4,z5,z6]),(0,[z8,z0,z2,z4,z682,z5,z6]),(0,[z8,z0,z2,z4,z5,z683,z6])],[(0,[z8,z0,z3,z4,z5,z6,z61]),(0,[z95,z8,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z684]),(0,[z8,z20,z0,z2,z4,z5,z193]),(0,[z8,z0,z685,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z178,z5,z6]),(0,[z8,z0,z25,z2,z4,z5,z6]),(0,[z8,z0,z21,z4,z5,z6,z99])],[(0,[z8,z0,z32,z102,z4,z5,z6]),(0,[z116,z8,z0,z2,z146,z5,z6]),(0,[z8,z49,z0,z4,z39,z5,z6]),(0,[z8,z0,z395,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z686,z5,z6])],[(0,[z237,z8,z1,z2,z4,z5,z6]),(0,[z8,z8,z0,z3,z4,z5,z6]),(0,[z98,z8,z0,z2,z168,z5,z6]),(1,[z8,z0,z2,z4,z380,z6])],[(0,[z8,z101,z0,z4,z5,z60,z6]),(0,[z8,z0,z2,z4,z58,z6,z37])],[(0,[z8,z182,z1,z2,z4,z5,z6]),(0,[z8,z23,z2,z4,z5,z377,z6])],[(0,[z687,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z96,z4,z5,z18]),(0,[z688,z8,z0,z2,z4,z5,z6]),(0,[z8,z689,z0,z2,z4,z5,z6]),(0,[z7,z8,z0,z2,z16,z5,z6])],[(0,[z8,z669,z0,z2,z4,z5,z6]),(1,[z8,z0,z2,z4,z479,z6]),(1,[z8,z0,z2,z138,z5,z6])],[(0,[z7,z376,z0,z2,z4,z5,z6])],[(1,[z8,z545,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z543,z5,z6])],[(0,[z690,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z96,z4,z6,z37])],[(0,[z691,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z133]),(0,[z692,z8,z0,z2,z4,z5,z6])]],
   [[(0,[z8,z45,z0,z4,z5,z144,z6]),(0,[z8,z0,z2,z4,z5,z6,z693])],[(0,[z8,z0,z32,z4,z5,z6,z99]),(1,[z8,z0,z373,z4,z5,z6]),(0,[z8,z131,z0,z2,z405,z5,z6]),(0,[z8,z0,z2,z4,z168,z5,z6])],[(0,[z8,z0,z2,z4,z5,z559,z6]),(0,[z8,z0,z3,z96,z4,z5,z6]),(0,[z8,z22,z110,z0,z2,z4,z6]),(0,[z8,z0,z2,z4,z6,z37,z693])],[(0,[z8,z110,z0,z2,z4,z179,z6]),(0,[z8,z0,z2,z694,z4,z5,z6])],[(0,[z8,z0,z2,z253,z4,z5,z6]),(0,[z8,z0,z695,z2,z4,z5,z6]),(0,[z84,z8,z0,z2,z4,z5,z6])],[(0,[z237,z186,z0,z2,z4,z5,z6]),(0,[z8,z0,z660,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z696])],[(0,[z8,z31,z0,z3,z4,z5,z6])],[(0,[z8,z23,z2,z4,z5,z11,z6]),(0,[z8,z0,z4,z39,z5,z6,z99])],[(0,[z191,z8,z22,z0,z2,z4,z6]),(0,[z8,z45,z0,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z5,z697,z6])],[(0,[z8,z23,z2,z16,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z6,z698]),(0,[z8,z22,z24,z0,z2,z4,z6]),(1,[z8,z0,z284,z4,z5,z6]),(0,[z8,z0,z699,z2,z4,z5,z6]),(0,[z700,z8,z0,z2,z4,z5,z6])],[(1,[z8,z1,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z324,z6]),(0,[z8,z0,z2,z4,z5,z6,z701]),(0,[z8,z0,z2,z424,z4,z5,z6])],[(0,[z95,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z702,z4,z5,z6]),(0,[z8,z0,z2,z5,z19,z6,z40])],[(0,[z52,z8,z0,z3,z4,z5,z6]),(0,[z8,z1,z2,z4,z288,z5,z6]),(0,[z8,z8,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z39,z5,z6,z61]),(0,[z8,z0,z2,z4,z5,z703,z6])],[(0,[z186,z0,z32,z2,z4,z5,z6]),(1,[z8,z45,z21,z4,z5,z6]),(0,[z704,z8,z0,z2,z4,z5,z6])],[(0,[z667,z8,z0,z2,z4,z5,z6]),(0,[z8,z0,z705,z2,z4,z5,z6]),(0,[z8,z0,z2,z89,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z29,z37])],[(0,[z8,z23,z110,z2,z4,z5,z6]),(0,[z8,z706,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z325,z5,z6]),(0,[z8,z131,z22,z0,z2,z4,z6]),(1,[z8,z0,z2,z16,z5,z19])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z8,z1,z2,z4,z5,z259]),(0,[z8,z23,z512,z4,z5,z6]),(0,[z8,z0,z707,z4,z5,z6]),(0,[z45,z327,z21,z4,z5,z6]),(0,[z8,z31,z0,z2,z6,z61])],[(0,[z167,z0,z104,z4,z5,z6]),(0,[z8,z0,z2,z4,z217,z37]),(0,[z8,z121,z0,z4,z6,z37]),(0,[z613,z8,z0,z2,z6,z61]),(0,[z8,z0,z197,z16,z5,z6])],[(0,[z191,z708,z2,z4,z5,z6]),(0,[z191,z22,z0,z3,z4,z6]),(0,[z8,z0,z32,z4,z709,z6]),(0,[z8,z0,z32,z4,z77,z6]),(0,[z8,z22,z0,z2,z68,z6]),(1,[z327,z21,z4,z5,z6]),(0,[z710,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z686,z37]),(0,[z339,z0,z94,z4,z5,z6])],[(0,[z98,z8,z23,z4,z5,z99]),(0,[z8,z0,z3,z711,z5,z6]),(0,[z8,z0,z32,z4,z5,z324]),(0,[z704,z0,z2,z4,z53,z6]),(0,[z249,z22,z0,z2,z4,z6]),(0,[z8,z712,z2,z4,z5,z6]),(0,[z376,z0,z197,z4,z5,z6])],[(0,[z8,z0,z189,z3,z4,z6]),(0,[z8,z0,z2,z4,z436,z37]),(0,[z0,z3,z4,z5,z6,z125]),(0,[z8,z203,z2,z4,z5,z324]),(0,[z8,z713,z0,z2,z4,z324]),(0,[z70,z0,z2,z68,z43,z6]),(0,[z8,z206,z438,z4,z5,z6])],[(0,[z8,z410,z2,z4,z5,z6]),(0,[z8,z0,z373,z4,z6,z37]),(0,[z8,z227,z0,z4,z5,z6]),(0,[z8,z101,z0,z300,z5,z6])],[(0,[z237,z1,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z714]),(0,[z8,z0,z2,z4,z320,z6]),(0,[z8,z0,z715,z4,z5,z6]),(0,[z8,z2,z4,z5,z716,z6])],[(0,[z8,z0,z2,z5,z6,z717]),(0,[z8,z110,z0,z2,z68,z6]),(0,[z8,z449,z20,z2,z4,z11]),(0,[z8,z0,z103,z4,z6,z29])],[(0,[z8,z22,z1,z3,z4,z6]),(0,[z614,z1,z2,z4,z5,z6]),(0,[z8,z78,z3,z4,z5,z6]),(0,[z8,z0,z2,z718,z5,z6]),(0,[z8,z0,z2,z4,z91,z719]),(0,[z8,z22,z0,z2,z168,z6]),(0,[z8,z252,z0,z231,z4,z6])],[(0,[z242,z2,z3,z4,z5,z6]),(0,[z124,z0,z3,z146,z5,z6]),(0,[z8,z720,z0,z4,z5,z6]),(0,[z295,z0,z284,z4,z5,z6])],[(0,[z8,z0,z721,z4,z5,z6]),(0,[z8,z0,z722,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z200])],[(0,[z8,z23,z723,z4,z5,z6]),(0,[z8,z24,z2,z137,z5,z6]),(0,[z8,z0,z4,z5,z6,z724]),(0,[z8,z0,z2,z4,z6,z725])],[(0,[z603,z1,z3,z4,z5,z6]),(0,[z8,z0,z2,z726,z5,z6])],[(0,[z8,z22,z0,z2,z4,z6]),(0,[z87,z0,z3,z4,z5,z6]),(0,[z8,z0,z284,z4,z6,z37]),(0,[z8,z0,z2,z138,z325,z6]),(0,[z8,z727,z0,z4,z5,z6]),(0,[z8,z31,z0,z2,z6,z728])],[(0,[z8,z0,z2,z4,z729,z6]),(0,[z1,z102,z3,z4,z5,z6]),(0,[z8,z1,z32,z4,z6,z37]),(0,[z8,z0,z730,z4,z5,z6]),(0,[z339,z731,z2,z4,z5,z6])],[(0,[z1,z1,z3,z4,z5,z6]),(0,[z8,z1,z4,z365,z5,z6]),(0,[z33,z23,z2,z4,z5,z125]),(0,[z8,z390,z2,z4,z5,z6]),(0,[z8,z182,z732,z4,z5,z6]),(0,[z8,z22,z0,z2,z733,z6])]],
   [[(0,[z8,z734,z2,z4,z5,z6]),(0,[z24,z1,z3,z4,z5,z6]),(0,[z8,z23,z2,z4,z13,z6]),(0,[z67,z410,z2,z4,z5,z6]),(0,[z472,z0,z2,z4,z543,z6]),(0,[z8,z735,z2,z4,z5,z6])],[(0,[z176,z1,z3,z4,z5,z6]),(0,[z465,z0,z3,z4,z5,z6]),(0,[z140,z0,z2,z4,z5,z125]),(0,[z8,z45,z21,z4,z6,z37]),(0,[z8,z210,z94,z4,z5,z6])],[(0,[z191,z0,z2,z4,z125,z37]),(0,[z481,z0,z2,z47,z5,z6]),(0,[z8,z93,z393,z4,z5,z6]),(0,[z8,z0,z2,z736,z5,z6]),(0,[z419,z164,z0,z2,z4,z6])],[(0,[z8,z0,z2,z737,z5,z6]),(0,[z8,z348,z2,z4,z5,z6]),(0,[z204,z0,z3,z4,z5,z6]),(0,[z8,z0,z738,z4,z5,z6]),(0,[z8,z0,z739,z4,z5,z6]),(0,[z8,z0,z2,z740,z5,z6]),(0,[z8,z110,z2,z4,z716,z6]),(0,[z167,z741,z2,z4,z5,z6])],[(0,[z8,z281,z21,z4,z5,z6]),(0,[z23,z142,z2,z4,z5,z6]),(0,[z8,z22,z0,z521,z4,z6]),(0,[z8,z0,z512,z4,z5,z6]),(0,[z8,z390,z2,z4,z543,z6]),(0,[z8,z0,z395,z4,z6,z29])],[(1,[z1,z2,z4,z125,z37]),(0,[z376,z1,z2,z4,z5,z6]),(0,[z8,z0,z742,z4,z5,z6]),(0,[z8,z49,z22,z182,z4,z6]),(0,[z98,z8,z0,z4,z77,z99])],[(0,[z23,z1,z32,z4,z5,z6]),(0,[z67,z23,z3,z4,z5,z6]),(0,[z0,z2,z4,z47,z5,z91]),(0,[z8,z348,z2,z361,z5,z6]),(0,[z8,z743,z2,z4,z5,z6])],[(0,[z205,z8,z2,z4,z377,z6]),(0,[z8,z0,z2,z4,z744,z6]),(0,[z8,z20,z32,z4,z5,z11]),(0,[z8,z22,z0,z2,z4,z579]),(0,[z95,z8,z2,z178,z6,z37]),(0,[z8,z0,z103,z4,z97,z6])],[(0,[z158,z8,z110,z2,z4,z6]),(0,[z8,z0,z393,z4,z5,z6]),(0,[z8,z0,z745,z4,z5,z6]),(0,[z566,z8,z2,z178,z5,z6])],[(0,[z1,z3,z4,z58,z5,z6]),(0,[z8,z189,z202,z2,z4,z6]),(0,[z8,z0,z4,z5,z6,z746]),(0,[z8,z23,z102,z4,z5,z144]),(0,[z8,z22,z0,z2,z4,z349]),(0,[z8,z0,z2,z4,z77,z6])],[(0,[z8,z0,z2,z4,z5,z747]),(0,[z8,z0,z2,z4,z37,z698]),(0,[z167,z0,z2,z105,z5,z6])],[(0,[z8,z30,z2,z4,z5,z340]),(0,[z237,z22,z0,z3,z4,z6]),(0,[z67,z0,z3,z4,z5,z125]),(0,[z8,z0,z2,z4,z479,z324]),(0,[z8,z22,z0,z245,z4,z6]),(0,[z8,z0,z284,z4,z325,z6])],[(0,[z1,z3,z4,z39,z5,z6]),(0,[z519,z0,z3,z4,z5,z6]),(0,[z8,z421,z3,z4,z5,z6]),(0,[z186,z0,z32,z4,z6,z37]),(0,[z8,z748,z2,z4,z5,z6])],[(0,[z8,z348,z2,z4,z5,z579]),(0,[z8,z210,z2,z16,z5,z6])],[(0,[z8,z0,z749,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z40]),(0,[z124,z23,z2,z146,z5,z6]),(0,[z8,z0,z32,z4,z6,z139]),(0,[z8,z374,z2,z4,z387,z6]),(0,[z0,z2,z214,z5,z6,z125]),(0,[z84,z8,z2,z4,z37,z193]),(0,[z750,z0,z2,z4,z5,z6]),(0,[z8,z609,z0,z4,z60,z6]),(1,[z8,z0,z4,z751,z6]),(0,[z8,z0,z102,z168,z5,z6]),(0,[z8,z0,z2,z4,z5,z752]),(0,[z356,z323,z0,z2,z4,z6])],[(0,[z8,z0,z753,z4,z5,z6]),(0,[z8,z0,z723,z4,z5,z6]),(0,[z8,z0,z2,z754,z4,z6]),(0,[z167,z0,z2,z168,z5,z6]),(0,[z376,z210,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z5,z125,z40]),(0,[z8,z0,z755,z4,z5,z6]),(0,[z8,z0,z443,z4,z5,z6]),(0,[z8,z0,z94,z4,z380,z6]),(0,[z8,z756,z2,z4,z5,z6])],[(0,[z8,z757,z1,z2,z4,z6]),(0,[z8,z1,z2,z248,z5,z6])],[(0,[z758,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z18,z37])],[(0,[z8,z0,z450,z4,z5,z6]),(0,[z8,z759,z2,z4,z5,z6]),(0,[z8,z760,z2,z4,z5,z6]),(0,[z8,z503,z2,z4,z5,z6])],[(0,[z8,z1,z190,z4,z5,z6]),(0,[z8,z0,z3,z4,z543,z6]),(0,[z8,z0,z2,z4,z6,z761]),(0,[z8,z22,z227,z0,z4,z6])],[(0,[z158,z52,z1,z2,z4,z6]),(0,[z472,z0,z3,z4,z5,z6]),(0,[z8,z2,z4,z762,z5,z6]),(0,[z8,z0,z2,z4,z6,z763]),(0,[z98,z8,z390,z4,z5,z99])],[(0,[z124,z1,z3,z4,z5,z6]),(0,[z8,z1,z2,z405,z5,z6]),(0,[z465,z23,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z396,z6]),(0,[z8,z0,z2,z764,z5,z6])],[(0,[z158,z0,z1,z3,z4,z6]),(0,[z8,z412,z2,z4,z5,z11]),(0,[z8,z0,z765,z4,z5,z6]),(0,[z0,z650,z32,z4,z5,z6]),(0,[z8,z0,z32,z766,z5,z6]),(0,[z8,z0,z2,z4,z477,z37])],[(0,[z1,z3,z4,z143,z5,z6]),(0,[z81,z1,z2,z4,z5,z6]),(0,[z8,z24,z3,z218,z5,z6]),(0,[z0,z3,z4,z260,z5,z6]),(0,[z767,z0,z2,z4,z5,z6]),(0,[z8,z0,z183,z768,z5,z6]),(0,[z8,z503,z2,z4,z543,z6])],[(0,[z484,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z769,z5,z6]),(0,[z770,z0,z2,z4,z5,z6]),(0,[z8,z0,z771,z4,z5,z6]),(0,[z8,z0,z2,z16,z19,z37]),(0,[z8,z0,z772,z4,z5,z6])],[(0,[z591,z1,z3,z4,z5,z6]),(0,[z8,z0,z773,z4,z5,z6]),(0,[z8,z0,z3,z4,z6,z309]),(0,[z8,z0,z2,z774,z5,z6]),(0,[z8,z22,z775,z2,z4,z6])],[(0,[z8,z123,z0,z3,z4,z6]),(0,[z8,z22,z0,z190,z4,z6]),(0,[z8,z0,z2,z4,z776,z6])],[(0,[z1,z3,z4,z5,z18,z6]),(0,[z533,z1,z3,z4,z5,z6]),(0,[z8,z0,z2,z711,z5,z6]),(0,[z8,z0,z2,z4,z5,z777]),(0,[z8,z45,z0,z168,z5,z6]),(0,[z8,z0,z4,z414,z60,z6]),(0,[z8,z0,z778,z4,z5,z6])],[(0,[z23,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z165,z6]),(0,[z1,z2,z4,z5,z6,z170]),(0,[z8,z0,z3,z4,z6,z779]),(0,[z8,z780,z2,z4,z5,z6]),(0,[z67,z0,z2,z4,z18,z37]),(0,[z8,z0,z2,z781,z4,z6]),(0,[z8,z0,z782,z4,z5,z6]),(0,[z8,z0,z2,z4,z487,z37]),(0,[z8,z783,z2,z4,z5,z6])],[(0,[z0,z32,z3,z4,z6,z37]),(0,[z8,z20,z2,z4,z5,z11])],[(0,[z8,z23,z558,z4,z5,z6]),(0,[z8,z784,z0,z2,z4,z6]),(0,[z339,z22,z0,z2,z4,z6]),(0,[z8,z731,z2,z4,z5,z6])]],
   [[(0,[z8,z0,z2,z4,z6,z785]),(0,[z8,z145,z0,z330,z5,z6]),(0,[z8,z786,z2,z4,z5,z6]),(0,[z8,z787,z2,z4,z5,z6])],[(0,[z8,z78,z2,z4,z5,z6]),(0,[z8,z0,z2,z788,z5,z6]),(0,[z0,z597,z3,z4,z5,z6]),(0,[z8,z410,z32,z4,z5,z6]),(0,[z8,z92,z0,z2,z6,z61]),(0,[z98,z327,z0,z4,z5,z6]),(0,[z8,z0,z789,z4,z6,z37])],[(0,[z8,z0,z2,z790,z5,z6]),(0,[z8,z23,z253,z4,z5,z6]),(0,[z8,z0,z32,z4,z320,z6]),(0,[z8,z0,z791,z4,z5,z6]),(0,[z95,z8,z2,z762,z5,z6]),(1,[z8,z0,z768,z5,z6])],[(0,[z472,z792,z2,z4,z5,z6]),(0,[z8,z793,z0,z4,z5,z6])],[(0,[z8,z388,z182,z4,z5,z6]),(0,[z8,z22,z545,z2,z4,z6]),(0,[z8,z0,z190,z4,z5,z91]),(0,[z8,z101,z0,z4,z155,z6]),(0,[z8,z794,z2,z4,z5,z6])],[(0,[z191,z545,z2,z4,z5,z6])],[(0,[z8,z795,z0,z2,z4,z6]),(0,[z667,z1,z3,z4,z5,z6]),(0,[z8,z1,z796,z2,z4,z6]),(0,[z8,z0,z2,z4,z5,z797]),(0,[z8,z110,z3,z4,z179,z6]),(0,[z8,z0,z32,z4,z6,z200]),(0,[z8,z49,z264,z4,z5,z6]),(0,[z8,z0,z2,z4,z798,z6]),(0,[z799,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z751,z6])],[(0,[z1,z2,z4,z5,z6,z192]),(0,[z472,z0,z32,z4,z5,z6]),(0,[z8,z101,z0,z76,z5,z6]),(0,[z8,z0,z2,z4,z800,z6])],[(0,[z1,z2,z4,z5,z6,z196]),(0,[z8,z801,z0,z3,z4,z6]),(0,[z8,z0,z802,z4,z5,z6])],[(0,[z186,z803,z2,z4,z5,z6]),(0,[z8,z23,z2,z4,z543,z6]),(0,[z8,z0,z34,z4,z5,z6]),(0,[z8,z0,z104,z4,z6,z37]),(0,[z804,z0,z2,z4,z5,z6]),(0,[z108,z8,z0,z2,z5,z40]),(0,[z8,z0,z103,z4,z751,z6])],[(0,[z8,z0,z4,z805,z5,z6]),(0,[z8,z806,z2,z4,z5,z6]),(0,[z8,z807,z2,z4,z5,z6]),(0,[z7,z8,z210,z2,z5,z40])],[(0,[z8,z0,z808,z4,z5,z6]),(0,[z182,z1,z3,z4,z5,z6]),(0,[z8,z121,z1,z4,z5,z6]),(0,[z809,z8,z0,z2,z4,z6]),(0,[z8,z0,z103,z4,z201,z6]),(0,[z8,z390,z32,z4,z5,z6]),(0,[z8,z0,z2,z68,z6,z37]),(0,[z8,z0,z810,z4,z5,z6]),(0,[z8,z0,z811,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z812]),(0,[z8,z813,z0,z2,z4,z6])],[(0,[z1,z3,z4,z5,z6,z290]),(0,[z8,z0,z2,z4,z396,z6]),(1,[z0,z2,z214,z5,z125]),(0,[z8,z0,z2,z4,z6,z814])],[(0,[z8,z0,z3,z4,z13,z6]),(0,[z8,z49,z0,z168,z5,z6]),(0,[z295,z20,z2,z4,z5,z6])],[(0,[z1,z2,z157,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z125]),(0,[z1,z3,z4,z47,z5,z6]),(0,[z8,z1,z393,z4,z5,z6]),(0,[z8,z131,z1,z4,z60,z6]),(0,[z8,z23,z2,z815,z5,z6]),(0,[z8,z23,z2,z4,z6,z309]),(0,[z8,z348,z32,z4,z5,z6]),(0,[z8,z0,z816,z2,z4,z6]),(0,[z8,z0,z2,z417,z5,z19]),(0,[z8,z0,z817,z4,z5,z6])]],
   [[(0,[z484,z0,z2,z4,z5,z6]),(0,[z8,z1,z438,z4,z5,z6]),(0,[z8,z1,z4,z5,z6,z746]),(0,[z8,z1,z2,z4,z77,z6]),(0,[z8,z22,z203,z2,z4,z6]),(0,[z67,z0,z104,z4,z5,z18])],[(0,[z8,z1,z2,z4,z5,z324]),(0,[z818,z8,z1,z2,z4,z6])],[(0,[z524,z8,z2,z364,z5,z6]),(0,[z70,z0,z245,z4,z43,z6]),(0,[z8,z0,z819,z4,z5,z6]),(0,[z8,z0,z443,z4,z6,z61]),(0,[z8,z0,z820,z4,z6,z37])],[(0,[z8,z22,z0,z157,z4,z6]),(0,[z8,z202,z147,z4,z5,z6]),(0,[z8,z0,z2,z4,z37,z229])],[(0,[z8,z23,z521,z4,z5,z6]),(0,[z8,z821,z2,z4,z5,z6])],[(0,[z8,z421,z2,z4,z5,z6]),(0,[z8,z822,z2,z4,z5,z6]),(0,[z673,z0,z2,z4,z5,z125]),(0,[z8,z255,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z5,z823]),(0,[z8,z0,z2,z4,z824,z6])],[(0,[z8,z428,z184,z2,z4,z6])],[(0,[z8,z1,z443,z4,z5,z6]),(0,[z8,z0,z129,z4,z6,z37]),(0,[z8,z0,z2,z4,z825,z6]),(0,[z376,z0,z2,z4,z5,z40])],[(0,[z8,z0,z2,z4,z826,z6]),(0,[z142,z0,z3,z4,z5,z6]),(0,[z8,z0,z660,z4,z371,z6]),(0,[z8,z827,z2,z4,z5,z6]),(0,[z8,z421,z2,z361,z5,z6]),(0,[z8,z828,z0,z2,z4,z18]),(0,[z8,z110,z2,z4,z6,z57]),(0,[z8,z0,z829,z4,z5,z6])],[(0,[z8,z0,z830,z4,z5,z6])],[(0,[z8,z1,z450,z4,z5,z6]),(0,[z8,z1,z94,z4,z5,z6]),(0,[z0,z253,z4,z5,z6,z125]),(0,[z8,z0,z438,z4,z387,z6]),(0,[z8,z0,z2,z4,z831,z6]),(0,[z8,z22,z0,z2,z138,z6])],[(0,[z8,z22,z1,z2,z4,z37]),(0,[z0,z699,z3,z4,z5,z6]),(0,[z456,z0,z3,z4,z5,z6]),(0,[z8,z832,z2,z4,z5,z6]),(0,[z124,z0,z2,z4,z125,z37]),(0,[z8,z0,z833,z4,z5,z6]),(0,[z8,z0,z197,z5,z6,z40])],[(0,[z158,z8,z1,z2,z4,z6]),(0,[z158,z8,z2,z4,z163,z6]),(0,[z8,z834,z2,z4,z5,z6]),(0,[z70,z0,z2,z4,z43,z259]),(0,[z67,z255,z2,z4,z5,z18]),(0,[z256,z0,z2,z4,z5,z18]),(0,[z8,z22,z0,z512,z4,z6]),(0,[z8,z0,z284,z248,z5,z6])],[(0,[z8,z0,z2,z187,z273,z6]),(0,[z835,z8,z2,z4,z5,z6]),(0,[z8,z0,z836,z4,z5,z6])],[(0,[z8,z23,z3,z4,z5,z6]),(0,[z8,z837,z0,z2,z4,z6]),(0,[z472,z0,z2,z4,z5,z6]),(0,[z8,z838,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z18,z37]),(0,[z8,z117,z190,z4,z5,z6]),(0,[z8,z0,z2,z4,z839,z6]),(0,[z8,z0,z147,z4,z6,z37]),(0,[z8,z374,z2,z187,z5,z6]),(0,[z8,z840,z2,z4,z5,z6]),(0,[z67,z0,z129,z4,z5,z18]),(0,[z841,z0,z2,z4,z5,z6])],[(0,[z8,z0,z149,z4,z6,z37]),(1,[z242,z3,z4,z5,z6]),(0,[z33,z0,z32,z4,z5,z125]),(0,[z8,z503,z32,z4,z5,z6]),(0,[z8,z117,z2,z4,z6,z37]),(0,[z8,z421,z2,z4,z5,z579]),(0,[z8,z0,z245,z68,z5,z6]),(0,[z0,z2,z4,z53,z839,z6]),(0,[z842,z0,z2,z4,z5,z6]),(0,[z376,z0,z843,z4,z5,z6])]],
   [[(0,[z8,z23,z157,z4,z5,z6]),(0,[z186,z189,z1,z2,z4,z6]),(0,[z0,z844,z3,z4,z5,z6]),(0,[z86,z2,z3,z4,z5,z6]),(0,[z84,z8,z32,z4,z5,z193]),(0,[z8,z2,z138,z5,z6,z193]),(0,[z8,z0,z2,z4,z5,z845]),(0,[z8,z0,z2,z89,z6,z72])],[(0,[z67,z0,z253,z4,z5,z6]),(0,[z8,z24,z2,z218,z5,z6]),(0,[z8,z0,z2,z4,z6,z846])],[(0,[z8,z0,z2,z4,z847,z6]),(0,[z8,z0,z848,z4,z5,z6]),(0,[z8,z0,z849,z4,z5,z6]),(0,[z8,z0,z2,z105,z6,z37]),(0,[z8,z22,z0,z722,z4,z6])],[(0,[z115,z0,z3,z4,z5,z6]),(0,[z8,z0,z2,z815,z5,z6]),(0,[z36,z0,z2,z146,z5,z6]),(0,[z850,z0,z2,z4,z5,z6])],[(0,[z8,z0,z844,z4,z5,z6]),(0,[z8,z851,z0,z4,z5,z6]),(0,[z8,z22,z0,z2,z16,z19])],[(0,[z1,z3,z239,z4,z5,z6]),(0,[z109,z8,z3,z4,z163,z6]),(0,[z8,z0,z32,z769,z5,z6]),(0,[z8,z0,z852,z4,z5,z6]),(0,[z8,z101,z0,z183,z6,z37])],[(0,[z8,z23,z2,z89,z143,z6]),(0,[z8,z0,z2,z4,z6,z779])],[(0,[z8,z1,z2,z4,z6,z785]),(0,[z1,z3,z21,z4,z5,z6]),(0,[z8,z0,z2,z168,z6,z37]),(0,[z7,z8,z0,z2,z37,z40])],[(0,[z8,z0,z521,z4,z5,z6]),(0,[z0,z393,z4,z5,z6,z125]),(0,[z8,z0,z853,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z99]),(0,[z639,z1,z3,z4,z5,z6]),(0,[z8,z854,z0,z2,z4,z6]),(0,[z8,z0,z2,z68,z5,z259]),(0,[z8,z0,z443,z89,z5,z6])],[(0,[z1,z3,z4,z5,z246,z6]),(0,[z186,z1,z2,z4,z6,z37]),(0,[z8,z0,z855,z4,z5,z6]),(0,[z419,z0,z2,z4,z53,z6])],[(0,[z574,z1,z3,z4,z5,z6]),(0,[z856,z0,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z6,z139]),(0,[z8,z0,z2,z4,z5,z857]),(0,[z8,z24,z2,z218,z6,z309])],[(0,[z8,z22,z23,z3,z4,z6]),(0,[z8,z78,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z858]),(0,[z7,z8,z0,z2,z5,z40])],[(0,[z0,z3,z96,z4,z5,z125]),(0,[z124,z0,z32,z146,z5,z6]),(0,[z8,z0,z2,z4,z6,z859]),(0,[z8,z860,z2,z4,z5,z6])],[(0,[z67,z0,z844,z4,z5,z6]),(0,[z124,z0,z2,z4,z5,z91]),(0,[z116,z22,z0,z2,z47,z6]),(0,[z8,z0,z2,z187,z6,z37]),(0,[z8,z0,z367,z4,z97,z6]),(0,[z8,z0,z2,z861,z6,z37])]],
   [[(0,[z8,z862,z2,z4,z5,z6]),(0,[z8,z0,z863,z4,z5,z6]),(0,[z8,z0,z2,z4,z864,z6]),(0,[z8,z22,z0,z2,z414,z6])],[(0,[z8,z1,z4,z805,z5,z6]),(0,[z8,z0,z2,z865,z5,z6]),(0,[z116,z0,z2,z47,z396,z6]),(0,[z8,z0,z866,z4,z5,z6])],[(0,[z8,z0,z3,z4,z5,z6]),(0,[z23,z32,z3,z4,z5,z6]),(0,[z8,z867,z2,z4,z5,z6]),(1,[z0,z2,z4,z5,z868]),(0,[z8,z22,z869,z2,z4,z6])],[(0,[z1,z2,z4,z260,z5,z6]),(0,[z8,z625,z0,z2,z6,z61]),(0,[z176,z0,z147,z4,z53,z6]),(0,[z0,z2,z4,z5,z18,z868]),(0,[z8,z870,z0,z4,z5,z6]),(0,[z8,z0,z2,z871,z5,z6])],[(0,[z8,z1,z2,z4,z396,z6]),(0,[z8,z0,z373,z4,z5,z324]),(0,[z8,z45,z316,z4,z5,z6]),(0,[z872,z8,z0,z2,z4,z6]),(0,[z8,z22,z0,z2,z4,z451])],[(0,[z1,z3,z262,z4,z5,z6]),(0,[z8,z0,z3,z361,z5,z6]),(0,[z8,z0,z32,z873,z5,z6]),(0,[z874,z0,z2,z4,z5,z6]),(0,[z8,z449,z0,z2,z4,z6])],[(0,[z67,z86,z3,z4,z5,z6]),(0,[z580,z0,z32,z4,z5,z6]),(0,[z33,z0,z2,z4,z5,z125]),(0,[z8,z0,z2,z4,z6,z875]),(0,[z8,z0,z2,z4,z5,z876])],[(0,[z484,z1,z2,z4,z5,z6]),(0,[z8,z877,z2,z4,z5,z6]),(0,[z8,z206,z34,z4,z5,z6]),(0,[z84,z8,z2,z4,z5,z193]),(0,[z8,z0,z2,z4,z13,z6]),(0,[z8,z210,z2,z5,z6,z40]),(0,[z8,z22,z0,z878,z4,z6])],[(0,[z8,z242,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z879,z6]),(0,[z8,z49,z64,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z880]),(0,[z52,z189,z1,z2,z4,z6]),(0,[z8,z881,z0,z4,z5,z6]),(0,[z882,z8,z93,z2,z4,z6])],[(0,[z0,z3,z357,z4,z5,z6]),(0,[z8,z203,z2,z4,z396,z6]),(0,[z8,z0,z2,z4,z6,z883]),(0,[z8,z0,z2,z4,z884,z6])],[(0,[z8,z117,z2,z4,z5,z324]),(0,[z376,z0,z885,z4,z5,z6])],[(0,[z8,z0,z3,z4,z5,z579]),(0,[z8,z22,z134,z2,z4,z6]),(0,[z327,z0,z4,z5,z144,z6]),(0,[z886,z0,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z618])],[(0,[z249,z23,z2,z4,z5,z6]),(0,[z67,z0,z3,z4,z5,z6]),(0,[z8,z887,z0,z2,z4,z6]),(0,[z8,z0,z2,z214,z273,z6]),(0,[z0,z2,z4,z5,z868,z125]),(0,[z8,z888,z2,z4,z5,z6]),(0,[z8,z0,z889,z4,z5,z6])],[(0,[z8,z0,z890,z4,z5,z6]),(0,[z8,z891,z2,z4,z5,z6]),(0,[z8,z374,z2,z214,z5,z6]),(0,[z8,z0,z2,z4,z892,z6])],[(0,[z8,z0,z2,z4,z5,z893]),(0,[z445,z1,z2,z4,z5,z6]),(0,[z191,z23,z149,z4,z5,z6]),(0,[z667,z8,z0,z4,z5,z135]),(0,[z8,z0,z2,z4,z6,z894]),(0,[z124,z93,z2,z146,z5,z6]),(0,[z176,z202,z2,z4,z53,z6]),(0,[z8,z22,z0,z2,z4,z463]),(0,[z8,z0,z2,z143,z6,z728])]],
   [[(0,[z8,z1,z2,z4,z320,z6]),(0,[z8,z895,z2,z4,z5,z6]),(0,[z520,z0,z3,z4,z5,z6]),(0,[z167,z0,z2,z4,z6,z37]),(0,[z8,z0,z102,z4,z5,z144])],[(0,[z8,z1,z2,z5,z6,z717]),(0,[z8,z0,z3,z4,z6,z319]),(0,[z8,z421,z32,z4,z5,z6]),(0,[z8,z896,z0,z2,z4,z6]),(0,[z897,z0,z2,z4,z5,z6]),(0,[z84,z8,z121,z4,z5,z193]),(0,[z8,z20,z2,z4,z11,z37])],[(0,[z0,z86,z3,z4,z5,z6]),(0,[z8,z348,z25,z4,z5,z6]),(0,[z8,z0,z2,z168,z77,z6]),(0,[z8,z22,z0,z2,z898,z6])],[(0,[z8,z0,z2,z4,z899,z6]),(0,[z52,z1,z2,z4,z6,z37]),(0,[z8,z412,z2,z4,z5,z559]),(0,[z0,z3,z4,z5,z6,z370]),(0,[z8,z0,z900,z4,z5,z6])],[(0,[z8,z1,z2,z4,z6,z200]),(0,[z8,z0,z2,z4,z396,z91]),(0,[z670,z8,z0,z2,z5,z40]),(0,[z8,z901,z0,z2,z4,z6])],[(0,[z472,z1,z2,z4,z5,z6]),(0,[z266,z1,z2,z4,z5,z6]),(0,[z0,z902,z3,z4,z5,z6]),(0,[z8,z49,z533,z4,z5,z6]),(0,[z124,z0,z2,z146,z5,z6]),(0,[z8,z903,z2,z4,z5,z6]),(0,[z904,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z905,z6]),(0,[z8,z0,z4,z39,z155,z6]),(0,[z8,z906,z2,z4,z5,z6])],[(0,[z8,z907,z2,z4,z5,z6]),(0,[z8,z0,z3,z908,z5,z6]),(0,[z67,z0,z2,z4,z5,z578]),(0,[z8,z828,z0,z2,z4,z37]),(0,[z8,z0,z909,z4,z5,z6]),(0,[z8,z910,z2,z4,z5,z6])],[(0,[z8,z23,z2,z4,z5,z6]),(0,[z911,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z414,z97,z6])],[(0,[z255,z1,z2,z4,z5,z6]),(0,[z8,z148,z0,z3,z4,z6]),(0,[z8,z0,z2,z4,z6,z912]),(0,[z8,z2,z218,z762,z5,z6]),(0,[z8,z0,z2,z16,z19,z200])],[(0,[z191,z255,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z543,z6]),(0,[z8,z22,z0,z2,z248,z6])],[(0,[z8,z913,z1,z4,z5,z6]),(0,[z8,z23,z2,z361,z5,z6]),(0,[z266,z0,z32,z4,z5,z6]),(0,[z206,z2,z4,z5,z6,z125]),(0,[z8,z0,z438,z187,z5,z6]),(0,[z8,z914,z2,z4,z6,z37])],[(0,[z191,z0,z129,z4,z5,z6]),(0,[z8,z869,z2,z4,z5,z6]),(0,[z8,z0,z2,z214,z5,z18]),(0,[z8,z0,z4,z5,z6,z845])],[(0,[z8,z0,z2,z873,z5,z6]),(0,[z8,z915,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z916]),(0,[z8,z0,z4,z5,z6,z917])],[(0,[z8,z24,z32,z218,z5,z6]),(0,[z8,z0,z2,z5,z19,z752])],[(0,[z46,z1,z3,z4,z5,z6]),(1,[z1,z129,z4,z5,z6]),(0,[z8,z123,z1,z2,z4,z6]),(0,[z8,z1,z512,z4,z5,z6]),(0,[z8,z0,z32,z4,z847,z6]),(0,[z8,z0,z918,z4,z5,z6]),(0,[z919,z0,z2,z4,z5,z6]),(0,[z109,z8,z2,z4,z163,z6]),(0,[z8,z0,z920,z4,z5,z6]),(0,[z8,z0,z103,z4,z244,z6])],[(0,[z654,z1,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z6,z309]),(0,[z38,z8,z0,z2,z5,z40]),(0,[z8,z0,z2,z214,z6,z37]),(0,[z8,z22,z0,z2,z105,z6]),(0,[z8,z347,z0,z2,z6,z585])]],
   [[(0,[z345,z1,z2,z4,z5,z6]),(0,[z0,z189,z1,z3,z4,z6]),(0,[z8,z921,z93,z2,z4,z6]),(0,[z8,z0,z2,z922,z4,z5])],[(0,[z226,z1,z3,z4,z5,z6]),(0,[z8,z1,z103,z4,z97,z6]),(0,[z8,z23,z2,z4,z5,z579]),(0,[z0,z3,z4,z6,z125,z37]),(0,[z8,z923,z0,z3,z4,z6]),(0,[z8,z22,z0,z3,z96,z4])],[(0,[z639,z1,z2,z4,z5,z6]),(0,[z8,z0,z3,z414,z5,z6]),(0,[z924,z0,z2,z4,z5,z6])],[(0,[z295,z0,z2,z4,z251,z6]),(0,[z8,z0,z925,z4,z5,z6])],[(0,[z22,z0,z3,z4,z6,z125]),(0,[z8,z0,z3,z89,z143,z6]),(0,[z339,z0,z3,z4,z5,z6]),(0,[z484,z0,z2,z138,z5,z6]),(0,[z98,z8,z22,z0,z4,z99])],[(0,[z191,z23,z2,z4,z6,z37]),(0,[z520,z23,z2,z4,z5,z6]),(0,[z502,z8,z533,z4,z5,z6]),(0,[z8,z374,z2,z4,z273,z6]),(0,[z0,z2,z4,z214,z5,z125])],[(0,[z22,z23,z1,z2,z4,z6]),(0,[z8,z23,z2,z4,z6,z319]),(0,[z116,z0,z3,z47,z5,z6]),(0,[z8,z0,z2,z4,z677,z37]),(0,[z70,z348,z2,z4,z43,z6]),(0,[z8,z483,z0,z2,z4,z37]),(0,[z140,z0,z2,z4,z125,z37]),(0,[z8,z22,z24,z2,z218,z6]),(0,[z8,z0,z2,z4,z6,z926]),(0,[z8,z0,z558,z4,z5,z6]),(0,[z927,z0,z2,z4,z5,z6]),(0,[z8,z2,z4,z928,z5,z6]),(0,[z8,z0,z929,z4,z5,z6])],[(0,[z8,z0,z2,z4,z5,z930]),(0,[z1,z2,z4,z5,z6,z318]),(0,[z8,z432,z21,z4,z5,z6]),(0,[z8,z0,z373,z4,z396,z6]),(0,[z8,z22,z0,z2,z4,z91]),(0,[z8,z931,z0,z4,z5,z6]),(0,[z8,z0,z2,z4,z932,z6]),(0,[z8,z933,z0,z2,z4,z6])],[(0,[z8,z0,z3,z4,z934,z6]),(0,[z8,z935,z2,z4,z5,z6]),(0,[z67,z0,z2,z4,z5,z372]),(0,[z8,z22,z255,z2,z4,z6]),(0,[z8,z936,z0,z2,z4,z6])],[(0,[z8,z0,z253,z4,z5,z6]),(0,[z8,z22,z1,z32,z4,z6]),(0,[z8,z0,z2,z490,z4,z37]),(0,[z8,z22,z0,z2,z4,z498])],[(0,[z0,z32,z549,z4,z5,z6]),(0,[z8,z937,z2,z4,z5,z6]),(0,[z8,z134,z521,z4,z5,z6]),(0,[z0,z438,z4,z5,z6,z125])],[(0,[z8,z0,z2,z4,z5,z6]),(0,[z8,z801,z1,z2,z4,z6]),(0,[z8,z0,z2,z4,z6,z938]),(0,[z8,z0,z939,z4,z5,z6]),(0,[z8,z110,z32,z4,z179,z6]),(0,[z0,z2,z940,z47,z5,z6]),(0,[z0,z2,z146,z940,z5,z6]),(0,[z941,z0,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z18,z37]),(0,[z8,z23,z197,z4,z5,z6]),(0,[z237,z242,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z578,z37]),(0,[z8,z131,z0,z405,z60,z6]),(0,[z98,z8,z0,z4,z543,z99]),(0,[z8,z0,z942,z4,z5,z6])],[(0,[z33,z1,z2,z4,z5,z125]),(0,[z8,z0,z2,z4,z943,z6]),(0,[z8,z591,z0,z171,z5,z6]),(0,[z8,z0,z2,z4,z525,z37]),(0,[z8,z0,z2,z768,z5,z6]),(0,[z8,z148,z0,z102,z4,z144]),(0,[z8,z944,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z13,z6]),(0,[z8,z603,z2,z218,z5,z6]),(0,[z8,z0,z902,z4,z5,z6]),(0,[z8,z945,z0,z4,z5,z6]),(0,[z8,z0,z2,z4,z946,z6]),(0,[z8,z0,z2,z361,z5,z6]),(0,[z8,z2,z4,z716,z163,z6])],[(0,[z8,z101,z1,z183,z5,z6]),(0,[z8,z203,z3,z4,z5,z6]),(0,[z327,z0,z4,z39,z5,z6]),(0,[z8,z947,z2,z4,z5,z6])]],
   [[(0,[z8,z0,z948,z4,z5,z6]),(0,[z8,z123,z23,z2,z4,z6]),(0,[z8,z121,z23,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z949]),(0,[z8,z206,z3,z4,z5,z6]),(0,[z8,z0,z2,z950,z5,z6]),(0,[z8,z0,z2,z4,z543,z6])],[(0,[z8,z23,z2,z4,z951,z6])],[(0,[z8,z383,z0,z4,z60,z6]),(0,[z8,z0,z32,z952,z5,z6]),(0,[z124,z22,z0,z2,z146,z6]),(0,[z953,z0,z2,z4,z5,z6]),(0,[z484,z0,z284,z4,z5,z6]),(0,[z8,z954,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z955])],[(0,[z1,z3,z416,z4,z5,z6]),(0,[z8,z210,z3,z4,z5,z6]),(0,[z8,z0,z32,z4,z13,z6]),(0,[z8,z0,z956,z4,z5,z6]),(0,[z8,z957,z2,z4,z5,z6]),(0,[z8,z0,z2,z958,z5,z6])],[(0,[z67,z1,z3,z4,z5,z6]),(0,[z8,z131,z23,z4,z60,z6]),(0,[z223,z0,z3,z4,z5,z6]),(0,[z8,z134,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z422,z6]),(0,[z33,z206,z2,z4,z5,z125]),(0,[z8,z2,z4,z6,z37,z955]),(0,[z8,z775,z2,z4,z5,z6])],[(0,[z8,z603,z2,z416,z5,z6]),(0,[z8,z0,z4,z959,z5,z6]),(0,[z8,z0,z2,z4,z5,z579]),(0,[z8,z0,z2,z960,z5,z6])],[(0,[z0,z104,z3,z4,z5,z6]),(0,[z8,z0,z32,z89,z143,z6]),(0,[z8,z0,z2,z4,z579,z37]),(0,[z8,z22,z86,z2,z4,z6]),(0,[z8,z0,z2,z4,z6,z309])],[(0,[z8,z1,z102,z4,z5,z144]),(0,[z8,z23,z2,z414,z5,z6]),(0,[z8,z0,z921,z2,z4,z6]),(0,[z8,z374,z2,z4,z6,z37]),(0,[z33,z0,z2,z4,z387,z125])],[(0,[z31,z1,z3,z4,z5,z6]),(0,[z8,z0,z2,z361,z5,z579]),(0,[z8,z0,z2,z4,z5,z961]),(0,[z8,z0,z962,z4,z5,z6])],[(0,[z1,z2,z96,z4,z5,z125]),(0,[z637,z1,z2,z4,z5,z6]),(0,[z339,z23,z2,z4,z5,z6]),(0,[z8,z639,z239,z4,z5,z6]),(0,[z963,z0,z2,z4,z5,z6])],[(0,[z8,z0,z2,z964,z5,z6]),(0,[z8,z23,z2,z4,z125,z37]),(0,[z8,z0,z2,z4,z6,z319]),(0,[z8,z0,z438,z214,z5,z6]),(0,[z569,z8,z2,z4,z5,z193])],[(0,[z8,z22,z0,z149,z4,z6]),(0,[z116,z23,z2,z47,z5,z6]),(0,[z249,z0,z3,z4,z5,z6]),(0,[z8,z0,z2,z47,z479,z6]),(0,[z8,z0,z512,z138,z5,z6])],[(0,[z124,z1,z2,z146,z5,z6]),(0,[z8,z965,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z444,z37])],[(0,[z189,z1,z2,z4,z6,z125]),(0,[z226,z8,z2,z178,z5,z6]),(0,[z8,z202,z2,z4,z6,z37]),(0,[z8,z0,z2,z702,z143,z6]),(0,[z7,z8,z0,z2,z380,z40])],[(0,[z8,z708,z2,z4,z5,z6]),(0,[z8,z0,z2,z966,z4,z6]),(0,[z8,z86,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z594,z37]),(0,[z8,z0,z2,z6,z728,z61])],[(0,[z8,z0,z2,z4,z6,z967]),(0,[z191,z0,z968,z4,z5,z6]),(0,[z8,z969,z2,z4,z5,z6]),(0,[z8,z93,z3,z4,z5,z6]),(0,[z8,z0,z2,z908,z5,z6]),(0,[z970,z0,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6]),(0,[z8,z22,z23,z2,z4,z37]),(0,[z8,z0,z796,z3,z4,z6]),(0,[z0,z2,z4,z125,z375,z37]),(0,[z971,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z972,z6]),(0,[z973,z0,z2,z4,z5,z6]),(0,[z8,z0,z197,z4,z5,z6]),(0,[z8,z974,z2,z4,z5,z6])],[(0,[z158,z8,z23,z2,z4,z6]),(0,[z0,z3,z516,z4,z5,z6]),(0,[z8,z732,z0,z4,z5,z6]),(0,[z12,z8,z2,z178,z5,z6]),(0,[z975,z0,z2,z4,z5,z6])],[(0,[z8,z335,z0,z3,z4,z6]),(0,[z8,z0,z3,z4,z380,z6]),(0,[z976,z0,z2,z4,z5,z6]),(0,[z8,z110,z2,z4,z179,z6]),(0,[z8,z22,z503,z2,z4,z6])],[(0,[z8,z23,z32,z4,z5,z6]),(0,[z8,z1,z34,z4,z5,z6]),(0,[z8,z1,z2,z873,z5,z6]),(0,[z0,z3,z4,z5,z125,z37]),(0,[z977,z0,z2,z4,z5,z6]),(0,[z8,z0,z4,z978,z5,z6])],[(0,[z580,z1,z2,z4,z5,z6]),(0,[z8,z23,z2,z4,z979,z6]),(0,[z8,z0,z2,z940,z5,z6]),(0,[z8,z421,z25,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z980]),(0,[z8,z816,z86,z2,z4,z6]),(0,[z295,z0,z2,z4,z6,z37]),(0,[z8,z981,z2,z4,z5,z6]),(0,[z8,z22,z0,z94,z4,z6])],[(0,[z1,z2,z357,z4,z5,z6]),(0,[z109,z8,z0,z2,z4,z259]),(0,[z8,z982,z2,z4,z6,z37])],[(0,[z8,z0,z3,z4,z479,z6]),(0,[z8,z0,z3,z138,z5,z6]),(0,[z8,z0,z2,z4,z983,z6]),(0,[z8,z390,z2,z105,z5,z6])],[(0,[z8,z0,z157,z4,z5,z6]),(0,[z8,z0,z190,z4,z6,z37]),(0,[z8,z0,z341,z39,z5,z6]),(0,[z750,z121,z0,z4,z5,z6])],[(0,[z8,z23,z2,z4,z387,z6]),(0,[z8,z545,z3,z4,z5,z6]),(0,[z8,z121,z21,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z984]),(0,[z8,z22,z0,z2,z4,z527]),(0,[z8,z0,z985,z4,z5,z6])],[(0,[z67,z22,z0,z3,z4,z6]),(0,[z208,z0,z3,z4,z5,z6]),(0,[z186,z410,z32,z4,z5,z6]),(0,[z8,z0,z2,z952,z5,z6]),(0,[z8,z110,z2,z4,z6,z696])],[(0,[z8,z0,z986,z4,z5,z6]),(0,[z191,z22,z23,z2,z4,z6]),(0,[z0,z209,z3,z4,z5,z6]),(0,[z109,z8,z32,z4,z163,z6]),(0,[z8,z0,z987,z4,z5,z6]),(0,[z8,z0,z2,z402,z143,z6])],[(0,[z8,z22,z0,z253,z4,z6]),(0,[z8,z0,z612,z4,z5,z246]),(0,[z8,z22,z206,z2,z4,z6]),(0,[z84,z8,z2,z138,z5,z193]),(0,[z8,z22,z121,z0,z4,z6]),(0,[z8,z390,z2,z168,z5,z6])],[(0,[z8,z189,z1,z3,z4,z6]),(0,[z8,z123,z0,z32,z4,z6]),(0,[z8,z988,z0,z2,z4,z6]),(0,[z140,z0,z2,z4,z43,z6]),(0,[z8,z0,z2,z4,z607,z37]),(0,[z8,z9,z2,z4,z6,z37])],[(0,[z8,z1,z558,z4,z5,z6]),(0,[z249,z0,z32,z4,z5,z6]),(0,[z339,z0,z2,z4,z5,z6]),(0,[z8,z0,z34,z4,z387,z6]),(0,[z8,z0,z2,z4,z387,z125]),(0,[z8,z989,z2,z4,z5,z6]),(0,[z8,z0,z2,z89,z143,z6]),(0,[z8,z338,z0,z4,z6,z693])],[(0,[z67,z1,z2,z4,z5,z125]),(0,[z8,z432,z369,z4,z5,z6]),(0,[z8,z110,z2,z4,z254,z6]),(0,[z0,z2,z3,z4,z125,z37]),(0,[z8,z0,z2,z898,z5,z6]),(0,[z8,z0,z103,z414,z5,z6]),(0,[z8,z0,z2,z990,z5,z6])],[(0,[z1,z3,z4,z371,z5,z6]),(0,[z1,z2,z129,z4,z5,z6]),(0,[z116,z0,z2,z47,z5,z6]),(0,[z8,z0,z2,z991,z5,z6]),(0,[z992,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z993]),(0,[z8,z0,z994,z4,z5,z6]),(0,[z8,z9,z2,z4,z306,z6])]],
   [[(0,[z1,z32,z3,z4,z5,z6]),(0,[z8,z1,z253,z4,z5,z6]),(0,[z8,z86,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z995]),(0,[z8,z996,z2,z4,z5,z6]),(0,[z8,z0,z2,z105,z77,z6])],[(0,[z8,z0,z2,z997,z5,z6]),(0,[z8,z0,z2,z4,z934,z6]),(0,[z8,z0,z998,z4,z5,z6]),(0,[z8,z0,z438,z4,z273,z6]),(0,[z8,z0,z2,z4,z358,z37]),(0,[z999,z8,z0,z2,z4,z6]),(0,[z8,z0,z1000,z4,z5,z6])],[(0,[z8,z0,z1001,z4,z5,z6]),(0,[z8,z1,z2,z4,z826,z6]),(0,[z8,z22,z0,z2,z584,z4]),(0,[z295,z0,z2,z4,z325,z6]),(0,[z8,z121,z390,z4,z5,z6]),(0,[z8,z1002,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z1003])],[(0,[z191,z0,z3,z4,z6,z37]),(0,[z8,z792,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z1004,z6])],[(0,[z226,z8,z2,z288,z5,z6]),(0,[z366,z0,z3,z4,z5,z6]),(0,[z8,z22,z211,z2,z4,z6]),(0,[z8,z0,z2,z4,z18,z200]),(0,[z8,z0,z2,z762,z5,z6]),(0,[z8,z22,z0,z4,z365,z6]),(0,[z8,z1005,z2,z4,z5,z6])],[(0,[z1,z3,z4,z179,z5,z6]),(0,[z8,z0,z1006,z4,z5,z6]),(1,[z8,z0,z414,z60,z6]),(0,[z8,z258,z0,z2,z6,z61]),(0,[z8,z22,z0,z2,z4,z329])],[(1,[z1,z3,z4,z6,z37]),(0,[z33,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z193]),(0,[z409,z0,z3,z4,z5,z6]),(0,[z180,z0,z32,z4,z5,z6]),(0,[z8,z0,z1007,z4,z5,z6]),(0,[z931,z0,z4,z5,z6,z193]),(0,[z8,z1008,z2,z4,z5,z6]),(0,[z8,z1009,z2,z4,z5,z6]),(0,[z8,z0,z2,z1010,z5,z6])],[(0,[z8,z0,z32,z4,z5,z6]),(0,[z8,z1,z2,z4,z543,z6]),(0,[z8,z23,z2,z4,z6,z1011]),(0,[z8,z23,z2,z4,z380,z6]),(0,[z0,z2,z902,z4,z5,z6]),(0,[z0,z3,z4,z461,z5,z6]),(0,[z327,z0,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z6,z1012]),(0,[z8,z184,z2,z4,z179,z6]),(0,[z8,z0,z2,z4,z37,z407])],[(0,[z1,z2,z4,z5,z6,z386]),(0,[z8,z203,z2,z4,z5,z6]),(0,[z399,z0,z3,z4,z5,z6]),(0,[z8,z713,z0,z2,z4,z6]),(0,[z8,z0,z160,z4,z6,z37]),(0,[z70,z421,z2,z4,z43,z6])],[(0,[z84,z8,z284,z4,z5,z193])],[(0,[z8,z0,z1013,z4,z5,z6]),(0,[z8,z1014,z0,z4,z5,z6]),(0,[z8,z0,z3,z16,z5,z19]),(0,[z8,z0,z32,z361,z5,z6]),(0,[z8,z49,z182,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z728]),(0,[z8,z0,z2,z922,z4,z37])],[(0,[z8,z23,z2,z4,z479,z6]),(0,[z8,z23,z2,z138,z5,z6]),(0,[z70,z0,z2,z4,z839,z6])],[(0,[z1,z2,z4,z6,z125,z37]),(0,[z8,z1,z2,z4,z847,z6]),(0,[z8,z22,z0,z32,z4,z37]),(0,[z8,z0,z245,z4,z6,z37]),(0,[z8,z250,z21,z4,z5,z6]),(0,[z8,z210,z2,z4,z5,z6]),(0,[z84,z295,z2,z4,z5,z193])],[(0,[z8,z134,z2,z4,z5,z6]),(0,[z115,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z97,z5,z6]),(0,[z158,z8,z0,z32,z4,z6]),(0,[z8,z1,z2,z4,z6,z309])],[(0,[z208,z23,z2,z4,z5,z6]),(0,[z8,z0,z102,z4,z144,z240])],[(0,[z8,z0,z1015,z4,z5,z6]),(0,[z0,z3,z4,z475,z5,z6]),(0,[z8,z0,z1016,z4,z5,z6]),(0,[z8,z0,z1017,z4,z5,z6]),(0,[z109,z8,z202,z2,z4,z6]),(0,[z8,z503,z2,z168,z5,z6])]],
   [[(0,[z8,z0,z32,z1018,z5,z6]),(0,[z8,z100,z0,z39,z155,z6]),(0,[z1019,z0,z2,z4,z5,z6])],[(0,[z8,z23,z373,z4,z5,z6]),(0,[z410,z2,z4,z5,z6,z125]),(0,[z8,z0,z2,z4,z6,z1020]),(0,[z8,z0,z32,z4,z5,z579]),(0,[z8,z0,z1021,z4,z5,z6])],[(0,[z8,z1,z521,z4,z5,z6]),(0,[z8,z0,z2,z1022,z5,z6]),(0,[z67,z335,z0,z2,z4,z18]),(0,[z1023,z0,z2,z4,z5,z6]),(0,[z1024,z0,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z554]),(0,[z8,z22,z0,z443,z4,z6]),(0,[z339,z0,z197,z4,z5,z6])],[(0,[z8,z0,z1025,z4,z5,z6]),(0,[z8,z0,z2,z4,z629,z37]),(0,[z8,z0,z438,z4,z6,z37])],[(0,[z249,z0,z2,z4,z5,z6]),(0,[z67,z206,z2,z4,z5,z6]),(0,[z8,z1026,z0,z2,z4,z6]),(0,[z98,z8,z0,z4,z37,z99])],[(0,[z502,z1,z3,z4,z5,z6]),(0,[z8,z0,z1027,z4,z5,z6]),(0,[z8,z0,z2,z4,z1028,z6])],[(0,[z1,z3,z218,z4,z5,z6]),(0,[z8,z1029,z0,z2,z4,z6]),(0,[z8,z0,z2,z4,z5,z1030]),(0,[z8,z0,z32,z4,z6,z319]),(0,[z333,z0,z2,z47,z5,z6]),(0,[z8,z0,z2,z248,z251,z6]),(0,[z8,z0,z2,z1031,z5,z6])],[(0,[z8,z86,z2,z4,z5,z6]),(0,[z8,z23,z4,z5,z6,z1032])],[(0,[z8,z388,z115,z4,z5,z6]),(0,[z8,z0,z189,z32,z4,z6]),(0,[z8,z93,z2,z4,z5,z6]),(0,[z8,z0,z3,z4,z125,z37]),(0,[z8,z0,z2,z68,z53,z6]),(0,[z8,z1033,z2,z4,z5,z6])],[(0,[z8,z23,z284,z4,z5,z6]),(0,[z1034,z0,z2,z4,z5,z6])],[(0,[z502,z8,z182,z4,z5,z6]),(0,[z8,z1035,z2,z4,z5,z6]),(0,[z484,z255,z2,z4,z5,z6]),(0,[z327,z0,z21,z4,z5,z6]),(0,[z98,z8,z0,z4,z5,z99])],[(0,[z189,z1,z2,z3,z4,z6]),(0,[z8,z148,z1,z2,z4,z6]),(0,[z409,z23,z2,z4,z5,z6]),(0,[z8,z0,z1036,z4,z5,z6]),(0,[z8,z1037,z0,z4,z5,z6]),(0,[z8,z100,z0,z39,z6,z37]),(0,[z8,z0,z2,z4,z380,z6]),(0,[z8,z0,z2,z4,z640,z37])],[(0,[z8,z1,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z1038,z6]),(0,[z237,z0,z3,z4,z6,z37]),(0,[z122,z0,z3,z4,z5,z6]),(0,[z120,z8,z0,z4,z5,z173]),(0,[z93,z2,z4,z5,z6,z125]),(0,[z0,z2,z4,z5,z839,z6]),(0,[z8,z2,z4,z179,z716,z6]),(0,[z7,z339,z0,z2,z5,z40])],[(0,[z8,z0,z4,z5,z6,z1039]),(0,[z8,z0,z2,z4,z1040,z6]),(0,[z8,z22,z0,z2,z4,z562]),(0,[z8,z0,z94,z4,z6,z37])],[(0,[z0,z3,z4,z5,z6,z290]),(0,[z8,z22,z0,z104,z4,z6]),(1,[z8,z732,z4,z5,z6]),(0,[z8,z0,z1041,z4,z5,z6]),(0,[z8,z0,z4,z5,z751,z6]),(0,[z167,z0,z2,z4,z77,z6])],[(0,[z8,z0,z2,z4,z386,z37]),(0,[z8,z23,z2,z16,z5,z19]),(0,[z8,z0,z2,z4,z479,z6]),(0,[z8,z0,z1042,z4,z5,z6])]],
   [[(0,[z8,z0,z2,z1043,z5,z6]),(0,[z8,z211,z2,z4,z6,z37]),(0,[z8,z0,z94,z4,z306,z6]),(0,[z8,z0,z1044,z4,z5,z6])],[(0,[z8,z545,z2,z4,z5,z6]),(0,[z8,z117,z2,z4,z396,z6]),(0,[z8,z0,z2,z47,z5,z91]),(0,[z400,z0,z2,z47,z5,z6]),(1,[z8,z2,z4,z5,z961]),(0,[z8,z101,z0,z270,z5,z6]),(0,[z8,z0,z2,z89,z672,z6]),(0,[z8,z210,z197,z4,z5,z6])],[(0,[z1,z3,z4,z5,z425,z6]),(0,[z1,z3,z4,z5,z19,z6]),(0,[z8,z22,z0,z2,z343,z4]),(0,[z101,z327,z0,z4,z5,z6]),(0,[z8,z0,z4,z6,z1045,z37]),(0,[z8,z0,z2,z424,z6,z72])],[(0,[z67,z93,z2,z4,z5,z6]),(0,[z8,z22,z0,z147,z4,z6]),(0,[z49,z327,z2,z4,z5,z6])],[(0,[z8,z1,z2,z89,z143,z6]),(0,[z8,z22,z1,z2,z96,z4]),(0,[z8,z31,z0,z3,z6,z61]),(0,[z8,z0,z1046,z4,z5,z6])],[(0,[z8,z1047,z2,z4,z5,z6]),(0,[z8,z0,z4,z365,z6,z37])],[(0,[z8,z23,z25,z4,z5,z6]),(0,[z8,z0,z3,z4,z387,z6]),(0,[z8,z348,z2,z68,z5,z6]),(0,[z8,z376,z0,z2,z5,z40])],[(0,[z8,z0,z2,z4,z648,z37]),(0,[z8,z0,z2,z1018,z5,z6]),(0,[z8,z0,z32,z414,z5,z6]),(0,[z8,z0,z2,z4,z1048,z6]),(0,[z8,z1049,z2,z4,z5,z6]),(0,[z8,z565,z0,z39,z5,z6])],[(0,[z158,z8,z2,z4,z152,z6]),(0,[z8,z1050,z0,z2,z4,z6]),(0,[z8,z0,z768,z39,z5,z6])],[(0,[z1,z3,z89,z4,z5,z6]),(0,[z339,z0,z32,z4,z5,z6]),(0,[z8,z1051,z0,z2,z4,z6]),(0,[z108,z8,z0,z4,z5,z99]),(0,[z8,z0,z1052,z4,z6,z37])],[(0,[z8,z1053,z1,z4,z5,z6]),(0,[z8,z1054,z23,z4,z5,z6]),(0,[z8,z0,z32,z4,z125,z37]),(0,[z8,z0,z245,z4,z5,z259]),(0,[z8,z1055,z2,z4,z5,z6]),(0,[z8,z0,z1056,z4,z5,z6])],[(0,[z52,z1,z450,z4,z5,z6]),(0,[z281,z0,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z1057,z6]),(0,[z116,z0,z32,z47,z5,z6]),(0,[z33,z0,z2,z4,z125,z37]),(0,[z8,z0,z2,z1058,z5,z6]),(0,[z1059,z0,z2,z4,z5,z6]),(0,[z376,z0,z2,z4,z6,z37])],[(0,[z1,z3,z4,z5,z6,z37]),(0,[z8,z0,z2,z4,z5,z1060]),(0,[z8,z0,z3,z4,z5,z91]),(0,[z116,z203,z2,z47,z5,z6]),(0,[z8,z0,z1061,z4,z5,z6]),(0,[z8,z1062,z0,z2,z4,z6]),(0,[z1063,z0,z2,z4,z5,z6])],[(0,[z8,z0,z1064,z4,z5,z6]),(0,[z8,z0,z34,z187,z5,z6]),(0,[z8,z1065,z0,z2,z4,z6]),(0,[z8,z0,z4,z5,z6,z1066])],[(0,[z1,z2,z4,z5,z125,z37]),(0,[z456,z1,z2,z4,z5,z6]),(0,[z8,z22,z23,z32,z4,z6]),(0,[z8,z639,z21,z4,z5,z6]),(0,[z8,z20,z512,z4,z5,z6]),(0,[z376,z0,z2,z4,z306,z6]),(0,[z339,z210,z2,z4,z5,z6]),(0,[z8,z0,z4,z5,z6,z1067])],[(0,[z8,z45,z239,z4,z5,z6]),(0,[z8,z0,z2,z4,z324,z1068]),(0,[z295,z0,z1069,z4,z5,z6]),(0,[z8,z22,z1070,z2,z4,z6])]],
   [[(0,[z8,z289,z2,z4,z254,z6]),(0,[z8,z0,z2,z4,z5,z1071]),(0,[z8,z1072,z0,z2,z4,z6]),(0,[z8,z211,z160,z4,z5,z6]),(0,[z8,z0,z1073,z4,z5,z6]),(0,[z8,z0,z197,z4,z380,z6])],[(0,[z8,z1074,z1,z2,z4,z6]),(0,[z8,z22,z0,z3,z4,z6]),(0,[z8,z637,z0,z2,z6,z61])],[(0,[z67,z0,z2,z4,z5,z648]),(0,[z8,z22,z117,z2,z4,z6])],[(0,[z295,z0,z2,z248,z5,z6]),(0,[z8,z0,z1075,z4,z5,z6]),(0,[z8,z0,z2,z16,z5,z19])],[(0,[z8,z101,z23,z183,z5,z6]),(0,[z8,z203,z32,z4,z5,z6]),(0,[z8,z22,z0,z34,z4,z6]),(0,[z8,z258,z0,z39,z5,z6]),(0,[z8,z131,z0,z4,z751,z6]),(0,[z8,z22,z0,z730,z4,z6])],[(0,[z0,z1,z157,z4,z5,z6]),(0,[z8,z206,z32,z4,z5,z6]),(0,[z8,z335,z0,z2,z4,z37]),(0,[z472,z0,z2,z105,z5,z6]),(1,[z8,z0,z443,z6,z61]),(0,[z376,z0,z2,z4,z5,z19])],[(0,[z8,z0,z2,z1076,z5,z6])],[(0,[z1,z2,z3,z4,z6,z37]),(0,[z8,z1077,z0,z4,z5,z6]),(0,[z8,z0,z2,z248,z6,z37]),(0,[z8,z2,z4,z5,z6,z1078])],[(0,[z8,z0,z2,z4,z951,z6]),(0,[z8,z210,z32,z4,z5,z6])],[(0,[z67,z1,z32,z4,z5,z6]),(0,[z8,z0,z1079,z4,z5,z6]),(0,[z8,z134,z32,z4,z5,z6])],[(0,[z8,z0,z1080,z4,z5,z6]),(0,[z70,z23,z2,z4,z43,z6]),(0,[z8,z0,z25,z4,z5,z6]),(0,[z8,z0,z2,z4,z1081,z6]),(0,[z1082,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z1083]),(0,[z472,z0,z2,z168,z5,z6])],[(0,[z249,z1,z2,z4,z5,z6]),(0,[z665,z0,z2,z146,z5,z6]),(0,[z70,z323,z0,z2,z4,z6]),(0,[z333,z0,z2,z4,z5,z125]),(0,[z8,z20,z2,z4,z11,z139])],[(0,[z174,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z1084,z6]),(0,[z8,z0,z2,z405,z6,z37]),(0,[z8,z1085,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z774,z6])],[(0,[z8,z0,z660,z4,z97,z6]),(0,[z8,z0,z25,z361,z5,z6]),(1,[z8,z2,z762,z5,z6]),(0,[z8,z20,z2,z4,z5,z107]),(0,[z339,z0,z2,z4,z380,z6]),(0,[z8,z0,z1086,z4,z5,z6])],[(0,[z502,z1,z2,z4,z5,z6]),(0,[z412,z1,z3,z4,z5,z6]),(0,[z8,z0,z2,z414,z5,z6]),(0,[z8,z31,z0,z2,z379,z6])],[(0,[z8,z0,z2,z4,z1087,z6])]],
   [[(0,[z189,z1,z3,z4,z5,z6])],[(0,[z8,z23,z2,z4,z5,z91]),(0,[z8,z0,z2,z4,z125,z37]),(0,[z8,z0,z1088,z4,z5,z6]),(0,[z8,z1089,z0,z2,z4,z6]),(0,[z8,z2,z4,z5,z961,z193])],[(0,[z1,z3,z183,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z1090]),(0,[z8,z410,z2,z4,z6,z37]),(0,[z8,z732,z2,z4,z5,z6]),(0,[z8,z227,z0,z4,z6,z37]),(0,[z8,z0,z4,z5,z6,z1045]),(0,[z8,z0,z39,z60,z6,z61]),(0,[z8,z0,z4,z5,z144,z845]),(0,[z8,z0,z1091,z4,z5,z6])],[(0,[z8,z1092,z32,z4,z5,z6]),(0,[z116,z0,z2,z47,z479,z6]),(0,[z8,z0,z2,z89,z6,z728])],[(0,[z180,z1,z2,z4,z5,z6]),(0,[z8,z93,z32,z4,z5,z6]),(0,[z628,z0,z2,z47,z5,z6]),(0,[z8,z0,z25,z4,z5,z579]),(0,[z8,z1093,z2,z4,z5,z6]),(0,[z7,z8,z0,z94,z5,z40]),(0,[z8,z0,z1094,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6]),(0,[z1,z32,z4,z5,z6,z125]),(0,[z8,z335,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z6,z938]),(0,[z8,z0,z2,z1095,z5,z6]),(0,[z8,z0,z1096,z4,z5,z6]),(0,[z8,z23,z104,z4,z5,z6]),(0,[z8,z374,z438,z4,z5,z6]),(0,[z8,z0,z1097,z4,z5,z6]),(0,[z8,z0,z1098,z4,z5,z6]),(0,[z8,z0,z2,z248,z325,z6]),(0,[z8,z0,z2,z4,z6,z1099]),(0,[z8,z1100,z0,z2,z4,z6])],[(0,[z199,z0,z32,z4,z5,z6]),(0,[z295,z22,z0,z2,z4,z6]),(0,[z8,z22,z0,z102,z4,z144])],[(0,[z8,z0,z2,z1101,z5,z6]),(0,[z67,z255,z3,z4,z5,z6]),(0,[z256,z0,z3,z4,z5,z6]),(0,[z8,z0,z32,z4,z380,z6]),(0,[z8,z0,z1102,z4,z5,z6])],[(0,[z666,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z361,z5,z6]),(0,[z1,z2,z4,z470,z5,z6]),(0,[z8,z31,z0,z443,z6,z61])],[(0,[z0,z412,z3,z4,z5,z6]),(0,[z389,z1,z2,z4,z5,z6]),(0,[z8,z23,z2,z4,z6,z240]),(0,[z8,z0,z3,z105,z5,z6]),(0,[z8,z148,z0,z32,z4,z6]),(0,[z8,z24,z218,z365,z5,z6]),(0,[z8,z0,z2,z4,z37,z404]),(0,[z8,z1103,z0,z2,z4,z6])],[(0,[z8,z0,z1104,z4,z5,z6]),(0,[z8,z0,z2,z4,z1105,z6]),(0,[z8,z0,z4,z751,z60,z6])],[(0,[z8,z0,z2,z4,z979,z6]),(0,[z8,z0,z2,z1106,z5,z6]),(0,[z8,z0,z32,z4,z479,z6]),(0,[z8,z0,z32,z138,z5,z6]),(0,[z8,z0,z2,z4,z1107,z6]),(0,[z8,z0,z1108,z4,z5,z6])],[(0,[z158,z23,z1,z2,z4,z6]),(0,[z8,z206,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z1109,z6]),(0,[z8,z0,z612,z4,z5,z144]),(0,[z8,z203,z2,z4,z479,z6]),(0,[z116,z0,z2,z940,z5,z6]),(0,[z8,z0,z2,z4,z6,z1110]),(0,[z8,z390,z2,z4,z6,z37]),(0,[z8,z210,z2,z4,z380,z6])],[(0,[z8,z545,z32,z4,z5,z6]),(0,[z8,z0,z34,z214,z5,z6]),(0,[z84,z8,z2,z4,z5,z961]),(0,[z8,z503,z2,z105,z5,z6]),(0,[z8,z0,z2,z443,z6,z61])],[(0,[z8,z0,z3,z168,z5,z6]),(0,[z0,z2,z47,z5,z125,z40]),(1,[z8,z0,z39,z155,z6])],[(0,[z8,z1,z2,z4,z5,z579]),(0,[z628,z0,z3,z4,z5,z6]),(0,[z8,z0,z2,z1111,z5,z6]),(0,[z8,z0,z2,z4,z387,z6]),(0,[z1112,z0,z2,z4,z5,z6])]],
   [[(0,[z67,z1,z2,z4,z5,z6]),(0,[z8,z0,z3,z1113,z5,z6]),(0,[z8,z348,z2,z4,z6,z37]),(0,[z8,z0,z39,z5,z6,z621])],[(0,[z30,z1,z2,z4,z5,z6]),(0,[z95,z8,z3,z178,z5,z6]),(0,[z8,z22,z93,z2,z4,z6]),(0,[z8,z0,z512,z4,z6,z37])],[(0,[z158,z186,z1,z2,z4,z6]),(0,[z8,z0,z2,z4,z1114,z6]),(0,[z8,z0,z2,z4,z6,z1115])],[(0,[z8,z23,z129,z4,z5,z6]),(0,[z8,z0,z1116,z4,z5,z6]),(0,[z8,z0,z878,z4,z5,z6]),(0,[z8,z0,z2,z4,z1117,z6])],[(0,[z8,z1,z2,z4,z6,z319]),(0,[z366,z1,z2,z4,z5,z6]),(0,[z109,z8,z2,z4,z377,z6]),(0,[z8,z0,z1118,z4,z5,z6]),(0,[z8,z22,z0,z438,z4,z6]),(0,[z8,z0,z1119,z4,z5,z6]),(0,[z8,z1120,z2,z4,z5,z6]),(0,[z8,z0,z102,z4,z5,z845])],[(1,[z22,z1,z3,z4,z6]),(0,[z8,z100,z1,z39,z5,z6]),(0,[z8,z0,z2,z4,z5,z91]),(0,[z8,z0,z393,z4,z6,z37]),(0,[z167,z22,z0,z2,z4,z6]),(0,[z8,z1070,z2,z4,z5,z6])],[(0,[z8,z0,z3,z187,z5,z6]),(0,[z186,z0,z902,z4,z5,z6]),(0,[z8,z0,z190,z4,z5,z324]),(0,[z8,z1121,z0,z4,z5,z6]),(0,[z1122,z0,z2,z4,z5,z6]),(0,[z8,z390,z102,z4,z5,z6])],[(0,[z22,z0,z32,z3,z4,z6]),(0,[z310,z8,z0,z4,z60,z6]),(0,[z167,z390,z2,z4,z5,z6])],[(0,[z412,z1,z2,z4,z5,z125]),(0,[z8,z1,z2,z966,z4,z6]),(0,[z8,z45,z369,z4,z5,z6]),(0,[z8,z421,z2,z68,z5,z6]),(0,[z8,z0,z1123,z4,z5,z6]),(0,[z8,z1124,z0,z4,z5,z6]),(0,[z8,z22,z0,z817,z4,z6])],[(0,[z0,z3,z4,z5,z6,z550]),(0,[z8,z0,z104,z4,z5,z6]),(0,[z351,z0,z3,z4,z5,z6]),(0,[z8,z0,z2,z1125,z5,z6])],[(0,[z8,z189,z2,z4,z10,z6]),(0,[z8,z1,z197,z4,z5,z6]),(0,[z8,z23,z147,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z552]),(0,[z249,z545,z2,z4,z5,z6]),(0,[z8,z1126,z2,z4,z5,z6]),(0,[z8,z1092,z2,z4,z5,z6]),(0,[z33,z0,z2,z187,z5,z125]),(0,[z8,z0,z2,z1127,z5,z6]),(0,[z8,z1128,z0,z2,z4,z6])],[(0,[z8,z23,z149,z4,z5,z6]),(0,[z8,z164,z0,z2,z4,z259]),(0,[z8,z0,z1129,z4,z5,z6]),(0,[z295,z30,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z6,z1130]),(0,[z67,z0,z2,z4,z18,z319]),(0,[z8,z0,z2,z4,z1131,z6]),(0,[z484,z0,z2,z4,z251,z6]),(0,[z8,z0,z2,z4,z75,z37]),(0,[z376,z0,z2,z16,z5,z6])],[(0,[z8,z0,z2,z4,z5,z1132]),(0,[z472,z0,z4,z5,z6,z99]),(0,[z8,z0,z443,z4,z6,z37])],[(0,[z95,z1,z3,z4,z5,z6]),(0,[z8,z23,z2,z105,z5,z6]),(0,[z8,z0,z2,z4,z6,z1011]),(0,[z8,z0,z4,z1133,z5,z6]),(0,[z8,z1134,z2,z4,z5,z6]),(0,[z8,z22,z374,z2,z4,z6]),(0,[z8,z0,z39,z5,z155,z6])],[(0,[z8,z0,z32,z16,z5,z19]),(0,[z8,z0,z4,z5,z144,z177]),(0,[z8,z0,z512,z4,z325,z6])]],
   [[(0,[z8,z0,z450,z4,z6,z37]),(0,[z23,z189,z1,z2,z4,z6]),(0,[z1,z3,z4,z5,z559,z6]),(0,[z8,z0,z2,z4,z53,z259]),(0,[z1135,z8,z0,z2,z4,z6]),(0,[z8,z0,z2,z414,z60,z6])],[(0,[z8,z1,z157,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z135]),(0,[z8,z101,z0,z768,z5,z6]),(0,[z8,z390,z4,z5,z6,z99]),(0,[z8,z22,z0,z2,z1136,z6])],[(0,[z8,z0,z1137,z4,z5,z6]),(0,[z8,z0,z2,z138,z5,z6])],[(0,[z8,z23,z2,z168,z5,z6])],[(0,[z8,z348,z245,z4,z5,z6]),(0,[z8,z0,z34,z4,z273,z6]),(0,[z8,z121,z0,z4,z5,z6]),(0,[z8,z9,z94,z4,z5,z6])],[(0,[z1,z3,z146,z4,z5,z6]),(0,[z8,z1,z2,z414,z5,z6]),(0,[z339,z0,z1138,z4,z5,z6]),(1,[z8,z0,z2,z922,z4])],[(0,[z8,z0,z3,z4,z1139,z6])],[(0,[z8,z22,z0,z450,z4,z6]),(0,[z22,z1,z2,z4,z6,z125]),(0,[z339,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z1140]),(0,[z8,z0,z129,z4,z5,z6]),(0,[z8,z164,z0,z2,z4,z37]),(0,[z8,z0,z2,z4,z1141,z6])],[(0,[z8,z1,z2,z4,z125,z37]),(0,[z70,z0,z3,z4,z43,z6]),(0,[z8,z0,z373,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z259]),(0,[z8,z0,z2,z4,z6,z1142]),(0,[z8,z2,z4,z5,z6,z961]),(0,[z8,z1143,z2,z4,z5,z6])],[(0,[z116,z1,z2,z47,z5,z6]),(0,[z1144,z8,z1,z2,z5,z6])],[(0,[z23,z1,z2,z4,z6,z37]),(0,[z818,z8,z0,z2,z4,z6]),(0,[z8,z0,z2,z4,z5,z1145]),(0,[z249,z45,z21,z4,z5,z6])],[(0,[z186,z23,z32,z4,z5,z6]),(0,[z8,z23,z2,z187,z5,z6]),(0,[z8,z0,z1146,z4,z5,z6]),(0,[z167,z503,z2,z4,z5,z6]),(0,[z8,z741,z2,z4,z5,z6])],[(0,[z8,z23,z189,z2,z4,z6]),(0,[z8,z1,z2,z1095,z5,z6]),(0,[z8,z0,z2,z146,z479,z6]),(0,[z8,z0,z2,z4,z259,z37]),(0,[z8,z828,z0,z2,z4,z6]),(0,[z98,z8,z503,z4,z5,z99])],[(0,[z8,z1147,z2,z4,z5,z6]),(0,[z8,z110,z0,z2,z4,z259]),(0,[z8,z1148,z2,z4,z5,z6])],[(0,[z351,z23,z2,z4,z5,z6]),(0,[z8,z0,z4,z5,z6,z1032]),(0,[z8,z78,z2,z4,z6,z37]),(0,[z8,z0,z2,z1149,z5,z6]),(0,[z8,z348,z2,z4,z5,z259])],[(0,[z809,z8,z1,z2,z4,z6]),(0,[z327,z2,z21,z4,z5,z6]),(0,[z151,z8,z2,z4,z5,z193])]],
   [[(0,[z158,z8,z1,z3,z4,z6]),(0,[z8,z669,z2,z137,z5,z6]),(0,[z8,z148,z23,z2,z4,z6]),(0,[z0,z3,z4,z5,z6,z571]),(0,[z8,z0,z284,z4,z5,z6]),(0,[z8,z793,z0,z4,z6,z37])],[(0,[z8,z1,z32,z4,z5,z6]),(0,[z176,z0,z2,z4,z6,z375]),(0,[z339,z1150,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z1151,z6]),(0,[z8,z0,z2,z4,z642,z37]),(0,[z472,z49,z0,z4,z5,z6]),(0,[z8,z576,z182,z4,z5,z6]),(0,[z8,z0,z102,z4,z5,z342]),(0,[z376,z9,z2,z4,z5,z6]),(0,[z8,z0,z4,z6,z37,z1066])],[(0,[z8,z335,z0,z32,z4,z6]),(0,[z8,z1152,z0,z2,z4,z6]),(0,[z182,z327,z0,z4,z5,z6]),(0,[z8,z0,z512,z4,z251,z6]),(0,[z8,z22,z0,z2,z4,z236])],[(0,[z116,z1,z3,z4,z5,z6]),(0,[z1153,z8,z0,z2,z4,z6]),(0,[z8,z45,z21,z4,z5,z6]),(0,[z8,z0,z1154,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z37])],[(0,[z23,z3,z4,z5,z6,z125]),(0,[z8,z0,z3,z68,z5,z6]),(0,[z481,z8,z0,z2,z5,z40]),(0,[z8,z24,z2,z287,z5,z6]),(0,[z8,z0,z1155,z4,z5,z6])],[(0,[z0,z242,z3,z4,z5,z6]),(0,[z8,z0,z3,z214,z5,z6]),(0,[z8,z0,z34,z4,z6,z37]),(0,[z1156,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z922,z4,z58]),(0,[z8,z22,z0,z1157,z4,z6])],[(0,[z8,z1158,z2,z4,z5,z6]),(0,[z8,z31,z1,z2,z6,z61]),(0,[z136,z1,z2,z4,z5,z6]),(0,[z158,z8,z348,z2,z4,z6]),(0,[z8,z0,z3,z4,z6,z240]),(0,[z8,z0,z2,z168,z5,z6]),(0,[z8,z1159,z2,z4,z5,z6]),(0,[z8,z0,z2,z105,z543,z6]),(0,[z8,z207,z2,z4,z6,z57])],[(0,[z8,z0,z16,z365,z5,z6]),(0,[z295,z2,z4,z5,z6,z193])],[(0,[z20,z1,z3,z4,z5,z6]),(0,[z8,z22,z23,z2,z96,z4]),(0,[z8,z0,z190,z4,z396,z6]),(0,[z116,z0,z2,z47,z5,z91]),(0,[z8,z0,z1160,z4,z5,z6]),(0,[z8,z0,z102,z4,z144,z37])],[(0,[z174,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z1161,z6]),(0,[z23,z599,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z550,z37]),(0,[z0,z32,z902,z4,z5,z6]),(0,[z8,z22,z421,z2,z4,z6]),(0,[z33,z0,z2,z214,z5,z125]),(0,[z95,z8,z2,z178,z5,z6]),(0,[z8,z22,z9,z2,z4,z6])],[(0,[z8,z0,z32,z4,z387,z6]),(0,[z8,z22,z100,z0,z39,z6])],[(0,[z8,z227,z1,z4,z5,z6]),(0,[z167,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z168,z543,z6])],[(0,[z8,z211,z393,z4,z5,z6]),(0,[z8,z206,z2,z4,z387,z6]),(0,[z0,z2,z4,z18,z125,z37]),(0,[z484,z0,z2,z4,z6,z37]),(0,[z376,z22,z0,z2,z4,z6]),(0,[z8,z0,z2,z5,z6,z752])],[(0,[z1,z3,z3,z4,z5,z6]),(0,[z8,z0,z3,z4,z251,z6]),(0,[z382,z0,z32,z4,z5,z6]),(0,[z8,z45,z390,z4,z5,z6]),(0,[z1162,z0,z2,z4,z5,z6])],[(0,[z1,z3,z4,z53,z5,z6]),(0,[z0,z1,z2,z4,z125,z37]),(0,[z8,z23,z4,z5,z6,z221]),(0,[z186,z0,z32,z4,z5,z6]),(0,[z8,z255,z3,z4,z5,z6]),(0,[z691,z0,z3,z4,z5,z6]),(0,[z8,z0,z843,z4,z5,z6]),(0,[z8,z1163,z2,z4,z5,z6])]],
   [[(0,[z8,z0,z189,z2,z4,z6]),(0,[z619,z1,z2,z4,z5,z6]),(0,[z22,z327,z0,z2,z4,z6]),(0,[z8,z1164,z0,z2,z4,z6])],[(0,[z7,z8,z0,z3,z5,z40]),(0,[z8,z0,z32,z4,z5,z91]),(0,[z8,z0,z2,z4,z1165,z6]),(0,[z8,z1166,z2,z4,z5,z6]),(0,[z8,z31,z0,z558,z6,z61])],[(0,[z708,z0,z2,z4,z5,z6]),(0,[z502,z8,z573,z4,z5,z6]),(0,[z8,z203,z2,z4,z5,z91]),(0,[z8,z421,z2,z4,z6,z37]),(0,[z8,z22,z202,z2,z4,z6])],[(0,[z8,z0,z1167,z4,z5,z6]),(0,[z8,z574,z0,z183,z5,z6]),(0,[z8,z0,z1168,z4,z5,z6]),(0,[z484,z0,z1169,z4,z5,z6]),(0,[z84,z8,z2,z4,z251,z193]),(0,[z8,z0,z1170,z4,z5,z6])],[(0,[z8,z22,z1,z2,z4,z6]),(0,[z199,z1,z2,z4,z5,z6]),(0,[z8,z1171,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z1172]),(0,[z8,z45,z597,z4,z5,z6]),(0,[z8,z22,z0,z284,z4,z6])],[(0,[z8,z1,z2,z4,z380,z6])],[(0,[z8,z1,z2,z4,z1038,z6]),(0,[z8,z0,z102,z4,z5,z398]),(0,[z8,z0,z1138,z4,z5,z6]),(0,[z8,z0,z2,z4,z1173,z6])],[(0,[z8,z110,z202,z2,z4,z6]),(0,[z8,z0,z1174,z4,z5,z6])],[],[(0,[z70,z1,z3,z4,z5,z6]),(0,[z131,z1,z3,z4,z5,z6]),(0,[z8,z1,z2,z4,z479,z6]),(0,[z8,z1,z2,z138,z5,z6]),(0,[z8,z117,z3,z4,z5,z6]),(0,[z8,z449,z0,z3,z4,z6]),(0,[z638,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z1175,z6])],[(0,[z8,z0,z1176,z4,z5,z6]),(0,[z8,z23,z2,z68,z5,z6]),(0,[z8,z202,z521,z4,z5,z6]),(0,[z8,z0,z836,z4,z6,z37]),(0,[z835,z8,z2,z4,z6,z37])],[(0,[z8,z0,z968,z4,z5,z6]),(0,[z8,z23,z3,z4,z6,z37]),(0,[z8,z23,z2,z214,z5,z6]),(0,[z8,z0,z2,z4,z1177,z6]),(0,[z484,z0,z2,z4,z325,z6]),(0,[z8,z0,z4,z1178,z5,z6]),(0,[z472,z0,z2,z4,z6,z37]),(0,[z8,z1179,z2,z4,z5,z6])],[(0,[z8,z1180,z2,z4,z5,z6]),(0,[z116,z0,z373,z47,z5,z6]),(0,[z8,z22,z0,z2,z214,z6]),(0,[z8,z49,z199,z4,z5,z6]),(0,[z167,z821,z2,z4,z5,z6])],[(0,[z158,z67,z1,z2,z4,z6]),(0,[z158,z8,z189,z2,z4,z6]),(0,[z23,z327,z2,z4,z5,z6]),(0,[z8,z0,z3,z4,z273,z6]),(0,[z8,z0,z414,z5,z60,z6])],[(0,[z8,z0,z2,z89,z459,z6]),(0,[z8,z0,z1181,z4,z5,z6]),(0,[z8,z22,z0,z558,z4,z6])],[(0,[z67,z22,z1,z2,z4,z6]),(0,[z8,z0,z2,z4,z557,z37]),(0,[z186,z86,z2,z4,z5,z6]),(0,[z8,z0,z1182,z4,z5,z6]),(0,[z295,z0,z738,z4,z5,z6])]],
   [[(0,[z8,z0,z2,z214,z5,z125]),(0,[z8,z0,z2,z4,z125,z200]),(0,[z8,z49,z390,z4,z5,z6]),(0,[z295,z0,z512,z4,z5,z6]),(0,[z8,z0,z512,z248,z5,z6])],[(0,[z0,z32,z3,z4,z5,z6]),(0,[z70,z0,z2,z4,z43,z6]),(0,[z33,z0,z2,z4,z273,z125])],[(0,[z8,z1183,z23,z4,z5,z6]),(0,[z237,z78,z3,z4,z5,z6]),(0,[z8,z1184,z0,z2,z4,z6]),(0,[z8,z1185,z2,z4,z5,z6]),(0,[z8,z0,z2,z1186,z5,z6]),(0,[z8,z1150,z2,z4,z5,z6])],[(0,[z1,z2,z549,z4,z5,z6]),(0,[z8,z0,z1187,z4,z5,z6]),(0,[z8,z23,z2,z4,z251,z6]),(0,[z84,z484,z2,z4,z5,z193]),(0,[z376,z0,z94,z4,z5,z6])],[(0,[z186,z1,z3,z4,z5,z6]),(0,[z691,z23,z2,z4,z5,z6]),(0,[z8,z202,z3,z4,z5,z6]),(0,[z8,z0,z3,z4,z155,z6]),(0,[z70,z0,z2,z361,z43,z6]),(0,[z1188,z0,z2,z4,z5,z6]),(0,[z8,z0,z1189,z4,z5,z6]),(0,[z8,z0,z789,z4,z5,z6])],[(0,[z1,z612,z3,z4,z5,z6]),(0,[z281,z1,z3,z4,z5,z6]),(0,[z22,z1,z2,z3,z4,z6]),(0,[z1,z2,z4,z5,z6,z552]),(0,[z8,z0,z2,z4,z1190,z6]),(0,[z8,z22,z0,z32,z96,z4]),(0,[z8,z203,z373,z4,z5,z6]),(0,[z8,z0,z521,z4,z6,z37]),(0,[z8,z86,z104,z4,z5,z6]),(0,[z8,z0,z2,z4,z1191,z6]),(0,[z472,z0,z102,z4,z5,z6]),(0,[z167,z0,z2,z4,z543,z6])],[(0,[z8,z0,z2,z4,z396,z324]),(0,[z8,z421,z245,z4,z5,z6]),(0,[z8,z1192,z2,z4,z5,z6])],[(0,[z8,z1,z284,z4,z5,z6]),(0,[z8,z591,z0,z39,z5,z6]),(0,[z8,z0,z2,z4,z128,z37]),(0,[z8,z0,z4,z5,z6,z1193]),(0,[z8,z2,z4,z5,z11,z961]),(0,[z8,z1194,z2,z4,z5,z6])],[(0,[z8,z327,z21,z4,z5,z6]),(0,[z8,z0,z2,z4,z1195,z6]),(0,[z472,z1196,z2,z4,z5,z6])],[(0,[z8,z0,z1197,z4,z5,z6]),(0,[z98,z1,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z557]),(0,[z8,z0,z2,z4,z479,z91]),(0,[z8,z0,z2,z4,z6,z1068]),(0,[z8,z0,z2,z532,z6,z61])],[(0,[z1,z2,z369,z4,z5,z6]),(0,[z8,z335,z23,z2,z4,z6]),(0,[z8,z0,z1198,z4,z5,z6]),(0,[z8,z21,z4,z5,z6,z698]),(0,[z84,z8,z22,z2,z4,z193]),(0,[z8,z1199,z2,z4,z5,z6])],[(0,[z399,z1,z2,z4,z5,z6]),(0,[z295,z0,z3,z4,z5,z6]),(0,[z8,z0,z885,z4,z5,z6]),(0,[z8,z117,z32,z4,z5,z6]),(0,[z70,z0,z2,z4,z43,z579]),(1,[z0,z2,z4,z839,z6])],[(0,[z8,z1200,z2,z4,z5,z6])],[(0,[z8,z1,z2,z16,z5,z19]),(0,[z8,z0,z3,z4,z1201,z6]),(0,[z7,z8,z0,z2,z306,z40])],[(0,[z8,z20,z2,z4,z5,z340]),(0,[z8,z0,z32,z105,z5,z6]),(0,[z8,z0,z2,z68,z5,z6]),(0,[z8,z1202,z2,z4,z5,z6]),(0,[z8,z0,z1203,z4,z5,z6])],[(0,[z110,z1,z3,z4,z5,z6]),(0,[z511,z0,z2,z4,z5,z125]),(0,[z8,z0,z3,z4,z6,z37]),(0,[z8,z0,z1204,z4,z5,z6]),(0,[z33,z0,z2,z4,z5,z868]),(0,[z8,z0,z1205,z4,z5,z6]),(0,[z8,z0,z2,z4,z1206,z6]),(0,[z8,z1207,z2,z4,z5,z6]),(0,[z8,z0,z2,z1208,z5,z6]),(0,[z8,z1209,z2,z4,z5,z6])]],
   [[(0,[z8,z421,z2,z4,z5,z259]),(0,[z8,z512,z4,z5,z6,z193]),(0,[z8,z0,z2,z4,z6,z240])],[(0,[z8,z0,z2,z4,z324,z37]),(0,[z8,z1210,z2,z4,z5,z6]),(0,[z0,z2,z4,z839,z43,z6]),(0,[z8,z0,z2,z4,z1211,z6])],[(0,[z8,z23,z2,z4,z273,z6]),(0,[z8,z242,z3,z4,z5,z6]),(0,[z8,z0,z3,z4,z306,z6]),(0,[z8,z0,z2,z146,z5,z91]),(0,[z8,z1050,z0,z2,z4,z91]),(0,[z8,z0,z2,z4,z6,z1212])],[(0,[z8,z0,z2,z4,z1213,z6]),(0,[z8,z913,z0,z4,z5,z6]),(0,[z191,z23,z253,z4,z5,z6]),(0,[z8,z0,z32,z168,z5,z6]),(0,[z8,z22,z0,z393,z4,z6]),(0,[z8,z86,z129,z4,z5,z6]),(0,[z472,z45,z0,z4,z5,z6]),(0,[z8,z503,z2,z4,z6,z37])],[(0,[z8,z1,z25,z4,z5,z6]),(0,[z161,z1,z2,z4,z5,z6]),(0,[z0,z3,z4,z5,z19,z125])],[(0,[z511,z8,z2,z4,z5,z290]),(0,[z0,z1,z129,z4,z5,z6]),(0,[z0,z968,z3,z4,z5,z6]),(0,[z8,z0,z820,z4,z5,z6]),(0,[z8,z0,z2,z4,z1214,z6])],[(0,[z8,z0,z1215,z4,z5,z6]),(0,[z8,z0,z2,z1216,z5,z6]),(0,[z67,z0,z3,z4,z5,z18]),(0,[z95,z8,z32,z178,z5,z6]),(0,[z8,z0,z2,z4,z1217,z6]),(0,[z8,z220,z0,z39,z5,z6]),(0,[z376,z0,z2,z5,z6,z40])],[(0,[z8,z0,z1218,z2,z4,z6]),(0,[z8,z23,z2,z4,z6,z1219]),(0,[z8,z426,z182,z4,z5,z6]),(0,[z931,z0,z2,z4,z5,z6]),(0,[z8,z0,z4,z5,z845,z99]),(0,[z8,z123,z0,z2,z4,z6])],[(0,[z8,z0,z1220,z4,z5,z6]),(0,[z8,z255,z2,z4,z5,z6]),(0,[z249,z0,z149,z4,z5,z6]),(1,[z86,z3,z4,z5,z6]),(0,[z8,z100,z0,z355,z5,z6]),(0,[z8,z0,z2,z68,z5,z579]),(0,[z8,z374,z34,z4,z5,z6])],[(0,[z8,z0,z2,z4,z1221,z6]),(0,[z8,z23,z2,z4,z155,z6]),(0,[z8,z1222,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z4,z324]),(0,[z109,z8,z348,z2,z4,z6]),(0,[z8,z0,z2,z39,z155,z6])],[(0,[z8,z100,z23,z39,z5,z6]),(0,[z67,z0,z3,z4,z6,z37]),(0,[z167,z0,z3,z4,z5,z6]),(0,[z176,z0,z521,z4,z53,z6]),(0,[z67,z0,z2,z214,z5,z6]),(0,[z8,z0,z2,z4,z1223,z6]),(0,[z8,z390,z2,z4,z77,z6]),(0,[z8,z1224,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z397]),(0,[z8,z0,z2,z4,z1225,z6]),(0,[z8,z0,z32,z187,z5,z6]),(0,[z8,z0,z2,z4,z6,z1226]),(0,[z8,z131,z0,z4,z60,z6])],[(1,[z158,z1,z3,z4,z6]),(0,[z8,z1227,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z1090]),(0,[z8,z0,z373,z4,z479,z6]),(0,[z8,z0,z1228,z4,z5,z6]),(0,[z8,z0,z2,z4,z716,z6]),(0,[z8,z1229,z2,z4,z5,z6])],[(0,[z52,z1,z3,z4,z5,z6]),(0,[z8,z0,z3,z4,z325,z6]),(0,[z8,z0,z1230,z4,z5,z6]),(0,[z8,z0,z1231,z4,z5,z6]),(0,[z8,z1232,z2,z4,z5,z6])],[(0,[z8,z1054,z0,z4,z5,z6]),(0,[z8,z432,z51,z4,z5,z6]),(0,[z8,z1233,z2,z4,z5,z6]),(0,[z8,z732,z45,z4,z5,z6]),(1,[z8,z0,z2,z5,z752]),(0,[z8,z22,z0,z1234,z4,z6])],[(0,[z495,z0,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z4,z5,z163,z6]),(0,[z295,z23,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z6,z1172]),(0,[z8,z1235,z2,z4,z5,z6]),(0,[z8,z227,z24,z218,z5,z6]),(0,[z8,z678,z2,z218,z5,z6]),(0,[z8,z0,z2,z922,z4,z6])],[(0,[z8,z1,z2,z1101,z5,z6]),(0,[z8,z0,z147,z4,z5,z6]),(0,[z8,z1236,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z1237]),(0,[z8,z1238,z2,z4,z5,z6]),(0,[z98,z472,z0,z4,z5,z99]),(0,[z98,z8,z0,z105,z5,z99])],[(0,[z8,z0,z149,z4,z5,z6]),(0,[z8,z117,z2,z4,z5,z6]),(0,[z1,z3,z4,z171,z5,z6]),(0,[z8,z22,z78,z2,z4,z6]),(0,[z8,z22,z0,z32,z4,z6]),(0,[z124,z0,z2,z146,z6,z37]),(0,[z84,z8,z2,z4,z325,z193]),(0,[z8,z20,z2,z4,z5,z961])],[(0,[z8,z1239,z2,z4,z5,z6]),(0,[z8,z1240,z3,z4,z5,z6]),(0,[z8,z0,z4,z365,z320,z6])],[(0,[z8,z23,z2,z4,z6,z37]),(0,[z8,z801,z0,z2,z4,z6]),(0,[z176,z0,z3,z4,z53,z6]),(0,[z8,z1241,z2,z4,z5,z6]),(0,[z1242,z0,z2,z4,z5,z6]),(0,[z8,z0,z284,z138,z5,z6])],[(0,[z8,z49,z573,z4,z5,z6]),(0,[z8,z0,z32,z4,z1243,z6]),(0,[z8,z0,z2,z4,z5,z868]),(0,[z8,z0,z2,z105,z5,z6])],[(0,[z8,z0,z2,z4,z6,z1244]),(0,[z8,z0,z2,z4,z273,z6]),(0,[z98,z8,z0,z168,z5,z99])],[(0,[z8,z23,z2,z4,z306,z6]),(0,[z8,z0,z2,z4,z6,z1245])],[(0,[z1,z3,z4,z288,z5,z6]),(0,[z70,z1,z2,z4,z43,z6]),(0,[z158,z8,z0,z2,z4,z6]),(0,[z8,z0,z1246,z4,z5,z6]),(0,[z8,z101,z0,z183,z5,z6]),(0,[z8,z0,z589,z183,z5,z6])],[(0,[z8,z1,z2,z4,z387,z6]),(0,[z186,z0,z2,z4,z125,z37]),(0,[z8,z0,z2,z4,z6,z1247])],[(0,[z22,z1,z3,z4,z5,z6]),(0,[z8,z0,z1248,z4,z5,z6]),(0,[z8,z23,z2,z4,z58,z37])],[(0,[z67,z23,z2,z4,z5,z18]),(0,[z8,z467,z0,z355,z5,z6]),(0,[z8,z0,z2,z4,z1249,z6]),(0,[z8,z0,z2,z4,z260,z37])],[(0,[z8,z0,z2,z1250,z5,z6]),(0,[z382,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z1113,z5,z6]),(0,[z484,z0,z2,z248,z5,z6]),(0,[z8,z22,z891,z2,z4,z6])],[(0,[z8,z0,z2,z4,z1251,z6]),(0,[z186,z1,z2,z4,z5,z6]),(0,[z8,z202,z2,z4,z5,z6]),(0,[z8,z0,z3,z4,z5,z259]),(0,[z70,z0,z32,z4,z43,z6]),(0,[z8,z0,z2,z1252,z5,z6]),(0,[z8,z0,z2,z4,z155,z6]),(0,[z8,z1253,z0,z2,z4,z6]),(0,[z8,z338,z0,z4,z60,z6])],[(0,[z8,z0,z2,z1254,z5,z6]),(0,[z33,z0,z438,z4,z5,z125]),(0,[z8,z335,z0,z2,z96,z4])],[(0,[z8,z1,z2,z4,z5,z91]),(0,[z191,z23,z3,z4,z5,z6])]],
   [[(0,[z8,z189,z1,z32,z4,z6]),(0,[z67,z0,z2,z4,z5,z868]),(0,[z8,z0,z427,z4,z97,z6])],[(0,[z628,z0,z2,z4,z43,z6]),(0,[z8,z0,z4,z5,z6,z1255]),(0,[z8,z20,z2,z4,z5,z631]),(0,[z8,z0,z2,z4,z1256,z6])],[(0,[z52,z708,z2,z4,z5,z6]),(0,[z8,z23,z2,z4,z325,z6]),(0,[z8,z0,z3,z1257,z5,z6]),(0,[z8,z0,z2,z187,z5,z6]),(0,[z124,z0,z160,z146,z5,z6]),(0,[z8,z24,z2,z762,z5,z6]),(0,[z8,z0,z2,z861,z5,z6])],[(0,[z1,z660,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z125]),(0,[z8,z1,z104,z4,z5,z6]),(0,[z8,z1258,z2,z4,z5,z6]),(0,[z505,z0,z32,z4,z5,z6]),(0,[z8,z0,z1259,z2,z4,z6]),(0,[z1260,z0,z2,z4,z5,z6]),(0,[z8,z0,z558,z4,z6,z37])],[(0,[z8,z23,z160,z4,z5,z6]),(0,[z8,z0,z1261,z4,z5,z6])],[(0,[z8,z837,z1,z2,z4,z6]),(0,[z8,z813,z23,z2,z4,z6]),(0,[z95,z8,z2,z364,z5,z6]),(0,[z0,z3,z4,z5,z6,z41]),(0,[z614,z0,z3,z4,z5,z6]),(0,[z186,z545,z32,z4,z5,z6]),(0,[z8,z982,z2,z4,z5,z6]),(0,[z98,z167,z0,z4,z5,z99]),(0,[z98,z8,z0,z4,z5,z845])],[(0,[z8,z0,z2,z4,z5,z1262]),(0,[z1,z2,z597,z4,z5,z6]),(0,[z8,z0,z253,z4,z6,z37]),(0,[z8,z0,z2,z4,z1201,z6])],[(0,[z638,z1,z2,z4,z5,z6]),(0,[z8,z211,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z1263]),(0,[z8,z0,z2,z1264,z5,z6]),(0,[z8,z100,z0,z39,z13,z6])],[(0,[z158,z1,z2,z3,z4,z6]),(0,[z8,z23,z245,z4,z5,z6]),(0,[z8,z1265,z2,z4,z5,z6])],[(0,[z8,z0,z2,z4,z1266,z6]),(0,[z176,z23,z2,z4,z53,z6]),(0,[z8,z22,z242,z2,z4,z6])],[(0,[z8,z0,z32,z68,z5,z6]),(0,[z8,z0,z695,z2,z4,z37]),(0,[z8,z0,z2,z733,z5,z6]),(0,[z7,z8,z9,z2,z5,z40])],[(0,[z8,z242,z2,z4,z5,z6]),(0,[z8,z0,z32,z214,z5,z6]),(0,[z8,z0,z2,z4,z5,z1267]),(0,[z8,z0,z2,z1268,z5,z6]),(0,[z8,z0,z2,z1269,z5,z6]),(0,[z8,z131,z0,z414,z60,z6]),(0,[z8,z0,z443,z5,z6,z61]),(0,[z8,z1270,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z306,z6])],[(0,[z664,z1,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z1243,z6]),(0,[z8,z0,z2,z4,z1271,z6]),(0,[z8,z31,z23,z2,z6,z61]),(0,[z8,z0,z32,z4,z6,z240]),(0,[z8,z22,z0,z2,z361,z6]),(0,[z8,z0,z1272,z4,z5,z6]),(0,[z8,z0,z2,z14,z143,z6])],[],[(0,[z67,z1,z104,z4,z5,z6]),(0,[z8,z0,z2,z4,z1273,z6]),(0,[z8,z208,z182,z4,z5,z6])],[(0,[z8,z263,z0,z4,z90,z6]),(0,[z8,z0,z1274,z4,z5,z6]),(0,[z484,z22,z0,z2,z4,z6]),(0,[z1275,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z16,z5,z752])]],
   [[(0,[z700,z0,z32,z4,z5,z6]),(0,[z1276,z0,z2,z4,z5,z6]),(0,[z8,z227,z0,z4,z320,z6]),(0,[z376,z862,z2,z4,z5,z6]),(0,[z8,z0,z2,z958,z6,z37])],[(0,[z8,z1,z129,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z1140]),(0,[z8,z227,z23,z4,z5,z6]),(0,[z8,z374,z3,z4,z5,z6]),(0,[z70,z351,z0,z2,z4,z6]),(0,[z8,z0,z1277,z4,z5,z6]),(0,[z8,z24,z2,z218,z6,z37])],[(0,[z8,z1,z373,z4,z5,z6]),(0,[z626,z1,z2,z4,z5,z6]),(0,[z8,z23,z2,z4,z5,z259]),(0,[z8,z1278,z0,z2,z4,z6]),(1,[z0,z3,z4,z125,z37]),(0,[z376,z0,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z1139,z6]),(0,[z8,z0,z32,z1216,z5,z6])],[(0,[z167,z0,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z251,z6]),(0,[z8,z49,z4,z5,z6,z658]),(0,[z8,z440,z0,z39,z5,z6]),(0,[z8,z0,z443,z4,z143,z6])],[(0,[z7,z8,z1,z2,z5,z40]),(0,[z45,z1,z3,z4,z5,z6]),(0,[z8,z189,z2,z4,z179,z6]),(0,[z8,z255,z32,z4,z5,z6]),(0,[z8,z784,z0,z32,z4,z6]),(0,[z8,z0,z2,z4,z5,z1279]),(1,[z931,z0,z4,z5,z6])],[(0,[z33,z374,z2,z4,z5,z125]),(0,[z8,z0,z2,z4,z1280,z6]),(0,[z8,z22,z0,z1174,z4,z6])],[(0,[z52,z1,z2,z4,z5,z6]),(0,[z8,z758,z2,z4,z5,z6]),(0,[z8,z0,z3,z4,z1281,z6]),(0,[z8,z1282,z2,z4,z5,z6]),(0,[z116,z117,z2,z47,z5,z6]),(0,[z8,z0,z1283,z4,z5,z6]),(0,[z670,z0,z2,z4,z5,z125]),(0,[z8,z0,z4,z5,z6,z221]),(0,[z8,z0,z2,z4,z325,z6]),(0,[z8,z1284,z0,z2,z4,z6]),(0,[z8,z22,z0,z197,z4,z6])],[(0,[z8,z22,z0,z160,z4,z6]),(0,[z8,z0,z4,z6,z221,z37])],[(0,[z8,z1,z147,z4,z5,z6]),(0,[z237,z23,z3,z4,z5,z6]),(0,[z8,z0,z160,z4,z5,z6]),(0,[z8,z0,z4,z1285,z5,z6]),(0,[z98,z8,z0,z4,z5,z698]),(0,[z8,z0,z2,z4,z6,z1286])],[(0,[z8,z22,z23,z2,z4,z6]),(0,[z8,z1,z149,z4,z5,z6])],[(0,[z256,z1,z2,z4,z5,z6]),(0,[z598,z23,z2,z4,z5,z6]),(0,[z8,z1233,z32,z4,z5,z6]),(0,[z124,z211,z2,z146,z5,z6])],[(0,[z388,z1,z3,z4,z5,z6]),(1,[z0,z902,z4,z5,z6]),(0,[z8,z0,z1287,z4,z5,z6]),(0,[z8,z1288,z2,z4,z5,z6])],[(0,[z67,z1,z129,z4,z5,z6]),(0,[z8,z1,z2,z105,z5,z6]),(0,[z8,z449,z1,z2,z4,z6]),(0,[z537,z8,z506,z2,z4,z6])],[(0,[z158,z1,z2,z4,z6,z125]),(0,[z0,z1,z3,z4,z6,z37]),(0,[z8,z0,z1289,z4,z5,z6]),(0,[z469,z0,z3,z4,z5,z6]),(0,[z8,z101,z0,z330,z5,z6]),(0,[z176,z0,z2,z4,z53,z6]),(0,[z472,z22,z0,z2,z4,z6]),(0,[z8,z1290,z2,z4,z5,z6]),(0,[z8,z0,z197,z4,z6,z37]),(0,[z8,z1291,z2,z4,z5,z6]),(0,[z8,z914,z2,z4,z5,z6])],[(0,[z8,z0,z3,z248,z5,z6]),(0,[z124,z0,z2,z283,z5,z6]),(0,[z8,z1292,z0,z4,z5,z6]),(0,[z151,z8,z0,z2,z5,z40]),(0,[z8,z1293,z2,z4,z5,z6]),(0,[z975,z0,z2,z4,z6,z37])],[(0,[z1,z2,z4,z5,z19,z125]),(0,[z8,z0,z2,z4,z1294,z6]),(0,[z109,z8,z0,z2,z68,z6]),(0,[z8,z0,z4,z1295,z5,z6]),(0,[z1296,z0,z2,z4,z5,z6])]],
   [[(0,[z8,z23,z32,z4,z6,z37]),(0,[z8,z0,z2,z4,z535,z37]),(0,[z8,z2,z178,z5,z6,z217]),(0,[z8,z0,z197,z4,z306,z6])],[(0,[z67,z758,z2,z4,z5,z6]),(0,[z8,z1,z1248,z4,z5,z6]),(0,[z8,z1,z2,z168,z5,z6]),(0,[z8,z49,z115,z4,z5,z6]),(0,[z8,z23,z4,z365,z5,z6]),(0,[z8,z0,z32,z4,z1297,z6]),(0,[z8,z981,z2,z4,z6,z37]),(0,[z8,z0,z2,z96,z922,z4])],[(0,[z628,z1,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z273,z6]),(0,[z8,z0,z373,z4,z5,z91]),(0,[z8,z0,z2,z214,z5,z6]),(0,[z8,z0,z4,z5,z6,z1298]),(0,[z8,z22,z0,z4,z6,z221])],[(0,[z8,z0,z3,z405,z5,z6]),(0,[z8,z1299,z2,z4,z5,z6]),(0,[z8,z134,z147,z4,z5,z6]),(0,[z84,z8,z2,z248,z5,z193])],[(0,[z8,z0,z157,z4,z6,z37]),(0,[z1,z3,z4,z178,z5,z6]),(0,[z8,z0,z2,z4,z6,z1300]),(0,[z8,z1301,z2,z4,z5,z6])],[(0,[z8,z0,z1302,z4,z5,z6]),(0,[z23,z699,z2,z4,z5,z6]),(1,[z8,z2,z4,z716,z6]),(0,[z8,z0,z2,z4,z1303,z6]),(0,[z8,z0,z2,z16,z5,z526]),(0,[z8,z323,z0,z2,z4,z37])],[(0,[z8,z383,z0,z4,z425,z6]),(0,[z8,z9,z3,z4,z5,z6]),(0,[z8,z0,z245,z4,z5,z579]),(0,[z376,z907,z2,z4,z5,z6])],[(0,[z376,z23,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z1249,z6]),(0,[z8,z0,z2,z16,z5,z80]),(0,[z8,z0,z2,z68,z43,z6]),(0,[z1304,z0,z2,z4,z5,z6]),(0,[z8,z243,z0,z39,z5,z6]),(0,[z8,z488,z0,z39,z5,z6]),(0,[z8,z0,z1305,z4,z5,z6]),(0,[z7,z8,z0,z2,z5,z752])],[(0,[z191,z23,z2,z4,z5,z6]),(0,[z8,z0,z3,z4,z58,z37]),(0,[z8,z31,z0,z32,z6,z61]),(0,[z83,z8,z2,z4,z6,z133])],[(0,[z186,z1,z32,z4,z5,z6]),(0,[z8,z1,z2,z187,z5,z6]),(0,[z8,z202,z32,z4,z5,z6]),(0,[z8,z0,z32,z4,z155,z6]),(0,[z8,z117,z2,z4,z5,z91]),(0,[z8,z0,z1306,z4,z5,z6]),(0,[z8,z20,z2,z138,z5,z6]),(0,[z472,z0,z2,z4,z77,z6])],[(0,[z49,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z118]),(0,[z8,z1029,z0,z3,z4,z6]),(0,[z1307,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z251,z6]),(0,[z8,z0,z2,z4,z1308,z6]),(0,[z339,z0,z2,z4,z6,z37])],[(1,[z708,z2,z4,z5,z6]),(0,[z0,z149,z3,z4,z5,z6]),(0,[z8,z0,z2,z1257,z5,z6]),(0,[z8,z22,z0,z373,z4,z6]),(0,[z109,z8,z2,z4,z716,z6]),(0,[z8,z1309,z2,z4,z5,z6])],[(0,[z708,z1,z2,z4,z5,z6]),(0,[z8,z0,z1310,z4,z5,z6]),(0,[z116,z0,z2,z47,z6,z37])],[(0,[z158,z1,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z719]),(0,[z176,z0,z599,z2,z4,z6]),(0,[z8,z0,z1234,z4,z5,z6]),(0,[z339,z0,z2,z4,z306,z6])],[(0,[z8,z449,z23,z2,z4,z6]),(0,[z8,z22,z0,z25,z4,z6]),(0,[z8,z123,z0,z2,z16,z19]),(0,[z8,z0,z1000,z4,z6,z37])],[(0,[z511,z1,z3,z4,z5,z6]),(0,[z8,z1311,z2,z4,z5,z6]),(0,[z8,z0,z1312,z4,z5,z6]),(0,[z8,z131,z0,z231,z4,z6])]],
   [[(0,[z8,z1,z2,z4,z1266,z6]),(0,[z295,z0,z32,z4,z5,z6]),(0,[z70,z0,z25,z4,z43,z6]),(0,[z8,z206,z2,z187,z5,z6]),(0,[z456,z0,z2,z4,z5,z18]),(0,[z8,z0,z2,z4,z6,z1313])],[(0,[z327,z0,z3,z4,z5,z6]),(0,[z8,z1314,z2,z4,z5,z6]),(1,[z0,z2,z940,z5,z6])],[(0,[z52,z1,z157,z4,z5,z6]),(0,[z469,z23,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z1315])],[(0,[z8,z1,z2,z4,z1243,z6]),(0,[z8,z23,z2,z248,z5,z6]),(0,[z8,z0,z2,z4,z1316,z6]),(0,[z8,z22,z0,z2,z187,z6]),(0,[z8,z0,z2,z187,z387,z6]),(0,[z8,z0,z1317,z4,z5,z6]),(0,[z8,z0,z2,z1010,z6,z37])],[(0,[z8,z0,z32,z4,z6,z37]),(0,[z8,z0,z1318,z4,z5,z6]),(0,[z1319,z8,z0,z2,z4,z6]),(0,[z8,z148,z0,z2,z4,z6]),(0,[z8,z27,z0,z2,z379,z6])],[(0,[z8,z1320,z0,z2,z4,z6]),(0,[z8,z574,z0,z262,z5,z6]),(0,[z33,z22,z0,z2,z4,z125]),(0,[z115,z327,z0,z4,z5,z6])],[(0,[z1,z2,z612,z4,z5,z6]),(0,[z8,z23,z190,z4,z5,z6]),(0,[z8,z1321,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z1322,z6]),(0,[z8,z117,z2,z4,z479,z6]),(0,[z0,z2,z47,z5,z6,z91])],[(0,[z8,z242,z32,z4,z5,z6]),(0,[z8,z0,z32,z4,z306,z6]),(0,[z8,z49,z182,z4,z6,z37])],[(0,[z8,z23,z2,z405,z5,z6]),(0,[z8,z0,z2,z4,z1297,z6])],[(1,[z189,z1,z3,z4,z6]),(0,[z8,z1323,z2,z4,z5,z6]),(0,[z569,z8,z0,z4,z5,z99]),(0,[z8,z0,z2,z4,z1324,z6]),(0,[z8,z0,z4,z768,z5,z6])],[(0,[z8,z374,z2,z4,z5,z6]),(0,[z8,z0,z32,z4,z58,z37]),(0,[z8,z0,z2,z1325,z5,z6])],[(0,[z8,z1326,z2,z4,z5,z6]),(0,[z67,z0,z32,z4,z5,z18]),(0,[z8,z0,z1327,z4,z5,z6]),(0,[z8,z1328,z2,z4,z5,z6]),(0,[z8,z22,z390,z2,z4,z6])],[(0,[z186,z22,z1,z2,z4,z6]),(0,[z8,z0,z1329,z4,z5,z6]),(0,[z8,z117,z373,z4,z5,z6]),(0,[z8,z210,z2,z4,z306,z6])],[(0,[z1,z650,z2,z4,z5,z6]),(0,[z8,z1,z4,z5,z6,z221]),(0,[z8,z1330,z2,z4,z5,z6]),(0,[z8,z0,z3,z4,z77,z6]),(0,[z8,z0,z25,z68,z5,z6]),(0,[z1153,z8,z86,z2,z4,z6]),(0,[z8,z0,z2,z1331,z5,z6]),(0,[z84,z8,z512,z4,z5,z193]),(0,[z8,z22,z0,z2,z96,z4])],[(0,[z8,z0,z2,z4,z6,z1219]),(0,[z8,z0,z3,z4,z5,z324])],[(0,[z0,z3,z4,z5,z6,z170]),(0,[z8,z0,z2,z4,z1281,z6]),(0,[z167,z0,z32,z4,z5,z6]),(0,[z8,z22,z20,z2,z4,z11]),(0,[z8,z222,z0,z183,z5,z6])]],
   [[(0,[z383,z1,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z41]),(0,[z8,z0,z3,z4,z1332,z6]),(0,[z8,z0,z4,z365,z6,z309]),(0,[z8,z22,z0,z2,z582,z4])],[(0,[z1,z3,z4,z10,z5,z6]),(0,[z505,z1,z2,z4,z5,z6]),(0,[z1,z3,z4,z5,z11,z6]),(0,[z22,z0,z1,z3,z4,z6]),(0,[z249,z0,z2,z4,z6,z37]),(0,[z8,z503,z2,z4,z77,z6])],[(0,[z52,z1,z32,z4,z5,z6]),(0,[z109,z8,z189,z2,z4,z6]),(0,[z538,z8,z2,z4,z5,z397]),(0,[z8,z0,z32,z4,z325,z6]),(0,[z8,z0,z365,z5,z6,z40])],[(0,[z1,z3,z16,z4,z5,z6]),(0,[z327,z0,z32,z4,z5,z6]),(0,[z8,z1333,z2,z4,z5,z6]),(0,[z8,z0,z102,z4,z5,z697]),(0,[z8,z1334,z2,z4,z5,z6]),(0,[z8,z0,z2,z1031,z6,z37])],[(0,[z8,z23,z4,z1335,z5,z6]),(0,[z8,z0,z209,z4,z5,z398]),(0,[z8,z86,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z6,z1336])],[(0,[z803,z1,z2,z4,z5,z6]),(0,[z8,z93,z2,z4,z6,z37]),(0,[z8,z0,z1337,z4,z5,z6]),(0,[z121,z931,z0,z4,z5,z6])],[(0,[z8,z0,z2,z4,z6,z1338]),(0,[z368,z0,z2,z4,z6,z375])],[(0,[z295,z0,z2,z4,z5,z6]),(0,[z667,z8,z0,z4,z5,z99]),(0,[z8,z0,z2,z4,z1339,z6]),(0,[z8,z0,z2,z248,z5,z6]),(0,[z1340,z0,z2,z4,z5,z6]),(0,[z8,z1341,z2,z4,z5,z6]),(0,[z8,z0,z1342,z4,z5,z6])],[(0,[z8,z1,z2,z68,z5,z6]),(0,[z598,z0,z3,z4,z5,z6]),(0,[z8,z45,z51,z4,z5,z6]),(0,[z882,z8,z0,z2,z4,z6]),(0,[z73,z8,z0,z427,z4,z6])],[(0,[z8,z1,z3,z4,z6,z37]),(0,[z1,z103,z3,z4,z5,z6]),(0,[z8,z1,z2,z214,z5,z6]),(0,[z511,z1,z2,z4,z5,z125]),(0,[z176,z0,z32,z4,z53,z6]),(0,[z8,z198,z0,z2,z6,z61]),(0,[z0,z2,z4,z5,z6,z868]),(0,[z8,z0,z1343,z4,z5,z6]),(0,[z8,z609,z0,z2,z6,z61]),(0,[z339,z0,z1344,z4,z5,z6])],[(0,[z8,z1,z2,z4,z6,z240]),(0,[z8,z1074,z0,z2,z4,z6]),(0,[z8,z0,z190,z4,z5,z6]),(0,[z8,z1345,z2,z4,z5,z6]),(0,[z8,z449,z0,z32,z4,z6]),(0,[z8,z0,z1346,z4,z5,z6])],[(0,[z8,z0,z2,z4,z6,z37]),(0,[z67,z86,z2,z4,z5,z18]),(0,[z8,z0,z2,z4,z5,z1347])],[(0,[z8,z0,z1348,z4,z5,z6])],[(0,[z8,z1,z2,z4,z1213,z6]),(0,[z667,z0,z3,z4,z5,z125]),(0,[z8,z1349,z3,z4,z5,z6]),(0,[z548,z0,z32,z4,z5,z6])],[(0,[z700,z1,z2,z4,z5,z6]),(0,[z8,z545,z2,z4,z6,z37]),(0,[z8,z0,z2,z361,z6,z37]),(0,[z8,z0,z1350,z4,z5,z6]),(0,[z8,z0,z1351,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6]),(0,[z0,z3,z51,z4,z5,z6]),(0,[z632,z0,z3,z4,z5,z6]),(0,[z0,z2,z4,z47,z125,z37]),(0,[z124,z0,z393,z146,z5,z6]),(0,[z176,z134,z2,z4,z53,z6]),(0,[z8,z9,z2,z4,z5,z6])]],
   [[(0,[z8,z1,z2,z1216,z5,z6]),(0,[z8,z23,z2,z4,z744,z6]),(0,[z8,z23,z103,z4,z97,z6]),(0,[z8,z0,z1352,z4,z5,z6]),(0,[z8,z1353,z2,z4,z5,z6]),(0,[z8,z206,z2,z214,z5,z6])],[(0,[z23,z1,z3,z4,z5,z6]),(0,[z8,z803,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z251,z6]),(0,[z8,z23,z393,z4,z5,z6]),(0,[z8,z0,z1169,z4,z5,z6]),(0,[z8,z0,z2,z4,z1354,z6]),(0,[z8,z0,z2,z4,z58,z37]),(0,[z8,z0,z1046,z4,z6,z37]),(0,[z8,z22,z0,z802,z4,z6])],[(0,[z8,z23,z438,z4,z5,z6]),(0,[z8,z23,z2,z4,z77,z6]),(0,[z8,z20,z3,z4,z5,z11]),(0,[z8,z0,z32,z4,z5,z259]),(0,[z67,z0,z2,z4,z5,z18]),(0,[z8,z0,z4,z1355,z5,z6])],[(0,[z8,z23,z2,z4,z5,z324]),(0,[z8,z0,z2,z214,z387,z6]),(0,[z472,z0,z209,z4,z5,z6])],[(0,[z8,z0,z1356,z4,z5,z6]),(0,[z191,z23,z32,z4,z5,z6]),(0,[z186,z0,z104,z4,z5,z6]),(0,[z1357,z0,z2,z4,z5,z6]),(0,[z8,z1049,z2,z4,z6,z37])],[(0,[z52,z22,z1,z2,z4,z6]),(0,[z8,z0,z757,z2,z4,z6]),(0,[z8,z0,z510,z4,z201,z6]),(0,[z8,z93,z160,z4,z5,z6]),(0,[z1358,z0,z2,z4,z5,z6])],[(0,[z191,z0,z3,z4,z5,z6]),(0,[z8,z0,z1359,z4,z5,z6]),(0,[z8,z0,z2,z1360,z5,z6]),(0,[z8,z1183,z0,z4,z5,z6]),(0,[z8,z0,z2,z183,z155,z6])],[(0,[z0,z612,z3,z4,z5,z125])],[(0,[z191,z0,z157,z4,z5,z6]),(0,[z327,z1,z3,z4,z5,z6]),(0,[z8,z1196,z2,z4,z5,z6]),(0,[z8,z1218,z1,z2,z4,z6]),(0,[z8,z0,z4,z1335,z5,z6]),(0,[z237,z0,z902,z4,z5,z6]),(0,[z8,z22,z410,z2,z4,z6])],[(1,[z1,z3,z4,z5,z6]),(0,[z8,z23,z443,z4,z5,z6]),(0,[z8,z0,z3,z4,z6,z139]),(0,[z484,z0,z512,z4,z5,z6]),(0,[z7,z376,z0,z2,z5,z40]),(0,[z8,z22,z0,z2,z726,z6])],[(0,[z327,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z1361,z6])],[(1,[z1,z157,z4,z5,z6]),(0,[z8,z0,z2,z1362,z5,z6]),(0,[z8,z23,z2,z4,z18,z37])],[(0,[z8,z23,z450,z4,z5,z6]),(0,[z8,z0,z796,z2,z4,z6]),(0,[z8,z23,z94,z4,z5,z6]),(0,[z8,z211,z32,z4,z5,z6]),(0,[z8,z22,z348,z2,z4,z6]),(0,[z8,z24,z2,z218,z320,z6]),(0,[z8,z0,z2,z4,z6,z1363])],[(0,[z1,z2,z4,z682,z5,z6]),(0,[z8,z1364,z2,z4,z5,z6]),(0,[z8,z227,z0,z4,z6,z309]),(0,[z8,z488,z0,z4,z60,z6])],[(0,[z1,z3,z4,z5,z6,z61]),(0,[z1,z3,z4,z5,z60,z6]),(0,[z511,z8,z2,z4,z5,z193]),(1,[z0,z2,z47,z5,z91]),(0,[z8,z335,z0,z2,z4,z6]),(0,[z8,z1365,z2,z4,z5,z6]),(0,[z8,z0,z2,z353,z143,z6])],[(0,[z8,z281,z239,z4,z5,z6]),(0,[z109,z1,z3,z4,z5,z6]),(0,[z8,z0,z245,z4,z5,z6]),(0,[z8,z1240,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z1366,z6]),(0,[z8,z0,z2,z1367,z5,z6])]],
   [[(0,[z8,z1,z2,z4,z273,z6]),(0,[z8,z0,z2,z4,z1368,z6])],[(0,[z8,z0,z3,z4,z396,z6]),(0,[z8,z110,z348,z2,z4,z6]),(0,[z33,z0,z34,z4,z5,z125]),(0,[z8,z0,z1369,z4,z5,z6]),(0,[z8,z22,z0,z2,z922,z4])],[(0,[z8,z0,z245,z361,z5,z6]),(0,[z8,z1370,z0,z4,z5,z6]),(0,[z472,z390,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z1371])],[(0,[z8,z23,z773,z4,z5,z6]),(0,[z8,z131,z0,z4,z90,z6]),(0,[z8,z1372,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z1373,z6]),(1,[z376,z0,z2,z5,z40])],[(0,[z632,z23,z2,z4,z5,z6]),(0,[z484,z0,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z1374]),(0,[z98,z8,z0,z4,z5,z173]),(0,[z8,z9,z197,z4,z5,z6]),(0,[z8,z2,z4,z6,z37,z1371])],[(0,[z100,z1,z3,z4,z5,z6]),(0,[z504,z0,z3,z4,z5,z6])],[(0,[z8,z0,z2,z4,z1375,z6]),(0,[z23,z708,z2,z4,z5,z6]),(0,[z8,z0,z438,z4,z5,z6]),(0,[z8,z374,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z709,z6]),(0,[z176,z0,z2,z4,z839,z6]),(0,[z8,z255,z104,z4,z5,z6]),(0,[z7,z8,z0,z197,z5,z40])],[(0,[z8,z1,z2,z4,z155,z6]),(0,[z376,z0,z32,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z324]),(0,[z8,z0,z25,z4,z6,z37]),(0,[z8,z206,z2,z4,z273,z6]),(0,[z1376,z0,z2,z4,z5,z6]),(0,[z8,z22,z101,z0,z183,z6])],[(0,[z8,z189,z1,z2,z4,z6]),(0,[z81,z0,z3,z4,z5,z6]),(0,[z8,z335,z0,z2,z4,z579])],[(0,[z7,z8,z23,z2,z5,z40]),(0,[z8,z0,z2,z4,z1332,z6]),(0,[z8,z0,z2,z4,z372,z37]),(0,[z8,z0,z2,z4,z5,z259]),(0,[z109,z8,z506,z2,z4,z6]),(0,[z8,z1085,z2,z4,z6,z37]),(0,[z499,z8,z0,z2,z353,z6])],[(0,[z186,z0,z149,z4,z5,z6]),(0,[z8,z23,z2,z788,z5,z6]),(0,[z186,z22,z0,z32,z4,z6]),(0,[z8,z0,z1344,z4,z5,z6])],[(0,[z8,z0,z2,z414,z6,z37])],[(0,[z1,z3,z96,z4,z5,z6]),(0,[z8,z1377,z2,z4,z5,z6]),(0,[z8,z410,z3,z4,z5,z6]),(0,[z8,z0,z2,z361,z5,z259]),(0,[z8,z0,z2,z1004,z5,z6]),(0,[z8,z0,z2,z4,z1378,z6])],[(0,[z1,z2,z4,z5,z6,z135]),(0,[z8,z0,z2,z4,z118,z37]),(0,[z8,z0,z3,z4,z320,z6])],[(0,[z8,z0,z1379,z4,z5,z6]),(0,[z295,z1,z2,z4,z5,z6]),(0,[z8,z23,z2,z4,z6,z139]),(0,[z116,z0,z190,z47,z5,z6]),(0,[z8,z0,z2,z138,z251,z6]),(0,[z8,z100,z0,z39,z5,z6])],[(0,[z237,z0,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z43,z259]),(0,[z8,z0,z2,z4,z1380,z6]),(0,[z8,z22,z45,z21,z4,z6]),(0,[z484,z0,z889,z4,z5,z6]),(0,[z8,z0,z4,z97,z751,z6]),(0,[z8,z0,z1091,z4,z6,z37])]],
   [[(0,[z0,z599,z3,z4,z5,z6]),(0,[z67,z0,z393,z4,z5,z6]),(0,[z1381,z0,z2,z4,z5,z6]),(0,[z8,z0,z94,z4,z5,z6])],[(0,[z8,z0,z1382,z4,z5,z6]),(0,[z8,z0,z3,z4,z6,z200]),(0,[z67,z0,z438,z4,z5,z6]),(0,[z8,z1383,z2,z4,z5,z6]),(0,[z339,z9,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z6,z37]),(0,[z8,z23,z34,z4,z5,z6]),(0,[z8,z0,z1384,z4,z5,z6]),(0,[z166,z8,z2,z178,z5,z6]),(0,[z8,z1385,z2,z4,z5,z6])],[(0,[z8,z211,z2,z4,z5,z6]),(0,[z67,z189,z1,z2,z4,z6]),(0,[z8,z0,z32,z248,z5,z6]),(0,[z8,z0,z2,z4,z91,z37])],[(0,[z158,z8,z1,z32,z4,z6]),(0,[z8,z255,z129,z4,z5,z6]),(0,[z8,z1386,z2,z4,z5,z6]),(0,[z1387,z0,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z306,z6]),(0,[z0,z3,z4,z5,z125,z40]),(0,[z8,z1388,z2,z4,z5,z6]),(0,[z8,z0,z2,z16,z5,z534]),(0,[z8,z0,z1389,z4,z5,z6]),(0,[z8,z1390,z2,z4,z5,z6])],[(0,[z8,z1391,z2,z4,z5,z6]),(0,[z8,z23,z2,z4,z396,z6]),(0,[z667,z0,z2,z4,z5,z125]),(0,[z8,z390,z3,z4,z5,z6]),(0,[z8,z1349,z2,z4,z5,z6]),(0,[z472,z503,z2,z4,z5,z6])],[(0,[z8,z1392,z2,z4,z5,z6]),(0,[z8,z203,z190,z4,z5,z6]),(0,[z8,z0,z2,z4,z1393,z6])],[(0,[z8,z1,z2,z4,z58,z37]),(0,[z8,z0,z32,z405,z5,z6]),(0,[z8,z203,z2,z4,z6,z37]),(0,[z8,z0,z2,z4,z387,z18]),(0,[z8,z0,z4,z365,z5,z6]),(0,[z84,z8,z4,z5,z221,z193])],[(0,[z8,z0,z1394,z4,z5,z6]),(0,[z67,z1,z2,z4,z5,z18]),(0,[z1,z2,z4,z5,z162,z6]),(0,[z484,z23,z2,z4,z5,z6]),(0,[z0,z2,z4,z940,z5,z6]),(0,[z8,z206,z2,z4,z6,z37]),(0,[z1395,z0,z2,z4,z5,z6]),(0,[z8,z22,z0,z2,z405,z6])],[(0,[z101,z1,z3,z4,z5,z6]),(0,[z8,z348,z3,z4,z5,z6]),(0,[z8,z22,z0,z129,z4,z6]),(0,[z8,z1396,z0,z2,z4,z6]),(0,[z8,z22,z210,z2,z4,z6])],[(0,[z518,z0,z3,z4,z5,z6]),(0,[z8,z426,z115,z4,z5,z6]),(0,[z8,z9,z32,z4,z5,z6]),(0,[z83,z8,z2,z4,z163,z6]),(0,[z8,z22,z0,z2,z66,z4]),(0,[z8,z0,z168,z5,z6,z99]),(0,[z376,z0,z2,z4,z380,z6])],[(0,[z1,z3,z4,z5,z152,z6]),(0,[z8,z0,z2,z4,z5,z1397]),(0,[z8,z0,z1398,z4,z5,z6]),(0,[z8,z0,z1052,z4,z5,z6]),(0,[z95,z8,z22,z2,z178,z6]),(0,[z8,z0,z1399,z4,z5,z6]),(0,[z8,z0,z284,z4,z251,z6]),(0,[z8,z1400,z2,z4,z5,z6]),(0,[z8,z210,z2,z4,z6,z37])],[(0,[z67,z1,z2,z4,z6,z37]),(0,[z167,z1,z2,z4,z5,z6]),(0,[z191,z1,z3,z4,z5,z6]),(0,[z8,z134,z2,z4,z6,z37])],[(0,[z376,z0,z2,z4,z5,z6]),(0,[z8,z0,z4,z1401,z5,z6])],[(0,[z8,z0,z2,z1136,z5,z6])]],
   [[(0,[z8,z1,z2,z4,z325,z6]),(0,[z8,z923,z0,z2,z4,z6]),(0,[z8,z0,z2,z1402,z5,z6])],[(0,[z327,z1,z2,z4,z5,z6]),(0,[z98,z8,z1,z4,z5,z99]),(0,[z633,z0,z3,z4,z5,z6])],[(0,[z8,z1,z160,z4,z5,z6]),(0,[z1144,z8,z0,z2,z5,z6]),(0,[z8,z23,z2,z4,z320,z6]),(0,[z8,z1403,z2,z4,z5,z6]),(0,[z8,z0,z2,z4,z489,z37]),(0,[z8,z732,z21,z4,z5,z6]),(0,[z8,z689,z21,z4,z5,z6]),(0,[z8,z0,z2,z4,z6,z139])],[(0,[z186,z242,z2,z4,z5,z6]),(0,[z8,z1404,z2,z4,z5,z6]),(0,[z8,z1405,z2,z4,z5,z6]),(0,[z1406,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z5,z6,z728]),(0,[z0,z2,z4,z5,z6,z1407]),(0,[z140,z0,z2,z4,z6,z224])],[(0,[z545,z1,z2,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z173]),(0,[z8,z100,z0,z768,z5,z6]),(0,[z8,z1408,z2,z4,z5,z6]),(0,[z8,z1409,z2,z4,z5,z6]),(0,[z7,z8,z22,z0,z2,z40])],[(0,[z1,z3,z4,z5,z43,z6]),(0,[z84,z1,z3,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z1410]),(0,[z8,z0,z2,z1411,z5,z6]),(0,[z7,z8,z0,z32,z5,z40]),(0,[z8,z0,z25,z4,z5,z259]),(0,[z8,z0,z2,z1412,z5,z6]),(1,[z8,z0,z4,z5,z845]),(0,[z0,z2,z4,z6,z37,z1407])],[(0,[z8,z1,z245,z4,z5,z6]),(0,[z8,z1053,z0,z4,z5,z6]),(0,[z8,z23,z2,z4,z6,z200]),(0,[z8,z0,z1069,z4,z5,z6]),(0,[z8,z1413,z2,z4,z5,z6]),(0,[z8,z0,z1414,z4,z5,z6]),(0,[z8,z347,z0,z2,z6,z61])],[(0,[z176,z1,z2,z4,z53,z6]),(0,[z472,z23,z2,z4,z5,z6]),(0,[z1415,z0,z2,z4,z5,z6]),(0,[z8,z0,z2,z5,z752,z40])],[(0,[z8,z22,z0,z3,z4,z37])],[(0,[z1,z3,z4,z5,z144,z6]),(0,[z158,z8,z0,z3,z4,z6]),(0,[z8,z0,z3,z4,z18,z37]),(0,[z8,z1416,z2,z4,z5,z6]),(0,[z8,z0,z1417,z4,z5,z6]),(0,[z8,z0,z1157,z4,z5,z6]),(0,[z109,z8,z2,z4,z644,z6]),(0,[z8,z1418,z0,z2,z4,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z33,z0,z3,z4,z5,z125]),(0,[z8,z503,z3,z4,z5,z6]),(0,[z8,z0,z1419,z4,z5,z6]),(0,[z8,z0,z2,z4,z1420,z6]),(0,[z8,z1421,z2,z4,z5,z6]),(1,[z8,z0,z2,z6,z728])],[(0,[z548,z1,z2,z4,z5,z6]),(0,[z84,z8,z3,z4,z5,z193]),(0,[z8,z0,z2,z766,z5,z6]),(0,[z116,z0,z2,z47,z5,z324]),(0,[z295,z0,z2,z138,z5,z6])],[(0,[z8,z0,z32,z4,z1368,z6]),(0,[z8,z2,z762,z178,z5,z6])],[(0,[z8,z1,z2,z4,z1375,z6]),(0,[z84,z8,z2,z4,z5,z397]),(0,[z0,z3,z4,z5,z6,z196]),(0,[z8,z49,z732,z4,z5,z6]),(0,[z8,z49,z121,z4,z5,z6])],[(0,[z8,z1422,z2,z4,z5,z6]),(0,[z8,z0,z190,z4,z479,z6]),(0,[z124,z0,z2,z940,z5,z6]),(0,[z502,z327,z2,z4,z5,z6]),(0,[z8,z0,z2,z1423,z5,z6])],[(0,[z8,z1,z1302,z4,z5,z6]),(0,[z8,z0,z2,z4,z5,z1424]),(0,[z8,z0,z2,z138,z6,z37]),(0,[z8,z0,z2,z405,z5,z6]),(0,[z8,z9,z2,z4,z380,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 477) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 477).take 467) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 944).take 471) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1415).take 202) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1617)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [477, 467, 471, 202] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 78).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 78).take 73).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 151).take 69).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 220).take 78).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 298).take 73).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 371).take 75).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 446).take 66).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [78, 73, 69, 78, 73, 75, 66] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_nil pcend)))))))

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

end PEqualNP.Outside.L_meta_36376

theorem PEqualNP.Outside.L_meta_36376 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276813448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276813448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36376.solve