import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36382

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
  Nat.testBit (4278124202 * 2 ^ 32 + 4276944008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x02800409218e322a#64 ++ 0x005000812431c645#64 ++ 0xff440c1fe39e327f#64 ++ 0xbfe88183fc73c64f#64 : BitVec 256),
   (0x010212248020c0d1#64 ++ 0x002042449004181a#64 ++ 0xb6ea32648463c3ff#64 ++ 0x76dd464c908c787f#64 : BitVec 256),
   (0x5202c28708745462#64 ++ 0x0a405850e10e8a8c#64 ++ 0x6df3c387187c7c66#64 ++ 0xedbe7870e30f8f8c#64 : BitVec 256),
   (0x841c015816802b04#64 ++ 0x5083802b02d00560#64 ++ 0xe3fc03f81f807f85#64 ++ 0xfc7f807f03f00ff0#64 : BitVec 256),
   (0x181d6c001f5b0000#64 ++ 0x6303ad8003eb6000#64 ++ 0x1fdffc001fff8003#64 ++ 0xe3fbff8003fff000#64 : BitVec 256),
   (0xe01fbbf6c0000000#64 ++ 0x7c03f77ed8000000#64 ++ 0xffdfffffe0000000#64 ++ 0x1ffbfffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [3, 12]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb6ea32648463c3ff 0x76dd464c908c787f

def z1 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff440c1fe39e327f 0xbfe88183fc73c64f

def z2 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1fdffc001fff8003 0xe3fbff8003fff000

def z3 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6df3c387187c7c66 0xedbe7870e30f8f8c

def z4 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x41bc03f81f807d80 0xc837807f03f00fb0

def z5 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe0000000 0x1ffbfffffc000000

def z6 : W := mkw 0x0002020400204040 0x0000404080040808 0x24e2020400604066 0x649c4040800c080c

def z7 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x4911c183181c3c00 0x8922383063038780

def z8 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe3fc03f81f807f85 0xfc7f807f03f00ff0

def z9 : W := mkw 0x190256249f7bc0d1 0x03204ac493ef781a 0xb6ea32649fffc3ff 0xf6dd464c93fff87f

def z10 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x9e0ffc7fe0000000 0x13c1ff8ffc000000

def z11 : W := mkw 0x1000400008500000 0x02000800010a0000 0x0dd3c000187c0002 0xe1ba7800030f8000

def z12 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe463c3ff 0x7ffffffffc8c787f

def z13 : W := mkw 0xe51fbbfed6a0ebd5 0x7ca3f77fdad41d7a 0xffffffffffe3ffff 0xfffffffffffc7fff

def z14 : W := mkw 0x6003baa6c0000000 0x2c007754d8000000 0xff47fc1fe0000000 0x1fe8ff83fc000000

def z15 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xa4e20264806043fe 0x749c404c900c087f

def z16 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x00aa32600461c180 0x4015464c008c3830

def z17 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x4915cd9b60000000 0x0922b9b36c000000

def z18 : W := mkw 0x5202c28f08f47662 0x0a405851e11e8ecc 0xeff7c39f1bfc7e67 0xfdfef873e37f8fcc

def z19 : W := mkw 0x1a9d6c093fdf322a 0x6353ad8127fbe645 0x5fdffc1b7fffb003 0xebfbff836ffff600

def z20 : W := mkw 0xf91ffff6df7bc0d1 0x7f23fffedbef781a 0xffffffffffffc3ff 0xfffffffffffff87f

def z21 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xfffbf3e79c7fffff 0xffff7e7cf38fffff

def z22 : W := mkw 0x5a1fee871f7f5462 0x6b43fdd0e3efea8c 0x7fffff871ffffc67 0xeffffff0e3ffff8c

def z23 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x0c03c007007c0062 0x01807800e00f800c

def z24 : W := mkw 0x180040001e510000 0x0300080003ca2000 0x000000001c618000 0x40000000038c3000

def z25 : W := mkw 0x028000092084322a 0x0050000124108645 0xed40001fe01c327e 0xbda80003fc03864f

def z26 : W := mkw 0xe01fbbf6c0204040 0x7c03f77ed8040808 0xffffffffe0604066 0x7ffffffffc0c080c

def z27 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe3dc03f81b803c00 0x9c7b807f03700780

def z28 : W := mkw 0x0382162da1aef2fb 0x007042c5b435de5f 0xb6ea326487fff3ff 0xf6dd464c90fffe7f

def z29 : W := mkw 0xf01ffbf6c8500000 0x7e03ff7ed90a0000 0xffdffffff87c0002 0xfffbffffff0f8000

def z30 : W := mkw 0x0382162da1aef2fb 0x007042c5b435de5f 0xffee3e7fe7fff3ff 0xfffdc7cffcfffe7f

def z31 : W := mkw 0x869c0559378e3b2e 0x50d380ab26f1c765 0xfffc0fffff9e7fff 0xffff81fffff3cfff

def z32 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xb6dbf3e480000000 0x16db7e7c90000000

def z33 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6931c387181c7c64 0x8d263870e3038f8c

def z34 : W := mkw 0x18016c00095b0000 0x23002d80012b6000 0x1c03fc00007f8002 0x03807f80000ff000

def z35 : W := mkw 0x028000012004102a 0x0050000024008205 0x00000007e0000078 0x00000000fc00000f

def z36 : W := mkw 0x1280440929fe766a 0x02500881253fcecd 0x002000001bfe7e7f 0xe0040000037fcfcf

def z37 : W := mkw 0x5282c68f29fe766a 0x0a5058d1e53fcecd 0xfff7cf9ffbfe7e7f 0xfffef9f3ff7fcfcf

def z38 : W := mkw 0x4282868f21ae766a 0x085050d1e435cecd 0xff640f9fe39e7e7f 0xbfec81f3fc73cfcf

def z39 : W := mkw 0x0002020400000000 0x0000404080000000 0x24c2020400000000 0x0498404080000000

def z40 : W := mkw 0x06800409378e3b2e 0x00d0008126f1c765 0x002000001f9e7fff 0xe004000003f3cfff

def z41 : W := mkw 0x0400000816802b04 0x0080000102d00560 0x002000001f807f85 0xe004000003f00ff0

def z42 : W := mkw 0x0100102080008091 0x0020020410001012 0x9208306084038399 0x1241060c10807073

def z43 : W := mkw 0x1a9d6c093fdf322a 0x6353ad8127fbe645 0xffdffc1fffffb27f 0xfffbff83fffff64f

def z44 : W := mkw 0x00000400010a0000 0x0000008000214000 0x1f440c00039e0003 0xa3e881800073c000

def z45 : W := mkw 0x8502137c80a0ebd5 0x10a0426f90141d7a 0xf6ea33fc8463ffff 0x7edd467f908c7fff

def z46 : W := mkw 0xa01f3b74c0000000 0x7403e76e98000000 0xb6ce3e7ce0000000 0x16d9c7cf9c000000

def z47 : W := mkw 0xd61ec3df1ef47f66 0x5ac3d87be3de8fec 0xefffc3ff1ffc7fe7 0xfdfff87fe3ff8ffc

def z48 : W := mkw 0x5282c687297e546a 0x0a5058d0e52fca8d 0x1c03cc07e07e007a 0x03807980fc0fc00f

def z49 : W := mkw 0x841c015016000904 0x5083802a02c00120 0x00b803e01c004d80 0x4017007c038009b0

def z50 : W := mkw 0x9c1d6d501f5b0904 0x7383adaa03eb6120 0x1fffffe01fffcd83 0xe3fffffc03fff9b0

def z51 : W := mkw 0x86800559218e3b2e 0x10d000ab2431c765 0xff640fffe39e7fff 0xbfec81fffc73cfff

def z52 : W := mkw 0x001f3a2480000000 0x6003e74490000000 0xbfdffe6480000000 0x17fbffcc90000000

def z53 : W := mkw 0x1000400008500000 0x02000800010a0000 0x0911c000181c0000 0x8122380003038000

def z54 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x411401981b803c00 0x8822803303700780

def z55 : W := mkw 0x081d2c00170b0000 0x6103a58002e16000 0x120c3c0007838001 0x0241878000f07000

def z56 : W := mkw 0x4202828700245462 0x08405050e0048a8c 0x6020038700007c64 0x0c040070e0000f8c

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0x61f0038018007c04 0xec3e007003000f80

def z58 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x820c007807800381 0x1041800f00f00070

def z59 : W := mkw 0x028000092084322a 0x0050000124108645 0xe000001fe000327c 0x1c000003fc00064f

def z60 : W := mkw 0xe29fbbffe084322a 0x7c53f77ffc108645 0xffdfffffe000327c 0x1ffbfffffc00064f

def z61 : W := mkw 0x02800409218e322a 0x005000812431c645 0x00000000039e327f 0xa00000000073c64f

def z62 : W := mkw 0x180044001f5b0000 0x0300088003eb6000 0x000000001fff8003 0xe000000003fff000

def z63 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z64 : W := mkw 0x001d280000000000 0x6003a50000000000 0x1fdffc0000000000 0x03fbff8000000000

def z65 : W := mkw 0x849c0558378a2b0c 0x509380ab06f14561 0x920c0c78e7820399 0x1241818f1cf04073

def z66 : W := mkw 0xe21fbbf7c0245462 0x7c43f77ef8048a8c 0xffffffffe0007c64 0x1ffffffffc000f8c

def z67 : W := mkw 0x18016c00095b0000 0x23002d80012b6000 0x1dd3fc00187f8002 0xe3ba7f80030ff000

def z68 : W := mkw 0xe41fbbfed6802b04 0x7c83f77fdad00560 0xffffffffff807f85 0xfffffffffff00ff0

def z69 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe002027f 0x3ffbfffffc00404f

def z70 : W := mkw 0x0382122da0a4f2fb 0x00704245b4149e5f 0xe020027fe00073fc 0x1c04004ffc000e7f

def z71 : W := mkw 0x0100102080008091 0x0020020410001012 0x0008306004018180 0x0001060c00803030

def z72 : W := mkw 0x02800401210e102a 0x005000802421c205 0x08000c03601c0000 0x010001806c038000

def z73 : W := mkw 0xe29fbfffe18e322a 0x7c53f7fffc31c645 0xffdfffffe39c3000 0x9ffbfffffc738600

def z74 : W := mkw 0xe00293f6c0000000 0x1c00527ed8000000 0xe00003ffe0000000 0x1c00007ffc000000

def z75 : W := mkw 0x0002122480000000 0x0000424490000000 0xb6ca326480000000 0x16d9464c90000000

def z76 : W := mkw 0x20013820c0000000 0x2400270418000000 0x10003c00e0000000 0x020007801c000000

def z77 : W := mkw 0x5002c28608704440 0x0a005850c10e0888 0x0df3c380187c4c02 0xe1be7870030f8980

def z78 : W := mkw 0x869c0559378e3b2e 0x50d380ab26f1c765 0x49140d9b7b9c3c00 0x892281b36f738780

def z79 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x7fffff801ffffc07 0xeffffff003ffff80

def z80 : W := mkw 0x191f7e249f7bc0d1 0x6323efc493ef781a 0xbffffe649fffc3ff 0xf7ffffcc93fff87f

def z81 : W := mkw 0x0000000000000000 0x0000000000000000 0xa2c8026000000000 0x1459004c00000000

def z82 : W := mkw 0x0000000000000000 0x0000000000000000 0xff440c1fe0000000 0x1fe88183fc000000

def z83 : W := mkw 0xe29fbfffe18e322a 0x7c53f7fffc31c645 0xffdfffffe39e327f 0xbffbfffffc73c64f

def z84 : W := mkw 0x110252248870c0d1 0x02204a44910e181a 0xbffbf2649c7fc3ff 0xf7ff7e4c938ff87f

def z85 : W := mkw 0x00800408218a2208 0x0010008104314441 0x92040c18e3820219 0x124081831c704043

def z86 : W := mkw 0x851e137c96a0ebd5 0x50a3c26f92d41d7a 0xf7fe33fc9fe3ffff 0xfeffc67f93fc7fff

def z87 : W := mkw 0x801c015000000000 0x5003802a00000000 0x4114019800000000 0x0822803300000000

def z88 : W := mkw 0x18016c001f5b0000 0x23002d8003eb6000 0x1c03fc001fff8003 0xe3807f8003fff000

def z89 : W := mkw 0x801c015000000000 0x5003802a00000000 0xe3dc03f800000000 0x1c7b807f00000000

def z90 : W := mkw 0x181c44001f5b0000 0x4303888003eb6000 0x03dc00001fff8003 0xe07b800003fff000

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0xb64000048002027f 0x36c800009000404f

def z92 : W := mkw 0x0000000800802200 0x0000000100100440 0xe344001803803205 0xbc68800300700640

def z93 : W := mkw 0x4002828600000000 0x08005050c0000000 0x6dd3c38700000000 0x0dba7870e0000000

def z94 : W := mkw 0x0100102080008091 0x0020020410001012 0xb2e832608403c39d 0x765d064c10807873

def z95 : W := mkw 0x410292a68020c0d1 0x08205254d004181a 0xfffbf3e78463c3ff 0x7fff7e7cf08c787f

def z96 : W := mkw 0x06800409378e3b2e 0x00d0008126f1c765 0xff640c1fff9e7fff 0xffec8183fff3cfff

def z97 : W := mkw 0xf21ffbf7c8745462 0x7e43ff7ef90e8a8c 0xfffffffff87c7c66 0xffffffffff0f8f8c

def z98 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x5d17fd9fe0000000 0x0ba2ffb3fc000000

def z99 : W := mkw 0x0100102080008091 0x0020020410001012 0xb6483064840383ff 0x36c9060c9080707f

def z100 : W := mkw 0xe29daddb618e322a 0x7c53b5bb6c31c645 0x4915cd9b639c3000 0x8922b9b36c738600

def z101 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x7ffbf3871c7ffc67 0xefff7e70e38fff8c

def z102 : W := mkw 0x010000000020c0d1 0x002000000004181a 0x002000000463c3ff 0x60040000008c787f

def z103 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xedf3c3e7987c7ffe 0xfdbe787cf30f8fff

def z104 : W := mkw 0x0000000000000000 0x0000000000000000 0xa2e8026004004385 0x745d004c00800870

def z105 : W := mkw 0x02800409218e322a 0x005000812431c645 0x5d040c1fe39e307a 0x8ba08183fc73c60f

def z106 : W := mkw 0x028000092084322a 0x0050000124108645 0x4000001b60003000 0x080000036c000600

def z107 : W := mkw 0x19037e24897bc0d1 0x23206fc4912f781a 0x1c03fc04807f807a 0x03807f80900ff00f

def z108 : W := mkw 0x191f7e249f7bc0d1 0x6323efc493ef781a 0x1fdffc049fff807b 0xe3fbff8093fff00f

def z109 : W := mkw 0x18016c00095b0000 0x23002d80012b6000 0x1ecbfc00047f8003 0x63d97f80008ff000

def z110 : W := mkw 0x0000000800802200 0x0000000100100440 0xe000001800003204 0x1c00000300000640

def z111 : W := mkw 0x9c1d6d581fdb2b04 0x7383adab03fb6560 0x4915cd981b9c3c00 0x8922b9b303738780

def z112 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x6d51c187181c3c66 0xadaa3830e303878c

def z113 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x140230048063807a 0x02804600900c700f

def z114 : W := mkw 0xf81dedd25f5b0000 0x7f03bdba4beb6000 0x5fdffd9b7fff8003 0xebfbffb36ffff000

def z115 : W := mkw 0x1a9d6c093fdf322a 0x6353ad8127fbe645 0x4915cc1b7b9c3000 0x8922b9836f738600

def z116 : W := mkw 0x1200400108745462 0x02400800210e8a8c 0x00200000187c7c66 0xe0040000030f8f8c

def z117 : W := mkw 0x841c015800802b04 0x5083802b00100560 0xe3fc03f800007f84 0x1c7f807f00000ff0

def z118 : W := mkw 0x6003baa6c0000000 0x2c007754d8000000 0x1c03fc07e0000000 0x03807f80fc000000

def z119 : W := mkw 0xa01d295040000000 0x7403a52a08000000 0x00040c1860000000 0x000081830c000000

def z120 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x0dd7cc001bfc0002 0xe1baf980037f8000

def z121 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffffffffe4004385 0x7ffffffffc800870

def z122 : W := mkw 0x001d280000000000 0x6003a50000000000 0xffdffc1fe0000000 0x1ffbff83fc000000

def z123 : W := mkw 0x8000015000000000 0x1000002a00000000 0xe00003f800000000 0x1c00007f00000000

def z124 : W := mkw 0x02800409218e322a 0x005000812431c645 0xe000001fe39e327f 0xbc000003fc73c64f

def z125 : W := mkw 0x0002122480000000 0x0000424490000000 0xb6ca326484638003 0x76d9464c908c7000

def z126 : W := mkw 0xa29d3d79e18e322a 0x7453a7af3c31c645 0xff4c3c7fe39e327f 0xbfe9878ffc73c64f

def z127 : W := mkw 0x181d68001e510000 0x6303ad0003ca2000 0x0011c00018000000 0x0002380003000000

def z128 : W := mkw 0x841c015016000904 0x5083802a02c00120 0x0010018018000c00 0x0002003003000180

def z129 : W := mkw 0x0000000000000000 0x0000000000000000 0x16ca300004638003 0x62d94600008c7000

def z130 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe13403f81b807f84 0x9c26807f03700ff0

def z131 : W := mkw 0x0200000100041022 0x0040000020008204 0x6000000700003064 0x0c000000e000060c

def z132 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x009bf3e000000000 0x00137e7c00000000

def z133 : W := mkw 0xf202d3f7c8745462 0x1e405a7ef90e8a8c 0xedf3c3fff87c7c66 0xfdbe787fff0f8f8c

def z134 : W := mkw 0x851c11789680ab95 0x50a3822f12d01572 0xf3fc33f89f83ff9d 0xfe7f867f13f07ff3

def z135 : W := mkw 0x0100000000008091 0x0020000000001012 0x0000000004038399 0x0000000000807073

def z136 : W := mkw 0x191d6c001f7bc0d1 0x6323ad8003ef781a 0x1ffffc001fffc3ff 0xe3ffff8003fff87f

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0xe344001800000000 0x1c68800300000000

def z138 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x1c9bffe7e0000000 0x03937ffcfc000000

def z139 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xfff7cf9ff87c7c66 0xfffef9f3ff0f8f8c

def z140 : W := mkw 0x00800408218a2208 0x0010008104314441 0xf3440c18e382321d 0xbe6881831c704643

def z141 : W := mkw 0x00000400010a0000 0x0000008000214000 0x1c000c00001e0002 0x038001800003c000

def z142 : W := mkw 0x0000000800802200 0x0000000100100440 0xe3f403981b807e05 0xfc7e807303700fc0

def z143 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0xffdffc1fffff8003 0xfffbff83fffff000

def z144 : W := mkw 0xde1fefdf1fff7f66 0x7bc3fdfbe3ffefec 0xffffffff1fffffe7 0xffffffffe3fffffc

def z145 : W := mkw 0x081d2c00170b0000 0x6103a58002e16000 0x16ce3c0007e38003 0x62d9c78000fc7000

def z146 : W := mkw 0x5302c2870874d4f3 0x0a605850e10e9a9e 0x6df3c3871c7fffff 0xedbe7870e38fffff

def z147 : W := mkw 0xe41fbbfec0802b04 0x7c83f77fd8100560 0xffffffffe0007f84 0x1ffffffffc000ff0

def z148 : W := mkw 0x8400015800802b04 0x1080002b00100560 0xe02003f800007f84 0x1c04007f00000ff0

def z149 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1e0ffc0007ff8003 0x03c1ff8000fff000

def z150 : W := mkw 0x1000400008500000 0x02000800010a0000 0x1fdbf0001c7f8003 0xe3fb7e00038ff000

def z151 : W := mkw 0xe003bbf6c0000000 0x3c00777ed8000000 0xfc03ffffe0000000 0x1f807ffffc000000

def z152 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x60200387187c7c66 0xec040070e30f8f8c

def z153 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x0915cc001b9c0000 0x8122b98003738000

def z154 : W := mkw 0xf81ffff6df5b0000 0x7f03fffedbeb6000 0xffdffffffb9c0000 0x9ffbffffff738000

def z155 : W := mkw 0xf21ffbf7c8541422 0x7e43ff7ef90a8284 0xffdffffff81c3c00 0x9ffbffffff038780

def z156 : W := mkw 0xf21ffbf7c8745462 0x7e43ff7ef90e8a8c 0x6dfbf3e7187c7c66 0xedbf7e7ce30f8f8c

def z157 : W := mkw 0x02800409218e322a 0x005000812431c645 0x49040c1b639c3000 0x892081836c738600

def z158 : W := mkw 0x181d68001e510000 0x6303ad0003ca2000 0x009bf0001c618000 0x40137e00038c3000

def z159 : W := mkw 0x5102d2a68870c4d1 0x0a205a54d10e189a 0xb6fbf3e49c63cfff 0x76df7e7c938c79ff

def z160 : W := mkw 0x010000000020c0d1 0x002000000004181a 0x16ea30000463c3ff 0x62dd4600008c787f

def z161 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe4638003 0x7ffbfffffc8c7000

def z162 : W := mkw 0x9c1d6d581fdb2b04 0x7383adab03fb6560 0x5fdffd981fffbc03 0xebfbffb303fff780

def z163 : W := mkw 0x9c1d69581ed12b04 0x7383ad2b03da2560 0xe3fff3f81fe1ff85 0xfc7ffe7f03fc3ff0

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0x8208006004000381 0x1041000c00800070

def z165 : W := mkw 0xe01fbbfec0802200 0x7c03f77fd8100440 0xffdfffffe3803205 0xbffbfffffc700640

def z166 : W := mkw 0x181d68001e510000 0x6303ad0003ca2000 0x03dff0001fe18001 0xe07bfe0003fc3000

def z167 : W := mkw 0x0a9d2c09378f322a 0x6153a58126f1e645 0xff4c3c1fe79fb27f 0xbfe98783fcf3f64f

def z168 : W := mkw 0x0000000800802200 0x0000000100100440 0xff440c1fe3803205 0xbfe88183fc700640

def z169 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0xbfdffc049fff827f 0xf7fbff8093fff04f

def z170 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xf7fe33f81fe3ff87 0xfeffc67f03fc7ff0

def z171 : W := mkw 0x0200000100041022 0x0040000020008204 0x6d400007001c3066 0xada80000e003860c

def z172 : W := mkw 0x0100102080008091 0x0020020410001012 0x1000300080038018 0x0200060010007003

def z173 : W := mkw 0xe28297ffe18e322a 0x1c5052fffc31c645 0xff440fffe39e327f 0xbfe881fffc73c64f

def z174 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x49b3c383187c7c00 0xc9367870630f8f80

def z175 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xe915cfffe0000000 0x1d22b9fffc000000

def z176 : W := mkw 0x191f7a249e71c0d1 0x6323ef4493ce381a 0x00bbf2601c61c180 0x40177e4c038c3830

def z177 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x0801c003001c0000 0x0100380060038000

def z178 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xeffbc3e71c7c7fe7 0xfdff787ce38f8ffc

def z179 : W := mkw 0x0002122480000000 0x0000424490000000 0x1402300480000000 0x0280460090000000

def z180 : W := mkw 0x1202420508745462 0x02404840a10e8a8c 0x24e20204187c7c66 0xe49c4040830f8f8c

def z181 : W := mkw 0x5000c08208500400 0x0a001810410a0080 0x0011c18018000c00 0x0002383003000180

def z182 : W := mkw 0x001d2c00010a0000 0x6003a58000214000 0x1fdffc00039e0003 0xa3fbff800073c000

def z183 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe22c03f807807f85 0x1c45807f00f00ff0

def z184 : W := mkw 0x1200400108745462 0x02400800210e8a8c 0x00000000007c0062 0x00000000000f800c

def z185 : W := mkw 0x5002c28608704440 0x0a005850c10e0888 0x24f3c38418604c66 0x649e7870830c098c

def z186 : W := mkw 0x5a1fee871f7f5462 0x6b43fdd0e3efea8c 0x6df7cf871bfc7c66 0xedbef9f0e37f8f8c

def z187 : W := mkw 0x0200000100041022 0x0040000020008204 0xff400007801e327f 0xbfe80000f003c64f

def z188 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x00b3c380187c7c66 0xe0167870030f8f8c

def z189 : W := mkw 0x0002020400204040 0x0000404080040808 0x2020020400004064 0x040400408000080c

def z190 : W := mkw 0x5002c28608704440 0x0a005850c10e0888 0x00b3c38018604c00 0x40167870030c0980

def z191 : W := mkw 0x0182162ca1aae2d9 0x003042c594355c5b 0xb6ee3e7ce7e3c3ff 0x76ddc7cf9cfc787f

def z192 : W := mkw 0x8c1d2d58178b2b04 0x7183a5ab02f16560 0x920c3c7807838381 0x1241878f00f07070

def z193 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x960a3064846383fb 0x12c1460c908c707f

def z194 : W := mkw 0x02800409218e322a 0x005000812431c645 0x1c000c07e39e327f 0xa3800180fc73c64f

def z195 : W := mkw 0x0400000816802b04 0x0080000102d00560 0x000000001b803c00 0x8000000003700780

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0xa020026000004384 0x1404004c00000870

def z197 : W := mkw 0x4202828700245462 0x08405050e0048a8c 0x0000000700000060 0x00000000e000000c

def z198 : W := mkw 0x1000400008500000 0x02000800010a0000 0x6df3c380187c7c06 0xedbe7870030f8f80

def z199 : W := mkw 0x1a1d6c011f7f5462 0x6343ad8023efea8c 0x1ffffc001ffffc67 0xe3ffff8003ffff8c

def z200 : W := mkw 0x0200000100041022 0x0040000020008204 0x49000003001c3000 0x8920000060038600

def z201 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x92aa32608463c399 0x5255464c108c7873

def z202 : W := mkw 0x5200c08308745462 0x0a401810610e8a8c 0x4931c183187c7c66 0xe9263830630f8f8c

def z203 : W := mkw 0xe28293ffe084322a 0x1c50527ffc108645 0xe00003ffe000327c 0x1c00007ffc00064f

def z204 : W := mkw 0xe01db9f2c0000000 0x7c03b73e58000000 0xdb1dfdfbe0000000 0x1b63bfbf7c000000

def z205 : W := mkw 0x0000102080000000 0x0000020410000000 0x9208306080000000 0x1241060c10000000

def z206 : W := mkw 0xf81ffff6df5b0000 0x7f03fffedbeb6000 0xffdfffffffff8003 0xfffbfffffffff000

def z207 : W := mkw 0x028000092084322a 0x0050000124108645 0xff440c1fe000327c 0x1fe88183fc00064f

def z208 : W := mkw 0x02800409218e322a 0x005000812431c645 0xfff40f9ffb9e7e7f 0xfffe81f3ff73cfcf

def z209 : W := mkw 0xe20293f7c0245462 0x1c40527ef8048a8c 0xe02003ffe0007c64 0x1c04007ffc000f8c

def z210 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x82bc03f81f804f81 0x5057807f03f009f0

def z211 : W := mkw 0x1000400008500000 0x02000800010a0000 0x0c03c000007c0002 0x01807800000f8000

def z212 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x0002300000618000 0x00004600000c3000

def z213 : W := mkw 0x160040091ef47f66 0x02c0080123de8fec 0x002000001ffc7fe7 0xe004000003ff8ffc

def z214 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0xebddcffb60000000 0x1d7bb9ff6c000000

def z215 : W := mkw 0x0080000820802208 0x0010000104100441 0x80000018e0000218 0x100000031c000043

def z216 : W := mkw 0x8400015816802b04 0x1080002b02d00560 0xe02003f81f807f85 0xfc04007f03f00ff0

def z217 : W := mkw 0x191f7e249f7bc0d1 0x6323efc493ef781a 0x1ffffe601fffc183 0xe3ffffcc03fff830

def z218 : W := mkw 0x02800401210e102a 0x005000802421c205 0x1c000c07e01e007a 0x03800180fc03c00f

def z219 : W := mkw 0x9c1d6d581fdb2b04 0x7383adab03fb6560 0xfffffff81fffff87 0xffffffff03fffff0

def z220 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xe3dff3f800000000 0x1c7bfe7f00000000

def z221 : W := mkw 0x600292a6c0000000 0x0c005254d8000000 0x00000007e0000000 0x00000000fc000000

def z222 : W := mkw 0x841d295816802b04 0x7083a52b02d00560 0xfffffff81f807f85 0xffffffff03f00ff0

def z223 : W := mkw 0x5b1ffea79f7fd4f3 0x6b63ffd4f3effa9e 0xffffffe79fffffff 0xfffffffcf3ffffff

def z224 : W := mkw 0x0400000816802b04 0x0080000102d00560 0x0000000007800381 0x0000000000f00070

def z225 : W := mkw 0x981d6d501f5b0000 0x7303adaa03eb6000 0xffdffff81fff8003 0xfffbffff03fff000

def z226 : W := mkw 0xe29daddb618e322a 0x7c53b5bb6c31c645 0xff55cd9fe39e327f 0xbfeab9b3fc73c64f

def z227 : W := mkw 0xd41ec3de1ef06f44 0x5a83d87bc3de0de8 0xe3ffc3f81fe07f85 0xfc7ff87f03fc0ff0

def z228 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb64230048063827f 0x36c84600900c704f

def z229 : W := mkw 0xa0001170c0000000 0x1400022e18000000 0x80000078e0000000 0x1000000f1c000000

def z230 : W := mkw 0x189d6c083fdb2208 0x6313ad8107fb6441 0x9fdffc18ffff821b 0xf3fbff831ffff043

def z231 : W := mkw 0xa81d3d70d70b0000 0x7503a7ae1ae16000 0x920c3c78e7838001 0x1241878f1cf07000

def z232 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x0000000480000078 0x000000009000000f

def z233 : W := mkw 0xa01d3970c0000000 0x7403a72e18000000 0x920c3c78e0000000 0x1241878f1c000000

def z234 : W := mkw 0x1a8044093fdf322a 0x0350088127fbe645 0x000000001fffb27f 0xe000000003fff64f

def z235 : W := mkw 0x0000000000000000 0x0000000000000000 0x9200000080020219 0x1240000010004043

def z236 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe461c180 0x5ffffffffc8c3830

def z237 : W := mkw 0x02800401210e102a 0x005000802421c205 0xbe400c07e01e027f 0x37c80180fc03c04f

def z238 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xfffc0fffff807f85 0xffff81fffff00ff0

def z239 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xa0200264800043fc 0x1404004c9000087f

def z240 : W := mkw 0x0000000000000000 0x0000000000000000 0x6020038000007c04 0x0c04007000000f80

def z241 : W := mkw 0x0200000900843222 0x0040000120108644 0xef44001f039c3267 0xbde88003e073864c

def z242 : W := mkw 0x02800409218e322a 0x005000812431c645 0x00000000039c3000 0x8000000000738600

def z243 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x00aa32600463c3ff 0x6015464c008c787f

def z244 : W := mkw 0x5a03ee87097f5462 0x2b407dd0e12fea8c 0x7df3ff87187ffc66 0xefbe7ff0e30fff8c

def z245 : W := mkw 0x02800409218e322a 0x005000812431c645 0xffce3c1fe7ffb27f 0xfff9c783fcfff64f

def z246 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x5fdffd9b60000000 0x0bfbffb36c000000

def z247 : W := mkw 0x5202d2a788745462 0x0a405a54f10e8a8c 0xfffbf3e7987c7c66 0xffff7e7cf30f8f8c

def z248 : W := mkw 0x5202c28708541422 0x0a405850e10a8284 0x6dd3c387181c3c00 0x8dba7870e3038780

def z249 : W := mkw 0x4282828f20a4766a 0x08505051e4148ecd 0xe020039fe0007e7c 0x1c040073fc000fcf

def z250 : W := mkw 0x181f7e249f5b0000 0x6303efc493eb6000 0xbfdffe649fff8003 0xf7fbffcc93fff000

def z251 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff440c1fe39c3000 0x9fe88183fc738600

def z252 : W := mkw 0x02800409218e322a 0x005000812431c645 0x1f440c00039e327f 0xa3e881800073c64f

def z253 : W := mkw 0x081d2c00170b0000 0x6103a58002e16000 0x00040c0003800000 0x0000818000700000

def z254 : W := mkw 0x01021624812ac0d1 0x002042c49025581a 0xbfee3e6487ffc3ff 0xf7fdc7cc90fff87f

def z255 : W := mkw 0x02800409218e322a 0x005000812431c645 0x9e040c1fe39e027b 0x13c08183fc73c04f

def z256 : W := mkw 0xe40293fec0802b04 0x1c80527fd8100560 0xe02003ffe0007f84 0x1c04007ffc000ff0

def z257 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x0cb3c387187c4c62 0x41967870e30f898c

def z258 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x83dc00781f800381 0xf07b800f03f00070

def z259 : W := mkw 0x101d680008500000 0x6203ad00010a0000 0x1fdffc00187c0002 0xe3fbff80030f8000

def z260 : W := mkw 0xa41d3978d6802b04 0x7483a72f1ad00560 0xf3fc3ff8ff807f85 0xfe7f87ff1ff00ff0

def z261 : W := mkw 0x5602c28f1ef47f66 0x0ac05851e3de8fec 0x6df3c3871ffc7fe7 0xedbe7870e3ff8ffc

def z262 : W := mkw 0xe69fbffff78e3b2e 0x7cd3f7fffef1c765 0xffffffffff9e7fff 0xfffffffffff3cfff

def z263 : W := mkw 0x02800409218e322a 0x005000812431c645 0xf2040c1fe382327d 0x1e408183fc70464f

def z264 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x499ffffb60000000 0x0933ffff6c000000

def z265 : W := mkw 0x1a9d6c093fdf322a 0x6353ad8127fbe645 0xff55cc1ffb9e327f 0xbfeab983ff73c64f

def z266 : W := mkw 0x028000092084322a 0x0050000124108645 0xf640001fe002327f 0x3ec80003fc00464f

def z267 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0xbffffe601fffc387 0xf7ffffcc03fff870

def z268 : W := mkw 0x00800400210a0008 0x0010008004214001 0x10000c00e0020018 0x020001801c004003

def z269 : W := mkw 0x581fea861e714440 0x6b03fd50c3ce2888 0x00bbf3801c61cc00 0x40177e70038c3980

def z270 : W := mkw 0x0000000000000000 0x0000000000000000 0x6140000000003004 0xac28000000000600

def z271 : W := mkw 0x0000000000000000 0x0000000000000000 0x00b0038018004c00 0x4016007003000980

def z272 : W := mkw 0x001c000016000000 0x4003800002c00000 0x020c000007800001 0x0041800000f00000

def z273 : W := mkw 0xe41da9da56802b04 0x7c83b53b4ad00560 0xebfdcffb7f807f85 0xfd7fb9ff6ff00ff0

def z274 : W := mkw 0xe41fbbfed6802b04 0x7c83f77fdad00560 0xffdfffffe7800381 0x1ffbfffffcf00070

def z275 : W := mkw 0x781ffea6df5b0000 0x6f03ffd4dbeb6000 0x1fdffc07ffff8003 0xe3fbff80fffff000

def z276 : W := mkw 0x0000000000000000 0x0000000000000000 0x16ca300000000000 0x02d9460000000000

def z277 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xe09bf3ffe0000000 0x1c137e7ffc000000

def z278 : W := mkw 0x801c015000000000 0x5003802a00000000 0x820c007800000000 0x1041800f00000000

def z279 : W := mkw 0x02800409218e322a 0x005000812431c645 0xe9040c1fe39c327c 0x9d208183fc73864f

def z280 : W := mkw 0x4200808300041422 0x0840101060008284 0x4000018300003c00 0x0800003060000780

def z281 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x7df3f387987ffc7e 0xefbe7e70f30fff8f

def z282 : W := mkw 0x0102122c80a0e2d1 0x0020424590141c5a 0xf7ee327c87e3f3ff 0xfefdc64f90fc7e7f

def z283 : W := mkw 0x03821625a12ed0fb 0x007042c4b425da1f 0x1c023c07e07f807a 0x03804780fc0ff00f

def z284 : W := mkw 0xf81ffff6df5b0000 0x7f03fffedbeb6000 0x1fdfffe01fff8003 0xe3fbfffc03fff000

def z285 : W := mkw 0xe41fbbfed6802b04 0x7c83f77fdad00560 0xe3fff3f81f807f85 0xfc7ffe7f03f00ff0

def z286 : W := mkw 0x879e177db7aefbff 0x50f3c2efb6f5df7f 0xfffe3fffffffffff 0xffffc7ffffffffff

def z287 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x6dfbf3e71c7dfde6 0xedbf7e7ce38fbfbc

def z288 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xa2ec027807804385 0x745d804f00f00870

def z289 : W := mkw 0xe00293f6c0000000 0x1c00527ed8000000 0x000003e000000000 0x0000007c00000000

def z290 : W := mkw 0x00000400010a0000 0x0000008000214000 0x09040c00039c0000 0x8120818000738000

def z291 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x413401981f807f85 0xe826803303f00ff0

def z292 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x1fdfffe000000000 0x03fbfffc00000000

def z293 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c000c07e0000000 0x03800180fc000000

def z294 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x0dd3c007187c0062 0xe1ba7800e30f800c

def z295 : W := mkw 0x869c0559378e3b2e 0x50d380ab26f1c765 0xff4c0c7fe79e33ff 0xbfe9818ffcf3c67f

def z296 : W := mkw 0x5282c687297e546a 0x0a5058d0e52fca8d 0x7df3cf87f87e7c7e 0xefbe79f0ff0fcf8f

def z297 : W := mkw 0x801c015800802200 0x5003802b00100440 0xe3dc03f803803205 0xbc7b807f00700640

def z298 : W := mkw 0x181d68001e510000 0x6303ad0003ca2000 0x1fdffc001c618000 0x43fbff80038c3000

def z299 : W := mkw 0x0000000000000000 0x0000000000000000 0x01d0000018000000 0xe03a000003000000

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000002027f 0x200000000000404f

def z301 : W := mkw 0x1200400108541422 0x02400800210a8284 0x00000000181c3c00 0x8000000003038780

def z302 : W := mkw 0x08000400170b0000 0x0100008002e16000 0x0000000007838001 0x0000000000f07000

def z303 : W := mkw 0xd61cc1db1ed43f26 0x5ac3983b63da87e4 0x4915c19b1b9c3c00 0x8922b83363738780

def z304 : W := mkw 0x00000400010a0000 0x0000008000214000 0xbf440c04839e027f 0xb7e881809073c04f

def z305 : W := mkw 0x430292a78024d4f3 0x08605254f0049a9e 0xe02003e780007ffc 0x1c04007cf0000fff

def z306 : W := mkw 0x9d1f7f7c9ffbebd5 0x73a3efef93ff7d7a 0xfffffffc9fffffff 0xffffffff93ffffff

def z307 : W := mkw 0xe01fabd640000000 0x7c03f57ac8000000 0x6dd7cf9f60000000 0x0dbaf9f3ec000000

def z308 : W := mkw 0x849c0558378a2b0c 0x509380ab06f14561 0xf3fc0ff8ff827f9d 0xfe7f81ff1ff04ff3

def z309 : W := mkw 0xf81ffbf6de510000 0x7f03ff7edbca2000 0x009bf3e01c618000 0x40137e7c038c3000

def z310 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xfffffffff8007c04 0xffffffffff000f80

def z311 : W := mkw 0x581fee861f5b0000 0x6b03fdd0c3eb6000 0x7fdfff871fff8003 0xeffbfff0e3fff000

def z312 : W := mkw 0x001c000016000000 0x4003800002c00000 0x03dc00001f800001 0xe07b800003f00000

def z313 : W := mkw 0x191f7a249e71c0d1 0x6323ef4493ce381a 0xb6fbf2649c63c3ff 0x76df7e4c938c787f

def z314 : W := mkw 0x6003baa6c0000000 0x2c007754d8000000 0x0003f00000000000 0x00007e0000000000

def z315 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xffee3e7fe463c3ff 0x7ffdc7cffc8c787f

def z316 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x2ce3c207007c4066 0x659c7840e00f880c

def z317 : W := mkw 0xe01fbff6c10a0000 0x7c03f7fed8214000 0xffdfffffe39e0003 0xbffbfffffc73c000

def z318 : W := mkw 0x02800409218e322a 0x005000812431c645 0xdb040c1be39e3219 0x9b6081837c73c643

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0x4110018018003c00 0x8822003003000780

def z320 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x4d13c187187c3c62 0x89a27830e30f878c

def z321 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x00b803e01f807f85 0xe017007c03f00ff0

def z322 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xfff3c387987e7e7f 0xfffe7870f30fcfcf

def z323 : W := mkw 0xe11fbbf6c0008091 0x7c23f77ed8001012 0xffdfffffe4038399 0x1ffbfffffc807073

def z324 : W := mkw 0x001d280016000000 0x6003a50002c00000 0x1fdffc001f800001 0xe3fbff8003f00000

def z325 : W := mkw 0x5282c68f29fe766a 0x0a5058d1e53fcecd 0x6df7cf9f7bfc7c66 0xedbef9f3ef7f8f8c

def z326 : W := mkw 0x0000000000000000 0x0000000000000000 0x02c8000004000001 0x6059000000800000

def z327 : W := mkw 0x081d2c00170b0000 0x6103a58002e16000 0x1f4c3c00079f8003 0xa3e9878000f3f000

def z328 : W := mkw 0x00000400010a0000 0x0000008000214000 0xff440c1fe39e0003 0xbfe88183fc73c000

def z329 : W := mkw 0xf29fffffe9fe766a 0x7e53fffffd3fcecd 0xfffffffffbfe7e7f 0xffffffffff7fcfcf

def z330 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb22832648403c3fd 0x1645064c9080787f

def z331 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x0c23c007187c7c66 0xe1847800e30f8f8c

def z332 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x0011c18000000000 0x0002383000000000

def z333 : W := mkw 0x8680015920843b2e 0x10d0002b24108765 0xe02003ffe0007ffc 0x1c04007ffc000fff

def z334 : W := mkw 0x851e13749620c9d5 0x50a3c26e92c4193a 0xb6fa33e49c63cfff 0x76df467c938c79ff

def z335 : W := mkw 0xe00293f6c0000000 0x1c00527ed8000000 0xedd3c3ffe0000000 0x1dba787ffc000000

def z336 : W := mkw 0x001d280000000000 0x6003a50000000000 0x1fdffc0004638003 0x63fbff80008c7000

def z337 : W := mkw 0x101c40001e500000 0x4203880003ca0000 0x0fdfc0001ffc0003 0xe1fbf80003ff8000

def z338 : W := mkw 0x0502122c96a0ebd5 0x00a0424592d41d7a 0xb6ea32649fe3ffff 0xf6dd464c93fc7fff

def z339 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb6ca32648063807a 0x16d9464c900c700f

def z340 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x16ea32600463c183 0x62dd464c008c7830

def z341 : W := mkw 0x5a02c6871f7f5462 0x0b4058d0e3efea8c 0x6df3c3871ffffc67 0xedbe7870e3ffff8c

def z342 : W := mkw 0x869c0559378e3b2e 0x50d380ab26f1c765 0xff540d9ffb9e3e7f 0xbfea81b3ff73c7cf

def z343 : W := mkw 0x0200000100041022 0x0040000020008204 0x6df00387181c7c66 0xedbe0070e3038f8c

def z344 : W := mkw 0x081d2c00170b0000 0x6103a58002e16000 0x13dc3c001f838001 0xe27b878003f07000

def z345 : W := mkw 0x00800408218a2208 0x0010008104314441 0xff440c1fe3820219 0x1fe88183fc704043

def z346 : W := mkw 0x001c000016000000 0x4003800002c00000 0x17de30001fe38003 0xe2fbc60003fc7000

def z347 : W := mkw 0x0000000000000000 0x0000000000000000 0x0dd3c00000000000 0x01ba780000000000

def z348 : W := mkw 0x5382d6afa9fef6fb 0x0a705ad5f53fdedf 0xffffffffffffffff 0xffffffffffffffff

def z349 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xa0aa32648461c3fc 0x5415464c908c387f

def z350 : W := mkw 0x1a8044093fdf322a 0x0350088127fbe645 0xff440c1fffffb27f 0xffe88183fffff64f

def z351 : W := mkw 0x0002122480000000 0x0000424490000000 0x008a326000000000 0x0011464c00000000

def z352 : W := mkw 0xe00293f6c0000000 0x1c00527ed8000000 0xf6ca33ffe0000000 0x1ed9467ffc000000

def z353 : W := mkw 0xfa9fffffffdf322a 0x7f53fffffffbe645 0xffdfffffffffb27f 0xfffbfffffffff64f

def z354 : W := mkw 0x02800409218e322a 0x005000812431c645 0x6d400007039e327f 0xada80000e073c64f

def z355 : W := mkw 0x010000000020c0d1 0x002000000004181a 0x002000000461c180 0x40040000008c3830

def z356 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x4dd3c183187c3c02 0xe9ba7830630f8780

def z357 : W := mkw 0x841e035c16a06b44 0x5083c06b82d40d68 0xe7fe03fc1fe07fe7 0xfcffc07f83fc0ffc

def z358 : W := mkw 0x6001a88240000000 0x2c00351048000000 0x0801cc0360000000 0x010039806c000000

def z359 : W := mkw 0x180044001f5b0000 0x0300088003eb6000 0x16ca30001fff8003 0xe2d9460003fff000

def z360 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x009bf0001fff8003 0xe0137e0003fff000

def z361 : W := mkw 0x18016c00095b0000 0x23002d80012b6000 0x1f47fc0003ff8003 0xa3e8ff80007ff000

def z362 : W := mkw 0x0002122480000000 0x0000424490000000 0xb6ca32648002027f 0x36d9464c9000404f

def z363 : W := mkw 0xf81dedd25f5b0000 0x7f03bdba4beb6000 0x4915cd9b7b9c0000 0x8922b9b36f738000

def z364 : W := mkw 0xf21de9d348541422 0x7e43bd3a690a8284 0x4915cd9b781c3c00 0x8922b9b36f038780

def z365 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe00043fc 0x1ffffffffc00087f

def z366 : W := mkw 0x9c1d69501e510904 0x7383ad2a03ca2120 0x00bbf3e01c61cd80 0x40177e7c038c39b0

def z367 : W := mkw 0x9c1c45581fdb2b04 0x538388ab03fb6560 0xe3fc03f81fffff87 0xfc7f807f03fffff0

def z368 : W := mkw 0x1a9d6c013f5f102a 0x6353ad8027ebe205 0x1fdffc07ffff807b 0xe3fbff80fffff00f

def z369 : W := mkw 0x010000000020c0d1 0x002000000004181a 0xb66000048463c3ff 0x76cc0000908c787f

def z370 : W := mkw 0x0000000000000000 0x0000000000000000 0x1640000000020003 0x22c8000000004000

def z371 : W := mkw 0x8c1d2d58178b2b04 0x7183a5ab02f16560 0xf3fc3ff81f83ff85 0xfe7f87ff03f07ff0

def z372 : W := mkw 0x851e137c96a0ebd5 0x50a3c26f92d41d7a 0xb6ee327c87e3c3ff 0x76ddc64f90fc787f

def z373 : W := mkw 0x0000000800802200 0x0000000100100440 0x8204001803800201 0x1040800300700040

def z374 : W := mkw 0x0200000100041022 0x0040000020008204 0xff440c1fe01c3066 0xbfe88183fc03860c

def z375 : W := mkw 0x829c0559218e322a 0x505380ab2431c645 0xffdc0fffe39e327f 0xbffb81fffc73c64f

def z376 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0xff55cd9fe0000000 0x1feab9b3fc000000

def z377 : W := mkw 0x5a1fea871e755462 0x6b43fd50e3ceaa8c 0x6dfbf3871c7dfc66 0xedbf7e70e38fbf8c

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00000048000027c 0x140000009000004f

def z379 : W := mkw 0x961c41591ef47f66 0x52c3882b23de8fec 0xe3fc03f81ffc7fe7 0xfc7f807f03ff8ffc

def z380 : W := mkw 0x02800409218e322a 0x005000812431c645 0xe3440018039e327f 0xbc6880030073c64f

def z381 : W := mkw 0x869c0559378e3b2e 0x50d380ab26f1c765 0xebfc0ffb7f9c7f85 0xfd7f81ff6ff38ff0

def z382 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020000004004385 0x6004000000800870

def z383 : W := mkw 0x0000000800802200 0x0000000100100440 0xe3ec027807807385 0xfc7d804f00f00e70

def z384 : W := mkw 0xf81ffff6c95b0000 0x7f03fffed92b6000 0xffdfffffe07f8002 0x1ffbfffffc0ff000

def z385 : W := mkw 0x811e13748020c0d1 0x5023c26e9004181a 0xf7fe33fc8463c3ff 0x7effc67f908c787f

def z386 : W := mkw 0x0202020500245062 0x00404040a0048a0c 0x6de20207007c7066 0xedbc4040e00f8e0c

def z387 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffdfffffe063807a 0x1ffbfffffc0c700f

def z388 : W := mkw 0x6283bea7e10e102a 0x2c5077d4fc21c205 0x1c03fc07e01e007a 0x03807f80fc03c00f

def z389 : W := mkw 0x4202828700245462 0x08405050e0048a8c 0x64e2038700607c66 0x6c9c4070e00c0f8c

def z390 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x0915cc001fff8003 0xe122b98003fff000

def z391 : W := mkw 0x1000400008704440 0x02000800010e0888 0x0020000018604c00 0x40040000030c0980

def z392 : W := mkw 0x180044001f5b0000 0x0300088003eb6000 0x1f440c001fff8003 0xe3e8818003fff000

def z393 : W := mkw 0x00800408218a2208 0x0010008104314441 0x00040c1863800000 0x000081830c700000

def z394 : W := mkw 0x130040010874d4f3 0x02600800210e9a9e 0x002000001c7fffff 0xe0040000038fffff

def z395 : W := mkw 0x02800409218e322a 0x005000812431c645 0xffec0e7fe79e73ff 0xfffd81cffcf3ce7f

def z396 : W := mkw 0xe21fbbf7c0041022 0x7c43f77ef8008204 0xffdfffffe01c3066 0xbffbfffffc03860c

def z397 : W := mkw 0xd21ec3d708745462 0x5a43d87ae10e8a8c 0xefffc3ff187c7c66 0xfdfff87fe30f8f8c

def z398 : W := mkw 0x4002828600000000 0x08005050c0000000 0x6df3c38718007c04 0xedbe7870e3000f80

def z399 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe0b803f81c007f84 0x5c17007f03800ff0

def z400 : W := mkw 0x4002828600000000 0x08005050c0000000 0x6000038700000000 0x0c000070e0000000

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0x04c2000000600002 0x60984000000c0000

def z402 : W := mkw 0x08012c00010b0000 0x2100258000216000 0x10003c0000038000 0x0200078000007000

def z403 : W := mkw 0xc61e83df16a47f66 0x58c3d07be2d48fec 0xe3fc03ff1f807fe5 0xfc7f807fe3f00ffc

def z404 : W := mkw 0x9c1d6d581fdb2b04 0x7383adab03fb6560 0xebfdcff81f9c7f85 0xfd7fb9ff03f38ff0

def z405 : W := mkw 0x8400015800802b04 0x1080002b00100560 0xe36403f803807f85 0xbc6c807f00700ff0

def z406 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb42232648063c3fe 0x1684464c900c787f

def z407 : W := mkw 0x02800401210e102a 0x005000802421c205 0x1f440c07e39e007b 0xa3e88180fc73c00f

def z408 : W := mkw 0x0102122480008091 0x0020424490001012 0xb6ca326484038399 0x16d9464c90807073

def z409 : W := mkw 0x00800408218a2208 0x0010008104314441 0xb6440c1ce382027f 0x36c881839c70404f

def z410 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xb6fbf3e48463c3ff 0x76df7e7c908c787f

def z411 : W := mkw 0x9c1d6d581fdb2b04 0x7383adab03fb6560 0x9fdffc781fff8383 0xf3fbff8f03fff070

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0xff440c1fe002027f 0x3fe88183fc00404f

def z413 : W := mkw 0x1000400008500000 0x02000800010a0000 0x0093c00018600000 0x40127800030c0000

def z414 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x099ffc001ffd8000 0xc133ff8003ffb000

def z415 : W := mkw 0x03801429a18eb2bb 0x007002853431d657 0xff4c3c7fe79fb3ff 0xbfe9878ffcf3f67f

def z416 : W := mkw 0x841c015016000904 0x5083802a02c00120 0x03fc03e01f804d81 0xe07f807c03f009b0

def z417 : W := mkw 0x851e137c96a0ebd5 0x50a3c26f92d41d7a 0xe3fe33f81fe1ff85 0xfc7fc67f03fc3ff0

def z418 : W := mkw 0x0382162da1aef2fb 0x007042c5b435de5f 0xff640e7fe39e73ff 0xbfec81cffc73ce7f

def z419 : W := mkw 0x0100102080008091 0x0020020410001012 0x8000006080000398 0x1000000c10000073

def z420 : W := mkw 0x181d68001e510000 0x6303ad0003ca2000 0x0ddbf0001c7d8002 0xe1bb7e00038fb000

def z421 : W := mkw 0x5002c28608704440 0x0a005850c10e0888 0x61f3c38018607c04 0xec3e7870030c0f80

def z422 : W := mkw 0x5282c68f29fe766a 0x0a5058d1e53fcecd 0xff47cc1fe3fe327f 0xbfe8f983fc7fc64f

def z423 : W := mkw 0x130252258874d4f3 0x02604a44b10e9a9e 0xb6ea32649c7fffff 0xf6dd464c938fffff

def z424 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xf7fc03fc9f827fff 0xfeff807f93f04fff

def z425 : W := mkw 0xe39fbfffe1aef2fb 0x7c73f7fffc35de5f 0xffffffffe7fff3ff 0xfffffffffcfffe7f

def z426 : W := mkw 0x0382122da0a4f2fb 0x00704245b4149e5f 0xf6ea327fe463f3ff 0x7edd464ffc8c7e7f

def z427 : W := mkw 0x0200000100245462 0x0040000020048a8c 0x0020000000007c64 0x0004000000000f8c

def z428 : W := mkw 0xe01fbbf6d6000000 0x7c03f77edac00000 0xffdfffffff800001 0xfffbfffffff00000

def z429 : W := mkw 0x4002828600000000 0x08005050c0000000 0x0093c38000000000 0x0012787000000000

def z430 : W := mkw 0xe41e93fed6802b04 0x5c83d27fdad00560 0xe3fc03ffff807f85 0xfc7f807ffff00ff0

def z431 : W := mkw 0x1b9f7e2dbffff2fb 0x6373efc5b7fffe5f 0xfffffe7ffffff3ff 0xffffffcffffffe7f

def z432 : W := mkw 0x869c0559378e3b2e 0x50d380ab26f1c765 0xe3fc03f81f9e7fff 0xfc7f807f03f3cfff

def z433 : W := mkw 0x0400000816802b04 0x0080000102d00560 0xa2e802601f807f85 0xf45d004c03f00ff0

def z434 : W := mkw 0x5282c28f28f4766a 0x0a505851e51e8ecd 0xedf3c39ff87c7e7e 0xfdbe7873ff0f8fcf

def z435 : W := mkw 0xa01d3970c0000000 0x7403a72e18000000 0xf3dc3ff8e0000000 0x1e7b87ff1c000000

def z436 : W := mkw 0x841c015016000904 0x5083802a02c00120 0x0008006004000180 0x0001000c00800030

def z437 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb6ea32648461c180 0x56dd464c908c3830

def z438 : W := mkw 0x02800401210e102a 0x005000802421c205 0xff440c1fe01e007a 0x1fe88183fc03c00f

def z439 : W := mkw 0xd61cc1db1ed43f26 0x5ac3983b63da87e4 0xebfdc3fb1f9c7f85 0xfd7fb87f63f38ff0

def z440 : W := mkw 0x0500000816a0ebd5 0x00a0000102d41d7a 0x002000001fe3ffff 0xe004000003fc7fff

def z441 : W := mkw 0x1200400108745462 0x02400800210e8a8c 0x61f00380187c7c66 0xec3e0070030f8f8c

def z442 : W := mkw 0x4000808200000000 0x0800101040000000 0x4911c18300000000 0x0922383060000000

def z443 : W := mkw 0x8400015800802b04 0x1080002b00100560 0xe1f003f818007f84 0xfc3e007f03000ff0

def z444 : W := mkw 0x801c015000000000 0x5003802a00000000 0xe3fc03f804004385 0x7c7f807f00800870

def z445 : W := mkw 0x0282060d21ae726a 0x005040c1a435ce4d 0xffe60e1fe3fe727f 0xfffcc1c3fc7fce4f

def z446 : W := mkw 0x8400015800802b04 0x1080002b00100560 0x8000007800000380 0x1000000f00000070

def z447 : W := mkw 0xe01e93f6c0000000 0x5c03d27ed8000000 0xe3dc03ffe0000000 0x1c7b807ffc000000

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020000018007c04 0xe004000003000f80

def z449 : W := mkw 0x010010208020c0d1 0x002002041004181a 0x922830608463c3ff 0x7245060c108c787f

def z450 : W := mkw 0x0000000000000000 0x0000000000000000 0x6d40000700000000 0x0da80000e0000000

def z451 : W := mkw 0xc60283df00a47f66 0x18c0507be0148fec 0xe02003ff00007fe4 0x1c04007fe0000ffc

def z452 : W := mkw 0x801c015000000000 0x5003802a00000000 0xe3fc03f818007c04 0xfc7f807f03000f80

def z453 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1f55cc001b9e0003 0xa3eab9800373c000

def z454 : W := mkw 0xe41fbbf6d6000904 0x7c83f77edac00120 0xfffffffffc004d80 0x5fffffffff8009b0

def z455 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xa02002648463c3ff 0x7404004c908c787f

def z456 : W := mkw 0xb81d7d70df5b0000 0x7703afae1beb6000 0x9fdffc78ffff8003 0xf3fbff8f1ffff000

def z457 : W := mkw 0x181d68001e510000 0x6303ad0003ca2000 0x16dbf0001c638003 0x62db7e00038c7000

def z458 : W := mkw 0xe10293f6c020c0d1 0x1c20527ed804181a 0xe02003ffe00043fc 0x1c04007ffc00087f

def z459 : W := mkw 0x869c015936843b2e 0x50d3802b26d08765 0xe3fc03ffff807ffd 0xfc7f807ffff00fff

def z460 : W := mkw 0x001d280000000000 0x6003a50000000000 0x009bf00000000000 0x00137e0000000000

def z461 : W := mkw 0x7803fea6c95b0000 0x2f007fd4d92b6000 0x1c03fc07e07f8002 0x03807f80fc0ff000

def z462 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe35401981b803e05 0xbc6a8033037007c0

def z463 : W := mkw 0x0382162da1aef2fb 0x007042c5b435de5f 0xff463c1fe3ffb27f 0xbfe8c783fc7ff64f

def z464 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1c9bfc001c7f8002 0x43937f80038ff000

def z465 : W := mkw 0x0000000000000000 0x0000000000000000 0xb640000480000000 0x16c8000090000000

def z466 : W := mkw 0xf31ffbf7c874d4f3 0x7e63ff7ef90e9a9e 0xfffffffffc7fffff 0xffffffffff8fffff

def z467 : W := mkw 0x001c0400170a0000 0x4003808002e14000 0x1fdc0c001f9e0003 0xe3fb818003f3c000

def z468 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xf20c3fffe0000000 0x1e4187fffc000000

def z469 : W := mkw 0x0400000816802b04 0x0080000102d00560 0x61f003801f807f85 0xec3e007003f00ff0

def z470 : W := mkw 0x801e137480000000 0x5003c26e90000000 0xf7de33fc80000000 0x1efbc67f90000000

def z471 : W := mkw 0x089d2c08378b2208 0x6113a58106f16441 0x920c3c18e7838219 0x124187831cf07043

def z472 : W := mkw 0x0400000016000904 0x0080000002c00120 0x002000001c004d80 0x40040000038009b0

def z473 : W := mkw 0xa01d3970c0000000 0x7403a72e18000000 0x0008306000000000 0x0001060c00000000

def z474 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x24ea32640461c1e6 0x649d464c808c383c

def z475 : W := mkw 0x0002020400204040 0x0000404080040808 0x36ea32040463c067 0x66dd4640808c780c

def z476 : W := mkw 0x081d2c00170b0000 0x6103a58002e16000 0x1fdffc0007838001 0x03fbff8000f07000

def z477 : W := mkw 0x5002c28608704440 0x0a005850c10e0888 0x6df3c38718604c00 0x4dbe7870e30c0980

def z478 : W := mkw 0x5002c28608500000 0x0a005850c10a0000 0x6dd3c387187c0002 0xedba7870e30f8000

def z479 : W := mkw 0xa11f3b74c020c0d1 0x7423e76e9804181a 0xb6ee3e7ce463c3ff 0x76ddc7cf9c8c787f

def z480 : W := mkw 0x091d3c20970b8091 0x6123a78412e17012 0x920c3c6087838399 0x1241878c10f07073

def z481 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x1c03f007807f807a 0x03807e00f00ff00f

def z482 : W := mkw 0x4002828600204040 0x08005050c0040808 0x6df3c38700604066 0x6dbe7870e00c080c

def z483 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x929ffff8e0000000 0x1253ffff1c000000

def z484 : W := mkw 0x0000000800802200 0x0000000100100440 0x0000000003803205 0xa000000000700640

def z485 : W := mkw 0x0000000000000000 0x0000000000000000 0xb6ea32600463c387 0x76dd464c008c7870

def z486 : W := mkw 0x6103baa6c020c0d1 0x2c207754d804181a 0x1c03fc07e063807a 0x03807f80fc0c700f

def z487 : W := mkw 0x5a1dec831f5f1422 0x6b43bd9063ebe284 0x4915cd831b9c3c00 0x8922b9b063738780

def z488 : W := mkw 0x001c000000000000 0x4003800000000000 0x03dc000000000000 0x007b800000000000

def z489 : W := mkw 0x02800401210e102a 0x005000802421c205 0x7d400c07e01e307e 0xafa80180fc03c60f

def z490 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1b1dfc001f9f8001 0x8363bf8003f3f000

def z491 : W := mkw 0x0000000000204040 0x0000000000040808 0x0020000000604066 0x60040000000c080c

def z492 : W := mkw 0x180044001f5b0000 0x0300088003eb6000 0x000000001b9c0000 0x8000000003738000

def z493 : W := mkw 0x0000000000000000 0x0000000000000000 0x00a8026004004180 0x4015004c00800830

def z494 : W := mkw 0x028000092084322a 0x0050000124108645 0xe344001fe380327d 0xbc688003fc70064f

def z495 : W := mkw 0x029d2c09218e322a 0x6053a5812431c645 0xffdffc1fe39e327f 0xbffbff83fc73c64f

def z496 : W := mkw 0x0000000000000000 0x0000000000000000 0x0344000003800001 0xa068800000700000

def z497 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0x00bbf3e00461c180 0x40177e7c008c3830

def z498 : W := mkw 0x601fbaa6c0000000 0x6c03f754d8000000 0x1fdffc07e0000000 0x03fbff80fc000000

def z499 : W := mkw 0x181f6e041f7b4040 0x6303edc083ef6808 0x3ffffe041fffc067 0xe7ffffc083fff80c

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0xb6e80264840243ff 0x76dd004c9080487f

def z501 : W := mkw 0x841c015016000904 0x5083802a02c00120 0xe3fc03f81c004d80 0x5c7f807f038009b0

def z502 : W := mkw 0x0001280000000000 0x2000250000000000 0x1c03fc0000000000 0x03807f8000000000

def z503 : W := mkw 0x03821625a12ed0fb 0x007042c4b425da1f 0xbeea3e67e47fc3ff 0x77dd47ccfc8ff87f

def z504 : W := mkw 0x941c41581ed02b04 0x5283882b03da0560 0xefffc3f81ffc7f87 0xfdfff87f03ff8ff0

def z505 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1d17fc001bff8002 0x83a2ff80037ff000

def z506 : W := mkw 0x02800409218e322a 0x005000812431c645 0xeb440c1b639c3205 0xbd6881836c738640

def z507 : W := mkw 0x010202040020c0d1 0x002040408004181a 0x24e202040463c3ff 0x649c4040808c787f

def z508 : W := mkw 0x0000000000000000 0x0000000000000000 0x20e0020000004004 0x641c004000000800

def z509 : W := mkw 0x0000000000000000 0x0000000000000000 0x2440000400000066 0x248800008000000c

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3f803e01c007f85 0xfc7f007c03800ff0

def z511 : W := mkw 0xa11d3970c0008091 0x7423a72e18001012 0x920c3c78e4038399 0x1241878f1c807073

def z512 : W := mkw 0xe00293f6c0000000 0x1c00527ed8000000 0xff440fffe0000000 0x1fe881fffc000000

def z513 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x16ca30048463807b 0x62d94600908c700f

def z514 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x43dc01981f803c01 0xe87b803303f00780

def z515 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x0004001803800000 0x0000800300700000

def z516 : W := mkw 0x081d280016010000 0x6103a50002c02000 0x0008300004018000 0x0001060000803000

def z517 : W := mkw 0x0400000800802b04 0x0080000100100560 0x0020000000007f84 0x0004000000000ff0

def z518 : W := mkw 0x1c0044081fdb2b04 0x0380088103fb6560 0x002000001fffff87 0xe004000003fffff0

def z519 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe3dc03f807800381 0x1c7b807f00f00070

def z520 : W := mkw 0x18016c00095b0000 0x23002d80012b6000 0x0801cc00001c0000 0x0100398000038000

def z521 : W := mkw 0x841c0558178a2b04 0x508380ab02f14560 0xfffc0ff81f9e7f87 0xffff81ff03f3cff0

def z522 : W := mkw 0x801c015000000000 0x5003802a00000000 0xffdc0fffe0000000 0x1ffb81fffc000000

def z523 : W := mkw 0x1a9d6c093fdf322a 0x6353ad8127fbe645 0x1fdffc001fffb27f 0xe3fbff8003fff64f

def z524 : W := mkw 0x029c0409378e322a 0x4053808126f1c645 0xffdc0c1fff9e327f 0xfffb8183fff3c64f

def z525 : W := mkw 0xc41e83de16802b04 0x5883d07bc2d00560 0xefffc3ff1f807f85 0xfdfff87fe3f00ff0

def z526 : W := mkw 0x5a1dec831f5f1422 0x6b43bd9063ebe284 0x5fdffd831fffbc03 0xebfbffb063fff780

def z527 : W := mkw 0x7203faa7c8745462 0x2e407f54f90e8a8c 0x1c03fc07e07c0062 0x03807f80fc0f800c

def z528 : W := mkw 0x851c015816a0ebd5 0x50a3802b02d41d7a 0xe3fc03f81fe3ffff 0xfc7f807f03fc7fff

def z529 : W := mkw 0x4002828600000000 0x08005050c0000000 0xffd7cf9fe0000000 0x1ffaf9f3fc000000

def z530 : W := mkw 0x4202828700041022 0x08405050e0008204 0x6dd3c387001c3066 0xadba7870e003860c

def z531 : W := mkw 0x5282c68f29fe766a 0x0a5058d1e53fcecd 0x6df3c3871bfe7e7f 0xedbe7870e37fcfcf

def z532 : W := mkw 0x4202828700245462 0x08405050e0048a8c 0x6df3c38700007c64 0x0dbe7870e0000f8c

def z533 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xbeebf267847fc3ff 0x77dd7e4cf08ff87f

def z534 : W := mkw 0x400292a680000000 0x08005254d0000000 0xffdbf3e780000000 0x1ffb7e7cf0000000

def z535 : W := mkw 0x0200000100041022 0x0040000020008204 0x0c000007001c0062 0x01800000e003800c

def z536 : W := mkw 0xfa1ffff7df7f5462 0x7f43fffefbefea8c 0xfffffffffffffc67 0xffffffffffffff8c

def z537 : W := mkw 0x0002020400204040 0x0000404080040808 0xa6ea0264046043e7 0x74dd404c808c087c

def z538 : W := mkw 0xf21febd748745462 0x7e43fd7ae90e8a8c 0x6df7cf9f787c7c66 0xedbef9f3ef0f8f8c

def z539 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x34e232048063c07e 0x669c4640900c780f

def z540 : W := mkw 0xf21ffbf7c8745462 0x7e43ff7ef90e8a8c 0xffdfffffe07c0062 0x1ffbfffffc0f800c

def z541 : W := mkw 0x190044001f7bc0d1 0x0320088003ef781a 0x002000001fffc3ff 0xe004000003fff87f

def z542 : W := mkw 0x0002122480000000 0x0000424490000000 0xa000026480000000 0x1400004c90000000

def z543 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xc31c01f81f803f81 0x9863803f03f007f0

def z544 : W := mkw 0x0002020400204040 0x0000404080040808 0x65f2038418607c66 0xecbe4070830c0f8c

def z545 : W := mkw 0x1a816c01295f102a 0x23502d80252be205 0x1c03fc07e07f807a 0x03807f80fc0ff00f

def z546 : W := mkw 0x4002828600000000 0x08005050c0000000 0x0c03c00700000000 0x01807800e0000000

def z547 : W := mkw 0x430292a78024d4f3 0x08605254f0049a9e 0xf6ea33e78463ffff 0x7edd467cf08c7fff

def z548 : W := mkw 0x1280440929fe766a 0x02500881253fcecd 0xff640c1ffbfe7e7f 0xffec8183ff7fcfcf

def z549 : W := mkw 0x6003baa6c0000000 0x2c007754d8000000 0x7dd3ff87e0000000 0x0fba7ff0fc000000

def z550 : W := mkw 0x091f3e24972bc0d1 0x6123e7c492e5781a 0xb6ee3e6487e3c3ff 0x76ddc7cc90fc787f

def z551 : W := mkw 0x1a816c0929df322a 0x23502d81253be645 0xff47fc1fe3ffb27f 0xbfe8ff83fc7ff64f

def z552 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x120c3c001fff8003 0xe241878003fff000

def z553 : W := mkw 0x0002122480204040 0x0000424490040808 0xb6ea326480604066 0x76dd464c900c080c

def z554 : W := mkw 0x00000400010a0000 0x0000008000214000 0x1fce3c0007ff8003 0xe3f9c78000fff000

def z555 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xf7fa33e49c63ffff 0xfeff467c938c7fff

def z556 : W := mkw 0x5a1fee871f7f5462 0x6b43fdd0e3efea8c 0x1fdffc071fff8063 0xe3fbff80e3fff00c

def z557 : W := mkw 0xe00081d240000000 0x1c00103a48000000 0x4000019b60000000 0x080000336c000000

def z558 : W := mkw 0x010000000020c0d1 0x002000000004181a 0x00200000000043fc 0x000400000000087f

def z559 : W := mkw 0x5002c28608704440 0x0a005850c10e0888 0x0003c00000600000 0x00007800000c0000

def z560 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x6ddbf3e700000000 0x0dbb7e7ce0000000

def z561 : W := mkw 0x1280440929de322a 0x02500881253bc645 0xffd7cc1ffbfe327f 0xfffaf983ff7fc64f

def z562 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x69f1c383181c7c04 0xed3e387063038f80

def z563 : W := mkw 0x1002420408704040 0x02004840810e0808 0x2df3c204187c4066 0xe5be7840830f880c

def z564 : W := mkw 0x0000000000000000 0x0000000000000000 0xe000001fe0000000 0x1c000003fc000000

def z565 : W := mkw 0xfc1ffffedfdb2b04 0x7f83ffffdbfb6560 0xffffffffffffff87 0xfffffffffffffff0

def z566 : W := mkw 0x0002020400204040 0x0000404080040808 0x00a2020000604000 0x40144040000c0800

def z567 : W := mkw 0x191d7c209f5b8091 0x6323af8413eb7012 0x9fdffc609fff839b 0xf3fbff8c13fff073

def z568 : W := mkw 0x8400015800802b04 0x1080002b00100560 0xe2e803f804007f85 0x7c5d007f00800ff0

def z569 : W := mkw 0x02800409218e322a 0x005000812431c645 0x6d440c1f639c3066 0xada88183ec73860c

def z570 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x142230048463c3ff 0x62844600908c787f

def z571 : W := mkw 0x181d6c081fdb2200 0x6303ad8103fb6440 0xffdffc181fffb207 0xfffbff8303fff640

def z572 : W := mkw 0x00000400010a0000 0x0000008000214000 0x12040c0003820001 0x0240818000704000

def z573 : W := mkw 0x0002020400204040 0x0000404080040808 0xb6e202048062427f 0x76dc4040900c484f

def z574 : W := mkw 0xd41ec3d61e704d44 0x5a83d87ac3ce09a8 0x00bbc3e01c604d80 0x4017787c038c09b0

def z575 : W := mkw 0x1200400108745462 0x02400800210e8a8c 0x6d600007187c7c66 0xedac0000e30f8f8c

def z576 : W := mkw 0x8400015000000904 0x1080002a00000120 0x002003e000004d80 0x0004007c000009b0

def z577 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x822c00781f807f85 0xf045800f03f00ff0

def z578 : W := mkw 0x841c015016000904 0x5083802a02c00120 0x61f803e01c007d84 0xec3f007c03800fb0

def z579 : W := mkw 0xd71ed3ff9ef4fff7 0x5ae3da7ff3de9ffe 0xfffff3ff9fffffff 0xfffffe7ff3ffffff

def z580 : W := mkw 0x801d295000000000 0x7003a52a00000000 0xffdffff800000000 0x1ffbffff00000000

def z581 : W := mkw 0x851e13749620c9d5 0x50a3c26e92c4193a 0x00ba33e01c61cd80 0x4017467c038c39b0

def z582 : W := mkw 0x5280c48b29de362a 0x0a501891653bc6c5 0x4915cd9b7b9c3c00 0x8922b9b36f738780

def z583 : W := mkw 0x5102d2a68870c4d1 0x0a205a54d10e189a 0x00bbf3e01c61cd80 0x40177e7c038c39b0

def z584 : W := mkw 0x02800409218e322a 0x005000812431c645 0xb6400004839e327f 0xb6c800009073c64f

def z585 : W := mkw 0x5280c48b29de362a 0x0a501891653bc6c5 0xff55cd9ffb9e3e7f 0xbfeab9b3ff73c7cf

def z586 : W := mkw 0x6103baa6c020c0d1 0x2c207754d804181a 0xbeebfe67e463c3ff 0x77dd7fccfc8c787f

def z587 : W := mkw 0x0000000800802200 0x0000000100100440 0x4104001803803000 0x8820800300700600

def z588 : W := mkw 0x1200400108541022 0x02400800210a8204 0x6dd3c007187c3066 0xedba7800e30f860c

def z589 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6dd3c387007c0062 0x0dba7870e00f800c

def z590 : W := mkw 0x00000400010a0000 0x0000008000214000 0x00000000039e0003 0xa00000000073c000

def z591 : W := mkw 0x0200000100041022 0x0040000020008204 0x00000000001c3066 0xa00000000003860c

def z592 : W := mkw 0x02800409218e322a 0x005000812431c645 0x5f440c1b639e3003 0xabe881836c73c600

def z593 : W := mkw 0x0282162da18e322a 0x005042c5b431c645 0xffce3e7fe39e327f 0xbff9c7cffc73c64f

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0x1208300004038001 0x0241060000807000

def z595 : W := mkw 0x011f3a248020c0d1 0x6023e7449004181a 0xbffffe648463c3ff 0x77ffffcc908c787f

def z596 : W := mkw 0x0000000800802200 0x0000000100100440 0xf744001c8382327f 0xbee880039070464f

def z597 : W := mkw 0x001c000816802200 0x4003800102d00440 0xe3dc00181f803205 0xfc7b800303f00640

def z598 : W := mkw 0x028000092084322a 0x0050000124108645 0x000000000000327c 0x000000000000064f

def z599 : W := mkw 0x02000401010e1022 0x004000802021c204 0x7f440c07039e3067 0xafe88180e073c60c

def z600 : W := mkw 0x5202c687097e5462 0x0a4058d0e12fca8c 0x7ff7cf871bfe7c67 0xeffef9f0e37fcf8c

def z601 : W := mkw 0x00800408218a2208 0x0010008104314441 0x9f440c18e39e021b 0xb3e881831c73c043

def z602 : W := mkw 0x041c000816802b04 0x4083800102d00560 0x03fc00001f807f85 0xe07f800003f00ff0

def z603 : W := mkw 0x1c1d6c081fdb2b04 0x6383ad8103fb6560 0x1ffffc001fffff87 0xe3ffff8003fffff0

def z604 : W := mkw 0x0002122480000000 0x0000424490000000 0xb6ea326484004385 0x76dd464c90800870

def z605 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x0bddcc001f9c0001 0xe17bb98003f38000

def z606 : W := mkw 0x00800408218a2208 0x0010008104314441 0x0000000003820219 0x0000000000704043

def z607 : W := mkw 0x801c015016000000 0x5003802a02c00000 0xe3dc03f81f800001 0xfc7b807f03f00000

def z608 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb6ea3264800043fc 0x16dd464c9000087f

def z609 : W := mkw 0x02800409218e322a 0x005000812431c645 0x49040c1b639e327f 0xa92081836c73c64f

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0x49040c1b60000000 0x092081836c000000

def z611 : W := mkw 0x001d280000000000 0x6003a50000000000 0x120c3c0000000000 0x0241878000000000

def z612 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6c23c387007c7c66 0x0d847870e00f8f8c

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0x008a300004618000 0x40114600008c3000

def z614 : W := mkw 0xe41fbbfed6802b04 0x7c83f77fdad00560 0xffdffffffb803c00 0x9ffbffffff700780

def z615 : W := mkw 0x4202828700245462 0x08405050e0048a8c 0x6d600387001c7c66 0xadac0070e0038f8c

def z616 : W := mkw 0x011e12249620c0d1 0x4023c24492c4181a 0xb7fe32649fe3c3ff 0xf6ffc64c93fc787f

def z617 : W := mkw 0x851c11789680ab95 0x50a3822f12d01572 0x920c307887838399 0x1241860f10f07073

def z618 : W := mkw 0x5a9fee8f3fff766a 0x6b53fdd1e7ffeecd 0xffffff9ffffffe7f 0xfffffff3ffffffcf

def z619 : W := mkw 0x841e137c96802b04 0x5083c26f92d00560 0xf7fe33fc9f807f85 0xfeffc67f93f00ff0

def z620 : W := mkw 0x801c015000000000 0x5003802a00000000 0x009803e000000000 0x0013007c00000000

def z621 : W := mkw 0x0400000816802b04 0x0080000102d00560 0xe36400181f807f85 0xfc6c800303f00ff0

def z622 : W := mkw 0xd602c3df08f47f66 0x1ac0587be11e8fec 0xedf3c3ff187c7fe6 0xfdbe787fe30f8ffc

def z623 : W := mkw 0x1200400108745462 0x02400800210e8a8c 0x0df3c000187c7c66 0xe1be7800030f8f8c

def z624 : W := mkw 0x4282868f218e322a 0x085050d1e431c645 0xffd7cf9fe39e327f 0xbffaf9f3fc73c64f

def z625 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xa2ea32600461c385 0x745d464c008c3870

def z626 : W := mkw 0x0000000000000000 0x0000000000000000 0xb6ca30048463827f 0x76d94600908c704f

def z627 : W := mkw 0xa09d3d78e18a2208 0x7413a7af1c314441 0x920c3c78e3820219 0x1241878f1c704043

def z628 : W := mkw 0xe41da9da56802b04 0x7c83b53b4ad00560 0x4915cd9b7b803c00 0x8922b9b36f700780

def z629 : W := mkw 0x581fee861f7b4440 0x6b03fdd0c3ef6888 0x1fffff801fffcc03 0xe3fffff003fff980

def z630 : W := mkw 0x0000000000000000 0x0000000000000000 0x92040c18e0000000 0x124081831c000000

def z631 : W := mkw 0x02800401210e102a 0x005000802421c205 0x00000000001e007a 0x000000000003c00f

def z632 : W := mkw 0x521fea8708745462 0x6a43fd50e10e8a8c 0x7fffff87187c7c66 0xeffffff0e30f8f8c

def z633 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6d43c007007c3066 0xada87800e00f860c

def z634 : W := mkw 0x19037e24897bc0d1 0x23206fc4912f781a 0xbeebfe64847fc3ff 0x77dd7fcc908ff87f

def z635 : W := mkw 0x861c015916843b26 0x50c3802b22d08764 0xeffc03ff1f9c7fe7 0xfdff807fe3f38ffc

def z636 : W := mkw 0xf01ffbf6c8704440 0x7e03ff7ed90e0888 0xfffffffff8604c00 0x5fffffffff0c0980

def z637 : W := mkw 0x01801428a18aa299 0x0030028514315453 0x920c3c78e7838399 0x1241878f1cf07073

def z638 : W := mkw 0x001c000016000000 0x4003800002c00000 0xa3fc02601f804385 0xf47f804c03f00870

def z639 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xa2e80264840043fd 0x745d004c9080087f

def z640 : W := mkw 0xd61ec3df1ef47f66 0x5ac3d87be3de8fec 0x6df7c39f1bfc7c66 0xedbef873e37f8f8c

def z641 : W := mkw 0x401faa8600000000 0x6803f550c0000000 0x7fdfff8700000000 0x0ffbfff0e0000000

def z642 : W := mkw 0x180044001f5b0000 0x0300088003eb6000 0x0dd3c0001fff8003 0xe1ba780003fff000

def z643 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x61f403981b807c04 0xec3e807303700f80

def z644 : W := mkw 0x6003baa6c0000000 0x2c007754d8000000 0xbecbfe67e0000000 0x17d97fccfc000000

def z645 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x14aa32648463c1fa 0x4295464c908c783f

def z646 : W := mkw 0x18004400095b0000 0x03000880012b6000 0x00000000007f8002 0x00000000000ff000

def z647 : W := mkw 0x6283beafe18e322a 0x2c5077d5fc31c645 0xff47fc1fe39e327f 0xbfe8ff83fc73c64f

def z648 : W := mkw 0xc01e83d600000000 0x5803d07ac0000000 0xefdfc3ff00000000 0x1dfbf87fe0000000

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0xa240000000000205 0x3448000000000040

def z650 : W := mkw 0x0100102080008091 0x0020020410001012 0x96ca30608463839b 0x72d9460c108c7073

def z651 : W := mkw 0xe10293f6c020c0d1 0x1c20527ed804181a 0xf6ea33ffe463c3ff 0x7edd467ffc8c787f

def z652 : W := mkw 0x7203faa7c8745462 0x2e407f54f90e8a8c 0x7df3ff87f87c7c66 0xefbe7ff0ff0f8f8c

def z653 : W := mkw 0xe41fbbf6d6000904 0x7c83f77edac00120 0x00bbf3e01c004d80 0x40177e7c038009b0

def z654 : W := mkw 0x181d6c00095b0000 0x6303ad80012b6000 0x1fdffc00007f8002 0x03fbff80000ff000

def z655 : W := mkw 0x8400015800802b04 0x1080002b00100560 0x4000019800003c00 0x0800003300000780

def z656 : W := mkw 0x10004400095a0000 0x02000880012b4000 0x1fd7cc001bfe0003 0xe3faf980037fc000

def z657 : W := mkw 0xe09fbffee18a2208 0x7c13f7ffdc314441 0xffdfffffe3820219 0x1ffbfffffc704043

def z658 : W := mkw 0x0380040921aef2fb 0x007000812435de5f 0x0020000007fff3ff 0xe004000000fffe7f

def z659 : W := mkw 0x841c015016000904 0x5083802a02c00120 0xa2f803e01c004f85 0x745f007c038009f0

def z660 : W := mkw 0x010000000020c0d1 0x002000000004181a 0xa2e802600463c3ff 0x745d004c008c787f

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0x1402300000638002 0x02804600000c7000

def z662 : W := mkw 0x851e137c96a0ebd5 0x50a3c26f92d41d7a 0xe3fc03fc9f807ffd 0xfc7f807f93f00fff

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x1f440c0000000000 0x03e8818000000000

def z664 : W := mkw 0xa01d3970c0000000 0x7403a72e18000000 0xff4c3c7fe0000000 0x1fe9878ffc000000

def z665 : W := mkw 0x9e9d6d593fdf3b2e 0x73d3adab27fbe765 0xffffffffffffffff 0xffffffffffffffff

def z666 : W := mkw 0x030212258024d0f3 0x00604244b0049a1e 0xffea3267847ff3ff 0xfffd464cf08ffe7f

def z667 : W := mkw 0x001d280000000000 0x6003a50000000000 0x0915cc0000000000 0x0122b98000000000

def z668 : W := mkw 0xf81ffbf6de510000 0x7f03ff7edbca2000 0xffdffffffc618000 0x5ffbffffff8c3000

def z669 : W := mkw 0x0002122480000000 0x0000424490000000 0xffce3e7fe0000000 0x1ff9c7cffc000000

def z670 : W := mkw 0x4002828600204440 0x08005050c0040888 0x0020038000004c00 0x0004007000000980

def z671 : W := mkw 0x02800409218e322a 0x005000812431c645 0xfc000c1fe01e327e 0x1f800183fc03c64f

def z672 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x60b3c38718607c64 0x4c167870e30c0f8c

def z673 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x129ffc001fe38001 0x4253ff8003fc7000

def z674 : W := mkw 0x02800409218e322a 0x005000812431c645 0x92040c18e39e327f 0xb24081831c73c64f

def z675 : W := mkw 0x001c000016000000 0x4003800002c00000 0x63fc03801f807c05 0xec7f807003f00f80

def z676 : W := mkw 0x4202828700245462 0x08405050e0048a8c 0x61f0038718007c64 0xec3e0070e3000f8c

def z677 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x0020026000004180 0x0004004c00000830

def z678 : W := mkw 0xa01d3970c0000000 0x7403a72e18000000 0x9fdffc78e0000000 0x13fbff8f1c000000

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0x140000048002007a 0x028000009000400f

def z680 : W := mkw 0x001c000016000000 0x4003800002c00000 0x009800001c000000 0x4013000003800000

def z681 : W := mkw 0x1a1d6c011f5f1022 0x6343ad8023ebe204 0x7fdffc071fffb067 0xeffbff80e3fff60c

def z682 : W := mkw 0xf61ffbffdef47f66 0x7ec3ff7ffbde8fec 0xfffffffffffc7fe7 0xffffffffffff8ffc

def z683 : W := mkw 0x001c000016000000 0x4003800002c00000 0x011400001b800000 0x8022800003700000

def z684 : W := mkw 0x0380040921aef2fb 0x007000812435de5f 0xff640c1fe7fff3ff 0xffec8183fcfffe7f

def z685 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe34c007807803385 0xbc69800f00f00670

def z686 : W := mkw 0x00000408018a2200 0x0000008100314440 0xff440c18039e3207 0xbfe881830073c640

def z687 : W := mkw 0x0000000000000000 0x0000000000000000 0x0d400000001c0002 0xa1a8000000038000

def z688 : W := mkw 0x0000000016000000 0x0000000002c00000 0x000000001f800001 0xe000000003f00000

def z689 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb6600264800243ff 0x36cc004c9000487f

def z690 : W := mkw 0x1801680008510000 0x23002d00010a2000 0x0003f00000618000 0x00007e00000c3000

def z691 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1fdffc001b9c0000 0x83fbff8003738000

def z692 : W := mkw 0xe29fbff7e10e102a 0x7c53f7fefc21c205 0xffdfffffe01e007a 0x1ffbfffffc03c00f

def z693 : W := mkw 0xe81fbff6d70b0000 0x7d03f7fedae16000 0xffdfffffe7838001 0x1ffbfffffcf07000

def z694 : W := mkw 0x1000400008500000 0x02000800010a0000 0x00000000187c0002 0xe0000000030f8000

def z695 : W := mkw 0x5a03ee87097f5462 0x2b407dd0e12fea8c 0x1c03fc07007f8062 0x03807f80e00ff00c

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000004638003 0x60000000008c7000

def z697 : W := mkw 0x8502137c80a0ebd5 0x10a0426f90141d7a 0xe02003fc80007ffc 0x1c04007f90000fff

def z698 : W := mkw 0xd61ec3d71e745d66 0x5ac3d87ae3ce8bac 0x6dfbc3e71c7c7de6 0xedbf787ce38f8fbc

def z699 : W := mkw 0xa41d3978d6802b04 0x7483a72f1ad00560 0x920c3c78e7800381 0x1241878f1cf00070

def z700 : W := mkw 0x010000000020c0d1 0x002000000004181a 0x000000000063807a 0x00000000000c700f

def z701 : W := mkw 0x0002020400204040 0x0000404080040808 0x0402000400600062 0x00804000800c000c

def z702 : W := mkw 0xf01ffbf6c8704440 0x7e03ff7ed90e0888 0x00bbf3e018604c00 0x40177e7c030c0980

def z703 : W := mkw 0x521ec2871e745462 0x4a43d850e3ce8a8c 0x6fffc3871ffc7c67 0xedfff870e3ff8f8c

def z704 : W := mkw 0x0000000000000000 0x0000000000000000 0x61d0038000000000 0x0c3a007000000000

def z705 : W := mkw 0xd69ec7df3ffe7f6e 0x5ad3d8fbe7ffcfed 0xffffcffffffe7fff 0xfffff9ffffffcfff

def z706 : W := mkw 0x1a0044011f7f5462 0x0340088023efea8c 0x002000001ffffc67 0xe004000003ffff8c

def z707 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x16dbf0001fff8003 0xe2db7e0003fff000

def z708 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe461c1e6 0x7ffffffffc8c383c

def z709 : W := mkw 0x841d295816802b04 0x7083a52b02d00560 0xebfdcff81f807f85 0xfd7fb9ff03f00ff0

def z710 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe3fc03f81f827fff 0xfc7f807f03f04fff

def z711 : W := mkw 0x02800409218e322a 0x005000812431c645 0x7d440c1fe39e307e 0xafa88183fc73c60f

def z712 : W := mkw 0x5082c68e29fa6648 0x0a1058d1c53f4cc9 0x92b7cf98fbe24e19 0x5256f9f31f7c49c3

def z713 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0xff55cd9fe002027f 0x3feab9b3fc00404f

def z714 : W := mkw 0x5300d0a3885494b3 0x0a601a14710a9296 0xdb19f1e39c1fbf99 0x9b633e3c7383f7f3

def z715 : W := mkw 0x1380440929fef6fb 0x02700881253fdedf 0x002000001fffffff 0xe004000003ffffff

def z716 : W := mkw 0x18016c00095b0000 0x23002d80012b6000 0x1fd7fc001bff8003 0xe3faff80037ff000

def z717 : W := mkw 0x6103baa6c020c0d1 0x2c207754d804181a 0xffeffe7fe463c3ff 0x7ffdffcffc8c787f

def z718 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xeffbf3e71c7dffe7 0xfdff7e7ce38fbffc

def z719 : W := mkw 0x8d1d3d78978bab95 0x71a3a7af12f17572 0x920c3c7887838399 0x1241878f10f07073

def z720 : W := mkw 0x981d6d501f5b0000 0x7303adaa03eb6000 0x5fdffd981fff8003 0xebfbffb303fff000

def z721 : W := mkw 0x1282460d29fe766a 0x025048c1a53fcecd 0xb6e202049bfe7e7f 0xf6dc4040937fcfcf

def z722 : W := mkw 0xf802d7f6df5b0000 0x1f005afedbeb6000 0xe00003ffffff8003 0xfc00007ffffff000

def z723 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xdb9ffffbe0000000 0x1b73ffff7c000000

def z724 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x7ff7cf87187c7c66 0xeffef9f0e30f8f8c

def z725 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe463827f 0x7ffbfffffc8c704f

def z726 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x9fdffc18ffff8003 0xf3fbff831ffff000

def z727 : W := mkw 0x6003baa6c0000000 0x2c007754d8000000 0x5d07fc1fe0000000 0x0ba0ff83fc000000

def z728 : W := mkw 0x5b03fea7897fd4f3 0x2b607fd4f12ffa9e 0x1c03fc07807f807a 0x03807f80f00ff00f

def z729 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1ecffc0007ff8003 0x63d9ff8000fff000

def z730 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xff57fd9fe0000000 0x1feaffb3fc000000

def z731 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6cb3c387187c7c66 0x4d967870e30f8f8c

def z732 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xfffbf3879c7ffe7f 0xffff7e70f38fffcf

def z733 : W := mkw 0xe01fbbf6d6000000 0x7c03f77edac00000 0xffffffffff807c05 0xfffffffffff00f80

def z734 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x0805cc1b60000000 0x0100b9836c000000

def z735 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe063c07e 0x7ffffffffc0c780f

def z736 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xeff7c39f187c7c66 0xfdfef873e30f8f8c

def z737 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x0cb3c387187c7c66 0xe1967870e30f8f8c

def z738 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0xbffffe649fffc3ff 0xf7ffffcc93fff87f

def z739 : W := mkw 0x5202d2a788745462 0x0a405a54f10e8a8c 0xfffbf3e7987e7e7f 0xffff7e7cf30fcfcf

def z740 : W := mkw 0x010010208020c0d1 0x002002041004181a 0x96ea30608463c3ff 0x72dd460c108c787f

def z741 : W := mkw 0xe11da9d24020c0d1 0x7c23b53a4804181a 0x4935cd9b6463c3ff 0x6926b9b36c8c787f

def z742 : W := mkw 0x5302c2870874d4f3 0x0a605850e10e9a9e 0xfff3c3879c7fffff 0xfffe7870f38fffff

def z743 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xebddcfffe0000000 0x1d7bb9fffc000000

def z744 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x4dd3c187187c3c62 0xe9ba7830e30f878c

def z745 : W := mkw 0x6001a88240000000 0x2c00351048000000 0xff45cc1fe0000000 0x1fe8b983fc000000

def z746 : W := mkw 0x5202c28708541422 0x0a405850e10a8284 0x6911c387181c3c00 0x8d223870e3038780

def z747 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x7fdfff801fff8003 0xeffbfff003fff000

def z748 : W := mkw 0xe01fabd640000000 0x7c03f57ac8000000 0xffd7cf9fe0000000 0x1ffaf9f3fc000000

def z749 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0xffdffffb60000000 0x1ffbffff6c000000

def z750 : W := mkw 0x010010208020c0d1 0x002002041004181a 0xb66830648463c3ff 0x76cd060c908c787f

def z751 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0xffdffc1fffff827f 0xfffbff83fffff04f

def z752 : W := mkw 0x1a9d68093ed5322a 0x6353ad0127daa645 0xe09bf01ffc61b27c 0x5c137e03ff8c364f

def z753 : W := mkw 0x0100102080008091 0x0020020410001012 0xb6ca3064846383ff 0x76d9460c908c707f

def z754 : W := mkw 0xe11fbbf6c0008091 0x7c23f77ed8001012 0xffdfffffe40383ff 0x3ffbfffffc80707f

def z755 : W := mkw 0x4a1fae87172f5462 0x6943f5d0e2e5ea8c 0x722c3f870783fc65 0x0e4587f0e0f07f8c

def z756 : W := mkw 0x5200c08308745462 0x0a401810610e8a8c 0x4911c183187c3c62 0x89223830630f878c

def z757 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe463c399 0x5ffffffffc8c7873

def z758 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x7ffbf3879c7ffc7f 0xefff7e70f38fff8f

def z759 : W := mkw 0x02800409218e322a 0x005000812431c645 0xffd40f9fe39e327f 0xbffa81f3fc73c64f

def z760 : W := mkw 0x18016c001f5b0000 0x23002d8003eb6000 0x1c03fc001bff8002 0x83807f80037ff000

def z761 : W := mkw 0x5202c28708541422 0x0a405850e10a8284 0x6df3c387181c7c04 0xedbe7870e3038f80

def z762 : W := mkw 0xa01d3970c0000000 0x7403a72e18000000 0xffdffc7fe0000000 0x1ffbff8ffc000000

def z763 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe0003004 0xbffbfffffc000600

def z764 : W := mkw 0x851e137c96a0ebd5 0x50a3c26f92d41d7a 0x5516319c9be3bc7a 0x8aa2c633937c778f

def z765 : W := mkw 0x8400015816802b04 0x1080002b02d00560 0x002003e01f807f85 0xe004007c03f00ff0

def z766 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x61f3c380187c7c66 0xec3e7870030f8f8c

def z767 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x099ffc001fff8003 0xe133ff8003fff000

def z768 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x7dfbf3e79c7ffdfe 0xefbf7e7cf38fffbf

def z769 : W := mkw 0x6403baaed6802b04 0x2c807755dad00560 0x1c23fc07ff807f85 0xe3847f80fff00ff0

def z770 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x00b803e01f807d80 0xc017007c03f00fb0

def z771 : W := mkw 0xe81fbbf6d6010000 0x7d03f77edac02000 0xffdfffffe4018000 0x1ffbfffffc803000

def z772 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0xeb55cd9b60000000 0x1d6ab9b36c000000

def z773 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x6931c383181c7c04 0x8d26387063038f80

def z774 : W := mkw 0x001d2c00010a0000 0x6003a58000214000 0x1fdffc0007ff8003 0xe3fbff8000fff000

def z775 : W := mkw 0x010010208020c0d1 0x002002041004181a 0x002830600463c3ff 0x6005060c008c787f

def z776 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x5fdffd801fffbc03 0xebfbffb003fff780

def z777 : W := mkw 0x5202d2a788541422 0x0a405a54f10a8284 0xffdbf3e7981c3c00 0x9ffb7e7cf3038780

def z778 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x0ddbf0001fff8003 0xe1bb7e0003fff000

def z779 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x03dff0001fff8003 0xe07bfe0003fff000

def z780 : W := mkw 0x02800409218e322a 0x005000812431c645 0xffd40c1ffb9e327f 0xfffa8183ff73c64f

def z781 : W := mkw 0x02800409218e322a 0x005000812431c645 0xffc60c1fe3fe327f 0xfff8c183fc7fc64f

def z782 : W := mkw 0xd61ec3df1ef47f66 0x5ac3d87be3de8fec 0x8e0fc07f07fc03e3 0x11c1f80fe0ff807c

def z783 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffffffffe0004384 0x1ffffffffc000870

def z784 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x5f55cd9b60000000 0x0beab9b36c000000

def z785 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xfffc0ff81f807f85 0xffff81ff03f00ff0

def z786 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x4dd7cd9b60000000 0x09baf9b36c000000

def z787 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe002007a 0x1ffbfffffc00400f

def z788 : W := mkw 0xe29fbfffe18e322a 0x7c53f7fffc31c645 0x009bf3e0039e327f 0xa0137e7c0073c64f

def z789 : W := mkw 0xe003bbf6c0000000 0x3c00777ed8000000 0x9c03fc7fe0000000 0x13807f8ffc000000

def z790 : W := mkw 0x0382162da1aef2fb 0x007042c5b435de5f 0x49ae3e7b67fdf180 0xc935c7cf6cffbe30

def z791 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffffffffe40243ff 0x7ffffffffc80487f

def z792 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffdfffffe0618000 0x1ffbfffffc0c3000

def z793 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdffffff8003c00 0x9ffbffffff000780

def z794 : W := mkw 0x02800409218e322a 0x005000812431c645 0xffcc0e7fe39e327f 0xbff981cffc73c64f

def z795 : W := mkw 0x4002828600204040 0x08005050c0040808 0xfff7cf9fe062427f 0x7ffef9f3fc0c484f

def z796 : W := mkw 0x10004400095a0000 0x02000880012b4000 0x1fdffc001fff8003 0xe3fbff8003fff000

def z797 : W := mkw 0xe01fbbf6d6000000 0x7c03f77edac00000 0xffdfffffffe38003 0xfffbfffffffc7000

def z798 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x4915cffb60000000 0x0922b9ff6c000000

def z799 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe3fc03ffff807f85 0xfc7f807ffff00ff0

def z800 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xfffffffffc007f85 0xffffffffff800ff0

def z801 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xbecffe7fe0000000 0x17d9ffcffc000000

def z802 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xedf3c39ff87c7c66 0xfdbe7873ff0f8f8c

def z803 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xf7ee327c8463c3ff 0x7efdc64f908c787f

def z804 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xf6ea327fe463c3ff 0x7edd464ffc8c787f

def z805 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xa2ea32600463c3ff 0x745d464c008c787f

def z806 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x5fdffc1b7fff8003 0xebfbff836ffff000

def z807 : W := mkw 0x8c1d2d58178b2b04 0x7183a5ab02f16560 0x820c0c7807800381 0x1041818f00f00070

def z808 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe33c03f81f807f85 0x9c67807f03f00ff0

def z809 : W := mkw 0x1280440929de362a 0x02500881253bc6c5 0x000000001b9e3e7f 0xa00000000373c7cf

def z810 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1b9ffc001fff8001 0xc373ff8003fff000

def z811 : W := mkw 0x4002828600000000 0x08005050c0000000 0xff47cc1fe0000000 0x1fe8f983fc000000

def z812 : W := mkw 0x400292a680000000 0x08005254d0000000 0xffdfffffe0000000 0x1ffbfffffc000000

def z813 : W := mkw 0x1000400008500000 0x02000800010a0000 0x4dd3c180187c3c02 0xe9ba7830030f8780

def z814 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0xbfdffc001fff8207 0xf7fbff8003fff040

def z815 : W := mkw 0x1a8044093fdf322a 0x0350088127fbe645 0x000000001b9c3000 0x8000000003738600

def z816 : W := mkw 0x4002828600000000 0x08005050c0000000 0x6dd7cf9f60000000 0x0dbaf9f3ec000000

def z817 : W := mkw 0xe01fabd640204040 0x7c03f57ac8040808 0x6df7cf9f60604066 0x6dbef9f3ec0c080c

def z818 : W := mkw 0xe103bbf6c020c0d1 0x3c20777ed804181a 0xfc23ffffe063c3fe 0x1f847ffffc0c787f

def z819 : W := mkw 0xb81d6d505f5b0000 0x7703adaa0beb6000 0x1fdffc187fff8003 0xe3fbff830ffff000

def z820 : W := mkw 0x0400000816802b04 0x0080000102d00560 0xe3f803e01f807f85 0xfc7f007c03f00ff0

def z821 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe0020003 0x3ffbfffffc004000

def z822 : W := mkw 0x841d295816802b04 0x7083a52b02d00560 0xf3fc3ff81f807f85 0xfe7f87ff03f00ff0

def z823 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xfffbf3e7987ffc7e 0xffff7e7cf30fff8f

def z824 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x5fdffd9fe0000000 0x0bfbffb3fc000000

def z825 : W := mkw 0x191f7e249f7bc0d1 0x6323efc493ef781a 0xa935ce649b9c43fc 0x9526b9cc9373887f

def z826 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdffffff8000000 0xfffbffffff000000

def z827 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff640f9fe39e7e7f 0xbfec81f3fc73cfcf

def z828 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe0000066 0x3ffbfffffc00000c

def z829 : W := mkw 0x981d6d501f5b0000 0x7303adaa03eb6000 0xfffffff81fffc387 0xffffffff03fff870

def z830 : W := mkw 0x18016c001f5b0000 0x23002d8003eb6000 0x1ecbfc001fff8003 0xe3d97f8003fff000

def z831 : W := mkw 0xe41fbbf6d6000904 0x7c83f77edac00120 0xffffffffff804d81 0xfffffffffff009b0

def z832 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6d33c387187c7c66 0x8da67870e30f8f8c

def z833 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x92aa32608463c3ff 0x7255464c108c787f

def z834 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xc3bc03f81f807f81 0xd877807f03f00ff0

def z835 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xe931c3e7981c7ffc 0x9d26387cf3038fff

def z836 : W := mkw 0x5300c0830874d4f3 0x0a601810610e9a9e 0x4931c1831c7fffff 0xe9263830638fffff

def z837 : W := mkw 0x02800409218e322a 0x005000812431c645 0xe9040c1fe39e327f 0xbd208183fc73c64f

def z838 : W := mkw 0x981d6d501f5b0000 0x7303adaa03eb6000 0x9fdffc781fff8003 0xf3fbff8f03fff000

def z839 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x4df3c383187c7c02 0xe9be7870630f8f80

def z840 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1f57fc001bff8003 0xa3eaff80037ff000

def z841 : W := mkw 0x02800409218e322a 0x005000812431c645 0x1c040c1fe39e007a 0x03808183fc73c00f

def z842 : W := mkw 0xe01db9f2c0000000 0x7c03b73e58000000 0x5915fd9be0000000 0x0b22bfb37c000000

def z843 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0xbfdffe601fff8003 0xf7fbffcc03fff000

def z844 : W := mkw 0x02800409218e322a 0x005000812431c645 0xffcc0c1fe79e327f 0xfff98183fcf3c64f

def z845 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb22832648463c3ff 0x7645064c908c787f

def z846 : W := mkw 0x18016c001f5b0000 0x23002d8003eb6000 0x0003f0001fff8003 0xe0007e0003fff000

def z847 : W := mkw 0x8c1d2d58178b2b04 0x7183a5ab02f16560 0x00040c1803800000 0x0000818300700000

def z848 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x6ddfffff60000000 0x0dbbffffec000000

def z849 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0xff51c187981e3e7f 0xbfea3830f303c7cf

def z850 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x009bf0001ffd8000 0xc0137e0003ffb000

def z851 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe0004180 0x1ffffffffc000830

def z852 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe461c3fc 0x5ffffffffc8c387f

def z853 : W := mkw 0x9c1d6d501f5b0904 0x7383adaa03eb6120 0xbfffffe01fffcf87 0xf7fffffc03fff9f0

def z854 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1ffffc001fffc387 0xe3ffff8003fff870

def z855 : W := mkw 0xe01db9f2c0000000 0x7c03b73e58000000 0x9a0dfc7be0000000 0x1341bf8f7c000000

def z856 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff640c1ffb9e7e7f 0xffec8183ff73cfcf

def z857 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6df7cf9f787c7c66 0xedbef9f3ef0f8f8c

def z858 : W := mkw 0x8400015816802b04 0x1080002b02d00560 0xe02003f81b807f84 0x9c04007f03700ff0

def z859 : W := mkw 0x0001280000000000 0x2000250000000000 0xff47fc1fe0000000 0x1fe8ff83fc000000

def z860 : W := mkw 0x5302c2870874d4f3 0x0a605850e10e9a9e 0xeffbc3e71c7fffff 0xfdff787ce38fffff

def z861 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x4917fd9b60000000 0x0922ffb36c000000

def z862 : W := mkw 0x410292a68020c0d1 0x08205254d004181a 0xffffffffe463c3ff 0x7ffffffffc8c787f

def z863 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0xffddcfffe0000000 0x1ffbb9fffc000000

def z864 : W := mkw 0x9c1d6d501f5b0904 0x7383adaa03eb6120 0x1fdffc601fff8183 0xe3fbff8c03fff030

def z865 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff540d9ffb9e3e7f 0xbfea81b3ff73c7cf

def z866 : W := mkw 0xe51fbbf6d620c9d5 0x7ca3f77edac4193a 0xfffffffffc63cfff 0x7fffffffff8c79ff

def z867 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x4bddcd9b60000000 0x097bb9b36c000000

def z868 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xa2f803e01f807f85 0xf45f007c03f00ff0

def z869 : W := mkw 0x02800409218e322a 0x005000812431c645 0xffee3e7fe7fff3ff 0xfffdc7cffcfffe7f

def z870 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6df3c387181c7c64 0x8dbe7870e3038f8c

def z871 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x4d51c183181c3c02 0xa9aa383063038780

def z872 : W := mkw 0x02800409218e322a 0x005000812431c645 0xffd7cc1fe39e327f 0xbffaf983fc73c64f

def z873 : W := mkw 0xe01fabd640000000 0x7c03f57ac8000000 0x4997cf9b60000000 0x0932f9f36c000000

def z874 : W := mkw 0x410292a68020c0d1 0x08205254d004181a 0xf6ea33e78463c3ff 0x7edd467cf08c787f

def z875 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1fffff801fffcc03 0xe3fffff003fff980

def z876 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xeff3c387187c7e67 0xfdfe7870e30f8fcc

def z877 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff463c1fe3ffb27f 0xbfe8c783fc7ff64f

def z878 : W := mkw 0xe01db9f2c0000000 0x7c03b73e58000000 0xc915cdfbe0000000 0x1922b9bf7c000000

def z879 : W := mkw 0xe01fbbf6d6000000 0x7c03f77edac00000 0xffdfffffe7800001 0x1ffbfffffcf00000

def z880 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1fdffc0007ff8003 0x03fbff8000fff000

def z881 : W := mkw 0x6003baa6c0000000 0x2c007754d8000000 0xffcffe7fe0000000 0x1ff9ffcffc000000

def z882 : W := mkw 0x5202d2a788745462 0x0a405a54f10e8a8c 0x7df3f387987c7c66 0xefbe7e70f30f8f8c

def z883 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1ffffe601fffc183 0xe3ffffcc03fff830

def z884 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xf7fc03fc9f807f85 0xfeff807f93f00ff0

def z885 : W := mkw 0x180044001f5b0000 0x0300088003eb6000 0x1fdbf0001fff8003 0xe3fb7e0003fff000

def z886 : W := mkw 0x5202c28708541422 0x0a405850e10a8284 0x4d13c187181c3c00 0x89a27830e3038780

def z887 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe461c385 0x7ffffffffc8c3870

def z888 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x6dd3c187187c3c66 0xedba7830e30f878c

def z889 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0x9e0ffc7fe46383fb 0x13c1ff8ffc8c707f

def z890 : W := mkw 0x841c015016000904 0x5083802a02c00120 0x63fc03e01f807d85 0xec7f807c03f00fb0

def z891 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffdfffffe463807b 0x7ffbfffffc8c700f

def z892 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xedf3c3e7187c7fe6 0xfdbe787ce30f8ffc

def z893 : W := mkw 0x1280440929fe766a 0x02500881253fcecd 0x0000000003fe327f 0xa0000000007fc64f

def z894 : W := mkw 0xa41d295856802b04 0x7483a52b0ad00560 0xe3fc0ff87f807f85 0xfc7f81ff0ff00ff0

def z895 : W := mkw 0x02800409218e322a 0x005000812431c645 0xffe40e1fe39e727f 0xfffc81c3fc73ce4f

def z896 : W := mkw 0x6103baa6c020c0d1 0x2c207754d804181a 0xff47fc1fe063827f 0x3fe8ff83fc0c704f

def z897 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe13403f81f807f85 0xfc26807f03f00ff0

def z898 : W := mkw 0x6001a88240000000 0x2c00351048000000 0x4905cc1b60000000 0x0920b9836c000000

def z899 : W := mkw 0x02800409218e322a 0x005000812431c645 0xfe040c1fe39e327f 0x1fc08183fc73c64f

def z900 : W := mkw 0x5202d2a788745462 0x0a405a54f10e8a8c 0x6dfbf3e7187c7c66 0xedbf7e7ce30f8f8c

def z901 : W := mkw 0xc70293ff80a4fff7 0x18e0527ff0149ffe 0xe02003ff80007ffc 0x1c04007ff0000fff

def z902 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe22c03f81f807f85 0xfc45807f03f00ff0

def z903 : W := mkw 0x5002c28608500000 0x0a005850c10a0000 0x6df3c387187c7c06 0xedbe7870e30f8f80

def z904 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xfe0fffffe0000000 0x1fc1fffffc000000

def z905 : W := mkw 0xe38293ffe0a4f2fb 0x1c70527ffc149e5f 0xe02003ffe00073fc 0x1c04007ffc000e7f

def z906 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xfff7cf9ff87e7e7f 0xfffef9f3ff0fcfcf

def z907 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0xebf9c3e31c1c7f85 0xfd7f387c63838ff0

def z908 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe3fc03fc9f807ffd 0xfc7f807f93f00fff

def z909 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x6df3c3e7187c7de6 0xedbe787ce30f8fbc

def z910 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6df3c3871c7c7fe7 0xedbe7870e38f8ffc

def z911 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1dd7fc001bff8002 0xe3baff80037ff000

def z912 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0x5d17fd9fe063807a 0x0ba2ffb3fc0c700f

def z913 : W := mkw 0x181d6c00095b0000 0x6303ad80012b6000 0x1fdffc0003ff8003 0xa3fbff80007ff000

def z914 : W := mkw 0x02800409218e322a 0x005000812431c645 0x9e040c1fe39e327f 0xb3c08183fc73c64f

def z915 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0xffdffc181fff8003 0xfffbff8303fff000

def z916 : W := mkw 0x981d6d501f5b0000 0x7303adaa03eb6000 0xfffffff81ffffc07 0xffffffff03ffff80

def z917 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6df3c387187c7c00 0xcdbe7870e30f8f80

def z918 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x69f1c387181c7c64 0xed3e3870e3038f8c

def z919 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x0df3c380187c7c66 0xe1be7870030f8f8c

def z920 : W := mkw 0xe01fbbf6c0204040 0x7c03f77ed8040808 0xffffffffe0604000 0x5ffffffffc0c0800

def z921 : W := mkw 0xe11fbbf6c0008091 0x7c23f77ed8001012 0xffdfffffe4018180 0x1ffbfffffc803030

def z922 : W := mkw 0x101c40001e500000 0x4203880003ca0000 0x1fdff0001fff8003 0xe3fbfe0003fff000

def z923 : W := mkw 0xe01fabd640000000 0x7c03f57ac8000000 0x7fdfff9f60000000 0x0ffbfff3ec000000

def z924 : W := mkw 0xe003bbf6c0000000 0x3c00777ed8000000 0xfecbffffe0000000 0x1fd97ffffc000000

def z925 : W := mkw 0x5382d6a7a97ed4fb 0x0a705ad4f52fda9f 0x1c03fc07e07f807a 0x03807f80fc0ff00f

def z926 : W := mkw 0x001c000016000000 0x4003800002c00000 0xe3fc03e01f807f85 0xfc7f807c03f00ff0

def z927 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xfffc0fffff827fff 0xffff81fffff04fff

def z928 : W := mkw 0xe01db9f2c0000000 0x7c03b73e58000000 0xff5dfdffe0000000 0x1febbfbffc000000

def z929 : W := mkw 0x8c1d295816812b04 0x7183a52b02d02560 0xe3fc33f81f81ff85 0xfc7f867f03f03ff0

def z930 : W := mkw 0x841d295816802b04 0x7083a52b02d00560 0xe3fff3f81f807f85 0xfc7ffe7f03f00ff0

def z931 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff4c3c1fe79fb27f 0xbfe98783fcf3f64f

def z932 : W := mkw 0x5202d2a788745462 0x0a405a54f10e8a8c 0xedf3c3e7987c7c66 0xfdbe787cf30f8f8c

def z933 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe4000381 0x1ffbfffffc800070

def z934 : W := mkw 0x1c1d6c001f5b0904 0x6383ad8003eb6120 0x1ffffc001fffcd83 0xe3ffff8003fff9b0

def z935 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe0b803f81f807f85 0xfc17007f03f00ff0

def z936 : W := mkw 0x9c1d6d501f5b0904 0x7383adaa03eb6120 0x7fffffe01ffffd87 0xeffffffc03ffffb0

def z937 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x49bbf3e31c7dfd80 0xc9377e7c638fbfb0

def z938 : W := mkw 0xe11fbbf6c0008091 0x7c23f77ed8001012 0xffdfffffe0038018 0x1ffbfffffc007003

def z939 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xf29fffffe0000000 0x1e53fffffc000000

def z940 : W := mkw 0x1b82562dbffff2fb 0x03704ac5b7fffe5f 0xb6ea32649ffff3ff 0xf6dd464c93fffe7f

def z941 : W := mkw 0x1a80440929df322a 0x03500881253be645 0x0000000003ffb27f 0xa0000000007ff64f

def z942 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xfd17ffffe0000000 0x1fa2fffffc000000

def z943 : W := mkw 0x18016c001f5b0000 0x23002d8003eb6000 0x1c03fc0007ff8003 0x03807f8000fff000

def z944 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x5fdffd9b64638003 0x6bfbffb36c8c7000

def z945 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb64a3064846383ff 0x36c9460c908c707f

def z946 : W := mkw 0x869c0551370e192e 0x50d380aa26e1c325 0x1cb80fe7fc1e4dfa 0x439701fcff83c9bf

def z947 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x6d51c187181c3c00 0x8daa3830e3038780

def z948 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xbeeffe7fe463c3ff 0x77ddffcffc8c787f

def z949 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0xdb15cd9be0000000 0x1b62b9b37c000000

def z950 : W := mkw 0x6003baa6c0000000 0x2c007754d8000000 0x9e07fc1fe0000000 0x13c0ff83fc000000

def z951 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe0020219 0x1ffbfffffc004043

def z952 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x5fdbf1831c7fbc03 0xebfb7e30638ff780

def z953 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x9fdffc601fff8383 0xf3fbff8c03fff070

def z954 : W := mkw 0x1382562da9fef6fb 0x02704ac5b53fdedf 0xb6ea32649fffffff 0xf6dd464c93ffffff

def z955 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x69f3c383187c7c04 0xed3e7870630f8f80

def z956 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x4931c183181c7c04 0xe926383063038f80

def z957 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1e0ffc001fff8003 0xe3c1ff8003fff000

def z958 : W := mkw 0xa49d3d78f78a2b0c 0x7493a7af1ef14561 0x920c3c78e7820399 0x1241878f1cf04073

def z959 : W := mkw 0xe01fabd640000000 0x7c03f57ac8000000 0xefdfcfff60000000 0x1dfbf9ffec000000

def z960 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x9fdffc7fe0000000 0x13fbff8ffc000000

def z961 : W := mkw 0x001d280000000000 0x6003a50000000000 0xff55cc1fe0000000 0x1feab983fc000000

def z962 : W := mkw 0x5202d2a788745462 0x0a405a54f10e8a8c 0xfffffffff87c7c66 0xffffffffff0f8f8c

def z963 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6931c387187c7c66 0xed263870e30f8f8c

def z964 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x61f803e01f807f85 0xec3f007c03f00ff0

def z965 : W := mkw 0xf91ffbf6de71c0d1 0x7f23ff7edbce381a 0x00bbf3e01c61c180 0x40177e7c038c3830

def z966 : W := mkw 0x1a8044093fdf322a 0x0350088127fbe645 0x000000001fffb003 0xe000000003fff600

def z967 : W := mkw 0x02800409218e322a 0x005000812431c645 0xfffc0fffff9e7fff 0xffff81fffff3cfff

def z968 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1c07fc0003ff8002 0x0380ff80007ff000

def z969 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0xe915cffb60000000 0x1d22b9ff6c000000

def z970 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x9fdffc009fff821b 0xf3fbff8013fff043

def z971 : W := mkw 0x18016c00095b0000 0x23002d80012b6000 0x1c03fc0003ff8003 0xa3807f80007ff000

def z972 : W := mkw 0x9e9d6d593fdf3b2e 0x73d3adab27fbe765 0x4915cd9b7b9c3c00 0x8922b9b36f738780

def z973 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6dfbf3871c7dfc66 0xedbf7e70e38fbf8c

def z974 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0x49bffffb6461c180 0x4937ffff6c8c3830

def z975 : W := mkw 0x5202c28708541422 0x0a405850e10a8284 0x6dd3c387181c3c66 0xadba7870e303878c

def z976 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xefffc3f81f807f85 0xfdfff87f03f00ff0

def z977 : W := mkw 0x1200400108745462 0x02400800210e8a8c 0x6df3c380187c7c66 0xedbe7870030f8f8c

def z978 : W := mkw 0x1000400008500000 0x02000800010a0000 0x69f1c380181c7c04 0xed3e387003038f80

def z979 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x6951c183181c3c04 0xad2a383063038780

def z980 : W := mkw 0xe41da9d256000904 0x7c83b53a4ac00120 0x4915cd9b78000c00 0x0922b9b36f000180

def z981 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe4618000 0x5ffbfffffc8c3000

def z982 : W := mkw 0x5302c2870874d4f3 0x0a605850e10e9a9e 0x6df3c3871c7dfde6 0xedbe7870e38fbfbc

def z983 : W := mkw 0x001d280000000000 0x6003a50000000000 0x4915cc1b60000000 0x0922b9836c000000

def z984 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe063c3fe 0x1ffffffffc0c787f

def z985 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xeffc03ff1f807f85 0xfdff807fe3f00ff0

def z986 : W := mkw 0x7202d2a7c8745462 0x0e405a54f90e8a8c 0x6df3c387f87c7c66 0xedbe7870ff0f8f8c

def z987 : W := mkw 0xb21d7971c8745462 0x7643af2e390e8a8c 0x922c3c78f87c7c66 0xf245878f1f0f8f8c

def z988 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x4993c183187c3c00 0xc9327830630f8780

def z989 : W := mkw 0xe01fbbf6c0204440 0x7c03f77ed8040888 0xffffffffe0004c00 0x1ffffffffc000980

def z990 : W := mkw 0x168044093ffe7f6e 0x02d0088127ffcfed 0x002000001ffe7fff 0xe004000003ffcfff

def z991 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x4915cd9b781c3c00 0x8922b9b36f038780

def z992 : W := mkw 0xe41fbbf6d6000904 0x7c83f77edac00120 0xfffffffffc007d84 0xffffffffff800fb0

def z993 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xf6ea33e48463ffff 0x7edd467c908c7fff

def z994 : W := mkw 0x1a8044093fdf322a 0x0350088127fbe645 0xb6ca30049fffb27f 0xf6d9460093fff64f

def z995 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xfff3f387987ffe7f 0xfffe7e70f30fffcf

def z996 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xfffffffffc63ffff 0xffffffffff8c7fff

def z997 : W := mkw 0x8400015816802b04 0x1080002b02d00560 0xe2e803f81f807f85 0xfc5d007f03f00ff0

def z998 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x7df3c387987e7c7e 0xefbe7870f30fcf8f

def z999 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0xffdffd9fe0000000 0x1ffbffb3fc000000

def z1000 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0xffffffe01fffff87 0xfffffffc03fffff0

def z1001 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x3fdffc041fff8067 0xe7fbff8083fff00c

def z1002 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xe99fffffe0000000 0x1d33fffffc000000

def z1003 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xfb1dffffe0000000 0x1f63bffffc000000

def z1004 : W := mkw 0xe01fbbf6c0204040 0x7c03f77ed8040808 0xffffffffe463c067 0x7ffffffffc8c780c

def z1005 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0xff55cd9ff81c3c00 0x9feab9b3ff038780

def z1006 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x4d33c187187c7c66 0xe9a67830e30f8f8c

def z1007 : W := mkw 0x4202828700041022 0x08405050e0008204 0x6df3c387181c7c66 0xedbe7870e3038f8c

def z1008 : W := mkw 0x841d295816802b04 0x7083a52b02d00560 0xffffffffff807f85 0xfffffffffff00ff0

def z1009 : W := mkw 0x5202d2a788745462 0x0a405a54f10e8a8c 0xfffbf3e79c7c7fe7 0xffff7e7cf38f8ffc

def z1010 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x6df1c387181c7c66 0xedbe3870e3038f8c

def z1011 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x24f3c384187c7c66 0xe49e7870830f8f8c

def z1012 : W := mkw 0xe01fbbf6d6000000 0x7c03f77edac00000 0xffdffffffb800000 0x9ffbffffff700000

def z1013 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6ff7c3871bfc7c67 0xedfef870e37f8f8c

def z1014 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe7fc03fc1f807fe7 0xfcff807f83f00ffc

def z1015 : W := mkw 0xe01fbbf6d6000000 0x7c03f77edac00000 0xffffffffff804385 0xfffffffffff00870

def z1016 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x5d9fffffe0000000 0x0bb3fffffc000000

def z1017 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x41bc03f81f807f85 0xe837807f03f00ff0

def z1018 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6df3c3871c7ffc67 0xedbe7870e38fff8c

def z1019 : W := mkw 0xe11fbbf6c0008091 0x7c23f77ed8001012 0xffffffffe403c39d 0x7ffffffffc807873

def z1020 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe06043fe 0x7ffffffffc0c087f

def z1021 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1c9bfc001fff8003 0xe3937f8003fff000

def z1022 : W := mkw 0x010000000020c0d1 0x002000000004181a 0xb6ea32600463c3ff 0x76dd464c008c787f

def z1023 : W := mkw 0x0000000800802200 0x0000000100100440 0xe3fc03f81f807f85 0xfc7f807f03f00ff0

def z1024 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x129ffc001fff8003 0xe253ff8003fff000

def z1025 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x7df3f3879c7fffff 0xefbe7e70f38fffff

def z1026 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x43fc03f81f807d81 0xe87f807f03f00fb0

def z1027 : W := mkw 0x5202c28708541422 0x0a405850e10a8284 0x6dd3c387187c3c02 0xedba7870e30f8780

def z1028 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1d17fc001fff8003 0xe3a2ff8003fff000

def z1029 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x962a30648463c3ff 0x72c5460c908c787f

def z1030 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe1bc03f81f807f84 0xdc37807f03f00ff0

def z1031 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x7df3f387187ffc66 0xefbe7e70e30fff8c

def z1032 : W := mkw 0x189d6c003f5b0008 0x6313ad8007eb6001 0x1fdffc00ffff801b 0xe3fbff801ffff003

def z1033 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x1c07fc1fe0000000 0x0380ff83fc000000

def z1034 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xedfbf3e79c7dfffe 0xfdbf7e7cf38fbfff

def z1035 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe3fc03f81f807d80 0xdc7f807f03f00fb0

def z1036 : W := mkw 0x801d295000000000 0x7003a52a00000000 0xffdfffffe0000000 0x1ffbfffffc000000

def z1037 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6d53c187187c3c66 0xadaa7830e30f878c

def z1038 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffffffffe4004180 0x5ffffffffc800830

def z1039 : W := mkw 0x841d295816802b04 0x7083a52b02d00560 0xfffffff81fe3ff87 0xffffffff03fc7ff0

def z1040 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb4aa32648463c3fe 0x5695464c908c787f

def z1041 : W := mkw 0x02800409218e322a 0x005000812431c645 0xbe440c1fe39e027f 0x37c88183fc73c04f

def z1042 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x16ea32600463c3ff 0x62dd464c008c787f

def z1043 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe000027c 0x1ffbfffffc00004f

def z1044 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x00b3c380187c7c00 0xc0167870030f8f80

def z1045 : W := mkw 0xe01db9f2c0000000 0x7c03b73e58000000 0x491dfdfb60000000 0x0923bfbf6c000000

def z1046 : W := mkw 0xe003bbf6c0000000 0x3c00777ed8000000 0xfdd3ffffe0000000 0x1fba7ffffc000000

def z1047 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x4915cd9fe0000000 0x0922b9b3fc000000

def z1048 : W := mkw 0x5002c28608704440 0x0a005850c10e0888 0x6df3c380187c7c06 0xedbe7870030f8f80

def z1049 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x5d17fd9b60000000 0x0ba2ffb36c000000

def z1050 : W := mkw 0x8c1d2d58178b2b04 0x7183a5ab02f16560 0xb6ee3e7807e3c387 0x76ddc7cf00fc7870

def z1051 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x6dfbf3e71c7fffff 0xedbf7e7ce38fffff

def z1052 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb62a32648463c3ff 0x16c5464c908c787f

def z1053 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1fdffc001bff8002 0x83fbff80037ff000

def z1054 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x6df3c383187c7c06 0xedbe7870630f8f80

def z1055 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x499dcffb60000000 0x0933b9ff6c000000

def z1056 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe37403f81b807f85 0xbc6e807f03700ff0

def z1057 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff440c1fe39c327c 0x9fe88183fc73864f

def z1058 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x6d55cd9f60000000 0x0daab9b3ec000000

def z1059 : W := mkw 0x1a8044093fff766a 0x0350088127ffeecd 0x002000001ffffe7f 0xe004000003ffffcf

def z1060 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xf7ea32648463f3ff 0xfefd464c908c7e7f

def z1061 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffffffffe0007c04 0x1ffffffffc000f80

def z1062 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x0011c180181c3c00 0x8002383003038780

def z1063 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1fdffc001ffd8000 0xc3fbff8003ffb000

def z1064 : W := mkw 0x001d280000000000 0x6003a50000000000 0xffdffc1fe463827f 0x7ffbff83fc8c704f

def z1065 : W := mkw 0x9c1d6d501f5b0904 0x7383adaa03eb6120 0x1fdffd801fff8c03 0xe3fbffb003fff180

def z1066 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe403c3fd 0x1ffffffffc80787f

def z1067 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe0000205 0x3ffbfffffc000040

def z1068 : W := mkw 0x011f3a248020c0d1 0x6023e7449004181a 0xfffffe7fe463c3ff 0x7fffffcffc8c787f

def z1069 : W := mkw 0x02800409218e322a 0x005000812431c645 0x49040c1fe39c3078 0x89208183fc73860f

def z1070 : W := mkw 0x5200c08308745462 0x0a401810610e8a8c 0x6d71c187187c7c66 0xedae3830e30f8f8c

def z1071 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xf7fe33f81f807f85 0xfeffc67f03f00ff0

def z1072 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xbfea3264847fc3ff 0xf7fd464c908ff87f

def z1073 : W := mkw 0x001f3a2480000000 0x6003e74490000000 0xffdffe7fe0000000 0x1ffbffcffc000000

def z1074 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xedf3c3e79c7fffff 0xfdbe787cf38fffff

def z1075 : W := mkw 0xe11fbbf6c0008091 0x7c23f77ed8001012 0xffdfffffe463839b 0x7ffbfffffc8c7073

def z1076 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xeffc03f81f9c7f87 0xfdff807f03f38ff0

def z1077 : W := mkw 0x438292afa0a4f6fb 0x08705255f4149edf 0xe02003ffe0007ffc 0x1c04007ffc000fff

def z1078 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe3fe33f81fe1ff85 0xfc7fc67f03fc3ff0

def z1079 : W := mkw 0x4000808200000000 0x0800101040000000 0x4915cd9b60000000 0x0922b9b36c000000

def z1080 : W := mkw 0xac1d3d78d78b2b04 0x7583a7af1af16560 0x920c3c78e7838381 0x1241878f1cf07070

def z1081 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb6ea32649c63ffff 0xf6dd464c938c7fff

def z1082 : W := mkw 0x18016c00095b0000 0x23002d80012b6000 0x1e07fc0003ff8003 0x03c0ff80007ff000

def z1083 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1f1ffc001fff8003 0x83e3ff8003fff000

def z1084 : W := mkw 0x5282c2872874546a 0x0a505850e50e8a8d 0x6df3c387f87c7c7e 0xedbe7870ff0f8f8f

def z1085 : W := mkw 0x5202c28708541422 0x0a405850e10a8284 0x4993c383181c3c00 0x8932787063038780

def z1086 : W := mkw 0xe11db9f2c0008091 0x7c23b73e58001012 0xdb1dfdfbe4038399 0x1b63bfbf7c807073

def z1087 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0xebfdcffb64004385 0x7d7fb9ff6c800870

def z1088 : W := mkw 0xe01da9d256000000 0x7c03b53a4ac00000 0x4bddcd9b7f800001 0xe97bb9b36ff00000

def z1089 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xfdf3f3e7987ffffe 0xffbe7e7cf30fffff

def z1090 : W := mkw 0x1a8044093fdf322a 0x0350088127fbe645 0x000000001b9e327f 0xa00000000373c64f

def z1091 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xa0aa32648463c3ff 0x7415464c908c787f

def z1092 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x413403f81b807d80 0x8826807f03700fb0

def z1093 : W := mkw 0x410292a68020c4d1 0x08205254d004189a 0xb6ea33e48463cfff 0x76dd467c908c79ff

def z1094 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xfffbf3e79c7dfde6 0xffff7e7cf38fbfbc

def z1095 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe2bc03f81f807f85 0x5c57807f03f00ff0

def z1096 : W := mkw 0x1b8044093ffff2fb 0x0370088127fffe5f 0x002000001ffff3ff 0xe004000003fffe7f

def z1097 : W := mkw 0x02800409218e322a 0x005000812431c645 0xdf040c1fe39e327b 0x9be08183fc73c64f

def z1098 : W := mkw 0xe01fbbf6d6000000 0x7c03f77edac00000 0xffdffffffc000000 0x5ffbffffff800000

def z1099 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x69f5cf9b78007c04 0xed3eb9f36f000f80

def z1100 : W := mkw 0xe01db9f2c0000000 0x7c03b73e58000000 0xfbddfffbe0000000 0x1f7bbfff7c000000

def z1101 : W := mkw 0x4000808200000000 0x0800101040000000 0xff55cd9fe0000000 0x1feab9b3fc000000

def z1102 : W := mkw 0xe51fbbf6d620c9d5 0x7ca3f77edac4193a 0xfffffffffc61cd80 0x5fffffffff8c39b0

def z1103 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffdfffffe0000078 0x1ffbfffffc00000f

def z1104 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xfffffffffc7fffff 0xffffffffff8fffff

def z1105 : W := mkw 0x1280440929fe766a 0x02500881253fcecd 0x002000001bfc7c66 0xe0040000037f8f8c

def z1106 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x7ffbf3e71c7ffde7 0xefff7e7ce38fffbc

def z1107 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x4911c187181c3c60 0x89223830e303878c

def z1108 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x0ddffc001ffd8002 0xe1bbff8003ffb000

def z1109 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x499ffd9b60000000 0x0933ffb36c000000

def z1110 : W := mkw 0x9c016d5809db2b04 0x33802dab013b6560 0xfc23fff8007fff86 0x1f847fff000ffff0

def z1111 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xebfc0ffb7f807f85 0xfd7f81ff6ff00ff0

def z1112 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe0638002 0x1ffbfffffc0c7000

def z1113 : W := mkw 0x8c9d2d58378b2b0c 0x7193a5ab06f16561 0x920c3c78e7838399 0x1241878f1cf07073

def z1114 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x4915cd9b78003c00 0x8922b9b36f000780

def z1115 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe01c0002 0xbffbfffffc038000

def z1116 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff4c0c7fe79e33ff 0xbfe9818ffcf3c67f

def z1117 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xfffffffff8004c00 0x5fffffffff000980

def z1118 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x49b1c383181c7c00 0xc936387063038f80

def z1119 : W := mkw 0x00000400010a0000 0x0000008000214000 0xff440c1fe39e027f 0xbfe88183fc73c04f

def z1120 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xf3fc33f81f83ff85 0xfe7f867f03f07ff0

def z1121 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6dd3c387187c3c62 0x8dba7870e30f878c

def z1122 : W := mkw 0xe41fbbf6d6000904 0x7c83f77edac00120 0xffdfffffe4000180 0x1ffbfffffc800030

def z1123 : W := mkw 0x5202d2a788745462 0x0a405a54f10e8a8c 0xfffbf3e79c7ffc67 0xffff7e7cf38fff8c

def z1124 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffdfffffe46383fb 0x1ffbfffffc8c707f

def z1125 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x9e9fffffe0000000 0x13d3fffffc000000

def z1126 : W := mkw 0x610292a6c020c0d1 0x0c205254d804181a 0xb6ea3267e463c3ff 0x76dd464cfc8c787f

def z1127 : W := mkw 0x5200c08308745462 0x0a401810610e8a8c 0x4931c183181c7c64 0x8926383063038f8c

def z1128 : W := mkw 0x18016c001f5b0000 0x23002d8003eb6000 0x1dd3fc001fff8003 0xe3ba7f8003fff000

def z1129 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xfffbc3e79c7e7fff 0xffff787cf38fcfff

def z1130 : W := mkw 0x1280440929de362a 0x02500881253bc6c5 0x000000001b9c3c00 0x8000000003738780

def z1131 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xe935cfffe00043fc 0x1d26b9fffc00087f

def z1132 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1e9ffc001fff8003 0x43d3ff8003fff000

def z1133 : W := mkw 0x110252248870c0d1 0x02204a44910e181a 0xfffbf3e49c7fffff 0xffff7e7c938fffff

def z1134 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x96ca3064846383fb 0x72d9460c908c707f

def z1135 : W := mkw 0x18016c001f5b0000 0x23002d8003eb6000 0x1f47fc001fff8003 0xe3e8ff8003fff000

def z1136 : W := mkw 0x02800401210e102a 0x005000802421c205 0xff440c1fe39e007b 0xbfe88183fc73c00f

def z1137 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x4913c183187c3c00 0x89227830630f8780

def z1138 : W := mkw 0x1002420408704040 0x02004840810e0808 0x6df3c384187c7c66 0xedbe7870830f8f8c

def z1139 : W := mkw 0x981d6d501f5b0000 0x7303adaa03eb6000 0x1fdfffe01fff8003 0xe3fbfffc03fff000

def z1140 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0xcb1dcdfb60000000 0x1963b9bf6c000000

def z1141 : W := mkw 0x5302c2870874d4f3 0x0a605850e10e9a9e 0x6df3c387187c7ffe 0xedbe7870e30f8fff

def z1142 : W := mkw 0xe01fbbf6c0204040 0x7c03f77ed8040808 0xfffffffff8607c66 0xffffffffff0c0f8c

def z1143 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x69d1c383181c3c00 0x8d3a387063038780

def z1144 : W := mkw 0x8400015800802b04 0x1080002b00100560 0xe3f403f81b807f85 0xfc7e807f03700ff0

def z1145 : W := mkw 0x410292a68020c0d1 0x08205254d004181a 0xb6fbf3e48463c3ff 0x76df7e7c908c787f

def z1146 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1fdffc049fff807b 0xe3fbff8093fff00f

def z1147 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb6ca3264846383fb 0x16d9464c908c707f

def z1148 : W := mkw 0x001d280000000000 0x6003a50000000000 0x5fdffc1b60000000 0x0bfbff836c000000

def z1149 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff440c1fe7ffb27f 0xffe88183fcfff64f

def z1150 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x4d13c183187c3c02 0x89a27830630f8780

def z1151 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x96aa32648463c3fb 0x52d5464c908c787f

def z1152 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xfffbf3e71c7fffe7 0xffff7e7ce38ffffc

def z1153 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6d71c387181c7c66 0xadae3870e3038f8c

def z1154 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff640e7fe39e73ff 0xbfec81cffc73ce7f

def z1155 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x00bbf3e01c7fffff 0xe0177e7c038fffff

def z1156 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xedf3c387987c7e7e 0xfdbe7870f30f8fcf

def z1157 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffffffffe0004004 0x7ffffffffc000800

def z1158 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff440c1fe39e307a 0x9fe88183fc73c60f

def z1159 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x03fc03e01f807f85 0xe07f807c03f00ff0

def z1160 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x4db3c387187c7c62 0xc9b67870e30f8f8c

def z1161 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1fdffc07ffff8003 0xe3fbff80fffff000

def z1162 : W := mkw 0x02800409218e322a 0x005000812431c645 0xed440c1fe39c327e 0xbda88183fc73864f

def z1163 : W := mkw 0x1e8044093fdf3b2e 0x03d0088127fbe765 0x002000001fffffff 0xe004000003ffffff

def z1164 : W := mkw 0x5200c08308745462 0x0a401810610e8a8c 0x4931c183187c7c00 0xc9263830630f8f80

def z1165 : W := mkw 0x410292a68020c0d1 0x08205254d004181a 0xbeebf2678463c3ff 0x77dd7e4cf08c787f

def z1166 : W := mkw 0x8400015816802b04 0x1080002b02d00560 0xe36403f81f807f85 0xfc6c807f03f00ff0

def z1167 : W := mkw 0x18016c00095b0000 0x23002d80012b6000 0x1d07fc0003ff8002 0x83a0ff80007ff000

def z1168 : W := mkw 0x02800409218e322a 0x005000812431c645 0xffce3c1fe39e327f 0xbff9c783fc73c64f

def z1169 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe40043fd 0x7ffffffffc80087f

def z1170 : W := mkw 0x601fbaa6c0000000 0x6c03f754d8000000 0xffdffc1fe0000000 0x1ffbff83fc000000

def z1171 : W := mkw 0x010010208020c0d1 0x002002041004181a 0xb2e832608463c3ff 0x765d064c108c787f

def z1172 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe3fc03f81b807f84 0x9c7f807f03700ff0

def z1173 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x6df3c387987c7c7e 0xedbe7870f30f8f8f

def z1174 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x5b1dfd9b60000000 0x0b63bfb36c000000

def z1175 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xdf1ffdffe0000000 0x1be3ffbffc000000

def z1176 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x7dd7ff9fe0000000 0x0fbafff3fc000000

def z1177 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x4dd3c183181c3c00 0x89ba783063038780

def z1178 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xebdffffb60000000 0x1d7bffff6c000000

def z1179 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe4038001 0x1ffbfffffc807000

def z1180 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x7ffbf387187c7c66 0xefff7e70e30f8f8c

def z1181 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x7fdffc001fffb007 0xeffbff8003fff600

def z1182 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffffffffe463c387 0x7ffffffffc8c7870

def z1183 : W := mkw 0xe103bbf6c020c0d1 0x3c20777ed804181a 0xfeebffffe463c3ff 0x7fdd7ffffc8c787f

def z1184 : W := mkw 0x6003baa6c0000000 0x2c007754d8000000 0xffd7ff9fe0000000 0x1ffafff3fc000000

def z1185 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x4d11c187181c3c62 0x89a23830e303878c

def z1186 : W := mkw 0xe01db9f2c0000000 0x7c03b73e58000000 0xdfdffdfbe0000000 0x1bfbffbf7c000000

def z1187 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb7ee326487e3c3ff 0xf6fdc64c90fc787f

def z1188 : W := mkw 0x401faa8600000000 0x6803f550c0000000 0xffdfff9fe0000000 0x1ffbfff3fc000000

def z1189 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0xe915cd9fe0000000 0x1d22b9b3fc000000

def z1190 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x24ea32640463c3ff 0x649d464c808c787f

def z1191 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0x5fdffffb60000000 0x0bfbffff6c000000

def z1192 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xbfee3e648463c3ff 0x77fdc7cc908c787f

def z1193 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x49b3c383187c7c66 0xe9367870630f8f8c

def z1194 : W := mkw 0x18016c00095b0000 0x23002d80012b6000 0x1fcffc0007ff8003 0xe3f9ff8000fff000

def z1195 : W := mkw 0xe11fbbf6d620c0d1 0x7c23f77edac4181a 0xffffffffffe3c3ff 0xfffffffffffc787f

def z1196 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xbeea3e67e463c3ff 0x77dd47ccfc8c787f

def z1197 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff640c1fe79e73ff 0xffec8183fcf3ce7f

def z1198 : W := mkw 0xe003bbf6c0000000 0x3c00777ed8000000 0xe801cfffe0000000 0x1d0039fffc000000

def z1199 : W := mkw 0x0000000000000000 0x0000000000000000 0xb6ea32648463c3ff 0x76dd464c908c787f

def z1200 : W := mkw 0xe003bbf6c0000000 0x3c00777ed8000000 0xff47ffffe0000000 0x1fe8fffffc000000

def z1201 : W := mkw 0xe01fabd640000000 0x7c03f57ac8000000 0x6915cf9f60000000 0x0d22b9f3ec000000

def z1202 : W := mkw 0x410292a68020c0d1 0x08205254d004181a 0xfffbf3e79c63ffff 0xffff7e7cf38c7fff

def z1203 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xf3fc03f89f827f9d 0xfe7f807f13f04ff3

def z1204 : W := mkw 0x02800409218e322a 0x005000812431c645 0xff440c1fe39e027b 0x1fe88183fc73c04f

def z1205 : W := mkw 0xe01fbbf6c0204040 0x7c03f77ed8040808 0xffffffffe0004064 0x1ffffffffc00080c

def z1206 : W := mkw 0x02800409218e322a 0x005000812431c645 0xf2040c1fe39e327f 0xbe408183fc73c64f

def z1207 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x6df3f387187dfc66 0xedbe7e70e30fbf8c

def z1208 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x82bc03f81f807f85 0xf057807f03f00ff0

def z1209 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x5d15cd9fe0000000 0x0ba2b9b3fc000000

def z1210 : W := mkw 0xe01da9d240000000 0x7c03b53a48000000 0x69d5cf9b60000000 0x0d3ab9f36c000000

def z1211 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xfff3c387987c7c66 0xfffe7870f30f8f8c

def z1212 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xedd7cfffe0000000 0x1dbaf9fffc000000

def z1213 : W := mkw 0xe41fbbf6c0000904 0x7c83f77ed8000120 0xffffffffe0004d80 0x1ffffffffc0009b0

def z1214 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xf3fc0ff8ff807f85 0xfe7f81ff1ff00ff0

def z1215 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe463c1fa 0x5ffffffffc8c783f

def z1216 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe0600002 0x7ffbfffffc0c0000

def z1217 : W := mkw 0x0000000000000000 0x0000000000000000 0xffd7cc1fe0000000 0x1ffaf983fc000000

def z1218 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1d9ffc001fff8002 0xc3b3ff8003fff000

def z1219 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe3800001 0xbffbfffffc700000

def z1220 : W := mkw 0x02800409218e322a 0x005000812431c645 0x9f440c1fe39e027b 0xb3e88183fc73c04f

def z1221 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xbffbf2648463c3ff 0x77ff7e4c908c787f

def z1222 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb6ee3e7ce463c3ff 0x76ddc7cf9c8c787f

def z1223 : W := mkw 0x010212248020c0d1 0x002042449004181a 0x14aa32648463c3ff 0x6295464c908c787f

def z1224 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x4911c183181c3c66 0xa92238306303878c

def z1225 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xf7fa33e48463c3ff 0x7eff467c908c787f

def z1226 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x7ff3c387187e7c67 0xeffe7870e30fcf8c

def z1227 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0xeffbc3e7187c7c66 0xfdff787ce30f8f8c

def z1228 : W := mkw 0x02800409218e322a 0x005000812431c645 0xfd040c1fe39e327e 0x9fa08183fc73c64f

def z1229 : W := mkw 0x1280440929de322a 0x02500881253bc645 0x000000001bfe327f 0xe0000000037fc64f

def z1230 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xfffbf3e7987c7ffe 0xffff7e7cf30f8fff

def z1231 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe463c183 0x7ffffffffc8c7830

def z1232 : W := mkw 0x06800409218e3b2e 0x00d000812431c765 0xff640c1fe39e7fff 0xbfec8183fc73cfff

def z1233 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffdfffffe063827f 0x3ffbfffffc0c704f

def z1234 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb6fa33e49c63cfff 0x76df467c938c79ff

def z1235 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6df3c387187e7e7f 0xedbe7870e30fcfcf

def z1236 : W := mkw 0x02800409218e322a 0x005000812431c645 0xeb440c1fe39c327d 0xbd688183fc73864f

def z1237 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xfc9bffffe0000000 0x1f937ffffc000000

def z1238 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xb6fbf3e49c7fffff 0xf6df7e7c938fffff

def z1239 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6ffbc3871c7c7c67 0xedff7870e38f8f8c

def z1240 : W := mkw 0xc01e83d600000000 0x5803d07ac0000000 0xffdfcfffe0000000 0x1ffbf9fffc000000

def z1241 : W := mkw 0x010010208020c0d1 0x002002041004181a 0x92083060846383fb 0x1241060c108c707f

def z1242 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xff4ffc7fe0000000 0x1fe9ff8ffc000000

def z1243 : W := mkw 0xe41da9d256000904 0x7c83b53a4ac00120 0x49bdcffb7c004d80 0x4937b9ff6f8009b0

def z1244 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x4931c383181c7c00 0x8926387063038f80

def z1245 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe1f403f81b807f84 0xfc3e807f03700ff0

def z1246 : W := mkw 0x02800409218e322a 0x005000812431c645 0x5d040c1fe39e327f 0xaba08183fc73c64f

def z1247 : W := mkw 0x5200c08308745462 0x0a401810610e8a8c 0x69f1c383187c7c66 0xed3e3870630f8f8c

def z1248 : W := mkw 0x5200c08308745462 0x0a401810610e8a8c 0x0031c180187c7c66 0xe0063830030f8f8c

def z1249 : W := mkw 0x02800409218e322a 0x005000812431c645 0x5f440c1fe39e307b 0xabe88183fc73c60f

def z1250 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0x5d13f187987fbc7a 0x8ba27e30f30ff78f

def z1251 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0xbfdffc049fff8003 0xf7fbff8093fff000

def z1252 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x6dfbc3e71c7c7de6 0xedbf787ce38f8fbc

def z1253 : W := mkw 0xe01fbbf6c0204040 0x7c03f77ed8040808 0xffdfffffe0600062 0x1ffbfffffc0c000c

def z1254 : W := mkw 0x6003baa6c0000000 0x2c007754d8000000 0xfc03fc1fe0000000 0x1f807f83fc000000

def z1255 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x0917fc001bfd8000 0x8122ff80037fb000

def z1256 : W := mkw 0xe01fbbf6c0204040 0x7c03f77ed8040808 0xffffffffe46043e7 0x7ffffffffc8c087c

def z1257 : W := mkw 0x1000400008500000 0x02000800010a0000 0xfffbf3e01c7fff87 0xffff7e7c038ffff0

def z1258 : W := mkw 0xe41fbbf6d6000904 0x7c83f77edac00120 0xffdffffff8000c00 0x1ffbffffff000180

def z1259 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe7fe03f81fe07f87 0xfcffc07f03fc0ff0

def z1260 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x69b3c387187c7c64 0xcd367870e30f8f8c

def z1261 : W := mkw 0xe003bbf6c0000000 0x3c00777ed8000000 0x5c03fd9fe0000000 0x0b807fb3fc000000

def z1262 : W := mkw 0x849c015836802b0c 0x5093802b06d00561 0xe3fc03f8ff807f9d 0xfc7f807f1ff00ff3

def z1263 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x4911c183187c3c02 0xe9223830630f8780

def z1264 : W := mkw 0xe41fbbf6d6000904 0x7c83f77edac00120 0xfffffffffc004f85 0x7fffffffff8009f0

def z1265 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x3ffffe001fffc007 0xe7ffffc003fff800

def z1266 : W := mkw 0xe11fbbf6c0008091 0x7c23f77ed8001012 0xffdfffffe0000398 0x1ffbfffffc000073

def z1267 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xf7fe33fc9fe3ffff 0xfeffc67f93fc7fff

def z1268 : W := mkw 0x8400015816802b04 0x1080002b02d00560 0xe1f003f81f807f85 0xfc3e007f03f00ff0

def z1269 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xfff3c3e7987e7fff 0xfffe787cf30fcfff

def z1270 : W := mkw 0xe01fbbf6c0204040 0x7c03f77ed8040808 0xffffffffe062427f 0x7ffffffffc0c484f

def z1271 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0x61fc03f81f807d84 0xec3f807f03f00fb0

def z1272 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x0bdffc001ffd8001 0xe17bff8003ffb000

def z1273 : W := mkw 0x181d68001e510000 0x6303ad0003ca2000 0x0fdff0001ffd8003 0xe1fbfe0003ffb000

def z1274 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xff55cfffe0000000 0x1feab9fffc000000

def z1275 : W := mkw 0x981d6d501f5b0000 0x7303adaa03eb6000 0xffdfffffffff8003 0xfffbfffffffff000

def z1276 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x60b3c387187c7c66 0xec167870e30f8f8c

def z1277 : W := mkw 0x8d1f3f7c97abebd5 0x71a3e7ef92f57d7a 0xb6ee3e7c87e3c3ff 0x76ddc7cf90fc787f

def z1278 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb2aa32648463c3fd 0x5655464c908c787f

def z1279 : W := mkw 0xe01fbbf6c0000000 0x7c03f77ed8000000 0xffdfffffe4000001 0x7ffbfffffc800000

def z1280 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1ffffc001ffffc07 0xe3ffff8003ffff80

def z1281 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1fdffc001fff827f 0xe3fbff8003fff04f

def z1282 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x6911c187181c3c64 0x8d223830e303878c

def z1283 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xffea32678463c3ff 0x7ffd464cf08c787f

def z1284 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x1f4ffc0007ff8003 0xa3e9ff8000fff000

def z1285 : W := mkw 0xe11fbbf6c020c0d1 0x7c23f77ed804181a 0xffffffffe00243ff 0x3ffffffffc00487f

def z1286 : W := mkw 0x1000400008500000 0x02000800010a0000 0x4911c180181c3c00 0x8922383003038780

def z1287 : W := mkw 0x5200c08308745462 0x0a401810610e8a8c 0x4df3c183187c7c66 0xe9be7830630f8f8c

def z1288 : W := mkw 0x8c1d2d58178b2b04 0x7183a5ab02f16560 0x120c3c1807838001 0x0241878300f07000

def z1289 : W := mkw 0xe001a9d240000000 0x3c00353a48000000 0x4801cd9b60000000 0x090039b36c000000

def z1290 : W := mkw 0x5200c08308541422 0x0a401810610a8284 0x49d1c183181c3c00 0xe93a383063038780

def z1291 : W := mkw 0xe01fabd640000000 0x7c03f57ac8000000 0x4d17cd9f60000000 0x09a2f9b3ec000000

def z1292 : W := mkw 0x5302d2a78874d4f3 0x0a605a54f10e9a9e 0xeffbc3e79c7c7fff 0xfdff787cf38f8fff

def z1293 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xf7fc03f81f827f87 0xfeff807f03f04ff0

def z1294 : W := mkw 0x9c1d6d501f5b0904 0x7383adaa03eb6120 0xfffffff81fffcd83 0xffffffff03fff9b0

def z1295 : W := mkw 0x010212248020c0d1 0x002042449004181a 0xb7fa32649c63c3ff 0xf6ff464c938c787f

def z1296 : W := mkw 0xe01da9d256000000 0x7c03b53a4ac00000 0x4915cd9b7b800000 0x8922b9b36f700000

def z1297 : W := mkw 0x841c015816802b04 0x5083802b02d00560 0xe3fc03f81fe3ff87 0xfc7f807f03fc7ff0

def z1298 : W := mkw 0x5202c28708745462 0x0a405850e10e8a8c 0x7df3cf87f87c7c66 0xefbe79f0ff0f8f8c

def z1299 : W := mkw 0x02800409218e322a 0x005000812431c645 0xfb040c1fe39e327d 0x9f608183fc73c64f

def z1300 : W := mkw 0x1200400108541022 0x02400800210a8204 0x6df3c387187c7c66 0xedbe7870e30f8f8c

def z1301 : W := mkw 0x5302c2870874d4f3 0x0a605850e10e9a9e 0x6df3c387187ffc7e 0xedbe7870e30fff8f

def z1302 : W := mkw 0x5302c2870874d4f3 0x0a605850e10e9a9e 0x7ffbf3871c7fffff 0xefff7e70e38fffff

def z1303 : W := mkw 0xe00293f6c0000000 0x1c00527ed8000000 0xffd7cfffe0000000 0x1ffaf9fffc000000

def z1304 : W := mkw 0x181d6c001f5b0000 0x6303ad8003eb6000 0x7fdffc071fff8003 0xeffbff80e3fff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z6,z0,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z9,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z10,z5])],[(0,[z0,z1,z11,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z12,z13]),(1,[z0,z1,z2,z3,z14,z8]),(0,[z15,z0,z1,z2,z3,z8,z5])],[(0,[z0,z0,z1,z2,z3,z8,z5]),(0,[z16,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z2,z3,z18,z8,z5])],[(0,[z0,z1,z2,z19,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z20]),(0,[z0,z1,z2,z21,z22,z8,z5]),(0,[z0,z1,z2,z7,z23,z8,z5]),(0,[z0,z1,z24,z2,z3,z8,z5]),(0,[z0,z25,z1,z2,z3,z8,z5])],[(1,[z0,z1,z2,z3,z8,z26]),(0,[z0,z1,z2,z3,z27,z8,z5]),(0,[z0,z1,z28,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z29])],[(0,[z0,z1,z2,z3,z4,z8,z5]),(0,[z0,z30,z2,z3,z8,z31,z5]),(0,[z0,z1,z2,z3,z8,z32,z5]),(1,[z0,z1,z2,z33,z8,z5]),(0,[z0,z1,z34,z2,z3,z8,z12]),(0,[z0,z35,z1,z2,z3,z8,z5]),(0,[z0,z1,z36,z2,z3,z37,z8]),(0,[z0,z1,z2,z38,z3,z8,z5])],[(0,[z39,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z40,z2,z3,z8,z5]),(0,[z0,z1,z41,z2,z3,z8,z5])],[(1,[z1,z30,z2,z3,z8,z12]),(0,[z6,z42,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z43,z7,z8,z5]),(0,[z0,z0,z1,z2,z3,z8,z17]),(0,[z44,z0,z2,z43,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z45,z5])]],
   [[(0,[z1,z2,z7,z3,z21,z8,z5]),(1,[z1,z2,z3,z21,z8,z12]),(0,[z0,z1,z2,z3,z8,z46,z5]),(0,[z0,z1,z2,z3,z8,z47,z17]),(0,[z0,z1,z2,z3,z48,z8,z5]),(0,[z0,z1,z3,z49,z8,z50,z5]),(0,[z0,z1,z2,z3,z8,z51,z5])],[(0,[z52,z0,z1,z2,z3,z8,z5]),(0,[z42,z0,z1,z2,z21,z8,z5]),(0,[z0,z1,z53,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z54,z31,z5]),(1,[z0,z1,z55,z56,z8,z5]),(0,[z57,z0,z1,z2,z8,z47,z5])],[(0,[z0,z1,z2,z21,z58,z8,z5]),(0,[z0,z59,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z60]),(0,[z0,z59,z1,z34,z3,z8,z5]),(0,[z0,z61,z1,z62,z2,z3,z8])],[(0,[z63,z0,z1,z2,z3,z8,z5]),(0,[z64,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z41,z2,z3,z8,z17]),(0,[z0,z1,z2,z3,z8,z65,z5]),(0,[z0,z1,z55,z2,z22,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z66]),(0,[z0,z1,z67,z2,z3,z8,z5]),(0,[z0,z1,z41,z2,z3,z8,z68])],[(0,[z0,z1,z2,z3,z8,z5,z69]),(0,[z0,z1,z70,z2,z3,z8,z5]),(0,[z71,z0,z1,z2,z3,z8,z5]),(0,[z0,z72,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z73]),(0,[z0,z1,z2,z21,z8,z74,z5]),(0,[z75,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z76,z3,z8,z5])],[(0,[z0,z1,z2,z77,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z78,z5]),(1,[z0,z1,z79,z3,z8,z5])],[(0,[z0,z1,z2,z80,z3,z8,z17]),(0,[z81,z0,z1,z2,z3,z8,z5]),(0,[z82,z0,z1,z2,z3,z8,z83]),(0,[z0,z1,z84,z2,z3,z8,z5]),(0,[z0,z1,z11,z3,z22,z8,z5])],[(0,[z85,z0,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z86,z12]),(0,[z0,z1,z2,z3,z87,z8,z5]),(0,[z0,z59,z1,z2,z3,z8,z17]),(0,[z0,z1,z2,z3,z22,z8,z17]),(0,[z0,z1,z88,z3,z89,z8,z5]),(0,[z0,z1,z90,z2,z3,z8,z5])]],
   [[(0,[z91,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z30,z2,z21,z8,z5]),(0,[z0,z1,z2,z7,z54,z8,z5]),(0,[z92,z0,z1,z2,z7,z8,z5]),(0,[z63,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z2,z93,z3,z8,z17]),(0,[z94,z0,z1,z2,z3,z8,z5]),(1,[z1,z2,z95,z3,z8,z5]),(0,[z0,z1,z96,z2,z3,z8,z5])],[(0,[z0,z1,z2,z7,z8,z5,z97]),(1,[z0,z1,z2,z3,z8,z98]),(0,[z99,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z100]),(0,[z0,z1,z2,z3,z58,z8,z5])],[(0,[z0,z1,z2,z3,z101,z8,z5]),(0,[z0,z1,z2,z21,z8,z5,z68]),(0,[z102,z0,z1,z2,z7,z8,z5])],[(1,[z0,z1,z2,z103,z8,z5]),(0,[z104,z0,z105,z2,z3,z8,z5]),(1,[z0,z1,z11,z22,z8,z5])],[(0,[z0,z106,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z107,z3,z8,z5]),(0,[z0,z1,z2,z7,z21,z8,z5]),(0,[z0,z1,z2,z108,z3,z8,z5]),(0,[z0,z1,z109,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z87,z8,z17]),(0,[z110,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z111,z5])],[(0,[z91,z0,z1,z2,z3,z8,z17]),(0,[z16,z0,z1,z2,z112,z8,z5]),(0,[z113,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z17,z114]),(0,[z0,z1,z2,z115,z3,z8,z5]),(0,[z82,z0,z1,z116,z2,z3,z8]),(0,[z0,z1,z2,z3,z117,z8,z5])],[(0,[z0,z1,z2,z21,z118,z8,z5]),(0,[z0,z1,z2,z3,z8,z119,z5]),(0,[z0,z1,z120,z2,z3,z8,z5]),(0,[z44,z0,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z121]),(0,[z0,z1,z2,z3,z58,z8,z17]),(0,[z122,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z123,z8,z5]),(0,[z0,z124,z1,z2,z3,z8,z5]),(0,[z125,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z126,z5])],[(0,[z0,z1,z127,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z128,z8,z5]),(0,[z129,z0,z1,z2,z101,z8,z5]),(1,[z0,z1,z2,z3,z130,z5]),(0,[z0,z1,z2,z21,z8,z31,z5]),(0,[z0,z131,z1,z2,z3,z8,z5]),(0,[z0,z61,z2,z3,z8,z132,z5]),(0,[z0,z1,z2,z3,z8,z5,z133]),(1,[z0,z1,z88,z3,z8,z5])]],
   [[(0,[z129,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z62,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z134,z5]),(0,[z135,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z136,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z74,z17]),(0,[z137,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z138,z5]),(1,[z0,z1,z2,z139,z8,z5]),(0,[z0,z1,z2,z3,z8,z74,z68])],[(0,[z102,z42,z1,z2,z3,z8,z5]),(0,[z140,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z7,z8,z5,z83]),(0,[z141,z0,z1,z2,z3,z8,z5]),(0,[z142,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z50,z5]),(1,[z0,z1,z2,z93,z8,z97])],[(0,[z0,z1,z2,z21,z8,z17,z5]),(1,[z0,z1,z143,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z144,z5])],[(0,[z0,z1,z145,z2,z7,z8,z5]),(0,[z102,z0,z1,z2,z146,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z147]),(0,[z0,z1,z2,z3,z148,z5,z68]),(0,[z57,z0,z1,z149,z3,z8,z5])],[(0,[z0,z1,z150,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z14,z8,z5]),(0,[z0,z1,z2,z3,z8,z151,z5]),(0,[z0,z1,z2,z152,z3,z8,z5]),(0,[z0,z1,z2,z3,z118,z8,z5])],[(0,[z0,z1,z153,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z154]),(0,[z42,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z5,z155]),(0,[z0,z1,z2,z3,z8,z5,z156])],[(1,[z0,z1,z2,z3,z8,z69]),(0,[z0,z157,z1,z2,z21,z8,z5]),(0,[z0,z61,z1,z2,z3,z8,z17]),(0,[z0,z1,z158,z2,z3,z8,z5]),(0,[z0,z1,z2,z159,z3,z8,z5]),(0,[z0,z61,z1,z2,z3,z8,z68]),(0,[z160,z0,z1,z2,z3,z8,z5])]],
   [[(0,[z0,z1,z2,z3,z8,z5,z161]),(0,[z0,z1,z2,z3,z8,z162,z5]),(0,[z0,z1,z2,z3,z8,z163,z5])],[(0,[z164,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z165]),(0,[z0,z1,z166,z2,z3,z8,z5]),(0,[z0,z1,z167,z2,z3,z8,z5]),(0,[z168,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z56,z21,z8,z5]),(0,[z0,z1,z2,z3,z54,z8,z12]),(0,[z0,z1,z2,z3,z8,z17,z5]),(0,[z0,z1,z2,z3,z37,z8,z17]),(0,[z0,z1,z2,z3,z118,z8,z17])],[(0,[z0,z1,z2,z169,z3,z8,z5]),(1,[z0,z1,z2,z3,z170,z5]),(0,[z0,z1,z153,z2,z3,z8,z17]),(0,[z0,z171,z1,z2,z21,z8,z5]),(0,[z172,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z31,z17]),(0,[z0,z1,z2,z3,z8,z5,z173])],[(0,[z91,z0,z1,z2,z174,z8,z5]),(0,[z102,z1,z30,z2,z3,z8,z5]),(0,[z129,z0,z1,z2,z3,z8,z175]),(0,[z0,z1,z2,z176,z3,z8,z5]),(0,[z104,z0,z1,z2,z7,z8,z5]),(0,[z0,z1,z55,z2,z7,z8,z5]),(0,[z0,z1,z2,z177,z3,z8,z5]),(0,[z104,z0,z1,z2,z178,z8,z5]),(0,[z179,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z158,z2,z3,z8,z17]),(0,[z0,z1,z180,z2,z3,z8,z5])],[(0,[z0,z1,z30,z2,z3,z8,z12]),(0,[z102,z1,z2,z3,z21,z8,z5]),(0,[z0,z1,z2,z181,z7,z8,z5]),(0,[z182,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z183,z8,z5]),(0,[z0,z1,z184,z2,z3,z8,z5])],[(0,[z0,z1,z2,z185,z3,z8,z5]),(0,[z0,z1,z2,z3,z186,z8,z5]),(0,[z0,z187,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z21,z8,z12]),(0,[z0,z1,z2,z188,z3,z8,z5])],[(0,[z189,z0,z1,z2,z3,z8,z5]),(0,[z75,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z17,z17]),(0,[z0,z1,z2,z3,z8,z17,z68]),(0,[z0,z171,z1,z2,z190,z8,z5]),(0,[z0,z191,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z192,z5]),(1,[z193,z1,z2,z3,z8,z5]),(0,[z0,z194,z1,z2,z3,z8,z5])]],
   [[(0,[z0,z1,z2,z7,z148,z8,z5]),(0,[z0,z1,z195,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z17,z5,z12]),(0,[z57,z0,z1,z2,z3,z47,z5])],[(0,[z16,z0,z1,z2,z7,z8,z5]),(0,[z196,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z121]),(0,[z0,z1,z2,z197,z3,z8,z5]),(1,[z0,z1,z198,z2,z8,z5]),(0,[z0,z1,z2,z199,z3,z8,z5])],[(0,[z0,z200,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z86,z5]),(0,[z201,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z89,z68])],[(0,[z0,z1,z2,z202,z3,z8,z5]),(0,[z122,z0,z1,z2,z43,z3,z8]),(0,[z0,z1,z2,z3,z8,z5,z203]),(0,[z0,z1,z11,z2,z22,z8,z5]),(0,[z193,z0,z1,z2,z3,z8,z5])],[(0,[z91,z0,z1,z2,z3,z4,z5]),(0,[z6,z0,z1,z2,z3,z8,z204]),(0,[z205,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z17]),(0,[z92,z0,z1,z2,z3,z49,z5]),(0,[z0,z1,z2,z3,z8,z68,z206]),(0,[z0,z207,z1,z2,z3,z8,z5]),(0,[z57,z0,z208,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z209])],[(0,[z0,z1,z2,z190,z3,z8,z12]),(0,[z0,z1,z62,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z210,z8,z5]),(0,[z0,z1,z211,z2,z3,z8,z5])],[(0,[z212,z0,z1,z2,z3,z8,z5]),(0,[z0,z0,z1,z2,z7,z8,z5])],[(0,[z0,z1,z213,z2,z3,z8,z5])]],
   [[(0,[z113,z0,z1,z2,z3,z86,z5]),(0,[z113,z0,z1,z2,z3,z8,z214]),(0,[z215,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z34,z2,z3,z148,z5]),(1,[z0,z1,z2,z3,z216,z5]),(0,[z0,z1,z208,z2,z3,z8,z5])],[(0,[z0,z1,z2,z217,z3,z8,z5]),(0,[z0,z218,z1,z2,z3,z8,z17]),(0,[z0,z59,z1,z3,z8,z219,z5]),(0,[z0,z1,z2,z3,z8,z220,z5]),(0,[z0,z1,z2,z3,z221,z8,z5]),(1,[z0,z1,z2,z3,z222,z5])],[(0,[z0,z1,z34,z153,z3,z8,z5]),(0,[z0,z1,z2,z21,z223,z8,z5]),(0,[z0,z1,z224,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z225,z5])],[(1,[z0,z1,z2,z3,z8,z161]),(0,[z6,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z34,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z226]),(0,[z0,z1,z2,z3,z8,z227,z5]),(0,[z228,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z229,z5])],[(0,[z0,z157,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z230,z3,z8,z5]),(0,[z57,z0,z1,z2,z3,z58,z5])],[(0,[z0,z1,z2,z80,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z231,z5]),(0,[z0,z1,z2,z93,z3,z8,z97])],[(0,[z232,z0,z1,z2,z3,z8,z5]),(0,[z0,z59,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z148,z54,z5]),(0,[z0,z1,z116,z2,z8,z233,z5])],[(0,[z63,z0,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z93,z7,z8,z5]),(0,[z0,z1,z2,z234,z3,z8,z5])]],
   [[(0,[z235,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z236]),(0,[z0,z237,z1,z2,z3,z8,z5]),(0,[z0,z171,z1,z2,z3,z8,z12]),(0,[z44,z0,z59,z2,z3,z8,z5]),(0,[z82,z0,z1,z2,z3,z238,z5]),(0,[z0,z61,z1,z2,z3,z8,z132])],[(0,[z239,z0,z1,z2,z3,z8,z12]),(0,[z42,z0,z1,z2,z3,z8,z5]),(0,[z64,z0,z1,z2,z21,z8,z5]),(0,[z240,z0,z1,z2,z3,z8,z5]),(0,[z0,z241,z1,z2,z3,z8,z5])],[(0,[z129,z1,z2,z80,z3,z8,z5]),(0,[z0,z1,z2,z3,z49,z54,z5]),(0,[z0,z242,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z148,z8,z12]),(0,[z82,z0,z1,z2,z3,z8,z12]),(1,[z243,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z244,z8,z5]),(0,[z0,z1,z2,z8,z233,z5,z97])],[(1,[z0,z1,z2,z174,z8,z5]),(0,[z129,z0,z245,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z246]),(1,[z0,z1,z2,z247,z8,z5]),(0,[z102,z0,z1,z2,z248,z8,z5]),(0,[z0,z1,z62,z158,z3,z8,z5]),(0,[z0,z1,z2,z249,z3,z8,z5]),(1,[z0,z61,z2,z3,z8,z132])],[(0,[z91,z0,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z250,z3,z8,z5]),(0,[z0,z251,z1,z2,z3,z8,z5]),(0,[z243,z0,z1,z2,z3,z8,z5]),(0,[z0,z252,z1,z2,z3,z8,z5])],[(0,[z0,z1,z253,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z54,z8,z5]),(0,[z0,z254,z1,z2,z3,z8,z5]),(1,[z0,z255,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z256])],[(0,[z0,z1,z2,z3,z8,z175,z5]),(0,[z0,z1,z2,z7,z8,z233,z5]),(0,[z0,z1,z2,z257,z3,z8,z5]),(0,[z0,z1,z2,z3,z258,z8,z5]),(0,[z0,z1,z2,z3,z118,z8,z74]),(0,[z0,z1,z259,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z97]),(0,[z0,z1,z2,z3,z8,z260,z5]),(0,[z0,z1,z2,z3,z261,z8,z5])],[(1,[z42,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z5,z262]),(0,[z0,z263,z1,z2,z3,z8,z5])]],
   [[(1,[z0,z1,z2,z3,z8,z264]),(0,[z0,z1,z30,z2,z3,z8,z5]),(0,[z0,z1,z2,z265,z3,z8,z5]),(0,[z0,z266,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z267,z3,z8,z5]),(0,[z268,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z269,z8,z5]),(0,[z0,z1,z2,z3,z8,z68,z97])],[(0,[z0,z1,z2,z3,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z12,z12]),(0,[z0,z1,z116,z2,z3,z8,z17]),(0,[z270,z0,z1,z2,z3,z8,z5]),(0,[z271,z0,z1,z2,z3,z8,z5]),(0,[z272,z0,z1,z2,z3,z8,z5])],[(1,[z0,z105,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z17,z273]),(0,[z0,z1,z34,z3,z8,z5,z206]),(0,[z0,z1,z2,z3,z8,z5,z274])],[(0,[z85,z0,z2,z3,z8,z31,z5]),(0,[z0,z1,z2,z3,z275,z8,z5])],[(0,[z276,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z7,z3,z8,z5]),(0,[z0,z1,z2,z3,z86,z219,z5]),(0,[z0,z1,z2,z3,z8,z277,z5]),(0,[z92,z0,z2,z3,z8,z31,z5]),(0,[z0,z1,z2,z3,z278,z8,z5])],[(0,[z0,z279,z1,z2,z3,z8,z5]),(0,[z129,z0,z1,z153,z3,z8,z5]),(0,[z0,z1,z2,z280,z3,z8,z5]),(0,[z0,z1,z153,z3,z8,z219,z5]),(0,[z0,z1,z2,z7,z8,z219,z5]),(1,[z0,z1,z2,z281,z8,z5]),(0,[z102,z0,z1,z2,z3,z8,z12]),(0,[z0,z282,z1,z2,z3,z8,z5])],[(0,[z0,z1,z283,z2,z3,z8,z5]),(0,[z129,z0,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z7,z8,z5,z12]),(0,[z0,z61,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z284]),(0,[z0,z1,z2,z3,z8,z5,z285]),(1,[z64,z0,z1,z3,z8,z206]),(1,[z0,z1,z149,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z286,z5]),(0,[z16,z0,z1,z2,z287,z8,z5]),(0,[z0,z1,z2,z7,z288,z8,z5]),(0,[z0,z1,z2,z248,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z289,z5]),(0,[z0,z1,z2,z3,z8,z5,z83]),(0,[z0,z1,z41,z2,z3,z89,z5])]],
   [[(0,[z290,z0,z1,z2,z3,z8,z5]),(1,[z1,z2,z21,z8,z86,z5]),(0,[z0,z1,z2,z3,z291,z8,z5]),(0,[z0,z1,z2,z3,z8,z292,z5]),(0,[z0,z1,z2,z190,z3,z8,z5]),(0,[z0,z218,z2,z3,z37,z8,z5]),(0,[z293,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z62,z34,z3,z8,z5]),(0,[z0,z1,z2,z294,z3,z8,z5]),(0,[z0,z1,z62,z2,z3,z8,z5]),(0,[z64,z0,z1,z3,z8,z5,z206]),(0,[z0,z1,z2,z3,z8,z295,z5])],[(0,[z0,z1,z2,z7,z3,z8,z17]),(0,[z0,z1,z2,z3,z296,z8,z5]),(0,[z0,z1,z2,z3,z297,z8,z5]),(0,[z0,z1,z298,z2,z3,z8,z5]),(0,[z299,z0,z1,z2,z3,z8,z5])],[(0,[z300,z0,z1,z2,z3,z8,z5]),(0,[z16,z157,z1,z2,z3,z8,z5]),(0,[z0,z1,z153,z2,z7,z8,z5]),(0,[z0,z1,z301,z2,z3,z8,z5]),(1,[z0,z1,z2,z188,z8,z5]),(0,[z0,z1,z2,z23,z58,z8,z5])],[(0,[z91,z0,z1,z2,z3,z8,z69]),(1,[z0,z1,z2,z3,z8,z236]),(0,[z0,z1,z158,z2,z7,z8,z5]),(0,[z0,z1,z2,z7,z8,z132,z5])],[(0,[z85,z0,z1,z2,z37,z8,z5]),(0,[z0,z1,z302,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z303,z5])],[(0,[z304,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z305,z21,z8,z5]),(0,[z0,z1,z150,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z214,z5]),(0,[z0,z218,z2,z3,z49,z8,z5])],[(0,[z91,z1,z30,z2,z3,z8,z5]),(0,[z16,z0,z157,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z306,z5]),(1,[z0,z1,z2,z3,z8,z307]),(0,[z0,z1,z2,z3,z8,z308,z5]),(0,[z0,z1,z41,z2,z3,z49,z5]),(0,[z0,z1,z2,z3,z8,z5,z309]),(0,[z57,z0,z1,z2,z3,z8,z310]),(0,[z0,z1,z2,z3,z311,z8,z5])],[(0,[z0,z157,z1,z2,z3,z8,z5]),(0,[z312,z0,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z313,z3,z8,z5]),(0,[z0,z1,z2,z3,z314,z8,z5]),(0,[z82,z315,z1,z2,z3,z8,z5])]],
   [[(0,[z0,z1,z253,z2,z21,z8,z5]),(0,[z1,z2,z3,z21,z8,z5,z12]),(0,[z0,z1,z2,z3,z8,z233,z12]),(0,[z0,z2,z3,z37,z8,z31,z5])],[(0,[z0,z1,z2,z33,z3,z8,z5]),(0,[z0,z1,z2,z316,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z317]),(0,[z0,z2,z3,z8,z132,z5,z83])],[(0,[z0,z318,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z21,z8,z119,z5]),(0,[z319,z0,z1,z2,z7,z8,z5]),(0,[z104,z0,z1,z2,z320,z8,z5]),(0,[z0,z1,z2,z3,z8,z8,z5]),(0,[z0,z1,z2,z3,z321,z8,z5]),(0,[z0,z1,z2,z56,z3,z8,z5]),(1,[z0,z1,z116,z2,z8,z233])],[(0,[z91,z0,z1,z2,z322,z8,z5]),(1,[z0,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z323]),(1,[z0,z1,z2,z178,z8,z5]),(0,[z104,z0,z1,z2,z3,z54,z5]),(0,[z0,z171,z1,z2,z3,z8,z5]),(0,[z324,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z325,z8,z5]),(0,[z326,z0,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z54,z8,z86,z5]),(0,[z0,z1,z327,z2,z3,z8,z5]),(0,[z328,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z5,z329]),(0,[z330,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z55,z2,z58,z8,z5]),(0,[z0,z1,z2,z331,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z332,z5]),(0,[z0,z187,z1,z2,z3,z8,z5]),(0,[z0,z200,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z333,z5]),(0,[z0,z1,z2,z3,z8,z334,z5]),(0,[z0,z1,z2,z3,z8,z335,z5])],[(0,[z0,z1,z158,z80,z3,z8,z5]),(0,[z104,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z219,z12]),(0,[z0,z1,z2,z56,z3,z8,z17]),(0,[z0,z59,z1,z43,z3,z8,z5])]],
   [[(1,[z0,z1,z2,z7,z8,z17]),(0,[z0,z218,z1,z2,z7,z8,z5]),(0,[z336,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z190,z8,z5,z97]),(0,[z0,z1,z337,z2,z3,z8,z5])],[(0,[z0,z1,z338,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z89,z5,z68])],[(0,[z0,z59,z157,z2,z3,z8,z5]),(0,[z0,z1,z2,z190,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z332,z17]),(0,[z0,z1,z2,z23,z3,z47,z5]),(0,[z339,z0,z1,z2,z3,z8,z5])],[(0,[z57,z0,z1,z2,z3,z8,z12]),(0,[z340,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z222,z5]),(0,[z0,z1,z2,z3,z341,z8,z5])],[(0,[z113,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z2,z3,z8,z342,z5]),(0,[z0,z1,z2,z3,z8,z132,z12]),(1,[z0,z1,z2,z146,z8,z5]),(0,[z0,z343,z1,z2,z3,z8,z5]),(0,[z0,z1,z344,z2,z3,z8,z5]),(0,[z345,z0,z1,z2,z3,z8,z5])],[(0,[z346,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z119,z17]),(1,[z0,z171,z2,z37,z8,z5]),(1,[z0,z1,z2,z3,z8,z151])],[(0,[z347,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z10])]],
   [[(0,[z0,z1,z2,z21,z348,z8,z5]),(0,[z349,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z350,z3,z8,z5]),(1,[z0,z1,z2,z23,z58,z5])],[(0,[z91,z0,z157,z2,z3,z8,z5]),(0,[z351,z0,z1,z2,z3,z8,z5]),(0,[z6,z0,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z12,z68])],[(1,[z104,z1,z2,z3,z86,z5]),(0,[z0,z1,z116,z2,z37,z8,z5])],[(0,[z0,z1,z2,z3,z8,z352,z5]),(0,[z0,z1,z2,z3,z8,z5,z353]),(0,[z0,z1,z2,z3,z49,z5,z68]),(0,[z0,z1,z34,z2,z3,z8,z5]),(0,[z0,z354,z1,z2,z3,z8,z5])],[(0,[z16,z0,z1,z2,z3,z8,z236]),(0,[z355,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z356,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z357,z5]),(0,[z0,z1,z2,z3,z358,z8,z5]),(0,[z312,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z359,z2,z3,z8,z5]),(0,[z0,z1,z360,z2,z3,z8,z5]),(0,[z82,z0,z2,z3,z8,z5,z83])],[(0,[z0,z1,z361,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z310])],[(0,[z129,z0,z1,z2,z3,z130,z5]),(0,[z239,z0,z1,z153,z3,z8,z5]),(0,[z0,z1,z2,z21,z8,z86,z5]),(0,[z0,z1,z2,z21,z8,z5,z206]),(1,[z0,z1,z2,z3,z8,z323]),(0,[z0,z1,z2,z7,z89,z8,z5]),(0,[z362,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z363]),(0,[z0,z1,z2,z3,z8,z5,z364])],[(0,[z0,z1,z2,z3,z348,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z365]),(0,[z239,z0,z1,z2,z21,z8,z5]),(0,[z104,z0,z1,z267,z3,z8,z5]),(0,[z0,z1,z2,z23,z3,z58,z5])]],
   [[(1,[z102,z1,z2,z21,z8,z5]),(0,[z82,z0,z1,z2,z21,z8,z5]),(0,[z0,z1,z116,z2,z7,z8,z5]),(0,[z0,z1,z34,z2,z3,z8,z17]),(1,[z0,z59,z158,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z366,z5]),(0,[z0,z1,z2,z3,z8,z367,z5])],[(0,[z0,z1,z359,z2,z3,z8,z17]),(0,[z0,z1,z2,z3,z358,z8,z17]),(0,[z0,z1,z2,z368,z3,z8,z5]),(0,[z369,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z41,z2,z3,z219,z5]),(0,[z64,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z62,z2,z3,z8,z74])],[(0,[z370,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z322,z8,z5]),(0,[z0,z1,z2,z93,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z371,z5]),(0,[z0,z1,z2,z3,z8,z372,z5]),(0,[z0,z1,z41,z2,z3,z118,z8])],[(0,[z0,z1,z153,z43,z3,z8,z5]),(0,[z0,z59,z158,z2,z3,z8,z5]),(0,[z373,z0,z1,z2,z3,z8,z5]),(0,[z0,z374,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z375,z8,z5])],[(0,[z91,z0,z1,z2,z3,z8,z264]),(0,[z0,z1,z2,z3,z8,z376,z5]),(0,[z0,z1,z180,z2,z3,z8,z17]),(0,[z0,z1,z2,z3,z377,z8,z5]),(0,[z0,z2,z3,z49,z8,z31,z5])],[(0,[z92,z0,z1,z2,z3,z31,z5]),(0,[z0,z1,z34,z3,z148,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z206])],[(0,[z378,z0,z1,z2,z3,z8,z5]),(0,[z16,z1,z2,z3,z8,z5,z12]),(0,[z64,z0,z1,z2,z3,z8,z17]),(1,[z0,z1,z2,z3,z321,z5]),(0,[z0,z1,z2,z3,z8,z379,z5]),(0,[z0,z380,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z381,z5]),(0,[z0,z1,z2,z7,z49,z8,z5]),(0,[z0,z105,z1,z2,z3,z8,z5]),(0,[z382,z0,z1,z2,z3,z8,z5]),(0,[z75,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z2,z37,z8,z5,z97]),(0,[z0,z1,z62,z3,z8,z219,z5])]],
   [[(0,[z383,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z7,z7,z8,z5]),(0,[z0,z1,z2,z3,z148,z86,z5]),(0,[z0,z1,z2,z3,z8,z5,z384]),(0,[z0,z1,z2,z3,z385,z8,z5])],[(0,[z0,z386,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z287,z8,z5]),(0,[z0,z1,z2,z3,z3,z8,z5]),(0,[z0,z1,z2,z280,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z387]),(0,[z0,z1,z2,z3,z388,z8,z5]),(0,[z0,z1,z2,z3,z219,z5,z68])],[(0,[z0,z1,z2,z389,z3,z8,z5]),(0,[z0,z1,z2,z37,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z86,z17]),(0,[z0,z1,z390,z2,z3,z8,z5]),(0,[z0,z1,z391,z2,z3,z8,z5]),(0,[z0,z1,z392,z2,z3,z8,z5])],[(0,[z393,z0,z1,z2,z3,z8,z5]),(0,[z102,z0,z1,z2,z21,z8,z5]),(0,[z0,z1,z394,z2,z21,z8,z5]),(0,[z0,z1,z395,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z12]),(0,[z0,z1,z2,z3,z8,z5,z396]),(0,[z64,z0,z1,z2,z3,z222,z5]),(0,[z0,z1,z2,z3,z8,z397,z5]),(0,[z0,z1,z2,z398,z3,z8,z5])],[(0,[z0,z1,z2,z3,z288,z8,z5]),(0,[z0,z1,z2,z3,z399,z8,z5]),(0,[z85,z0,z1,z2,z190,z8,z5]),(0,[z0,z218,z1,z2,z3,z49,z5]),(0,[z0,z1,z2,z400,z3,z8,z5])],[(0,[z401,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z41,z2,z7,z8,z5]),(0,[z0,z1,z11,z2,z58,z8,z5]),(0,[z0,z1,z402,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z403,z5])],[(0,[z129,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z80,z3,z8,z219,z5]),(0,[z0,z1,z2,z3,z8,z404,z5]),(0,[z0,z1,z301,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z13]),(0,[z113,z0,z1,z2,z281,z8,z5]),(0,[z0,z1,z2,z3,z405,z8,z5]),(0,[z406,z0,z1,z2,z3,z8,z5]),(0,[z0,z407,z1,z2,z3,z8,z5])],[(0,[z102,z16,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z204,z5]),(0,[z44,z0,z1,z2,z21,z8,z5]),(0,[z0,z1,z11,z2,z3,z8,z12]),(0,[z408,z0,z1,z2,z3,z8,z5])]],
   [[(0,[z409,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z89,z8,z12]),(0,[z0,z1,z2,z3,z8,z5,z410]),(1,[z0,z1,z2,z3,z8,z310]),(0,[z0,z1,z2,z3,z8,z411,z5])],[(0,[z1,z153,z2,z80,z3,z8,z5]),(0,[z0,z1,z2,z21,z54,z8,z5]),(0,[z412,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z413,z2,z3,z8,z5]),(0,[z0,z1,z55,z56,z3,z8,z5]),(0,[z57,z0,z1,z2,z23,z8,z5])],[(0,[z91,z0,z1,z414,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z365]),(0,[z0,z1,z2,z23,z21,z8,z5]),(0,[z0,z1,z2,z21,z8,z5,z97]),(0,[z0,z1,z415,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z416,z8,z5])],[(0,[z0,z1,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z417,z5]),(0,[z129,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z418,z2,z3,z8,z5]),(0,[z419,z0,z1,z2,z3,z8,z5]),(0,[z42,z1,z2,z7,z3,z8,z5]),(0,[z0,z1,z420,z2,z3,z8,z5]),(0,[z0,z1,z2,z421,z3,z8,z5]),(0,[z82,z0,z1,z2,z93,z3,z8]),(0,[z0,z1,z2,z3,z422,z8,z5]),(0,[z0,z1,z423,z2,z3,z8,z5])],[(0,[z91,z0,z1,z2,z3,z424,z5]),(1,[z0,z279,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z307,z5]),(0,[z0,z1,z2,z3,z37,z8,z12]),(0,[z0,z1,z2,z3,z8,z12,z425]),(1,[z0,z1,z2,z248,z8,z5]),(0,[z0,z1,z426,z2,z3,z8,z5]),(0,[z0,z427,z1,z2,z3,z8,z5]),(0,[z312,z0,z1,z2,z3,z8,z428])],[(0,[z0,z218,z157,z2,z3,z8,z5]),(0,[z0,z1,z2,z21,z21,z8,z5]),(0,[z0,z1,z2,z305,z3,z8,z5]),(0,[z0,z1,z2,z43,z3,z8,z12]),(0,[z0,z1,z43,z3,z8,z5,z206]),(0,[z0,z1,z2,z429,z3,z8,z5]),(0,[z0,z1,z3,z22,z8,z219,z5]),(0,[z0,z1,z2,z3,z8,z5,z430])],[(0,[z0,z1,z2,z431,z3,z8,z5]),(0,[z0,z1,z2,z56,z7,z8,z5]),(0,[z75,z0,z1,z2,z247,z8,z5]),(0,[z0,z1,z2,z3,z8,z432,z5]),(0,[z0,z61,z1,z2,z3,z118,z8])],[(1,[z0,z1,z2,z3,z8,z204]),(0,[z0,z1,z433,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z434,z8,z5]),(1,[z85,z0,z2,z190,z8,z5]),(0,[z312,z0,z1,z2,z3,z8,z5]),(0,[z312,z0,z1,z34,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z435,z5])]],
   [[(0,[z42,z113,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z436,z8,z5]),(0,[z437,z0,z1,z2,z3,z8,z5]),(0,[z0,z438,z1,z2,z3,z8,z5])],[(0,[z42,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z2,z7,z8,z439,z5]),(1,[z0,z1,z2,z320,z8,z5]),(0,[z0,z1,z440,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z49,z8,z12]),(0,[z0,z1,z441,z2,z3,z8,z5])],[(0,[z129,z0,z1,z2,z3,z8,z161]),(0,[z0,z1,z2,z442,z3,z8,z5]),(0,[z0,z1,z2,z3,z443,z8,z5])],[(0,[z0,z1,z245,z2,z3,z8,z5]),(0,[z239,z0,z1,z2,z103,z8,z5]),(0,[z0,z1,z2,z21,z8,z5,z83]),(0,[z0,z1,z2,z3,z444,z8,z12]),(0,[z0,z1,z2,z3,z8,z17,z132])],[(0,[z0,z1,z445,z2,z3,z8,z5]),(0,[z113,z0,z1,z2,z7,z8,z5]),(1,[z0,z1,z2,z3,z8,z387]),(0,[z0,z1,z2,z3,z8,z17,z226]),(1,[z44,z0,z43,z3,z8,z5]),(1,[z0,z1,z2,z3,z238,z5]),(0,[z0,z1,z2,z3,z446,z8,z5]),(0,[z0,z1,z2,z3,z8,z447,z5]),(0,[z448,z0,z1,z2,z3,z8,z5]),(1,[z449,z1,z2,z3,z8,z5])],[(1,[z0,z1,z2,z101,z8,z5]),(0,[z104,z0,z1,z2,z21,z8,z5]),(0,[z0,z1,z55,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z54,z8,z17]),(0,[z85,z0,z1,z2,z3,z8,z12]),(0,[z450,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z451,z5]),(0,[z0,z1,z2,z3,z452,z8,z5])],[(0,[z0,z1,z453,z2,z3,z8,z5]),(0,[z393,z0,z1,z2,z21,z8,z5]),(0,[z92,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z5,z454]),(0,[z455,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z456,z5])],[(0,[z0,z1,z2,z3,z8,z264,z5]),(0,[z0,z1,z457,z2,z3,z8,z5])]],
   [[(0,[z0,z1,z30,z2,z3,z8,z17]),(0,[z0,z1,z2,z3,z8,z5,z458]),(0,[z82,z0,z1,z62,z2,z3,z8])],[(0,[z0,z1,z2,z3,z21,z8,z17]),(1,[z122,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z3,z8,z459,z5]),(0,[z460,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z198,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z461,z8,z5])],[(0,[z0,z1,z2,z3,z462,z8,z5]),(0,[z57,z0,z1,z2,z21,z8,z5]),(0,[z64,z0,z1,z2,z3,z8,z74]),(0,[z0,z1,z2,z3,z118,z8,z97])],[(0,[z0,z1,z463,z2,z3,z8,z5])],[(0,[z44,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z464,z2,z3,z8,z5])],[(0,[z104,z0,z1,z2,z3,z86,z5]),(0,[z64,z0,z61,z1,z2,z3,z8])],[(0,[z465,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z12,z20]),(0,[z0,z1,z2,z3,z8,z12,z466]),(0,[z0,z2,z190,z3,z37,z8,z5]),(0,[z467,z0,z1,z2,z3,z8,z5]),(0,[z82,z0,z61,z2,z3,z8,z5]),(0,[z0,z1,z55,z11,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z468,z5]),(0,[z0,z1,z2,z58,z8,z47,z5]),(0,[z0,z1,z469,z2,z3,z8,z5])],[(0,[z0,z1,z34,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z470,z8,z5]),(0,[z0,z1,z2,z23,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z17,z97]),(0,[z0,z1,z2,z234,z43,z3,z8]),(0,[z0,z1,z56,z3,z22,z8,z5]),(0,[z312,z0,z1,z2,z3,z148,z5]),(0,[z0,z1,z2,z8,z192,z219,z5]),(0,[z1,z2,z93,z95,z3,z8,z5])]],
   [[(0,[z0,z1,z2,z190,z3,z8,z17]),(0,[z0,z1,z62,z2,z3,z8,z17]),(0,[z0,z61,z1,z2,z3,z8,z83]),(0,[z0,z1,z2,z93,z3,z8,z233])],[(1,[z0,z1,z414,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z170,z5]),(0,[z6,z0,z1,z2,z3,z8,z5]),(1,[z1,z2,z21,z8,z5,z12]),(0,[z0,z1,z2,z21,z148,z8,z5]),(0,[z0,z1,z471,z2,z3,z8,z5]),(0,[z0,z1,z472,z2,z3,z8,z5])],[(1,[z0,z1,z2,z3,z8,z175]),(0,[z0,z1,z2,z3,z8,z473,z5]),(0,[z474,z0,z1,z2,z3,z8,z5]),(0,[z475,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z216,z8,z5]),(0,[z0,z1,z476,z2,z3,z8,z5])],[(1,[z0,z1,z2,z3,z424,z5]),(0,[z0,z1,z2,z177,z7,z8,z5]),(0,[z0,z1,z2,z7,z8,z47,z5]),(0,[z113,z1,z2,z3,z54,z8,z5]),(0,[z0,z1,z2,z477,z3,z8,z5]),(0,[z0,z1,z2,z478,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z479,z5])],[(0,[z0,z1,z480,z2,z3,z8,z5]),(0,[z0,z1,z2,z481,z21,z8,z5]),(0,[z0,z1,z2,z482,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z483,z5]),(0,[z484,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z49,z8,z454]),(0,[z485,z0,z1,z2,z3,z8,z5])],[(0,[z64,z0,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z486,z8,z12]),(0,[z0,z1,z62,z43,z3,z8,z5]),(0,[z0,z1,z2,z3,z487,z8,z5]),(0,[z488,z0,z1,z2,z3,z8,z5]),(0,[z0,z489,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z93,z8,z5,z97])],[(0,[z0,z1,z2,z80,z21,z8,z5]),(0,[z0,z1,z490,z2,z3,z8,z5]),(0,[z491,z0,z1,z2,z3,z8,z5]),(0,[z6,z0,z1,z2,z3,z8,z17]),(0,[z75,z0,z1,z2,z7,z8,z5]),(1,[z0,z1,z267,z3,z8,z5]),(0,[z0,z1,z492,z2,z3,z8,z12])],[(0,[z493,z0,z1,z2,z3,z8,z5]),(0,[z0,z157,z1,z2,z3,z8,z17]),(0,[z239,z0,z1,z2,z3,z8,z5]),(0,[z129,z0,z1,z2,z33,z8,z5]),(0,[z113,z1,z2,z3,z21,z8,z5]),(0,[z0,z61,z1,z116,z2,z3,z8]),(0,[z0,z494,z1,z2,z3,z8,z5]),(0,[z0,z1,z495,z2,z3,z8,z5])]],
   [[(0,[z0,z242,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z93,z21,z8,z5]),(0,[z0,z1,z2,z7,z8,z46,z5]),(0,[z0,z1,z2,z3,z8,z17,z83]),(0,[z496,z0,z1,z2,z3,z8,z5]),(0,[z82,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z148,z8,z5])],[(1,[z129,z1,z80,z3,z8,z5]),(1,[z0,z1,z2,z21,z8,z12]),(0,[z0,z1,z2,z3,z8,z5,z497]),(1,[z0,z1,z2,z3,z8,z454]),(1,[z0,z208,z2,z3,z8,z5])],[(0,[z0,z1,z2,z7,z22,z8,z5]),(0,[z0,z1,z55,z2,z3,z8,z12]),(1,[z0,z1,z2,z8,z192,z5]),(0,[z0,z1,z2,z3,z498,z8,z5])],[(0,[z0,z1,z34,z80,z3,z8,z5]),(0,[z0,z1,z2,z499,z3,z8,z5]),(0,[z0,z171,z1,z2,z3,z8,z17]),(1,[z315,z1,z2,z3,z8,z5]),(0,[z57,z0,z1,z55,z2,z8,z5])],[(0,[z0,z1,z80,z43,z3,z8,z5]),(0,[z239,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z2,z3,z49,z8,z5]),(0,[z500,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z501,z8,z5]),(0,[z0,z1,z34,z3,z22,z8,z5]),(0,[z502,z0,z1,z2,z3,z8,z5])],[(1,[z16,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z148,z8,z17]),(0,[z82,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z503,z2,z3,z8,z5]),(1,[z82,z0,z2,z3,z8,z83]),(0,[z82,z0,z1,z2,z3,z8,z68]),(0,[z0,z1,z2,z3,z8,z504,z5])],[(0,[z104,z0,z1,z505,z3,z8,z5]),(0,[z0,z506,z1,z2,z3,z8,z5]),(0,[z85,z0,z218,z2,z3,z8,z5]),(0,[z507,z0,z1,z2,z3,z8,z5])],[(0,[z16,z0,z1,z2,z3,z8,z12]),(0,[z508,z0,z1,z2,z3,z8,z5]),(0,[z92,z0,z218,z2,z3,z8,z5])]],
   [[(0,[z509,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z103,z8,z5]),(0,[z510,z0,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z511,z12]),(0,[z0,z1,z2,z3,z8,z512,z5])],[(0,[z0,z1,z2,z7,z58,z8,z5]),(0,[z92,z0,z1,z2,z3,z8,z5]),(0,[z513,z0,z1,z2,z3,z8,z5])],[(0,[z129,z0,z1,z2,z7,z8,z5]),(0,[z239,z0,z1,z2,z356,z8,z5]),(0,[z0,z1,z2,z3,z514,z8,z5]),(0,[z0,z1,z2,z3,z515,z8,z5]),(0,[z0,z1,z516,z2,z3,z8,z5]),(0,[z0,z1,z517,z2,z3,z8,z5])],[(0,[z0,z1,z394,z2,z3,z8,z5]),(0,[z0,z1,z2,z7,z8,z74,z5]),(0,[z102,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z518,z3,z8,z5]),(0,[z0,z1,z2,z3,z519,z8,z5])],[(0,[z0,z1,z520,z2,z3,z8,z5]),(0,[z42,z1,z2,z3,z8,z86,z5]),(0,[z0,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z521,z5]),(0,[z0,z1,z2,z3,z522,z8,z5]),(0,[z0,z1,z2,z523,z3,z8,z5]),(0,[z0,z1,z524,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z525,z5])],[(0,[z91,z0,z1,z169,z3,z8,z5]),(0,[z0,z1,z11,z2,z21,z8,z5]),(0,[z0,z1,z2,z7,z526,z8,z5]),(0,[z0,z1,z2,z3,z8,z47,z12]),(0,[z0,z1,z2,z3,z139,z8,z5]),(0,[z0,z1,z2,z3,z527,z8,z5])],[(0,[z16,z0,z1,z2,z3,z8,z376]),(0,[z0,z1,z2,z3,z8,z98,z5]),(0,[z0,z1,z2,z3,z8,z528,z5]),(0,[z0,z1,z2,z529,z3,z8,z5]),(0,[z82,z0,z1,z360,z3,z8,z5]),(0,[z0,z1,z2,z530,z3,z8,z5]),(0,[z0,z1,z2,z3,z531,z8,z5]),(0,[z312,z0,z1,z3,z8,z219,z5]),(0,[z0,z1,z2,z532,z3,z8,z5]),(0,[z0,z1,z2,z3,z533,z8,z5])],[(0,[z0,z61,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z534,z21,z8,z5]),(0,[z0,z1,z2,z21,z8,z233,z5]),(0,[z44,z0,z1,z2,z3,z8,z5]),(0,[z44,z0,z1,z34,z3,z8,z5]),(0,[z0,z535,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z536]),(0,[z537,z0,z1,z2,z3,z8,z5])]],
   [[(0,[z42,z0,z1,z2,z7,z8,z5]),(0,[z0,z1,z41,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z5,z538]),(0,[z0,z1,z3,z148,z8,z219,z5])],[(0,[z0,z1,z2,z7,z8,z5,z68]),(1,[z312,z0,z1,z3,z219,z5]),(0,[z539,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z116,z2,z3,z8,z97])],[(0,[z0,z1,z2,z23,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z540])],[(0,[z0,z1,z2,z80,z3,z8,z12]),(0,[z0,z1,z2,z541,z3,z8,z5]),(0,[z542,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z43,z21,z8,z5]),(0,[z82,z243,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z543,z8,z5]),(0,[z544,z0,z1,z2,z3,z8,z5]),(0,[z0,z59,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z22,z8,z12]),(0,[z0,z1,z2,z545,z3,z8,z5]),(0,[z0,z1,z2,z546,z3,z8,z5])],[(0,[z0,z1,z2,z7,z118,z8,z5]),(0,[z0,z1,z2,z7,z37,z8,z5]),(0,[z0,z1,z145,z2,z3,z8,z5]),(0,[z104,z0,z395,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z86,z31,z5]),(0,[z63,z0,z1,z2,z3,z8,z12])],[(0,[z0,z1,z2,z3,z8,z5,z425]),(0,[z129,z0,z1,z80,z3,z8,z5]),(0,[z0,z1,z2,z21,z8,z219,z5]),(0,[z0,z1,z2,z7,z8,z31,z5]),(0,[z0,z1,z2,z3,z8,z439,z5]),(0,[z0,z1,z2,z547,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z233,z5]),(0,[z0,z1,z548,z2,z3,z8,z5])],[(0,[z0,z1,z30,z2,z7,z8,z5]),(0,[z0,z157,z2,z43,z3,z8,z5]),(0,[z0,z1,z2,z21,z8,z5,z12]),(0,[z0,z1,z2,z3,z8,z238,z5]),(0,[z0,z1,z2,z3,z549,z8,z5])]],
   [[(0,[z85,z0,z2,z190,z3,z8,z5])],[(0,[z6,z0,z1,z2,z3,z8,z26]),(0,[z0,z1,z550,z2,z3,z8,z5]),(0,[z0,z1,z2,z551,z3,z8,z5]),(0,[z0,z1,z552,z2,z3,z8,z5])],[(0,[z91,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z7,z8,z17,z5]),(0,[z0,z171,z2,z3,z37,z8,z5]),(0,[z553,z0,z1,z2,z3,z8,z5])],[(0,[z554,z0,z1,z2,z3,z8,z5]),(0,[z239,z1,z153,z2,z3,z8,z5]),(0,[z85,z0,z1,z2,z21,z8,z5]),(0,[z113,z0,z1,z2,z3,z54,z5]),(0,[z0,z1,z2,z3,z58,z8,z12]),(0,[z0,z1,z2,z3,z8,z233,z17]),(1,[z0,z1,z3,z8,z50,z5]),(0,[z57,z555,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z556,z8,z5]),(0,[z0,z1,z2,z3,z8,z233,z68]),(0,[z0,z1,z3,z89,z8,z225,z5])],[(0,[z0,z1,z2,z3,z8,z557,z5]),(0,[z558,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z21,z8,z5]),(0,[z92,z0,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z21,z8,z132,z5]),(0,[z0,z1,z2,z559,z3,z8,z5])],[(0,[z129,z0,z1,z2,z3,z170,z5]),(0,[z0,z1,z2,z3,z8,z246,z5]),(0,[z104,z0,z1,z2,z3,z8,z5]),(0,[z113,z0,z1,z2,z3,z8,z387]),(0,[z0,z1,z2,z3,z8,z74,z12]),(0,[z0,z1,z2,z3,z8,z560,z5]),(0,[z0,z218,z1,z2,z3,z31,z5]),(0,[z0,z1,z561,z2,z3,z8,z5]),(0,[z0,z1,z55,z2,z3,z8,z5]),(0,[z0,z1,z55,z34,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z219,z5]),(0,[z64,z0,z1,z2,z3,z216,z5])],[(0,[z0,z1,z2,z181,z3,z8,z5]),(1,[z0,z1,z2,z562,z8,z5]),(0,[z0,z1,z361,z3,z49,z8,z5]),(0,[z82,z0,z1,z2,z3,z8,z132])],[(0,[z0,z1,z563,z2,z3,z8,z5]),(0,[z0,z1,z62,z2,z7,z8,z5]),(0,[z0,z1,z2,z190,z7,z8,z5]),(0,[z0,z1,z2,z3,z49,z86,z5]),(0,[z0,z1,z2,z79,z3,z8,z5])]],
   [[(0,[z564,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z3,z8,z219,z5,z206]),(0,[z0,z1,z2,z3,z8,z5,z565]),(0,[z0,z555,z1,z2,z3,z8,z5])],[(0,[z566,z0,z1,z2,z3,z8,z5]),(0,[z0,z218,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z567,z3,z8,z5]),(0,[z0,z315,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z118,z8,z206])],[(0,[z0,z1,z2,z3,z568,z8,z5]),(0,[z0,z1,z2,z3,z8,z219,z17]),(0,[z0,z61,z1,z2,z93,z3,z8]),(0,[z57,z0,z1,z2,z3,z8,z5])],[(0,[z0,z569,z1,z2,z3,z8,z5]),(0,[z42,z0,z1,z2,z3,z8,z323]),(1,[z0,z1,z2,z202,z8,z5]),(0,[z0,z1,z2,z3,z8,z132,z5]),(0,[z82,z64,z0,z1,z2,z3,z8])],[(1,[z0,z1,z169,z3,z8,z5]),(0,[z0,z61,z1,z2,z3,z8,z12]),(0,[z0,z171,z1,z2,z37,z8,z5]),(0,[z570,z0,z1,z2,z3,z8,z5])],[(2,[z1,z2,z21,z8,z12]),(0,[z0,z1,z2,z571,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z424,z5]),(0,[z0,z157,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z17,z206]),(0,[z572,z0,z1,z2,z3,z8,z5]),(0,[z573,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z574,z5])],[(1,[z75,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z118,z8,z12]),(0,[z57,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z575,z2,z3,z8,z5])]],
   [[(0,[z0,z1,z153,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z5,z466]),(0,[z0,z1,z2,z3,z8,z31,z12]),(0,[z0,z1,z2,z3,z576,z8,z5]),(0,[z0,z1,z2,z3,z8,z47,z5]),(0,[z0,z1,z2,z3,z577,z8,z5])],[(0,[z0,z1,z158,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z578,z8,z5]),(0,[z0,z1,z116,z2,z3,z8,z233])],[(1,[z91,z30,z2,z3,z8,z5]),(0,[z16,z0,z30,z2,z3,z8,z5]),(0,[z0,z30,z2,z43,z3,z8,z5]),(0,[z0,z1,z2,z21,z8,z579,z5]),(0,[z0,z171,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z580,z8,z5]),(0,[z64,z0,z1,z2,z3,z8,z206]),(0,[z0,z1,z116,z2,z93,z8,z5])],[(0,[z239,z0,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z581,z5]),(0,[z102,z1,z2,z3,z8,z17,z5]),(0,[z0,z1,z2,z3,z582,z8,z5])],[(0,[z0,z1,z2,z583,z21,z8,z5]),(0,[z1,z2,z3,z21,z8,z86,z5]),(0,[z82,z0,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z17,z12]),(0,[z0,z584,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z114]),(0,[z0,z1,z2,z529,z3,z37,z8]),(0,[z449,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z7,z585,z8,z5]),(0,[z0,z1,z2,z143,z3,z8,z5]),(0,[z0,z1,z2,z3,z586,z8,z5])],[(0,[z587,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z80,z3,z8,z5]),(0,[z0,z1,z588,z2,z3,z8,z5]),(0,[z0,z1,z34,z2,z3,z219,z5]),(0,[z0,z1,z2,z589,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z458,z12]),(0,[z312,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z433,z2,z3,z8,z17]),(0,[z590,z0,z1,z2,z3,z8,z5]),(0,[z0,z591,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z22,z8,z5]),(0,[z0,z1,z88,z2,z3,z8,z5])]],
   [[(0,[z0,z592,z1,z2,z3,z8,z5]),(0,[z0,z1,z593,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z247,z8,z5]),(0,[z0,z1,z2,z93,z3,z8,z5])],[(0,[z594,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z116,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z579,z5]),(1,[z42,z1,z2,z7,z8,z5]),(1,[z113,z1,z2,z3,z54,z5]),(1,[z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z12,z97]),(0,[z0,z584,z1,z2,z3,z8,z17]),(0,[z0,z595,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z320,z3,z8,z5]),(0,[z0,z1,z195,z2,z3,z8,z12]),(0,[z0,z1,z2,z442,z3,z8,z17]),(0,[z0,z158,z2,z43,z3,z8,z5])],[(0,[z129,z0,z279,z2,z3,z8,z5]),(0,[z596,z0,z1,z2,z3,z8,z5]),(0,[z597,z0,z1,z2,z3,z8,z5]),(0,[z0,z598,z1,z2,z3,z8,z5]),(0,[z0,z599,z1,z2,z3,z8,z5]),(1,[z0,z1,z3,z8,z225,z5])],[(0,[z0,z1,z2,z3,z600,z8,z5]),(0,[z82,z0,z1,z2,z139,z8,z5]),(0,[z601,z0,z1,z2,z3,z8,z5])],[(0,[z16,z0,z1,z2,z21,z8,z5]),(1,[z0,z1,z505,z3,z8,z5]),(0,[z0,z1,z116,z2,z190,z8,z5]),(0,[z0,z1,z198,z2,z8,z219,z5]),(0,[z0,z1,z62,z3,z8,z74,z5]),(0,[z0,z1,z602,z2,z3,z8,z5]),(0,[z449,z1,z2,z93,z3,z8,z5]),(0,[z0,z1,z2,z603,z3,z8,z5])],[(0,[z0,z218,z1,z2,z3,z8,z12]),(0,[z44,z0,z1,z3,z8,z219,z5]),(0,[z0,z1,z2,z3,z8,z5,z428]),(0,[z604,z0,z1,z2,z3,z8,z5])],[(0,[z0,z59,z30,z2,z3,z8,z5]),(0,[z239,z0,z1,z80,z3,z8,z5]),(0,[z0,z1,z2,z21,z89,z8,z5]),(0,[z0,z1,z605,z2,z3,z8,z5]),(0,[z82,z0,z1,z143,z3,z8,z5]),(0,[z0,z255,z1,z2,z3,z8,z5])]],
   [[(1,[z0,z1,z2,z3,z8,z376]),(0,[z6,z1,z2,z3,z21,z8,z5]),(0,[z510,z0,z1,z2,z3,z8,z5]),(0,[z606,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z74,z5]),(0,[z0,z1,z2,z3,z607,z8,z5]),(0,[z608,z0,z1,z2,z3,z8,z5]),(0,[z57,z0,z255,z2,z3,z8,z5])],[(0,[z0,z609,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z5])],[(0,[z610,z0,z1,z2,z3,z8,z5]),(0,[z0,z0,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z526,z8,z5]),(0,[z0,z1,z2,z3,z281,z8,z5]),(0,[z0,z1,z2,z3,z8,z12,z83]),(0,[z0,z1,z41,z2,z3,z31,z5]),(0,[z611,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z612,z3,z8,z5]),(0,[z0,z1,z41,z2,z3,z148,z5])],[(0,[z613,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z481,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z614]),(0,[z0,z1,z2,z615,z3,z8,z5]),(0,[z0,z616,z1,z2,z3,z8,z5])],[(0,[z91,z0,z30,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z617,z5]),(0,[z0,z1,z2,z3,z618,z8,z5]),(0,[z0,z1,z11,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z118,z89,z8])],[(0,[z0,z1,z2,z174,z3,z8,z5]),(0,[z0,z1,z41,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z619,z5]),(0,[z0,z1,z2,z3,z620,z8,z5]),(0,[z0,z1,z621,z2,z3,z8,z5]),(0,[z0,z1,z11,z2,z56,z8,z5]),(0,[z57,z0,z1,z11,z2,z8,z5]),(0,[z0,z1,z2,z3,z8,z622,z5]),(0,[z0,z1,z623,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z89,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z68])],[(0,[z0,z1,z2,z534,z3,z8,z5]),(0,[z412,z0,z1,z2,z3,z8,z5]),(0,[z610,z0,z1,z2,z3,z8,z17]),(0,[z0,z61,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z624,z3,z8,z5])]],
   [[(0,[z0,z1,z2,z21,z49,z8,z5]),(0,[z625,z0,z1,z2,z3,z8,z5])],[(0,[z626,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z627,z5]),(0,[z0,z1,z2,z3,z8,z5,z628])],[(0,[z0,z59,z1,z2,z21,z8,z5]),(0,[z0,z1,z11,z2,z3,z8,z17]),(0,[z0,z1,z2,z3,z37,z8,z5]),(0,[z0,z1,z2,z3,z629,z8,z5])],[(0,[z157,z1,z30,z2,z3,z8,z5]),(0,[z63,z0,z1,z2,z21,z8,z5]),(0,[z75,z102,z1,z2,z3,z8,z5]),(0,[z75,z1,z2,z3,z8,z5,z12]),(0,[z0,z1,z2,z3,z89,z8,z17]),(0,[z0,z1,z2,z43,z3,z8,z5]),(0,[z630,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z31,z5]),(1,[z0,z1,z62,z3,z8,z74]),(0,[z0,z1,z2,z3,z89,z8,z68])],[(1,[z0,z395,z2,z3,z8,z5]),(0,[z0,z631,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z14,z49,z8]),(0,[z0,z1,z55,z3,z8,z219,z5]),(0,[z0,z1,z2,z3,z632,z8,z5])],[(0,[z0,z1,z53,z2,z3,z8,z5]),(0,[z0,z1,z505,z2,z3,z8,z5]),(0,[z104,z1,z2,z3,z8,z86,z5]),(0,[z44,z0,z1,z158,z3,z8,z5]),(0,[z0,z1,z2,z633,z3,z8,z5]),(0,[z0,z1,z2,z634,z3,z8,z5]),(1,[z555,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z21,z515,z8,z5]),(0,[z0,z1,z116,z2,z3,z8,z12])],[(0,[z0,z1,z2,z112,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z635,z5]),(0,[z0,z1,z2,z3,z8,z5,z636]),(0,[z82,z0,z1,z2,z3,z321,z5])]],
   [[(0,[z91,z0,z1,z2,z21,z8,z5]),(0,[z0,z637,z1,z2,z3,z8,z5]),(0,[z638,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z178,z8,z5]),(1,[z102,z1,z2,z3,z8,z17]),(0,[z0,z1,z2,z43,z3,z8,z17]),(0,[z639,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z640,z5]),(0,[z0,z1,z2,z3,z444,z8,z5]),(1,[z92,z0,z2,z3,z31,z5]),(0,[z0,z1,z2,z641,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z428])],[(0,[z104,z0,z1,z2,z3,z8,z98]),(0,[z0,z1,z2,z3,z8,z497,z12]),(0,[z312,z0,z1,z2,z3,z219,z5]),(0,[z0,z1,z642,z2,z3,z8,z5])],[(0,[z0,z1,z414,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z643,z8,z5]),(0,[z319,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z54,z219,z5]),(0,[z85,z0,z1,z2,z3,z8,z5]),(0,[z57,z0,z1,z79,z3,z8,z5])],[(1,[z0,z1,z2,z3,z8,z5]),(0,[z91,z16,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z644,z8,z5]),(0,[z0,z1,z2,z3,z49,z8,z17]),(0,[z645,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z646,z2,z3,z8,z5]),(0,[z0,z1,z62,z2,z3,z8,z206]),(0,[z0,z1,z2,z3,z118,z5,z68]),(0,[z0,z1,z2,z3,z647,z8,z5])],[(0,[z113,z0,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z648,z5]),(0,[z0,z1,z2,z3,z118,z8,z233])],[(0,[z649,z0,z1,z2,z3,z8,z5]),(0,[z129,z239,z1,z2,z3,z8,z5]),(0,[z42,z0,z1,z2,z3,z8,z307]),(0,[z0,z1,z2,z7,z3,z8,z12]),(0,[z57,z0,z1,z2,z7,z8,z5]),(0,[z650,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z651]),(0,[z0,z1,z149,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z652,z8,z5])],[(0,[z409,z0,z1,z2,z7,z8,z5]),(0,[z113,z0,z1,z2,z562,z8,z5]),(0,[z0,z1,z36,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z653]),(0,[z0,z1,z654,z2,z3,z8,z5])]],
   [[(0,[z0,z1,z2,z3,z655,z8,z5]),(1,[z6,z1,z2,z21,z8,z5]),(0,[z85,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z656,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z657])],[(0,[z0,z1,z658,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z659,z8,z5]),(1,[z1,z2,z3,z8,z17,z12]),(0,[z92,z0,z1,z2,z3,z8,z17]),(0,[z0,z218,z1,z2,z3,z8,z5]),(0,[z660,z0,z1,z2,z3,z8,z5])],[(0,[z661,z0,z1,z2,z3,z8,z5]),(0,[z239,z0,z1,z2,z3,z8,z365]),(0,[z0,z1,z2,z3,z146,z8,z5])],[(0,[z0,z1,z2,z3,z8,z662,z5]),(0,[z0,z1,z2,z562,z3,z8,z5]),(0,[z102,z0,z1,z2,z3,z8,z17]),(0,[z663,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z664,z5]),(0,[z0,z1,z2,z95,z3,z8,z5])],[(1,[z0,z245,z2,z3,z8,z5]),(0,[z0,z1,z301,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z665,z5]),(0,[z0,z1,z666,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z130,z8,z5]),(0,[z667,z0,z1,z2,z3,z8,z5]),(0,[z42,z1,z2,z3,z8,z5,z12]),(1,[z0,z1,z2,z234,z3,z8]),(0,[z0,z1,z2,z3,z8,z5,z668])],[(0,[z669,z0,z1,z2,z3,z8,z5]),(0,[z239,z0,z1,z2,z3,z8,z246]),(0,[z0,z1,z153,z2,z21,z8,z5]),(0,[z0,z1,z158,z153,z3,z8,z5]),(0,[z312,z0,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z670,z3,z8,z5]),(0,[z0,z671,z1,z2,z3,z8,z5])],[(1,[z0,z1,z2,z356,z8,z5]),(0,[z0,z1,z158,z2,z21,z8,z5]),(0,[z44,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z2,z672,z3,z8,z5]),(0,[z0,z1,z673,z2,z3,z8,z5]),(0,[z0,z674,z1,z2,z3,z8,z5])]],
   [[(0,[z675,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z676,z3,z8,z5])],[(0,[z0,z218,z30,z2,z3,z8,z5]),(0,[z677,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z26]),(0,[z0,z1,z2,z442,z7,z8,z5]),(0,[z0,z1,z2,z7,z8,z5,z155]),(0,[z0,z1,z2,z3,z8,z5,z273]),(0,[z0,z1,z2,z3,z8,z678,z5])],[(0,[z679,z0,z1,z2,z3,z8,z5]),(0,[z0,z157,z2,z3,z8,z31,z5]),(0,[z0,z1,z2,z3,z585,z8,z5]),(0,[z0,z1,z2,z482,z3,z8,z5]),(0,[z667,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z2,z23,z3,z8,z17]),(0,[z680,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z681,z3,z8,z5]),(1,[z0,z1,z360,z3,z8,z5]),(0,[z57,z0,z1,z2,z3,z8,z10]),(0,[z0,z1,z2,z3,z8,z5,z682])],[(0,[z683,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z486,z8,z5]),(0,[z0,z1,z684,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z685,z8,z5]),(0,[z686,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z41,z2,z3,z118,z5])],[(0,[z0,z1,z492,z2,z3,z8,z5]),(0,[z0,z1,z2,z583,z3,z8,z5]),(0,[z0,z1,z2,z56,z3,z8,z12]),(0,[z687,z0,z1,z2,z3,z8,z5]),(0,[z44,z0,z1,z43,z3,z8,z5]),(0,[z85,z0,z171,z2,z3,z8,z5]),(1,[z0,z1,z34,z3,z148,z5])],[(1,[z0,z1,z2,z7,z8,z12]),(0,[z688,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z223,z8,z5]),(1,[z1,z2,z7,z21,z8,z5]),(0,[z689,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z690,z2,z3,z8,z5]),(0,[z0,z1,z3,z8,z74,z5,z206])],[(0,[z0,z1,z2,z3,z322,z8,z5]),(0,[z75,z0,z1,z2,z21,z8,z5]),(0,[z0,z1,z691,z2,z3,z8,z5]),(1,[z0,z1,z36,z2,z3,z8]),(0,[z0,z1,z2,z3,z8,z5,z692]),(0,[z0,z1,z2,z3,z8,z5,z693]),(1,[z0,z1,z41,z2,z3,z118])]],
   [[(0,[z0,z1,z2,z3,z8,z12,z206]),(0,[z0,z1,z2,z3,z31,z5,z68]),(0,[z0,z1,z694,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z17,z538]),(0,[z0,z1,z2,z3,z695,z8,z5]),(0,[z0,z1,z55,z2,z56,z8,z5]),(0,[z312,z0,z1,z2,z3,z8,z151]),(0,[z0,z1,z116,z2,z3,z8,z5])],[(0,[z1,z30,z2,z3,z8,z5,z12]),(0,[z696,z0,z1,z2,z3,z8,z5]),(0,[z104,z0,z1,z2,z3,z8,z121]),(0,[z113,z0,z1,z2,z3,z8,z12]),(0,[z336,z0,z1,z2,z3,z8,z12])],[(1,[z113,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z697,z5]),(1,[z0,z1,z2,z529,z3,z8]),(0,[z0,z1,z2,z3,z8,z698,z5]),(0,[z0,z1,z2,z3,z8,z699,z5])],[(1,[z0,z1,z2,z112,z8,z5]),(1,[z0,z1,z2,z21,z8,z17]),(0,[z0,z1,z2,z21,z8,z5,z466]),(0,[z0,z1,z2,z21,z8,z47,z5]),(0,[z104,z113,z1,z2,z3,z8,z5]),(0,[z700,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z557,z17]),(0,[z82,z0,z1,z2,z3,z118,z8]),(0,[z64,z0,z1,z62,z3,z8,z5])],[(0,[z16,z0,z1,z2,z3,z8,z5]),(0,[z701,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z7,z8,z86,z5]),(0,[z0,z1,z2,z7,z8,z5,z206]),(0,[z104,z0,z1,z2,z3,z8,z17]),(0,[z0,z1,z55,z2,z3,z8,z17]),(0,[z0,z59,z1,z158,z3,z8,z5]),(1,[z0,z1,z361,z3,z8,z5]),(0,[z57,z193,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z702])],[(0,[z0,z1,z2,z3,z287,z8,z5]),(0,[z75,z0,z1,z2,z202,z8,z5]),(0,[z0,z1,z2,z3,z8,z511,z5]),(0,[z0,z1,z158,z3,z8,z5,z206]),(0,[z82,z0,z1,z2,z188,z8,z5]),(0,[z0,z1,z2,z3,z703,z8,z5]),(0,[z704,z0,z1,z2,z3,z8,z5]),(1,[z57,z0,z1,z2,z47,z5])],[(1,[z0,z1,z2,z3,z8,z214]),(0,[z0,z1,z2,z3,z8,z705,z5]),(0,[z0,z1,z2,z706,z3,z8,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z191,z1,z2,z21,z8,z5])],[(0,[z1,z2,z3,z8,z332,z12]),(0,[z0,z1,z707,z3,z8,z17]),(0,[z0,z1,z2,z3,z8,z708]),(0,[z0,z1,z3,z219,z68,z206]),(0,[z0,z1,z149,z3,z8,z310]),(0,[z0,z1,z3,z118,z8,z225])],[],[(0,[z0,z245,z2,z3,z130,z5]),(0,[z0,z1,z2,z3,z709,z5]),(0,[z243,z1,z2,z3,z8,z12]),(0,[z412,z0,z2,z3,z8,z83])],[(0,[z0,z1,z2,z174,z8,z12]),(0,[z0,z1,z2,z3,z710,z5]),(0,[z1,z2,z21,z118,z8,z12]),(0,[z1,z2,z3,z8,z119,z12]),(0,[z0,z1,z79,z21,z8,z5]),(0,[z0,z1,z2,z247,z8,z12]),(0,[z1,z338,z2,z3,z8,z12])],[(0,[z475,z1,z2,z21,z8,z5]),(0,[z0,z711,z2,z3,z8,z5]),(0,[z0,z1,z2,z712,z8,z5])],[(0,[z16,z1,z2,z3,z8,z713]),(0,[z1,z62,z2,z21,z8,z12]),(0,[z1,z2,z190,z21,z8,z12]),(0,[z0,z255,z2,z3,z8,z12])],[(0,[z0,z1,z2,z714,z8,z5]),(0,[z0,z1,z715,z2,z21,z8]),(0,[z0,z1,z716,z3,z8,z5]),(0,[z0,z1,z2,z3,z717,z8])],[(0,[z0,z1,z150,z22,z8,z5]),(0,[z0,z395,z2,z3,z8,z17]),(0,[z0,z1,z2,z718,z8,z5])],[(0,[z102,z1,z2,z287,z8,z5]),(0,[z0,z1,z2,z8,z719,z5]),(0,[z1,z2,z21,z8,z45,z5]),(0,[z0,z1,z2,z481,z515,z5]),(0,[z0,z2,z712,z3,z8,z5])],[(0,[z315,z1,z2,z3,z8,z17]),(0,[z0,z1,z3,z8,z720,z17])],[(0,[z0,z1,z721,z2,z3,z8]),(0,[z0,z1,z3,z8,z5,z722])],[(0,[z0,z1,z2,z3,z8,z723]),(0,[z0,z1,z2,z281,z8,z387]),(0,[z0,z1,z2,z724,z8,z5])],[(0,[z157,z1,z2,z21,z8,z12]),(0,[z1,z2,z159,z3,z8,z12]),(0,[z92,z0,z2,z3,z31,z17]),(0,[z0,z1,z2,z3,z8,z725]),(0,[z0,z1,z726,z3,z8,z5])],[(0,[z16,z1,z2,z287,z8,z12]),(0,[z0,z1,z2,z3,z727,z8]),(0,[z0,z1,z2,z21,z130,z5]),(0,[z0,z1,z2,z3,z728,z5]),(0,[z82,z1,z2,z21,z8,z12]),(0,[z0,z1,z88,z21,z8,z5]),(0,[z1,z2,z21,z8,z12,z97]),(0,[z0,z1,z729,z3,z8,z5]),(0,[z0,z1,z2,z281,z8,z12])],[(0,[z0,z1,z2,z3,z8,z730]),(0,[z6,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z731,z8,z5]),(0,[z0,z1,z2,z732,z8,z5]),(0,[z0,z1,z2,z3,z8,z733]),(0,[z555,z1,z2,z3,z8,z734]),(0,[z0,z1,z2,z3,z8,z735])]],
   [[(0,[z0,z1,z2,z3,z8,z17])],[(0,[z1,z2,z21,z8,z86,z12]),(0,[z171,z1,z2,z21,z8,z12]),(0,[z0,z1,z2,z188,z238,z5])],[(0,[z0,z1,z143,z21,z8,z5]),(0,[z0,z1,z2,z736,z8,z5]),(0,[z0,z1,z2,z737,z8,z5]),(0,[z0,z1,z738,z3,z8,z5])],[(0,[z0,z1,z2,z188,z8,z12]),(0,[z0,z1,z2,z739,z8,z5]),(0,[z740,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z234,z3,z8])],[(0,[z0,z1,z2,z7,z8,z204]),(0,[z449,z1,z2,z3,z8,z307]),(0,[z191,z1,z2,z3,z8,z12]),(0,[z1,z2,z3,z8,z17,z741]),(0,[z168,z0,z2,z3,z31,z5]),(0,[z0,z1,z2,z3,z222,z5])],[(0,[z0,z1,z2,z3,z424,z264]),(0,[z0,z1,z2,z356,z8,z5]),(0,[z1,z2,z714,z21,z8,z5]),(0,[z254,z1,z2,z21,z8,z5]),(0,[z1,z2,z3,z586,z8,z17]),(0,[z0,z171,z2,z712,z8,z5]),(0,[z0,z1,z2,z742,z8,z5])],[(0,[z0,z1,z2,z3,z8,z161]),(0,[z0,z1,z2,z3,z8,z743]),(0,[z0,z1,z2,z744,z8,z5]),(0,[z1,z2,z21,z8,z12,z83]),(0,[z0,z1,z267,z320,z8,z5]),(0,[z0,z1,z2,z3,z745,z8]),(0,[z0,z61,z2,z3,z8,z653]),(0,[z0,z1,z2,z746,z8,z5])],[(0,[z0,z1,z2,z442,z8,z97])],[(0,[z42,z1,z2,z248,z8,z5]),(0,[z0,z1,z360,z3,z8,z5]),(0,[z0,z1,z2,z3,z14,z321]),(0,[z0,z1,z747,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z748]),(0,[z0,z1,z2,z3,z8,z749]),(0,[z750,z1,z2,z3,z8,z5]),(0,[z0,z1,z55,z676,z8,z5]),(0,[z555,z255,z2,z3,z8,z5])],[(0,[z0,z1,z751,z3,z8,z5]),(0,[z0,z2,z752,z3,z8,z5]),(0,[z753,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z7,z8,z12]),(0,[z510,z1,z2,z21,z8,z12]),(0,[z0,z1,z2,z178,z8,z12]),(0,[z44,z0,z234,z43,z3,z8]),(0,[z0,z1,z2,z3,z8,z754])],[(0,[z1,z2,z7,z21,z8,z5]),(1,[z0,z1,z755,z8,z5]),(0,[z0,z1,z2,z756,z8,z5])],[(0,[z0,z1,z169,z3,z8,z69]),(0,[z129,z1,z80,z101,z8,z5]),(0,[z1,z394,z2,z21,z8,z12]),(0,[z282,z1,z2,z21,z8,z5]),(0,[z160,z1,z2,z21,z8,z5]),(0,[z193,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z757]),(0,[z0,z1,z36,z2,z3,z8])],[(0,[z0,z1,z2,z758,z8,z5]),(0,[z0,z759,z2,z3,z8,z5])]],
   [[(0,[z0,z1,z760,z3,z8,z12])],[(0,[z0,z1,z2,z21,z89,z68]),(0,[z0,z1,z2,z93,z8,z155]),(0,[z0,z1,z505,z3,z8,z98]),(0,[z0,z1,z34,z3,z443,z5])],[(0,[z0,z1,z2,z21,z321,z5])],[(0,[z0,z1,z2,z7,z8,z376]),(0,[z1,z301,z2,z21,z8,z5]),(0,[z0,z1,z359,z3,z8,z74])],[(0,[z91,z30,z2,z3,z8,z69]),(0,[z1,z2,z21,z54,z8,z12])],[(0,[z0,z1,z53,z526,z8,z5]),(0,[z0,z1,z2,z761,z8,z5]),(0,[z0,z1,z2,z3,z8,z762]),(0,[z0,z1,z2,z3,z8,z763])],[(0,[z0,z1,z169,z322,z8,z5]),(0,[z0,z1,z2,z146,z8,z12]),(0,[z315,z1,z2,z3,z118,z8]),(0,[z1,z2,z95,z3,z8,z119])],[(0,[z113,z1,z2,z21,z8,z17]),(0,[z0,z1,z2,z21,z216,z5]),(0,[z104,z1,z2,z3,z764,z5]),(0,[z0,z171,z2,z37,z8,z12]),(0,[z122,z0,z1,z2,z3,z765]),(0,[z0,z1,z2,z766,z8,z5])],[(0,[z0,z1,z767,z3,z8,z5]),(0,[z0,z1,z2,z112,z8,z17]),(0,[z0,z1,z2,z7,z8,z175]),(0,[z1,z2,z21,z21,z8,z12]),(0,[z570,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z768,z8,z5]),(0,[z0,z1,z2,z3,z14,z8])],[(0,[z0,z1,z2,z23,z58,z12]),(0,[z0,z1,z361,z3,z8,z17]),(0,[z0,z1,z2,z3,z769,z89])],[(0,[z0,z1,z2,z3,z770,z12]),(0,[z0,z1,z2,z3,z8,z771]),(0,[z0,z1,z2,z3,z8,z772])],[(0,[z129,z1,z80,z3,z8,z175]),(0,[z0,z1,z2,z3,z8,z26]),(0,[z104,z1,z2,z3,z86,z12]),(0,[z336,z0,z1,z3,z8,z206]),(0,[z0,z1,z2,z773,z8,z5])],[(0,[z91,z30,z2,z322,z8,z5]),(0,[z0,z1,z2,z3,z4,z17]),(0,[z0,z1,z2,z33,z8,z5]),(0,[z0,z1,z267,z7,z8,z5]),(0,[z0,z1,z267,z178,z8,z5]),(0,[z774,z0,z1,z3,z8,z12]),(0,[z243,z1,z360,z3,z8,z5]),(0,[z82,z0,z2,z624,z3,z8])],[(0,[z775,z1,z2,z3,z8,z5])],[(0,[z0,z1,z776,z3,z8,z5]),(0,[z0,z1,z2,z3,z769,z8])],[(1,[z1,z2,z287,z8,z12]),(0,[z1,z2,z777,z21,z8,z5]),(0,[z1,z2,z3,z21,z8,z12]),(0,[z0,z1,z2,z7,z8,z454]),(0,[z0,z1,z778,z3,z8,z5])]],
   [[(0,[z239,z1,z2,z21,z8,z12]),(0,[z555,z1,z2,z7,z8,z5]),(0,[z0,z1,z779,z3,z8,z5])],[(0,[z102,z1,z2,z21,z8,z12])],[(0,[z0,z1,z2,z21,z8,z246]),(0,[z0,z61,z2,z21,z8,z132]),(0,[z1,z338,z2,z21,z8,z5]),(0,[z345,z0,z2,z190,z8,z5]),(0,[z0,z780,z2,z3,z8,z5])],[(0,[z102,z1,z2,z7,z8,z17]),(0,[z0,z171,z36,z2,z37,z8]),(0,[z0,z1,z2,z3,z225,z68])],[(0,[z0,z157,z169,z3,z8,z5]),(0,[z0,z781,z2,z3,z8,z5]),(0,[z0,z1,z2,z7,z8,z428]),(1,[z0,z1,z2,z782,z5])],[(0,[z0,z1,z2,z3,z8,z783]),(0,[z0,z1,z55,z56,z8,z17]),(0,[z667,z0,z1,z3,z8,z114])],[(0,[z42,z1,z2,z21,z8,z12])],[(0,[z0,z1,z2,z21,z8,z264]),(0,[z0,z1,z150,z223,z8,z5]),(0,[z0,z1,z2,z3,z321,z12]),(0,[z0,z1,z2,z3,z8,z784]),(0,[z0,z1,z2,z3,z785,z5]),(0,[z0,z1,z2,z3,z8,z786])],[(0,[z0,z1,z2,z3,z8,z787]),(0,[z449,z1,z2,z21,z8,z5]),(0,[z0,z2,z3,z8,z5,z788])],[(0,[z0,z1,z79,z3,z8,z17]),(0,[z0,z1,z2,z3,z8,z789])],[(0,[z91,z790,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z791]),(0,[z0,z1,z469,z2,z3,z118])],[(0,[z0,z1,z2,z3,z8,z792]),(0,[z6,z1,z2,z714,z8,z5]),(0,[z0,z1,z2,z3,z8,z793]),(0,[z104,z1,z267,z3,z86,z5]),(0,[z0,z794,z2,z3,z8,z5]),(0,[z0,z1,z2,z795,z3,z8])],[(0,[z0,z1,z796,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z797]),(0,[z0,z1,z2,z3,z8,z798]),(0,[z0,z1,z2,z3,z799,z5])],[(0,[z0,z1,z2,z3,z8,z800]),(0,[z0,z1,z2,z7,z8,z801]),(0,[z102,z1,z2,z146,z8,z17])],[(0,[z0,z1,z2,z802,z8,z5]),(0,[z803,z1,z2,z3,z8,z5])],[(0,[z0,z245,z2,z7,z8,z5]),(0,[z0,z1,z2,z103,z8,z17]),(0,[z510,z1,z2,z3,z86,z5]),(0,[z0,z1,z11,z22,z8,z17]),(0,[z804,z1,z2,z3,z8,z5]),(0,[z805,z1,z2,z3,z8,z5])]],
   [[(0,[z1,z2,z21,z8,z119,z12])],[],[],[(0,[z16,z157,z2,z21,z8,z5]),(0,[z0,z1,z806,z3,z8,z5]),(0,[z0,z1,z2,z3,z130,z17]),(0,[z0,z1,z2,z8,z807,z5]),(0,[z1,z2,z21,z8,z12,z12]),(0,[z205,z1,z2,z3,z8,z12]),(0,[z0,z1,z88,z3,z8,z17]),(0,[z0,z1,z2,z3,z8,z10])],[(0,[z0,z1,z2,z3,z808,z5]),(0,[z0,z1,z2,z139,z8,z17]),(0,[z775,z1,z2,z529,z3,z8])],[(0,[z0,z1,z2,z21,z8,z307]),(0,[z0,z1,z809,z2,z7,z8]),(0,[z0,z1,z11,z526,z8,z5]),(0,[z0,z1,z2,z3,z444,z68])],[(0,[z0,z1,z2,z3,z8,z69]),(0,[z0,z1,z810,z3,z8,z5]),(0,[z700,z1,z2,z21,z8,z5]),(0,[z1,z2,z21,z8,z12,z13]),(0,[z0,z1,z2,z811,z3,z8]),(0,[z1,z116,z2,z95,z8,z5])],[(0,[z790,z30,z2,z3,z8,z5]),(0,[z0,z1,z34,z7,z148,z5]),(0,[z0,z1,z143,z3,z8,z17])],[],[(0,[z0,z1,z2,z812,z21,z8]),(0,[z1,z2,z7,z714,z8,z5])],[(0,[z0,z1,z2,z3,z170,z5]),(0,[z0,z1,z2,z3,z130,z161]),(0,[z0,z1,z2,z320,z8,z12]),(0,[z0,z1,z813,z2,z8,z5]),(0,[z312,z0,z1,z3,z219,z151])],[(0,[z0,z1,z814,z3,z8,z5]),(0,[z0,z245,z80,z3,z8,z5]),(0,[z0,z1,z2,z815,z3,z8])],[],[(0,[z0,z1,z2,z816,z3,z8]),(0,[z129,z1,z80,z21,z8,z5]),(0,[z0,z208,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z238,z12]),(0,[z449,z1,z2,z3,z8,z12]),(0,[z0,z1,z360,z139,z8,z5])],[(0,[z0,z1,z2,z322,z8,z5]),(0,[z0,z1,z2,z101,z8,z12]),(0,[z0,z1,z253,z305,z8,z5]),(0,[z42,z1,z2,z3,z8,z817])],[(0,[z0,z1,z2,z3,z8,z818]),(0,[z0,z1,z3,z8,z819,z17]),(0,[z0,z1,z820,z2,z3,z17])]],
   [[(0,[z0,z1,z2,z3,z8,z821]),(0,[z408,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z822,z5])],[(0,[z1,z2,z3,z533,z8,z12])],[(0,[z701,z1,z2,z21,z8,z5]),(0,[z1,z2,z534,z21,z8,z12]),(0,[z0,z105,z505,z3,z8,z5]),(0,[z0,z1,z2,z823,z8,z5])],[(0,[z91,z30,z414,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z824]),(0,[z42,z1,z2,z562,z8,z5]),(0,[z193,z1,z2,z3,z8,z17]),(0,[z160,z1,z2,z3,z8,z17])],[(0,[z0,z1,z2,z7,z14,z8]),(0,[z1,z301,z2,z95,z8,z5])],[(0,[z0,z1,z2,z287,z8,z5]),(0,[z0,z1,z825,z3,z8,z5]),(0,[z0,z1,z62,z3,z8,z458]),(0,[z0,z1,z198,z2,z8,z17]),(0,[z0,z1,z2,z3,z8,z826])],[(0,[z1,z2,z43,z21,z8,z12]),(0,[z242,z1,z2,z21,z8,z12]),(0,[z319,z0,z1,z2,z439,z5]),(0,[z0,z827,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z828]),(0,[z0,z1,z3,z8,z829,z5]),(0,[z0,z1,z830,z3,z8,z17]),(0,[z0,z1,z2,z3,z8,z831])],[(0,[z1,z2,z3,z8,z741,z12])],[(0,[z0,z1,z2,z832,z8,z5]),(0,[z485,z1,z80,z3,z8,z5]),(0,[z104,z1,z2,z21,z86,z5]),(0,[z833,z1,z2,z3,z8,z5]),(0,[z675,z0,z1,z3,z219,z5]),(0,[z0,z255,z2,z3,z8,z10])],[(0,[z0,z1,z2,z3,z834,z5]),(0,[z1,z2,z3,z8,z376,z12]),(0,[z0,z1,z2,z101,z8,z175]),(0,[z1,z440,z2,z21,z8,z5]),(0,[z0,z1,z776,z7,z8,z5]),(0,[z0,z1,z3,z416,z219,z5])],[(0,[z0,z1,z2,z835,z8,z5]),(0,[z0,z1,z2,z836,z8,z5]),(0,[z0,z1,z145,z280,z8,z5]),(0,[z0,z1,z267,z3,z54,z5]),(0,[z0,z1,z2,z3,z580,z68])],[(0,[z0,z1,z2,z3,z424,z12]),(0,[z0,z837,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z216,z17]),(0,[z0,z1,z3,z8,z838,z5])],[(0,[z0,z1,z2,z839,z8,z5]),(0,[z412,z30,z2,z3,z8,z5]),(0,[z0,z1,z840,z3,z8,z5]),(0,[z0,z1,z195,z2,z3,z486])],[(0,[z0,z1,z2,z3,z8,z365]),(0,[z304,z0,z43,z3,z8,z5]),(0,[z0,z841,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z842])],[(0,[z0,z1,z2,z33,z130,z5]),(0,[z0,z1,z267,z3,z8,z12]),(0,[z0,z1,z843,z3,z8,z5])]],
   [[(0,[z0,z279,z2,z3,z8,z5]),(0,[z0,z844,z2,z3,z8,z5]),(0,[z0,z1,z2,z248,z8,z5]),(0,[z1,z2,z37,z21,z8,z12]),(0,[z0,z1,z360,z3,z321,z5]),(0,[z0,z1,z2,z3,z118,z321]),(0,[z845,z1,z2,z3,z8,z5])],[(0,[z1,z2,z95,z3,z8,z97])],[(0,[z0,z1,z2,z3,z4,z69]),(0,[z0,z1,z715,z2,z3,z8]),(0,[z129,z1,z80,z3,z8,z12]),(0,[z349,z1,z2,z21,z8,z5]),(0,[z1,z2,z3,z8,z817,z12]),(0,[z0,z208,z2,z3,z8,z12])],[(0,[z71,z1,z2,z3,z8,z12]),(0,[z0,z1,z394,z2,z8,z233]),(0,[z1,z2,z95,z7,z8,z5]),(0,[z0,z1,z846,z3,z8,z5])],[(0,[z0,z1,z2,z8,z847,z5]),(0,[z0,z1,z2,z7,z8,z98]),(0,[z0,z1,z2,z178,z8,z98])],[],[(0,[z0,z1,z2,z3,z8,z848]),(0,[z0,z1,z2,z849,z8,z5]),(0,[z500,z1,z2,z3,z86,z5]),(0,[z0,z1,z850,z3,z8,z5]),(0,[z243,z1,z2,z3,z8,z17])],[(0,[z0,z1,z2,z174,z8,z17]),(0,[z0,z1,z2,z7,z8,z793]),(0,[z0,z1,z2,z247,z8,z17])],[(0,[z0,z1,z2,z3,z8,z851]),(0,[z1,z2,z21,z8,z5,z364]),(0,[z0,z1,z2,z3,z8,z852]),(0,[z44,z0,z43,z3,z8,z5])],[(0,[z0,z105,z2,z3,z8,z5]),(0,[z0,z1,z3,z8,z853,z5]),(0,[z0,z1,z854,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z855]),(0,[z0,z255,z2,z3,z8,z17]),(0,[z0,z856,z2,z3,z8,z5])],[(0,[z0,z1,z2,z322,z4,z5]),(0,[z0,z1,z2,z857,z8,z5]),(0,[z63,z1,z2,z21,z8,z12]),(0,[z0,z1,z2,z3,z858,z12]),(0,[z64,z315,z1,z2,z3,z8]),(0,[z859,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z860,z8,z5])],[(0,[z0,z105,z2,z3,z8,z121]),(0,[z0,z1,z2,z3,z8,z861])],[(0,[z491,z1,z2,z21,z8,z5]),(0,[z1,z2,z21,z8,z372,z5]),(0,[z1,z2,z529,z862,z3,z8]),(0,[z0,z1,z79,z3,z8,z10]),(0,[z0,z1,z3,z225,z5,z68])],[(0,[z0,z1,z2,z3,z8,z863]),(0,[z0,z1,z2,z356,z8,z246]),(0,[z1,z2,z3,z8,z12,z628]),(0,[z0,z1,z3,z8,z864,z5]),(0,[z0,z1,z149,z3,z8,z5]),(0,[z64,z0,z1,z3,z8,z206])],[(0,[z0,z865,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z866]),(0,[z437,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z867])],[]],
   [[],[(0,[z0,z245,z2,z101,z8,z5]),(0,[z0,z1,z301,z2,z8,z46]),(0,[z0,z1,z2,z281,z8,z17]),(0,[z0,z1,z2,z3,z868,z17])],[(0,[z0,z1,z2,z3,z8,z236]),(0,[z239,z1,z153,z3,z8,z12]),(0,[z42,z1,z2,z7,z8,z323]),(0,[z0,z2,z712,z37,z8,z5])],[(0,[z1,z2,z21,z8,z5,z387]),(0,[z1,z55,z2,z21,z8,z12]),(0,[z113,z1,z2,z3,z643,z5]),(0,[z104,z1,z2,z3,z86,z98]),(0,[z0,z869,z2,z3,z8,z5])],[(0,[z1,z2,z21,z8,z86,z17])],[(0,[z0,z1,z414,z3,z8,z5]),(0,[z0,z1,z2,z870,z8,z5]),(0,[z0,z1,z2,z871,z8,z5]),(0,[z0,z872,z2,z3,z8,z5]),(0,[z0,z1,z423,z2,z8,z233])],[(0,[z0,z1,z2,z7,z170,z5]),(0,[z0,z1,z2,z21,z8,z204]),(1,[z1,z2,z3,z764,z5]),(0,[z0,z1,z2,z188,z8,z17]),(0,[z0,z1,z2,z3,z8,z873]),(0,[z555,z208,z2,z3,z8,z5])],[(0,[z349,z1,z2,z3,z8,z12]),(0,[z1,z2,z874,z3,z8,z5])],[(0,[z16,z157,z2,z3,z8,z17])],[(0,[z0,z1,z875,z3,z8,z5]),(0,[z0,z1,z2,z95,z8,z97])],[(0,[z75,z1,z2,z202,z8,z12]),(0,[z0,z1,z359,z3,z8,z557]),(0,[z0,z1,z62,z3,z8,z512]),(1,[z1,z2,z862,z3,z8])],[(0,[z0,z1,z2,z876,z8,z5]),(0,[z0,z877,z2,z3,z8,z5]),(0,[z0,z1,z2,z21,z8,z387]),(0,[z0,z1,z2,z21,z238,z5]),(0,[z0,z1,z2,z3,z8,z878]),(0,[z0,z1,z2,z3,z8,z879]),(0,[z0,z1,z880,z3,z8,z5]),(0,[z0,z1,z3,z89,z225,z68])],[(0,[z0,z1,z2,z3,z881,z8]),(0,[z0,z1,z2,z882,z8,z5]),(0,[z0,z1,z180,z2,z8,z233])],[(0,[z0,z1,z883,z3,z8,z5]),(0,[z0,z1,z2,z21,z8,z12]),(0,[z0,z1,z729,z7,z8,z5])],[(0,[z91,z30,z169,z3,z8,z5]),(0,[z0,z1,z2,z3,z884,z5]),(0,[z113,z1,z2,z178,z8,z5]),(0,[z0,z1,z2,z8,z192,z5])],[(0,[z0,z30,z2,z3,z424,z5]),(0,[z0,z1,z2,z7,z8,z17]),(0,[z0,z1,z885,z3,z8,z5]),(0,[z0,z1,z2,z234,z7,z8]),(0,[z0,z1,z2,z178,z8,z17]),(0,[z1,z2,z3,z8,z12,z538]),(0,[z0,z1,z360,z188,z8,z5]),(0,[z0,z1,z2,z886,z8,z5])]],
   [[(0,[z0,z1,z2,z3,z8,z887])],[(0,[z16,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z888,z8,z5]),(0,[z0,z1,z2,z3,z8,z889]),(0,[z44,z0,z551,z3,z8,z5])],[(0,[z0,z1,z80,z3,z170,z5]),(0,[z1,z2,z7,z533,z8,z5]),(0,[z0,z1,z2,z442,z8,z538])],[(0,[z1,z2,z21,z49,z8,z12]),(0,[z0,z1,z2,z3,z890,z5]),(0,[z0,z1,z2,z3,z8,z891]),(0,[z0,z255,z149,z3,z8,z5])],[(0,[z0,z1,z2,z21,z8,z376]),(0,[z1,z2,z80,z21,z8,z12]),(0,[z0,z1,z2,z892,z8,z5]),(0,[z0,z1,z2,z7,z222,z5]),(0,[z0,z1,z2,z202,z8,z12]),(0,[z0,z1,z893,z2,z3,z8])],[(0,[z129,z245,z80,z3,z8,z5]),(0,[z0,z1,z2,z21,z894,z5]),(0,[z0,z1,z2,z3,z8,z151]),(0,[z0,z1,z2,z3,z8,z722])],[(0,[z0,z1,z2,z7,z8,z161]),(0,[z0,z1,z433,z2,z3,z118]),(0,[z0,z374,z2,z37,z8,z5]),(0,[z193,z1,z2,z3,z8,z10])],[],[(0,[z0,z1,z360,z7,z8,z5]),(0,[z85,z0,z2,z421,z8,z5])],[(0,[z0,z1,z2,z21,z8,z175]),(0,[z0,z895,z2,z3,z8,z5]),(0,[z1,z2,z21,z515,z8,z12]),(0,[z0,z1,z36,z2,z7,z8]),(0,[z0,z1,z2,z3,z896,z8]),(0,[z0,z1,z2,z146,z8,z17]),(1,[z0,z2,z3,z8,z788])],[(0,[z0,z1,z2,z21,z424,z5]),(0,[z0,z1,z2,z112,z8,z236]),(0,[z0,z1,z2,z3,z897,z5]),(0,[z0,z171,z2,z37,z8,z17]),(0,[z0,z1,z2,z3,z898,z8]),(0,[z0,z899,z2,z3,z8,z5])],[(0,[z1,z503,z2,z3,z8,z12])],[(0,[z0,z1,z2,z23,z58,z17]),(0,[z0,z1,z90,z3,z8,z74])],[(0,[z0,z1,z2,z900,z8,z5]),(0,[z0,z1,z2,z103,z8,z365]),(0,[z0,z1,z2,z3,z8,z323]),(0,[z0,z1,z267,z21,z8,z5]),(0,[z0,z1,z3,z8,z901,z5]),(0,[z0,z1,z2,z3,z902,z5]),(0,[z312,z0,z1,z3,z219,z5]),(0,[z0,z1,z2,z903,z8,z5]),(0,[z0,z1,z2,z3,z607,z68])],[(0,[z104,z1,z2,z3,z86,z17]),(0,[z312,z0,z1,z198,z219,z5])],[(0,[z129,z1,z825,z3,z8,z5]),(0,[z393,z1,z2,z21,z8,z12]),(0,[z0,z59,z158,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z904])]],
   [[(0,[z0,z1,z2,z21,z8,z454]),(0,[z0,z1,z3,z8,z12,z905])],[(0,[z0,z1,z414,z3,z4,z5]),(0,[z1,z2,z21,z8,z303,z5])],[(0,[z339,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z320,z8,z98]),(0,[z0,z1,z2,z906,z8,z12])],[(0,[z0,z279,z2,z3,z130,z5]),(0,[z113,z1,z2,z907,z8,z5])],[(0,[z0,z1,z2,z3,z908,z5]),(0,[z0,z1,z2,z909,z8,z5]),(0,[z0,z1,z2,z910,z8,z5])],[(0,[z0,z1,z2,z3,z8,z817]),(0,[z0,z1,z2,z21,z8,z428]),(0,[z1,z2,z21,z8,z479,z5]),(0,[z0,z1,z911,z3,z8,z5]),(0,[z0,z105,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z912]),(0,[z555,z1,z2,z177,z8,z5]),(0,[z0,z1,z441,z2,z8,z233])],[(0,[z82,z0,z2,z3,z647,z8])],[(0,[z1,z2,z21,z487,z8,z5]),(0,[z0,z1,z3,z8,z50,z5]),(0,[z0,z1,z913,z3,z8,z5]),(0,[z0,z914,z2,z3,z8,z5])],[],[(0,[z16,z1,z2,z112,z8,z12]),(0,[z1,z153,z2,z21,z8,z12]),(0,[z64,z0,z1,z7,z8,z206]),(0,[z0,z1,z149,z7,z8,z5]),(0,[z0,z1,z915,z3,z8,z5]),(0,[z0,z1,z3,z8,z916,z5])],[(0,[z0,z1,z2,z7,z8,z26]),(0,[z0,z1,z2,z3,z321,z17])],[(0,[z0,z1,z2,z917,z8,z5]),(0,[z0,z1,z2,z918,z8,z5]),(0,[z0,z1,z116,z2,z8,z46]),(0,[z0,z1,z2,z919,z8,z5])],[(0,[z218,z30,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z920])],[(0,[z0,z1,z2,z174,z8,z69])],[(0,[z0,z1,z2,z3,z8,z921]),(0,[z0,z1,z2,z7,z8,z236]),(0,[z129,z1,z80,z33,z8,z5]),(0,[z0,z1,z922,z3,z8,z5]),(0,[z44,z0,z752,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z310])]],
   [[(0,[z0,z1,z169,z3,z8,z5]),(0,[z0,z245,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z923]),(0,[z0,z1,z2,z3,z8,z924]),(0,[z570,z1,z2,z3,z8,z17])],[(0,[z0,z1,z433,z2,z3,z358])],[(0,[z1,z2,z21,z8,z132,z12]),(0,[z595,z1,z2,z21,z8,z5])],[(0,[z0,z1,z2,z139,z118,z8]),(0,[z0,z1,z3,z219,z5,z428])],[(0,[z0,z1,z2,z3,z925,z5]),(0,[z0,z1,z2,z812,z3,z8]),(0,[z926,z0,z1,z2,z21,z5]),(0,[z0,z1,z2,z3,z927,z5]),(0,[z0,z1,z116,z2,z139,z8])],[(0,[z0,z1,z2,z3,z8,z928]),(0,[z315,z1,z2,z93,z3,z8])],[(0,[z91,z30,z2,z3,z8,z5]),(0,[z555,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z929,z5]),(0,[z0,z1,z2,z3,z930,z5]),(0,[z85,z0,z2,z190,z8,z5]),(0,[z0,z1,z143,z3,z118,z8])],[(0,[z0,z931,z2,z3,z8,z5]),(0,[z0,z1,z2,z932,z8,z5]),(0,[z218,z1,z2,z21,z8,z12]),(0,[z1,z2,z21,z8,z47,z12]),(0,[z339,z1,z2,z3,z8,z12])],[],[(0,[z1,z2,z3,z287,z8,z12]),(0,[z0,z1,z2,z3,z8,z933]),(0,[z102,z1,z2,z3,z8,z741]),(0,[z0,z1,z934,z3,z8,z5])],[(0,[z0,z1,z2,z322,z8,z264]),(0,[z6,z1,z2,z21,z8,z204]),(0,[z0,z1,z2,z3,z935,z5]),(0,[z0,z1,z3,z8,z936,z5]),(0,[z0,z1,z55,z198,z8,z5])],[(0,[z324,z0,z1,z3,z219,z5]),(1,[z0,z1,z3,z225,z68])],[(0,[z0,z1,z2,z937,z8,z5]),(0,[z0,z1,z820,z2,z21,z5]),(0,[z0,z1,z2,z3,z8,z938]),(0,[z0,z1,z2,z3,z8,z939]),(0,[z0,z1,z2,z940,z3,z8]),(0,[z0,z1,z2,z941,z3,z8])],[(0,[z0,z1,z2,z3,z8,z942]),(0,[z1,z2,z3,z21,z8,z26]),(0,[z616,z1,z2,z21,z8,z5]),(0,[z94,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z320,z8,z17])],[(0,[z102,z1,z2,z777,z8,z5]),(0,[z0,z1,z943,z3,z8,z5])],[(0,[z1,z28,z2,z3,z8,z12]),(0,[z0,z1,z3,z8,z225,z5])]],
   [[(0,[z30,z2,z43,z3,z8,z12]),(0,[z683,z0,z1,z3,z219,z5]),(0,[z1,z2,z21,z8,z579,z12]),(0,[z0,z1,z2,z3,z238,z17]),(0,[z449,z1,z2,z3,z8,z17]),(0,[z0,z1,z55,z8,z411,z5]),(0,[z193,z1,z149,z3,z8,z5])],[(0,[z0,z1,z2,z101,z8,z17]),(0,[z0,z1,z2,z3,z8,z944]),(0,[z6,z1,z2,z21,z8,z12]),(0,[z0,z1,z2,z7,z8,z151]),(0,[z945,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z222,z206])],[(0,[z1,z2,z583,z21,z8,z12]),(0,[z0,z1,z2,z7,z8,z10]),(1,[z0,z1,z2,z3,z769])],[(0,[z0,z2,z3,z8,z946,z5]),(0,[z0,z1,z2,z947,z8,z5]),(0,[z0,z1,z116,z2,z531,z8]),(0,[z0,z1,z2,z3,z8,z948])],[],[(0,[z0,z1,z2,z7,z8,z69]),(0,[z0,z245,z2,z3,z8,z12]),(0,[z1,z2,z21,z148,z86,z5]),(0,[z1,z2,z21,z385,z8,z5]),(0,[z0,z1,z2,z442,z8,z155]),(0,[z0,z1,z2,z3,z8,z949]),(0,[z0,z1,z116,z2,z8,z664]),(0,[z0,z255,z2,z3,z8,z310])],[(0,[z75,z1,z2,z21,z8,z12]),(0,[z1,z593,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z950,z8]),(0,[z0,z1,z2,z3,z14,z68])],[(0,[z0,z1,z2,z3,z8,z951]),(0,[z129,z1,z2,z21,z8,z12]),(0,[z0,z1,z2,z952,z8,z5]),(0,[z0,z1,z2,z777,z8,z5]),(0,[z1,z116,z2,z21,z8,z12]),(0,[z0,z1,z953,z3,z8,z5]),(0,[z0,z1,z954,z2,z3,z8]),(0,[z0,z1,z2,z3,z769,z5])],[(0,[z0,z1,z2,z356,z8,z12]),(0,[z1,z2,z21,z8,z5,z12]),(0,[z1,z2,z481,z21,z86,z5]),(0,[z553,z1,z2,z21,z8,z5]),(0,[z0,z1,z116,z2,z8,z511])],[(0,[z0,z1,z2,z955,z8,z5]),(0,[z587,z0,z2,z3,z31,z5]),(0,[z0,z1,z707,z3,z8,z5]),(0,[z0,z1,z2,z7,z8,z323]),(0,[z0,z207,z158,z3,z8,z5]),(0,[z0,z1,z360,z3,z238,z5]),(0,[z64,z0,z1,z3,z216,z206]),(0,[z57,z0,z208,z2,z47,z5]),(0,[z0,z1,z2,z956,z8,z5])],[(0,[z0,z1,z2,z3,z894,z17]),(0,[z0,z1,z957,z3,z8,z5])],[(0,[z1,z2,z21,z8,z5,z13]),(0,[z0,z1,z360,z3,z8,z12])],[(0,[z0,z1,z169,z3,z4,z5]),(0,[z129,z1,z80,z3,z170,z5]),(0,[z0,z1,z2,z8,z958,z5])],[(0,[z1,z2,z21,z8,z5,z410]),(0,[z0,z1,z2,z3,z8,z959]),(0,[z0,z1,z751,z3,z8,z12]),(0,[z0,z1,z34,z3,z148,z12])],[(0,[z1,z2,z582,z21,z8,z5])],[(0,[z0,z1,z2,z3,z424,z17]),(0,[z1,z2,z7,z21,z8,z12]),(0,[z0,z1,z2,z3,z8,z960]),(0,[z0,z1,z62,z3,z8,z74])]],
   [[(0,[z0,z395,z2,z3,z8,z5]),(0,[z961,z0,z1,z2,z3,z8])],[(0,[z0,z1,z2,z962,z8,z5]),(0,[z0,z245,z2,z3,z8,z175]),(0,[z122,z0,z1,z62,z3,z8])],[(0,[z91,z30,z2,z3,z4,z5]),(0,[z315,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z963,z8,z5]),(0,[z0,z1,z267,z3,z8,z17]),(0,[z113,z1,z2,z562,z54,z5]),(0,[z0,z1,z3,z8,z720,z5])],[(0,[z689,z1,z153,z3,z8,z5]),(0,[z0,z1,z41,z2,z21,z118]),(0,[z0,z1,z2,z93,z8,z466]),(0,[z0,z105,z2,z320,z8,z5]),(0,[z485,z1,z2,z3,z8,z12]),(0,[z555,z1,z2,z23,z8,z5]),(0,[z0,z1,z2,z3,z452,z68])],[(0,[z1,z2,z95,z21,z8,z5]),(0,[z1,z2,z562,z21,z8,z5]),(0,[z64,z0,z1,z3,z8,z114]),(0,[z0,z1,z2,z3,z964,z5]),(0,[z82,z0,z2,z3,z8,z83])],[(0,[z129,z1,z80,z3,z8,z17]),(0,[z0,z1,z2,z21,z8,z98]),(0,[z1,z301,z2,z21,z8,z12]),(0,[z0,z1,z3,z54,z50,z5]),(0,[z0,z208,z2,z3,z8,z17]),(0,[z92,z0,z2,z3,z31,z5])],[(0,[z0,z2,z3,z8,z12,z965]),(0,[z408,z1,z2,z3,z8,z12])],[(0,[z0,z1,z2,z966,z3,z8]),(0,[z0,z967,z2,z21,z8,z5]),(0,[z0,z1,z968,z21,z8,z5]),(0,[z0,z1,z2,z529,z21,z8]),(0,[z1,z2,z3,z8,z12,z226]),(0,[z57,z0,z1,z2,z47,z12]),(0,[z315,z1,z2,z3,z8,z68])],[(0,[z1,z150,z2,z21,z8,z12]),(0,[z1,z2,z21,z444,z8,z12]),(0,[z113,z1,z2,z3,z764,z5]),(0,[z0,z1,z2,z3,z8,z969]),(0,[z57,z193,z1,z2,z47,z5]),(0,[z0,z1,z79,z3,z8,z310])],[(0,[z1,z2,z21,z8,z458,z12]),(0,[z0,z1,z21,z8,z901,z5]),(0,[z0,z61,z2,z3,z8,z497]),(0,[z0,z752,z43,z3,z8,z5])],[(0,[z0,z1,z970,z3,z8,z5]),(0,[z0,z1,z971,z3,z8,z5])],[(0,[z1,z2,z482,z21,z8,z5]),(0,[z0,z1,z2,z7,z8,z310]),(0,[z0,z1,z492,z3,z8,z458]),(0,[z1,z2,z3,z8,z972,z5])],[(0,[z0,z1,z414,z174,z8,z5]),(0,[z0,z1,z2,z973,z8,z5]),(0,[z129,z1,z80,z3,z8,z161]),(0,[z85,z0,z2,z712,z8,z5])],[(0,[z0,z1,z2,z7,z8,z365]),(0,[z0,z1,z394,z2,z8,z119]),(0,[z513,z1,z2,z3,z54,z5]),(0,[z1,z2,z3,z8,z17,z12]),(0,[z553,z1,z2,z3,z8,z12])],[(0,[z0,z1,z2,z3,z8,z974]),(0,[z0,z1,z2,z33,z8,z12])],[(0,[z0,z279,z2,z7,z8,z5]),(0,[z573,z1,z2,z21,z8,z5]),(0,[z409,z0,z2,z190,z8,z5])]],
   [[(0,[z0,z1,z2,z975,z8,z5]),(0,[z625,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z976,z5]),(0,[z0,z1,z977,z2,z8,z5])],[(0,[z0,z1,z414,z3,z8,z264]),(0,[z0,z1,z978,z2,z8,z5]),(0,[z187,z1,z2,z21,z8,z12]),(0,[z0,z1,z301,z2,z8,z511]),(0,[z0,z1,z2,z979,z8,z5]),(0,[z0,z1,z2,z3,z8,z980])],[(0,[z0,z1,z2,z3,z8,z981]),(0,[z1,z2,z3,z8,z17,z410])],[(0,[z0,z1,z2,z982,z8,z5]),(0,[z0,z1,z21,z8,z50,z5]),(0,[z983,z0,z1,z2,z3,z8]),(0,[z0,z1,z116,z2,z529,z8])],[(0,[z555,z1,z2,z21,z8,z5])],[(0,[z82,z0,z1,z2,z3,z222]),(0,[z0,z1,z2,z3,z8,z984]),(0,[z0,z1,z2,z3,z148,z428])],[(0,[z0,z1,z2,z3,z985,z5]),(0,[z0,z1,z2,z986,z8,z5]),(0,[z0,z1,z2,z58,z782,z5]),(0,[z0,z1,z2,z8,z987,z5])],[(0,[z102,z1,z2,z21,z8,z17]),(0,[z44,z0,z43,z7,z8,z5]),(0,[z595,z1,z2,z3,z8,z17]),(0,[z0,z2,z3,z946,z31,z5])],[(0,[z474,z1,z2,z21,z8,z5]),(0,[z0,z105,z2,z178,z8,z5]),(0,[z0,z1,z2,z988,z8,z5])],[(0,[z1,z2,z95,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z989]),(0,[z0,z1,z990,z2,z3,z8]),(0,[z0,z1,z2,z991,z8,z5])],[(0,[z0,z1,z2,z33,z8,z175]),(0,[z0,z1,z2,z3,z8,z992])],[(0,[z0,z395,z2,z3,z86,z5]),(0,[z993,z1,z2,z3,z8,z5]),(0,[z0,z1,z3,z580,z8,z206])],[(0,[z0,z1,z2,z177,z288,z5]),(0,[z0,z1,z2,z994,z3,z8]),(0,[z0,z59,z752,z3,z8,z5]),(0,[z0,z1,z2,z995,z8,z5])],[(0,[z0,z1,z2,z562,z8,z5]),(0,[z57,z1,z2,z21,z8,z12]),(0,[z0,z1,z2,z3,z8,z996]),(0,[z0,z1,z2,z3,z997,z17])],[(0,[z0,z1,z2,z998,z8,z5]),(0,[z0,z1,z2,z21,z728,z5]),(0,[z0,z438,z2,z3,z49,z5])],[(0,[z0,z1,z2,z3,z8,z999]),(0,[z539,z1,z2,z21,z8,z5]),(0,[z0,z208,z149,z3,z8,z5])]],
   [[(0,[z0,z1,z2,z21,z8,z17]),(0,[z0,z1,z1000,z3,z8,z5]),(0,[z330,z1,z2,z7,z8,z5]),(0,[z94,z1,z2,z3,z8,z12])],[(0,[z0,z1,z1001,z3,z8,z5]),(0,[z0,z1,z361,z3,z8,z5])],[(0,[z0,z59,z457,z3,z8,z5]),(0,[z0,z245,z153,z3,z8,z5]),(0,[z193,z1,z2,z3,z8,z310])],[(0,[z1,z2,z547,z7,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1002]),(0,[z0,z1,z414,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z1003]),(0,[z1,z2,z21,z8,z497,z12])],[(0,[z0,z1,z2,z21,z222,z5]),(0,[z0,z1,z2,z3,z444,z13]),(0,[z0,z1,z2,z3,z8,z1004])],[(0,[z1,z2,z907,z21,z8,z5]),(0,[z0,z1,z180,z2,z8,z119])],[(0,[z0,z1,z2,z21,z8,z161]),(0,[z510,z0,z1,z2,z579,z5]),(0,[z409,z0,z2,z181,z8,z5]),(0,[z0,z1,z2,z1005,z8,z5]),(0,[z104,z105,z2,z3,z86,z5]),(0,[z0,z1,z2,z1006,z8,z5]),(0,[z0,z1,z2,z202,z8,z17])],[],[(0,[z0,z1,z360,z21,z8,z5]),(0,[z0,z1,z2,z1007,z8,z5])],[(0,[z0,z1,z267,z3,z8,z98]),(0,[z122,z0,z1,z2,z3,z1008])],[(0,[z0,z1,z2,z101,z170,z5]),(0,[z0,z1,z34,z21,z148,z5]),(0,[z0,z1,z21,z8,z225,z5]),(0,[z75,z1,z2,z3,z8,z741]),(0,[z0,z1,z62,z3,z222,z5]),(0,[z0,z1,z602,z2,z3,z118]),(0,[z0,z1,z2,z1009,z8,z5])],[(0,[z0,z1,z2,z1010,z8,z5]),(0,[z0,z1,z2,z3,z170,z12]),(0,[z0,z395,z505,z3,z8,z5]),(0,[z604,z1,z2,z3,z8,z12]),(0,[z0,z2,z3,z8,z788,z83])],[(0,[z0,z1,z2,z1011,z8,z5]),(0,[z0,z1,z2,z3,z8,z1012]),(0,[z474,z1,z2,z3,z8,z12]),(0,[z0,z584,z2,z3,z8,z132]),(0,[z0,z1,z2,z1013,z8,z5]),(0,[z0,z1,z55,z56,z8,z5])],[(0,[z0,z1,z2,z3,z1014,z5]),(0,[z1,z2,z115,z21,z8,z5])],[(0,[z0,z1,z2,z3,z8,z713]),(0,[z0,z1,z2,z3,z8,z1015]),(0,[z507,z1,z2,z21,z8,z5]),(1,[z0,z2,z712,z8,z5])]],
   [[(0,[z16,z1,z2,z7,z8,z12]),(0,[z42,z1,z2,z7,z8,z5]),(0,[z113,z1,z2,z3,z54,z5]),(0,[z0,z1,z2,z398,z8,z97])],[(0,[z0,z1,z2,z3,z8,z1016]),(0,[z0,z1,z2,z3,z1017,z5]),(0,[z0,z1,z2,z1018,z8,z5]),(0,[z0,z1,z2,z3,z8,z1019])],[(0,[z502,z0,z1,z3,z8,z206])],[(0,[z30,z2,z3,z8,z31,z12]),(0,[z1,z423,z2,z7,z8,z5]),(0,[z0,z1,z2,z3,z8,z1020])],[(0,[z0,z1,z505,z3,z8,z5]),(0,[z0,z1,z1021,z3,z8,z5]),(0,[z1022,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z424,z69]),(0,[z1023,z0,z1,z2,z21,z5]),(0,[z0,z1,z2,z3,z8,z741]),(0,[z0,z1,z1024,z3,z8,z5]),(0,[z0,z1,z2,z1025,z8,z5])],[(0,[z0,z1,z2,z3,z1026,z5]),(0,[z0,z1,z2,z1027,z8,z5]),(0,[z0,z1,z505,z3,z8,z121]),(0,[z315,z1,z2,z139,z8,z5]),(0,[z0,z1,z755,z3,z8,z5]),(0,[z312,z0,z1,z192,z219,z5])],[(0,[z0,z1,z169,z174,z8,z5]),(0,[z0,z266,z158,z3,z8,z5]),(0,[z0,z1,z1028,z3,z8,z5]),(0,[z82,z0,z495,z2,z3,z8]),(0,[z0,z1,z3,z8,z225,z68])],[(0,[z0,z1,z2,z3,z170,z175]),(0,[z0,z1,z2,z21,z14,z8]),(0,[z1,z2,z21,z58,z8,z12]),(0,[z0,z1,z2,z562,z8,z214]),(0,[z82,z0,z2,z139,z8,z83]),(0,[z0,z208,z2,z3,z8,z10]),(0,[z57,z0,z1,z149,z47,z5]),(0,[z1029,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z1030,z5]),(0,[z0,z1,z2,z1031,z8,z5]),(1,[z1,z2,z247,z8,z12]),(0,[z0,z1,z3,z8,z829,z12]),(0,[z315,z1,z143,z3,z8,z5])],[(0,[z113,z1,z2,z21,z86,z5]),(0,[z0,z1,z2,z3,z222,z12]),(0,[z0,z1,z1032,z3,z8,z5]),(0,[z0,z61,z548,z2,z3,z8])],[(0,[z0,z1,z2,z3,z130,z5]),(0,[z0,z1,z2,z101,z8,z161]),(0,[z0,z1,z2,z21,z8,z26]),(0,[z1,z253,z2,z21,z8,z12]),(0,[z0,z1,z2,z3,z8,z1033]),(0,[z0,z1,z2,z1034,z8,z5]),(0,[z82,z0,z143,z3,z8,z83])],[(0,[z0,z1,z169,z3,z8,z264]),(1,[z1,z2,z714,z8,z5]),(0,[z92,z1,z2,z21,z8,z12]),(0,[z312,z0,z1,z7,z219,z5]),(0,[z228,z1,z2,z3,z54,z5])],[(0,[z0,z1,z2,z322,z424,z5]),(0,[z91,z30,z2,z174,z8,z5])],[(0,[z0,z1,z2,z3,z1035,z5]),(0,[z16,z251,z2,z3,z8,z5]),(0,[z0,z59,z158,z7,z8,z5]),(0,[z0,z1,z2,z3,z87,z273]),(0,[z0,z1,z2,z3,z1036,z8]),(0,[z0,z1,z2,z3,z118,z769])],[(0,[z0,z1,z2,z1037,z8,z5]),(0,[z0,z1,z2,z3,z8,z1038]),(0,[z926,z0,z1,z2,z3,z5]),(0,[z513,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z1039,z5]),(0,[z1040,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z769,z68])]],
   [[(0,[z0,z1,z21,z8,z819,z5]),(0,[z0,z1041,z2,z3,z8,z5]),(0,[z449,z1,z2,z248,z8,z5]),(0,[z1042,z1,z2,z3,z8,z5]),(0,[z0,z1,z55,z79,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1043]),(0,[z0,z279,z2,z101,z8,z5]),(0,[z0,z1,z2,z1044,z8,z5]),(0,[z0,z1,z2,z3,z8,z1045]),(0,[z0,z1,z2,z3,z8,z1046]),(0,[z0,z1,z2,z3,z8,z1047])],[(0,[z91,z30,z2,z3,z8,z264]),(0,[z1,z2,z3,z8,z111,z12])],[],[(0,[z0,z1,z2,z1048,z8,z5]),(0,[z0,z1,z2,z3,z8,z1049])],[(0,[z0,z1,z3,z8,z5,z905]),(0,[z0,z1,z2,z8,z1050,z5]),(0,[z0,z395,z2,z3,z8,z121]),(0,[z44,z122,z0,z43,z3,z8])],[(0,[z0,z1,z2,z1051,z8,z5])],[(0,[z0,z1,z3,z8,z819,z5]),(0,[z0,z1,z820,z2,z3,z5]),(0,[z1052,z1,z2,z3,z8,z5])],[(0,[z544,z1,z2,z21,z8,z5]),(0,[z0,z1,z1053,z3,z8,z5]),(0,[z0,z1,z850,z3,z8,z12]),(0,[z0,z1,z2,z3,z709,z17])],[(0,[z1,z2,z21,z8,z17,z12]),(0,[z555,z1,z2,z3,z8,z17]),(0,[z315,z1,z2,z3,z321,z5]),(0,[z243,z1,z2,z947,z8,z5]),(0,[z0,z1,z2,z93,z8,z987])],[(0,[z0,z1,z2,z1054,z8,z5]),(0,[z1,z2,z21,z586,z8,z5]),(0,[z0,z1,z2,z23,z288,z5]),(0,[z0,z1,z3,z8,z74,z722])],[(0,[z0,z1,z2,z3,z8,z5]),(0,[z0,z157,z2,z3,z424,z5]),(0,[z537,z1,z2,z21,z8,z5]),(0,[z0,z105,z2,z3,z8,z12]),(0,[z113,z1,z2,z3,z54,z214]),(0,[z82,z0,z2,z3,z321,z83])],[(0,[z0,z1,z2,z3,z8,z1055])],[(0,[z0,z1,z2,z3,z1056,z5]),(0,[z0,z1,z2,z21,z8,z800]),(0,[z0,z1,z145,z56,z8,z5]),(0,[z0,z1,z2,z3,z8,z121])],[(0,[z201,z1,z2,z7,z8,z5])],[(0,[z0,z1,z169,z7,z8,z5]),(0,[z0,z245,z2,z3,z170,z5]),(0,[z0,z1057,z2,z3,z8,z5]),(0,[z0,z1,z149,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z1058])]],
   [[(0,[z0,z1,z2,z1059,z3,z8]),(0,[z122,z0,z1,z143,z3,z8])],[(0,[z0,z254,z43,z3,z8,z5]),(0,[z1060,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z501,z68]),(0,[z0,z208,z2,z3,z8,z310])],[(0,[z1,z2,z3,z348,z8,z12]),(0,[z122,z0,z1,z2,z21,z8]),(0,[z0,z1,z2,z3,z8,z1061])],[(0,[z0,z1,z2,z21,z8,z10]),(0,[z315,z1,z2,z1062,z8,z5])],[(0,[z6,z1,z2,z21,z8,z17])],[(0,[z0,z1,z1063,z3,z8,z5]),(0,[z91,z30,z2,z7,z8,z5]),(0,[z129,z279,z80,z3,z8,z5]),(0,[z0,z2,z190,z712,z8,z5])],[(0,[z0,z1,z2,z21,z8,z69]),(0,[z102,z1,z2,z247,z8,z5]),(0,[z1064,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z3,z8,z734]),(0,[z0,z1,z3,z50,z5,z68])],[(0,[z0,z1,z3,z8,z1065,z5])],[(0,[z0,z245,z2,z3,z8,z17]),(0,[z0,z1,z2,z3,z8,z1066])],[(0,[z0,z1,z2,z3,z8,z1067]),(0,[z0,z1,z153,z3,z170,z5]),(0,[z312,z1,z2,z21,z8,z12]),(0,[z0,z1,z2,z1062,z8,z5]),(0,[z99,z1,z2,z7,z8,z5]),(0,[z0,z1068,z1,z2,z3,z8])],[(0,[z16,z1,z2,z3,z8,z69]),(0,[z0,z1,z2,z21,z170,z5]),(0,[z0,z1,z2,z534,z8,z466]),(0,[z0,z1069,z2,z3,z8,z5])],[(0,[z0,z1,z2,z1070,z8,z5]),(0,[z0,z105,z267,z3,z8,z5])],[(0,[z0,z1,z55,z305,z8,z5])],[(0,[z0,z1,z2,z3,z1071,z5])],[(0,[z243,z1,z2,z3,z8,z5]),(0,[z1072,z1,z2,z3,z8,z5]),(0,[z0,z1,z41,z2,z3,z118])],[(0,[z0,z1,z2,z174,z8,z5]),(0,[z1073,z0,z1,z2,z3,z8]),(0,[z0,z245,z2,z3,z8,z161]),(0,[z0,z1,z2,z3,z946,z5])]],
   [[(0,[z193,z1,z2,z562,z8,z5]),(0,[z0,z1,z34,z3,z148,z17]),(0,[z0,z1,z2,z1074,z8,z5])],[(0,[z510,z0,z1,z2,z47,z5]),(0,[z42,z1,z2,z3,z8,z387]),(0,[z1,z666,z2,z7,z8,z5]),(0,[z0,z255,z2,z3,z8,z5])],[(0,[z113,z1,z2,z21,z8,z5]),(0,[z1,z2,z7,z21,z8,z17]),(0,[z0,z1,z2,z529,z3,z8]),(0,[z0,z1,z2,z3,z8,z1075])],[(0,[z0,z1,z2,z112,z8,z5]),(0,[z104,z1,z2,z21,z8,z12]),(0,[z0,z1,z2,z3,z1076,z5]),(0,[z315,z1,z2,z3,z8,z132]),(0,[z555,z1,z149,z3,z8,z5]),(0,[z0,z1,z41,z2,z3,z769])],[(0,[z0,z1,z414,z3,z424,z5]),(0,[z0,z1,z1077,z3,z8,z5]),(0,[z0,z1,z2,z3,z1078,z5]),(0,[z0,z1,z2,z1079,z3,z8]),(0,[z57,z555,z1,z2,z47,z5])],[(0,[z1,z415,z2,z3,z8,z12]),(0,[z362,z1,z2,z3,z8,z12]),(0,[z82,z0,z2,z3,z8,z788]),(0,[z0,z1,z2,z8,z1080,z5]),(0,[z1081,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z214]),(0,[z0,z1,z3,z86,z50,z5]),(0,[z0,z1,z1082,z3,z8,z5]),(0,[z0,z1,z56,z755,z8,z5]),(0,[z0,z1,z2,z93,z8,z364])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z1083,z3,z8,z5]),(0,[z0,z187,z2,z348,z8,z5]),(0,[z1,z2,z3,z8,z307,z12]),(0,[z1,z426,z2,z3,z8,z12]),(0,[z0,z1,z2,z1084,z8,z5]),(0,[z0,z1,z2,z1085,z8,z5])],[(0,[z1,z2,z287,z8,z5,z12]),(0,[z0,z1,z2,z3,z8,z1086]),(0,[z0,z1,z2,z3,z8,z1087]),(0,[z0,z1,z2,z3,z8,z1088]),(0,[z315,z1,z2,z188,z8,z5]),(0,[z0,z1,z2,z1089,z8,z5])],[(0,[z0,z1,z2,z3,z868,z5]),(0,[z0,z1,z2,z1090,z3,z8]),(0,[z102,z1,z2,z3,z8,z307]),(0,[z1091,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z1092,z5]),(0,[z1,z2,z1093,z3,z8,z5])],[(0,[z57,z0,z1,z2,z47,z17]),(0,[z82,z0,z2,z188,z8,z83]),(0,[z0,z1,z2,z1094,z8,z5])],[(0,[z1,z2,z21,z8,z5,z651]),(0,[z0,z1,z2,z482,z8,z466]),(0,[z0,z1,z2,z3,z1095,z5]),(0,[z1,z2,z862,z3,z8,z5])],[(0,[z0,z1,z2,z1096,z3,z8]),(0,[z0,z1097,z2,z3,z8,z5]),(0,[z0,z1041,z2,z7,z8,z5]),(0,[z0,z282,z2,z3,z31,z5])],[(0,[z0,z1,z41,z2,z3,z14])],[(0,[z1,z30,z2,z3,z8,z12]),(0,[z0,z1,z2,z21,z8,z365]),(0,[z228,z1,z2,z21,z8,z5]),(0,[z0,z841,z2,z21,z8,z5]),(0,[z0,z1,z62,z7,z8,z74]),(0,[z0,z1,z2,z3,z8,z1098])],[(0,[z6,z1,z2,z21,z8,z26]),(0,[z0,z395,z2,z7,z8,z5]),(0,[z0,z395,z2,z178,z8,z5]),(0,[z0,z1,z2,z3,z8,z1099])]],
   [[(0,[z0,z279,z2,z21,z8,z5]),(0,[z393,z0,z2,z583,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1100]),(0,[z315,z1,z2,z7,z8,z5]),(0,[z0,z59,z158,z3,z8,z12])],[(0,[z290,z0,z43,z3,z8,z5]),(0,[z0,z1,z2,z1101,z3,z8])],[(0,[z0,z1,z2,z322,z8,z12]),(0,[z82,z0,z2,z7,z8,z83]),(0,[z0,z1,z2,z3,z8,z1102])],[(0,[z0,z245,z2,z33,z8,z5]),(0,[z0,z1,z2,z3,z8,z1103]),(0,[z92,z0,z2,z7,z31,z5]),(0,[z315,z1,z2,z1104,z8,z5]),(0,[z0,z1,z79,z3,z8,z5])],[(0,[z0,z1,z1105,z2,z3,z8]),(0,[z0,z1,z2,z1106,z8,z5])],[(0,[z1,z2,z21,z8,z5,z26]),(0,[z0,z1,z2,z3,z222,z74]),(0,[z0,z1,z2,z3,z782,z5]),(0,[z0,z1,z116,z2,z8,z233])],[(0,[z0,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z178,z8,z5]),(0,[z0,z171,z2,z529,z37,z8])],[(0,[z1,z2,z21,z486,z8,z5]),(0,[z44,z0,z43,z21,z8,z5]),(0,[z315,z1,z2,z3,z8,z83]),(0,[z0,z1,z2,z1107,z8,z5])],[(0,[z0,z105,z2,z21,z8,z5]),(0,[z369,z1,z2,z21,z8,z5]),(0,[z82,z243,z2,z3,z8,z83])],[(0,[z0,z1,z1108,z3,z8,z5]),(0,[z0,z1,z2,z287,z8,z12]),(0,[z0,z1,z2,z103,z8,z5]),(0,[z0,z1,z2,z1104,z8,z5]),(0,[z0,z1,z11,z22,z8,z5]),(0,[z0,z1,z2,z8,z233,z987])],[(0,[z0,z1,z2,z174,z4,z5]),(0,[z0,z2,z3,z8,z5,z965]),(0,[z1,z2,z305,z21,z8,z12]),(0,[z0,z1,z760,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1109]),(0,[z0,z1,z11,z755,z8,z5]),(0,[z0,z1,z11,z79,z8,z5]),(0,[z0,z1,z2,z3,z1110,z5])],[(0,[z1,z2,z95,z3,z8,z17]),(0,[z555,z1,z2,z3,z8,z10])],[(0,[z113,z1,z2,z21,z8,z214]),(0,[z64,z0,z1,z21,z8,z206]),(0,[z0,z1,z149,z21,z8,z5]),(0,[z0,z1,z2,z3,z1111,z17]),(0,[z0,z1,z116,z2,z8,z479])],[(0,[z104,z395,z2,z3,z86,z5]),(0,[z61,z1,z2,z95,z3,z8]),(0,[z0,z1,z88,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1112]),(0,[z0,z1,z2,z139,z8,z5])]],
   [[(0,[z346,z0,z1,z3,z219,z5]),(0,[z1,z2,z3,z8,z17,z651]),(0,[z0,z1,z2,z8,z1113,z5]),(1,[z0,z1,z3,z8,z722]),(0,[z0,z1,z2,z3,z8,z1114]),(0,[z0,z1,z2,z3,z8,z987])],[(0,[z0,z1,z2,z287,z8,z376]),(0,[z0,z1,z2,z3,z8,z1115]),(0,[z0,z1,z2,z93,z8,z97])],[(0,[z412,z30,z2,z3,z8,z12]),(0,[z0,z1,z2,z21,z8,z236]),(0,[z660,z1,z2,z21,z8,z5]),(0,[z0,z1116,z2,z3,z8,z5]),(0,[z0,z1,z143,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1117]),(0,[z0,z1,z41,z3,z50,z5])],[(0,[z0,z1,z2,z1118,z8,z5]),(0,[z82,z315,z2,z3,z8,z83]),(0,[z0,z1,z55,z755,z8,z5]),(0,[z0,z1,z2,z8,z987,z97])],[(0,[z0,z1,z2,z139,z8,z68]),(0,[z0,z1,z2,z23,z58,z5])],[(0,[z0,z1,z414,z21,z8,z5]),(0,[z0,z279,z2,z3,z8,z12]),(0,[z1119,z0,z2,z3,z8,z5]),(0,[z0,z1,z2,z248,z8,z12]),(0,[z0,z1,z2,z3,z770,z5]),(0,[z0,z1,z62,z3,z8,z447]),(0,[z0,z1,z3,z148,z1110,z5])],[(0,[z16,z30,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z1120,z5]),(0,[z0,z1,z2,z1121,z8,z5]),(0,[z0,z1,z2,z3,z1008,z5]),(0,[z0,z1,z2,z3,z8,z1122])],[(0,[z774,z0,z1,z3,z8,z5]),(0,[z650,z1,z2,z7,z8,z5]),(0,[z0,z1,z143,z3,z8,z68])],[(0,[z85,z0,z2,z190,z8,z12]),(0,[z0,z1,z2,z1123,z8,z5])],[(0,[z1,z2,z862,z3,z37,z8]),(0,[z0,z1,z2,z3,z8,z1124])],[(0,[z0,z255,z79,z3,z8,z5])],[(0,[z0,z1,z752,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1125])],[(0,[z0,z1,z2,z907,z8,z5]),(0,[z455,z1,z2,z21,z8,z5]),(0,[z0,z1,z755,z22,z8,z5]),(0,[z1,z2,z3,z1126,z8,z5]),(0,[z0,z1,z2,z1127,z8,z5]),(0,[z0,z1,z1128,z3,z8,z5])],[(0,[z412,z1,z2,z21,z8,z12]),(0,[z44,z0,z43,z3,z8,z12]),(0,[z0,z1,z2,z1129,z8,z5])],[(0,[z193,z1,z2,z3,z8,z5]),(0,[z1,z2,z21,z348,z8,z12]),(0,[z0,z1,z505,z320,z8,z5]),(0,[z0,z1,z1130,z2,z3,z8])],[(0,[z0,z1,z169,z3,z424,z5]),(0,[z0,z1,z2,z3,z170,z17]),(0,[z0,z1,z2,z3,z8,z1131]),(0,[z0,z1,z885,z21,z8,z5]),(0,[z0,z1,z301,z2,z8,z233])]],
   [[(0,[z1023,z0,z1,z2,z3,z5]),(0,[z1,z11,z2,z21,z8,z12]),(0,[z0,z1,z361,z7,z8,z5]),(0,[z0,z1,z1132,z3,z8,z5]),(0,[z92,z0,z2,z3,z946,z5]),(0,[z0,z1,z198,z2,z8,z5]),(0,[z0,z1,z1133,z2,z8,z5])],[(0,[z16,z1,z2,z21,z8,z12]),(0,[z0,z279,z2,z3,z8,z175]),(0,[z113,z1,z2,z281,z54,z5]),(0,[z0,z1,z2,z3,z89,z68])],[(0,[z510,z1,z2,z21,z86,z5]),(0,[z0,z1,z2,z7,z8,z214]),(0,[z0,z1,z830,z3,z8,z5]),(0,[z0,z1,z2,z3,z321,z5]),(0,[z243,z1,z2,z139,z8,z5]),(0,[z1134,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z7,z4,z5]),(0,[z500,z30,z2,z3,z8,z5]),(0,[z0,z105,z2,z3,z8,z98]),(0,[z0,z1,z62,z523,z3,z8]),(0,[z555,z1,z2,z8,z47,z5])],[],[(0,[z91,z30,z2,z3,z424,z5]),(0,[z0,z1,z2,z21,z8,z151]),(0,[z1,z2,z178,z8,z86,z5]),(0,[z0,z1,z1135,z3,z8,z5]),(0,[z243,z1,z143,z3,z8,z5]),(0,[z688,z0,z1,z3,z219,z5]),(0,[z0,z1136,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z170,z161]),(0,[z330,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z1137,z8,z5])],[(0,[z0,z1,z1138,z2,z8,z5]),(0,[z0,z1,z3,z8,z1139,z5]),(0,[z0,z1,z2,z3,z321,z68]),(0,[z0,z1,z2,z3,z216,z5])],[(0,[z0,z1,z2,z3,z8,z1140])],[(0,[z1,z2,z547,z3,z8,z12])],[(0,[z0,z1,z414,z3,z8,z12]),(0,[z1,z30,z2,z7,z8,z12]),(0,[z42,z1,z2,z7,z8,z307]),(0,[z0,z1,z41,z3,z225,z5])],[(0,[z0,z1,z2,z1141,z8,z5]),(0,[z0,z1,z2,z3,z8,z1142]),(0,[z0,z1,z62,z3,z8,z722]),(0,[z0,z1,z2,z1143,z8,z5])],[(0,[z102,z1,z2,z248,z8,z17]),(0,[z243,z1,z2,z1051,z8,z5])],[(0,[z0,z1,z2,z21,z8,z323]),(0,[z0,z395,z2,z320,z8,z5]),(0,[z0,z1,z2,z3,z222,z17]),(0,[z57,z0,z1,z2,z47,z10])],[(0,[z0,z1,z2,z356,z8,z17]),(0,[z0,z395,z2,z3,z54,z5]),(0,[z0,z1,z2,z3,z1144,z5]),(0,[z1,z2,z1145,z3,z8,z5])],[(0,[z0,z59,z158,z21,z8,z5])]],
   [[(0,[z0,z1,z1146,z3,z8,z5]),(0,[z1,z2,z3,z8,z713,z12]),(0,[z0,z1,z79,z7,z8,z5])],[(0,[z0,z1,z360,z3,z8,z17]),(0,[z1147,z1,z2,z3,z8,z5])],[(0,[z1148,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z3,z8,z246]),(0,[z0,z1,z2,z247,z8,z5]),(0,[z315,z1,z2,z3,z238,z5]),(0,[z0,z61,z2,z3,z8,z132]),(0,[z0,z1,z2,z755,z8,z5])],[(0,[z0,z1149,z2,z3,z8,z5]),(0,[z1,z825,z80,z3,z8,z5]),(0,[z1,z2,z21,z8,z5,z155]),(0,[z1,z2,z248,z21,z8,z5]),(0,[z0,z1,z505,z7,z8,z5]),(0,[z0,z1,z505,z178,z8,z5]),(0,[z0,z1,z2,z8,z192,z12]),(0,[z0,z1,z198,z22,z8,z5])],[(0,[z0,z790,z2,z3,z8,z5]),(0,[z315,z1,z2,z3,z8,z12]),(0,[z82,z0,z2,z3,z238,z83]),(0,[z0,z1,z198,z79,z8,z5]),(0,[z0,z1,z2,z1150,z8,z5]),(0,[z193,z255,z2,z3,z8,z5])],[(0,[z0,z30,z169,z3,z8,z5]),(0,[z0,z1,z2,z320,z8,z5]),(0,[z1151,z1,z2,z3,z8,z5])],[(0,[z42,z1,z2,z3,z8,z12]),(0,[z1,z2,z21,z8,z357,z5])],[(0,[z0,z1,z2,z3,z8,z264]),(0,[z507,z1,z2,z3,z8,z17])],[(0,[z102,z1,z2,z3,z8,z376]),(0,[z449,z1,z2,z3,z8,z5]),(0,[z1,z2,z23,z21,z8,z12]),(0,[z0,z1,z2,z3,z8,z387]),(0,[z0,z1,z2,z3,z238,z5]),(0,[z0,z1,z2,z1152,z8,z5])],[(0,[z638,z0,z1,z3,z219,z5]),(0,[z1,z423,z2,z3,z8,z12])],[(0,[z0,z1,z2,z1153,z8,z5]),(0,[z0,z1,z2,z7,z130,z5]),(0,[z0,z1,z7,z8,z50,z5]),(0,[z0,z1,z88,z7,z8,z5]),(0,[z412,z0,z2,z3,z8,z425])],[(0,[z0,z1,z2,z33,z170,z5]),(0,[z0,z1154,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z219,z428])],[(0,[z0,z1,z796,z3,z8,z5]),(0,[z0,z1,z2,z1155,z8,z5]),(0,[z0,z1,z2,z281,z8,z5]),(0,[z0,z1,z2,z3,z89,z273]),(1,[z0,z1,z3,z222,z206])],[(0,[z1,z2,z482,z21,z8,z12]),(0,[z82,z0,z2,z3,z8,z226]),(0,[z122,z0,z1,z2,z3,z8])],[(0,[z0,z1,z2,z1156,z8,z5]),(0,[z0,z1,z922,z21,z8,z5]),(0,[z0,z1,z143,z7,z8,z5]),(0,[z0,z105,z2,z3,z8,z17]),(1,[z1,z2,z95,z8,z97])],[(0,[z0,z1,z2,z3,z8,z1157]),(0,[z1,z2,z21,z8,z86,z5]),(0,[z0,z1,z2,z21,z8,z310]),(0,[z0,z1158,z2,z3,z8,z5])]],
   [[(0,[z0,z1,z169,z21,z8,z5]),(1,[z1,z2,z21,z8,z387]),(0,[z0,z1,z2,z3,z1159,z5])],[(0,[z0,z1,z2,z1160,z8,z5]),(0,[z0,z1,z2,z188,z8,z5]),(0,[z0,z1,z1161,z3,z8,z5])],[(0,[z383,z0,z2,z3,z31,z5]),(0,[z0,z1162,z2,z3,z8,z5]),(1,[z1,z2,z21,z8,z12]),(0,[z0,z1,z2,z3,z894,z5]),(0,[z104,z1,z505,z3,z86,z5]),(0,[z312,z0,z1,z3,z219,z12]),(0,[z0,z1,z149,z3,z8,z17]),(0,[z0,z1,z2,z1163,z3,z8]),(0,[z0,z1,z2,z1164,z8,z5]),(0,[z1,z2,z1165,z3,z8,z5])],[(0,[z626,z1,z80,z3,z8,z5])],[(0,[z0,z1,z2,z33,z8,z17]),(0,[z0,z1,z2,z21,z925,z5]),(0,[z82,z1,z2,z95,z3,z8])],[(0,[z0,z1,z2,z3,z8,z307]),(0,[z0,z1,z2,z3,z1166,z5]),(0,[z0,z1,z2,z529,z8,z97]),(0,[z0,z1,z3,z8,z222,z206])],[(0,[z91,z30,z2,z21,z8,z5]),(0,[z0,z59,z3,z8,z366,z5]),(0,[z0,z1,z143,z139,z8,z5])],[(0,[z0,z1,z2,z3,z424,z5]),(0,[z660,z1,z2,z3,z8,z17]),(0,[z64,z0,z1,z3,z222,z206]),(0,[z193,z1,z79,z3,z8,z5])],[(0,[z0,z1,z1167,z3,z8,z5]),(0,[z0,z1168,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1169])],[(0,[z59,z30,z2,z3,z8,z12]),(0,[z193,z1,z2,z7,z8,z5])],[(0,[z0,z1,z2,z174,z8,z264]),(0,[z0,z1,z2,z33,z8,z161]),(0,[z0,z1,z2,z3,z1170,z8]),(0,[z1171,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z1172,z5]),(0,[z0,z1,z2,z7,z8,z121]),(0,[z0,z1,z2,z178,z8,z121]),(0,[z0,z1,z3,z8,z50,z12])],[(0,[z129,z1,z80,z3,z8,z5]),(0,[z0,z1,z2,z7,z89,z68]),(0,[z0,z1,z2,z562,z8,z387]),(0,[z0,z208,z2,z3,z8,z5])],[(0,[z0,z1,z2,z1173,z8,z5]),(0,[z1,z2,z21,z8,z12,z425]),(0,[z336,z1,z2,z21,z8,z12]),(0,[z0,z1,z2,z3,z8,z1174]),(0,[z0,z1,z34,z3,z1110,z5])],[(0,[z554,z0,z43,z3,z8,z5]),(0,[z625,z157,z2,z3,z8,z5]),(0,[z1,z2,z21,z148,z8,z12]),(0,[z0,z1,z2,z562,z8,z12])]],
   [[(0,[z0,z1,z2,z3,z8,z1175]),(0,[z0,z1,z2,z3,z8,z1176]),(0,[z0,z1,z2,z1177,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1178]),(0,[z0,z1,z2,z3,z764,z5]),(0,[z455,z1,z2,z3,z8,z17])],[(0,[z0,z1,z2,z3,z8,z1179]),(0,[z1,z2,z481,z21,z8,z12]),(0,[z1,z2,z534,z3,z8,z12]),(0,[z0,z1,z7,z8,z225,z5]),(0,[z315,z1,z116,z2,z3,z8]),(0,[z1,z2,z93,z95,z8,z97])],[(0,[z0,z1,z2,z3,z4,z264]),(0,[z0,z1,z2,z1180,z8,z5]),(0,[z0,z1,z2,z7,z216,z5]),(0,[z0,z1,z1181,z3,z8,z5])],[(0,[z0,z1,z2,z146,z8,z5]),(0,[z201,z1,z2,z3,z8,z12]),(0,[z243,z1,z2,z188,z8,z5]),(0,[z0,z1,z2,z3,z8,z1182]),(0,[z0,z1,z88,z3,z89,z68])],[(0,[z0,z1,z169,z3,z8,z12]),(0,[z59,z1,z2,z21,z8,z12]),(0,[z0,z171,z2,z37,z8,z5]),(0,[z0,z1,z2,z862,z3,z8]),(0,[z0,z1,z2,z3,z8,z1183])],[(0,[z1,z2,z93,z21,z8,z12]),(0,[z1,z84,z2,z7,z8,z5]),(0,[z0,z1,z2,z139,z321,z5])],[(0,[z0,z1,z2,z281,z8,z214]),(0,[z0,z1,z2,z3,z1184,z8])],[(0,[z0,z61,z1,z2,z3,z222])],[(0,[z1,z2,z21,z86,z219,z5]),(0,[z0,z200,z2,z585,z8,z5]),(0,[z0,z1,z41,z2,z7,z118]),(0,[z104,z1,z2,z3,z86,z5]),(0,[z0,z1,z2,z3,z927,z12]),(0,[z0,z1,z2,z1185,z8,z5]),(0,[z0,z1,z143,z3,z321,z5])],[(0,[z0,z1,z2,z3,z8,z1186]),(0,[z1,z550,z2,z21,z8,z5]),(0,[z312,z0,z1,z3,z219,z428])],[(0,[z91,z30,z2,z3,z8,z12]),(0,[z637,z1,z2,z3,z8,z12]),(0,[z104,z1,z2,z3,z86,z121]),(0,[z1,z2,z247,z8,z5,z12]),(0,[z0,z1,z806,z3,z8,z17])],[(0,[z645,z1,z2,z21,z8,z5]),(0,[z1187,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z1188,z3,z8]),(0,[z0,z1,z34,z3,z117,z5]),(0,[z193,z1,z2,z3,z8,z1124])],[(0,[z243,z1,z2,z7,z8,z5]),(0,[z0,z1,z2,z529,z7,z8]),(0,[z0,z1,z2,z3,z8,z1189]),(0,[z1190,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1191]),(0,[z0,z61,z2,z7,z8,z132]),(0,[z1192,z1,z2,z3,z8,z5]),(0,[z64,z0,z1,z3,z8,z722])],[(0,[z0,z1,z2,z1193,z8,z5]),(0,[z0,z1,z1194,z3,z8,z5]),(0,[z102,z1,z2,z21,z8,z5]),(0,[z0,z1,z62,z21,z8,z74]),(0,[z99,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z1195]),(0,[z1196,z1,z2,z3,z8,z5]),(0,[z0,z1,z3,z8,z50,z454])]],
   [[(0,[z0,z395,z2,z21,z8,z5]),(0,[z1,z2,z21,z8,z12,z20]),(0,[z1,z2,z21,z8,z12,z466]),(0,[z0,z255,z2,z7,z8,z5]),(0,[z0,z1197,z2,z3,z8,z5]),(0,[z113,z1,z2,z3,z54,z387]),(0,[z0,z1,z3,z14,z8,z50])],[(0,[z0,z1,z2,z103,z8,z246]),(0,[z0,z1,z2,z3,z8,z1198]),(0,[z1199,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1200]),(0,[z0,z1,z2,z3,z8,z1201])],[(0,[z315,z1,z2,z21,z8,z5]),(0,[z85,z1,z2,z21,z8,z12]),(0,[z113,z1,z2,z3,z54,z12]),(0,[z1,z2,z1202,z3,z8,z5])],[(0,[z0,z1,z2,z7,z8,z264])],[(0,[z0,z1,z2,z3,z1203,z5]),(0,[z82,z0,z2,z21,z8,z83]),(0,[z0,z1,z3,z8,z225,z12])],[(0,[z0,z1,z2,z3,z997,z5]),(0,[z61,z1,z2,z21,z8,z12]),(0,[z92,z0,z2,z21,z31,z5]),(0,[z1,z2,z21,z8,z233,z12]),(0,[z0,z1,z267,z3,z86,z5]),(0,[z0,z1204,z2,z3,z8,z5])],[(0,[z0,z1,z2,z322,z8,z17]),(0,[z91,z1,z2,z21,z8,z12]),(0,[z0,z1,z2,z3,z8,z1205]),(0,[z0,z1,z505,z3,z8,z12]),(0,[z0,z584,z2,z3,z8,z332]),(0,[z0,z1,z361,z3,z8,z454])],[(0,[z1,z2,z159,z7,z8,z5]),(0,[z1,z666,z2,z3,z8,z12])],[(0,[z0,z1,z2,z534,z8,z97]),(0,[z0,z1206,z2,z3,z8,z5]),(0,[z555,z1,z2,z3,z8,z310])],[(0,[z0,z1,z2,z1207,z8,z5]),(0,[z0,z1,z2,z3,z1208,z5])],[(0,[z1,z158,z2,z21,z8,z12]),(0,[z0,z1,z2,z3,z8,z1209])],[(0,[z1,z2,z21,z8,z334,z5]),(0,[z0,z1,z2,z3,z8,z1210])],[(0,[z1,z2,z21,z8,z219,z12])],[(0,[z0,z1,z2,z1211,z8,z5]),(0,[z669,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z287,z8,z17]),(0,[z0,z1,z2,z3,z8,z1212]),(0,[z0,z1,z2,z1101,z7,z8]),(0,[z0,z171,z2,z585,z8,z5]),(0,[z0,z1,z2,z3,z8,z1213]),(0,[z0,z1,z2,z3,z1214,z5]),(0,[z312,z0,z1,z3,z1110,z5]),(0,[z0,z1,z2,z3,z123,z68])],[(0,[z0,z1,z62,z143,z3,z8])],[(0,[z0,z279,z2,z3,z170,z5]),(0,[z0,z1,z2,z202,z8,z5]),(0,[z0,z1,z2,z3,z8,z1215]),(0,[z0,z1,z143,z3,z238,z5]),(0,[z57,z0,z1,z2,z782,z5])]],
   [[(0,[z0,z1,z2,z3,z8,z1216]),(0,[z312,z0,z1,z21,z219,z5]),(0,[z0,z1,z116,z2,z8,z119]),(0,[z1,z2,z7,z8,z17,z12])],[(0,[z42,z1,z2,z3,z8,z26]),(0,[z0,z1,z2,z7,z8,z307]),(0,[z645,z1,z2,z3,z8,z12]),(0,[z1,z2,z3,z8,z479,z17]),(0,[z1217,z0,z1,z2,z3,z8]),(0,[z324,z0,z1,z3,z8,z206])],[(0,[z0,z1,z1218,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1219]),(0,[z0,z1220,z2,z3,z8,z5])],[(0,[z1,z195,z2,z21,z8,z12]),(0,[z75,z1,z2,z3,z8,z12]),(0,[z0,z1,z116,z2,z8,z987])],[(0,[z125,z1,z2,z3,z8,z12]),(0,[z1221,z1,z2,z3,z8,z5]),(0,[z0,z1,z41,z2,z3,z498])],[(0,[z0,z395,z2,z3,z8,z12]),(0,[z1222,z1,z2,z3,z8,z5]),(0,[z0,z1,z654,z3,z148,z5]),(0,[z0,z1,z149,z3,z8,z10])],[(0,[z0,z1,z2,z3,z8,z204]),(0,[z1,z2,z21,z8,z12,z68]),(0,[z0,z208,z79,z3,z8,z5])],[(0,[z328,z0,z43,z3,z8,z5]),(0,[z1223,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z1224,z8,z5]),(0,[z1225,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z1226,z8,z5]),(0,[z0,z279,z2,z3,z8,z17]),(0,[z0,z1,z2,z248,z8,z17]),(0,[z243,z1,z2,z3,z321,z5]),(0,[z0,z1,z143,z188,z8,z5])],[(0,[z1,z2,z95,z21,z8,z12]),(0,[z0,z1,z2,z482,z8,z97])],[(0,[z0,z1,z2,z320,z8,z121]),(0,[z92,z0,z2,z3,z31,z12])],[(0,[z1,z2,z9,z3,z8,z12]),(0,[z85,z0,z2,z190,z8,z17]),(0,[z0,z1,z2,z93,z8,z538])],[(0,[z0,z1,z2,z101,z8,z5]),(0,[z0,z1,z2,z356,z8,z365]),(0,[z122,z0,z1,z3,z8,z206]),(0,[z0,z158,z752,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z12])],[(0,[z1,z2,z21,z22,z8,z12]),(0,[z0,z1,z2,z1227,z8,z5]),(0,[z0,z616,z1,z3,z219,z5])],[(0,[z0,z279,z2,z3,z8,z161]),(0,[z0,z1228,z2,z3,z8,z5]),(0,[z1,z2,z21,z86,z31,z5])]],
   [[(0,[z129,z1,z80,z3,z130,z5]),(0,[z0,z1,z1000,z21,z8,z5]),(0,[z44,z0,z43,z3,z8,z17]),(0,[z0,z1,z3,z607,z219,z5])],[(0,[z0,z1,z361,z21,z8,z5]),(0,[z369,z1,z2,z3,z8,z17])],[(0,[z1,z492,z2,z21,z8,z12]),(0,[z0,z1,z2,z857,z8,z17]),(0,[z315,z1,z62,z2,z3,z8]),(0,[z0,z1,z1229,z2,z3,z8]),(0,[z0,z1,z2,z1230,z8,z5])],[],[(0,[z0,z1,z2,z3,z8,z376])],[(0,[z104,z1,z2,z7,z86,z5]),(0,[z0,z395,z267,z3,z8,z5]),(0,[z104,z1,z2,z178,z86,z5])],[(0,[z1,z2,z3,z247,z8,z12])],[(0,[z340,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z1231])],[(0,[z0,z1,z2,z188,z321,z5]),(0,[z0,z1232,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z175]),(0,[z1,z2,z3,z714,z8,z5]),(0,[z1,z2,z21,z49,z86,z5]),(0,[z0,z1,z2,z234,z21,z8]),(0,[z0,z1,z2,z3,z8,z1233]),(0,[z57,z0,z1,z2,z47,z310])],[],[(0,[z1234,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z1235,z8,z5]),(0,[z0,z1,z2,z287,z8,z236]),(0,[z0,z1236,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1237]),(0,[z1,z2,z95,z3,z8,z233])],[(0,[z0,z1,z414,z3,z8,z17]),(0,[z626,z30,z2,z3,z8,z5]),(0,[z0,z1,z267,z3,z8,z5]),(0,[z1,z2,z21,z89,z8,z12]),(0,[z650,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z1238,z8,z5])],[(0,[z0,z1,z2,z1239,z8,z5]),(0,[z0,z1,z41,z2,z3,z486]),(0,[z0,z1,z2,z3,z8,z1240]),(0,[z0,z218,z2,z3,z578,z5]),(0,[z243,z1,z2,z3,z238,z5]),(0,[z1241,z1,z2,z3,z8,z5])],[(0,[z0,z1,z267,z3,z8,z121]),(0,[z57,z0,z1,z2,z504,z5])]],
   [[(0,[z113,z1,z2,z21,z54,z5]),(0,[z64,z1,z2,z21,z8,z12]),(0,[z42,z1,z2,z714,z8,z5]),(0,[z0,z1,z2,z3,z8,z1242]),(0,[z0,z1,z2,z3,z8,z454]),(0,[z193,z208,z2,z3,z8,z5])],[(0,[z555,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z7,z321,z5]),(0,[z336,z0,z1,z3,z8,z20]),(0,[z0,z1,z2,z3,z8,z1243]),(0,[z1,z2,z3,z385,z8,z17]),(0,[z0,z1,z2,z1244,z8,z5]),(0,[z0,z1,z3,z8,z722,z206]),(0,[z1,z2,z95,z8,z5,z97])],[(0,[z0,z1,z2,z3,z1245,z5]),(0,[z113,z1,z2,z21,z8,z387]),(0,[z1,z2,z21,z8,z31,z12]),(0,[z0,z1246,z2,z3,z8,z5])],[(0,[z0,z1,z36,z2,z21,z8]),(0,[z0,z1,z2,z1247,z8,z5]),(0,[z610,z0,z2,z3,z8,z226]),(0,[z0,z1,z2,z58,z371,z5])],[(0,[z0,z1,z2,z1248,z8,z5]),(0,[z0,z279,z2,z33,z8,z5]),(0,[z0,z1,z505,z21,z8,z5]),(0,[z113,z1,z2,z21,z8,z12]),(0,[z1,z41,z2,z21,z8,z12]),(0,[z102,z1,z2,z3,z8,z17]),(0,[z1,z2,z3,z8,z5,z741])],[(0,[z0,z1,z2,z112,z8,z12]),(0,[z0,z1249,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z428]),(0,[z0,z1,z34,z3,z8,z428])],[(0,[z0,z1,z2,z1250,z8,z5]),(0,[z0,z1,z361,z3,z8,z12]),(0,[z0,z1,z2,z8,z192,z17])],[(0,[z0,z1,z1251,z3,z8,z5]),(0,[z1,z30,z2,z3,z8,z69]),(0,[z0,z1,z2,z1252,z8,z5]),(0,[z243,z1,z2,z3,z8,z376]),(0,[z0,z1,z2,z3,z8,z1253]),(0,[z0,z1,z885,z3,z8,z17]),(0,[z0,z1,z2,z3,z1254,z8]),(0,[z0,z1,z1255,z3,z8,z5]),(0,[z0,z1,z2,z93,z139,z8])],[(0,[z626,z1,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z858,z5])],[(0,[z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z8,z1256])],[(0,[z0,z1,z1257,z2,z8,z5])],[(0,[z0,z1,z2,z21,z8,z1033])],[(0,[z0,z1,z2,z322,z8,z69]),(0,[z0,z1,z2,z3,z8,z1258]),(0,[z0,z1,z2,z112,z8,z376]),(0,[z0,z1,z2,z3,z1259,z5]),(0,[z315,z1,z2,z3,z8,z332])],[(0,[z0,z1,z2,z1260,z8,z5]),(0,[z0,z1,z2,z3,z8,z1261]),(0,[z1,z2,z56,z21,z8,z12]),(0,[z0,z1,z2,z3,z1262,z5]),(0,[z0,z1,z2,z1263,z8,z5])],[(0,[z0,z1,z2,z174,z424,z5]),(0,[z0,z1,z2,z3,z8,z1264]),(0,[z0,z1,z1265,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z801])],[(0,[z142,z0,z2,z3,z31,z5])]],
   [[(0,[z0,z245,z2,z3,z8,z5]),(0,[z57,z0,z1,z2,z439,z5]),(0,[z315,z1,z360,z3,z8,z5]),(0,[z0,z1,z3,z1110,z219,z5])],[(0,[z0,z1,z2,z7,z8,z246]),(0,[z1,z2,z3,z8,z764,z5]),(0,[z64,z0,z1,z143,z3,z8])],[(0,[z30,z2,z3,z8,z497,z12]),(0,[z0,z1,z55,z56,z8,z12]),(0,[z82,z0,z360,z3,z8,z83])],[(0,[z0,z1,z2,z3,z8,z1266]),(0,[z0,z1,z2,z3,z1267,z5])],[(0,[z0,z1,z2,z8,z782,z5])],[(0,[z312,z0,z1,z3,z219,z17]),(0,[z0,z1,z2,z3,z1268,z5])],[(0,[z0,z1,z79,z3,z8,z12]),(0,[z0,z1,z3,z222,z5,z206]),(0,[z555,z1,z2,z3,z8,z996])],[(0,[z0,z1,z2,z7,z8,z387]),(0,[z0,z1,z2,z7,z238,z5]),(0,[z449,z1,z2,z7,z8,z5]),(0,[z0,z59,z158,z3,z8,z17]),(0,[z0,z1,z2,z1269,z8,z5]),(0,[z0,z1,z2,z3,z8,z1270])],[(0,[z0,z1,z2,z3,z1271,z5]),(0,[z122,z0,z1,z2,z7,z8]),(0,[z0,z61,z2,z3,z8,z788]),(0,[z0,z61,z2,z350,z3,z8]),(0,[z0,z1,z34,z3,z148,z5])],[],[(0,[z1,z2,z21,z486,z8,z12]),(0,[z0,z1,z809,z2,z3,z8])],[(0,[z0,z1,z2,z21,z8,z5]),(0,[z44,z1,z2,z21,z8,z12])],[(0,[z0,z1,z2,z103,z8,z12]),(0,[z0,z1,z11,z22,z8,z12])],[(0,[z1,z790,z2,z3,z8,z5]),(0,[z0,z1,z2,z21,z8,z121]),(0,[z1,z2,z21,z223,z8,z12]),(0,[z0,z187,z2,z37,z8,z5]),(0,[z555,z1,z11,z2,z8,z5])],[(0,[z0,z1,z1272,z3,z8,z5]),(0,[z1,z34,z2,z21,z8,z12]),(0,[z0,z1,z1273,z3,z8,z5]),(0,[z193,z1,z2,z3,z8,z1210])],[(0,[z0,z1,z2,z101,z130,z5]),(0,[z0,z1,z3,z8,z50,z17]),(0,[z0,z1,z2,z139,z238,z5]),(0,[z0,z2,z3,z8,z132,z788])]],
   [[(0,[z0,z1,z2,z3,z8,z1274]),(0,[z0,z1,z2,z3,z130,z12]),(0,[z0,z1,z88,z3,z8,z12]),(0,[z0,z1,z3,z8,z1275,z5])],[(0,[z1,z2,z825,z3,z8,z5]),(0,[z0,z1,z2,z139,z8,z12]),(0,[z0,z1,z2,z1276,z8,z5]),(0,[z0,z1,z2,z8,z1277,z5]),(0,[z449,z1,z2,z93,z8,z97])],[(0,[z1,z2,z583,z3,z8,z12]),(0,[z0,z1,z2,z562,z8,z17]),(0,[z1278,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z788]),(0,[z57,z0,z1,z2,z47,z5])],[(0,[z0,z1,z2,z3,z8,z1279]),(0,[z104,z1,z2,z320,z86,z5]),(1,[z0,z1,z3,z219,z428]),(0,[z0,z1,z1280,z3,z8,z5])],[(0,[z0,z1,z1281,z3,z8,z5]),(0,[z0,z1,z2,z3,z1039,z12]),(0,[z0,z1,z143,z3,z8,z12])],[(0,[z1,z2,z21,z8,z511,z12]),(0,[z15,z1,z2,z21,z8,z5]),(0,[z596,z0,z2,z3,z31,z5]),(0,[z0,z1,z2,z1282,z8,z5]),(0,[z1283,z1,z2,z3,z8,z5]),(0,[z0,z1,z1284,z3,z8,z5]),(0,[z555,z1,z55,z2,z8,z5])],[(0,[z0,z1,z2,z7,z424,z5]),(0,[z0,z1,z2,z1044,z8,z12]),(0,[z0,z1,z2,z3,z8,z1285])],[(0,[z0,z1,z1286,z2,z8,z5]),(0,[z1119,z0,z2,z3,z8,z12])],[(0,[z0,z1,z169,z3,z8,z17]),(0,[z0,z1,z2,z1287,z8,z5]),(0,[z0,z1,z34,z3,z568,z5]),(0,[z0,z1,z2,z481,z58,z5]),(0,[z0,z1,z2,z8,z1288,z5]),(0,[z254,z1,z2,z3,z8,z12]),(0,[z1,z2,z3,z8,z12,z100]),(0,[z0,z242,z2,z3,z8,z497]),(0,[z0,z1,z2,z3,z8,z1289])],[(0,[z0,z1,z2,z1290,z8,z5])],[(0,[z1,z2,z3,z21,z8,z387]),(1,[z1,z2,z3,z8,z741]),(0,[z555,z1,z79,z3,z8,z5]),(0,[z0,z1,z2,z782,z47,z5]),(0,[z0,z1,z2,z3,z8,z1291])],[(0,[z1,z2,z21,z8,z528,z5])],[(0,[z0,z1,z2,z3,z130,z175]),(0,[z129,z1,z80,z7,z8,z5]),(0,[z0,z208,z2,z7,z8,z5]),(0,[z0,z1,z3,z8,z219,z428])],[(0,[z0,z395,z2,z3,z8,z98]),(0,[z0,z1,z2,z1292,z8,z5])],[(0,[z0,z1,z2,z3,z1293,z5]),(0,[z91,z30,z2,z3,z8,z17]),(0,[z243,z1,z2,z21,z8,z5]),(0,[z0,z1,z34,z3,z399,z5])],[(0,[z0,z1,z109,z3,z148,z5]),(0,[z608,z1,z2,z3,z8,z12]),(0,[z0,z1,z3,z8,z1294,z5])]],
   [[(1,[z1,z2,z21,z8,z26]),(0,[z85,z0,z2,z583,z8,z5]),(0,[z1,z2,z3,z764,z86,z5]),(0,[z282,z1,z2,z3,z8,z12]),(0,[z193,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z906,z8,z5])],[(0,[z0,z255,z2,z21,z8,z5]),(0,[z0,z1,z2,z3,z522,z68]),(0,[z1295,z1,z2,z3,z8,z5])],[(0,[z0,z1,z198,z2,z8,z12]),(0,[z0,z1,z2,z1011,z8,z17]),(1,[z0,z752,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1296]),(0,[z57,z0,z255,z2,z47,z5])],[(0,[z0,z1,z414,z3,z8,z69]),(0,[z1,z2,z21,z8,z439,z5])],[(0,[z0,z1,z1077,z21,z8,z5]),(0,[z1,z2,z95,z3,z8,z5])],[(0,[z0,z1,z2,z3,z1111,z5]),(0,[z0,z1,z2,z3,z1297,z5]),(0,[z42,z1,z2,z7,z8,z17]),(0,[z0,z1,z2,z3,z8,z98]),(0,[z113,z1,z2,z3,z54,z17]),(0,[z0,z1,z2,z1298,z8,z5]),(0,[z0,z1,z2,z23,z782,z5])],[(0,[z0,z1,z2,z21,z8,z214]),(1,[z0,z1,z3,z1110,z5]),(0,[z57,z0,z1,z79,z47,z5])],[(0,[z0,z1,z2,z21,z4,z5]),(0,[z0,z967,z2,z3,z8,z5]),(0,[z0,z1,z968,z3,z8,z5]),(0,[z0,z1,z3,z8,z225,z17]),(0,[z0,z343,z2,z37,z8,z5])],[],[(0,[z351,z1,z2,z3,z8,z12]),(0,[z0,z1299,z2,z3,z8,z5]),(0,[z0,z1,z505,z3,z8,z17]),(0,[z485,z1,z2,z3,z86,z5]),(0,[z0,z1,z2,z3,z216,z12]),(0,[z0,z1,z1300,z2,z8,z5])],[(0,[z1,z2,z21,z8,z12,z206]),(0,[z1,z2,z21,z8,z74,z12]),(0,[z75,z1,z2,z247,z8,z12]),(0,[z1,z2,z3,z8,z12,z363]),(0,[z1,z2,z3,z8,z12,z364])],[(0,[z0,z1,z414,z322,z8,z5]),(0,[z0,z1,z2,z1301,z8,z5]),(0,[z0,z1,z2,z529,z139,z8]),(1,[z0,z1,z2,z8,z987])],[(0,[z239,z1,z153,z7,z8,z5]),(0,[z1,z84,z2,z3,z8,z12]),(0,[z0,z1,z2,z1302,z8,z5])],[(0,[z1,z2,z177,z21,z8,z5]),(0,[z0,z1,z2,z3,z8,z1303]),(0,[z0,z1,z1304,z3,z8,z5])],[(0,[z1,z30,z2,z21,z8,z12]),(0,[z406,z1,z2,z21,z8,z5]),(0,[z0,z1,z361,z3,z14,z8])],[(0,[z0,z865,z2,z3,z8,z5]),(0,[z1,z2,z3,z54,z764,z5]),(0,[z0,z1,z2,z3,z765,z5]),(0,[z0,z1,z3,z8,z1110,z5])]]]

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
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 502).take 492) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 994).take 430) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1424)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [502, 492, 430] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 108).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 216).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 323).take 93).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 416).take 96).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [108, 108, 107, 93, 96] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

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

end PEqualNP.Outside.L_meta_36382

theorem PEqualNP.Outside.L_meta_36382 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276944008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276944008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36382.solve