import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41506

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
  Nat.testBit (4277071584 * 2 ^ 32 + 4205496448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x004261c3209586c9#64 ++ 0x000109870c82561b#64 ++ 0x04c6e3c723ff8ffe#64 ++ 0x94131b8f1c8ffe3f#64 : BitVec 256),
   (0x09582c58c24c3b52#64 ++ 0x082560b1630930ed#64 ++ 0x1b793c78c24cfffd#64 ++ 0xf86de4f1e30933ff#64 : BitVec 256),
   (0x6381c02d6c70d19c#64 ++ 0x058e0700b5b1c346#64 ++ 0xe381c07ffc70f1fb#64 ++ 0xaf8e0701fff1c3c7#64 : BitVec 256),
   (0xbc01d680b780ec20#64 ++ 0x12f0075a02de03b0#64 ++ 0xfc01ff80ff80fe37#64 ++ 0xdff007fe03fe03f8#64 : BitVec 256),
   (0xdfac0000db6a0000#64 ++ 0x037eb000036da800#64 ++ 0xfffe0000ffff002f#64 ++ 0xeffff80003fffc00#64 : BitVec 256),
   (0xf6f7bb7600000000#64 ++ 0x23dbdeedd8000000#64 ++ 0xffffffff0000001f#64 ++ 0xf3fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [6, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [11, 4]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x04c6e3c723ff8ffe 0x94131b8f1c8ffe3f

def z1 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b793c78c24cfffd 0xf86de4f1e30933ff

def z2 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe381c07ffc70f1fb 0xaf8e0701fff1c3c7

def z3 : W := mkw 0x6b99cc3dee78f99e 0x0dae6730f7b9e3e6 0xfbb9dc7ffc70f1fb 0xefeee771fff1c3c7

def z4 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc01ff80ff80fe37 0xdff007fe03fe03f8

def z5 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfffe0000ffff002f 0xeffff80003fffc00

def z6 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffffffff0000001f 0xf3fffffffc000000

def z7 : W := mkw 0x09080408c2483912 0x08242010230920e4 0x00000000c0007000 0x08000000030001c0

def z8 : W := mkw 0xfef7fff7b795eee9 0x33fbdfffdede57bb 0xffffffffffffffff 0xffffffffffffffff

def z9 : W := mkw 0x9400000011000000 0x0250000000440000 0xe40000003d800002 0x0790000000f60000

def z10 : W := mkw 0x9c00168093802c20 0x1270005a024e00b0 0xfc003f80ff800e27 0xdff000fe03fe0038

def z11 : W := mkw 0xbd5bffdbf7ddfffb 0x1af56fff6fdf77ff 0xffffffffffffffff 0xffffffffffffffff

def z12 : W := mkw 0x6281c0252c30c08c 0x058a070094b0c302 0xe080c0473c7081fa 0x878203011cf1c207

def z13 : W := mkw 0x09080000c2480000 0x0024200003092000 0x1b780000c24c002d 0xe86de00003093000

def z14 : W := mkw 0xdffc2c58db6e3b52 0x0b7ff0b1636db8ed 0xffff3c78ffffffff 0xfffffcf1e3ffffff

def z15 : W := mkw 0xf6a7932600000000 0x23da9e4c98000000 0xfffec3870000000f 0xe3fffb0e1c000000

def z16 : W := mkw 0x0002018200810401 0x0000080608020410 0x0406038001830000 0x0010180e00060c00

def z17 : W := mkw 0xf6f7bb77001502c9 0x23dbdeeddc00540b 0xffffffff007f01df 0xf3fffffffc01fc07

def z18 : W := mkw 0xd6e661c339b786c9 0x035b99870ce6de1b 0xe4c6e3c73fff8ffe 0x97931b8f1cfffe3f

def z19 : W := mkw 0xbc01d681b790eca8 0x12f0075a06de43b2 0xfc81ffc7fff0ffff 0xdff207ff1fffc3ff

def z20 : W := mkw 0x0000000000000000 0x0000000000000000 0x04c6000023ff002e 0x84131800008ffc00

def z21 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xfb39ffff00000011 0x73ece7fffc000000

def z22 : W := mkw 0xf6f7fbf7209586c9 0x23dbdfefdc82561b 0xffffffff00008fdf 0xf3fffffffc00023f

def z23 : W := mkw 0x2003932600000000 0x20800e4c98000000 0x0000c38700000000 0x0000030e1c000000

def z24 : W := mkw 0x4380002d4870119c 0x050e0000b521c046 0x0380007f007001c8 0x200e0001fc01c007

def z25 : W := mkw 0x9c00168093802c20 0x1270005a024e00b0 0x1c003f8003800e04 0x507000fe000e0038

def z26 : W := mkw 0xbc01c000b700c000 0x02f0070002dc0300 0xfc01c000ff80f037 0xcff0070003fe03c0

def z27 : W := mkw 0x43ac0000486a0000 0x010eb0000121a800 0x03fe0000007f0008 0x200ff8000001fc00

def z28 : W := mkw 0x63adc02d6c7ad19c 0x058eb700b5b1eb46 0xe3ffc07ffc7ff1fb 0xaf8fff01fff1ffc7

def z29 : W := mkw 0xff81d62dff70f9bc 0x17fe0758b7fdc3e6 0xfb81dc7ffc70f1fb 0xefee0771fff1c3c7

def z30 : W := mkw 0xf6b59a3400000000 0x23dad668d0000000 0xffff1c380000000f 0xe3fffc70e0000000

def z31 : W := mkw 0xbc43f7c2b780ec20 0x12f10fdf0ade03b0 0xfcc7ffc7ff80fe3f 0xdff31fff1ffe03f8

def z32 : W := mkw 0x9d583ed8d3cc3f72 0x1a7560fb634f30fd 0x1f793ff8c3ccfffd 0xf87de4ffe30f33ff

def z33 : W := mkw 0x4380000048600000 0x010e000001218000 0xe7c60000ffff002f 0xaf9f180003fffc00

def z34 : W := mkw 0x6281802400000000 0x018a060090000000 0xe381c07f0000001b 0xa38e0701fc000000

def z35 : W := mkw 0xf7f7fb7f6c70d19c 0x27dfdfedfdb1c346 0xfffffffffc70f1ff 0xfffffffffff1c3c7

def z36 : W := mkw 0x9d7e3f5ac24c3b52 0x2a75f8fd6b0930ed 0x1f7f3ff8c24cfffd 0xf87dfcffe30933ff

def z37 : W := mkw 0xf6f5ba7400000000 0x23dbd6e9d0000000 0xfb793c780000001d 0xf3ede4f1e0000000

def z38 : W := mkw 0x0000408020808400 0x0000010200820210 0x0400e38023808e36 0x9410038e008e0238

def z39 : W := mkw 0xbc43f7c3b795eee9 0x12f10fdf0ede57bb 0xfcc7ffc7ffffffff 0xdff31fff1fffffff

def z40 : W := mkw 0x0000000800001110 0x0000000020000044 0x000100780000f1d0 0x00000401e00003c7

def z41 : W := mkw 0x2801d680a680ec20 0x10a0075a029a03b0 0x1801ff80c200fe35 0xd86007fe030803f8

def z42 : W := mkw 0x010040096c70d19c 0x0404010025b1c346 0x00000000fc70f1e0 0x0c00000003f1c3c7

def z43 : W := mkw 0x94763b5200000000 0x2251d8ed48000000 0x1c7e3f8000000004 0x5071f8fe00000000

def z44 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfcc7ff80fffffe3f 0xdff31ffe03fffff8

def z45 : W := mkw 0xf6a7d3a720918489 0x23da9f4e9c824612 0xe486c38721b30002 0x07921b0e1c86cc00

def z46 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe380c07f3c7001ca 0x278e0301fcf1c007

def z47 : W := mkw 0xbd59fed8f7ccff72 0x1af567fb63df33fd 0xff79fff8ffccffff 0xfffde7ffe3ff33ff

def z48 : W := mkw 0xffffbb76c2480000 0x23fffeeddb092000 0xffffffffc24c003f 0xfbffffffff093000

def z49 : W := mkw 0xb401d2002400c000 0x02d0074800900300 0xfc01ff80fc00f037 0xdff007fe03f003c0

def z50 : W := mkw 0x2001d6802480ec20 0x1080075a009203b0 0x0001ff800000fe10 0x100007fe000003f8

def z51 : W := mkw 0x095a2d5ac24c3b52 0x082568b56b0930ed 0x1fffffffc24cffff 0xf87fffffff0933ff

def z52 : W := mkw 0xdfac0400db6a2800 0x037eb010036da8a0 0xffff3c00fffffe3f 0xfffffcf003fffff8

def z53 : W := mkw 0x000040803580c420 0x1000010200d60310 0x000000003d800000 0x0400000000f60000

def z54 : W := mkw 0x2001c02d2410d19c 0x04800700b4904346 0x0001c07f0000f1d0 0x00000701fc0003c7

def z55 : W := mkw 0x9c2c0000930a0000 0x0270b000024c2800 0x1c7e0000038f0004 0x4071f800000e3c00

def z56 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x00013c78c24cfff0 0x180004f1e30933ff

def z57 : W := mkw 0x08004480b780ec20 0x1020011202de03b0 0x0400e380ff80fe36 0x9c10038e03fe03f8

def z58 : W := mkw 0xd7ac0000596a0000 0x035eb0000165a800 0xe7fe00003dff000a 0x279ff80000f7fc00

def z59 : W := mkw 0x09000408c2403910 0x00240010230900e4 0x1b013c78c240fffd 0xf86c04f1e30903ff

def z60 : W := mkw 0xb401920000000000 0x02d0064800000000 0xfc01ff8000000017 0xd3f007fe00000000

def z61 : W := mkw 0x42f6297600000000 0x210bd8a5d8000000 0x03fe007f00000008 0x200ff801fc000000

def z62 : W := mkw 0x6281c02d2410d19c 0x058a0700b4904346 0xe381c07f0000f1db 0xa38e0701fc0003c7

def z63 : W := mkw 0x4380402d6870919c 0x050e0100b5a1c246 0x0380c07f207081fa 0xa40e0301fc81c207

def z64 : W := mkw 0x20119a3400000000 0x20804668d0000000 0x00011c3800000000 0x00000470e0000000

def z65 : W := mkw 0xf6b59a3400000000 0x23dad668d0000000 0xfb391c3800000001 0x63ece470e0000000

def z66 : W := mkw 0x085a6dd3a29daecb 0x082169b74e8a76bb 0x1cfeffc723ff8ffe 0xd473fbff1c8ffe3f

def z67 : W := mkw 0xfea7d7a6b780ec20 0x33fa9f5e9ade03b0 0xfc87ff87ff80fe37 0xdff21ffe1ffe03f8

def z68 : W := mkw 0xb443f3c3209586c9 0x02d10fcf0c82561b 0xfcc7ffc723ff8fff 0xd7f31fff1c8ffe3f

def z69 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x0000e3c723ff8ff0 0x1400038f1c8ffe3f

def z70 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x0000e3c700008fd0 0x1000038f1c00023f

def z71 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfb380000dc000001 0x6bece00003700000

def z72 : W := mkw 0x2001c02d2410d19c 0x04800700b4904346 0x0081c07f2070f1fa 0x84020701fc81c3c7

def z73 : W := mkw 0x08080400820c2a42 0x08202010020830a9 0x00000000020c0e00 0x0000000000083038

def z74 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x0040e3c7024c8ffc 0x9001038f1c09323f

def z75 : W := mkw 0xfeb5deb4b780ec20 0x33fad77ad2de03b0 0xff39ffb8ff80fe37 0xfffce7fee3fe03f8

def z76 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x04c6e38723bf0e06 0x14131b8e1c8efc38

def z77 : W := mkw 0x63c3e1ef6cf5d7dd 0x058f0f87bdb3d75f 0xe381e3fffc70fffb 0xbf8e078ffff1c3ff

def z78 : W := mkw 0xfeb59e3497006820 0x33fad678d25c01a0 0xfb391c38dc007001 0x6bece470e37001c0

def z79 : W := mkw 0x0002010200000000 0x0000080408000000 0x0486c38700000002 0x00121b0e1c000000

def z80 : W := mkw 0xdfbc0c18db6a3912 0x0b7ef030636da8e4 0xfb391c38dc007001 0x6bece470e37001c0

def z81 : W := mkw 0x0000408020808400 0x0000010200820210 0x0400c38021800002 0x0410030e00860000

def z82 : W := mkw 0x6381802d4c70519c 0x058e0600b531c146 0xe381007fdc7071c9 0x2b8e0401ff71c1c7

def z83 : W := mkw 0xffbd9a34db6a0000 0x23fef668d36da800 0xffff1c38ffff002f 0xeffffc70e3fffc00

def z84 : W := mkw 0xfe81d6a5bfb0ecac 0x17fa075a96fec3b2 0xfc81ff87ffb0fe37 0xdff207fe1ffec3f8

def z85 : W := mkw 0xfef7bff693802c20 0x33fbdeffda4e00b0 0xffffffff03800e1f 0xf3fffffffc0e0038

def z86 : W := mkw 0x09080400c2482800 0x00242010030920a0 0x1b793c00c24cfe3d 0xf86de4f0030933f8

def z87 : W := mkw 0x6381802c4c605114 0x058e0600b1318144 0xe3010078dc40f1f9 0xab8c0401e37103c7

def z88 : W := mkw 0xdfae4183fbfb8489 0x037eb9060fefee12 0xfffec387ffff002f 0xeffffb0e1ffffc00

def z89 : W := mkw 0x0000400120108088 0x0000010004804202 0x0080c047207081fa 0x840203011c81c207

def z90 : W := mkw 0xff81d6adfff0fdbc 0x17fe075ab7ffc3f6 0xff81fffffff0ffff 0xfffe07ffffffc3ff

def z91 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x18783c00c24cffe4 0x5861e0f0030933ff

def z92 : W := mkw 0x42f669f7209586c9 0x210bd9a7dc82561b 0x07fee3ff23ff8ffe 0xb41ffb8ffc8ffe3f

def z93 : W := mkw 0xd6e661c3209586c9 0x035b99870c82561b 0xfffee3c723ff8fff 0xf7fffb8f1c8ffe3f

def z94 : W := mkw 0x09084489e2ddbfdb 0x08242112278b76ff 0x00000000e3ffffe0 0x0c000000038fffff

def z95 : W := mkw 0x6381c0ad6cf0d59c 0x058e0702b5b3c356 0xe781e3fffff0ffff 0xbf9e078fffffc3ff

def z96 : W := mkw 0x0800040082002800 0x00200010020800a0 0x18013c00c200fe35 0xd86004f0030803f8

def z97 : W := mkw 0x0800040082002800 0x00200010020800a0 0x00000000c200fe20 0x08000000030803f8

def z98 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xe4860000ffff0022 0x0f92180003fffc00

def z99 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0x1c01ff800380fe14 0x507007fe000e03f8

def z100 : W := mkw 0xffadd6adfffafdbc 0x17feb75ab7ffebf6 0xffffffffffffffff 0xffffffffffffffff

def z101 : W := mkw 0x0052295200000000 0x000148a548000000 0x1fffffff0000001f 0xf07ffffffc000000

def z102 : W := mkw 0x095a6ddbe2ddbfdb 0x082569b76f8b76ff 0x1fffffffe3ffffff 0xfc7fffffff8fffff

def z103 : W := mkw 0x0002418320918489 0x000009060c824612 0x0000c38700000000 0x0000030e1c000000

def z104 : W := mkw 0xbc01960082002800 0x02f00658020800a0 0xfc01ff80c200fe37 0xdbf007fe030803f8

def z105 : W := mkw 0x0000408120908488 0x0000010204824212 0x0480e3c723f08ffe 0x9412038f1c8fc23f

def z106 : W := mkw 0x09180c18c2483912 0x08246030630920e4 0x1b391c38c0007001 0x686ce470e30001c0

def z107 : W := mkw 0xffffbf7ec24c3b52 0x2bfffefdfb0930ed 0xffffffffc24cffff 0xfbffffffff0933ff

def z108 : W := mkw 0x6381802c4c605114 0x058e0600b1318144 0xe3010038dc007001 0x2b8c0400e37001c0

def z109 : W := mkw 0xffadc02dff7ad19c 0x07feb700b7fdeb46 0xffffc07ffffff1ff 0xefffff01ffffffc7

def z110 : W := mkw 0x0800040097006820 0x10200010025c01a0 0x00000000dc007000 0x08000000037001c0

def z111 : W := mkw 0xdfac002ddb7a119c 0x077eb000b76de846 0xfffe007fffff01ef 0xeffff801fffffc07

def z112 : W := mkw 0x0000400120108088 0x0000010004804202 0x00000000207081e0 0x040000000081c207

def z113 : W := mkw 0x08582c50820c2a42 0x082160b1420830a9 0x18783c40024c8ffc 0xd061e0f10009323f

def z114 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfb380000ffff0021 0x6fece00003fffc00

def z115 : W := mkw 0x010040096c70d19c 0x0404010025b1c346 0x0080c047fc70f1fa 0x8c0203011ff1c3c7

def z116 : W := mkw 0x09080408c24c3b52 0x08242010230930ed 0x00000000c24cffe0 0x08000000030933ff

def z117 : W := mkw 0xf6a7932600000000 0x23da9e4c98000000 0xe486c38700000002 0x03921b0e1c000000

def z118 : W := mkw 0x4bd82c7dca7c3bde 0x0d2f60b1f729f0ef 0x1bf93c7fc27cfffd 0xf86fe4f1ff09f3ff

def z119 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc01df80fd807003 0x4ff0077e03f601c0

def z120 : W := mkw 0x9c6e21c2938f0641 0x0271b8870a4e3c19 0x1c7e2380038f0e04 0x5071f88e000e3c38

def z121 : W := mkw 0x0042214200000000 0x0001088508000000 0x04c6e3c70000001e 0x90131b8f1c000000

def z122 : W := mkw 0xf6f7fbf7209586c9 0x23dbdfefdc82561b 0xffffffff23ff8fff 0xf7fffffffc8ffe3f

def z123 : W := mkw 0x6381c0ad6cf5d7dd 0x058e0702b5b3d75f 0xe381c07ffffffffb 0xaf8e0701ffffffff

def z124 : W := mkw 0x62d1a87400000000 0x018b46a1d0000000 0xfbf9fc7f0000001f 0xf3efe7f1fc000000

def z125 : W := mkw 0x63d3fb7f6c70d19c 0x258f4fedfdb1c346 0xe381fffffc70f1fb 0xbf8e07fffff1c3c7

def z126 : W := mkw 0xffefe1efffffd7dd 0x07ffbf87bfffff5f 0xffffe3ffffffffff 0xffffff8fffffffff

def z127 : W := mkw 0x94763b5200000000 0x2251d8ed48000000 0x1cfeffc70000001e 0xd073fbff1c000000

def z128 : W := mkw 0x94763bd200850641 0x2251d8ef48021419 0x1c7e3f80038f0e04 0x5071f8fe000e3c38

def z129 : W := mkw 0xdffc2c50db6e2a42 0x0b7ff0b1436db8a9 0xfffe3c00ffff0e2f 0xfffff8f003fffc38

def z130 : W := mkw 0x2001c02d2410d19c 0x04800700b4904346 0xe001c07ffc00f1f3 0x8f800701fff003c7

def z131 : W := mkw 0xf6a7932619220000 0x23da9e4c98648800 0xe486c3873db30002 0x07921b0e1cf6cc00

def z132 : W := mkw 0x01582858404c1352 0x080560a16101304d 0x03780078004c01c8 0x200de001e0013007

def z133 : W := mkw 0xb401d2803580c420 0x12d0074a00d60310 0xe400c3803d800002 0x0790030e00f60000

def z134 : W := mkw 0x0002418320918489 0x000009060c824612 0x04c6c38723ff002e 0x84131b0e1c8ffc00

def z135 : W := mkw 0xf6f7bb7619220000 0x23dbdeedd8648800 0xffffffff3db3001f 0xf7fffffffcf6cc00

def z136 : W := mkw 0xb477bb5200000000 0x22d1deed48000000 0xfc7fff8000000017 0xd3f1fffe00000000

def z137 : W := mkw 0xb453bb7600000000 0x22d14eedd8000000 0xfc01ffff00000017 0xd3f007fffc000000

def z138 : W := mkw 0x00422143001502c9 0x000108850c00540b 0x00c60047007f01c8 0x000318011c01fc07

def z139 : W := mkw 0xdfee61c3fbff86c9 0x037fb9870feffe1b 0xfffee3c7ffff8fff 0xfffffb8f1ffffe3f

def z140 : W := mkw 0x6281c02520108088 0x018a070094804202 0xe381c07f207081fb 0xa78e0701fc81c207

def z141 : W := mkw 0x0000000000000000 0x0000000000000000 0x1b7800000000000d 0xe06de00000000000

def z142 : W := mkw 0x09084480ffeaec20 0x1024211203ffabb0 0x00000000fffffe20 0x0c00000003fffff8

def z143 : W := mkw 0x6b81c42dee70f99c 0x05ae0710b7b9c3e6 0xfb81fc7ffe70ffff 0xffee07f1fff9c3ff

def z144 : W := mkw 0xf681922400000000 0x03da064890000000 0xff81ffff0000001f 0xf3fe07fffc000000

def z145 : W := mkw 0x00502c5800043b52 0x080140b1600010ed 0x00013c780000ffd0 0x100004f1e00003ff

def z146 : W := mkw 0xd6a4000019220000 0x035a900000648800 0xe48600003db30002 0x0792180000f6cc00

def z147 : W := mkw 0x0050285000000000 0x000140a140000000 0x1b793c780000001d 0xf06de4f1e0000000

def z148 : W := mkw 0x62f7bb7600000000 0x218bdeedd8000000 0x03ffffff00000018 0x300ffffffc000000

def z149 : W := mkw 0x9c4237c293852e61 0x127108df0a4e14b9 0x1c463f80038f0e04 0x507118fe000e3c38

def z150 : W := mkw 0x9d2c0000db6a0000 0x0274b000036da800 0x1c7e0000ffff0024 0x4c71f80003fffc00

def z151 : W := mkw 0x0040204000040240 0x0001008100001009 0x00402040024c8ffc 0x900100810009323f

def z152 : W := mkw 0x00004081209586c9 0x000001020482561b 0x0000000023ff8fe0 0x04000000008ffe3f

def z153 : W := mkw 0x09080000db6a0000 0x00242000036da800 0x00000000ffff0020 0x0c00000003fffc00

def z154 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z155 : W := mkw 0x0118081840481112 0x0804602061012044 0x0338003800000000 0x200ce000e0000000

def z156 : W := mkw 0xbc01968097806c20 0x12f0065a025e01b0 0xfc013f80df807e05 0x5bf004fe037e01f8

def z157 : W := mkw 0x0100000840401110 0x0004000021010044 0x03010078c040f1f9 0xa80c0401e30103c7

def z158 : W := mkw 0x6bd9ec7dee7cfbde 0x0daf67b1f7b9f3ef 0xfbf9fc7ffe7cffff 0xffefe7f1fff9f3ff

def z159 : W := mkw 0x6b89c02dff7ad19c 0x05ae2700b7fdeb46 0xe381c07ffffff1fb 0xaf8e0701ffffffc7

def z160 : W := mkw 0x9c7e3b52930a0000 0x2271f8ed4a4c2800 0x1c7e3f80038f0004 0x5071f8fe000e3c00

def z161 : W := mkw 0x43ac0000486a0000 0x010eb0000121a800 0x0338000000000000 0x200ce00000000000

def z162 : W := mkw 0x2001c0002400c000 0x0080070000900300 0x0001c0000000f010 0x00000700000003c0

def z163 : W := mkw 0x2001c0002400c000 0x0080070000900300 0xe001c000fc00f033 0x8f80070003f003c0

def z164 : W := mkw 0xdffe3b52db6a0000 0x237ff8ed4b6da800 0xfffe3f80ffff002f 0xfffff8fe03fffc00

def z165 : W := mkw 0x0052297600000000 0x200148a5d8000000 0x0000007f00000000 0x00000001fc000000

def z166 : W := mkw 0x0000008000800400 0x0000000200020010 0x0400238003800e04 0x1010008e000e0038

def z167 : W := mkw 0x2101c0086440d110 0x0084070021910344 0xe301c078fc40f1fb 0xaf8c0701e3f103c7

def z168 : W := mkw 0xffadd680ffeaec20 0x13feb75a03ffabb0 0xffffff80fffffe3f 0xfffffffe03fffff8

def z169 : W := mkw 0x4b880000ca680000 0x012e20000329a000 0xfbf80000fe7c002f 0xefefe00003f9f000

def z170 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xf801ff80dc00fe11 0x5be007fe037003f8

def z171 : W := mkw 0xd6f6297600000000 0x235bd8a5d8000000 0xfffe007f0000000f 0xe3fff801fc000000

def z172 : W := mkw 0x095a2ddac2cd3f53 0x082568b76b0b34fd 0x1f7f3ff8c3cffffd 0xf87dfcffe30f3fff

def z173 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000023800026 0x84100000008e0000

def z174 : W := mkw 0xbc01d6adb790fdbc 0x16f0075ab6de43f6 0xfc01ffffff80fff7 0xdff007fffffe03ff

def z175 : W := mkw 0x01080000486a0000 0x000420000121a800 0x00000000007f0000 0x000000000001fc00

def z176 : W := mkw 0x4380402d6c70d19c 0x050e0100b5b1c346 0x0380007ffc70f1e8 0x2c0e0001fff1c3c7

def z177 : W := mkw 0x08582c50820c2a42 0x082160b1420830a9 0x18783c00020c0e04 0x5061e0f000083038

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000000fc000023 0x8f80000003f00000

def z179 : W := mkw 0x2959fed8e6ccff72 0x18a567fb639b33fd 0x1b79fff8c24cfffd 0xf86de7ffe30933ff

def z180 : W := mkw 0xd6a4000000000000 0x035a900000000000 0xfffe00000000000f 0xe3fff80000000000

def z181 : W := mkw 0xffffbb76db6a0000 0x23fffeeddb6da800 0xffffffffffff003f 0xfffffffffffffc00

def z182 : W := mkw 0x0000000100100088 0x0000000004004002 0x00800047007001c8 0x000200011c01c007

def z183 : W := mkw 0xffad802cdf6a5114 0x07feb600b37da944 0xfb390038dc007001 0x6bece400e37001c0

def z184 : W := mkw 0x09586c59e25cbbda 0x082561b1678972ef 0x1bf9fc7fe27cffff 0xfc6fe7f1ff89f3ff

def z185 : W := mkw 0x08004481b795eee9 0x1020011206de57bb 0x00000000ffffffe0 0x0c00000003ffffff

def z186 : W := mkw 0x6b89c02dee78d19c 0x05ae2700b7b9e346 0xfbf9c07ffe7cf1ff 0xefefe701fff9f3c7

def z187 : W := mkw 0x9c2c0000930a0000 0x0270b000024c2800 0x1838000000000000 0x4060e00000000000

def z188 : W := mkw 0xdfee2143db7f02c9 0x037fb8850f6dfc0b 0xfffe0047ffff01ef 0xeffff8011ffffc07

def z189 : W := mkw 0xdfac0408db6e3b52 0x0b7eb010236db8ed 0xfffe0000ffffffef 0xeffff80003ffffff

def z190 : W := mkw 0x000040002400c000 0x0000010000900300 0x00000000fc00f020 0x0c00000003f003c0

def z191 : W := mkw 0x9c4261c3b39586c9 0x027109870ece561b 0xfcc6e3c7ffff8fff 0xdff31b8f1ffffe3f

def z192 : W := mkw 0x63c3e1ef6cf5d7dd 0x058f0f87bdb3d75f 0xe7c7e3ffffffffff 0xbf9f1f8fffffffff

def z193 : W := mkw 0x004221c200850641 0x0001088708021419 0x04462380038f0e04 0x1011188e000e3c38

def z194 : W := mkw 0x0808000082080000 0x0020200002082000 0x18780000020c0004 0x4061e00000083000

def z195 : W := mkw 0x6281802400000000 0x018a060090000000 0xe080c00700000002 0x038203001c000000

def z196 : W := mkw 0xfea5d680b780ec20 0x13fa975a02de03b0 0xffffff80ff80fe3f 0xfffffffe03fe03f8

def z197 : W := mkw 0x0002418320918489 0x000009060c824612 0x0486c38721b30002 0x04121b0e1c86cc00

def z198 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xe487ffff00000012 0x13921ffffc000000

def z199 : W := mkw 0x9c7c2c50930e2a42 0x0a71f0b1424c38a9 0x1c7e3c00038f0e04 0x5071f8f0000e3c38

def z200 : W := mkw 0xd6f4285000000000 0x035bd0a140000000 0xffff3c780000001f 0xf3fffcf1e0000000

def z201 : W := mkw 0x6381802d4870119c 0x058e0600b521c046 0xe381c07f007001db 0xa38e0701fc01c007

def z202 : W := mkw 0x08004480b780ec20 0x1020011202de03b0 0x00000000ff80fe20 0x0c00000003fe03f8

def z203 : W := mkw 0xbc01960097006820 0x12f00658025c01a0 0xf8011c00dc007001 0x4be00470037001c0

def z204 : W := mkw 0x0100000840401110 0x0004000021010044 0x00000000c040f1e0 0x08000000030103c7

def z205 : W := mkw 0x6281c0252c30c08c 0x058a070094b0c302 0xe381c07f3c30001b 0xa78e0701fcf0c000

def z206 : W := mkw 0x09080408c24c3b52 0x08242010230930ed 0x03010078c24cfff9 0xa80c0401e30933ff

def z207 : W := mkw 0x6381c0006c60c000 0x018e070001b18300 0xe381c000fc70f03b 0xaf8e070003f1c3c0

def z208 : W := mkw 0x00004081209586c9 0x000001020482561b 0x0080c04723ff8ffa 0x840203011c8ffe3f

def z209 : W := mkw 0x42f6297600000000 0x210bd8a5d8000000 0x07fee3ff0000001e 0xb01ffb8ffc000000

def z210 : W := mkw 0x010040096c70d19c 0x0404010025b1c346 0x03010078fc70f1f9 0xac0c0401e3f1c3c7

def z211 : W := mkw 0x4380000048600000 0x010e000001218000 0xe3800000fc70002b 0xaf8e000003f1c000

def z212 : W := mkw 0xfef7fff6b780ec20 0x33fbdfffdade03b0 0xffffffffff80fe3f 0xfffffffffffe03f8

def z213 : W := mkw 0x085a2dd2828d2e43 0x082168b74a0a34b9 0x1c7e3f80038f0e04 0x5071f8fe000e3c38

def z214 : W := mkw 0x09180c18c24c3b52 0x08246030630930ed 0x1b391c38c24cffe1 0x686ce470e30933ff

def z215 : W := mkw 0x6383c1af6cf1d59d 0x058e0f06bdb3c756 0xe787c3fffdf3f1fb 0xaf9e1f0ffff7cfc7

def z216 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xfcfeff8700000006 0x53f3fbfe1c000000

def z217 : W := mkw 0x0050285000000000 0x000140a140000000 0x0378007800000008 0x200de001e0000000

def z218 : W := mkw 0x09080408db6e3b52 0x08242010236db8ed 0x00000000ffffffe0 0x0c00000003ffffff

def z219 : W := mkw 0x09084009ff7ad19c 0x0424210027fdeb46 0x00000000fffff1e0 0x0c00000003ffffc7

def z220 : W := mkw 0xf6a7d3a63580c420 0x33da9f4e98d60310 0xe486c3873d800002 0x07921b0e1cf60000

def z221 : W := mkw 0xf6b79b3600000000 0x23dade6cd8000000 0xffbfdfbf00000003 0x63feff7efc000000

def z222 : W := mkw 0x4380002c48601114 0x050e0000b1218044 0x0300003800000000 0x200c0000e0000000

def z223 : W := mkw 0x9c00000093000000 0x02700000024c0000 0xfcc60000ffff002f 0xcff3180003fffc00

def z224 : W := mkw 0xf781d22d6c70d19c 0x07de0748b5b1c346 0xff81fffffc70f1ff 0xfffe07fffff1c3c7

def z225 : W := mkw 0x9c00000093000000 0x02700000024c0000 0x1c00000003800004 0x40700000000e0000

def z226 : W := mkw 0x2001802c04005114 0x04800600b0100144 0x0001003800007000 0x00000400e00001c0

def z227 : W := mkw 0x0042214200000000 0x0001088508000000 0x0000e3c700000010 0x1000038f1c000000

def z228 : W := mkw 0xf6f7fb7720108088 0x23dbdfeddc804202 0xffffffff207081ff 0xf7fffffffc81c207

def z229 : W := mkw 0xd6e6214200000000 0x035b988508000000 0xfffee3c70000001f 0xf3fffb8f1c000000

def z230 : W := mkw 0xdf800000db600000 0x037e0000036d8000 0xff800000fff0002f 0xeffe000003ffc000

def z231 : W := mkw 0xf7ffbb76486a0000 0x23dffeedd921a800 0xffffffff007f001f 0xf3fffffffc01fc00

def z232 : W := mkw 0x004221c200850641 0x0001088708021419 0x044623c003cf8ffc 0x9011188f000f3e3f

def z233 : W := mkw 0x08582c58820c3b52 0x082160b1620830ed 0x18793c78020cffd4 0x5061e4f1e00833ff

def z234 : W := mkw 0x09080408c24c3b52 0x08242010230930ed 0x1b780000c24cffed 0xe86de000030933ff

def z235 : W := mkw 0x0042214200000000 0x0001088508000000 0x04c6e3c723ff003e 0x94131b8f1c8ffc00

def z236 : W := mkw 0x0000000000000000 0x0000000000000000 0x008000002070002a 0x840200000081c000

def z237 : W := mkw 0x0800000082000000 0x0020000002080000 0x18000000c2000025 0xc860000003080000

def z238 : W := mkw 0x09080000c2480000 0x0024200003092000 0x00000000c24c0020 0x0800000003093000

def z239 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe301c07fdc00f1d1 0x2b8c0701ff7003c7

def z240 : W := mkw 0x6b998c3cce687916 0x0dae6630f339a1e4 0xfb391c38dc007001 0x6bece470e37001c0

def z241 : W := mkw 0x0100000048600000 0x0004000001218000 0x00000000fc700020 0x0c00000003f1c000

def z242 : W := mkw 0x09582c58db6e3b52 0x082560b1636db8ed 0x1b793c78fffffffd 0xfc6de4f1e3ffffff

def z243 : W := mkw 0x0000008000850641 0x0000000200021419 0x00000000038f0e00 0x00000000000e3c38

def z244 : W := mkw 0xb401d2803580c420 0x12d0074a00d60310 0xfc01ff803d800017 0xd7f007fe00f60000

def z245 : W := mkw 0x010000084c605114 0x0404000021318144 0x00000000dc007000 0x08000000037001c0

def z246 : W := mkw 0x2051fed82484ff72 0x188147fb609213fd 0x0001fff80000ffd0 0x100007ffe00003ff

def z247 : W := mkw 0x6381c0256c70c08c 0x058e070095b1c302 0xe380c007fc70002b 0xaf8e03001ff1c000

def z248 : W := mkw 0x2101c02d6c70d19c 0x04840700b5b1c346 0x0001c07ffc70f1f0 0x0c000701fff1c3c7

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x00010000c000f031 0x88000400030003c0

def z250 : W := mkw 0x9d7c2c58d34e3b52 0x0a75f0b1634d38ed 0x1f7f3c78c3cffffd 0xf87dfcf1e30f3fff

def z251 : W := mkw 0x6bd9ac7cc24c3b52 0x09af66b1f30930ed 0xfbf9fc7fc24cffff 0xfbefe7f1ff0933ff

def z252 : W := mkw 0x000044802480ec20 0x10000112009203b0 0x000000000000fe00 0x00000000000003f8

def z253 : W := mkw 0x2101c0096c70d19c 0x0484070025b1c346 0xe001c000fc70f1f3 0x8f80070003f1c3c7

def z254 : W := mkw 0xd6f63b5200000000 0x235bd8ed48000000 0xfffe3f800000000f 0xf3fff8fe00000000

def z255 : W := mkw 0x00422143001502c9 0x000108850c00540b 0x04c6e3c7007f01de 0x90131b8f1c01fc07

def z256 : W := mkw 0xf6f7bf7e00043b52 0x2bdbdefdf80010ed 0xffffffff0000ffdf 0xf3fffffffc0003ff

def z257 : W := mkw 0x6281802400000000 0x018a060090000000 0xe301003800000001 0x238c0400e0000000

def z258 : W := mkw 0x00502c5000042a42 0x080140b1400010a9 0x00003c0000000e00 0x100000f000000038

def z259 : W := mkw 0x0000002d0010119c 0x04000000b4004046 0x0000007f000001c0 0x00000001fc000007

def z260 : W := mkw 0x42a4000000000000 0x010a900000000000 0x03fe000000000008 0x200ff80000000000

def z261 : W := mkw 0x094a61c3fbff86c9 0x002529870feffe1b 0x04c6e3c7ffff8ffe 0x9c131b8f1ffffe3f

def z262 : W := mkw 0x0000408020808400 0x0000010200820210 0x0000e38000008e10 0x1000038e00000238

def z263 : W := mkw 0x9d2c0000d34a0000 0x0274b000034d2800 0x1f7e0000c3cf002d 0xe87df800030f3c00

def z264 : W := mkw 0x0042214200040240 0x0001088508001009 0x04c6e3c7024c8ffe 0x90131b8f1c09323f

def z265 : W := mkw 0xdeac0000930a0000 0x037ab000024c2800 0xfffe0000038f000f 0xe3fff800000e3c00

def z266 : W := mkw 0x004060c020848640 0x0001018300821219 0x0440e3c023cc8ffe 0x9411038f008f323f

def z267 : W := mkw 0x08502c5882043b52 0x082140b1620810ed 0x18013c78c200fff5 0xd86004f1e30803ff

def z268 : W := mkw 0x09180c18c2483912 0x08246030630920e4 0x1b791c38c24c702d 0xe86de470e30931c0

def z269 : W := mkw 0x00502c5800043b52 0x080140b1600010ed 0x1b793c780000ffdd 0xf06de4f1e00003ff

def z270 : W := mkw 0x0000400020008000 0x0000010000800200 0x0000c00020008032 0x8400030000800200

def z271 : W := mkw 0x09586cd9e2ddbfdb 0x082561b3678b76ff 0x1b793c78e3fffffd 0xfc6de4f1e38fffff

def z272 : W := mkw 0x0000000000000000 0x0000000000000000 0x04460000038f0004 0x00111800000e3c00

def z273 : W := mkw 0x2053bb7600000000 0x20814eedd8000000 0x0001ffff00000010 0x100007fffc000000

def z274 : W := mkw 0xbc01d280b780c420 0x12f0074a02de0310 0xfc00c380ff800027 0xcff0030e03fe0000

def z275 : W := mkw 0x0000408020808400 0x0000010200820210 0x04c6e38023ff8e3e 0x94131b8e008ffe38

def z276 : W := mkw 0x4280000000000000 0x010a000000000000 0xe38000000000000b 0xa38e000000000000

def z277 : W := mkw 0xbc01968093802c20 0x12f0065a024e00b0 0xfc01ff8003800e17 0xd3f007fe000e0038

def z278 : W := mkw 0x4380002d4870119c 0x050e0000b521c046 0x0381007fc070f1f9 0xa80e0401ff01c3c7

def z279 : W := mkw 0x09080008c2481110 0x0024200023092044 0x1b790078c24cf1fd 0xe86de401e30933c7

def z280 : W := mkw 0x9c004480b780ec20 0x1270011202de03b0 0xfc000000ff80fe27 0xcff0000003fe03f8

def z281 : W := mkw 0x09080000c2480000 0x0024200003092000 0x1ffe0000e3ff002f 0xec7ff800038ffc00

def z282 : W := mkw 0x005269d3209586c9 0x000149a74c82561b 0x1fffffff23ff8fff 0xf47ffffffc8ffe3f

def z283 : W := mkw 0xffffffffe2ddbfdb 0x2bffffffff8b76ff 0xffffffffe3ffffff 0xffffffffff8fffff

def z284 : W := mkw 0xb403d3833591c4a9 0x12d00f4e0cd64712 0xe486c3873db30002 0x07921b0e1cf6cc00

def z285 : W := mkw 0xf7f7bb7e40401110 0x23dfdeedf9010044 0xffffffffc040f1ff 0xfbffffffff0103c7

def z286 : W := mkw 0x08582c50820c2a42 0x082160b1420830a9 0x18793c00c20cfe35 0xd861e4f0030833f8

def z287 : W := mkw 0x43c261c368f586c9 0x010f09870da3d61b 0xe7c6e3c7ffff8fff 0xbf9f1b8f1ffffe3f

def z288 : W := mkw 0x9c00000093000000 0x02700000024c0000 0xfc000000ff800027 0xcff0000003fe0000

def z289 : W := mkw 0x2053fff62480ec20 0x30814fffd89203b0 0x0001ffff0000fe10 0x100007fffc0003f8

def z290 : W := mkw 0xdfac0008db6a1110 0x037eb000236da844 0xffff0078fffff1ff 0xeffffc01e3ffffc7

def z291 : W := mkw 0xf6f7fb762400c000 0x23dbdfedd8900300 0xfffffffffc00f03f 0xfffffffffff003c0

def z292 : W := mkw 0xdfac1680dbea2c20 0x137eb05a036fa8b0 0xfffe3f80ffff0e2f 0xfffff8fe03fffc38

def z293 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfffe0000dc00000f 0xebfff80003700000

def z294 : W := mkw 0x2043e1c32495c6c9 0x00810f870c92571b 0xe4c7e3c7ffffffff 0x9f931f8f1fffffff

def z295 : W := mkw 0x002c0000000a0000 0x0000b00000002800 0x007e0000000f0000 0x0001f80000003c00

def z296 : W := mkw 0xbc41f6c0b784ee60 0x12f107db02de13b9 0xfc41ffc0ffccffff 0xdff107ff03ff33ff

def z297 : W := mkw 0xdffe6ddbfbffbfdb 0x0b7ff9b76feffeff 0xffffffffffffffff 0xffffffffffffffff

def z298 : W := mkw 0x0100400960509198 0x0004010025814246 0x0381c07fe070f1fb 0xac0e0701ff81c3c7

def z299 : W := mkw 0x08180c1082082802 0x08206030420820a0 0x18381c0000000000 0x4060e07000000000

def z300 : W := mkw 0x2053fbf7209586c9 0x20814fefdc82561b 0x0001ffff00008fd0 0x100007fffc00023f

def z301 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xe7fec3ff0000000a 0x239ffb0ffc000000

def z302 : W := mkw 0xf6a5d2803da2c420 0x13da974a00f68b10 0xe486c3803db30002 0x07921b0e00f6cc00

def z303 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x0400e3c723808ff6 0x9410038f1c8e023f

def z304 : W := mkw 0x4bfc2c58ca6e3b52 0x092ff0b16329b8ed 0x1bff3c78c27ffffd 0xf86ffcf1e309ffff

def z305 : W := mkw 0xb401920000000000 0x02d0064800000000 0xf8011c0000000001 0x43e0047000000000

def z306 : W := mkw 0xd6f63b7600000000 0x235bd8edd8000000 0x1ffe3fff0000000c 0x707ff8fffc000000

def z307 : W := mkw 0x00523b5200000000 0x200148ed48000000 0x00003f8000000000 0x100000fe00000000

def z308 : W := mkw 0x2959ec7de65cfbde 0x0ca567b1f79973ef 0x1b79fc7fc24cfffd 0xf86de7f1ff0933ff

def z309 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x04c6c3c721ff01ca 0x04131b0f1c87fc07

def z310 : W := mkw 0x0040204000040240 0x0001008100001009 0x00400040004c01c8 0x0001000100013007

def z311 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080c0470000001a 0x800203011c000000

def z312 : W := mkw 0xfffdfed8ffeeff72 0x1bfff7fb63ffbbfd 0xfffffff8ffffffff 0xffffffffe3ffffff

def z313 : W := mkw 0x4bac0000db6a0000 0x012eb000036da800 0x03fe0000ffff0028 0x2c0ff80003fffc00

def z314 : W := mkw 0x43c2216f487513dd 0x050f0885bd21d44f 0x03c6007f007f01c8 0x200f1801fc01fc07

def z315 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffffffff23ff003f 0xf7fffffffc8ffc00

def z316 : W := mkw 0x0002418320918489 0x000009060c824612 0x0486e38723b38e36 0x94121b8e1c8ece38

def z317 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x0446238023ff8fe4 0x1411188e008ffe3f

def z318 : W := mkw 0x63f7e97f6c70d19c 0x258fdfa5fdb1c346 0xe3ffc07ffc70f1fb 0xaf8fff01fff1c3c7

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000200002008e34 0x9000008000080238

def z320 : W := mkw 0x43ac0000486a0000 0x010eb0000121a800 0x07fe000023ff002e 0xa41ff800008ffc00

def z321 : W := mkw 0x0076295200000000 0x2001d8a548000000 0x007e000000000000 0x0001f80000000000

def z322 : W := mkw 0xf6f7bbf600850641 0x23dbdeefd8021419 0xffffffff038f0e1f 0xf3fffffffc0e3c38

def z323 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c60000007f0008 0x000318000001fc00

def z324 : W := mkw 0xffffff7fee7cfbde 0x2ffffffdffb9f3ef 0xfffffffffe7cffff 0xfffffffffff9f3ff

def z325 : W := mkw 0xb401920000000000 0x02d0064800000000 0xe400c38000000002 0x0390030e00000000

def z326 : W := mkw 0xbc2dd680b78aec20 0x12f0b75a02de2bb0 0xfc7fff80ff8ffe37 0xdff1fffe03fe3ff8

def z327 : W := mkw 0xffffbf7ec2483912 0x2bfffefdfb0920e4 0xffffffffc000701f 0xfbffffffff0001c0

def z328 : W := mkw 0xffbd9e3cc2483912 0x2bfef678f30920e4 0xfb391c38c0007001 0x6bece470e30001c0

def z329 : W := mkw 0xf6a7d3272c30c08c 0x27da9f4c9cb0c302 0xe486c3873c300002 0x07921b0e1cf0c000

def z330 : W := mkw 0xd7ac0000486a0000 0x035eb0000121a800 0xfffe0000007f000f 0xe3fff8000001fc00

def z331 : W := mkw 0x0010081000000000 0x0000402040000000 0x1b391c3800000001 0x606ce470e0000000

def z332 : W := mkw 0x6bd9ac7cce6c7b56 0x0daf66b1f339b1ed 0xfb793c78de4cfffd 0xfbede4f1e37933ff

def z333 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe7c7c07ffffff1ff 0xaf9f1f01ffffffc7

def z334 : W := mkw 0x9d080000db6a0000 0x02742000036da800 0xfc000000ffff0027 0xcff0000003fffc00

def z335 : W := mkw 0x63d1ec7d6c74fbde 0x0d8f47b1f5b1d3ef 0xe381fc7ffc70fffb 0xbf8e07f1fff1c3ff

def z336 : W := mkw 0x62d3bb7600000000 0x218b4eedd8000000 0xe381ffff0000001b 0xb38e07fffc000000

def z337 : W := mkw 0xffadc02dff7ad19c 0x07feb700b7fdeb46 0xfbb9c07ffc70f1fb 0xefeee701fff1c3c7

def z338 : W := mkw 0x00100c1800003912 0x08004030600000e4 0x00011c3800007000 0x00000470e00001c0

def z339 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc00ff803f800e06 0x57f003fe00fe0038

def z340 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b783c78024c0fcc 0x706de0f1e009303f

def z341 : W := mkw 0x2001960004006820 0x10800658001001a0 0x00011c0000007000 0x00000470000001c0

def z342 : W := mkw 0xdeac00009b2a0000 0x037ab000026ca800 0xfcfe00003fbf0006 0x47f3f80000fefc00

def z343 : W := mkw 0x2001d6ad2490fdbc 0x1480075ab49243f6 0x0001ffff0000ffd0 0x100007fffc0003ff

def z344 : W := mkw 0x09586c59ee7cfbde 0x0c2561b167b9f3ef 0x1b793c78fe7cfffd 0xfc6de4f1e3f9f3ff

def z345 : W := mkw 0xf6a5802400000000 0x03da960090000000 0xffffc07f0000001f 0xe3ffff01fc000000

def z346 : W := mkw 0x628180240c204004 0x058a060090308100 0xe00000001c000000 0x0380000000700000

def z347 : W := mkw 0x00422143001502c9 0x000108850c00540b 0x00000047000001c0 0x000000011c000007

def z348 : W := mkw 0xdfac4081fbff86c9 0x037eb10207effe1b 0xfffe0000ffff8fef 0xeffff80003fffe3f

def z349 : W := mkw 0x62f7a97600000000 0x218bdea5d8000000 0xe3ffc07f0000001b 0xa38fff01fc000000

def z350 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x0080e3c720708ffa 0x9402038f1c81c23f

def z351 : W := mkw 0xffadd280ffeac420 0x13feb74a03ffab10 0xfffec380ffff002f 0xeffffb0e03fffc00

def z352 : W := mkw 0x004221c3009506c9 0x000108870c02541b 0x04c623c703ff0fcc 0x1013188f1c0ffc3f

def z353 : W := mkw 0x2053bb7600000000 0x20814eedd8000000 0x1b79ffff0000001d 0xf06de7fffc000000

def z354 : W := mkw 0x0002010300110089 0x000008040c004402 0x0086000700330000 0x000218001c00cc00

def z355 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfb780000de4c002d 0xebede00003793000

def z356 : W := mkw 0x0000408120918489 0x0000010204824612 0x0000000021b30000 0x040000000086cc00

def z357 : W := mkw 0x2051ec7d2414fbde 0x0c8147b1f49053ef 0x0001fc7f0000ffd0 0x100007f1fc0003ff

def z358 : W := mkw 0x00422143001502c9 0x000108850c00540b 0x04c6004723ff01ee 0x841318011c8ffc07

def z359 : W := mkw 0x014261cb60d597d9 0x000509872d83565f 0x07c7e3ffe3ffffff 0xbc1f1f8fff8fffff

def z360 : W := mkw 0x6381c02c6c60d114 0x058e0700b1b18344 0xe301c038fc00f033 0xaf8c0700e3f003c0

def z361 : W := mkw 0x63d9e87d6c7cd3de 0x0d8f67a1f5b1f34f 0xe3f9c07ffc7cf1fb 0xaf8fe701fff1f3c7

def z362 : W := mkw 0x9424000011020000 0x0250900000440800 0x0406000001830000 0x0010180000060c00

def z363 : W := mkw 0xbc01d600b700e820 0x12f0075802dc03a0 0xf801dc00fc00f033 0xcfe0077003f003c0

def z364 : W := mkw 0x0000408020808400 0x0000010200820210 0x0000000023808e20 0x04000000008e0238

def z365 : W := mkw 0xfffffbf7fbff86c9 0x23ffffefdfeffe1b 0xffffffffffff8fff 0xfffffffffffffe3f

def z366 : W := mkw 0xfff7fffffff0fdbc 0x37ffdfffffffc3f6 0xfffffffffff0ffff 0xffffffffffffc3ff

def z367 : W := mkw 0xffffbf7edb6e3b52 0x2bfffefdfb6db8ed 0xffffffffffffffff 0xffffffffffffffff

def z368 : W := mkw 0xf6f7fb7f2410d19c 0x27dbdfedfc904346 0xffffffff0000f1df 0xf3fffffffc0003c7

def z369 : W := mkw 0xd7a4000059620000 0x035e900001658800 0xe7860000fdf3002b 0xaf9e180003f7cc00

def z370 : W := mkw 0xb443f3c33595c6e9 0x12d10fcf0cd6571b 0xe4c6e3c73fff8ffe 0x97931b8f1cfffe3f

def z371 : W := mkw 0x00526ddb2095bfdb 0x080149b76c8256ff 0x0001ffff0000ffd0 0x100007fffc0003ff

def z372 : W := mkw 0xdfac4001fb7a8088 0x037eb10007edea02 0xfffec047ffff81ff 0xeffffb011ffffe07

def z373 : W := mkw 0xfffffffef7ccff72 0x3bfffffffbdf33fd 0xffffffffffccffff 0xffffffffffff33ff

def z374 : W := mkw 0x2001d2802480c420 0x1080074a00920310 0x0000c38000000000 0x0000030e00000000

def z375 : W := mkw 0x4bfe2d7ec24c3b52 0x292ff8b5fb0930ed 0x1bff3c7fc24cfffd 0xf86ffcf1ff0933ff

def z376 : W := mkw 0x09180c18c2483912 0x08246030630920e4 0x1b391c78c040f1f9 0xe86ce471e30103c7

def z377 : W := mkw 0x9400120000000000 0x0250004800000000 0x1c003f8000000004 0x507000fe00000000

def z378 : W := mkw 0x0042614320108088 0x000109850c804202 0x04c6e3c7207081fe 0x94131b8f1c81c207

def z379 : W := mkw 0x9c00000093000000 0x02700000024c0000 0xf8000000dc000001 0x4be0000003700000

def z380 : W := mkw 0x9c004080b3808400 0x0270010202ce0210 0xfc00e380ff808e37 0xdff0038e03fe0238

def z381 : W := mkw 0xdfac0000c2480000 0x037eb00003092000 0xfffe0000c24c002f 0xebfff80003093000

def z382 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x0446e3c7038f8fd4 0x10111b8f1c0e3e3f

def z383 : W := mkw 0xf6a5c0253d32c08c 0x07da970094f4cb02 0xe486c0073db30002 0x07921b001cf6cc00

def z384 : W := mkw 0x9424000000000000 0x0250900000000000 0x1c7e000000000004 0x4071f80000000000

def z385 : W := mkw 0xbc01960097006820 0x12f00658025c01a0 0xf8013c00de00fe35 0xdbe004f0037803f8

def z386 : W := mkw 0xbc01960097006820 0x12f00658025c01a0 0xfc011c00ff807027 0xcff0047003fe01c0

def z387 : W := mkw 0x00004081209586c9 0x000001020482561b 0x0000000000008fc0 0x000000000000023f

def z388 : W := mkw 0xdfee21c2dbef0641 0x037fb8870b6fbc19 0xfffe2380ffff0e2f 0xfffff88e03fffc38

def z389 : W := mkw 0xfffdec7dff7efbde 0x0ffff7b1f7fdfbef 0xfffffc7fffffffff 0xfffffff1ffffffff

def z390 : W := mkw 0x2001c0002400c000 0x0080070000900300 0xe000c0003c000002 0x0780030000f00000

def z391 : W := mkw 0x0000400120108088 0x0000010004804202 0x0080c00720300002 0x040203001c80c000

def z392 : W := mkw 0x0140204840441350 0x000500812101104d 0x03412078c24cfffd 0xb80d0481e30933ff

def z393 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b791c78c04c71c9 0x686de471e30131c7

def z394 : W := mkw 0xffd9fefdfffcfffe 0x1fff67fbf7fff3ff 0xfff9fffffffcffff 0xffffe7fffffff3ff

def z395 : W := mkw 0x43f6297f4870119c 0x250fd8a5fd21c046 0x03fe007f007001c8 0x200ff801fc01c007

def z396 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfbb80000fc70002b 0xefeee00003f1c000

def z397 : W := mkw 0x2053bf7e00043b52 0x28814efdf80010ed 0x0001ffff0000ffd0 0x100007fffc0003ff

def z398 : W := mkw 0x09582c50c24c2a42 0x082560b1430930a9 0x1b783c00c24c0e2d 0xf86de0f003093038

def z399 : W := mkw 0xffad9600df6a6820 0x13feb658037da9a0 0xffff1c00ffff702f 0xeffffc7003fffdc0

def z400 : W := mkw 0x6281c0252c30c08c 0x058a070094b0c302 0xe080c0073c300002 0x078203001cf0c000

def z401 : W := mkw 0x42b4083400000000 0x210ad020d0000000 0x0338003800000000 0x200ce000e0000000

def z402 : W := mkw 0x6381802c4c605114 0x058e0600b1318144 0xe3810038fc70702b 0xaf8e0400e3f1c1c0

def z403 : W := mkw 0x01582858404c1352 0x080560a16101304d 0x1b793c78004c01dd 0xf06de4f1e0013007

def z404 : W := mkw 0x00004081209586c9 0x000001020482561b 0x04c6000023ff8fee 0x84131800008ffe3f

def z405 : W := mkw 0x2043e1ef2495d7dd 0x04810f87bc92575f 0x0001e3ff0000ffd0 0x1000078ffc0003ff

def z406 : W := mkw 0xf681d2a53db0c4ac 0x17da074a94f6c312 0xe480c3873db00002 0x0792030e1cf6c000

def z407 : W := mkw 0xffffbb76db6a0000 0x23fffeeddb6da800 0xffffffffdc00001f 0xfbffffffff700000

def z408 : W := mkw 0xbd01d688f7c0fd30 0x12f4075a23df03f4 0xff01fff8ffc0ffff 0xfffc07ffe3ff03ff

def z409 : W := mkw 0x0050285800041352 0x080140a16000104d 0x00000078000001c0 0x00000001e0000007

def z410 : W := mkw 0xbc51fed8b784ff72 0x1af147fb62de13fd 0xfc01fff8ff80fff7 0xdff007ffe3fe03ff

def z411 : W := mkw 0xfeffbb76930a0000 0x23fbfeedda4c2800 0xffffffff038f001f 0xf3fffffffc0e3c00

def z412 : W := mkw 0xffbd9a34db6a0000 0x23fef668d36da800 0xfb391c38dc000001 0x6bece470e3700000

def z413 : W := mkw 0xf6a5922400000000 0x23da964890000000 0xe000000000000000 0x0380000000000000

def z414 : W := mkw 0x0100000840401110 0x0004000021010044 0x03000078004001c8 0x200c0001e0010007

def z415 : W := mkw 0x08080000930a0000 0x00202000024c2800 0x00000000038f0000 0x00000000000e3c00

def z416 : W := mkw 0xbd01d689fff0fdbc 0x16f4075a27ffc3f6 0xfc01ff80fff0fff7 0xdff007fe03ffc3ff

def z417 : W := mkw 0xbc03d783b791eca9 0x12f00f5e0ede47b2 0xfc87ff87ffb3fe37 0xdff21ffe1ffecff8

def z418 : W := mkw 0x0042214200000000 0x0001088508000000 0x0446238000000004 0x1011188e00000000

def z419 : W := mkw 0xb443b34200000000 0x02d10ecd08000000 0xfcc7ffc70000001f 0xd3f31fff1c000000

def z420 : W := mkw 0xfef7bf7682002800 0x23fbdefdda0800a0 0xffffffffc200fe3f 0xfbffffffff0803f8

def z421 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b393c78c000ffd1 0x786ce4f1e30003ff

def z422 : W := mkw 0xffaf9326db6a0000 0x23febe4c9b6da800 0xfffec387ffff002f 0xeffffb0e1ffffc00

def z423 : W := mkw 0x09586cd8f7ccff72 0x182561b363df33fd 0x1b793c78ffccfffd 0xfc6de4f1e3ff33ff

def z424 : W := mkw 0xdfee2142db6a0000 0x037fb8850b6da800 0xfffee3c7ffff003f 0xfffffb8f1ffffc00

def z425 : W := mkw 0x43d8287d487c13de 0x0d0f60a1f521f04f 0x03f8007f007c01c8 0x200fe001fc01f007

def z426 : W := mkw 0x9c2c0000930a0000 0x0270b000024c2800 0xfc7e0000ff8f0027 0xcff1f80003fe3c00

def z427 : W := mkw 0x4280002400000000 0x010a000090000000 0x0380007f00000008 0x200e0001fc000000

def z428 : W := mkw 0x43ee2143487f02c9 0x010fb8850d21fc0b 0x03fe0047007f01c8 0x200ff8011c01fc07

def z429 : W := mkw 0x00582850000c0242 0x080160a140003009 0x00780000000c0000 0x0001e00000003000

def z430 : W := mkw 0xd6a4000019220000 0x035a900000648800 0xfffe00003db3000f 0xe7fff80000f6cc00

def z431 : W := mkw 0x0108000040480000 0x0004200001012000 0x03780000004c0008 0x200de00000013000

def z432 : W := mkw 0xdffc2850db6a0000 0x037ff0a1436da800 0xffff3c78ffff003f 0xfffffcf1e3fffc00

def z433 : W := mkw 0x004261c220858641 0x0001098708821619 0x0446e380238f8e36 0x94111b8e008e3e38

def z434 : W := mkw 0x63c1e06d6c74d3dc 0x058f0781b5b1d34f 0xe3c1e07ffe7cffff 0xbf8f0781fff9f3ff

def z435 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1fff3c78e3ffffff 0xfc7ffcf1e38fffff

def z436 : W := mkw 0x6b81c4adfff0fdbc 0x15ae0712b7ffc3f6 0xe381c07ffff0fffb 0xaf8e0701ffffc3ff

def z437 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xff380000ff800027 0xeffce00003fe0000

def z438 : W := mkw 0xffadc025ff7ac08c 0x07feb70097fdeb02 0xfffec007ffff002f 0xeffffb001ffffc00

def z439 : W := mkw 0x2101c02d6450d19c 0x04840700b5914346 0x0301c07fc040f1f9 0xa80c0701ff0103c7

def z440 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x00c6e3c7007f8fd8 0x10031b8f1c01fe3f

def z441 : W := mkw 0x2053fbf7209586c9 0x20814fefdc82561b 0x04c7ffff23ff8ffe 0x94131ffffc8ffe3f

def z442 : W := mkw 0xbc51fed0b780ec20 0x12f147fb42de03b0 0xff79fff8ff80fe3f 0xfffde7ffe3fe03f8

def z443 : W := mkw 0x09080000db6a0000 0x00242000036da800 0x00000000dc000000 0x0800000003700000

def z444 : W := mkw 0x9c6e61c3b39f86c9 0x0271b9870ece7e1b 0x1cfee3c723ff8ffe 0xd473fb8f1c8ffe3f

def z445 : W := mkw 0x010040896cf5d7dd 0x0404010225b3d75f 0x00000000ffffffe0 0x0c00000003ffffff

def z446 : W := mkw 0x00426143201582c9 0x000109850c80560b 0x00c6c047207f81fa 0x84031b011c81fe07

def z447 : W := mkw 0x94767bd3209586c9 0x2251d9ef4c82561b 0x1cfeffc723ff8ffe 0xd473fbff1c8ffe3f

def z448 : W := mkw 0x09004489fff0fdbc 0x1424011227ffc3f6 0x00000000fff0ffe0 0x0c00000003ffc3ff

def z449 : W := mkw 0xf7f7bb7648600000 0x23dfdeedd9218000 0xfffffffffc70003f 0xfffffffffff1c000

def z450 : W := mkw 0xf6a5920000000000 0x03da964800000000 0xffffff800000001f 0xf3fffffe00000000

def z451 : W := mkw 0xf6f7fbf620808400 0x23dbdfefd8820210 0xffffffff23808e3f 0xf7fffffffc8e0238

def z452 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xfbff1c7f00000009 0x63effc71fc000000

def z453 : W := mkw 0x4380400168708088 0x010e010005a1c202 0xe380c047fc7081fb 0xaf8e03011ff1c207

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x0301007800000019 0xa00c0401e0000000

def z455 : W := mkw 0xdfac4009ff7ad19c 0x077eb10027fdeb46 0xfffe0000fffff1ef 0xeffff80003ffffc7

def z456 : W := mkw 0xbc43f7c2b785ee61 0x12f10fdf0ade17b9 0xfc47ff80ff8ffe37 0xdff11ffe03fe3ff8

def z457 : W := mkw 0x9c4277c3b395aee9 0x127109df0ece56bb 0x1cc6ffc723ff8ffe 0xd4731bff1c8ffe3f

def z458 : W := mkw 0x2001920000000000 0x0080064800000000 0x0001ff8000000010 0x100007fe00000000

def z459 : W := mkw 0x2001c0012410c088 0x0080070004904302 0xe081c047fc70f1fb 0x8f8207011ff1c3c7

def z460 : W := mkw 0x0000000019220000 0x0000000000648800 0x000000003db30000 0x0400000000f6cc00

def z461 : W := mkw 0x09582c58c2483912 0x082560b1630920e4 0x1b793c78c000701d 0xf86de4f1e30001c0

def z462 : W := mkw 0x01582c58404c3b52 0x080560b1610130ed 0x03793c78004cffd8 0x300de4f1e00133ff

def z463 : W := mkw 0x9c2c0000930a0000 0x0270b000024c2800 0x1cfe000023ff002e 0xc473f800008ffc00

def z464 : W := mkw 0x09180c18c2483912 0x08246030630920e4 0x1b393c38c200fe35 0xf86ce4f0e30803f8

def z465 : W := mkw 0x0800000093000000 0x00200000024c0000 0x00000000ff800020 0x0c00000003fe0000

def z466 : W := mkw 0x0000000000040240 0x0000000000001009 0x00000000024c8fe0 0x000000000009323f

def z467 : W := mkw 0xb401d28020808400 0x02d0074a00820210 0xfc01ff8023808e37 0xd7f007fe008e0238

def z468 : W := mkw 0x0050285000000000 0x000140a140000000 0x00013c7800000010 0x100004f1e0000000

def z469 : W := mkw 0x0040204000040240 0x0001008100001009 0x0000204000008fd0 0x100000810000023f

def z470 : W := mkw 0x095a2d5bc25d3bdb 0x082568b56f0974ef 0x1bff3c7fc27ffffd 0xf86ffcf1ff09ffff

def z471 : W := mkw 0x0100000040400000 0x0004000001010000 0x03000000c0400029 0xa80c000003010000

def z472 : W := mkw 0x9c2c1680938a2c20 0x1270b05a024e28b0 0x1c7e3f80038f0e04 0x5071f8fe000e3c38

def z473 : W := mkw 0x63d1e87d6c70d19c 0x058f47a1f5b1c346 0xfbf9fc7ffc70f1ff 0xffefe7f1fff1c3c7

def z474 : W := mkw 0x010000094870119c 0x040400002521c046 0x00000000007001c0 0x000000000001c007

def z475 : W := mkw 0xffad8024db6a0000 0x03feb600936da800 0xffffc07fffff003f 0xefffff01fffffc00

def z476 : W := mkw 0x004221c200850641 0x0001088708021419 0x04c6e3c7038f0e1e 0x90131b8f1c0e3c38

def z477 : W := mkw 0xff81c02dff70d19c 0x07fe0700b7fdc346 0xff81c07ffff0f1ff 0xeffe0701ffffc3c7

def z478 : W := mkw 0xffad9200db6a0000 0x03feb648036da800 0xffffff80ffff003f 0xfffffffe03fffc00

def z479 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b793c38c20c7e05 0x786de4f0e30831f8

def z480 : W := mkw 0x63c3e16f6c75d3dd 0x058f0f85bdb1d74f 0xe3c7c07ffc7ff1fb 0xaf8f1f01fff1ffc7

def z481 : W := mkw 0xb401d6802480ec20 0x12d0075a009203b0 0xfc01ff800000fe17 0xd3f007fe000003f8

def z482 : W := mkw 0x0042214200050241 0x0001088508001409 0x00460000000f0000 0x0001180000003c00

def z483 : W := mkw 0x0040204000040240 0x0001008100001009 0x04c6204023ff8ffe 0x94131881008ffe3f

def z484 : W := mkw 0x9c00168093802c20 0x1270005a024e00b0 0x1c013f80c380fe35 0xd87004fe030e03f8

def z485 : W := mkw 0x4bd82c58ca6c3b52 0x092f60b16329b0ed 0xfbf93c78fe7cffff 0xffefe4f1e3f9f3ff

def z486 : W := mkw 0x4b880000db6a0000 0x012e2000036da800 0xe3800000ffff002b 0xaf8e000003fffc00

def z487 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0x0381c07f0070f1d8 0x200e0701fc01c3c7

def z488 : W := mkw 0x09080408c24c3b52 0x08242010230930ed 0x18013c00c24cfff5 0xd86004f0030933ff

def z489 : W := mkw 0x2001802400000000 0x0080060090000000 0x0001c07f00000010 0x00000701fc000000

def z490 : W := mkw 0x08004480a280ac00 0x00200112028a02b0 0x1c01ff80e380fe37 0xdc7007fe038e03f8

def z491 : W := mkw 0x09084081fbff86c9 0x0024210207effe1b 0x00000000ffff8fe0 0x0c00000003fffe3f

def z492 : W := mkw 0x2001800000000000 0x0080060000000000 0xe001c00000000013 0x8380070000000000

def z493 : W := mkw 0x0050285000000000 0x000140a140000000 0x18783c0000000004 0x5061e0f000000000

def z494 : W := mkw 0x00422143001502c9 0x000108850c00540b 0x00c62047027f8ffc 0x900318811c09fe3f

def z495 : W := mkw 0x08582c50820c2a42 0x082160b1420830a9 0x1b793c78020c0e1d 0xf06de4f1e0083038

def z496 : W := mkw 0xdea4000093000000 0x037a9000024c0000 0xfffe0000ff80002f 0xeffff80003fe0000

def z497 : W := mkw 0x084265c3a295aec9 0x002109970e8a56bb 0x1cc7ffc7e3ffffff 0xdc731fff1f8fffff

def z498 : W := mkw 0x004060c1209586c9 0x000101830482561b 0x0040204023ff8ffc 0x94010081008ffe3f

def z499 : W := mkw 0xf7a7d32f6c70d19c 0x27de9f4cbdb1c346 0xe787c3fffc70f1fb 0xaf9e1f0ffff1c3c7

def z500 : W := mkw 0xfffffb7fff7ad19c 0x27ffffedfffdeb46 0xfffffffffffff1ff 0xffffffffffffffc7

def z501 : W := mkw 0x428000250830008c 0x050a00009420c002 0x0080000700300000 0x000200001c00c000

def z502 : W := mkw 0x42a4000008220000 0x010a900000208800 0x0086000000330000 0x000218000000cc00

def z503 : W := mkw 0x63c3e16f6c70d19c 0x058f0f85bdb1c346 0xe7c7e3fffc70f1ff 0xbf9f1f8ffff1c3c7

def z504 : W := mkw 0x01502c5840443b52 0x080540b1610110ed 0x03013c78c040fff9 0xb80c04f1e30103ff

def z505 : W := mkw 0x4380002d4870119c 0x050e0000b521c046 0xe380007ffc7001eb 0xaf8e0001fff1c007

def z506 : W := mkw 0x295bbf7ec24c3b52 0x28a56efdfb0930ed 0x1b79ffffc24cfffd 0xf86de7ffff0933ff

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000040004081f8 0x8000000100010207

def z508 : W := mkw 0xf6f7bb7600040240 0x23dbdeedd8001009 0xffffffff024c8fff 0xf3fffffffc09323f

def z509 : W := mkw 0x42f62977001502c9 0x210bd8a5dc00540b 0x03fe007f007f01c8 0x200ff801fc01fc07

def z510 : W := mkw 0x094a65cbe2ddbfdb 0x082529972f8b76ff 0x04c6e3c7e3fffffe 0x9c131b8f1f8fffff

def z511 : W := mkw 0x43ee61c368ff86c9 0x010fb9870da3fe1b 0x07fee3c723ff8ffe 0xb41ffb8f1c8ffe3f

def z512 : W := mkw 0xbc01920093000000 0x02f00648024c0000 0xfc01ff80ff800037 0xdff007fe03fe0000

def z513 : W := mkw 0x0000000000000000 0x0000000000000000 0x0486000021b30002 0x041218000086cc00

def z514 : W := mkw 0xf6f7fbf720918489 0x23dbdfefdc824612 0xffffffff21b3001f 0xf7fffffffc86cc00

def z515 : W := mkw 0x09586cd8e2ccbf52 0x082561b3638b32fd 0x1f79fff8e3ccffff 0xfc7de7ffe38f33ff

def z516 : W := mkw 0x2053fb7f2410d19c 0x24814fedfc904346 0x0001ffff0000f1d0 0x100007fffc0003c7

def z517 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe381c03ffc307003 0x2f8e0700fff0c1c0

def z518 : W := mkw 0xffad802cdf6a5114 0x07feb600b37da944 0xffff0038ffff702f 0xeffffc00e3fffdc0

def z519 : W := mkw 0x0000000000000000 0x0000000000000000 0x04c600000000000e 0x8013180000000000

def z520 : W := mkw 0x9c00040093002800 0x02700010024c00a0 0xfc013c00ff80fe37 0xdff004f003fe03f8

def z521 : W := mkw 0xbd59be58c24c3b52 0x0af566f9630930ed 0xff79fff8c24cffff 0xfbfde7ffe30933ff

def z522 : W := mkw 0xffc3f7effff5fffd 0x17ff0fdfbfffd7ff 0xffc7ffffffffffff 0xffff1fffffffffff

def z523 : W := mkw 0xf6b59a3400000000 0x23dad668d0000000 0xfbb9dc7f0000001b 0xe3eee771fc000000

def z524 : W := mkw 0x6281c02d2c30d19c 0x058a0700b4b0c346 0xe081c07f3c30f1d2 0x07820701fcf0c3c7

def z525 : W := mkw 0x2053bb7600000000 0x20814eedd8000000 0x04c7ffff0000001e 0x90131ffffc000000

def z526 : W := mkw 0x94763b5200000000 0x2251d8ed48000000 0x1f7f3ff80000001d 0xf07dfcffe0000000

def z527 : W := mkw 0x01582858404c1352 0x080560a16101304d 0x03790078c04cf1f9 0xa80de401e30133c7

def z528 : W := mkw 0x09084409ee7cfbde 0x0c24211027b9f3ef 0x00000000fe7cffe0 0x0c00000003f9f3ff

def z529 : W := mkw 0xdffc2858db6e1352 0x0b7ff0a1636db84d 0xfffe0078ffff01ef 0xeffff801e3fffc07

def z530 : W := mkw 0x0800040082002800 0x00200010020800a0 0x18011c00c0007001 0x48600470030001c0

def z531 : W := mkw 0x0840244082042a40 0x00210091020810a9 0x18413c40c24cfffd 0xd86104f1030933ff

def z532 : W := mkw 0xd6a4000000000000 0x035a900000000000 0xfffe000023ff002f 0xe7fff800008ffc00

def z533 : W := mkw 0x00406041201482c8 0x000101810480520b 0x00c0e047227c8ffe 0x940303811c89f23f

def z534 : W := mkw 0x2043f7c32495eee9 0x10810fdf0c9257bb 0x0001ffc70000ffd0 0x100007ff1c0003ff

def z535 : W := mkw 0xbd09d680ffeaec20 0x12f4275a03ffabb0 0xfc01ff80fffffe37 0xdff007fe03fffff8

def z536 : W := mkw 0x09482448c24c3b52 0x08252091230930ed 0x00402040c24cfffc 0x98010081030933ff

def z537 : W := mkw 0xbd09d688f7ccff72 0x1af4275a23df33fd 0xfc01ff80ffccfff7 0xdff007fe03ff33ff

def z538 : W := mkw 0xf7f7bb7f4870119c 0x27dfdeedfd21c046 0xffffffff007001df 0xf3fffffffc01c007

def z539 : W := mkw 0x095a6ddbe2ddbfdb 0x082569b76f8b76ff 0x1b79ffffc24cfffd 0xf86de7ffff0933ff

def z540 : W := mkw 0x094a61c3e2dd86c9 0x002529870f8b761b 0x1ffee3c7e3ff8fff 0xfc7ffb8f1f8ffe3f

def z541 : W := mkw 0xb401d2803580c420 0x12d0074a00d60310 0xe401c380fd80f033 0x8f90070e03f603c0

def z542 : W := mkw 0xf6f7fb772c30c08c 0x27dbdfeddcb0c302 0xffffffff3c30001f 0xf7fffffffcf0c000

def z543 : W := mkw 0x00526ddb2095bfdb 0x080149b76c8256ff 0x04c7ffff23fffffe 0x94131ffffc8fffff

def z544 : W := mkw 0xf7ffbb7e404c1352 0x2bdffeedf901304d 0xffffffff004c01df 0xf3fffffffc013007

def z545 : W := mkw 0x43c261ef68f597dd 0x050f0987bda3d65f 0x07c6e3ff23ff8ffe 0xb41f1b8ffc8ffe3f

def z546 : W := mkw 0xf6f7fff62480ec20 0x33dbdfffd89203b0 0xffffffff0000fe1f 0xf3fffffffc0003f8

def z547 : W := mkw 0x004221c200850641 0x0001088708021419 0x0000238000000e00 0x1000008e00000038

def z548 : W := mkw 0xff81d6acffe0fd34 0x17fe075ab3ff83f4 0xff01ffb8ff80fe37 0xfffc07fee3fe03f8

def z549 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0x1ffe000003ff000c 0x607ff800000ffc00

def z550 : W := mkw 0xbc53fff6b780ec20 0x32f14fffdade03b0 0xfc01ffffff80fe37 0xdff007fffffe03f8

def z551 : W := mkw 0x2043e1ef2495d7dd 0x04810f87bc92575f 0x04c7e3ff23fffffe 0x94131f8ffc8fffff

def z552 : W := mkw 0x9c005680b780ec20 0x1270015a02de03b0 0x1c003f80ff80fe24 0x5c7000fe03fe03f8

def z553 : W := mkw 0x0100000840401110 0x0004000021010044 0x03010038c0007001 0x280c0400e30001c0

def z554 : W := mkw 0xff81962cdf607934 0x17fe0658b37d81e4 0xfb011c38dc007001 0x6bec0470e37001c0

def z555 : W := mkw 0x09582858c24c1352 0x082560a16309304d 0x1b780078c24c01ed 0xe86de001e3093007

def z556 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x00c6004723ff8fe8 0x040318011c8ffe3f

def z557 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe080c007fc70f1e2 0x0f8203001ff1c3c7

def z558 : W := mkw 0xffadc000ff6ac000 0x03feb70003fdab00 0xffffc000fffff03f 0xefffff0003ffffc0

def z559 : W := mkw 0x09080000db6a0000 0x00242000036da800 0x1b780000ffff002d 0xec6de00003fffc00

def z560 : W := mkw 0x004221c200850641 0x0001088708021419 0x04c6238023ff0e2e 0x9413188e008ffc38

def z561 : W := mkw 0x4380000048600000 0x010e000001218000 0xe3000000dc000001 0x2b8c000003700000

def z562 : W := mkw 0x2801c400a600e800 0x00a00710029803a0 0xf801fc00fe00fe37 0xdfe007f003f803f8

def z563 : W := mkw 0xd7a4000048600000 0x035e900001218000 0xfffe0000fc70002f 0xeffff80003f1c000

def z564 : W := mkw 0x9400000000000000 0x0250000000000000 0xfc00000000000007 0xc3f0000000000000

def z565 : W := mkw 0x084265c3b795eee9 0x102109970ede57bb 0x04c6e3c7fffffffe 0x9c131b8f1fffffff

def z566 : W := mkw 0x0000000000000000 0x0000000000000000 0x18013c0000000015 0xd06004f000000000

def z567 : W := mkw 0x43ac0000486a0000 0x010eb0000121a800 0xe3fe0000fc7f002b 0xaf8ff80003f1fc00

def z568 : W := mkw 0xf7f7fbff6cf5d7dd 0x27dfdfeffdb3d75f 0xffffffffffffffff 0xffffffffffffffff

def z569 : W := mkw 0x2001800004004000 0x0080060000100100 0xe0010000dc007001 0x0b800400037001c0

def z570 : W := mkw 0x0040204000040240 0x0001008100001009 0x00402000020c0e04 0x1001008000083038

def z571 : W := mkw 0x09080000c2480000 0x0024200003092000 0x1b380000c0000001 0x686ce00003000000

def z572 : W := mkw 0xbc43f7c3b795eee9 0x12f10fdf0ede57bb 0xfc01ffc7ff80fff7 0xdff007ff1ffe03ff

def z573 : W := mkw 0x0000040000002800 0x00000010000000a0 0x00013c000000fe10 0x100004f0000003f8

def z574 : W := mkw 0xfe81d6a4b780ec20 0x13fa075a92de03b0 0xff81ffffff80fe3f 0xfffe07fffffe03f8

def z575 : W := mkw 0x9d582c58d34c3b52 0x0a7560b1634d30ed 0xff793c78ffccffff 0xfffde4f1e3ff33ff

def z576 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xff7f3fb800000005 0x73fdfcfee0000000

def z577 : W := mkw 0xfef7bf7697006820 0x33fbdefdda5c01a0 0xffffffffdc00701f 0xfbffffffff7001c0

def z578 : W := mkw 0xbc59fed0b78cee62 0x1af167fb42de33b9 0xfc79ff80ff8cfe37 0xdff1e7fe03fe33f8

def z579 : W := mkw 0xbd09d680f7c8ec20 0x12f4275a03df23b0 0xff79ff80ffccfe3f 0xfffde7fe03ff33f8

def z580 : W := mkw 0x00004081209586c9 0x000001020482561b 0x0400e38023ff8ff6 0x9410038e008ffe3f

def z581 : W := mkw 0xb401920015004020 0x12d0064800540100 0xe00000001c000000 0x0380000000700000

def z582 : W := mkw 0x09482040c24c0240 0x0025208103093009 0x1b782040c24c8ffd 0xf86de0810309323f

def z583 : W := mkw 0xf7a5c02d7d72d19c 0x07de9700b5f5cb46 0xe787c07ffdf3f1fb 0xaf9e1f01fff7cfc7

def z584 : W := mkw 0x2801d680b780ec20 0x10a0075a02de03b0 0x0001ff80ff80fe30 0x1c0007fe03fe03f8

def z585 : W := mkw 0x00502c5800043b52 0x080140b1600010ed 0x00413c78024cfffc 0x900104f1e00933ff

def z586 : W := mkw 0xf781d2ad7df0d5bc 0x17de074ab5f7c356 0xe781c3fffdf0f1fb 0xaf9e070ffff7c3c7

def z587 : W := mkw 0xb401d2803580c420 0x12d0074a00d60310 0xe400e3803f808e36 0x9790038e00fe0238

def z588 : W := mkw 0x2001d6802480ec20 0x1080075a009203b0 0x0401ff802380fe36 0x941007fe008e03f8

def z589 : W := mkw 0x42a6012600000000 0x210a980498000000 0x0086000700000000 0x000218001c000000

def z590 : W := mkw 0x00024183209586c9 0x000009060c82561b 0x0486c38723ff8fe2 0x04121b0e1c8ffe3f

def z591 : W := mkw 0x6381802c40401110 0x018e0600b1010044 0xe381c07fc040f1fb 0xab8e0701ff0103c7

def z592 : W := mkw 0xf6e7f3e7209586c9 0x23db9fcf9c82561b 0xe4c6e3c723ff8ffe 0x97931b8f1c8ffe3f

def z593 : W := mkw 0x0150285840401110 0x000540a161010044 0x1b793c78c040f1fd 0xf86de4f1e30103c7

def z594 : W := mkw 0x9d080000d3480000 0x02742000034d2000 0xff780000ffcc002f 0xeffde00003ff3000

def z595 : W := mkw 0x6281c0242400c000 0x018a070090900300 0xe381c07ffc00f03b 0xaf8e0701fff003c0

def z596 : W := mkw 0xdfbc0c18db6a3912 0x0b7ef030636da8e4 0xffff1c38ffff702f 0xeffffc70e3fffdc0

def z597 : W := mkw 0xdfac4080fbea8400 0x037eb10203efaa10 0xfffee380ffff8e3f 0xfffffb8e03fffe38

def z598 : W := mkw 0x015a69db60dd97db 0x080569a76d83765f 0x07fee3ff23ff8ffe 0xb41ffb8ffc8ffe3f

def z599 : W := mkw 0x43fc2858486e1352 0x090ff0a16121b84d 0x03fe0078007f01c8 0x200ff801e001fc07

def z600 : W := mkw 0xb477bb7600000000 0x22d1deedd8000000 0x1c7fffff00000014 0x5071fffffc000000

def z601 : W := mkw 0x62c3e1e7209586c9 0x018b0f879c82561b 0xe7c7e3ff23ff8fff 0xb79f1f8ffc8ffe3f

def z602 : W := mkw 0x2001d6802480ec20 0x1080075a009203b0 0xe001ff80fc00fe33 0x9f8007fe03f003f8

def z603 : W := mkw 0xf7b5da3d6c70d19c 0x27ded768f5b1c346 0xfbb9dc7ffc70f1fb 0xefeee771fff1c3c7

def z604 : W := mkw 0xf6a7932600000000 0x23da9e4c98000000 0xfc87ff8700000017 0xd3f21ffe1c000000

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000023ff0020 0x04000000008ffc00

def z606 : W := mkw 0x9c763fd293802c20 0x3271d8ff4a4e00b0 0x1c7e3f8003800e04 0x5071f8fe000e0038

def z607 : W := mkw 0x0000000000000000 0x0000000000000000 0x00400000024c002c 0x8001000000093000

def z608 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfbfe0000dc7f0009 0x6beff8000371fc00

def z609 : W := mkw 0x4bac0000ca6a0000 0x012eb0000329a800 0x1bfe0000c27f002d 0xe86ff8000309fc00

def z610 : W := mkw 0x004261c320918489 0x000109870c824612 0x04c6e3c721b3001e 0x94131b8f1c86cc00

def z611 : W := mkw 0xbc77ffd2b780ec20 0x32f1dfff4ade03b0 0xfc7fff80ff80fe37 0xdff1fffe03fe03f8

def z612 : W := mkw 0x0040204000000000 0x0001008100000000 0x004020400000001c 0x9001008100000000

def z613 : W := mkw 0xf7f7bb7e4c605114 0x27dfdeedf9318144 0xffffffffdc00701f 0xfbffffffff7001c0

def z614 : W := mkw 0xdffc2c58db6e3b52 0x0b7ff0b1636db8ed 0xfb793c78de4cfffd 0xfbede4f1e37933ff

def z615 : W := mkw 0x09084488f7ccff72 0x1824211223df33fd 0x00000000ffccffe0 0x0c00000003ff33ff

def z616 : W := mkw 0xf6f7fbf63580c420 0x33dbdfefd8d60310 0xffffffff3d80001f 0xf7fffffffcf60000

def z617 : W := mkw 0xf7b59a3c4c605114 0x27ded668f1318144 0xfb391c38dc007001 0x6bece470e37001c0

def z618 : W := mkw 0xf7a5c02d6c70d19c 0x07de9700b5b1c346 0xffffc07ffc70f1ff 0xefffff01fff1c3c7

def z619 : W := mkw 0x09080000db6a0000 0x00242000036da800 0x04c60000ffff002e 0x8c13180003fffc00

def z620 : W := mkw 0x2801c480b780ec20 0x10a0071202de03b0 0xe001c000ff80fe33 0x8f80070003fe03f8

def z621 : W := mkw 0x6381d6ad6cf0fdbc 0x158e075ab5b3c3f6 0xe381fffffc70fffb 0xbf8e07fffff1c3ff

def z622 : W := mkw 0x000040092410d19c 0x0400010024904346 0x000000000000f1c0 0x00000000000003c7

def z623 : W := mkw 0x0050285000040240 0x000140a140001009 0x1b793c78024c8ffd 0xf06de4f1e009323f

def z624 : W := mkw 0x000040012c30c08c 0x0400010004b0c302 0x000000003c300000 0x0400000000f0c000

def z625 : W := mkw 0xb401d6803580ec20 0x12d0075a00d603b0 0xe401ff803d80fe12 0x179007fe00f603f8

def z626 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x03780078c24cffe8 0x280de001e30933ff

def z627 : W := mkw 0x004261c220808400 0x0001098708820210 0x04c6e3c723808e3e 0x94131b8f1c8e0238

def z628 : W := mkw 0x09582850c2480000 0x002560a143092000 0x1b793c78c24c003d 0xf86de4f1e3093000

def z629 : W := mkw 0xbc01d681b795eee9 0x12f0075a06de57bb 0xfc01ff80fffffff7 0xdff007fe03ffffff

def z630 : W := mkw 0xb451ba5000000000 0x02d146e940000000 0xff79fff80000001f 0xf3fde7ffe0000000

def z631 : W := mkw 0x6283c1a72cb1c48d 0x058a0f069cb2c712 0xe486c3873db30002 0x07921b0e1cf6cc00

def z632 : W := mkw 0x00000001001502c9 0x000000000400540b 0x00000000007f01c0 0x000000000001fc07

def z633 : W := mkw 0x01582858404c1352 0x080560a16101304d 0x03782078024c8ffc 0xb00de081e009323f

def z634 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe3010038fc70f1e1 0x2f8c0400e3f1c3c7

def z635 : W := mkw 0xdea400009b220000 0x037a9000026c8800 0xfc860000ffb30027 0xcff2180003fecc00

def z636 : W := mkw 0x015a295b405d13db 0x080568a56d01744f 0x03fe007f007f01c8 0x200ff801fc01fc07

def z637 : W := mkw 0xbd199e18d7487932 0x1af46678635d21e4 0xfb391c38dc007001 0x6bece470e37001c0

def z638 : W := mkw 0x4380000848601110 0x010e000021218044 0xe3810078fc70f1fb 0xaf8e0401e3f1c3c7

def z639 : W := mkw 0xd6a4000019220000 0x035a900000648800 0xe00000001c000000 0x0380000000700000

def z640 : W := mkw 0xf6b59a3400000000 0x23dad668d0000000 0xff39ffb800000017 0xf3fce7fee0000000

def z641 : W := mkw 0x6381802c4c605114 0x058e0600b1318144 0xe381c07fdc00701b 0xab8e0701ff7001c0

def z642 : W := mkw 0x0800040082002800 0x00200010020800a0 0x18003c0002000e04 0x506000f000080038

def z643 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x0486e3c721b38fd2 0x14121b8f1c86ce3f

def z644 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xf8011c00ff80fe21 0x4fe0047003fe03f8

def z645 : W := mkw 0x0000168000802c20 0x1000005a000200b0 0x00003f8000000e00 0x100000fe00000038

def z646 : W := mkw 0x43fe2976486a0000 0x210ff8a5d921a800 0x03fe007f007f0008 0x200ff801fc01fc00

def z647 : W := mkw 0x01080008404c1352 0x080420002101304d 0x00000000004c01c0 0x0000000000013007

def z648 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x04c6e3c700008fde 0x90131b8f1c00023f

def z649 : W := mkw 0x438040096c70d19c 0x050e010025b1c346 0xe3800000fc70f1eb 0xaf8e000003f1c3c7

def z650 : W := mkw 0x0000040800043b52 0x08000010200010ed 0x000000000000ffc0 0x00000000000003ff

def z651 : W := mkw 0xfef7bb7693000000 0x23fbdeedda4c0000 0xffffffffff80003f 0xfffffffffffe0000

def z652 : W := mkw 0x2001c0802480c400 0x0080070200920310 0xe401e380ff80fe37 0x9f90078e03fe03f8

def z653 : W := mkw 0xbd59be58d74c7b72 0x1af566f9635d31ed 0xfb793c78de4cfffd 0xfbede4f1e37933ff

def z654 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xff7e0000df8f0005 0x6bfdf800037e3c00

def z655 : W := mkw 0x94341a1000000000 0x2250d06840000000 0x18381c0000000000 0x4060e07000000000

def z656 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xe400c380ff80fe22 0x0f90030e03fe03f8

def z657 : W := mkw 0xdfec2040db6e0240 0x037fb081036db809 0xfffe2040ffff8fff 0xfffff88103fffe3f

def z658 : W := mkw 0x6bdbedffeefdffdf 0x0daf6fb7ffbbf7ff 0xffffffffffffffff 0xffffffffffffffff

def z659 : W := mkw 0xffeff7c3ffffeee9 0x13ffbfdf0fffffbb 0xffffffc7ffffffff 0xffffffff1fffffff

def z660 : W := mkw 0xfea5d680bfa2ec20 0x13fa975a02fe8bb0 0xfc87ff80ffb3fe37 0xdff21ffe03fecff8

def z661 : W := mkw 0x2959ec58e64cfb52 0x08a567b1639933ed 0xfb79fc78fe4cffff 0xffede7f1e3f933ff

def z662 : W := mkw 0xff81d680ffe0ec20 0x13fe075a03ff83b0 0xff81ff80fff0fe3f 0xfffe07fe03ffc3f8

def z663 : W := mkw 0xd6a4000019220000 0x035a900000648800 0xe4c600003fff002e 0x8793180000fffc00

def z664 : W := mkw 0x0800048093802c20 0x10200012024e00b0 0x0000000003800e00 0x00000000000e0038

def z665 : W := mkw 0x9c00160093002820 0x12700058024c00a0 0x18001c0000000000 0x4060007000000000

def z666 : W := mkw 0x9c583ed0938c2e62 0x1a7160fb424e30b9 0x1c783f80038c0e04 0x5071e0fe000e3038

def z667 : W := mkw 0x6281c0252c30c08c 0x058a070094b0c302 0xe081c007fc30f033 0x8f8207001ff0c3c0

def z668 : W := mkw 0xd6a4000000000000 0x035a900000000000 0xe486000000000002 0x0392180000000000

def z669 : W := mkw 0x6b89c42dee7cfbde 0x0dae2710b7b9f3ef 0xe381c07ffe7cfffb 0xaf8e0701fff9f3ff

def z670 : W := mkw 0x4380000048600000 0x010e000001218000 0x0380000000700008 0x200e00000001c000

def z671 : W := mkw 0x9c7e3f52820c2a42 0x2a71f8fd4a0830a9 0x1c7e3f80020c0e04 0x5071f8fe00083038

def z672 : W := mkw 0x9c005680b380ac20 0x1270015a02ce02b0 0x1c00ff8023808e36 0xd47003fe008e0238

def z673 : W := mkw 0x0042214200000000 0x0001088508000000 0x00c6004700000008 0x000318011c000000

def z674 : W := mkw 0x0002418320918489 0x000009060c824612 0x0486c3c721f381fa 0x84121b0f1c87ce07

def z675 : W := mkw 0x2001c0252410c08c 0x0480070094904302 0x0000c00700000000 0x000003001c000000

def z676 : W := mkw 0x014261cb6cf5d7dd 0x040509872db3d75f 0x04c6e3c7fffffffe 0x9c131b8f1fffffff

def z677 : W := mkw 0xdfac4480ffeaec20 0x137eb11203ffabb0 0xfffe0000fffffe2f 0xeffff80003fffff8

def z678 : W := mkw 0xd6a4000000000000 0x035a900000000000 0xfb38000000000001 0x63ece00000000000

def z679 : W := mkw 0x43fe297e404c1352 0x290ff8a5f901304d 0x03fe007f004c01c8 0x200ff801fc013007

def z680 : W := mkw 0x08004480b780ec20 0x1020011202de03b0 0x18013c00ff80fe35 0xdc6004f003fe03f8

def z681 : W := mkw 0x62c3a16600000000 0x018b0e8598000000 0xe7c7e3ff0000001f 0xb39f1f8ffc000000

def z682 : W := mkw 0x9400128011800420 0x1250004a00460010 0x0400038001800000 0x0010000e00060000

def z683 : W := mkw 0xfffffff6ffeaec20 0x33ffffffdbffabb0 0xfffffffffffffe3f 0xfffffffffffffff8

def z684 : W := mkw 0x9426130200000000 0x2250984c08000000 0x0406038000000000 0x0010180e00000000

def z685 : W := mkw 0x0000400120108088 0x0000010004804202 0x0000c047000081d0 0x000003011c000207

def z686 : W := mkw 0x08502c5082002800 0x002140b1420800a0 0x1b793c78c200fe3d 0xf86de4f1e30803f8

def z687 : W := mkw 0xf6e7b36600000000 0x23db9ecd98000000 0xe4c6e3c70000001e 0x93931b8f1c000000

def z688 : W := mkw 0xbc01960097006820 0x12f00658025c01a0 0xfc01ff80dc007017 0xdbf007fe037001c0

def z689 : W := mkw 0x6381802448600000 0x018e060091218000 0xe381c07ffc70003b 0xaf8e0701fff1c000

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400e38000000016 0x9010038e00000000

def z691 : W := mkw 0xd6a6418339b38489 0x035a99060ce6ce12 0xe486c3873db30002 0x07921b0e1cf6cc00

def z692 : W := mkw 0x2043f7c32495eee9 0x10810fdf0c9257bb 0x04c7ffc723fffffe 0x94131fff1c8fffff

def z693 : W := mkw 0xdffe2976db6a0000 0x237ff8a5db6da800 0xfffe007fffff002f 0xeffff801fffffc00

def z694 : W := mkw 0xffadd680ffeaec20 0x13feb75a03ffabb0 0xff39ff80ff80fe37 0xfffce7fe03fe03f8

def z695 : W := mkw 0xfeffbf76820c2a42 0x2bfbfefdda0830a9 0xffffffff020c0e1f 0xf3fffffffc083038

def z696 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xffbe0000fdb30003 0x6ffef80003f6cc00

def z697 : W := mkw 0xfffdbe7cc24c3b52 0x2bfff6f9f30930ed 0xfb793c78c24cfffd 0xfbede4f1e30933ff

def z698 : W := mkw 0xf6a7932600000000 0x23da9e4c98000000 0xe787c3ff0000001b 0xa39e1f0ffc000000

def z699 : W := mkw 0x62c3e1e72cb5c6cd 0x058b0f879cb2d71b 0xe4c6e3c73fff8ffe 0x97931b8f1cfffe3f

def z700 : W := mkw 0x4280000008200000 0x010a000000208000 0xe08000003c300002 0x0782000000f0c000

def z701 : W := mkw 0x0000400120108088 0x0000010004804202 0x04c6c04723ff81fe 0x84131b011c8ffe07

def z702 : W := mkw 0xffad9600df6a6820 0x13feb658037da9a0 0xfb391c00dc007001 0x6bece470037001c0

def z703 : W := mkw 0xbd19de98f7c8fd32 0x1af4677a63df23f4 0xff39ffb8ff80fe37 0xfffce7fee3fe03f8

def z704 : W := mkw 0x42f6297600000000 0x210bd8a5d8000000 0x1bff3c7f0000001d 0xf06ffcf1fc000000

def z705 : W := mkw 0x43ac002d487a119c 0x050eb000b521e846 0x03fe007f007f01c8 0x200ff801fc01fc07

def z706 : W := mkw 0xdffc2c58c24c3b52 0x0b7ff0b1630930ed 0xffff3c78c24cffff 0xfbfffcf1e30933ff

def z707 : W := mkw 0x2801c480a680ec00 0x00a00712029a03b0 0xfc01ff80ff80fe37 0xdff007fe03fe03f8

def z708 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x07c7e3ff23ff8fff 0xb41f1f8ffc8ffe3f

def z709 : W := mkw 0xbc09d680b788ec20 0x12f0275a02de23b0 0xfc79ff80ff8cfe37 0xdff1e7fe03fe33f8

def z710 : W := mkw 0xbc2dc02db71ad19c 0x06f0b700b6dc6b46 0x1c7fc07f038ff1d4 0x4071ff01fc0e3fc7

def z711 : W := mkw 0x4af66df6b780ec20 0x312bd9b7dade03b0 0x03fe007fff80fe28 0x2c0ff801fffe03f8

def z712 : W := mkw 0x63adc02d6c7ad19c 0x058eb700b5b1eb46 0xe7ffc07ffffff1ff 0xaf9fff01ffffffc7

def z713 : W := mkw 0x6ad9ec75ae3ceace 0x0dab67b1d6b8f3ab 0xf8f8fc073e3c0e06 0x57e3e3f01cf8f038

def z714 : W := mkw 0x6381c02c6440d110 0x018e0700b1910344 0xe381c07ffc40f1fb 0xaf8e0701fff103c7

def z715 : W := mkw 0xf6f7bb760c204004 0x27dbdeedd8308100 0xffffffff1c00001f 0xf3fffffffc700000

def z716 : W := mkw 0x4380402d6c70d19c 0x050e0100b5b1c346 0xe380007ffc70f1eb 0xaf8e0001fff1c3c7

def z717 : W := mkw 0xbc01968097806c20 0x12f0065a025e01b0 0xfc013f80df80fe35 0xdbf004fe037e03f8

def z718 : W := mkw 0xffaf972ec24c3b52 0x2bfebe5cbb0930ed 0xe486c387c24cffe2 0x0b921b0e1f0933ff

def z719 : W := mkw 0xbc01d681b791eca9 0x12f0075a06de47b2 0xfc01ff80ffb3fe37 0xdff007fe03fecff8

def z720 : W := mkw 0x005269d3209586c9 0x000149a74c82561b 0x04c7ffff23ff8ffe 0x94131ffffc8ffe3f

def z721 : W := mkw 0x63add6806ceaec20 0x118eb75a01b3abb0 0x03ffff80007ffe18 0x300ffffe0001fff8

def z722 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe3c1c07ffe7cf1ff 0xaf8f0701fff9f3c7

def z723 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc87ff80ffb3fe37 0xdff21ffe03fecff8

def z724 : W := mkw 0xd7ac0000596a0000 0x035eb0000165a800 0xe7fe00003fff002e 0xa79ff80000fffc00

def z725 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b793c38c24cffe5 0x786de4f0e30933ff

def z726 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffffffff2380003f 0xf7fffffffc8e0000

def z727 : W := mkw 0xdea4000093000000 0x037a9000024c0000 0xfffe0000ffff002f 0xeffff80003fffc00

def z728 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x04c6c3c723ff8fea 0x04131b0f1c8ffe3f

def z729 : W := mkw 0xdfac0408db6a3910 0x037eb010236da8e4 0xffff3c78ffffffff 0xfffffcf1e3ffffff

def z730 : W := mkw 0x0150285840441350 0x000540a16101104d 0x1b793c78c24cfffd 0xf86de4f1e30933ff

def z731 : W := mkw 0xbc43b74397156ae9 0x12f10edd0e5c55ab 0xf8c71c47dc7f71c9 0x4be31c711f71fdc7

def z732 : W := mkw 0xdeac00009b2a0000 0x037ab000026ca800 0xfcfe0000ffbf0027 0xcff3f80003fefc00

def z733 : W := mkw 0xf6b79b3600000000 0x23dade6cd8000000 0xfb39dfbf00000001 0x63ece77efc000000

def z734 : W := mkw 0xd6f42c5819263b52 0x0b5bd0b1606498ed 0xe4873c783db3ffd2 0x17921cf1e0f6cfff

def z735 : W := mkw 0x00502c5800043b52 0x080140b1600010ed 0x1b793c78024cfffd 0xf06de4f1e00933ff

def z736 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xffff0078ffff003f 0xeffffc01e3fffc00

def z737 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfcfe0000ffff0026 0x4ff3f80003fffc00

def z738 : W := mkw 0x004221c3009506c9 0x000108870c02541b 0x04c6e3c703ff0fde 0x90131b8f1c0ffc3f

def z739 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe301c07ffc70f1f1 0x2f8c0701fff1c3c7

def z740 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc47ff80ff8ffe37 0xdff11ffe03fe3ff8

def z741 : W := mkw 0xf6a5d2a53db2c4ac 0x17da974a94f6cb12 0xe486c3873db30002 0x07921b0e1cf6cc00

def z742 : W := mkw 0xdeac00009b2a0000 0x037ab000026ca800 0xfcfe00003fff002e 0xc7f3f80000fffc00

def z743 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfbfe0000ffff0029 0x6feff80003fffc00

def z744 : W := mkw 0x09180c18c24c3b52 0x08246030630930ed 0x1b391c38c000ffc1 0x686ce470e30003ff

def z745 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xe401ff80ff80fe32 0x1f9007fe03fe03f8

def z746 : W := mkw 0x091a4d9be2d9bd9b 0x082469366f8b66f6 0x1fbfdfbfe1b37003 0x6c7eff7eff86cdc0

def z747 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc01ff80df80fe15 0x5bf007fe037e03f8

def z748 : W := mkw 0xd7a4000048600000 0x035e900001218000 0xfffe0000ffff002f 0xeffff80003fffc00

def z749 : W := mkw 0x6281c0252410c088 0x018a070094904302 0xe381c07ffc70f1fb 0xaf8e0701fff1c3c7

def z750 : W := mkw 0x00024183209586c9 0x000009060c82561b 0x0486e38723ff8ff6 0x94121b8e1c8ffe3f

def z751 : W := mkw 0x6381802d4c70519c 0x058e0600b531c146 0xe381c07fdc7071db 0xab8e0701ff71c1c7

def z752 : W := mkw 0xdfac0024db6a0000 0x037eb000936da800 0xfffe007fffff002f 0xeffff801fffffc00

def z753 : W := mkw 0x9c005680b780ec20 0x1270015a02de03b0 0xfc003f80ff80fe27 0xdff000fe03fe03f8

def z754 : W := mkw 0x43ac0000486a0000 0x010eb0000121a800 0xe7fe0000ffff002f 0xaf9ff80003fffc00

def z755 : W := mkw 0xbc01d6a4b780ec20 0x12f0075a92de03b0 0xfc01ffffff80fe37 0xdff007fffffe03f8

def z756 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xe7fe0000ffff002a 0x2f9ff80003fffc00

def z757 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xff79ff80ff80fe3f 0xfffde7fe03fe03f8

def z758 : W := mkw 0x4b880000ca680000 0x012e20000329a000 0xfffe0000ffff002f 0xeffff80003fffc00

def z759 : W := mkw 0xf6f7bb7619220000 0x23dbdeedd8648800 0xffffffff3fff003f 0xf7fffffffcfffc00

def z760 : W := mkw 0xf6b5dab5209586c9 0x23dad76ad482561b 0xfb391c3823ff8fe1 0x67ece470e08ffe3f

def z761 : W := mkw 0x005068d1209586c9 0x000141a34482561b 0x1b793c7823ff8ffd 0xf46de4f1e08ffe3f

def z762 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x1cc7ffc723ff8fff 0xd4731fff1c8ffe3f

def z763 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe380c07ffc70f1ea 0x2f8e0301fff1c3c7

def z764 : W := mkw 0x09582c58ca6c3b52 0x082560b16329b0ed 0x1b793c78fe7cfffd 0xfc6de4f1e3f9f3ff

def z765 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b791c78c24cffe9 0x686de471e30933ff

def z766 : W := mkw 0x005269d3209586c9 0x000149a74c82561b 0x07fee3ff23ff8ffe 0xb41ffb8ffc8ffe3f

def z767 : W := mkw 0xb559fad875ccd772 0x1ad567eb61d7335d 0xe778c3f83dcc01ca 0x279de30fe0f73007

def z768 : W := mkw 0xffad962cdf6a7934 0x17feb658b37da9e4 0xfb391c38dc007001 0x6bece470e37001c0

def z769 : W := mkw 0x6389c02d6c7ad19c 0x058e2700b5b1eb46 0xe381c07ffc7ff1fb 0xaf8e0701fff1ffc7

def z770 : W := mkw 0xbc2dd680b78aec20 0x12f0b75a02de2bb0 0xfc39ff80ff80fe37 0xdff0e7fe03fe03f8

def z771 : W := mkw 0x95767b5b6c70d19c 0x2655d9ed6db1c346 0x1c7e3f80fc70f1e4 0x5c71f8fe03f1c3c7

def z772 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffffffff02008e3f 0xf3fffffffc080238

def z773 : W := mkw 0x2053bb7600000000 0x20814eedd8000000 0x1b39ffff00000011 0x706ce7fffc000000

def z774 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x04c6e38723ff8fe6 0x14131b8e1c8ffe3f

def z775 : W := mkw 0x09080408c2483910 0x00242010230920e4 0x1b793c78c24cfffd 0xf86de4f1e30933ff

def z776 : W := mkw 0x9c2c0000930a0000 0x0270b000024c2800 0xfcfe0000ffff002f 0xcff3f80003fffc00

def z777 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffffffff007f001f 0xf3fffffffc01fc00

def z778 : W := mkw 0xdfee61c3fbff86c9 0x037fb9870feffe1b 0xfb38e3c7dc008fd1 0x7bece38f1f70023f

def z779 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0xfb793c78fe4cffff 0xffede4f1e3f933ff

def z780 : W := mkw 0xd7ac0000596a0000 0x035eb0000165a800 0xe7fe0000fdff002b 0xaf9ff80003f7fc00

def z781 : W := mkw 0x2053fbff2495d7dd 0x24814feffc92575f 0x0001ffff0000ffd0 0x100007fffc0003ff

def z782 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe781c07ffff0f1ff 0xaf9e0701ffffc3c7

def z783 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b793c78c000ffdd 0xf86de4f1e30003ff

def z784 : W := mkw 0x6381c0ad6cf0d59c 0x058e0702b5b3c356 0xe7c7e3ffffffffff 0xbf9f1f8fffffffff

def z785 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfffe0040ffff81ff 0xeffff80103fffe07

def z786 : W := mkw 0x43da297f487d13df 0x0d0f68a5fd21f44f 0x03fe007f007f01c8 0x200ff801fc01fc07

def z787 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xfbb9ffff0000001b 0xf3eee7fffc000000

def z788 : W := mkw 0x6281c02d2410d19c 0x058a0700b4904346 0xe381c07ffc00f1fb 0xaf8e0701fff003c7

def z789 : W := mkw 0xb453bb5200000000 0x02d14eed48000000 0xffffffff0000001f 0xf3fffffffc000000

def z790 : W := mkw 0x9c7e2dd2938f2e43 0x0a71f8b74a4e3cb9 0x1c7e3f80038f0e04 0x5071f8fe000e3c38

def z791 : W := mkw 0x6381c0ad6cf1d59d 0x058e0702b5b3c756 0xe381c07ffdf3f1fb 0xaf8e0701fff7cfc7

def z792 : W := mkw 0x6381802d4c70519c 0x058e0600b531c146 0xe381007ffc7071eb 0xaf8e0401fff1c1c7

def z793 : W := mkw 0x2001c02d2410d19c 0x04800700b4904346 0xe001c07fdc00f1d1 0x0b800701ff7003c7

def z794 : W := mkw 0x09180c18c24c3b52 0x08246030630930ed 0x1b791c38c24cffed 0xe86de470e30933ff

def z795 : W := mkw 0x0042214200040240 0x0001088508001009 0x04c6e3c723ff8ffe 0x94131b8f1c8ffe3f

def z796 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe381c07ffc7071cb 0x2f8e0701fff1c1c7

def z797 : W := mkw 0x63c3a1ee4ce55755 0x058f0e87b933955d 0xe74723b8df8f7e05 0x3b9d1c8ee37e3df8

def z798 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffffffff038f001f 0xf3fffffffc0e3c00

def z799 : W := mkw 0x4380002d4870119c 0x050e0000b521c046 0xe381007ffc70f1fb 0xaf8e0401fff1c3c7

def z800 : W := mkw 0x62d3a97600000000 0x018b4ea5d8000000 0xffffffff0000001f 0xf3fffffffc000000

def z801 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe787c07ffdf3f1fb 0xaf9e1f01fff7cfc7

def z802 : W := mkw 0x095a2d5ac24c3b52 0x082568b56b0930ed 0x1f7f3ff8c24cfffd 0xf87dfcffe30933ff

def z803 : W := mkw 0x09582c58d34e3b52 0x082560b1634d38ed 0x1b793c78c3cffffd 0xf86de4f1e30f3fff

def z804 : W := mkw 0x295bbb76db6a0000 0x20a56eeddb6da800 0x0001ffffffff0030 0x1c0007fffffffc00

def z805 : W := mkw 0xdfac0408db6a3912 0x0b7eb010236da8e4 0xfffe0000ffff702f 0xeffff80003fffdc0

def z806 : W := mkw 0x09084489f7ddfffb 0x1824211227df77ff 0x00000000ffffffe0 0x0c00000003ffffff

def z807 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b793c78c20cffd5 0x786de4f1e30833ff

def z808 : W := mkw 0xbc01968097806c20 0x12f0065a025e01b0 0xfc013f80ff807e27 0xdff004fe03fe01f8

def z809 : W := mkw 0x6381c0ad6cf0d59c 0x058e0702b5b3c356 0xe381c07ffff0fffb 0xaf8e0701ffffc3ff

def z810 : W := mkw 0xbc25d680b780ec20 0x12f0975a02de03b0 0xfc7fff80ff80fe37 0xdff1fffe03fe03f8

def z811 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfffe0000ffbf0007 0x6ffff80003fefc00

def z812 : W := mkw 0xf6b79b3600000000 0x23dade6cd8000000 0xffffdfbf0000000f 0xe3ffff7efc000000

def z813 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xff39ffff00000017 0xf3fce7fffc000000

def z814 : W := mkw 0xf6a7d3a73591c4a9 0x33da9f4e9cd64712 0xe486c3873db30002 0x07921b0e1cf6cc00

def z815 : W := mkw 0xb453bb7600000000 0x22d14eedd8000000 0xff79ffff0000001f 0xf3fde7fffc000000

def z816 : W := mkw 0x2001d6802480ec20 0x1080075a009203b0 0xe001ff80dc00fe11 0x1b8007fe037003f8

def z817 : W := mkw 0x00502c5800043b52 0x080140b1600010ed 0x1b393c780000ffd1 0x706ce4f1e00003ff

def z818 : W := mkw 0xf6f7bb7608200000 0x23dbdeedd8208000 0xffffffff3c30001f 0xf7fffffffcf0c000

def z819 : W := mkw 0x09084489fffafdbc 0x1424211227ffebf6 0x00000000ffffffe0 0x0c00000003ffffff

def z820 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe781e3fffc70f1ff 0xbf9e078ffff1c3c7

def z821 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe381c07fdc00f1db 0xab8e0701ff7003c7

def z822 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xffff0000fffff03f 0xeffffc0003ffffc0

def z823 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xfffeffff0000000e 0x73fffbfffc000000

def z824 : W := mkw 0x42f6297600000000 0x210bd8a5d8000000 0x1fffffff0000001f 0xf07ffffffc000000

def z825 : W := mkw 0x6381802d4c70519c 0x058e0600b531c146 0xe381007fdc70f1f9 0xab8e0401ff71c3c7

def z826 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xfffffffffc00003f 0xfffffffffff00000

def z827 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xf801ff80fc00fe33 0xdfe007fe03f003f8

def z828 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfffe00003fff000e 0x67fff80000fffc00

def z829 : W := mkw 0x62d3bb7600000000 0x218b4eedd8000000 0xfbf9ffff0000001f 0xf3efe7fffc000000

def z830 : W := mkw 0x9c763fd293852e61 0x3271d8ff4a4e14b9 0x1c7e3f80038f0e04 0x5071f8fe000e3c38

def z831 : W := mkw 0x43fe297f487c13de 0x2d0ff8a5fd21f04f 0x03fe007f007c01c8 0x200ff801fc01f007

def z832 : W := mkw 0xf6f7bb7608220000 0x23dbdeedd8208800 0xffffffff0033001f 0xf3fffffffc00cc00

def z833 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x1ffee3c723ff8fff 0xf47ffb8f1c8ffe3f

def z834 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffbfffff00000013 0x73fefffffc000000

def z835 : W := mkw 0xf6f7bb7619220000 0x23dbdeedd8648800 0xffffffff1c00001f 0xf3fffffffc700000

def z836 : W := mkw 0xb401d2802480c400 0x02d0074a00920310 0xfc01ff80ff80fe37 0xdff007fe03fe03f8

def z837 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1f793c78e3ccffff 0xfc7de4f1e38f33ff

def z838 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xfbffffff00000019 0x73effffffc000000

def z839 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b393c78c200fff5 0xf86ce4f1e30803ff

def z840 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe381c07ffffff1fb 0xaf8e0701ffffffc7

def z841 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xffff3c00ffff003f 0xfffffcf003fffc00

def z842 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b793c78c04cffd9 0x786de4f1e30133ff

def z843 : W := mkw 0x6381c0ad6cf0d59c 0x058e0702b5b3c356 0xe381e3fffc70fffb 0xbf8e078ffff1c3ff

def z844 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc01ff80ff807e07 0x5ff007fe03fe01f8

def z845 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0x1fffffff0000001c 0x707ffffffc000000

def z846 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe301c07fdc40f1f9 0xab8c0701ff7103c7

def z847 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1bf93c78e27cffff 0xfc6fe4f1e389f3ff

def z848 : W := mkw 0x095a2d5ac24d3b53 0x082568b56b0934ed 0x1b7f3c78c24ffffd 0xf86dfcf1e3093fff

def z849 : W := mkw 0x005269d3209586c9 0x000149a74c82561b 0x1cfeffc723ff8ffe 0xd473fbff1c8ffe3f

def z850 : W := mkw 0x62f7bb7600000000 0x218bdeedd8000000 0x1bffffff0000001d 0xf06ffffffc000000

def z851 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b793c78024cffdc 0x706de4f1e00933ff

def z852 : W := mkw 0x2801d680b780ec20 0x10a0075a02de03b0 0xe001ff80ff80fe33 0x9f8007fe03fe03f8

def z853 : W := mkw 0xd6a4000019220000 0x035a900000648800 0xfffe00003fff002f 0xe7fff80000fffc00

def z854 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xff7fffff00000015 0x73fdfffffc000000

def z855 : W := mkw 0x09582c58db6e3b52 0x082560b1636db8ed 0x1b793c78de4cfffd 0xf86de4f1e37933ff

def z856 : W := mkw 0x094a254ac24c3b52 0x082528952b0930ed 0x04c6e3c7c24cfffe 0x98131b8f1f0933ff

def z857 : W := mkw 0xdfac0400db6a2800 0x037eb010036da8a0 0xfffe0000fffffe2f 0xeffff80003fffff8

def z858 : W := mkw 0xbc09d680b78aec20 0x12f0275a02de2bb0 0xfc01ff80ff8ffe37 0xdff007fe03fe3ff8

def z859 : W := mkw 0xbc01960097006820 0x12f00658025c01a0 0xfc01ff80de00fe37 0xdbf007fe037803f8

def z860 : W := mkw 0xdfac1200db6a0000 0x037eb048036da800 0xfffe3f80ffff002f 0xfffff8fe03fffc00

def z861 : W := mkw 0x9d080000d3480000 0x02742000034d2000 0xfffe0000ffff002f 0xeffff80003fffc00

def z862 : W := mkw 0x095a2d5ac24c3b52 0x082568b56b0930ed 0x1b79ffffc24cfffd 0xf86de7ffff0933ff

def z863 : W := mkw 0xd7ac0000596a0000 0x035eb0000165a800 0xfffe00003dff000f 0xe7fff80000f7fc00

def z864 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe381c07ffc30f1d3 0x2f8e0701fff0c3c7

def z865 : W := mkw 0xbc01d681b790eca8 0x12f0075a06de43b2 0xfc01ff80fff0fff7 0xdff007fe03ffc3ff

def z866 : W := mkw 0xffbd9e3cdb6a3912 0x2bfef678f36da8e4 0xfb391c38dc007001 0x6bece470e37001c0

def z867 : W := mkw 0xbc01d681b790eca8 0x12f0075a06de43b2 0xfcc7ffc7ffffffff 0xdff31fff1fffffff

def z868 : W := mkw 0x09084489e2ddbfdb 0x08242112278b76ff 0x00000000c24cffe0 0x08000000030933ff

def z869 : W := mkw 0xdfac0008db6a1110 0x037eb000236da844 0xfffe0000fffff1ef 0xeffff80003ffffc7

def z870 : W := mkw 0xdfac0400db6a2800 0x037eb010036da8a0 0xfffe3c00ffff0e2f 0xfffff8f003fffc38

def z871 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xfb81fc7ffc70f1ff 0xffee07f1fff1c3c7

def z872 : W := mkw 0x6281c02d2c30d19c 0x058a0700b4b0c346 0xe081c07ffc30f1f3 0x8f820701fff0c3c7

def z873 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc81ff80fff0fe3f 0xdff207fe03ffc3f8

def z874 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffffffff2070003f 0xf7fffffffc81c000

def z875 : W := mkw 0x6381d22d6c70d19c 0x058e0748b5b1c346 0xe381fffffc70f1fb 0xbf8e07fffff1c3c7

def z876 : W := mkw 0x09084489fbffbfdb 0x0824211227effeff 0x00000000ffffffe0 0x0c00000003ffffff

def z877 : W := mkw 0x6381d2ad6cf0d5bc 0x158e074ab5b3c356 0xe381c3fffc70f1fb 0xaf8e070ffff1c3c7

def z878 : W := mkw 0x09582c58d34c3b52 0x082560b1634d30ed 0x1b793c78ffccfffd 0xfc6de4f1e3ff33ff

def z879 : W := mkw 0x2053fff72495eee9 0x30814fffdc9257bb 0x0001ffff0000ffd0 0x100007fffc0003ff

def z880 : W := mkw 0x2801d680a680ec20 0x10a0075a029a03b0 0xf801ff80fe00fe37 0xdfe007fe03f803f8

def z881 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe081c07ffc70f1f2 0x0f820701fff1c3c7

def z882 : W := mkw 0xdf8016addbf03dbc 0x177e005ab76fc0f6 0x1f803fff03f00fcc 0x707e00fffc0fc03f

def z883 : W := mkw 0x09582c58ca6e3b52 0x082560b16329b8ed 0x1b793c78c27ffffd 0xf86de4f1e309ffff

def z884 : W := mkw 0xf6f7bb7600040240 0x23dbdeedd8001009 0xffffffff00008fdf 0xf3fffffffc00023f

def z885 : W := mkw 0xbc01d600a600e800 0x02f00758029803a0 0xfc01ff80fe00fe37 0xdff007fe03f803f8

def z886 : W := mkw 0x9c00168093802c20 0x1270005a024e00b0 0xfc013f80ff80fe37 0xdff004fe03fe03f8

def z887 : W := mkw 0xbc01960093002800 0x02f00658024c00a0 0xfc01ff80ff80fe37 0xdff007fe03fe03f8

def z888 : W := mkw 0x63a5c02d6c70d19c 0x058e9700b5b1c346 0xe3ffc07ffc70f1fb 0xaf8fff01fff1c3c7

def z889 : W := mkw 0xf6d1ba7400000000 0x03db46e9d0000000 0xfff9ffff0000001f 0xf3ffe7fffc000000

def z890 : W := mkw 0xb477bb7600000000 0x22d1deedd8000000 0x1f7fffff0000001d 0xf07dfffffc000000

def z891 : W := mkw 0x63a5c02d6c72d19c 0x058e9700b5b1cb46 0xe387c07ffc73f1fb 0xaf8e1f01fff1cfc7

def z892 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffffdfff0000000b 0x63ffff7ffc000000

def z893 : W := mkw 0x43f6297f487513dd 0x250fd8a5fd21d44f 0x03fe007f007f01c8 0x200ff801fc01fc07

def z894 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1f79fff8c24cffff 0xf87de7ffe30933ff

def z895 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe381007ffc70f1e9 0x2f8e0401fff1c3c7

def z896 : W := mkw 0x01582c58404c3b52 0x080560b1610130ed 0x1b793c78004cffdd 0xf06de4f1e00133ff

def z897 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc41ff80ffccfe3f 0xdff107fe03ff33f8

def z898 : W := mkw 0xf6f7bb7604004000 0x23dbdeedd8100100 0xffffffffdc00701f 0xfbffffffff7001c0

def z899 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b393c78c24cfff1 0x786ce4f1e30933ff

def z900 : W := mkw 0xdfac0400db6a2800 0x037eb010036da8a0 0xffff1c00ffff702f 0xeffffc7003fffdc0

def z901 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x0486e3c723ff8ff2 0x14121b8f1c8ffe3f

def z902 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0xe4c6e3c7ffff8fff 0x9f931b8f1ffffe3f

def z903 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffffffbf00000007 0x73fffffefc000000

def z904 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b793c78e3fffffd 0xfc6de4f1e38fffff

def z905 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe301c07ffc00f1f3 0xaf8c0701fff003c7

def z906 : W := mkw 0x4380400968709198 0x010e010025a1c246 0xe381c07ffc70f1fb 0xaf8e0701fff1c3c7

def z907 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xff7e0000ffff0025 0x6ffdf80003fffc00

def z908 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe3c7c07ffc7ff1fb 0xaf8f1f01fff1ffc7

def z909 : W := mkw 0x0000408120908488 0x0000010204824212 0x04c6e3c723ff8ffe 0x94131b8f1c8ffe3f

def z910 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfffe0000fdff000b 0x6ffff80003f7fc00

def z911 : W := mkw 0x9c5a3fd2938d2e63 0x1a7168ff4a4e34b9 0x1c7e3f80038f0e04 0x5071f8fe000e3c38

def z912 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xf801ff80ff80fe31 0x5fe007fe03fe03f8

def z913 : W := mkw 0x00024183209586c9 0x000009060c82561b 0x04c6c38723ff8fee 0x84131b0e1c8ffe3f

def z914 : W := mkw 0xf6a5922400000000 0x03da964890000000 0xffffffff0000001f 0xf3fffffffc000000

def z915 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc013f80ff80fe25 0x5ff004fe03fe03f8

def z916 : W := mkw 0x43fe295b487f13db 0x090ff8a56d21fc4f 0x03fe007f007f01c8 0x200ff801fc01fc07

def z917 : W := mkw 0x2053bb7600000000 0x20814eedd8000000 0x1fffffff0000001f 0xf07ffffffc000000

def z918 : W := mkw 0x09180c18c24c3b52 0x08246030630930ed 0x1b393c38c24cfff5 0xf86ce4f0e30933ff

def z919 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfcc7ff80ff80fe3f 0xdff31ffe03fe03f8

def z920 : W := mkw 0x095a2d5ac24c3b52 0x082568b56b0930ed 0x1bff3c7fc24cfffd 0xf86ffcf1ff0933ff

def z921 : W := mkw 0x9d2c0000db6a0000 0x0274b000036da800 0xfc7e0000ffff0027 0xcff1f80003fffc00

def z922 : W := mkw 0x2101c02d6c70d19c 0x04840700b5b1c346 0xe001c07ffc70f1f3 0x8f800701fff1c3c7

def z923 : W := mkw 0xd6f63b7600000000 0x235bd8edd8000000 0x1ffeffff0000001e 0xf07ffbfffc000000

def z924 : W := mkw 0xdfac1600db6a2820 0x137eb058036da8a0 0xfffe1c00ffff002f 0xeffff87003fffc00

def z925 : W := mkw 0x6381802c48601110 0x018e0600b1218044 0xe381c07ffc70f1fb 0xaf8e0701fff1c3c7

def z926 : W := mkw 0x2053edff2495ffdf 0x0c814fb7fc9257ff 0x0001ffff0000ffd0 0x100007fffc0003ff

def z927 : W := mkw 0x2101c0096450d198 0x0084070025914346 0xe381c07ffc70f1fb 0xaf8e0701fff1c3c7

def z928 : W := mkw 0x63adc02d6c7ad19c 0x058eb700b5b1eb46 0xe3b9c07ffc70f1fb 0xaf8ee701fff1c3c7

def z929 : W := mkw 0x08582c58820c3b52 0x082160b1620830ed 0x1b793c78020cffdd 0xf06de4f1e00833ff

def z930 : W := mkw 0x01502c5840443b52 0x080540b1610110ed 0x1b793c78c040fffd 0xf86de4f1e30103ff

def z931 : W := mkw 0xf6f7bb7600040240 0x23dbdeedd8001009 0xffffffff004c01df 0xf3fffffffc013007

def z932 : W := mkw 0x0052295200000000 0x000148a548000000 0x1b79ffff0000001d 0xf06de7fffc000000

def z933 : W := mkw 0xd6ac0000192a0000 0x035ab0000064a800 0xe4fe00003dbf0002 0x0793f80000f6fc00

def z934 : W := mkw 0xf6b79b3600000000 0x23dade6cd8000000 0xffbfdfff0000001b 0xe3feff7ffc000000

def z935 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc01ffc0ffc0ffff 0xdff007ff03ff03ff

def z936 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xfbf9c07ffc70f1ff 0xefefe701fff1c3c7

def z937 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffffffffc000f03f 0xfbffffffff0003c0

def z938 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x04c6e3c703ff8fdc 0x10131b8f1c0ffe3f

def z939 : W := mkw 0xf6b79b3600000000 0x23dade6cd8000000 0xffbfffbf00000017 0xf3fefffefc000000

def z940 : W := mkw 0x9c7e3fd2938c2e62 0x3a71f8ff4a4e30b9 0x1c7e3f80038c0e04 0x5071f8fe000e3038

def z941 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe381e07ffe70ffff 0xbf8e0781fff9c3ff

def z942 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1fff3c78c24cffff 0xf87ffcf1e30933ff

def z943 : W := mkw 0x6381802d4c70519c 0x058e0600b531c146 0xe301007fdc0071c1 0x2b8c0401ff7001c7

def z944 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xf801ff80de00fe35 0xdbe007fe037803f8

def z945 : W := mkw 0xdfac0008db6a1110 0x037eb000236da844 0xfffe0078ffff01ef 0xeffff801e3fffc07

def z946 : W := mkw 0xbc01d681b790eca8 0x12f0075a06de43b2 0xfc81ff87ffb0fe37 0xdff207fe1ffec3f8

def z947 : W := mkw 0x09582c58db6e3b52 0x082560b1636db8ed 0x1fff3c78ffffffff 0xfc7ffcf1e3ffffff

def z948 : W := mkw 0x6389c02d6c78d19c 0x058e2700b5b1e346 0xe3f9c07ffc7cf1fb 0xaf8fe701fff1f3c7

def z949 : W := mkw 0xf6f7bb7615004020 0x33dbdeedd8540100 0xffffffff1c00001f 0xf3fffffffc700000

def z950 : W := mkw 0x08502c5082042a40 0x002140b1420810a9 0x1b793c78c24cfffd 0xf86de4f1e30933ff

def z951 : W := mkw 0xb401d6803580ec20 0x12d0075a00d603b0 0xe401ff80fd80fe33 0x9f9007fe03f603f8

def z952 : W := mkw 0xbc01d6a5b790ecac 0x16f0075a96de43b2 0xfc01ff87ff80fe37 0xdff007fe1ffe03f8

def z953 : W := mkw 0x9c004480b380ac00 0x0270011202ce02b0 0xfc01ff80ff80fe37 0xdff007fe03fe03f8

def z954 : W := mkw 0x095a2d5ac24c3b52 0x082568b56b0930ed 0x1fffffffe3ffffff 0xfc7fffffff8fffff

def z955 : W := mkw 0x6381802c4c605114 0x058e0600b1318144 0xe381c07fdc40f1fb 0xab8e0701ff7103c7

def z956 : W := mkw 0x2001d6802480ec20 0x1080075a009203b0 0xe401ff80ff80fe37 0x9f9007fe03fe03f8

def z957 : W := mkw 0xf6f7bb7600050241 0x23dbdeedd8001409 0xffffffff000f001f 0xf3fffffffc003c00

def z958 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x04c6e3c723ff0fce 0x14131b8f1c8ffc3f

def z959 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfffe2000ffff8e3f 0xfffff88003fffe38

def z960 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc01ff80fd80fe13 0x5ff007fe03f603f8

def z961 : W := mkw 0x09180c18c2483912 0x08246030630920e4 0x1b393c78c240fffd 0xf86ce4f1e30903ff

def z962 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc00ff80ff80fe26 0x5ff003fe03fe03f8

def z963 : W := mkw 0xf6a7d3a73db0c4ac 0x37da9f4e9cf6c312 0xe486c3873db00002 0x07921b0e1cf6c000

def z964 : W := mkw 0xbc2dd680b78aec20 0x12f0b75a02de2bb0 0xfcffff80fffffe3f 0xdff3fffe03fffff8

def z965 : W := mkw 0xbc25d680b782ec20 0x12f0975a02de0bb0 0xfc07ff80ff83fe37 0xdff01ffe03fe0ff8

def z966 : W := mkw 0xf6f7bb7600040240 0x23dbdeedd8001009 0xffffffff23ff8fff 0xf7fffffffc8ffe3f

def z967 : W := mkw 0x08502c5882043b52 0x082140b1620810ed 0x1b793c78c200fffd 0xf86de4f1e30803ff

def z968 : W := mkw 0xdfac0008db6a1110 0x037eb000236da844 0xffff0038ffff702f 0xeffffc00e3fffdc0

def z969 : W := mkw 0x09180c18c24c3b52 0x08246030630930ed 0x1b391c78c24cfff9 0xe86ce471e30933ff

def z970 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfffee380ffff003f 0xfffffb8e03fffc00

def z971 : W := mkw 0xbc01968097806c20 0x12f0065a025e01b0 0xf8013f80dc007e01 0x5be004fe037001f8

def z972 : W := mkw 0xb401d6802480ec20 0x12d0075a009203b0 0xfc01ff80fc00fe37 0xdff007fe03f003f8

def z973 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xfb79ffff0000001d 0xf3ede7fffc000000

def z974 : W := mkw 0x004261c3209586c9 0x000109870c82561b 0x04c7e3c7e3ffffff 0x9c131f8f1f8fffff

def z975 : W := mkw 0x09502c58c2403910 0x002540b1630900e4 0x1b793c78c240fffd 0xf86de4f1e30903ff

def z976 : W := mkw 0x4bac0000db6a0000 0x012eb000036da800 0xe3fe0000ffff002b 0xaf8ff80003fffc00

def z977 : W := mkw 0xbc01968097806c20 0x12f0065a025e01b0 0xfc01ff80df807e17 0xdbf007fe037e01f8

def z978 : W := mkw 0x2053ffdb2495fffb 0x18814fff6c9257ff 0x0001ffff0000ffd0 0x100007fffc0003ff

def z979 : W := mkw 0xdfac002cdb6a1114 0x077eb000b36da844 0xfffe0038ffff002f 0xeffff800e3fffc00

def z980 : W := mkw 0x94763b5200000000 0x2251d8ed48000000 0x1fffffff0000001f 0xf07ffffffc000000

def z981 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1f7f3c78c3cffffd 0xf87dfcf1e30f3fff

def z982 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe381c07fdc70f1d9 0x2b8e0701ff71c3c7

def z983 : W := mkw 0xf6a7d3a72cb1c48d 0x27da9f4e9cb2c712 0xe486c3873db30002 0x07921b0e1cf6cc00

def z984 : W := mkw 0xd6f6295200000000 0x035bd8a548000000 0xffffffff0000001f 0xf3fffffffc000000

def z985 : W := mkw 0x2001c02d2410d19c 0x04800700b4904346 0xe081c07ffc70f1fb 0x8f820701fff1c3c7

def z986 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1bf9fc7fc24cffff 0xf86fe7f1ff0933ff

def z987 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1bff3c78c27ffffd 0xf86ffcf1e309ffff

def z988 : W := mkw 0xdeac00009b2a0000 0x037ab000026ca800 0xfffe00003fbf000f 0xe7fff80000fefc00

def z989 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffffffff21b3001f 0xf7fffffffc86cc00

def z990 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc01ff80dc00fe17 0xdbf007fe037003f8

def z991 : W := mkw 0x09084489fffcfffe 0x1c24211227fff3ff 0x00000000fffcffe0 0x0c00000003fff3ff

def z992 : W := mkw 0x9c7e3f52930e2a42 0x2a71f8fd4a4c38a9 0x1c7e3f80038f0e04 0x5071f8fe000e3c38

def z993 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffffffff024c003f 0xf3fffffffc093000

def z994 : W := mkw 0xf6f7bb7611000000 0x23dbdeedd8440000 0xffffffff3d80001f 0xf7fffffffcf60000

def z995 : W := mkw 0xbc01d681b790eca8 0x12f0075a06de43b2 0xfc01ffc7ff80fff7 0xdff007ff1ffe03ff

def z996 : W := mkw 0x09084489eefdffdf 0x0c24211227bbf7ff 0x00000000ffffffe0 0x0c00000003ffffff

def z997 : W := mkw 0x00024183209586c9 0x000009060c82561b 0x0486c3c723ff8ffa 0x84121b0f1c8ffe3f

def z998 : W := mkw 0xdfac0000db6a0000 0x037eb000036da800 0xfffec047ffff003f 0xeffffb011ffffc00

def z999 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc81ffc7ff80fe3f 0xdff207ff1ffe03f8

def z1000 : W := mkw 0x6381c02d6c70d19c 0x058e0700b5b1c346 0xe7c7c07ffc70f1ff 0xaf9f1f01fff1c3c7

def z1001 : W := mkw 0xf6f7bb7611020000 0x23dbdeedd8440800 0xffffffff0183001f 0xf3fffffffc060c00

def z1002 : W := mkw 0x43fe297e486e1352 0x290ff8a5f921b84d 0x03fe007f007f01c8 0x200ff801fc01fc07

def z1003 : W := mkw 0xf6f7bb7600000000 0x23dbdeedd8000000 0xffffffff004081ff 0xf3fffffffc010207

def z1004 : W := mkw 0x004261c32495c6c9 0x000109870c92571b 0x04c6e3c7fffffffe 0x9c131b8f1fffffff

def z1005 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xfc01ff80fffffe37 0xdff007fe03fffff8

def z1006 : W := mkw 0x2101c02d6450d19c 0x04840700b5914346 0xe301c07ffc40f1fb 0xaf8c0701fff103c7

def z1007 : W := mkw 0xf6f7bb7600040240 0x23dbdeedd8001009 0xffffffff020c0e1f 0xf3fffffffc083038

def z1008 : W := mkw 0xbc01d680b780ec20 0x12f0075a02de03b0 0xff01fff8ff80fe3f 0xfffc07ffe3fe03f8

def z1009 : W := mkw 0x6381c0ad6cf0d59c 0x058e0702b5b3c356 0xe781c3fffdf0f1fb 0xaf9e070ffff7c3c7

def z1010 : W := mkw 0xf6b59a3400000000 0x23dad668d0000000 0xffb9ffff0000001f 0xf3fee7fffc000000

def z1011 : W := mkw 0x09582c58c24c3b52 0x082560b1630930ed 0x1b393c78c040fff9 0xf86ce4f1e30103ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z8]),(0,[z0,z1,z2,z9,z4,z5,z6]),(0,[z0,z1,z2,z10,z4,z5,z6])],[(0,[z0,z1,z2,z4,z11,z5,z6]),(0,[z0,z1,z12,z2,z4,z5,z6]),(1,[z0,z13,z2,z4,z14,z6]),(0,[z0,z1,z2,z4,z5,z15,z6])],[(0,[z16,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z17]),(0,[z0,z1,z2,z4,z18,z5,z6])],[(0,[z0,z1,z2,z4,z19,z5,z6]),(0,[z20,z0,z1,z2,z4,z5,z21]),(0,[z0,z1,z2,z4,z5,z6,z22]),(0,[z0,z1,z23,z2,z4,z5,z6]),(1,[z0,z1,z24,z25,z5,z6]),(0,[z0,z1,z2,z26,z4,z5,z6]),(0,[z0,z1,z27,z28,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z29]),(0,[z0,z1,z2,z4,z5,z30,z6]),(0,[z0,z1,z2,z4,z31,z5,z6]),(0,[z0,z1,z2,z32,z4,z5,z6])],[(0,[z0,z1,z33,z2,z4,z5,z6]),(0,[z0,z1,z34,z4,z5,z6,z35]),(0,[z0,z1,z2,z36,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z37,z6]),(0,[z38,z1,z2,z4,z39,z5,z6]),(0,[z40,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z41,z2,z4,z5,z6]),(1,[z0,z42,z1,z43,z4,z5])],[(1,[z0,z1,z2,z44,z5,z6]),(0,[z0,z1,z2,z4,z5,z45,z6]),(0,[z0,z1,z46,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z47,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z48]),(0,[z0,z1,z2,z49,z4,z5,z6]),(0,[z0,z1,z50,z27,z2,z4,z6])]],
   [[(0,[z0,z1,z51,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z52,z6]),(0,[z53,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z54,z55,z4,z5,z6]),(0,[z0,z56,z1,z2,z4,z5,z6])],[(0,[z0,z57,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z58,z5,z6]),(0,[z0,z59,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z60,z4,z5,z6]),(0,[z0,z1,z61,z2,z4,z5,z6]),(0,[z0,z1,z62,z2,z4,z5,z6])],[(0,[z0,z1,z63,z2,z4,z5,z6]),(0,[z0,z1,z64,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z65,z6])],[(0,[z0,z66,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z67]),(0,[z0,z1,z2,z68,z4,z5,z6]),(0,[z69,z0,z1,z2,z4,z5,z6])],[(0,[z70,z1,z2,z4,z71,z5,z6]),(0,[z0,z1,z72,z2,z4,z5,z6]),(0,[z0,z1,z24,z2,z4,z5,z6])],[(0,[z0,z73,z1,z2,z4,z5,z6]),(0,[z74,z0,z1,z2,z4,z5,z6])],[(0,[z38,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z75]),(0,[z76,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z58,z6])],[]],
   [[(0,[z0,z1,z2,z77,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z78])],[(0,[z79,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z80,z6])],[(0,[z81,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z82,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z83]),(0,[z0,z1,z2,z4,z5,z6,z84]),(0,[z0,z1,z2,z4,z5,z6,z85]),(0,[z0,z86,z1,z2,z4,z5,z6])],[(0,[z0,z1,z87,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z88,z6]),(0,[z89,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z90]),(0,[z0,z91,z1,z2,z4,z5,z6]),(0,[z0,z1,z92,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z93,z5,z6])],[(0,[z0,z94,z1,z2,z4,z5,z6]),(1,[z0,z1,z95,z4,z5,z6]),(0,[z0,z96,z1,z2,z4,z52,z6]),(0,[z0,z97,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z98,z5,z6]),(0,[z0,z1,z2,z99,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z100])],[(0,[z0,z101,z1,z102,z2,z4,z5]),(0,[z103,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z104,z4,z5,z6]),(0,[z105,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z106,z2,z4,z5,z6,z107]),(0,[z0,z1,z108,z4,z5,z6,z109]),(0,[z0,z110,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z44,z5,z6]),(0,[z0,z1,z2,z4,z5,z111,z6])],[(0,[z112,z0,z1,z2,z4,z5,z6]),(0,[z0,z113,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z114,z5,z6]),(0,[z0,z115,z1,z2,z4,z5,z6]),(0,[z0,z116,z2,z4,z5,z117,z6]),(0,[z0,z1,z118,z2,z4,z5,z6])],[(0,[z0,z1,z2,z119,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z21]),(0,[z0,z1,z2,z120,z4,z5,z6]),(1,[z121,z1,z2,z4,z5,z122]),(0,[z0,z1,z2,z123,z4,z5,z6]),(0,[z0,z1,z124,z2,z4,z5,z6]),(0,[z0,z1,z2,z125,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z126]),(0,[z0,z1,z2,z127,z4,z5,z6]),(0,[z0,z1,z2,z128,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z129,z6]),(1,[z0,z1,z28,z4,z5,z6]),(0,[z0,z1,z130,z27,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z131,z6])],[(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z132,z2,z133,z4,z5,z6]),(0,[z134,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z135]),(0,[z0,z1,z2,z136,z4,z5,z6]),(0,[z0,z1,z2,z137,z4,z5,z6])],[(0,[z38,z138,z1,z2,z4,z5,z6]),(0,[z70,z0,z1,z2,z4,z139,z6]),(0,[z0,z1,z140,z2,z4,z5,z6]),(0,[z141,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z34,z2,z4,z5,z35]),(0,[z0,z142,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z143,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z144,z6])],[(1,[z0,z145,z2,z4,z146,z6]),(1,[z0,z147,z2,z4,z5,z107]),(0,[z0,z1,z148,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z149,z4,z5,z6]),(0,[z0,z1,z2,z55,z4,z146,z6]),(0,[z0,z1,z2,z150,z4,z5,z6])],[(0,[z151,z1,z102,z2,z4,z5,z6]),(0,[z152,z0,z116,z1,z2,z4,z5]),(0,[z0,z153,z1,z2,z4,z5,z6])],[(0,[z154,z0,z1,z2,z4,z5,z6]),(0,[z0,z155,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z156,z4,z5,z6]),(0,[z0,z1,z2,z95,z4,z5,z6]),(0,[z0,z157,z2,z158,z4,z5,z6]),(0,[z0,z1,z2,z159,z4,z5,z6])],[(0,[z0,z1,z2,z160,z4,z5,z6])],[(0,[z0,z1,z161,z2,z4,z5,z6]),(0,[z0,z1,z162,z2,z4,z5,z6]),(0,[z0,z1,z163,z4,z5,z6,z109]),(0,[z0,z1,z2,z4,z5,z164,z6]),(0,[z0,z165,z1,z2,z4,z5,z6])],[(0,[z166,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z167,z2,z4,z5,z6]),(0,[z0,z1,z50,z2,z4,z6,z168])],[(0,[z0,z145,z102,z2,z4,z5,z6]),(0,[z0,z1,z169,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z117,z6,z107])]],
   [[(0,[z20,z0,z1,z2,z170,z5,z6]),(0,[z0,z1,z27,z2,z4,z14,z6]),(0,[z0,z1,z2,z4,z171,z5,z6])],[(0,[z0,z1,z172,z2,z4,z5,z6]),(0,[z173,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z174,z5,z6]),(0,[z0,z175,z1,z2,z4,z5,z6]),(0,[z0,z1,z176,z2,z4,z5,z6])],[(0,[z0,z157,z177,z2,z4,z5,z6]),(0,[z0,z13,z1,z2,z4,z14,z6]),(0,[z178,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z179,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z180,z5,z181])],[(0,[z182,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z183])],[(0,[z0,z1,z184,z2,z4,z5,z6]),(0,[z0,z185,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z186,z4,z5,z6])],[(0,[z0,z1,z2,z187,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z188,z6]),(0,[z0,z1,z2,z4,z5,z189,z6]),(0,[z190,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z191,z4,z5,z6])],[(0,[z0,z1,z54,z192,z4,z5,z6]),(0,[z193,z0,z1,z108,z4,z5,z6]),(0,[z0,z194,z1,z2,z4,z5,z6]),(0,[z0,z1,z195,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z196])],[(0,[z197,z1,z2,z4,z5,z6,z122]),(0,[z0,z1,z2,z4,z146,z5,z135])]],
   [[(0,[z0,z1,z2,z4,z5,z198,z6]),(0,[z0,z1,z2,z199,z4,z5,z6]),(0,[z0,z1,z2,z4,z200,z5,z6]),(0,[z0,z1,z201,z2,z4,z5,z6]),(0,[z0,z202,z1,z61,z2,z4,z5])],[(1,[z138,z1,z2,z203,z5,z6]),(0,[z0,z204,z1,z2,z4,z5,z6]),(0,[z0,z1,z205,z2,z4,z5,z6]),(0,[z0,z206,z1,z2,z4,z5,z6]),(0,[z0,z1,z207,z2,z4,z5,z6])],[(0,[z208,z0,z1,z2,z4,z5,z6])],[(0,[z0,z106,z1,z2,z4,z5,z6]),(0,[z0,z1,z209,z2,z4,z5,z6]),(0,[z0,z210,z1,z2,z4,z5,z6]),(0,[z0,z1,z211,z4,z5,z6,z109]),(1,[z0,z1,z130,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z212])],[(0,[z0,z213,z1,z2,z4,z5,z6]),(0,[z121,z0,z214,z2,z4,z5,z6]),(0,[z0,z145,z13,z2,z4,z5,z6])],[(0,[z0,z1,z2,z215,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z216,z6]),(0,[z0,z217,z1,z2,z4,z5,z6]),(0,[z0,z218,z1,z2,z4,z5,z6]),(0,[z0,z219,z1,z2,z4,z5,z6]),(0,[z0,z1,z34,z2,z43,z4,z5]),(0,[z0,z1,z2,z4,z5,z220,z6])],[(0,[z151,z0,z1,z2,z4,z5,z221]),(0,[z152,z197,z1,z2,z4,z5,z6]),(0,[z0,z1,z222,z2,z4,z5,z6]),(0,[z0,z1,z2,z223,z4,z5,z6]),(0,[z0,z1,z50,z2,z203,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z224])],[(0,[z0,z116,z106,z2,z4,z5,z6]),(0,[z0,z1,z2,z225,z4,z5,z6]),(1,[z0,z1,z50,z27,z2,z6])]],
   [[(0,[z0,z1,z226,z2,z4,z5,z6]),(0,[z227,z0,z1,z2,z4,z5,z6]),(1,[z70,z1,z2,z4,z71,z6])],[(0,[z0,z1,z2,z4,z5,z221,z6])],[(0,[z0,z1,z2,z4,z5,z6,z228]),(0,[z0,z1,z2,z4,z229,z5,z6]),(0,[z0,z1,z2,z4,z230,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z231])],[(0,[z232,z0,z1,z2,z4,z5,z6]),(0,[z0,z96,z1,z2,z4,z58,z6]),(0,[z0,z233,z1,z2,z4,z5,z6])],[(0,[z89,z193,z1,z2,z4,z5,z6]),(0,[z0,z1,z24,z192,z4,z5,z6]),(0,[z0,z234,z1,z2,z4,z5,z6])],[(0,[z197,z106,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z65,z181]),(0,[z235,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z236,z0,z1,z2,z4,z5,z6]),(0,[z0,z237,z1,z2,z4,z5,z6]),(0,[z0,z238,z1,z2,z4,z5,z6])],[(0,[z0,z1,z108,z4,z5,z6,z90]),(0,[z0,z1,z239,z2,z4,z5,z6]),(0,[z0,z1,z2,z240,z4,z5,z6])]],
   [[(0,[z151,z0,z106,z2,z4,z5,z6]),(0,[z0,z241,z1,z2,z4,z5,z6]),(1,[z0,z242,z2,z4,z5,z6])],[(0,[z243,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z244,z4,z5,z6])],[(0,[z0,z245,z1,z2,z4,z5,z6]),(0,[z0,z1,z246,z2,z4,z5,z6]),(0,[z0,z1,z247,z2,z4,z5,z6]),(0,[z0,z1,z248,z2,z4,z5,z6])],[(0,[z89,z0,z1,z192,z4,z5,z6]),(0,[z0,z96,z1,z2,z133,z5,z6])],[(0,[z249,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z250,z4,z5,z6]),(0,[z0,z1,z2,z251,z4,z5,z6]),(0,[z252,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z253,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z254,z5,z6])],[(0,[z255,z0,z1,z2,z4,z5,z6])],[]],
   [[(0,[z0,z1,z2,z158,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z256])],[(0,[z197,z0,z106,z2,z4,z5,z6]),(0,[z0,z1,z257,z2,z4,z5,z6]),(0,[z0,z258,z1,z2,z4,z5,z6]),(0,[z259,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z260,z2,z4,z5,z6]),(0,[z0,z261,z1,z2,z4,z5,z6])],[(0,[z89,z0,z1,z2,z156,z5,z6]),(0,[z262,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z263,z4,z5,z6]),(0,[z264,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z163,z2,z5,z6,z90]),(0,[z0,z1,z2,z4,z265,z5,z6])],[(0,[z266,z0,z1,z2,z4,z5,z6]),(0,[z0,z132,z1,z2,z133,z5,z6]),(0,[z0,z267,z1,z2,z4,z5,z6])],[(0,[z0,z268,z1,z2,z4,z5,z6]),(0,[z0,z1,z163,z4,z5,z6,z90]),(0,[z0,z269,z153,z2,z4,z5,z6])],[(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z270,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z203,z4,z5,z6]),(0,[z0,z1,z271,z2,z4,z5,z6]),(0,[z0,z1,z55,z4,z5,z6,z109])],[(0,[z272,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z273,z2,z4,z5,z122]),(0,[z0,z1,z163,z50,z2,z5,z6]),(0,[z0,z1,z2,z43,z4,z5,z6])],[(0,[z0,z1,z82,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z0,z132,z96,z2,z4,z5,z6]),(0,[z0,z1,z2,z274,z4,z5,z6]),(0,[z0,z145,z2,z4,z146,z5,z6]),(0,[z275,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z276,z2,z4,z5,z6])],[(1,[z89,z1,z192,z4,z5,z6]),(0,[z0,z1,z2,z277,z4,z5,z6])],[(0,[z138,z0,z1,z2,z203,z5,z6]),(0,[z0,z1,z278,z2,z4,z5,z6]),(0,[z0,z116,z1,z2,z4,z5,z6]),(0,[z0,z279,z1,z2,z4,z5,z6]),(0,[z0,z1,z50,z2,z4,z5,z6]),(0,[z0,z1,z2,z280,z4,z5,z6])],[(0,[z0,z102,z2,z4,z5,z14,z6]),(0,[z0,z281,z1,z2,z4,z5,z6]),(0,[z0,z2,z133,z4,z47,z5,z6]),(0,[z147,z282,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z283]),(0,[z38,z0,z1,z2,z39,z5,z6]),(0,[z0,z1,z2,z284,z4,z5,z6]),(0,[z0,z1,z2,z4,z71,z5,z6]),(1,[z0,z51,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z285]),(0,[z0,z13,z2,z4,z5,z14,z6]),(0,[z0,z286,z1,z2,z4,z5,z6]),(0,[z0,z42,z1,z2,z4,z5,z6]),(0,[z0,z153,z1,z2,z4,z5,z181]),(1,[z0,z153,z1,z273,z2,z4])],[(0,[z0,z1,z50,z2,z39,z5,z6]),(0,[z70,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z287,z2,z4,z5,z6]),(0,[z0,z1,z2,z288,z5,z6,z168]),(0,[z0,z1,z289,z2,z4,z5,z6])],[(0,[z0,z157,z1,z2,z4,z290,z6]),(0,[z0,z1,z2,z4,z5,z6,z291]),(0,[z0,z1,z2,z4,z5,z292,z6])],[(0,[z0,z1,z2,z4,z293,z5,z6]),(0,[z0,z1,z294,z2,z4,z5,z6]),(0,[z295,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z55,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z296,z5,z6]),(0,[z0,z1,z2,z4,z5,z297,z6])],[(0,[z0,z298,z1,z2,z4,z5,z6])],[(0,[z0,z299,z1,z2,z4,z5,z6]),(0,[z0,z1,z300,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z301,z6]),(0,[z0,z1,z163,z2,z25,z5,z6])],[(0,[z151,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z146,z6,z109])],[(1,[z0,z1,z2,z4,z5,z221]),(0,[z0,z1,z2,z4,z5,z302,z6]),(0,[z303,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z304,z2,z4,z5,z6])],[(0,[z0,z1,z2,z305,z4,z5,z6]),(0,[z0,z1,z2,z170,z4,z5,z6]),(0,[z0,z1,z2,z4,z306,z5,z6]),(0,[z0,z307,z1,z2,z4,z5,z6]),(0,[z0,z1,z308,z2,z4,z5,z6]),(0,[z0,z202,z1,z2,z60,z5,z6])],[(0,[z0,z1,z273,z2,z4,z5,z65]),(0,[z309,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z211,z4,z6,z109]),(0,[z0,z1,z273,z2,z4,z5,z6])],[(0,[z310,z0,z1,z2,z4,z5,z6]),(0,[z311,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z312]),(0,[z0,z1,z2,z4,z146,z6,z168]),(0,[z0,z1,z313,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z314,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z315]),(0,[z316,z0,z1,z2,z4,z5,z6]),(0,[z317,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z27,z2,z288,z4,z6]),(0,[z0,z1,z2,z318,z4,z5,z6])],[(0,[z319,z0,z1,z2,z4,z5,z6]),(0,[z138,z1,z2,z203,z4,z5,z6]),(0,[z0,z1,z320,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z14,z6]),(0,[z0,z147,z145,z2,z4,z5,z6]),(0,[z0,z321,z1,z2,z4,z5,z6]),(0,[z0,z42,z1,z34,z4,z5,z6])],[],[(0,[z0,z1,z102,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z322]),(0,[z323,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z324]),(0,[z0,z1,z2,z325,z4,z5,z6]),(1,[z0,z1,z2,z326,z5,z6]),(1,[z0,z1,z2,z4,z180,z181])],[(0,[z197,z0,z1,z2,z4,z5,z6]),(1,[z197,z106,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z327]),(0,[z121,z0,z147,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z328]),(0,[z0,z1,z211,z2,z4,z6,z109])],[(0,[z0,z1,z2,z4,z5,z329,z6])],[(0,[z0,z1,z2,z4,z330,z5,z6])],[(0,[z331,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z332,z4,z5,z6])]],
   [[(1,[z0,z1,z333,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z122]),(0,[z0,z1,z2,z334,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z65,z107]),(0,[z0,z1,z2,z335,z4,z5,z6]),(0,[z0,z1,z336,z2,z4,z5,z6]),(1,[z0,z1,z2,z288,z6,z168])],[(0,[z20,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z337]),(0,[z0,z1,z163,z2,z5,z6,z168])],[(0,[z338,z0,z1,z2,z4,z5,z6]),(0,[z0,z96,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z339,z4,z5,z6]),(0,[z0,z340,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z28,z4,z5,z6])],[(0,[z0,z1,z341,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z342,z5,z6]),(0,[z0,z1,z343,z2,z4,z5,z6]),(0,[z0,z1,z344,z2,z4,z5,z6]),(0,[z0,z1,z61,z2,z60,z4,z5])],[(0,[z0,z1,z2,z4,z5,z345,z6]),(1,[z0,z202,z1,z61,z2,z5])]],
   [[(0,[z0,z1,z346,z2,z4,z5,z6]),(0,[z347,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z348,z6]),(0,[z0,z1,z349,z2,z4,z5,z6])],[(1,[z282,z1,z2,z4,z5,z6]),(0,[z0,z147,z2,z4,z5,z6,z107]),(0,[z350,z0,z1,z2,z4,z5,z6])],[(0,[z197,z151,z1,z2,z4,z5,z6]),(1,[z0,z157,z158,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z351]),(0,[z352,z0,z1,z2,z4,z5,z6])],[(0,[z0,z132,z1,z2,z4,z5,z6]),(1,[z0,z1,z353,z2,z4,z5])],[(0,[z354,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z355,z5,z6]),(0,[z0,z1,z2,z4,z326,z5,z6])],[(0,[z356,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z156,z5,z6]),(0,[z0,z1,z357,z2,z4,z5,z6]),(0,[z358,z0,z1,z2,z4,z5,z6])],[(0,[z0,z359,z1,z2,z4,z5,z6])],[(0,[z0,z1,z360,z2,z4,z5,z6]),(0,[z0,z1,z2,z333,z4,z5,z6]),(0,[z0,z1,z2,z361,z4,z5,z6]),(0,[z0,z1,z54,z25,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z1,z2,z362,z4,z5,z6])],[(0,[z0,z101,z1,z2,z4,z5,z6]),(0,[z0,z1,z108,z2,z4,z5,z6]),(0,[z0,z1,z2,z363,z4,z5,z6]),(0,[z364,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z365])],[(0,[z0,z1,z353,z2,z4,z146,z5]),(0,[z0,z1,z2,z4,z5,z6,z366])],[(0,[z0,z1,z2,z4,z5,z6,z367]),(0,[z0,z1,z2,z4,z5,z6,z368])],[(0,[z0,z1,z2,z39,z5,z6,z90]),(0,[z0,z1,z2,z4,z369,z5,z6]),(0,[z0,z1,z2,z370,z4,z5,z6]),(0,[z0,z1,z2,z55,z326,z5,z6])],[(0,[z0,z371,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z372,z6]),(0,[z0,z1,z2,z192,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z373]),(0,[z0,z1,z374,z2,z4,z5,z6]),(0,[z0,z145,z2,z4,z5,z117,z6]),(0,[z0,z1,z375,z2,z4,z5,z6]),(0,[z0,z153,z1,z273,z2,z4,z5])],[(0,[z0,z376,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z21,z6]),(0,[z0,z1,z2,z377,z4,z5,z6]),(0,[z378,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z379,z4,z5,z6])]],
   [[(0,[z0,z1,z54,z108,z4,z5,z6]),(0,[z0,z96,z2,z4,z47,z5,z6])],[(1,[z38,z1,z2,z39,z5,z6]),(0,[z0,z1,z2,z380,z4,z5,z6]),(0,[z0,z1,z2,z4,z381,z5,z6]),(0,[z382,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z383,z6]),(0,[z0,z1,z2,z384,z4,z5,z6])],[(0,[z0,z1,z2,z385,z4,z5,z6]),(0,[z0,z1,z2,z386,z4,z5,z6]),(0,[z387,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z388,z6]),(0,[z0,z1,z2,z4,z5,z6,z389]),(0,[z0,z1,z390,z2,z4,z5,z6])],[(0,[z391,z0,z1,z2,z4,z5,z6]),(0,[z0,z392,z1,z2,z4,z5,z6]),(0,[z0,z393,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z122,z181]),(1,[z0,z1,z2,z4,z290,z6]),(0,[z0,z1,z2,z4,z5,z6,z394]),(0,[z0,z1,z163,z54,z4,z5,z6]),(0,[z0,z1,z395,z2,z4,z5,z6]),(0,[z0,z1,z27,z2,z5,z6,z168])],[(0,[z0,z1,z2,z4,z396,z5,z6]),(0,[z0,z214,z1,z2,z4,z5,z6]),(0,[z0,z1,z397,z2,z4,z5,z6]),(0,[z0,z116,z1,z2,z4,z5,z181]),(0,[z0,z1,z24,z25,z4,z5,z6]),(0,[z0,z398,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z399]),(0,[z0,z177,z400,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z180,z6,z181])],[(0,[z0,z1,z401,z2,z4,z5,z6]),(0,[z0,z1,z402,z2,z4,z5,z6]),(1,[z0,z177,z400,z4,z5,z6]),(0,[z0,z403,z1,z2,z4,z5,z6]),(0,[z404,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z405,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z406,z6]),(0,[z0,z1,z2,z288,z4,z6,z168])],[(0,[z0,z1,z2,z4,z5,z6,z407]),(0,[z0,z1,z2,z4,z408,z5,z6]),(0,[z0,z409,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z410,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z411]),(0,[z0,z1,z2,z4,z5,z6,z412])],[(0,[z0,z1,z2,z4,z5,z413,z6]),(0,[z0,z414,z1,z2,z4,z5,z6]),(0,[z0,z147,z1,z2,z4,z5,z117]),(0,[z0,z415,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z416,z5,z6])],[(0,[z0,z1,z2,z4,z146,z5,z6]),(0,[z0,z202,z1,z61,z2,z5,z6])],[(0,[z0,z1,z2,z4,z417,z5,z6]),(0,[z20,z0,z1,z2,z4,z5,z315]),(0,[z0,z147,z1,z2,z4,z5,z6])],[(0,[z418,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z419,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z420]),(0,[z0,z1,z24,z2,z5,z6,z90])],[(0,[z0,z1,z24,z108,z4,z5,z6]),(0,[z20,z0,z421,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z422])],[(0,[z1,z2,z203,z4,z39,z5,z6]),(0,[z152,z0,z147,z1,z2,z4,z5]),(0,[z0,z1,z423,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z424,z6]),(0,[z0,z1,z425,z2,z4,z5,z6])],[(0,[z0,z1,z2,z426,z4,z5,z6]),(0,[z0,z1,z427,z2,z4,z5,z6]),(0,[z0,z1,z54,z211,z4,z5,z6])],[(0,[z0,z1,z428,z2,z4,z5,z6]),(0,[z0,z429,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z430,z5,z6])],[(0,[z0,z431,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z432,z6]),(1,[z0,z116,z2,z4,z5,z117]),(0,[z0,z116,z1,z2,z4,z5,z117])],[(0,[z20,z0,z1,z333,z4,z5,z6]),(0,[z433,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z211,z2,z4,z5,z6])],[(0,[z0,z1,z2,z434,z4,z5,z6]),(0,[z89,z0,z1,z108,z4,z5,z6]),(0,[z0,z1,z2,z4,z39,z5,z6]),(0,[z0,z1,z435,z2,z4,z5,z6]),(0,[z121,z1,z2,z4,z5,z6,z122]),(0,[z0,z1,z2,z436,z4,z5,z6])],[(0,[z0,z1,z2,z4,z437,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z438]),(0,[z0,z1,z439,z2,z4,z5,z6]),(0,[z440,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z441,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z442,z5,z6])]],
   [[(0,[z0,z443,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z444,z4,z5,z6]),(0,[z0,z42,z1,z43,z4,z5,z6])],[(0,[z0,z445,z1,z2,z4,z5,z6]),(1,[z20,z1,z2,z4,z139,z6]),(0,[z446,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z447,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z315]),(0,[z0,z448,z1,z2,z4,z5,z6]),(0,[z0,z1,z211,z2,z55,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z449]),(0,[z0,z1,z2,z4,z5,z450,z6])],[(0,[z0,z145,z106,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z451]),(0,[z0,z1,z2,z133,z4,z5,z6]),(0,[z0,z202,z1,z2,z4,z5,z212])],[(0,[z0,z1,z2,z39,z5,z6,z168]),(0,[z0,z1,z2,z55,z4,z14,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z452,z6]),(0,[z0,z1,z453,z2,z4,z5,z6]),(0,[z454,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z24,z2,z25,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z35]),(0,[z0,z1,z2,z4,z5,z455,z6]),(0,[z0,z202,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z456,z5,z6]),(0,[z0,z1,z2,z457,z4,z5,z6]),(0,[z0,z1,z458,z2,z4,z5,z6])],[(0,[z0,z1,z459,z2,z4,z5,z6]),(0,[z460,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z461,z1,z2,z4,z5,z6]),(0,[z0,z147,z116,z2,z4,z5,z6]),(0,[z0,z462,z1,z2,z4,z5,z6]),(0,[z0,z269,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z463,z4,z5,z6]),(0,[z0,z464,z1,z2,z4,z5,z6]),(1,[z152,z1,z2,z4,z5,z65]),(0,[z0,z465,z1,z2,z4,z5,z6])],[(0,[z466,z0,z1,z2,z4,z5,z6]),(0,[z0,z106,z2,z4,z5,z14,z6]),(0,[z0,z1,z2,z467,z4,z5,z6]),(0,[z0,z468,z1,z2,z4,z5,z6]),(0,[z0,z1,z130,z2,z4,z5,z6])],[(0,[z469,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z470,z2,z4,z5,z6]),(0,[z0,z471,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z472,z4,z5,z6])],[(0,[z0,z1,z192,z4,z5,z6,z109])],[(1,[z0,z421,z2,z4,z5,z6]),(0,[z152,z1,z2,z4,z5,z65,z6]),(0,[z0,z1,z2,z4,z5,z290,z6]),(0,[z0,z1,z2,z473,z4,z5,z6])],[(0,[z0,z474,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z475]),(0,[z476,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z477]),(0,[z0,z1,z2,z4,z5,z6,z478])],[(0,[z0,z479,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z480,z4,z5,z6]),(0,[z0,z1,z2,z481,z4,z5,z6])]],
   [[(0,[z482,z0,z1,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z71,z6]),(1,[z0,z214,z2,z4,z5,z6]),(0,[z483,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z117,z122]),(0,[z0,z1,z2,z484,z4,z5,z6]),(0,[z0,z1,z485,z2,z4,z5,z6]),(0,[z0,z1,z486,z2,z4,z5,z6]),(0,[z0,z1,z487,z2,z4,z5,z6]),(0,[z0,z1,z50,z2,z288,z5,z6]),(0,[z0,z488,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z25,z203,z5,z6]),(0,[z0,z1,z400,z2,z4,z5,z6]),(0,[z0,z1,z489,z2,z4,z5,z6]),(0,[z0,z1,z2,z60,z5,z6,z212])],[(0,[z0,z490,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z181])],[(0,[z193,z0,z1,z2,z4,z5,z6]),(0,[z0,z491,z1,z2,z4,z5,z6]),(0,[z0,z1,z492,z2,z4,z5,z6])],[(0,[z0,z493,z1,z2,z4,z5,z6]),(0,[z494,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z24,z2,z5,z6,z168]),(0,[z0,z495,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z496,z5,z6])],[(0,[z0,z497,z1,z2,z4,z5,z6]),(0,[z498,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z499]),(0,[z0,z1,z2,z4,z5,z6,z500])],[(0,[z0,z1,z501,z2,z4,z5,z6]),(0,[z0,z1,z502,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z503,z4,z5,z6]),(0,[z0,z504,z1,z2,z4,z5,z6]),(0,[z0,z1,z505,z2,z4,z5,z6]),(0,[z0,z1,z506,z2,z4,z5,z6])],[(0,[z507,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z508]),(0,[z138,z0,z1,z2,z4,z5,z6]),(0,[z20,z1,z2,z4,z5,z139,z6]),(0,[z0,z1,z509,z2,z4,z5,z6]),(0,[z0,z2,z4,z146,z5,z14,z6]),(0,[z0,z510,z1,z2,z4,z5,z6]),(0,[z0,z1,z511,z2,z4,z5,z6]),(0,[z0,z1,z2,z512,z4,z5,z6])],[(0,[z0,z94,z1,z102,z2,z4,z5]),(0,[z513,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z514]),(0,[z0,z1,z515,z2,z4,z5,z6]),(0,[z0,z1,z516,z2,z4,z5,z6])],[(0,[z0,z1,z517,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z65,z6,z122]),(1,[z0,z1,z34,z4,z5,z35])],[(0,[z0,z1,z2,z4,z5,z6,z518]),(0,[z138,z0,z1,z2,z39,z5,z6]),(0,[z519,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z520,z4,z5,z6]),(0,[z0,z1,z2,z288,z4,z5,z6]),(0,[z0,z1,z2,z4,z521,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z522]),(0,[z0,z1,z2,z4,z5,z523,z6]),(0,[z0,z1,z524,z2,z4,z5,z6]),(0,[z0,z1,z34,z2,z4,z5,z6])],[(0,[z0,z1,z525,z2,z4,z5,z6]),(0,[z0,z1,z2,z526,z4,z5,z6]),(0,[z0,z145,z1,z2,z4,z5,z6]),(0,[z0,z527,z1,z2,z4,z5,z6])],[]],
   [[(0,[z0,z528,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z529,z6])],[(0,[z0,z1,z2,z4,z5,z117,z65]),(0,[z0,z1,z2,z4,z5,z117,z6]),(1,[z0,z1,z2,z60,z5,z212])],[(0,[z0,z530,z1,z2,z4,z5,z6]),(0,[z121,z0,z1,z2,z4,z5,z122]),(0,[z0,z177,z1,z400,z4,z5,z6])],[],[(0,[z0,z531,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z532,z5,z6]),(1,[z0,z1,z54,z55,z4,z6]),(0,[z0,z42,z1,z2,z4,z5,z35])],[(1,[z151,z102,z2,z4,z5,z6]),(0,[z533,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z534,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z535,z5,z6])],[(0,[z0,z536,z1,z2,z4,z5,z6]),(0,[z0,z147,z1,z2,z4,z5,z181]),(0,[z0,z1,z2,z4,z537,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z538])]],
   [[(0,[z0,z1,z539,z2,z4,z5,z6]),(0,[z0,z540,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z541,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z542]),(0,[z0,z543,z1,z2,z4,z5,z6]),(0,[z0,z1,z54,z2,z55,z4,z6])],[(0,[z0,z1,z2,z4,z5,z6,z544]),(0,[z0,z145,z1,z2,z4,z146,z6]),(0,[z0,z1,z545,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z546])],[(0,[z0,z116,z102,z2,z4,z5,z6]),(0,[z547,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z548]),(0,[z0,z1,z2,z4,z549,z5,z6]),(0,[z0,z1,z2,z4,z550,z5,z6])],[(0,[z0,z1,z551,z2,z4,z5,z6]),(0,[z0,z1,z2,z552,z4,z5,z6]),(0,[z0,z1,z2,z60,z4,z5,z212])],[(1,[z0,z94,z1,z2,z4,z5]),(0,[z0,z553,z1,z2,z4,z5,z6]),(0,[z0,z157,z1,z2,z4,z342,z6]),(0,[z0,z1,z2,z4,z5,z6,z554]),(0,[z0,z555,z1,z2,z4,z5,z6]),(0,[z556,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z557,z2,z4,z5,z6]),(0,[z0,z1,z2,z25,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z558])],[(0,[z89,z0,z1,z2,z19,z5,z6])]],
   [[(0,[z0,z157,z1,z158,z4,z5,z6]),(0,[z0,z559,z1,z2,z4,z5,z6]),(0,[z560,z0,z1,z2,z4,z5,z6])],[(0,[z0,z102,z2,z4,z5,z6,z107]),(0,[z0,z1,z561,z2,z4,z5,z6]),(0,[z0,z1,z2,z25,z39,z5,z6]),(0,[z0,z177,z1,z158,z4,z5,z6]),(0,[z0,z1,z562,z2,z4,z5,z6]),(0,[z0,z1,z163,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z563,z5,z6]),(0,[z0,z1,z2,z564,z4,z5,z6]),(0,[z0,z565,z1,z2,z4,z5,z6])],[(0,[z20,z0,z435,z2,z4,z5,z6]),(0,[z121,z0,z1,z2,z4,z5,z6]),(0,[z121,z0,z1,z2,z4,z5,z65]),(0,[z566,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z25,z4,z5,z6,z109]),(0,[z0,z1,z567,z2,z4,z5,z6])],[(0,[z0,z1,z192,z4,z5,z6,z90]),(0,[z0,z1,z2,z4,z5,z6,z568]),(0,[z193,z1,z108,z2,z4,z5,z6]),(0,[z0,z1,z569,z2,z4,z5,z6])],[(0,[z570,z0,z1,z2,z4,z5,z6]),(0,[z151,z0,z102,z2,z4,z5,z6]),(0,[z0,z571,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z572,z5,z6]),(0,[z573,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z574]),(0,[z0,z1,z2,z575,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z576,z6]),(0,[z0,z1,z2,z4,z5,z6,z577]),(0,[z0,z157,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z578,z5,z6]),(0,[z0,z1,z2,z4,z579,z5,z6]),(0,[z580,z0,z1,z2,z4,z5,z6])],[(0,[z151,z0,z1,z2,z4,z5,z508]),(0,[z0,z1,z2,z581,z4,z5,z6]),(0,[z0,z1,z2,z203,z5,z6,z90]),(0,[z0,z582,z1,z2,z4,z5,z6]),(0,[z0,z177,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z583]),(0,[z0,z1,z54,z2,z4,z6,z109]),(0,[z0,z1,z584,z2,z4,z5,z6])],[(0,[z0,z585,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z586]),(0,[z0,z1,z273,z2,z4,z180,z5])]],
   [[(0,[z0,z1,z2,z587,z4,z5,z6]),(0,[z0,z1,z588,z2,z4,z5,z6]),(0,[z0,z1,z589,z2,z4,z5,z6]),(1,[z0,z132,z2,z133,z5,z6]),(0,[z0,z282,z1,z2,z4,z5,z6]),(0,[z0,z153,z1,z2,z4,z180,z6])],[(1,[z590,z1,z2,z4,z5,z6]),(0,[z0,z1,z591,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z592,z6]),(0,[z0,z593,z1,z2,z4,z5,z6])],[(1,[z0,z96,z2,z47,z5,z6]),(0,[z0,z1,z2,z594,z4,z5,z6]),(0,[z0,z1,z595,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z596,z6]),(0,[z0,z1,z2,z4,z5,z597,z6]),(0,[z0,z598,z1,z2,z4,z5,z6]),(0,[z0,z1,z599,z2,z4,z5,z6]),(0,[z590,z147,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z600,z4,z5,z6]),(0,[z0,z42,z1,z2,z43,z4,z5])],[(0,[z197,z0,z102,z2,z4,z5,z6]),(0,[z0,z1,z601,z2,z4,z5,z6])],[(0,[z1,z2,z4,z71,z5,z139,z6]),(0,[z70,z0,z1,z2,z4,z71,z6]),(0,[z0,z1,z602,z2,z55,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z603]),(0,[z0,z1,z2,z4,z5,z604,z6]),(0,[z0,z1,z2,z4,z5,z6,z107])]],
   [[(0,[z605,z0,z1,z2,z4,z5,z6])],[(0,[z0,z421,z1,z2,z4,z5,z6]),(1,[z0,z1,z163,z5,z6,z90]),(0,[z0,z1,z2,z606,z4,z5,z6])],[(0,[z607,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z608,z5,z6]),(0,[z0,z400,z2,z158,z4,z5,z6]),(0,[z0,z1,z609,z2,z4,z5,z6]),(0,[z610,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z611,z5,z6])],[(0,[z612,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z613]),(0,[z0,z1,z2,z4,z5,z614,z6]),(0,[z0,z615,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z616]),(0,[z0,z1,z2,z4,z5,z6,z617]),(0,[z0,z1,z2,z4,z5,z6,z618])],[(0,[z193,z0,z1,z192,z4,z5,z6]),(0,[z0,z619,z1,z2,z4,z5,z6]),(0,[z0,z1,z620,z2,z4,z5,z6]),(0,[z0,z1,z2,z621,z4,z5,z6])],[(0,[z20,z0,z1,z239,z4,z5,z6]),(0,[z622,z0,z1,z2,z4,z5,z6])],[(0,[z0,z623,z1,z2,z4,z5,z6]),(0,[z624,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z625,z4,z5,z6]),(0,[z0,z626,z1,z2,z4,z5,z6]),(0,[z627,z0,z1,z2,z4,z5,z6]),(0,[z0,z628,z1,z2,z4,z5,z6])],[(0,[z0,z1,z50,z24,z2,z5,z6])]],
   [[(0,[z121,z0,z51,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z629,z5,z6]),(0,[z0,z96,z1,z2,z47,z5,z6]),(0,[z0,z1,z2,z630,z4,z5,z6]),(0,[z0,z1,z43,z4,z5,z6,z35]),(0,[z0,z153,z242,z2,z4,z5,z6])],[(0,[z1,z102,z2,z4,z5,z6,z122]),(0,[z0,z1,z631,z2,z4,z5,z6]),(0,[z632,z0,z1,z2,z4,z5,z6]),(0,[z0,z633,z1,z2,z4,z5,z6]),(1,[z0,z435,z2,z4,z5,z6]),(0,[z152,z121,z1,z2,z4,z5,z6]),(0,[z0,z1,z634,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z635,z5,z6]),(0,[z0,z1,z50,z27,z2,z5,z6])],[(0,[z0,z636,z1,z2,z4,z5,z6]),(0,[z38,z0,z1,z82,z4,z5,z6]),(0,[z0,z1,z2,z4,z637,z5,z6]),(0,[z0,z1,z638,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z135])],[(0,[z0,z1,z2,z4,z639,z5,z6]),(0,[z1,z108,z2,z192,z4,z5,z6]),(0,[z20,z70,z1,z2,z4,z5,z6]),(0,[z0,z1,z27,z2,z4,z5,z6])],[(0,[z38,z0,z1,z95,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z139,z6]),(0,[z590,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z640,z6]),(0,[z152,z0,z1,z2,z4,z5,z122]),(0,[z0,z1,z641,z2,z4,z5,z6]),(0,[z0,z642,z1,z2,z4,z5,z6]),(0,[z643,z0,z1,z2,z4,z5,z6]),(0,[z0,z13,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z644,z4,z5,z6]),(0,[z645,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z646,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z52,z6]),(0,[z0,z647,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z14,z117,z6]),(0,[z648,z0,z1,z2,z4,z5,z6]),(1,[z0,z269,z2,z4,z5,z6])]],
   [[(0,[z0,z132,z1,z2,z47,z5,z6]),(0,[z0,z147,z1,z273,z2,z4,z5]),(0,[z0,z1,z649,z2,z4,z5,z6])],[(1,[z193,z1,z108,z4,z5,z6]),(0,[z650,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z651])],[(0,[z0,z1,z652,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z653,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z508]),(0,[z0,z1,z2,z4,z654,z5,z6]),(0,[z0,z1,z2,z655,z4,z5,z6]),(0,[z0,z147,z1,z2,z4,z5,z107])],[(0,[z0,z1,z2,z656,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z109])],[(0,[z0,z1,z2,z4,z5,z657,z6]),(0,[z0,z1,z2,z658,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z659]),(0,[z0,z1,z2,z4,z5,z6,z660]),(0,[z0,z1,z661,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z662]),(0,[z0,z1,z61,z2,z5,z6,z212]),(0,[z0,z1,z273,z2,z4,z6,z181])],[(1,[z0,z101,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z663,z5,z6]),(0,[z0,z1,z2,z203,z5,z6,z168])],[(0,[z20,z0,z1,z2,z4,z139,z6]),(0,[z0,z1,z27,z2,z4,z146,z6]),(0,[z0,z1,z353,z2,z4,z5,z6]),(0,[z0,z664,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z665,z4,z5,z6]),(0,[z20,z0,z1,z2,z44,z5,z6]),(0,[z0,z1,z2,z666,z4,z5,z6]),(0,[z0,z1,z667,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z668,z5,z6]),(0,[z0,z1,z2,z669,z4,z5,z6]),(0,[z0,z1,z670,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z168])],[(0,[z0,z13,z1,z2,z4,z146,z6]),(0,[z0,z1,z2,z671,z4,z5,z6]),(0,[z0,z116,z1,z273,z2,z4,z5]),(0,[z0,z1,z25,z4,z5,z6,z90])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z19,z5,z6]),(0,[z0,z1,z2,z672,z4,z5,z6]),(0,[z38,z0,z1,z2,z203,z5,z6]),(0,[z673,z0,z1,z2,z4,z5,z6])],[(0,[z89,z1,z2,z192,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z122,z107]),(1,[z0,z1,z2,z4,z342,z6]),(0,[z674,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z675,z2,z4,z5,z6]),(0,[z0,z676,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z677,z6])],[(0,[z106,z1,z102,z2,z4,z5,z6]),(1,[z0,z1,z239,z4,z5,z6]),(0,[z0,z1,z2,z4,z678,z5,z6]),(0,[z0,z116,z1,z2,z4,z5,z107]),(0,[z0,z1,z679,z2,z4,z5,z6]),(0,[z0,z680,z1,z2,z4,z5,z6]),(0,[z0,z1,z242,z2,z4,z5,z6])],[(0,[z0,z1,z681,z2,z4,z5,z6]),(0,[z152,z0,z1,z2,z4,z5,z6]),(0,[z152,z0,z1,z2,z4,z5,z65]),(0,[z0,z1,z2,z682,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z683])],[(0,[z121,z0,z116,z1,z2,z4,z5]),(0,[z0,z1,z2,z684,z4,z5,z6]),(0,[z0,z1,z602,z2,z4,z5,z6])],[(0,[z685,z0,z1,z2,z4,z5,z6]),(0,[z0,z686,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z180,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z687,z6]),(0,[z0,z1,z2,z4,z14,z6,z109])],[(0,[z0,z1,z2,z688,z4,z5,z6]),(0,[z0,z1,z689,z2,z4,z5,z6])],[(0,[z690,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z691,z5,z6]),(0,[z0,z1,z692,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z693,z6])],[(0,[z0,z1,z2,z4,z5,z6,z694]),(0,[z0,z1,z2,z4,z5,z6,z695]),(0,[z0,z145,z1,z2,z4,z14,z6]),(0,[z0,z147,z2,z4,z5,z14,z6])],[(0,[z0,z1,z2,z4,z696,z5,z6]),(1,[z0,z1,z2,z170,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z697]),(0,[z0,z157,z1,z400,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z698,z6]),(0,[z0,z1,z699,z2,z4,z5,z6]),(0,[z0,z1,z700,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z14,z6,z168]),(0,[z701,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z163,z24,z4,z5,z6]),(1,[z0,z1,z602,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z702])],[(0,[z152,z1,z102,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z703,z5,z6]),(0,[z0,z1,z54,z2,z4,z5,z6]),(0,[z0,z153,z1,z273,z2,z4,z6])],[(0,[z0,z1,z704,z2,z4,z5,z6]),(0,[z0,z1,z705,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z151,z94,z102,z2,z4,z5]),(0,[z0,z1,z707,z2,z5,z6]),(0,[z708,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z709,z5,z6]),(0,[z0,z1,z4,z710,z6,z109]),(0,[z0,z1,z711,z2,z60,z5])],[(0,[z0,z1,z712,z4,z5,z6]),(1,[z0,z713,z4,z5,z6]),(0,[z0,z1,z714,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z715]),(0,[z0,z435,z2,z170,z5,z6]),(0,[z404,z1,z2,z4,z5,z65]),(0,[z0,z145,z2,z4,z146,z6]),(0,[z0,z1,z163,z5,z6,z100]),(0,[z0,z1,z716,z4,z5,z6])]],
   [[],[(0,[z0,z1,z2,z717,z5,z6]),(0,[z0,z1,z2,z4,z5,z718]),(0,[z0,z1,z211,z4,z6,z109])],[(0,[z0,z1,z2,z719,z5,z6]),(0,[z0,z1,z192,z19,z5,z6]),(0,[z0,z96,z2,z47,z58,z6]),(0,[z720,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z721,z288,z6])],[(0,[z0,z1,z722,z4,z5,z6]),(0,[z0,z1,z2,z723,z5,z6]),(0,[z0,z1,z2,z4,z724,z6]),(0,[z0,z725,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z726]),(0,[z0,z1,z2,z4,z727,z6]),(0,[z0,z1,z2,z4,z5,z315]),(0,[z235,z1,z2,z4,z5,z122]),(0,[z282,z2,z4,z5,z14,z6]),(0,[z0,z1,z28,z4,z14,z6]),(0,[z0,z1,z705,z25,z5,z6])]],
   [[(0,[z0,z281,z2,z4,z14,z6]),(0,[z728,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z729,z6]),(0,[z0,z1,z130,z50,z27,z6])],[(0,[z0,z421,z2,z4,z5,z6]),(0,[z0,z730,z2,z4,z5,z6]),(0,[z0,z1,z2,z731,z5,z6]),(0,[z0,z1,z2,z4,z732,z6]),(0,[z0,z1,z713,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z135]),(0,[z0,z1,z2,z4,z5,z733]),(1,[z0,z1,z711,z2,z5])],[(0,[z0,z2,z4,z734,z5,z6])],[(0,[z0,z735,z2,z4,z5,z6]),(0,[z0,z157,z158,z4,z342,z6]),(0,[z0,z1,z2,z4,z736,z6]),(0,[z0,z1,z2,z4,z737,z6]),(0,[z0,z1,z28,z4,z146,z6]),(0,[z738,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z214,z2,z4,z5,z6]),(0,[z105,z1,z2,z39,z5,z6]),(0,[z0,z1,z739,z4,z5,z6]),(0,[z0,z2,z4,z734,z14,z6]),(0,[z0,z1,z2,z326,z14,z6]),(0,[z0,z2,z4,z146,z734,z6]),(0,[z0,z1,z24,z472,z5,z6])],[(0,[z0,z1,z2,z740,z5,z6]),(0,[z0,z536,z2,z4,z5,z117]),(0,[z0,z1,z50,z2,z721,z6])],[(0,[z0,z435,z2,z44,z5,z6]),(0,[z0,z1,z2,z4,z52,z6]),(0,[z0,z2,z4,z5,z741,z6])],[(0,[z483,z102,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z742,z6]),(0,[z0,z1,z333,z4,z5,z6]),(0,[z0,z1,z2,z4,z743,z6]),(0,[z0,z1,z459,z5,z6,z90]),(0,[z0,z1,z2,z4,z532,z181]),(0,[z0,z744,z2,z4,z5,z6])]],
   [[(0,[z193,z1,z108,z4,z5,z6]),(0,[z0,z619,z1,z273,z2,z4]),(0,[z0,z1,z2,z326,z146,z6])],[(0,[z79,z1,z2,z4,z5,z122]),(0,[z0,z1,z569,z5,z6,z90]),(0,[z0,z1,z2,z745,z5,z6])],[(1,[z746,z2,z4,z5,z6]),(0,[z0,z1,z2,z747,z5,z6]),(0,[z0,z1,z2,z4,z748,z6]),(0,[z0,z1,z749,z4,z5,z6]),(0,[z0,z116,z271,z2,z4,z5]),(0,[z750,z1,z2,z4,z5,z6]),(0,[z0,z1,z41,z27,z2,z6])],[(0,[z0,z1,z652,z5,z6,z90]),(0,[z0,z1,z751,z4,z5,z6]),(1,[z282,z2,z4,z5,z107]),(0,[z0,z1,z2,z4,z752,z6]),(0,[z0,z1,z2,z753,z5,z6])]],
   [[(0,[z0,z1,z754,z2,z4,z6]),(0,[z0,z1,z54,z463,z4,z6]),(0,[z121,z51,z2,z4,z5,z122])],[(0,[z138,z1,z2,z203,z5,z6]),(0,[z0,z1,z2,z755,z5,z6])],[(0,[z0,z1,z2,z223,z6,z168]),(0,[z0,z1,z239,z170,z5,z6]),(0,[z282,z1,z2,z4,z5,z117]),(0,[z0,z202,z1,z61,z2,z5])],[(0,[z623,z102,z2,z4,z5,z6]),(0,[z0,z1,z34,z4,z5,z35]),(0,[z0,z1,z2,z721,z6,z168]),(0,[z0,z1,z27,z2,z721,z6])]],
   [[(0,[z282,z1,z2,z4,z5,z6]),(0,[z560,z1,z108,z4,z5,z6]),(0,[z138,z1,z2,z731,z5,z6]),(0,[z0,z1,z2,z4,z756,z6]),(0,[z0,z1,z2,z757,z5,z6])],[(0,[z197,z1,z2,z4,z5,z508]),(0,[z0,z1,z2,z19,z5,z6]),(0,[z0,z147,z397,z2,z4,z5]),(0,[z0,z116,z2,z4,z5,z718]),(0,[z0,z1,z711,z2,z5,z6])],[(0,[z0,z1,z2,z4,z342,z6]),(0,[z0,z1,z353,z2,z4,z5]),(0,[z0,z1,z2,z4,z710,z6])],[(0,[z0,z1,z758,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z759]),(0,[z1,z2,z4,z5,z760,z122]),(0,[z0,z116,z2,z4,z5,z131])]],
   [[(0,[z0,z761,z1,z2,z4,z5]),(0,[z0,z157,z158,z4,z290,z6]),(0,[z0,z713,z158,z4,z5,z6]),(0,[z762,z1,z2,z4,z5,z6]),(0,[z0,z1,z763,z4,z5,z6]),(0,[z0,z764,z2,z4,z5,z6])],[(0,[z51,z2,z4,z5,z6,z122])],[(0,[z1,z102,z2,z4,z5,z508]),(0,[z0,z765,z2,z4,z5,z6]),(0,[z121,z282,z1,z2,z4,z5]),(0,[z766,z1,z2,z4,z5,z6]),(0,[z0,z2,z133,z767,z5,z6]),(0,[z1,z2,z4,z5,z6,z768]),(0,[z0,z1,z769,z4,z5,z6])],[(0,[z0,z1,z2,z770,z5,z6]),(0,[z0,z1,z2,z520,z6,z168]),(0,[z0,z1,z273,z2,z4,z98]),(0,[z0,z1,z2,z771,z4,z5])]],
   [[(1,[z102,z2,z4,z5,z508]),(0,[z0,z1,z50,z320,z2,z6]),(0,[z20,z435,z2,z4,z139,z6]),(0,[z0,z1,z43,z771,z4,z5])],[(0,[z0,z1,z2,z4,z5,z772]),(0,[z0,z1,z773,z2,z4,z5]),(0,[z0,z435,z2,z4,z5,z21]),(0,[z0,z1,z239,z44,z5,z6]),(0,[z774,z1,z2,z4,z5,z6]),(0,[z0,z775,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z776,z4,z6]),(0,[z0,z1,z2,z4,z5,z777]),(0,[z1,z2,z4,z71,z778,z6]),(0,[z0,z779,z2,z4,z5,z6])],[(0,[z0,z1,z2,z170,z5,z6]),(1,[z1,z2,z731,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z780,z6]),(0,[z0,z242,z2,z4,z5,z6]),(0,[z0,z1,z602,z2,z5,z6])],[(0,[z102,z2,z4,z5,z6,z508]),(0,[z0,z1,z781,z2,z4,z6]),(0,[z0,z1,z782,z4,z5,z6]),(0,[z0,z783,z2,z4,z5,z6]),(0,[z0,z1,z602,z5,z6,z109]),(0,[z0,z1,z784,z4,z5,z6])],[(0,[z0,z101,z2,z4,z5,z14]),(0,[z0,z2,z767,z4,z5,z6]),(0,[z0,z1,z638,z4,z6,z109])],[(0,[z0,z1,z2,z4,z785,z6]),(0,[z0,z1,z786,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z787]),(0,[z20,z1,z333,z4,z139,z6]),(0,[z70,z1,z2,z4,z778,z6]),(0,[z0,z145,z2,z4,z146,z135]),(0,[z0,z1,z788,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z789,z4,z5]),(0,[z0,z1,z790,z4,z5,z6]),(0,[z0,z1,z791,z4,z5,z6]),(0,[z0,z1,z792,z4,z5,z6]),(0,[z0,z1,z793,z4,z5,z6]),(0,[z0,z1,z333,z4,z5,z21]),(0,[z0,z794,z2,z4,z5,z6]),(0,[z795,z1,z2,z4,z5,z6])],[(0,[z0,z1,z796,z4,z5,z6]),(0,[z1,z797,z192,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z798]),(0,[z0,z1,z799,z4,z5,z6]),(1,[z0,z2,z4,z734,z6]),(0,[z0,z1,z2,z4,z430,z181])],[(0,[z0,z1,z800,z2,z4,z5]),(0,[z0,z1,z801,z4,z5,z6]),(0,[z152,z1,z2,z4,z5,z37]),(0,[z0,z802,z2,z4,z5,z6]),(0,[z0,z435,z2,z4,z5,z315]),(0,[z0,z1,z24,z25,z5,z6]),(0,[z0,z803,z2,z4,z5,z6]),(1,[z0,z1,z804,z2,z4])],[(0,[z0,z1,z2,z4,z805,z6]),(1,[z1,z797,z4,z5,z6]),(0,[z1,z2,z4,z5,z760,z6]),(0,[z0,z1,z2,z4,z290,z6]),(1,[z0,z2,z767,z5,z6]),(0,[z147,z282,z2,z4,z5,z107])]],
   [[(0,[z0,z806,z1,z2,z4,z5]),(0,[z89,z1,z192,z19,z5,z6]),(0,[z0,z807,z2,z4,z5,z6]),(0,[z0,z1,z2,z808,z5,z6]),(0,[z0,z1,z809,z4,z5,z6]),(1,[z1,z2,z4,z5,z760]),(0,[z282,z116,z2,z4,z5,z6]),(0,[z0,z1,z2,z810,z5,z6]),(0,[z0,z1,z34,z771,z4,z5])],[(0,[z0,z1,z2,z4,z811,z6]),(0,[z0,z1,z2,z4,z5,z812]),(0,[z0,z1,z2,z4,z5,z813]),(1,[z0,z1,z4,z710,z6]),(0,[z0,z1,z211,z4,z710,z6]),(0,[z0,z1,z804,z2,z4,z180])],[(0,[z0,z2,z4,z5,z814,z6]),(0,[z0,z1,z2,z815,z4,z5]),(0,[z0,z13,z2,z4,z734,z6])],[(0,[z89,z1,z192,z156,z5,z6]),(0,[z0,z1,z33,z4,z6,z109]),(0,[z0,z1,z816,z2,z5,z6]),(0,[z0,z817,z2,z4,z5,z6])]],
   [[(0,[z275,z1,z2,z39,z5,z6]),(0,[z0,z1,z2,z4,z5,z818]),(0,[z0,z819,z1,z2,z4,z5])],[(0,[z101,z1,z2,z4,z5,z122]),(0,[z0,z1,z820,z4,z5,z6]),(0,[z0,z1,z333,z4,z5,z315]),(0,[z0,z1,z821,z4,z5,z6]),(0,[z0,z1,z2,z4,z822,z6]),(0,[z0,z1,z2,z4,z5,z823]),(0,[z0,z1,z4,z710,z5,z6])],[(0,[z0,z1,z824,z2,z4,z5]),(0,[z0,z1,z825,z4,z5,z6]),(0,[z0,z435,z333,z4,z5,z6]),(0,[z0,z1,z2,z767,z5,z6]),(0,[z0,z1,z2,z4,z5,z826]),(1,[z0,z1,z771,z4,z5])],[(0,[z0,z1,z2,z827,z5,z6]),(0,[z20,z1,z239,z4,z139,z6]),(0,[z0,z1,z2,z4,z828,z6]),(0,[z0,z1,z829,z2,z4,z5])]],
   [[(0,[z701,z1,z192,z4,z5,z6]),(0,[z0,z1,z830,z4,z5,z6]),(0,[z0,z1,z239,z4,z5,z21]),(0,[z0,z1,z831,z2,z5,z6]),(0,[z0,z132,z2,z133,z5,z6]),(0,[z0,z1,z2,z4,z5,z832]),(0,[z833,z1,z2,z4,z5,z6]),(0,[z0,z1,z54,z602,z55,z6])],[(0,[z0,z1,z2,z4,z5,z834]),(0,[z590,z1,z2,z4,z5,z6]),(0,[z610,z106,z2,z4,z5,z6]),(0,[z498,z1,z2,z4,z5,z65])],[(0,[z0,z1,z2,z4,z5,z835]),(0,[z0,z1,z2,z836,z5,z6]),(0,[z0,z837,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z838]),(0,[z0,z839,z2,z4,z5,z6]),(0,[z0,z1,z840,z4,z5,z6]),(0,[z0,z96,z2,z47,z5,z6]),(0,[z0,z1,z2,z4,z841,z6]),(0,[z0,z1,z50,z2,z549,z6])],[(0,[z0,z267,z2,z4,z146,z6]),(1,[z0,z1,z2,z721,z6])]],
   [[(0,[z0,z842,z2,z4,z5,z6]),(0,[z0,z1,z843,z4,z5,z6]),(0,[z152,z1,z2,z4,z5,z760]),(0,[z0,z153,z1,z273,z2,z4]),(0,[z0,z1,z273,z804,z2,z4])],[(0,[z0,z1,z2,z844,z5,z6]),(0,[z197,z746,z2,z4,z5,z6]),(0,[z105,z1,z192,z4,z5,z6]),(0,[z38,z1,z82,z39,z5,z6]),(0,[z0,z1,z2,z4,z5,z845])],[(0,[z0,z1,z846,z4,z5,z6]),(0,[z0,z847,z2,z4,z5,z6]),(0,[z0,z848,z2,z4,z5,z6]),(0,[z849,z1,z2,z4,z5,z6]),(0,[z0,z1,z850,z2,z4,z5]),(0,[z0,z86,z2,z4,z14,z6])],[(0,[z0,z746,z2,z4,z5,z6]),(0,[z38,z1,z95,z39,z5,z6]),(0,[z20,z1,z2,z170,z139,z6]),(1,[z0,z2,z4,z5,z718]),(0,[z0,z851,z2,z4,z5,z6]),(0,[z0,z1,z163,z343,z5,z6]),(0,[z0,z1,z852,z2,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z853,z6]),(0,[z0,z1,z2,z4,z5,z854]),(0,[z0,z1,z2,z170,z5,z21]),(0,[z0,z282,z2,z4,z5,z107])],[(0,[z0,z106,z2,z4,z5,z508]),(0,[z0,z1,z239,z4,z5,z315]),(0,[z0,z855,z2,z4,z5,z6]),(0,[z0,z856,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z857,z6]),(0,[z0,z1,z163,z5,z6,z90]),(0,[z0,z1,z2,z858,z5,z6])],[(0,[z0,z1,z2,z859,z5,z6]),(0,[z0,z1,z95,z39,z5,z6]),(0,[z0,z1,z2,z4,z860,z6])],[(0,[z151,z102,z2,z4,z5,z221]),(0,[z0,z1,z2,z861,z4,z6]),(0,[z0,z145,z2,z4,z663,z6]),(0,[z0,z421,z239,z4,z5,z6]),(0,[z0,z862,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z863,z6]),(0,[z0,z1,z294,z5,z6,z90])]],
   [[(0,[z0,z1,z2,z4,z5,z221]),(0,[z0,z1,z864,z4,z5,z6]),(0,[z0,z1,z2,z865,z5,z6]),(0,[z433,z1,z108,z4,z5,z6]),(0,[z1,z51,z2,z4,z5,z122]),(0,[z1,z2,z4,z5,z6,z866])],[(0,[z0,z147,z51,z2,z4,z5]),(0,[z0,z400,z713,z4,z5,z6]),(0,[z0,z1,z2,z867,z5,z6]),(0,[z0,z269,z2,z4,z5,z181])],[(1,[z1,z2,z4,z778,z6]),(0,[z0,z868,z1,z2,z4,z5]),(1,[z51,z2,z4,z5,z122]),(0,[z1,z2,z4,z5,z65,z760]),(0,[z0,z1,z2,z4,z869,z6]),(0,[z0,z157,z713,z4,z5,z6]),(0,[z0,z1,z2,z4,z870,z6]),(0,[z0,z1,z871,z4,z5,z6]),(0,[z0,z1,z872,z4,z5,z6]),(0,[z0,z1,z28,z4,z5,z6]),(0,[z0,z1,z130,z50,z5,z6])],[(0,[z0,z1,z2,z873,z5,z6]),(0,[z0,z1,z2,z4,z5,z874]),(0,[z0,z1,z2,z721,z5,z6]),(0,[z0,z1,z875,z4,z5,z6])]],
   [[(0,[z0,z876,z1,z2,z4,z5]),(0,[z1,z2,z731,z39,z5,z6]),(0,[z0,z1,z877,z4,z5,z6]),(0,[z0,z147,z2,z4,z5,z718]),(0,[z0,z878,z2,z4,z5,z6])],[(0,[z0,z435,z2,z4,z5,z6]),(0,[z0,z145,z101,z2,z4,z5]),(0,[z0,z1,z879,z2,z4,z6]),(0,[z446,z1,z2,z203,z5,z6]),(0,[z0,z1,z2,z170,z5,z315]),(0,[z0,z1,z880,z2,z5,z6]),(0,[z0,z1,z881,z4,z5,z6]),(0,[z0,z1,z882,z5,z6,z90]),(0,[z0,z883,z2,z4,z5,z6]),(0,[z0,z269,z153,z273,z2,z4])],[(0,[z0,z1,z2,z4,z5,z884]),(0,[z20,z1,z2,z44,z139,z6]),(0,[z0,z1,z2,z885,z5,z6]),(0,[z0,z1,z2,z886,z5,z6]),(0,[z0,z1,z2,z887,z5,z6]),(0,[z0,z147,z2,z4,z5,z107]),(0,[z0,z1,z888,z4,z5,z6])],[(0,[z1,z2,z797,z4,z5,z6]),(0,[z0,z421,z2,z170,z5,z6]),(0,[z0,z1,z2,z44,z5,z21]),(0,[z0,z1,z2,z4,z5,z889]),(0,[z0,z1,z2,z890,z4,z5]),(0,[z0,z1,z891,z4,z5,z6]),(0,[z0,z1,z2,z326,z5,z6]),(0,[z0,z1,z2,z4,z180,z181])]],
   [[(0,[z197,z106,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z892]),(0,[z0,z1,z893,z2,z5,z6]),(0,[z0,z894,z2,z4,z5,z6]),(0,[z0,z1,z895,z4,z5,z6]),(0,[z152,z1,z2,z4,z5,z65]),(0,[z0,z145,z2,z4,z734,z6]),(0,[z0,z2,z4,z5,z718,z107]),(0,[z0,z2,z4,z5,z6,z718]),(0,[z0,z896,z2,z4,z5,z6]),(0,[z0,z1,z61,z711,z2,z5])],[(0,[z0,z1,z2,z897,z5,z6]),(0,[z0,z102,z2,z4,z5,z508]),(0,[z151,z746,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z898]),(0,[z38,z1,z2,z731,z5,z6]),(0,[z0,z899,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z900,z6]),(0,[z901,z1,z2,z4,z5,z6]),(0,[z902,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z903]),(0,[z0,z623,z2,z4,z5,z107]),(0,[z0,z269,z2,z4,z5,z6]),(0,[z282,z1,z2,z4,z5,z181])]],
   [[(0,[z0,z904,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z117,z718])],[(0,[z0,z1,z905,z4,z5,z6]),(0,[z0,z1,z333,z170,z5,z6]),(0,[z0,z1,z2,z288,z6,z168])],[(0,[z0,z353,z2,z4,z5,z14])],[(0,[z0,z1,z906,z4,z5,z6]),(0,[z0,z1,z2,z4,z907,z6]),(0,[z0,z1,z908,z4,z5,z6]),(0,[z909,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z910,z6]),(0,[z0,z1,z911,z4,z5,z6]),(0,[z0,z1,z2,z44,z5,z315]),(0,[z0,z1,z2,z912,z5,z6]),(0,[z264,z1,z2,z4,z5,z122]),(0,[z913,z1,z2,z4,z5,z6])],[(0,[z264,z102,z2,z4,z5,z6]),(0,[z101,z282,z1,z2,z4,z5]),(0,[z106,z746,z2,z4,z5,z6]),(0,[z358,z1,z2,z203,z5,z6]),(0,[z0,z96,z2,z767,z5,z6]),(0,[z0,z1,z2,z4,z5,z914])],[(0,[z0,z101,z1,z2,z4,z5]),(0,[z0,z1,z2,z915,z5,z6]),(0,[z0,z421,z2,z44,z5,z6])],[(0,[z0,z1,z916,z2,z5,z6]),(0,[z0,z1,z917,z2,z4,z5]),(0,[z0,z918,z2,z4,z5,z6]),(0,[z0,z1,z2,z919,z5,z6]),(0,[z0,z116,z51,z2,z4,z5]),(0,[z0,z1,z163,z174,z5,z6])]],
   [[(0,[z0,z1,z797,z4,z5,z6]),(0,[z0,z1,z711,z2,z5,z212])],[(0,[z0,z101,z116,z2,z4,z5]),(0,[z0,z920,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z760]),(0,[z0,z1,z2,z921,z4,z6]),(0,[z0,z1,z24,z882,z5,z6]),(0,[z0,z1,z54,z4,z710,z6]),(0,[z0,z1,z922,z4,z5,z6])],[(0,[z0,z1,z2,z4,z923,z5]),(0,[z0,z1,z63,z25,z5,z6]),(0,[z0,z157,z158,z4,z5,z6]),(0,[z0,z1,z439,z55,z4,z6]),(0,[z0,z202,z1,z711,z2,z5])],[(0,[z151,z102,z2,z4,z5,z508]),(0,[z0,z101,z51,z2,z4,z5]),(0,[z0,z1,z2,z4,z924,z6]),(0,[z0,z1,z925,z4,z5,z6]),(0,[z0,z1,z25,z882,z5,z6]),(0,[z0,z1,z804,z2,z4,z181])]],
   [[(0,[z0,z1,z2,z4,z5,z508]),(0,[z0,z1,z926,z2,z4,z6]),(0,[z0,z1,z927,z4,z5,z6]),(0,[z0,z1,z108,z19,z5,z6]),(0,[z0,z1,z239,z4,z5,z6]),(0,[z0,z1,z928,z4,z5,z6]),(0,[z0,z1,z333,z44,z5,z6]),(0,[z152,z282,z1,z2,z4,z5]),(0,[z0,z929,z2,z4,z5,z6]),(0,[z0,z930,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z931]),(0,[z0,z116,z2,z4,z5,z687]),(0,[z0,z1,z2,z156,z5,z6]),(0,[z20,z1,z2,z4,z139,z21]),(0,[z0,z932,z1,z2,z4,z5]),(0,[z590,z147,z2,z4,z5,z107]),(0,[z0,z1,z2,z4,z933,z6]),(0,[z0,z1,z771,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z934]),(0,[z0,z1,z130,z4,z5,z6])],[(0,[z0,z1,z2,z935,z5,z6]),(0,[z0,z1,z936,z4,z5,z6])]],
   [[(0,[z0,z101,z2,z4,z5,z107]),(0,[z0,z1,z95,z203,z5,z6]),(0,[z0,z1,z2,z4,z5,z937]),(0,[z938,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z939]),(0,[z0,z1,z940,z4,z5,z6]),(0,[z0,z153,z1,z804,z2,z4])],[(0,[z0,z1,z941,z4,z5,z6]),(0,[z746,z102,z2,z4,z5,z6]),(0,[z197,z461,z2,z4,z5,z6]),(0,[z0,z942,z2,z4,z5,z6]),(0,[z152,z51,z2,z4,z5,z6]),(0,[z0,z2,z767,z47,z5,z6]),(0,[z0,z504,z2,z4,z146,z6]),(0,[z0,z1,z2,z882,z5,z6]),(0,[z0,z1,z50,z27,z2,z6]),(0,[z0,z1,z943,z4,z5,z6]),(0,[z0,z153,z242,z273,z2,z4])],[(0,[z0,z1,z2,z944,z5,z6]),(0,[z70,z1,z2,z4,z71,z6]),(0,[z0,z1,z2,z4,z945,z6]),(0,[z0,z96,z2,z47,z52,z6]),(0,[z0,z1,z50,z27,z28,z6])]],
   [[(0,[z0,z1,z2,z946,z5,z6]),(0,[z0,z947,z2,z4,z5,z6]),(0,[z0,z1,z948,z4,z5,z6]),(0,[z0,z1,z4,z882,z5,z6]),(0,[z0,z1,z2,z60,z5,z212]),(0,[z0,z1,z804,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z949]),(0,[z134,z106,z2,z4,z5,z6]),(0,[z0,z950,z2,z4,z5,z6]),(0,[z0,z1,z2,z951,z5,z6]),(0,[z0,z1,z2,z952,z5,z6]),(0,[z0,z1,z55,z4,z710,z6]),(0,[z0,z1,z54,z602,z5,z6]),(0,[z0,z1,z804,z2,z4,z6])],[(0,[z0,z1,z2,z953,z5,z6]),(0,[z20,z1,z2,z4,z139,z315]),(0,[z0,z1,z567,z4,z6,z109]),(0,[z0,z954,z2,z4,z5,z6])],[(0,[z0,z1,z54,z55,z4,z6])]],
   [[(0,[z151,z102,z2,z4,z5,z6]),(0,[z0,z1,z955,z4,z5,z6]),(0,[z0,z1,z956,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z957]),(0,[z20,z421,z2,z4,z139,z6]),(0,[z0,z2,z713,z4,z5,z6]),(0,[z0,z1,z54,z55,z326,z6])],[(0,[z38,z1,z2,z39,z5,z6]),(0,[z0,z421,z2,z4,z5,z21]),(0,[z958,z1,z2,z4,z5,z6]),(0,[z0,z13,z2,z4,z14,z6])],[(0,[z0,z1,z2,z4,z959,z6]),(0,[z0,z1,z2,z960,z5,z6]),(0,[z151,z101,z102,z2,z4,z5]),(0,[z0,z961,z2,z4,z5,z6]),(0,[z0,z177,z713,z4,z5,z6])],[(0,[z0,z1,z2,z962,z5,z6]),(0,[z0,z559,z2,z4,z14,z6]),(0,[z0,z2,z4,z5,z963,z6]),(0,[z0,z42,z1,z771,z4,z5])]],
   [[(0,[z331,z0,z2,z4,z5,z107]),(0,[z0,z1,z2,z964,z5,z6]),(0,[z121,z214,z2,z4,z5,z122]),(0,[z0,z1,z2,z965,z5,z6]),(0,[z0,z1,z2,z4,z5,z966]),(0,[z0,z967,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z968,z6]),(0,[z0,z1,z2,z721,z4,z6])],[(0,[z102,z2,z4,z5,z122,z107]),(0,[z0,z969,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z970,z6]),(0,[z1,z2,z4,z5,z778,z6]),(0,[z0,z147,z2,z4,z5,z367]),(0,[z0,z1,z2,z971,z5,z6]),(0,[z0,z1,z2,z972,z5,z6]),(0,[z0,z42,z1,z43,z4,z5]),(0,[z0,z269,z273,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z973]),(0,[z0,z1,z2,z44,z5,z6]),(0,[z0,z1,z2,z4,z778,z6]),(0,[z0,z51,z2,z4,z5,z122]),(0,[z0,z177,z400,z4,z5,z6]),(0,[z974,z1,z2,z4,z5,z6]),(0,[z0,z147,z506,z2,z4,z5]),(0,[z0,z1,z163,z621,z5,z6]),(0,[z0,z975,z2,z4,z5,z6]),(0,[z0,z1,z976,z2,z4,z6])]],
   [[(0,[z0,z94,z1,z2,z4,z5]),(0,[z0,z1,z2,z977,z5,z6]),(0,[z0,z132,z2,z767,z5,z6]),(0,[z0,z1,z54,z4,z549,z6])],[(0,[z746,z1,z2,z4,z5,z6])],[(0,[z0,z421,z2,z4,z5,z315])],[(0,[z0,z1,z978,z2,z4,z6]),(0,[z0,z1,z2,z4,z979,z6]),(0,[z0,z145,z353,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z980,z4,z5]),(0,[z0,z981,z2,z4,z5,z6]),(0,[z0,z1,z982,z4,z5,z6]),(0,[z0,z279,z2,z4,z14,z6])],[(0,[z0,z2,z4,z5,z983,z6]),(1,[z0,z1,z882,z5,z6])],[(0,[z0,z1,z2,z4,z984,z5]),(0,[z0,z1,z985,z4,z5,z6]),(0,[z0,z1,z2,z4,z58,z6]),(0,[z0,z145,z2,z4,z98,z6]),(0,[z0,z1,z2,z426,z6,z168])],[(0,[z0,z986,z2,z4,z5,z6]),(0,[z1,z108,z797,z4,z5,z6]),(0,[z0,z1,z24,z672,z5,z6]),(0,[z0,z1,z2,z4,z734,z6])]],
   [[(0,[z0,z987,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z988,z6]),(0,[z0,z147,z2,z4,z5,z256]),(0,[z282,z1,z273,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z989]),(0,[z0,z1,z2,z990,z5,z6]),(0,[z0,z991,z1,z2,z4,z5])],[(0,[z0,z1,z82,z4,z5,z6]),(0,[z0,z421,z333,z4,z5,z6]),(0,[z0,z1,z992,z4,z5,z6]),(0,[z145,z282,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z993]),(0,[z466,z102,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z994]),(0,[z282,z1,z2,z4,z5,z107]),(0,[z0,z116,z2,z4,z5,z117])]],
   [[(0,[z152,z101,z1,z2,z4,z5]),(0,[z89,z1,z192,z4,z5,z6]),(0,[z0,z1,z2,z995,z5,z6]),(0,[z0,z1,z95,z4,z5,z6]),(0,[z1,z2,z4,z778,z139,z6]),(0,[z0,z1,z163,z882,z5,z6])],[(0,[z0,z996,z1,z2,z4,z5]),(0,[z997,z1,z2,z4,z5,z6]),(0,[z0,z218,z2,z4,z5,z117])],[(0,[z152,z116,z102,z2,z4,z5]),(0,[z0,z1,z2,z4,z998,z6]),(0,[z89,z1,z797,z4,z5,z6])],[(0,[z0,z51,z2,z4,z5,z6]),(0,[z0,z1,z2,z999,z5,z6]),(0,[z0,z435,z239,z4,z5,z6]),(0,[z0,z1,z1000,z4,z5,z6]),(0,[z0,z51,z2,z4,z5,z65]),(0,[z152,z510,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1001]),(0,[z0,z1,z1002,z2,z5,z6]),(0,[z0,z145,z353,z2,z4,z146]),(0,[z0,z1,z130,z5,z6,z168]),(0,[z0,z1,z711,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z4,z5,z1003]),(0,[z1,z2,z203,z731,z5,z6]),(0,[z1004,z1,z2,z4,z5,z6])],[(0,[z193,z1,z797,z4,z5,z6]),(0,[z20,z1,z2,z4,z139,z6]),(0,[z0,z1,z2,z1005,z5,z6]),(0,[z0,z1,z1006,z4,z5,z6]),(0,[z282,z2,z4,z5,z6,z107])],[(0,[z0,z1,z2,z4,z5,z1007]),(0,[z1,z2,z4,z731,z5,z6]),(0,[z0,z1,z2,z4,z5,z21]),(0,[z20,z1,z2,z4,z778,z6]),(0,[z121,z1,z2,z4,z5,z122]),(0,[z121,z1,z2,z4,z5,z760]),(0,[z0,z1,z2,z1008,z5,z6]),(0,[z0,z1,z771,z4,z5,z35])],[(0,[z0,z1,z1009,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1010]),(0,[z0,z1011,z2,z4,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 4 128 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 560) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 560).take 426) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 986)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [560, 426] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 103).take 25).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [103, 25] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 4) (nb2 := 128) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_41506

theorem PEqualNP.Outside.L_meta_41506 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4205496448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4205496448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41506.solve