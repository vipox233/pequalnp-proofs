import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36334

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277061824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x08004045604c63c0#64 ++ 0x108004045604c63c#64 ++ 0xf414c0cfe0dce7cd#64 ++ 0xdf414c0cfe0dce7c#64 : BitVec 256),
   (0x9001031301050d50#64 ++ 0x09001031301050d5#64 ++ 0xee2b073303273fff#64 ++ 0xfee2b073303273ff#64 : BitVec 256),
   (0x204c582c2c3830a0#64 ++ 0x9204c582c2c3830a#64 ++ 0x5fcc783c3c3838fb#64 ++ 0xb5fcc783c3c3838f#64 : BitVec 256),
   (0xc1b06dc037c03e05#64 ++ 0x1c1b06dc037c03e0#64 ++ 0x3df07fc03fc03f07#64 ++ 0x73df07fc03fc03f0#64 : BitVec 256),
   (0x00fe80001ab28006#64 ++ 0x200fe80001ab2800#64 ++ 0xffff80003fffc00f#64 ++ 0x0ffff80003fffc00#64 : BitVec 256),
   (0x00ffb6ba80000007#64 ++ 0xc00ffb6ba8000000#64 ++ 0xfcffffffc0000000#64 ++ 0xffcffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff80003fffc00f 0x0ffff80003fffc00

def z1 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xffffffffffffc00f 0xfffffffffffffc00

def z2 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xf414c0cfe0dce7cd 0xdf414c0cfe0dce7c

def z3 : W := mkw 0x20004804240830a0 0x120004804240830a 0x00000000000038f0 0x000000000000038f

def z4 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x5fcc783c3c3838fb 0xb5fcc783c3c3838f

def z5 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xee2b073303273fff 0xfee2b073303273ff

def z6 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3df07fc03fc03f07 0x73df07fc03fc03f0

def z7 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffc0000000 0xffcffffffc000000

def z8 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0x0beb3f301f230002 0x20beb3f301f23000

def z9 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0x00007fffc0000000 0xf00007fffc000000

def z10 : W := mkw 0x204c48042c3830a0 0x1204c48042c3830a 0x5fcc00003c3838fb 0x05fcc00003c3838f

def z11 : W := mkw 0xc1feedc03ff2be07 0x3c1feedc03ff2be0 0x3df4ffc03fd8ff07 0x73df4ffc03fd8ff0

def z12 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x5fcc780c3c38000b 0x05fcc780c3c38000

def z13 : W := mkw 0x0001021200000000 0x0000102120000000 0xec2b073300000000 0xfec2b07330000000

def z14 : W := mkw 0x00feb4a880000007 0xc00feb4a88000000 0x10d4f8ccc0000000 0x010d4f8ccc000000

def z15 : W := mkw 0x00feb4a89ab28007 0xe00feb4a89ab2800 0xfffff8ccffffc00f 0x0fffff8ccffffc00

def z16 : W := mkw 0x20fffebebebab0a7 0xf20fffebebebab0a 0xfffffffffffff8ff 0xffffffffffffff8f

def z17 : W := mkw 0x00b3a69280000007 0x400b3a6928000000 0xf437c7cfc0000000 0xdf437c7cfc000000

def z18 : W := mkw 0x00b0404032c02204 0x100b0404032c0220 0x3df040c03fc02707 0x53df040c03fc0270

def z19 : W := mkw 0x204c18280c301020 0x8204c18280c30102 0x0bc838301c201832 0x20bc838301c20183

def z20 : W := mkw 0x20fffebeac3830a7 0xd20fffebeac3830a 0xfffffffffc3838fb 0xffffffffffc3838f

def z21 : W := mkw 0x9801035341454f50 0x09801035341454f5 0xa03387c3c3c7c704 0x4a03387c3c3c7c70

def z22 : W := mkw 0x204c58282c303020 0x9204c58282c30302 0x1fc878303c203833 0x31fc878303c20383

def z23 : W := mkw 0x08000005400c41c0 0x008000005400c41c 0xc004800fc01cc0c8 0x8c004800fc01cc0c

def z24 : W := mkw 0xc1b02d8017801c05 0x0c1b02d8017801c0 0x09e03f001f001802 0x209e03f001f00180

def z25 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x1014c0cfe0d8e7c0 0xd1014c0cfe0d8e7c

def z26 : W := mkw 0x0000000000000000 0x0000000000000000 0xee2b00000327000f 0x0ee2b00000327000

def z27 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x11d07fc03cc03f00 0x711d07fc03cc03f0

def z28 : W := mkw 0x20017ebea40830a1 0xd20017ebea40830a 0x00007fffc00038f0 0xf00007fffc00038f

def z29 : W := mkw 0x9000010101050d50 0x09000010101050d5 0x0000000003070704 0x0000000000307070

def z30 : W := mkw 0x004e800008328002 0x2004e80000832800 0xdfcf80003c3fc00b 0x0dfcf80003c3fc00

def z31 : W := mkw 0x00b2800000000006 0x000b280000000000 0xa033800000000000 0x0a03380000000000

def z32 : W := mkw 0x00fe800000000006 0x000fe80000000000 0xfcffc0cfc0000000 0xdfcffc0cfc000000

def z33 : W := mkw 0x004e800008328002 0x2004e80000832800 0xc20f8000003fc008 0x0c20f8000003fc00

def z34 : W := mkw 0x00b0000012800004 0x000b000001280000 0x3df000003fc00007 0x03df000003fc0000

def z35 : W := mkw 0x0000000000000000 0x0000000000000000 0x3410000020c00005 0x03410000020c0000

def z36 : W := mkw 0x20fed82c3ebab0a6 0xb20fed82c3ebab0a 0xfffff83c3ffff8ff 0xbfffff83c3ffff8f

def z37 : W := mkw 0x90ff83131bb78d56 0x290ff83131bb78d5 0xffff87333fffffff 0xfffff87333ffffff

def z38 : W := mkw 0xc1feedc03ff2be07 0x3c1feedc03ff2be0 0xffffffc03fffff0f 0x7ffffffc03fffff0

def z39 : W := mkw 0xc9b06dc577cc7fc5 0x1c9b06dc577cc7fc 0xfdf4ffcfffdcffcf 0xffdf4ffcfffdcffc

def z40 : W := mkw 0x0000480024003000 0x1000048002400300 0x1dc078003c003803 0x31dc078003c00380

def z41 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0x0beb00001f230002 0x00beb00001f23000

def z42 : W := mkw 0x0001123a80000000 0xc0001123a8000000 0x0000003fc0000000 0x80000003fc000000

def z43 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x341040cfe0c027c5 0xd341040cfe0c027c

def z44 : W := mkw 0x084fd27fe04c63c2 0xd084fd27fe04c63c 0xf41fc0ffe0dce7cd 0xdf41fc0ffe0dce7c

def z45 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff80303ffff8ff 0xbffff80303ffff8f

def z46 : W := mkw 0x000000001ab28000 0x2000000001ab2800 0x030000003fffc00f 0x0030000003fffc00

def z47 : W := mkw 0x00fe800000000006 0x000fe80000000000 0xfcff800000000000 0x0fcff80000000000

def z48 : W := mkw 0xc900494577cc7fc0 0x1c900494577cc7fc 0x010000003fdcffcf 0x0010000003fdcffc

def z49 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0xffdcf83c3cfcf8ff 0xbffdcf83c3cfcf8f

def z50 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xffffffffdf230002 0xfffffffffdf23000

def z51 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0x11d480003cd8c000 0x011d480003cd8c00

def z52 : W := mkw 0x9001031301050d50 0x09001031301050d5 0x0000073300003ff0 0xf0000073300003ff

def z53 : W := mkw 0x0800004140444340 0x0080000414044434 0xa01080c3c0c4c704 0x4a01080c3c0c4c70

def z54 : W := mkw 0x98014357614d6fd0 0x198014357614d6fd 0xfe3fc7ffe3ffffff 0xffe3fc7ffe3fffff

def z55 : W := mkw 0xc1b06dc137c43f45 0x1c1b06dc137c43f4 0xfdf07fc33fc43fcf 0xffdf07fc33fc43fc

def z56 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xb014c0cfe0dcc704 0x4b014c0cfe0dcc70

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e080030002038fb 0xb4e080030002038f

def z58 : W := mkw 0xb04d5b3f2d3d3df0 0x9b04d5b3f2d3d3df 0xffef7f3f3f3f3fff 0xfffef7f3f3f3f3ff

def z59 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414800020dcc00d 0x0f414800020dcc00

def z60 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x000040cfc00027c0 0xd000040cfc00027c

def z61 : W := mkw 0xc1b3a7d293c00e07 0x4c1b3a7d293c00e0 0xa03387c3c3c00704 0x4a03387c3c3c0070

def z62 : W := mkw 0x00b2800012828006 0x200b280001282800 0xa033800003c7c004 0x0a033800003c7c00

def z63 : W := mkw 0xc100494025403e00 0x1c100494025403e0 0x0000000000003f00 0x00000000000003f0

def z64 : W := mkw 0x00b0248012800005 0x000b024801280000 0x3df07fc03fc00007 0x73df07fc03fc0000

def z65 : W := mkw 0x20fe98281eb29026 0xa20fe98281eb2902 0x0beb38301f231832 0x20beb38301f23183

def z66 : W := mkw 0x9001031301050d50 0x09001031301050d5 0x2c20073303003ff7 0xf2c20073303003ff

def z67 : W := mkw 0x0001021200000000 0x0000102120000000 0xc00b003300000000 0x8c00b00330000000

def z68 : W := mkw 0xc1b06dc437c83e85 0x1c1b06dc437c83e8 0x7df47fcc3fd83fcf 0xf7df47fcc3fd83fc

def z69 : W := mkw 0x0000404020402200 0x1000040402040220 0x341040c020c02705 0x5341040c020c0270

def z70 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x11c4780c3c180000 0x011c4780c3c18000

def z71 : W := mkw 0xd1ffefd33ff7bf57 0x3d1ffefd33ff7bf5 0xfffffff33fffffff 0xffffffff33ffffff

def z72 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0x08eb3f3000000000 0x208eb3f300000000

def z73 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x0000000020dce7cd 0x00000000020dce7c

def z74 : W := mkw 0x0000000000000000 0x0000000000000000 0x2400000000002705 0x5240000000000270

def z75 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xefeb00001f27000f 0x0efeb00001f27000

def z76 : W := mkw 0xe1fc3da81fb01c25 0x8e1fc3da81fb01c2 0x0be83f301f201832 0x20be83f301f20183

def z77 : W := mkw 0x080040457afee3c0 0x3080040457afee3c 0xf714c0cfffffe7cf 0xdf714c0cfffffe7c

def z78 : W := mkw 0xc1006dc025403e01 0x1c1006dc025403e0 0x00007fc000003f00 0x700007fc000003f0

def z79 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414c0cfc0000000 0xdf414c0cfc000000

def z80 : W := mkw 0x9001031301050d50 0x09001031301050d5 0x0a2b073003273fff 0x20a2b073003273ff

def z81 : W := mkw 0xc100090017801c00 0x0c100090017801c0 0x010000001f001802 0x0010000001f00180

def z82 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfeffffffc02038fb 0xffeffffffc02038f

def z83 : W := mkw 0x204d7ebeac3830a1 0xd204d7ebeac3830a 0x5fcc7ffffc3838fb 0xf5fcc7ffffc3838f

def z84 : W := mkw 0x00fe800000000006 0x000fe80000000000 0x10d4800000000000 0x010d480000000000

def z85 : W := mkw 0x9001031201010c10 0x09001031201010c1 0xee2b07300327183f 0x2ee2b07300327183

def z86 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xa010c0cfc0c4e7c4 0xda010c0cfc0c4e7c

def z87 : W := mkw 0x904d031309350d50 0x0904d031309350d5 0xffef07333f3f3fff 0xfffef07333f3f3ff

def z88 : W := mkw 0x284c586d6c7c73e0 0x9284c586d6c7c73e 0xffdcf8fffcfcffff 0xfffdcf8fffcfcfff

def z89 : W := mkw 0x20fed82c3ebab0a6 0xb20fed82c3ebab0a 0x5fdcf83c3cf8f8fb 0xb5fdcf83c3cf8f8f

def z90 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xfe1cc0ffe0fcffff 0xffe1cc0ffe0fcfff

def z91 : W := mkw 0x00b2800012828006 0x200b280001282800 0x0010800000c0c000 0x00010800000c0c00

def z92 : W := mkw 0x08000005400c41c0 0x008000005400c41c 0x0000000fc00000c0 0x80000000fc00000c

def z93 : W := mkw 0x9000010101050d50 0x09000010101050d5 0x0200000003273fff 0x00200000003273ff

def z94 : W := mkw 0x9001031201010c10 0x09001031201010c1 0x0a2b073003231832 0x20a2b07300323183

def z95 : W := mkw 0x00b0248000000005 0x000b024800000000 0x3cf07fc000000000 0x73cf07fc00000000

def z96 : W := mkw 0xc100494037c03e00 0x1c100494037c03e0 0x010000003fc03f07 0x0010000003fc03f0

def z97 : W := mkw 0x204c182c0c3810a0 0x8204c182c0c3810a 0x4bcc383c1c3818fa 0xa4bcc383c1c3818f

def z98 : W := mkw 0x00b3b6ba80000007 0xc00b3b6ba8000000 0xa033ffffc0000000 0xfa033ffffc000000

def z99 : W := mkw 0x304d123f083d01f0 0x8304d123f083d01f 0xc20f003f003f00f8 0x8c20f003f003f00f

def z100 : W := mkw 0x8000010001000c00 0x08000010001000c0 0x2c20070003003f07 0x72c20070003003f0

def z101 : W := mkw 0x004f923a88328002 0xe004f923a8832800 0xc20f803fc03fc008 0x8c20f803fc03fc00

def z102 : W := mkw 0x0000400420082080 0x1000040042008208 0x0000400c000020c0 0x90000400c000020c

def z103 : W := mkw 0xe1fefdec3ffabea7 0xbe1fefdec3ffabea 0xfffffffc3fffffff 0xffffffffc3ffffff

def z104 : W := mkw 0x9001031301050d50 0x09001031301050d5 0x4e08073300203ffb 0xf4e08073300203ff

def z105 : W := mkw 0x204c102808300020 0x8204c10280830002 0x0208003000200030 0x0020800300020003

def z106 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0x3ffb00003fe30007 0x03ffb00003fe3000

def z107 : W := mkw 0x90b1031313850d54 0x090b1031313850d5 0xfffb07333fe73fff 0xffffb07333fe73ff

def z108 : W := mkw 0x904d133b01050d50 0x8904d133b01050d5 0xfeef7f3f03273fff 0xffeef7f3f03273ff

def z109 : W := mkw 0x08fe80055abec1c6 0x208fe80055abec1c 0xffff800fffffc0cf 0x8ffff800fffffc0c

def z110 : W := mkw 0x0000000000000000 0x0000000000000000 0x1cc0780000000000 0x31cc078000000000

def z111 : W := mkw 0x204d5a3e2c3830a0 0x9204d5a3e2c3830a 0xffef7f3f3c3838fb 0xfffef7f3f3c3838f

def z112 : W := mkw 0x8000490025003c00 0x18000490025003c0 0x3de07f003f003f07 0x73de07f003f003f0

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0xee2b0030032738ff 0xbee2b0030032738f

def z114 : W := mkw 0x00ffb6ba92828007 0xe00ffb6ba9282800 0xfcffffffc3c7c004 0xffcffffffc3c7c00

def z115 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffffc0cfffffc00f 0xdffffc0cfffffc00

def z116 : W := mkw 0x080176ffe04c63c1 0xd080176ffe04c63c 0x00007fffc00027c0 0xf00007fffc00027c

def z117 : W := mkw 0x0000000100040140 0x0000000010004014 0xe4000003000427cd 0xde4000003000427c

def z118 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x09e07fc01f003f02 0x709e07fc01f003f0

def z119 : W := mkw 0x90ff83131bb78d56 0x290ff83131bb78d5 0xefeb07331f273fff 0xfefeb07331f273ff

def z120 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xb0f7ffcfc0000000 0x4b0f7ffcfc000000

def z121 : W := mkw 0x0000000000000000 0x0000000000000000 0x42080030002000f8 0x842080030002000f

def z122 : W := mkw 0x00b136ba80000005 0xc00b136ba8000000 0x3cf07fffc0000000 0xf3cf07fffc000000

def z123 : W := mkw 0x08fff6ffe04c63c7 0xd08fff6ffe04c63c 0xfcffffffe0dce7cd 0xffcffffffe0dce7c

def z124 : W := mkw 0x204c102c083800a0 0x8204c102c083800a 0x4e0c003c003838fb 0xb4e0c003c003838f

def z125 : W := mkw 0x200048042c3830a0 0x1200048042c3830a 0x030000003c3838fb 0x0030000003c3838f

def z126 : W := mkw 0x0000102800000000 0x8000010280000000 0x0000783c00000000 0xb0000783c0000000

def z127 : W := mkw 0x2000582c240830a0 0x92000582c240830a 0x5404783c201838f9 0xb5404783c201838f

def z128 : W := mkw 0x0000000100040140 0x0000000010004014 0x00000003000027c0 0xd00000003000027c

def z129 : W := mkw 0x00fe800012828006 0x200fe80001282800 0xfcff800003c7c004 0x0fcff800003c7c00

def z130 : W := mkw 0x00fea4801ab28007 0x200fea4801ab2800 0xffffffc03fffc00f 0x7ffffffc03fffc00

def z131 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xa023070303070704 0x4a02307030307070

def z132 : W := mkw 0x90ffb7bb81050d57 0xc90ffb7bb81050d5 0xfeffffffc3273fff 0xffeffffffc3273ff

def z133 : W := mkw 0xc1fffffab7c03e07 0xdc1fffffab7c03e0 0xfdffffffffc03f07 0xffdffffffffc03f0

def z134 : W := mkw 0x004f923a80000002 0xc004f923a8000000 0xc00f803fc0000000 0x8c00f803fc000000

def z135 : W := mkw 0x8000010001000c00 0x08000010001000c0 0x2020070003000704 0x4202007000300070

def z136 : W := mkw 0x2000582c240830a0 0x92000582c240830a 0x0000783c000038f0 0xb0000783c000038f

def z137 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x213007c03fc03f07 0x4213007c03fc03f0

def z138 : W := mkw 0x0000400020002000 0x1000040002000200 0x1400400020002001 0x1140040002000200

def z139 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xb1f780003fdfc004 0x0b1f780003fdfc00

def z140 : W := mkw 0xc9b06dc577cc7fc5 0x1c9b06dc577cc7fc 0x3df07fcfffc03fc7 0xf3df07fcfffc03fc

def z141 : W := mkw 0x0002800000028002 0x2000280000002800 0x800380000007c000 0x0800380000007c00

def z142 : W := mkw 0x49b06cc476c87285 0x149b06cc476c8728 0x11d4f8ccfcd8c000 0x011d4f8ccfcd8c00

def z143 : W := mkw 0xc1b2edc037c2be07 0x3c1b2edc037c2be0 0xbdf3ffc03fc7ff07 0x7bdf3ffc03fc7ff0

def z144 : W := mkw 0x00ffa69280000007 0x400ffa6928000000 0xfcff87c3c0000000 0x4fcff87c3c000000

def z145 : W := mkw 0x2800586d644c73e0 0x92800586d644c73e 0xf414f8ffe0dcfffd 0xff414f8ffe0dcfff

def z146 : W := mkw 0x004c48002c303000 0x1004c48002c30300 0x5fcc78003c38380b 0x35fcc78003c38380

def z147 : W := mkw 0x20fefcacac3830a7 0xd20fefcacac3830a 0x11d4f8ccfc180000 0x011d4f8ccfc18000

def z148 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0x5cef7f3c00000000 0xb5cef7f3c0000000

def z149 : W := mkw 0x1001021300050150 0x0100102130005015 0xc20b0033002700f8 0x8c20b0033002700f

def z150 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0xfdf4ffc03fdcff0f 0x7fdf4ffc03fdcff0

def z151 : W := mkw 0x004c102800000000 0x8004c10280000000 0x5ccc783c00000000 0xb5ccc783c0000000

def z152 : W := mkw 0x00b280001ab28006 0x200b280001ab2800 0xa33380003fffc00f 0x0a33380003fffc00

def z153 : W := mkw 0x0001269280000001 0x4000126928000000 0x000007c3c0000000 0x4000007c3c000000

def z154 : W := mkw 0x084e8005483ec1c2 0x2084e8005483ec1c 0xc20f800fc03fc0c8 0x8c20f800fc03fc0c

def z155 : W := mkw 0x000000001ab28000 0x2000000001ab2800 0xef2b00003fffc00f 0x0ef2b00003fffc00

def z156 : W := mkw 0x004e800008328002 0x2004e80000832800 0xee2f8000033fc00f 0x0ee2f8000033fc00

def z157 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414c0cfe0dcc00d 0xdf414c0cfe0dcc00

def z158 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xfe3fc0cfe3ffe7cf 0xdfe3fc0cfe3ffe7c

def z159 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0xfffb7fc03fe73f0f 0x7fffb7fc03fe73f0

def z160 : W := mkw 0x00b0248000000005 0x000b024800000000 0x08e03f0000000000 0x208e03f000000000

def z161 : W := mkw 0xe1fffffebff83ea7 0xde1fffffebff83ea 0xfffffffffff83fff 0xffffffffffff83ff

def z162 : W := mkw 0x204c102c083800a0 0x8204c102c083800a 0x420c003c003800f8 0x8420c003c003800f

def z163 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0x18fffffcc0000000 0x218fffffcc000000

def z164 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xd3df80003cffc008 0x0d3df80003cffc00

def z165 : W := mkw 0x004c000008300000 0x0004c00000830000 0x5fcc00003c38000b 0x05fcc00003c38000

def z166 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xc20b073300273ff8 0xfc20b073300273ff

def z167 : W := mkw 0x000000001ab28000 0x2000000001ab2800 0xf71480003fffc00f 0x0f71480003fffc00

def z168 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x5dcc783c3c180000 0xb5dcc783c3c18000

def z169 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0x0beb00003fffc00f 0x00beb00003fffc00

def z170 : W := mkw 0x204c18280c301020 0x8204c18280c30102 0x5fcc38303c38183b 0x25fcc38303c38183

def z171 : W := mkw 0x004c000008300000 0x0004c00000830000 0x5fcc00303c3838fb 0xb5fcc00303c3838f

def z172 : W := mkw 0x00b064c020402205 0x100b064c02040220 0x3cf07fc020c02705 0x73cf07fc020c0270

def z173 : W := mkw 0xc100494037c03e00 0x1c100494037c03e0 0x1dc078003fc03f07 0x31dc078003fc03f0

def z174 : W := mkw 0x0800404460486280 0x1080040446048628 0x1014c0cce0d8c000 0x01014c0cce0d8c00

def z175 : W := mkw 0x004e800008328002 0x2004e80000832800 0x020b000000230000 0x0020b00000023000

def z176 : W := mkw 0x200048043ebab0a0 0x3200048043ebab0a 0x030000003ffff8ff 0x0030000003ffff8f

def z177 : W := mkw 0x1001021300050150 0x0100102130005015 0x00000033000000f0 0x800000033000000f

def z178 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0xffdcf8fffc3838fb 0xfffdcf8fffc3838f

def z179 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c08003000000000 0xb4c0800300000000

def z180 : W := mkw 0x00b3a69280000007 0x400b3a6928000000 0xa03387c3c0000000 0x4a03387c3c000000

def z181 : W := mkw 0xb04d1b3a0d311c30 0x8b04d1b3a0d311c3 0x0beb3f301f231832 0x20beb3f301f23183

def z182 : W := mkw 0x08fec0457afee3c6 0x308fec0457afee3c 0xffffc0cfffffe7cf 0xdffffc0cfffffe7c

def z183 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x0bc838303c3838fb 0x20bc838303c3838f

def z184 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a08003000201832 0x20a0800300020183

def z185 : W := mkw 0xc9b025c153c44f45 0x0c9b025c153c44f4 0xa03087c3c3c4c704 0x4a03087c3c3c4c70

def z186 : W := mkw 0x004fb6ba80000003 0xc004fb6ba8000000 0xc00fffffc0000000 0xfc00fffffc000000

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0xe400000300000000 0xde40000030000000

def z188 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xeceb3f3300000000 0xfeceb3f330000000

def z189 : W := mkw 0xc9b06dc477c87e85 0x1c9b06dc477c87e8 0x3df4ffccffd8ff07 0x73df4ffccffd8ff0

def z190 : W := mkw 0xc1feedc037c03e07 0x1c1feedc037c03e0 0xfdffffc03fc03f07 0x7fdffffc03fc03f0

def z191 : W := mkw 0x08fff6fffafee3c7 0xf08fff6fffafee3c 0xffffffffffffe7cf 0xfffffffffffffe7c

def z192 : W := mkw 0x0800004140444340 0x0080000414044434 0xf41480c3e0dcc70d 0x4f41480c3e0dcc70

def z193 : W := mkw 0x00fe800012800006 0x000fe80001280000 0xfdff80003fc00007 0x0fdff80003fc0000

def z194 : W := mkw 0xc1b025c013c00e05 0x0c1b025c013c00e0 0x203007c003c00704 0x4203007c003c0070

def z195 : W := mkw 0xd1b127d313c50f55 0x0d1b127d313c50f5 0xa03307c303c70704 0x4a03307c303c7070

def z196 : W := mkw 0xd1b16fd337c53f55 0x1d1b16fd337c53f5 0xfffb7ff33fe73fff 0xffffb7ff33fe73ff

def z197 : W := mkw 0x9000010101050d50 0x09000010101050d5 0xee2b000003273fff 0x0ee2b000003273ff

def z198 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0x08eb7fffc0000000 0xf08eb7fffc000000

def z199 : W := mkw 0x0000400420082080 0x1000040042008208 0x5404400c201820c9 0x95404400c201820c

def z200 : W := mkw 0x0000000100040140 0x0000000010004014 0xee08003300243fff 0xfee08003300243ff

def z201 : W := mkw 0x00ff923a80000006 0xc00ff923a8000000 0xfcff803fc0000000 0x8fcff803fc000000

def z202 : W := mkw 0xc1b3efd2b7c03e07 0x5c1b3efd2b7c03e0 0xbdf3ffc3ffc03f07 0x7bdf3ffc3ffc03f0

def z203 : W := mkw 0x004c582824003000 0x9004c58282400300 0x5dcc783c3c003803 0xb5dcc783c3c00380

def z204 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xa8fbbff3c0000000 0x6a8fbbff3c000000

def z205 : W := mkw 0xe1fc7dec3ff83ea5 0x9e1fc7dec3ff83ea 0x7ffc7ffc3ff83fff 0xf7ffc7ffc3ff83ff

def z206 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xe03f87ffc0000000 0xce03f87ffc000000

def z207 : W := mkw 0xc100014013c00e00 0x0c100014013c00e0 0x0000000003c00704 0x00000000003c0070

def z208 : W := mkw 0x204fda3eac3830a2 0xd204fda3eac3830a 0xdfcff83ffc3838fb 0xbdfcff83ffc3838f

def z209 : W := mkw 0x1001021300050150 0x0100102130005015 0xe60b0033002727fd 0xde60b0033002727f

def z210 : W := mkw 0x41b06cc036c03205 0x141b06cc036c0320 0x1dd078c03cc03803 0x31dd078c03cc0380

def z211 : W := mkw 0x004c102808300000 0x8004c10280830000 0x5fcc783c3c38000b 0xb5fcc783c3c38000

def z212 : W := mkw 0x08fec0457afee3c6 0x308fec0457afee3c 0xf5d4c0cffcdce7cd 0xdf5d4c0cffcdce7c

def z213 : W := mkw 0x204c18280c301020 0x8204c18280c30102 0x4fc838301c2038fb 0xb4fc838301c2038f

def z214 : W := mkw 0x9001031301050d50 0x09001031301050d5 0x0a2b073303233ff2 0xf0a2b073303233ff

def z215 : W := mkw 0x90ffb7ba81010c17 0xc90ffb7ba81010c1 0x0aeb3f3003231832 0x20aeb3f300323183

def z216 : W := mkw 0x2800586d644c73e0 0x92800586d644c73e 0x000078ffc0003ff0 0xf000078ffc0003ff

def z217 : W := mkw 0x9001031201010c10 0x09001031201010c1 0x0023070003030000 0x0002307000303000

def z218 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfeffffffc327000f 0xffeffffffc327000

def z219 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0xfdf4ffcfffc03f07 0xffdf4ffcfffc03f0

def z220 : W := mkw 0x20fec8043ebab0a6 0x320fec8043ebab0a 0xffff80003ffff8ff 0x0ffff80003ffff8f

def z221 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x13c4780c3c3838fb 0x013c4780c3c3838f

def z222 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x11c4783c3c1838f0 0xb11c4783c3c1838f

def z223 : W := mkw 0x00ffb6ba92800007 0xc00ffb6ba9280000 0xfdffffffffc00007 0xffdffffffffc0000

def z224 : W := mkw 0x0001021200000000 0x0000102120000000 0x082b073000000000 0x2082b07300000000

def z225 : W := mkw 0x98014357614d6fd0 0x198014357614d6fd 0xee2b073323ffffff 0xfee2b073323fffff

def z226 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x7ff87ff03fe03fff 0xf7ff87ff03fe03ff

def z227 : W := mkw 0x0000248000000001 0x0000024800000000 0x00007fc000000000 0x700007fc00000000

def z228 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xfe3f873323ffffff 0xffe3f873323fffff

def z229 : W := mkw 0xc1ffbfba97801c07 0xcc1ffbfba97801c0 0x09eb3f301f001802 0x209eb3f301f00180

def z230 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0x01c000001c000000 0x001c000001c00000

def z231 : W := mkw 0x0000000100040140 0x0000000010004014 0x00000000000427cd 0x000000000000427c

def z232 : W := mkw 0x0001021200000000 0x0000102120000000 0xa023070300000000 0x4a02307030000000

def z233 : W := mkw 0x200048042c3830a0 0x1200048042c3830a 0x1fc078003c3838fb 0x31fc078003c3838f

def z234 : W := mkw 0xd9b16fd777cd7fd5 0x1d9b16fd777cd7fd 0xffffffffffffffff 0xffffffffffffffff

def z235 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0x10d4ffffc0000000 0xf10d4ffffc000000

def z236 : W := mkw 0x0001021300040140 0x0000102130004014 0xec2b0733000427cd 0xfec2b0733000427c

def z237 : W := mkw 0x200048042c3830a0 0x1200048042c3830a 0x010000003c180000 0x0010000003c18000

def z238 : W := mkw 0x1000000100050150 0x0100000010005015 0x02000000002700f8 0x002000000002700f

def z239 : W := mkw 0x00fe80011ab68146 0x200fe80011ab6814 0xffff80033fffe7cf 0xdffff80033fffe7c

def z240 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x31f07fc03fc00704 0x431f07fc03fc0070

def z241 : W := mkw 0x88004145614c6fc0 0x188004145614c6fc 0xfc34c7cfe3dcffcf 0xffc34c7cfe3dcffc

def z242 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0x3df480003fd8c007 0x03df480003fd8c00

def z243 : W := mkw 0x00fe90281ab28006 0xa00fe90281ab2800 0xfffff83c3fffc00f 0xbfffff83c3fffc00

def z244 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xaa2b073303271f36 0x6aa2b073303271f3

def z245 : W := mkw 0x904f933b81050d52 0xc904f933b81050d5 0xee2f873fc3273fff 0xfee2f873fc3273ff

def z246 : W := mkw 0xc1006dc025403e01 0x1c1006dc025403e0 0x1dc07fc03c003f03 0x71dc07fc03c003f0

def z247 : W := mkw 0x00feb4a880000007 0xc00feb4a88000000 0x5cdcf8fcc0000000 0xb5cdcf8fcc000000

def z248 : W := mkw 0x080040457afee3c0 0x3080040457afee3c 0x030000003fffe7cf 0x0030000003fffe7c

def z249 : W := mkw 0x004e80001ab28002 0x2004e80001ab2800 0xc30f80003fffc00f 0x0c30f80003fffc00

def z250 : W := mkw 0x00b0248000000005 0x000b024800000000 0xfcf4ffcfc0000000 0xffcf4ffcfc000000

def z251 : W := mkw 0x004e800000000002 0x0004e80000000000 0xc00f800000000000 0x0c00f80000000000

def z252 : W := mkw 0x08fef4ede04c63c7 0xd08fef4ede04c63c 0xf4d4f8cfe0dce7cd 0xdf4d4f8cfe0dce7c

def z253 : W := mkw 0x41b06cc036c03205 0x141b06cc036c0320 0x11d078c03cc00000 0x011d078c03cc0000

def z254 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414800000000000 0x0f41480000000000

def z255 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z256 : W := mkw 0x00feb4a89ab28007 0xe00feb4a89ab2800 0x11d4f8ccfcd8c000 0x011d4f8ccfcd8c00

def z257 : W := mkw 0x90b3831313878d56 0x290b3831313878d5 0xa033870303c7c704 0x4a033870303c7c70

def z258 : W := mkw 0x204c102c083800a0 0x8204c102c083800a 0x5fcc003c3c3800fb 0x85fcc003c3c3800f

def z259 : W := mkw 0x20fe98281eb29026 0xa20fe98281eb2902 0xffffb8303fffd83f 0x2ffffb8303fffd83

def z260 : W := mkw 0x0000080004001000 0x0000008000400100 0x09c038001c001802 0x209c038001c00180

def z261 : W := mkw 0x00b0000000000004 0x000b000000000000 0x3cf0000000000000 0x03cf000000000000

def z262 : W := mkw 0x004c400428382080 0x1004c40042838208 0x5fcc400c3c3820cb 0x95fcc400c3c3820c

def z263 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000030000038f0 0xb00000030000038f

def z264 : W := mkw 0x98010317410d4dd0 0x098010317410d4dd 0xee2f873fc33fffff 0xfee2f873fc33ffff

def z265 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xe23f800003ffc00c 0x0e23f800003ffc00

def z266 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x540440cfe01827c9 0xd540440cfe01827c

def z267 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xfdfffffffcd8c000 0xffdfffffffcd8c00

def z268 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xfe3fc7ffc3273fff 0xffe3fc7ffc3273ff

def z269 : W := mkw 0x08b3e6d7e04c63c7 0x508b3e6d7e04c63c 0xf437c7cfe0dce7cd 0xdf437c7cfe0dce7c

def z270 : W := mkw 0xc1b02dc017c01e05 0x0c1b02dc017c01e0 0x29f03fc01fc01f06 0x629f03fc01fc01f0

def z271 : W := mkw 0xc1b02d8017801c05 0x0c1b02d8017801c0 0x2de03f001f003f07 0x72de03f001f003f0

def z272 : W := mkw 0x20ffb6be883800a7 0xc20ffb6be883800a 0xfeffffffc03800f8 0xffeffffffc03800f

def z273 : W := mkw 0x204c582c240830a0 0x9204c582c240830a 0x5ccc783c000038f0 0xb5ccc783c000038f

def z274 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xec2b073300003ff0 0xfec2b073300003ff

def z275 : W := mkw 0x0000484024403200 0x1000048402440320 0x3dd078c03cc03f07 0x73dd078c03cc03f0

def z276 : W := mkw 0x0000004000400200 0x0000000400040020 0x201000c000c00704 0x4201000c000c0070

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0xe40000000004000d 0x0e40000000004000

def z278 : W := mkw 0x204ed82c2c3ab0a2 0xb204ed82c2c3ab0a 0xdfcff83c3c3ff8fb 0xbdfcff83c3c3ff8f

def z279 : W := mkw 0xd1014b5337c53f50 0x1d1014b5337c53f5 0xef2b07333fe73fff 0xfef2b07333fe73ff

def z280 : W := mkw 0xb04d5b3e2d393cb0 0x9b04d5b3e2d393cb 0x5fef7f3c3f3b38fb 0xb5fef7f3c3f3b38f

def z281 : W := mkw 0x004f923a80000002 0xc004f923a8000000 0xdccff83fc0000000 0xbdccff83fc000000

def z282 : W := mkw 0xc9b06dc577cc7fc5 0x1c9b06dc577cc7fc 0x3df07fc03fdcffcf 0x73df07fc03fdcffc

def z283 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xa223070303273fff 0x4a223070303273ff

def z284 : W := mkw 0x0000480024003000 0x1000048002400300 0x010000003c003803 0x0010000003c00380

def z285 : W := mkw 0x004c102800000000 0x8004c10280000000 0x5ecc783c002038fb 0xb5ecc783c002038f

def z286 : W := mkw 0x00ff821200000006 0x000ff82120000000 0xfcff873300000000 0xffcff87330000000

def z287 : W := mkw 0x08014257604c63c0 0x108014257604c63c 0xfc3fc7ffe0dce7cd 0xffc3fc7ffe0dce7c

def z288 : W := mkw 0x08ffb6bfc00c41c7 0xc08ffb6bfc00c41c 0xfcffffffc01cc0c8 0xffcffffffc01cc0c

def z289 : W := mkw 0x08b2804152c6c346 0x208b2804152c6c34 0xa03380c3c3c7c704 0x4a03380c3c3c7c70

def z290 : W := mkw 0x00fffebaa4003007 0xd00fffebaa400300 0xfdfffffffc003803 0xffdfffffffc00380

def z291 : W := mkw 0x004e800008328002 0x2004e80000832800 0x000480000018c000 0x0000480000018c00

def z292 : W := mkw 0x00ffb6ba88328007 0xe00ffb6ba8832800 0xfeffffffc03fc008 0xffeffffffc03fc00

def z293 : W := mkw 0x00b2800012828006 0x200b280001282800 0xf437800023dfc00d 0x0f437800023dfc00

def z294 : W := mkw 0x08004845644c73c0 0x108004845644c73c 0xfdd4f8cffcdcffcf 0xffdd4f8cffcdcffc

def z295 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xc004c0cfc01ce7c8 0xdc004c0cfc01ce7c

def z296 : W := mkw 0x0000400420082080 0x1000040042008208 0xf414c0cfe01820c9 0xdf414c0cfe01820c

def z297 : W := mkw 0x00ffb6bb80040147 0xc00ffb6bb8004014 0xfcffffffc00427cd 0xffcffffffc00427c

def z298 : W := mkw 0x00fec8003eb2b006 0x300fec8003eb2b00 0xfffff8003ffff80f 0x3fffff8003ffff80

def z299 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0xf414ffffc0000000 0xff414ffffc000000

def z300 : W := mkw 0x084c4045687c63c0 0x1084c4045687c63c 0xffdcc0cffcfce7cf 0xdffdcc0cffcfce7c

def z301 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff80001f230002 0x0ffff80001f23000

def z302 : W := mkw 0xb04c592d2d3d3df0 0x9b04c592d2d3d3df 0x5fcc783c3f3f3fff 0xb5fcc783c3f3f3ff

def z303 : W := mkw 0x98004145614d6fd0 0x198004145614d6fd 0x0200000023ffffff 0x00200000023fffff

def z304 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xe400073300043ffd 0xfe400073300043ff

def z305 : W := mkw 0x41feecc03ef2b207 0x341feecc03ef2b20 0x11d4f8c03cd8c000 0x011d4f8c03cd8c00

def z306 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xe40040cfc00427cd 0xde40040cfc00427c

def z307 : W := mkw 0x41b06cc036c03205 0x141b06cc036c0320 0x3df07fc03cc00000 0x73df07fc03cc0000

def z308 : W := mkw 0xf1fd7fff3ffd3ff5 0x9f1fd7fff3ffd3ff 0xffff7fff3fff3fff 0xfffff7fff3fff3ff

def z309 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x09e03f003fc03f07 0x209e03f003fc03f0

def z310 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xac23070303073f07 0x7ac23070303073f0

def z311 : W := mkw 0x004c102800000000 0x8004c10280000000 0xfcdcf8ffc0000000 0xffcdcf8ffc000000

def z312 : W := mkw 0x0000480024003000 0x1000048002400300 0x5fc878303c2038fb 0xb5fc878303c2038f

def z313 : W := mkw 0x00b0248000000005 0x000b024800000000 0x10d078c000000000 0x010d078c00000000

def z314 : W := mkw 0x0000000100040140 0x0000000010004014 0xc0000003000400c8 0x8c0000003000400c

def z315 : W := mkw 0x1001021300050150 0x0100102130005015 0x8003000300070000 0x0800300030007000

def z316 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffe0dcc00d 0xffcffffffe0dcc00

def z317 : W := mkw 0xb04d5b3f2d3d3df0 0x9b04d5b3f2d3d3df 0x5fcc7f3f3c383ffb 0xf5fcc7f3f3c383ff

def z318 : W := mkw 0x0000404020402200 0x1000040402040220 0x101040c020c00000 0x0101040c020c0000

def z319 : W := mkw 0x00b1269200000005 0x000b126920000000 0xfcfb7ff300000000 0xffcfb7ff30000000

def z320 : W := mkw 0x08fff6fee0486287 0xd08fff6fee048628 0xfcffffffe0d8c000 0xffcffffffe0d8c00

def z321 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x1014c0cce0dce7cd 0x01014c0cce0dce7c

def z322 : W := mkw 0xc1fefde8b7c03e07 0xdc1fefde8b7c03e0 0x3df4ffccffc03f07 0x73df4ffccffc03f0

def z323 : W := mkw 0x0000404120442340 0x1000040412044234 0xf41040c320c427cd 0xdf41040c320c427c

def z324 : W := mkw 0x61fc7cec3ef832a5 0x961fc7cec3ef832a 0x5fdc78fc3cf838fb 0xb5fdc78fc3cf838f

def z325 : W := mkw 0xc1b0494037c03e04 0x1c1b0494037c03e0 0x3df000003fc03f07 0x03df000003fc03f0

def z326 : W := mkw 0xc1b06d8037803c05 0x1c1b06d8037803c0 0x1de07f003f003803 0x31de07f003f00380

def z327 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x55c4780c3c1820c9 0x955c4780c3c1820c

def z328 : W := mkw 0xc9feedc57ffeffc7 0x3c9feedc57ffeffc 0xffffffcfffffffcf 0xfffffffcfffffffc

def z329 : W := mkw 0x2000582c240830a0 0x92000582c240830a 0x1dc0783c3c0038f3 0xb1dc0783c3c0038f

def z330 : W := mkw 0x18014257604d63d0 0x118014257604d63d 0xf61fc0ffe0ffe7fd 0xdf61fc0ffe0ffe7f

def z331 : W := mkw 0x98014357614d6fd0 0x198014357614d6fd 0xee2b47ffc3273fff 0xfee2b47ffc3273ff

def z332 : W := mkw 0xd1b16fd337c53f55 0x1d1b16fd337c53f5 0xbdf37fc33fc73f07 0x7bdf37fc33fc73f0

def z333 : W := mkw 0x0000404020402200 0x1000040402040220 0x000040c000002700 0x5000040c00000270

def z334 : W := mkw 0x20ffbeba8c301027 0xc20ffbeba8c30102 0xffffffffdc201832 0xfffffffffdc20183

def z335 : W := mkw 0x0800404460486280 0x1080040446048628 0x5414c0cce0d8e0c9 0x95414c0cce0d8e0c

def z336 : W := mkw 0x0800404460486280 0x1080040446048628 0x3414c0cce0d8e705 0x53414c0cce0d8e70

def z337 : W := mkw 0x20ffbeba8c301027 0xc20ffbeba8c30102 0x0beb3f301c201832 0x20beb3f301c20183

def z338 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000020dcc00d 0x00000000020dcc00

def z339 : W := mkw 0x28fed86d7efef3e6 0xb28fed86d7efef3e 0xfffff8ffffffffff 0xffffff8fffffffff

def z340 : W := mkw 0x0003821280000002 0x4000382128000000 0x80038003c0000000 0x080038003c000000

def z341 : W := mkw 0x0000400420082080 0x1000040042008208 0x1004400c20180000 0x01004400c2018000

def z342 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xd014c0cfe0dcc0c8 0x8d014c0cfe0dcc0c

def z343 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x5404400c20dce7cd 0x95404400c20dce7c

def z344 : W := mkw 0xe1fc7dac3fb83ca5 0x9e1fc7dac3fb83ca 0x5fec7f3c3f3838fb 0xb5fec7f3c3f3838f

def z345 : W := mkw 0x004c000008300000 0x0004c00000830000 0x0bc800001c200002 0x00bc800001c20000

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0x02000000002038fb 0x002000000002038f

def z347 : W := mkw 0x00b0000012800004 0x000b000001280000 0xfffb00003fe7000f 0x0fffb00003fe7000

def z348 : W := mkw 0x00004005200c21c0 0x100004005200c21c 0xf404400f201c27cd 0xdf404400f201c27c

def z349 : W := mkw 0x284c506d687c63e0 0x9284c506d687c63e 0xf61cc0ffe0fce7fd 0xdf61cc0ffe0fce7f

def z350 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xc004800fe0dce7cd 0x8c004800fe0dce7c

def z351 : W := mkw 0xd1fffffbb7c53f57 0xdd1fffffbb7c53f5 0xffffffffffe73fff 0xfffffffffffe73ff

def z352 : W := mkw 0x00fff6bea0082087 0xd00fff6bea008208 0xfcffffffe01820c9 0xffcffffffe01820c

def z353 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x11d078c03fc03f07 0x011d078c03fc03f0

def z354 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xfdff80003cd8c000 0x0fdff80003cd8c00

def z355 : W := mkw 0x900103131bb78d50 0x2900103131bb78d5 0xef2b07333fffffff 0xfef2b07333ffffff

def z356 : W := mkw 0x0000000000000000 0x0000000000000000 0xc004800fc0000000 0x8c004800fc000000

def z357 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0x1bff80003ffbc002 0x01bff80003ffbc00

def z358 : W := mkw 0x41b06cc036c03205 0x141b06cc036c0320 0x35d078c03cc02705 0x535d078c03cc0270

def z359 : W := mkw 0x0800000440084080 0x0080000044008408 0x0004800cc018c000 0x00004800cc018c00

def z360 : W := mkw 0x00feb4a880000007 0xc00feb4a88000000 0x3cf4ffccc0000000 0x73cf4ffccc000000

def z361 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x1dc4780c3c183803 0x31dc4780c3c18380

def z362 : W := mkw 0x1001021300050150 0x0100102130005015 0xee2b0033032700ff 0x8ee2b0033032700f

def z363 : W := mkw 0x9801035341454f50 0x09801035341454f5 0xee3b87f3c3e7ffff 0xfee3b87f3c3e7fff

def z364 : W := mkw 0x0000000000000000 0x0000000000000000 0x1dc000003c000003 0x01dc000003c00000

def z365 : W := mkw 0x0000404020402200 0x1000040402040220 0xf414c0cfe0c02705 0xdf414c0cfe0c0270

def z366 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x0bc8783c1c2038f2 0xb0bc8783c1c2038f

def z367 : W := mkw 0x0800004140444340 0x0080000414044434 0x000000c3c0000700 0x4000000c3c000070

def z368 : W := mkw 0x90ffb7ba81010c17 0xc90ffb7ba81010c1 0xfeffffffc3231832 0xffeffffffc323183

def z369 : W := mkw 0x004c502c20082080 0x9004c502c2008208 0x5ccc783c201820c9 0xb5ccc783c201820c

def z370 : W := mkw 0x00b000001ab28004 0x200b000001ab2800 0x3ff000003fffc00f 0x03ff000003fffc00

def z371 : W := mkw 0xc100494037c03e00 0x1c100494037c03e0 0x351040c03fc03f07 0x5351040c03fc03f0

def z372 : W := mkw 0x204c18280c301020 0x8204c18280c30102 0x5fcc783c1c201832 0xb5fcc783c1c20183

def z373 : W := mkw 0x284c586d6c7c73e0 0x9284c586d6c7c73e 0x5fcc78fffc383ffb 0xf5fcc78fffc383ff

def z374 : W := mkw 0x084f923fc00c41c2 0xc084f923fc00c41c 0xc00f803fc01cc0c8 0x8c00f803fc01cc0c

def z375 : W := mkw 0x9000010101050d50 0x09000010101050d5 0x0000000000003ff0 0x00000000000003ff

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0xc20b000000270008 0x0c20b00000027000

def z377 : W := mkw 0x90b3a79381050d57 0x490b3a79381050d5 0xa03387c3c3070704 0x4a03387c3c307070

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe3f800023ffc00f 0x0fe3f800023ffc00

def z379 : W := mkw 0x284c102d483c41e0 0x8284c102d483c41e 0xc20c803fc03cc0f8 0x8c20c803fc03cc0f

def z380 : W := mkw 0x00fc34a800000005 0x800fc34a80000000 0x7cfc7ffc00000000 0xf7cfc7ffc0000000

def z381 : W := mkw 0x204c102c083800a0 0x8204c102c083800a 0x0004000c00180000 0x00004000c0018000

def z382 : W := mkw 0x0000000000000000 0x0000000000000000 0x000040cfc0000000 0xd000040cfc000000

def z383 : W := mkw 0xb84d5b7f6d7d7ff0 0x9b84d5b7f6d7d7ff 0xffffffffffffffff 0xffffffffffffffff

def z384 : W := mkw 0xd1016fd325453f51 0x1d1016fd325453f5 0x00007ff300003ff0 0xf00007ff300003ff

def z385 : W := mkw 0x204c102c083800a0 0x8204c102c083800a 0x5ecc783c003800f8 0xb5ecc783c003800f

def z386 : W := mkw 0x18010217400d41d0 0x018010217400d41d 0xc20f803fc03fc0f8 0x8c20f803fc03fc0f

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0x5404400c00000000 0x95404400c0000000

def z388 : W := mkw 0x9000010101050d50 0x09000010101050d5 0x2e20070003273fff 0x72e20070003273ff

def z389 : W := mkw 0x204c502c283820a0 0x9204c502c283820a 0x560c403c203820f9 0x9560c403c203820f

def z390 : W := mkw 0x10ffb6bb80050157 0xc10ffb6bb8005015 0xfeffffffc02700f8 0xffeffffffc02700f

def z391 : W := mkw 0xc1006dc025403e01 0x1c1006dc025403e0 0x2c207fc003003f07 0x72c207fc003003f0

def z392 : W := mkw 0xe10049443ff83ea0 0x1e10049443ff83ea 0x030000003ff83fff 0x0030000003ff83ff

def z393 : W := mkw 0x0000000008328000 0x2000000000832800 0x02000000003fc008 0x002000000003fc00

def z394 : W := mkw 0x004e902880000002 0xc004e90288000000 0x0004800cc0000000 0x00004800cc000000

def z395 : W := mkw 0x004f923a80000002 0xc004f923a8000000 0xec2f873fc0000000 0xfec2f873fc000000

def z396 : W := mkw 0x00b3a69280000007 0x400b3a6928000000 0x0023070000000000 0x0002307000000000

def z397 : W := mkw 0x0000000000000000 0x0000000000000000 0x341040c000000000 0x5341040c00000000

def z398 : W := mkw 0x200008000c301020 0x0200008000c30102 0x030000001c201832 0x0030000001c20183

def z399 : W := mkw 0x00b0000012800004 0x000b000001280000 0xfdf480003fdcc00f 0x0fdf480003fdcc00

def z400 : W := mkw 0xe1007dec25483ea1 0x9e1007dec25483ea 0x00007ffc00003ff0 0xf00007ffc00003ff

def z401 : W := mkw 0x98fff7ffe14d6fd7 0xd98fff7ffe14d6fd 0xfeffffffe3ffffff 0xffeffffffe3fffff

def z402 : W := mkw 0x0800004040404200 0x0080000404040420 0x001080c0c0c0c000 0x0001080c0c0c0c00

def z403 : W := mkw 0x00fe800000000006 0x000fe80000000000 0x08eb000000000000 0x008eb00000000000

def z404 : W := mkw 0x8000010001000c00 0x08000010001000c0 0x0000070000003f00 0x70000070000003f0

def z405 : W := mkw 0x0000400420082080 0x1000040042008208 0x00000000201820c9 0x000000000201820c

def z406 : W := mkw 0x0001021200000000 0x0000102120000000 0x0000073300000000 0xf000007330000000

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c20000003000007 0x02c2000000300000

def z408 : W := mkw 0xe9fc7ded7ffc7fe5 0x9e9fc7ded7ffc7fe 0xfffcfffffffcffff 0xffffcfffffffcfff

def z409 : W := mkw 0xe14c7dec2d783ea1 0x9e14c7dec2d783ea 0x5fcc7ffc3c383ffb 0xf5fcc7ffc3c383ff

def z410 : W := mkw 0x0800004140444340 0x0080000414044434 0x0000000000c4c704 0x00000000000c4c70

def z411 : W := mkw 0x98004145614d6fd0 0x198004145614d6fd 0xf614c0cfe3ffffff 0xdf614c0cfe3fffff

def z412 : W := mkw 0x00b3a69292828007 0x600b3a6929282800 0xa03387c3c3c7c004 0x4a03387c3c3c7c00

def z413 : W := mkw 0x20fed82c3ebab0a6 0xb20fed82c3ebab0a 0x11d4f80c3cd8c000 0x011d4f80c3cd8c00

def z414 : W := mkw 0x00b0000012800004 0x000b000001280000 0x11d000003cc00000 0x011d000003cc0000

def z415 : W := mkw 0x084c506d604c63c0 0x9084c506d604c63c 0xfcdcf8ffe0dce7cd 0xffcdcf8ffe0dce7c

def z416 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xec2b073303070704 0xfec2b07330307070

def z417 : W := mkw 0x0000000000000000 0x0000000000000000 0x020000000327000f 0x0020000000327000

def z418 : W := mkw 0x00fc00001ab00004 0x000fc00001ab0000 0x7ffc00003ff8000f 0x07ffc00003ff8000

def z419 : W := mkw 0x0001021200000000 0x0000102120000000 0xee2b07330327000f 0xfee2b07330327000

def z420 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e0800000020000b 0x04e0800000020000

def z421 : W := mkw 0x9001031301050d50 0x09001031301050d5 0x0000070300000700 0x4000007030000070

def z422 : W := mkw 0xd1b16fd237c13e15 0x1d1b16fd237c13e1 0x3ffb7ff03fe33f37 0x73ffb7ff03fe33f3

def z423 : W := mkw 0x00ffa6929ab28007 0x600ffa6929ab2800 0xffff87c3ffffc00f 0x4ffff87c3ffffc00

def z424 : W := mkw 0x00b0248000000005 0x000b024800000000 0x203007c000000000 0x4203007c00000000

def z425 : W := mkw 0x00fec0403af2a206 0x300fec0403af2a20 0xffffc0c03fffe70f 0x5ffffc0c03fffe70

def z426 : W := mkw 0x08004005600c61c0 0x108004005600c61c 0xd404c00fe01ce0c9 0x9d404c00fe01ce0c

def z427 : W := mkw 0x0000000008300000 0x0000000000830000 0x030000003c38000b 0x0030000003c38000

def z428 : W := mkw 0x20000004083800a0 0x020000004083800a 0x02000000003800f8 0x002000000003800f

def z429 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x19f07fc03fc01802 0x219f07fc03fc0180

def z430 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xca2b0733032718fa 0xaca2b0733032718f

def z431 : W := mkw 0x41006cc024403201 0x141006cc02440320 0x000078c000000000 0x0000078c00000000

def z432 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x420c783c003838f8 0xb420c783c003838f

def z433 : W := mkw 0x0800004140444340 0x0080000414044434 0xf414c0cfc0c4c704 0xdf414c0cfc0c4c70

def z434 : W := mkw 0xc9b06dc177c47f45 0x1c9b06dc177c47f4 0xbdf0ffc3ffc4ff07 0x7bdf0ffc3ffc4ff0

def z435 : W := mkw 0x284c586c6c7872a0 0x9284c586c6c7872a 0x5fdcf8fcfcf8f8fb 0xb5fdcf8fcfcf8f8f

def z436 : W := mkw 0x10ff82131ab78156 0x210ff82131ab7815 0xffff80333fffc0ff 0x8ffff80333fffc0f

def z437 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x000040cfe0dce7cd 0xd000040cfe0dce7c

def z438 : W := mkw 0x000034a880000001 0xc000034a88000000 0x000078ccc0000000 0x0000078ccc000000

def z439 : W := mkw 0x90ffb7bb81050d57 0xc90ffb7bb81050d5 0xfcffffffc0003ff0 0xffcffffffc0003ff

def z440 : W := mkw 0x8000010101040d40 0x08000010101040d4 0xec20070303043fcf 0xfec20070303043fc

def z441 : W := mkw 0xc1002d8005001c01 0x0c1002d8005001c0 0x00003f0000001800 0x200003f000000180

def z442 : W := mkw 0x90ff831301050d56 0x090ff831301050d5 0xfeff873303273fff 0xffeff873303273ff

def z443 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0048000001cc008 0x0c0048000001cc00

def z444 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0x3cfb7ff000000000 0x73cfb7ff00000000

def z445 : W := mkw 0x2000582c240830a0 0x92000582c240830a 0x0000780c00000000 0x00000780c0000000

def z446 : W := mkw 0xd1b16fd337c53f55 0x1d1b16fd337c53f5 0x3df07ff33fc03ff7 0xf3df07ff33fc03ff

def z447 : W := mkw 0x9000010101050d50 0x09000010101050d5 0x4e08003003273fff 0xb4e08003003273ff

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c20070000000000 0x72c2007000000000

def z449 : W := mkw 0x004c000008300000 0x0004c00000830000 0xffef00003f3f000f 0x0ffef00003f3f000

def z450 : W := mkw 0xc1b06dc03ff2be05 0x3c1b06dc03ff2be0 0x3ff07fc03fffff0f 0x73ff07fc03fffff0

def z451 : W := mkw 0x900137bb81050d51 0xc900137bb81050d5 0xee2b7fffc3273fff 0xfee2b7fffc3273ff

def z452 : W := mkw 0x0000400420082080 0x1000040042008208 0xf414c00c20dce0cd 0x9f414c00c20dce0c

def z453 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0xffef783c3f3f38ff 0xbffef783c3f3f38f

def z454 : W := mkw 0xd1016fd325453f51 0x1d1016fd325453f5 0xee2b7ff303273fff 0xfee2b7ff303273ff

def z455 : W := mkw 0x9000010101050d50 0x09000010101050d5 0xe600000303273fff 0xde600000303273ff

def z456 : W := mkw 0xc1b02d8017801c05 0x0c1b02d8017801c0 0x3df07fc01f001802 0x73df07fc01f00180

def z457 : W := mkw 0x20fc7cac2c3830a5 0x920fc7cac2c3830a 0x7ffc7ffc3c3838fb 0xf7ffc7ffc3c3838f

def z458 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x430c003c3c3838fb 0x8430c003c3c3838f

def z459 : W := mkw 0xb0014b172d3d3df0 0x1b0014b172d3d3df 0xef2b07333f3f3fff 0xfef2b07333f3f3ff

def z460 : W := mkw 0x08000045404c43c0 0x008000045404c43c 0xe01480cfc0dcc7cc 0xce01480cfc0dcc7c

def z461 : W := mkw 0x90014b1325053d50 0x190014b1325053d5 0xffeb7f333f273fff 0xfffeb7f333f273ff

def z462 : W := mkw 0x0000000000000000 0x0000000000000000 0x1014800020d8c000 0x01014800020d8c00

def z463 : W := mkw 0x200048042c3830a0 0x1200048042c3830a 0x4f0800303c3838fb 0xb4f0800303c3838f

def z464 : W := mkw 0xe14c596c3ff83ea0 0x9e14c596c3ff83ea 0x5fcc783c3ff83fff 0xb5fcc783c3ff83ff

def z465 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0x00003f3000000000 0x200003f300000000

def z466 : W := mkw 0x0800404460486280 0x1080040446048628 0x0000000020d8c000 0x00000000020d8c00

def z467 : W := mkw 0x0000000100040140 0x0000000010004014 0xf414800320dce7cd 0xdf414800320dce7c

def z468 : W := mkw 0x20fed82c3ebab0a6 0xb20fed82c3ebab0a 0x5fef783c3f3b38fb 0xb5fef783c3f3b38f

def z469 : W := mkw 0xb0015b3f250d3df0 0x9b0015b3f250d3df 0xee2b7f3f03273fff 0xfee2b7f3f03273ff

def z470 : W := mkw 0x284c586d6c7c73e0 0x9284c586d6c7c73e 0x5fcc783c3cfcffff 0xb5fcc783c3cfcfff

def z471 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0xec2b7fffc0000000 0xfec2b7fffc000000

def z472 : W := mkw 0x90ffb7bb9bb78d57 0xe90ffb7bb9bb78d5 0xffffffffffffffff 0xffffffffffffffff

def z473 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xcbef80001f3fc00a 0x0cbef80001f3fc00

def z474 : W := mkw 0x004c00001ab28000 0x2004c00001ab2800 0x5fcc00003fffc00f 0x05fcc00003fffc00

def z475 : W := mkw 0xc100494037c03e00 0x1c100494037c03e0 0x2d2007003fc03f07 0x72d2007003fc03f0

def z476 : W := mkw 0x0000000000000000 0x0000000000000000 0x44000000000020c9 0x944000000000020c

def z477 : W := mkw 0x00b0000012800004 0x000b000001280000 0x2030000003c00004 0x02030000003c0000

def z478 : W := mkw 0x104f923b80050152 0xc104f923b8005015 0xc20f803fc02700f8 0x8c20f803fc02700f

def z479 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xc20b003303273fff 0x8c20b003303273ff

def z480 : W := mkw 0x00fec0043abaa086 0x300fec0043abaa08 0xffffc00c3fffe0cf 0x9ffffc00c3fffe0c

def z481 : W := mkw 0xc1b0258013800c05 0x0c1b0258013800c0 0x0020070003000000 0x0002007000300000

def z482 : W := mkw 0x20fffebeac3830a7 0xd20fffebeac3830a 0xfdfffffffc180000 0xffdfffffffc18000

def z483 : W := mkw 0xd1b127d313c50f55 0x0d1b127d313c50f5 0xee3b07f303e73fff 0xfee3b07f303e73ff

def z484 : W := mkw 0x0001021200000000 0x0000102120000000 0xee2b0733002038fb 0xfee2b0733002038f

def z485 : W := mkw 0x900137bb81050d51 0xc900137bb81050d5 0x00007fffc0003ff0 0xf00007fffc0003ff

def z486 : W := mkw 0x0800404460486280 0x1080040446048628 0xf414c0cfe0d8c000 0xdf414c0cfe0d8c00

def z487 : W := mkw 0x98014357614d6fd0 0x198014357614d6fd 0x000047ffc0003ff0 0xf000047ffc0003ff

def z488 : W := mkw 0x41fffefab6c03207 0xd41fffefab6c0320 0xfdfffffffcc00000 0xffdfffffffcc0000

def z489 : W := mkw 0x90ff83121bb38c16 0x290ff83121bb38c1 0x0beb07301f231832 0x20beb07301f23183

def z490 : W := mkw 0xb0015b3f250d3df0 0x9b0015b3f250d3df 0x00007f3f00003ff0 0xf00007f3f00003ff

def z491 : W := mkw 0x284c586d6c7c73e0 0x9284c586d6c7c73e 0xf5d4f8cffcdce7cd 0xdf5d4f8cffcdce7c

def z492 : W := mkw 0xc1fffffabff2be07 0xfc1fffffabff2be0 0xffffffffffffff0f 0xfffffffffffffff0

def z493 : W := mkw 0x204e902c083a80a2 0xa204e902c083a80a 0xc20f803c003fc0f8 0x8c20f803c003fc0f

def z494 : W := mkw 0x80b0258001000c05 0x080b0258001000c0 0x3cf07fc003003f07 0x73cf07fc003003f0

def z495 : W := mkw 0x0800404160446340 0x1080040416044634 0xb410c0c3e0c4e705 0x5b410c0c3e0c4e70

def z496 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x20307fc003c03f04 0x720307fc003c03f0

def z497 : W := mkw 0x98014357614d6fd0 0x198014357614d6fd 0xf414c7ffe0dcfffd 0xff414c7ffe0dcfff

def z498 : W := mkw 0xc1fead801fb29c07 0x2c1fead801fb29c0 0xffffbf003fffd80f 0x2ffffbf003fffd80

def z499 : W := mkw 0x004e800008328002 0x2004e80000832800 0xf61f800020ffc00d 0x0f61f800020ffc00

def z500 : W := mkw 0x9001031201010c10 0x09001031201010c1 0x0000073000001830 0x2000007300000183

def z501 : W := mkw 0x28fffeffec7c73e7 0xd28fffeffec7c73e 0xfffffffffcfcffff 0xffffffffffcfcfff

def z502 : W := mkw 0xc1017ffaa5403e01 0xdc1017ffaa5403e0 0x00007fffc0003f00 0xf00007fffc0003f0

def z503 : W := mkw 0x90ff83121bb38c16 0x290ff83121bb38c1 0xffff87303fffd83f 0x2ffff87303fffd83

def z504 : W := mkw 0xc9fffffff7cc7fc7 0xdc9fffffff7cc7fc 0xfdffffffffdcffcf 0xffdffffffffdcffc

def z505 : W := mkw 0xc1feedc03ff2be07 0x3c1feedc03ff2be0 0x3ffb7fc03fe33f07 0x73ffb7fc03fe33f0

def z506 : W := mkw 0x90fe81011bb78d56 0x290fe81011bb78d5 0xffff80003fffffff 0x0ffff80003ffffff

def z507 : W := mkw 0x08fff6ffe04c63c7 0xd08fff6ffe04c63c 0xfcffffffc00027c0 0xffcffffffc00027c

def z508 : W := mkw 0x0000000000000000 0x0000000000000000 0xa01080c3c0000000 0x4a01080c3c000000

def z509 : W := mkw 0x004f923a80000002 0xc004f923a8000000 0xf41fc0ffc0000000 0xdf41fc0ffc000000

def z510 : W := mkw 0x9001031301050d50 0x09001031301050d5 0x0200073303273fff 0xf0200073303273ff

def z511 : W := mkw 0xc1006dc037c03e01 0x1c1006dc037c03e0 0x01007fc03fc03f07 0x701007fc03fc03f0

def z512 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x00000000000027c0 0x000000000000027c

def z513 : W := mkw 0x08b2c04572cee3c6 0x308b2c04572cee3c 0xf437c0cfe3dfe7cd 0xdf437c0cfe3dfe7c

def z514 : W := mkw 0x80fe81001bb28c06 0x280fe81001bb28c0 0xffff87003fffff0f 0x7ffff87003fffff0

def z515 : W := mkw 0x0000000000000000 0x0000000000000000 0xa023000003070004 0x0a02300000307000

def z516 : W := mkw 0x20fefcacac3830a7 0xd20fefcacac3830a 0x5fdcf8fcfc3838fb 0xb5fdcf8fcfc3838f

def z517 : W := mkw 0x0000000000000000 0x0000000000000000 0xec2b000000000000 0x0ec2b00000000000

def z518 : W := mkw 0x9001031201010c10 0x09001031201010c1 0x2e2b073003233f37 0x72e2b073003233f3

def z519 : W := mkw 0x20fed82c2c3830a6 0x920fed82c2c3830a 0xfffff83c3c3838fb 0xbfffff83c3c3838f

def z520 : W := mkw 0x20fc582c3eb830a4 0x920fc582c3eb830a 0x7ffc783c3ff838ff 0xb7ffc783c3ff838f

def z521 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c00000000003803 0x30c0000000000380

def z522 : W := mkw 0x0800404460486280 0x1080040446048628 0xf414c0cce0dcc00d 0x0f414c0cce0dcc00

def z523 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xa01080c3e0dce7cd 0x4a01080c3e0dce7c

def z524 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0x5fef00003f3b000b 0x05fef00003f3b000

def z525 : W := mkw 0x0800000140044140 0x0080000014004414 0x80008003c004c000 0x080008003c004c00

def z526 : W := mkw 0x1001021300050150 0x0100102130005015 0xce0b0033002738fb 0xbce0b0033002738f

def z527 : W := mkw 0x9001031201010c10 0x09001031201010c1 0xee2b073303231832 0xfee2b07330323183

def z528 : W := mkw 0xc1b025c013c00e05 0x0c1b025c013c00e0 0x3cf07fc003c00704 0x73cf07fc003c0070

def z529 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xf5d480003cdcc00d 0x0f5d480003cdcc00

def z530 : W := mkw 0x204c586c2c7832a0 0x9204c586c2c7832a 0x7fdc78fc3cf83fff 0xf7fdc78fc3cf83ff

def z531 : W := mkw 0x1001021300050150 0x0100102130005015 0xee2b0733002700f8 0xfee2b0733002700f

def z532 : W := mkw 0x08fe80415af6c346 0x208fe80415af6c34 0xffff80c3ffffc70f 0x4ffff80c3ffffc70

def z533 : W := mkw 0x41feecc03ef2b207 0x341feecc03ef2b20 0xfffff8c03fffc00f 0x0fffff8c03fffc00

def z534 : W := mkw 0x2000182804001020 0x8200018280400102 0x0000383000001830 0x2000038300000183

def z535 : W := mkw 0x80ffb7ba81000c07 0xc80ffb7ba81000c0 0xfcffffffc3003f07 0xffcffffffc3003f0

def z536 : W := mkw 0x004c000000000000 0x0004c00000000000 0x5ccc000000000000 0x05ccc00000000000

def z537 : W := mkw 0x0000000012828000 0x2000000001282800 0x0000000003c7c004 0x00000000003c7c00

def z538 : W := mkw 0x41b02c8016801005 0x041b02c801680100 0x01c038001c000000 0x001c038001c00000

def z539 : W := mkw 0xd100494137c53f50 0x1d100494137c53f5 0x030000003fe73fff 0x0030000003fe73ff

def z540 : W := mkw 0xc9b065c573cc6fc5 0x1c9b065c573cc6fc 0xf434c7cfe3dce7cd 0xdf434c7cfe3dce7c

def z541 : W := mkw 0x004c000008300000 0x0004c00000830000 0x11c400003c180000 0x011c400003c18000

def z542 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xc8efbf3fc0000000 0xac8efbf3fc000000

def z543 : W := mkw 0x000000001ab28000 0x2000000001ab2800 0x010000003cd8c000 0x0010000003cd8c00

def z544 : W := mkw 0xc1b17ffab7c03e05 0xdc1b17ffab7c03e0 0x3df07fffffc03f07 0xf3df07fffffc03f0

def z545 : W := mkw 0xc1b2a5c013c28e07 0x2c1b2a5c013c28e0 0xa03387c003c7c704 0x4a03387c003c7c70

def z546 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xf414800020dce7cd 0x0f414800020dce7c

def z547 : W := mkw 0x00fe800000000006 0x000fe80000000000 0xfcff800020dcc00d 0x0fcff800020dcc00

def z548 : W := mkw 0x08b064c5604c63c5 0x108b064c5604c63c 0xfcf4ffcfe0dce7cd 0xffcf4ffcfe0dce7c

def z549 : W := mkw 0x304d5a3f2c3d31f0 0x9304d5a3f2c3d31f 0xdfcf783f3c3f38fb 0xbdfcf783f3c3f38f

def z550 : W := mkw 0x900001011bb78d50 0x2900001011bb78d5 0x030000003fffffff 0x0030000003ffffff

def z551 : W := mkw 0x80b0010013800c04 0x080b0010013800c0 0x3df007003fc03f07 0x73df007003fc03f0

def z552 : W := mkw 0xc1fc7de837c03e05 0x9c1fc7de837c03e0 0x7dfc7ffc3fc03f07 0xf7dfc7ffc3fc03f0

def z553 : W := mkw 0xe1b06dc43ff83ea5 0x1e1b06dc43ff83ea 0x3ff07fc03ff83fff 0x73ff07fc03ff83ff

def z554 : W := mkw 0x9001031201010c10 0x09001031201010c1 0x4e2b0730032338fb 0xb4e2b0730032338f

def z555 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x1bcc783c3c381832 0x21bcc783c3c38183

def z556 : W := mkw 0x0000000100040140 0x0000000010004014 0xa000000300040704 0x4a00000030004070

def z557 : W := mkw 0xc9006dc5654c7fc1 0x1c9006dc5654c7fc 0x00007fcfc0003fc0 0xf00007fcfc0003fc

def z558 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xe22b0733032707fc 0xce22b0733032707f

def z559 : W := mkw 0x08000005400c41c0 0x008000005400c41c 0xf414c0cfc01cc0c8 0xdf414c0cfc01cc0c

def z560 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xabfb80001fe7c006 0x0abfb80001fe7c00

def z561 : W := mkw 0x08fec0447afae286 0x308fec0447afae28 0xffffc0ccffffc00f 0x0ffffc0ccffffc00

def z562 : W := mkw 0xc1fea5c01bf28e07 0x2c1fea5c01bf28e0 0xffff87c03fffc70f 0x4ffff87c03fffc70

def z563 : W := mkw 0x8001031201000c00 0x08001031201000c0 0xec2b073303003f07 0xfec2b073303003f0

def z564 : W := mkw 0xd1b12f9217811c15 0x0d1b12f9217811c1 0x0beb3f301f231832 0x20beb3f301f23183

def z565 : W := mkw 0x20fffebea40830a7 0xd20fffebea40830a 0xfcffffffc00038f0 0xffcffffffc00038f

def z566 : W := mkw 0xc10049403ff2be00 0x3c10049403ff2be0 0x030000003fffff0f 0x0030000003fffff0

def z567 : W := mkw 0x284c582d6c3c71e0 0x9284c582d6c3c71e 0xdfccf83ffc3cf8fb 0xbdfccf83ffc3cf8f

def z568 : W := mkw 0x49b06cc576cc73c5 0x149b06cc576cc73c 0xf5d4f8cffcdce7cd 0xdf5d4f8cffcdce7c

def z569 : W := mkw 0x2000582c2c3830a0 0x92000582c2c3830a 0x0300783c3c3838fb 0xb0300783c3c3838f

def z570 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xf414c0cfc00027c0 0xdf414c0cfc00027c

def z571 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xffffbf303fffc00f 0x2ffffbf303fffc00

def z572 : W := mkw 0x08000005400c41c0 0x008000005400c41c 0xe404800fc01ce7cd 0xde404800fc01ce7c

def z573 : W := mkw 0x00feb4a880000007 0xc00feb4a88000000 0xfcfff8ccc0000000 0x0fcfff8ccc000000

def z574 : W := mkw 0x1001021200010010 0x0100102120001001 0x020b003000230030 0x0020b00300023003

def z575 : W := mkw 0x08fec0447afae286 0x308fec0447afae28 0x11d4c0ccfcd8c000 0x011d4c0ccfcd8c00

def z576 : W := mkw 0x004d36ba80000001 0xc004d36ba8000000 0x5ccc7fffc0000000 0xf5ccc7fffc000000

def z577 : W := mkw 0xc9006dc5654c7fc1 0x1c9006dc5654c7fc 0xf414ffcfe0dcffcd 0xff414ffcfe0dcffc

def z578 : W := mkw 0x0000000012800000 0x0000000001280000 0x010000003fc00007 0x0010000003fc0000

def z579 : W := mkw 0xc1b02d8017801c05 0x0c1b02d8017801c0 0x3df03f003fc01807 0x23df03f003fc0180

def z580 : W := mkw 0x0000400420082080 0x1000040042008208 0x5e0c403c203838fb 0xb5e0c403c203838f

def z581 : W := mkw 0x61fc7cec3ef832a5 0x961fc7cec3ef832a 0x11d478cc3cd80000 0x011d478cc3cd8000

def z582 : W := mkw 0x00b2800012828006 0x200b280001282800 0x0023000003030000 0x0002300000303000

def z583 : W := mkw 0x41b06cc036c03205 0x141b06cc036c0320 0x3df078c03fc00007 0x03df078c03fc0000

def z584 : W := mkw 0x90ffb7bb81050d57 0xc90ffb7bb81050d5 0xfcffffffc3070704 0xffcffffffc307070

def z585 : W := mkw 0x00b2800012828006 0x200b280001282800 0xbdf380003fc7c007 0x0bdf380003fc7c00

def z586 : W := mkw 0x004c102800000000 0x8004c10280000000 0x08c8383000000000 0x208c838300000000

def z587 : W := mkw 0x08ffb6fbc0444347 0xc08ffb6fbc044434 0xfcffffffc0c4c704 0xffcffffffc0c4c70

def z588 : W := mkw 0x08fec0457afee3c6 0x308fec0457afee3c 0xffff80003fffe7cf 0x0ffff80003fffe7c

def z589 : W := mkw 0x00b06c8024003005 0x100b06c802400300 0x3df07fc03c003803 0x73df07fc03c00380

def z590 : W := mkw 0x90014317210d2dd0 0x190014317210d2dd 0xfe2f473f233f3fff 0xffe2f473f233f3ff

def z591 : W := mkw 0x2000102c000800a0 0x82000102c000800a 0x0000003c000000f0 0x80000003c000000f

def z592 : W := mkw 0x90b3a79381050d57 0x490b3a79381050d5 0xee3b87f3c3273fff 0xfee3b87f3c3273ff

def z593 : W := mkw 0x08fef4ece0486287 0xd08fef4ece048628 0x10d4f8cce0d8c000 0x010d4f8cce0d8c00

def z594 : W := mkw 0xb04d133f093d0df0 0x8b04d133f093d0df 0xee2f073f033f3fff 0xfee2f073f033f3ff

def z595 : W := mkw 0xe1fc7de83ff03e25 0x9e1fc7de83ff03e2 0x3ff87ff03fe03f37 0x73ff87ff03fe03f3

def z596 : W := mkw 0x8000414021402e00 0x18000414021402e0 0x3c3047c023c03f07 0x73c3047c023c03f0

def z597 : W := mkw 0x08000005400c41c0 0x008000005400c41c 0xf414800fe0dcc0cd 0x8f414800fe0dcc0c

def z598 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xe4230703030727cd 0xde4230703030727c

def z599 : W := mkw 0x0000404020402200 0x1000040402040220 0xf414c0c020dce70d 0x5f414c0c020dce70

def z600 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xa023073303073ff4 0xfa023073303073ff

def z601 : W := mkw 0x080176ffe04c63c1 0xd080176ffe04c63c 0xf414ffffe0dce7cd 0xff414ffffe0dce7c

def z602 : W := mkw 0x004c102800000000 0x8004c10280000000 0x10c4780c00000000 0x010c4780c0000000

def z603 : W := mkw 0xc1b16fd237c03e05 0x1c1b16fd237c03e0 0xfdfb7ff33fc03f07 0xffdfb7ff33fc03f0

def z604 : W := mkw 0x00ff923a9ab28006 0xe00ff923a9ab2800 0xffff803fffffc00f 0x8ffff803fffffc00

def z605 : W := mkw 0x104f821308378152 0x2104f82130837815 0xc20f8033003fc0f8 0x8c20f8033003fc0f

def z606 : W := mkw 0x004d123a00000000 0x8004d123a0000000 0xfcef7f3f00000000 0xffcef7f3f0000000

def z607 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffbf3000000000 0x2fcffbf300000000

def z608 : W := mkw 0x004c000008300000 0x0004c00000830000 0x420c000000380008 0x0420c00000038000

def z609 : W := mkw 0x904f831309378d52 0x2904f831309378d5 0xee2f8733033fffff 0xfee2f8733033ffff

def z610 : W := mkw 0x204f923e883800a2 0xc204f923e883800a 0xc20f803fc03800f8 0x8c20f803fc03800f

def z611 : W := mkw 0x004c000008300000 0x0004c00000830000 0xffdc80003cfcc00f 0x0ffdc80003cfcc00

def z612 : W := mkw 0x41b024c012c00205 0x041b024c012c0020 0x001000c000c00000 0x0001000c000c0000

def z613 : W := mkw 0x98014357614d6fd0 0x198014357614d6fd 0xf437c7cfe3dfe7cd 0xdf437c7cfe3dfe7c

def z614 : W := mkw 0xe1b07dec37c83ea5 0x9e1b07dec37c83ea 0x3df07ffc3fc03ff7 0xf3df07ffc3fc03ff

def z615 : W := mkw 0x08b3a6d3c0444347 0x408b3a6d3c044434 0xa03387c3c0c4c704 0x4a03387c3c0c4c70

def z616 : W := mkw 0x0000000400080080 0x0000000040008008 0x4004000c001800c8 0x84004000c001800c

def z617 : W := mkw 0x0000480424083080 0x1000048042408308 0x5dc4780c3c1838cb 0xb5dc4780c3c1838c

def z618 : W := mkw 0x41fefce8b6c03207 0xd41fefce8b6c0320 0x11d4f8ccfcc00000 0x011d4f8ccfcc0000

def z619 : W := mkw 0x00fe800008328006 0x200fe80000832800 0xfeff8000003fc008 0x0feff8000003fc00

def z620 : W := mkw 0x00fea48000000007 0x000fea4800000000 0xfcffffc000000000 0x7fcffffc00000000

def z621 : W := mkw 0xb04d1b3b0d351d70 0x8b04d1b3b0d351d7 0xefeb3f331f273fff 0xfefeb3f331f273ff

def z622 : W := mkw 0x00feb4a880000007 0xc00feb4a88000000 0xf4d4f8cfc0000000 0xdf4d4f8cfc000000

def z623 : W := mkw 0x0800004140444340 0x0080000414044434 0xe41080c3c0c4e7cd 0xde41080c3c0c4e7c

def z624 : W := mkw 0xa04c592c2d383ca0 0x9a04c592c2d383ca 0x7fec7f3c3f383fff 0xf7fec7f3c3f383ff

def z625 : W := mkw 0x90b3831313878d56 0x290b3831313878d5 0xee3b873303e7ffff 0xfee3b873303e7fff

def z626 : W := mkw 0x0000404020402200 0x1000040402040220 0x0000000020c02705 0x00000000020c0270

def z627 : W := mkw 0xc1fec9403ff2be06 0x3c1fec9403ff2be0 0xffff80003fffff0f 0x0ffff80003fffff0

def z628 : W := mkw 0x0000404420482280 0x1000040442048228 0x741440cc20d827cd 0xd741440cc20d827c

def z629 : W := mkw 0xc1fc6dc03ff03e05 0x1c1fc6dc03ff03e0 0x7ffc7fc03ff83f0f 0x77ffc7fc03ff83f0

def z630 : W := mkw 0xc1fead801fb29c07 0x2c1fead801fb29c0 0x0beb3f001f231802 0x20beb3f001f23180

def z631 : W := mkw 0x200048042c3830a0 0x1200048042c3830a 0x5704400c3c3838fb 0x95704400c3c3838f

def z632 : W := mkw 0x004f923a80000002 0xc004f923a8000000 0x000b003000000000 0x0000b00300000000

def z633 : W := mkw 0xb0ffffbfad3d3df7 0xdb0ffffbfad3d3df 0xffffffffff3f3fff 0xfffffffffff3f3ff

def z634 : W := mkw 0x20fe902c1aba80a6 0xa20fe902c1aba80a 0xffff803c3fffc0ff 0x8ffff803c3fffc0f

def z635 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xd0dff8ffc0000000 0x8d0dff8ffc000000

def z636 : W := mkw 0x00b0480036803004 0x100b048003680300 0x3df078003fc03807 0x33df078003fc0380

def z637 : W := mkw 0x00b3a69280000007 0x400b3a6928000000 0xbcf3ffc3c0000000 0x7bcf3ffc3c000000

def z638 : W := mkw 0x00ffb6ba88300007 0xc00ffb6ba8830000 0xfffffffffc38000b 0xffffffffffc38000

def z639 : W := mkw 0xc1b06dc025403e05 0x1c1b06dc025403e0 0x3cf07fc000003f00 0x73cf07fc000003f0

def z640 : W := mkw 0x0000000000000000 0x0000000000000000 0x5404000020180009 0x0540400002018000

def z641 : W := mkw 0xc1ffbfba97801c07 0xcc1ffbfba97801c0 0xfdffffffdf001802 0xffdffffffdf00180

def z642 : W := mkw 0xc1ffb7fa93c00e07 0xcc1ffb7fa93c00e0 0xfcffffffc3c00704 0xffcffffffc3c0070

def z643 : W := mkw 0x08fec045604c63c6 0x108fec045604c63c 0xfcffc0cfe0dce7cd 0xdfcffc0cfe0dce7c

def z644 : W := mkw 0x000000001ab28000 0x2000000001ab2800 0x030000001f230002 0x0030000001f23000

def z645 : W := mkw 0xc1b025c013c00e05 0x0c1b025c013c00e0 0x3df007c03fc00707 0x43df007c03fc0070

def z646 : W := mkw 0x20fffebeac3830a7 0xd20fffebeac3830a 0x5fef7f3c3c3838fb 0xb5fef7f3c3c3838f

def z647 : W := mkw 0x4100484036c03200 0x14100484036c0320 0x010000003cc00000 0x0010000003cc0000

def z648 : W := mkw 0x8000010001000c00 0x08000010001000c0 0x0820070003001802 0x2082007000300180

def z649 : W := mkw 0xd1b12f9317851d55 0x0d1b12f9317851d5 0xefeb3f331f273fff 0xfefeb3f331f273ff

def z650 : W := mkw 0x90ffb7bb81050d57 0xc90ffb7bb81050d5 0xeeeb3f3303273fff 0xfeeeb3f3303273ff

def z651 : W := mkw 0x004c102800000000 0x8004c10280000000 0x400c003c00000000 0x8400c003c0000000

def z652 : W := mkw 0x00fff6faa0402207 0xd00fff6faa040220 0xfcffffffe0c02705 0xffcffffffe0c0270

def z653 : W := mkw 0xc1006dc025403e01 0x1c1006dc025403e0 0x34107fc020c03f05 0x734107fc020c03f0

def z654 : W := mkw 0x00fe800000000006 0x000fe80000000000 0xfeff80000327000f 0x0feff80000327000

def z655 : W := mkw 0x8000010001000c00 0x08000010001000c0 0xee2b070003273f0f 0x7ee2b070003273f0

def z656 : W := mkw 0x204c582d2c3c31e0 0x9204c582d2c3c31e 0xffcc783f3c3c3fff 0xfffcc783f3c3c3ff

def z657 : W := mkw 0x00b2800012828006 0x200b280001282800 0xee3b800003e7c00f 0x0ee3b800003e7c00

def z658 : W := mkw 0x90ff83131bb78d56 0x290ff83131bb78d5 0xffff87033fffc70f 0x4ffff87033fffc70

def z659 : W := mkw 0x0800404460486280 0x1080040446048628 0x000040ccc0000000 0x0000040ccc000000

def z660 : W := mkw 0x00fe902800000006 0x800fe90280000000 0xfcfff83c00000000 0xbfcfff83c0000000

def z661 : W := mkw 0x280048456c7c73e0 0x1280048456c7c73e 0xf714c0cffcfcffff 0xdf714c0cffcfcfff

def z662 : W := mkw 0x8000010001000c00 0x08000010001000c0 0x6e28073003203fff 0xf6e28073003203ff

def z663 : W := mkw 0x00feb4a880000007 0xc00feb4a88000000 0x00c0380000000000 0x000c038000000000

def z664 : W := mkw 0x00fe800008300006 0x000fe80000830000 0xffff80003c38000b 0x0ffff80003c38000

def z665 : W := mkw 0x280048456c7c73e0 0x1280048456c7c73e 0x030000003cfcffff 0x0030000003cfcfff

def z666 : W := mkw 0x20fed82c3ebab0a6 0xb20fed82c3ebab0a 0xfffff80c3fffc00f 0x0fffff80c3fffc00

def z667 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x341040c020dce7cd 0x5341040c020dce7c

def z668 : W := mkw 0x9000010001010c10 0x09000010001010c1 0x0200000003231832 0x0020000000323183

def z669 : W := mkw 0x0000480024003000 0x1000048002400300 0x11c078003c000000 0x011c078003c00000

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a2b000003230002 0x00a2b00000323000

def z671 : W := mkw 0x90b1279301050d55 0x090b1279301050d5 0xfefb7ff303273fff 0xffefb7ff303273ff

def z672 : W := mkw 0x204c18280c301020 0x8204c18280c30102 0x01c038001c000000 0x001c038001c00000

def z673 : W := mkw 0x9001435321452f50 0x19001435321452f5 0xfe3b47f323e73fff 0xffe3b47f323e73ff

def z674 : W := mkw 0xb00049052d3d3df0 0x1b00049052d3d3df 0x030000003f3f3fff 0x0030000003f3f3ff

def z675 : W := mkw 0x98ffc3577bffefd6 0x398ffc3577bffefd 0xffffc7ffffffffff 0xfffffc7fffffffff

def z676 : W := mkw 0xc10025c001400e01 0x0c10025c001400e0 0x000007c000000700 0x4000007c00000070

def z677 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xee2b07030327070f 0x4ee2b07030327070

def z678 : W := mkw 0xc1fffffaa5403e07 0xdc1fffffaa5403e0 0xfcffffffc0003f00 0xffcffffffc0003f0

def z679 : W := mkw 0x00b2a48080000007 0x400b2a4808000000 0x001080c0c0000000 0x0001080c0c000000

def z680 : W := mkw 0xb0ffdb3f3fbfbdf6 0xbb0ffdb3f3fbfbdf 0xffffff3f3fffffff 0xfffffff3f3ffffff

def z681 : W := mkw 0x00ff82121ab28006 0x200ff82121ab2800 0xffff87333fffc00f 0xfffff87333fffc00

def z682 : W := mkw 0x00b3a69280000007 0x400b3a6928000000 0xec3b87f3c0000000 0xfec3b87f3c000000

def z683 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x53cc783c3c3800f8 0x853cc783c3c3800f

def z684 : W := mkw 0x0000000100040140 0x0000000010004014 0xee2b0003032727cf 0xdee2b0003032727c

def z685 : W := mkw 0x2000582c240830a0 0x92000582c240830a 0x4e08783c002038fb 0xb4e08783c002038f

def z686 : W := mkw 0x0000000000000000 0x0000000000000000 0xa010800000c4c004 0x0a010800000c4c00

def z687 : W := mkw 0x0000480024003000 0x1000048002400300 0x0000780000003800 0x3000078000000380

def z688 : W := mkw 0xc900494577cc7fc0 0x1c900494577cc7fc 0xf514c0cfffdcffcf 0xdf514c0cfffdcffc

def z689 : W := mkw 0x204c582c3ebab0a0 0xb204c582c3ebab0a 0x5fcc783c3ffff8ff 0xb5fcc783c3ffff8f

def z690 : W := mkw 0x08b0404572cc63c4 0x108b0404572cc63c 0xfdf4c0cfffdce7cf 0xdfdf4c0cfffdce7c

def z691 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0x13d480003fffc00f 0x013d480003fffc00

def z692 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0x5fdc80003cf8c00b 0x05fdc80003cf8c00

def z693 : W := mkw 0x0000000000000000 0x0000000000000000 0x1014c0ccc0000000 0x01014c0ccc000000

def z694 : W := mkw 0x08000005400c41c0 0x008000005400c41c 0x00000000001cc0c8 0x000000000001cc0c

def z695 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xe400000320dce7cd 0xde400000320dce7c

def z696 : W := mkw 0xc1b025c013c00e05 0x0c1b025c013c00e0 0x2c3007c003c03f07 0x72c3007c003c03f0

def z697 : W := mkw 0xc1fffffab7c03e07 0xdc1fffffab7c03e0 0x3dfb7ff03fc03f07 0x73dfb7ff03fc03f0

def z698 : W := mkw 0x0001021200000000 0x0000102120000000 0xfc3fc7ffc0000000 0xffc3fc7ffc000000

def z699 : W := mkw 0xd1b06dc137c53f55 0x1d1b06dc137c53f5 0x3ff07fc03fe73fff 0x73ff07fc03fe73ff

def z700 : W := mkw 0xc1b065c033c02e05 0x1c1b065c033c02e0 0x343047c023c02705 0x5343047c023c0270

def z701 : W := mkw 0x0000000100040140 0x0000000010004014 0xf414c0cfc00427cd 0xdf414c0cfc00427c

def z702 : W := mkw 0x8000010001000c00 0x08000010001000c0 0x0000000003003f07 0x00000000003003f0

def z703 : W := mkw 0xe1fc7dec3ff83ea5 0x9e1fc7dec3ff83ea 0x3df47fcc3fd83f07 0x73df47fcc3fd83f0

def z704 : W := mkw 0x00b0000012800004 0x000b000001280000 0x09e000001f000002 0x009e000001f00000

def z705 : W := mkw 0x084ec045687ee3c2 0x3084ec045687ee3c 0xf61fc0cfe0ffe7cd 0xdf61fc0cfe0ffe7c

def z706 : W := mkw 0x284c586c6c7872a0 0x9284c586c6c7872a 0x11d4f8ccfcd8c000 0x011d4f8ccfcd8c00

def z707 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x5fcc78fffc3838fb 0xf5fcc78fffc3838f

def z708 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x2de07fc01f003f07 0x72de07fc01f003f0

def z709 : W := mkw 0xc1b02d8017801c05 0x0c1b02d8017801c0 0x09e03f001f003f02 0x709e03f001f003f0

def z710 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xf3ff80003fffc00c 0x0f3ff80003fffc00

def z711 : W := mkw 0x8000010001000c00 0x08000010001000c0 0xee2b073003273fff 0xfee2b073003273ff

def z712 : W := mkw 0x80b06d8025003c05 0x180b06d8025003c0 0x3df07fc03f003f07 0x73df07fc03f003f0

def z713 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff80003fffe70f 0x5ffff80003fffe70

def z714 : W := mkw 0x004d36ba88300001 0xc004d36ba8830000 0x5fcc7ffffc38000b 0xf5fcc7ffffc38000

def z715 : W := mkw 0x00b3b6ba80000007 0xc00b3b6ba8000000 0xf437ffffc0000000 0xff437ffffc000000

def z716 : W := mkw 0x004e80001ab28002 0x2004e80001ab2800 0xdfcf80003fffc00f 0x0dfcf80003fffc00

def z717 : W := mkw 0x204ed82c2c3ab0a2 0xb204ed82c2c3ab0a 0xffeff83c3f3ff8ff 0xbffeff83c3f3ff8f

def z718 : W := mkw 0x104f923b88378152 0xe104f923b8837815 0xc20f803fc03fc0f8 0x8c20f803fc03fc0f

def z719 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xd014c0cfe0dce7cd 0x8d014c0cfe0dce7c

def z720 : W := mkw 0x204c182c0c3810a0 0x8204c182c0c3810a 0x0bc8383c1c2018f2 0xa0bc8383c1c2018f

def z721 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xfe3fc7ffe3ffffff 0xffe3fc7ffe3fffff

def z722 : W := mkw 0xc9b02d85578c5dc5 0x0c9b02d85578c5dc 0xc9e4bf0fdf1cd8ca 0xac9e4bf0fdf1cd8c

def z723 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0xfdf07fc03fc43f0f 0x7fdf07fc03fc43f0

def z724 : W := mkw 0x204c18280c301020 0x8204c18280c30102 0x5fcc38303c3838fb 0xb5fcc38303c3838f

def z725 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xee2f873fc3273fff 0xfee2f873fc3273ff

def z726 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0x2c207fffc0000000 0xf2c207fffc000000

def z727 : W := mkw 0x28004845644c73e0 0x128004845644c73e 0xf414c0cfe0dcfffd 0xdf414c0cfe0dcfff

def z728 : W := mkw 0x204c582c2c3ab0a0 0xb204c582c2c3ab0a 0x5fcc783c3c3ff8fb 0xb5fcc783c3c3ff8f

def z729 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x1dd07fc03cc03f03 0x71dd07fc03cc03f0

def z730 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff80c3ffffc00f 0x4ffff80c3ffffc00

def z731 : W := mkw 0xe1fc35ec1bf80ea5 0x8e1fc35ec1bf80ea 0x623c07fc03f807fc 0xc623c07fc03f807f

def z732 : W := mkw 0x000136ba9ab28001 0xe000136ba9ab2800 0x03007fffffffc00f 0xf03007fffffffc00

def z733 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x0bc838301c2038f2 0x20bc838301c2038f

def z734 : W := mkw 0x00fea4801ab28007 0x200fea4801ab2800 0xffffbf003fffc00f 0x2ffffbf003fffc00

def z735 : W := mkw 0x08fff6ffe04c63c7 0xd08fff6ffe04c63c 0x08eb3f3020dce7cd 0x208eb3f3020dce7c

def z736 : W := mkw 0xc14fdb7ab7c03e02 0xdc14fdb7ab7c03e0 0xc10f803fffc03f07 0x8c10f803fffc03f0

def z737 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfeffffffc3230002 0xffeffffffc323000

def z738 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xfc34c0cfe3dce7cf 0xdfc34c0cfe3dce7c

def z739 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff80033fffc00f 0xdffff80033fffc00

def z740 : W := mkw 0x00b3b6ba92828007 0xe00b3b6ba9282800 0xa033ffffc3c7c004 0xfa033ffffc3c7c00

def z741 : W := mkw 0x90feb5a981050d57 0xc90feb5a981050d5 0x12d4f8ccc3273fff 0x012d4f8ccc3273ff

def z742 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0xf414ffffe0dcc00d 0xff414ffffe0dcc00

def z743 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xf614c0cfe3ffe7cf 0xdf614c0cfe3ffe7c

def z744 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffffc0ccffffc00f 0x0ffffc0ccffffc00

def z745 : W := mkw 0x20ffb6ba88300027 0xc20ffb6ba8830002 0xfeffffffc0200030 0xffeffffffc020003

def z746 : W := mkw 0xc1b06dc437c83e85 0x1c1b06dc437c83e8 0x3df07fcc3fc03fc7 0xf3df07fcc3fc03fc

def z747 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xffffffffdf3fc00a 0xfffffffffdf3fc00

def z748 : W := mkw 0xc1b025c013c00e05 0x0c1b025c013c00e0 0x3df07fc03fc00707 0x73df07fc03fc0070

def z749 : W := mkw 0x9001031301050d50 0x09001031301050d5 0x2e2b073303233ff7 0xf2e2b073303233ff

def z750 : W := mkw 0x004d36ba80000001 0xc004d36ba8000000 0xfcef7fffc0000000 0xffcef7fffc000000

def z751 : W := mkw 0x004c48002c303000 0x1004c48002c30300 0x5fcc78303c3838fb 0xb5fcc78303c3838f

def z752 : W := mkw 0xd1b127d313c50f55 0x0d1b127d313c50f5 0x203007c303c00704 0x4203007c303c0070

def z753 : W := mkw 0x00b06cc024403205 0x100b06cc02440320 0x3df07fc03cc03f07 0x73df07fc03cc03f0

def z754 : W := mkw 0x00b2800012828006 0x200b280001282800 0xfdf780003fdfc00f 0x0fdf780003fdfc00

def z755 : W := mkw 0xc9b06dc477c87e85 0x1c9b06dc477c87e8 0x7df4ffccffd8ffcf 0xf7df4ffccffd8ffc

def z756 : W := mkw 0x00ffb6ba9ab00007 0xc00ffb6ba9ab0000 0xfffffffffff8000f 0xffffffffffff8000

def z757 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0x18ffffffc0000000 0xf18ffffffc000000

def z758 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffffc00c3fffc00f 0x9ffffc00c3fffc00

def z759 : W := mkw 0x004fb6ba80000003 0xc004fb6ba8000000 0x000b7fffc0000000 0xf000b7fffc000000

def z760 : W := mkw 0x00fea4801ab28007 0x200fea4801ab2800 0xffffffcfffffc00f 0xfffffffcfffffc00

def z761 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff80003ffff80f 0x3ffff80003ffff80

def z762 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xee2b073323ffffff 0xfee2b073323fffff

def z763 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xffeb07333f273fff 0xfffeb07333f273ff

def z764 : W := mkw 0xc1b2edc037c2be07 0x3c1b2edc037c2be0 0x3df0ffc03fc0ff07 0x73df0ffc03fc0ff0

def z765 : W := mkw 0x000000001ab28000 0x2000000001ab2800 0xff3f80003fffc00f 0x0ff3f80003fffc00

def z766 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffe0180009 0xffcffffffe018000

def z767 : W := mkw 0x284c18694c745360 0x8284c18694c74536 0xabd8b8f3dce4df36 0x6abd8b8f3dce4df3

def z768 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0xc00b7fffc0000000 0xfc00b7fffc000000

def z769 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xfcd4f8cfe0dce7cd 0xffcd4f8cfe0dce7c

def z770 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xf4d4ffffc0000000 0xff4d4ffffc000000

def z771 : W := mkw 0x204c586c2c7832a0 0x9204c586c2c7832a 0xffdcf8fffcf83fff 0xfffdcf8fffcf83ff

def z772 : W := mkw 0x204c18280c301020 0x8204c18280c30102 0x4bc838301c2018fa 0xa4bc838301c2018f

def z773 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffc004000d 0xffcffffffc004000

def z774 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0xfffb7ff03fe73fff 0xffffb7ff03fe73ff

def z775 : W := mkw 0xc14eedc02d72be03 0x3c14eedc02d72be0 0xc20fffc0003fff08 0x7c20fffc0003fff0

def z776 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x7fdc78fc3c3838fb 0xf7fdc78fc3c3838f

def z777 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xfffffffffcf8c00b 0xffffffffffcf8c00

def z778 : W := mkw 0x00b064c032c02205 0x100b064c032c0220 0x3df07fc03fc02707 0x73df07fc03fc0270

def z779 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xfe2f473f03273fff 0xffe2f473f03273ff

def z780 : W := mkw 0x204c586c2c7832a0 0x9204c586c2c7832a 0x5fdc78fc3cf838fb 0xb5fdc78fc3cf838f

def z781 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xa8fbffffc0000000 0xfa8fbffffc000000

def z782 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xfffffffffcffc008 0xffffffffffcffc00

def z783 : W := mkw 0xc9b06dc477c87e85 0x1c9b06dc477c87e8 0x3df07fccffc03f07 0x73df07fccffc03f0

def z784 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xe014c0cfc0dce7cc 0xde014c0cfc0dce7c

def z785 : W := mkw 0x2000582c240830a0 0x92000582c240830a 0x5fc8783c3c2038fb 0xb5fc8783c3c2038f

def z786 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xffffffcfffffc00f 0x4ffffffcfffffc00

def z787 : W := mkw 0x00fea4801ab28007 0x200fea4801ab2800 0xffff87c03fffc00f 0x4ffff87c03fffc00

def z788 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xdbff80003fffc00a 0x0dbff80003fffc00

def z789 : W := mkw 0x004d36ba80000001 0xc004d36ba8000000 0x400c7fffc0000000 0xf400c7fffc000000

def z790 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x5fcc38303c3838fb 0x25fcc38303c3838f

def z791 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfdfffffffc000003 0xffdfffffffc00000

def z792 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xe03fffffc0000000 0xfe03fffffc000000

def z793 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xfdff80003fdfc004 0x0fdff80003fdfc00

def z794 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xe22b073303273fff 0xce22b073303273ff

def z795 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xf5f780003fdfc00d 0x0f5f780003fdfc00

def z796 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xffffffffffe30007 0xfffffffffffe3000

def z797 : W := mkw 0x000000001ab28000 0x2000000001ab2800 0xa32300003fffc00f 0x0a32300003fffc00

def z798 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3df4ffc03fd8ff07 0x73df4ffc03fd8ff0

def z799 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x13c4783c3c3838fb 0xb13c4783c3c3838f

def z800 : W := mkw 0xe1b06dc437c83ea5 0x1e1b06dc437c83ea 0x3df07fc03fc03ff7 0x73df07fc03fc03ff

def z801 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x19f07fc03fc03f02 0x719f07fc03fc03f0

def z802 : W := mkw 0xc900494577cc7fc0 0x1c900494577cc7fc 0x010000003fc03fc7 0x0010000003fc03fc

def z803 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3ff87ff03fe03f37 0x73ff87ff03fe03f3

def z804 : W := mkw 0x0800004140444340 0x0080000414044434 0xf414c0cfe0dcc70d 0xdf414c0cfe0dcc70

def z805 : W := mkw 0x00ffb6ba88300007 0xc00ffb6ba8830000 0xfdfffffffc180000 0xffdfffffffc18000

def z806 : W := mkw 0xc1b06dc437c83e85 0x1c1b06dc437c83e8 0xfdf4ffcc3fdcffcf 0xffdf4ffcc3fdcffc

def z807 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x5fdcf8fcfc3838fb 0xb5fdcf8fcfc3838f

def z808 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x1de07fc03f003f03 0x71de07fc03f003f0

def z809 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x7df87ff03fc03f07 0xf7df87ff03fc03f0

def z810 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xfe2f0733233f3fff 0xffe2f0733233f3ff

def z811 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0x4e087fffc02038fb 0xf4e087fffc02038f

def z812 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x19f07fc03fc03f07 0x219f07fc03fc03f0

def z813 : W := mkw 0x9001031301050d50 0x09001031301050d5 0x0a2b073003233ff2 0x20a2b073003233ff

def z814 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0xdfcf783c3c3f38fb 0xbdfcf783c3c3f38f

def z815 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x2de03f003fc03f07 0x72de03f003fc03f0

def z816 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3ff07fc03fe03fff 0x73ff07fc03fe03ff

def z817 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfeffffffc0201832 0xffeffffffc020183

def z818 : W := mkw 0x004c102808300000 0x8004c10280830000 0x5fcc783c3c3838fb 0xb5fcc783c3c3838f

def z819 : W := mkw 0xc9004945654c7fc0 0x1c9004945654c7fc 0x0000000000003fc0 0x00000000000003fc

def z820 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xaa2b073303273ff6 0xfaa2b073303273ff

def z821 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x7df07fc03fc03fcf 0xf7df07fc03fc03fc

def z822 : W := mkw 0x00fc34a800000005 0x800fc34a80000000 0xfcfcffffc0000000 0xffcfcffffc000000

def z823 : W := mkw 0x2000582c240830a0 0x92000582c240830a 0x09c0783c1c0038f2 0xb09c0783c1c0038f

def z824 : W := mkw 0x08004845644c73c0 0x108004845644c73c 0xf5d4f8cffcdce7cd 0xdf5d4f8cffcdce7c

def z825 : W := mkw 0x204c18280c301020 0x8204c18280c30102 0x0bc838301c2038fb 0x20bc838301c2038f

def z826 : W := mkw 0xb04d5b3f2d3d3df0 0x9b04d5b3f2d3d3df 0xb1e77f0f3f1f0704 0x4b1e77f0f3f1f070

def z827 : W := mkw 0x10014a1324053150 0x110014a132405315 0xdfcb78333c2738fb 0xbdfcb78333c2738f

def z828 : W := mkw 0x90ff83131bb78d56 0x290ff83131bb78d5 0x11d487333cd8fff0 0xf11d487333cd8fff

def z829 : W := mkw 0x9001031301050d50 0x09001031301050d5 0x0a2b073303273fff 0xf0a2b073303273ff

def z830 : W := mkw 0xc1b02dc017c01e05 0x0c1b02dc017c01e0 0x3df03fc03fc01f07 0x63df03fc03fc01f0

def z831 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xf414c0ffe0dcfffd 0xff414c0ffe0dcfff

def z832 : W := mkw 0x08000045404c43c0 0x008000045404c43c 0xf41480cfe0dcc7cd 0xcf41480cfe0dcc7c

def z833 : W := mkw 0x00b136ba80000005 0xc00b136ba8000000 0xfcfb7fffc0000000 0xffcfb7fffc000000

def z834 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xee3b87f3c3273fff 0xfee3b87f3c3273ff

def z835 : W := mkw 0xc1b06d8037803c05 0x1c1b06d8037803c0 0x3de07f003f003f07 0x73de07f003f003f0

def z836 : W := mkw 0xc9b06dc477c87e85 0x1c9b06dc477c87e8 0xfdf4ffccffdcff0f 0x7fdf4ffccffdcff0

def z837 : W := mkw 0x0000480024003000 0x1000048002400300 0x1dc078303c0038f3 0xb1dc078303c0038f

def z838 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x4fc838303c3838fb 0xb4fc838303c3838f

def z839 : W := mkw 0x204c182c0c3810a0 0x8204c182c0c3810a 0x4fcc383c1c3838fb 0xb4fcc383c1c3838f

def z840 : W := mkw 0x004e80001ab28002 0x2004e80001ab2800 0x030b00003fffc00f 0x0030b00003fffc00

def z841 : W := mkw 0x08004845644c73c0 0x108004845644c73c 0xffdcf8fffcfcffff 0xfffdcf8fffcfcfff

def z842 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff80303fffc0ff 0x8ffff80303fffc0f

def z843 : W := mkw 0x00b280001ab28006 0x200b280001ab2800 0x032300003fffc00f 0x0032300003fffc00

def z844 : W := mkw 0x08fec0457afee3c6 0x308fec0457afee3c 0x0beb40cfdf2327c2 0xd0beb40cfdf2327c

def z845 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfeffffffc0270008 0xffeffffffc027000

def z846 : W := mkw 0x00fea4809ab28007 0x600fea4809ab2800 0xffff80c0ffffc00f 0x0ffff80c0ffffc00

def z847 : W := mkw 0x00b280001ab28006 0x200b280001ab2800 0xef3b80003fffc00f 0x0ef3b80003fffc00

def z848 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x35f07fc03fc02705 0x535f07fc03fc0270

def z849 : W := mkw 0x00feb4a89ab28007 0xe00feb4a89ab2800 0xffffffccffffc00f 0x7ffffffccffffc00

def z850 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0x11d4fffffcd8c000 0xf11d4fffffcd8c00

def z851 : W := mkw 0x00ffb6ba92800007 0xc00ffb6ba9280000 0xfdffffffffdcc00f 0xffdffffffffdcc00

def z852 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x4bcc783c1c3838fa 0xb4bcc783c1c3838f

def z853 : W := mkw 0x00ffb6ba92828007 0xe00ffb6ba9282800 0xfcffffffc3030000 0xffcffffffc303000

def z854 : W := mkw 0x20b2d82c368ab0a6 0xb20b2d82c368ab0a 0xa033f83c03c7f8f4 0xba033f83c03c7f8f

def z855 : W := mkw 0x00fd36ba80000005 0xc00fd36ba8000000 0x7cfc7fffc0000000 0xf7cfc7fffc000000

def z856 : W := mkw 0x200048042c3830a0 0x1200048042c3830a 0x5fc878303c3838fb 0xb5fc878303c3838f

def z857 : W := mkw 0x084f923fc83ec1c2 0xe084f923fc83ec1c 0xc20f803fc03fc0c8 0x8c20f803fc03fc0c

def z858 : W := mkw 0x80b0258013800c05 0x080b0258013800c0 0x3df07fc03fc03f07 0x73df07fc03fc03f0

def z859 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3ff07fc03fe73f0f 0x73ff07fc03fe73f0

def z860 : W := mkw 0xc1b02dc017c01e05 0x0c1b02dc017c01e0 0x09e03fc01f001f02 0x609e03fc01f001f0

def z861 : W := mkw 0x00ffb6ba88300007 0xc00ffb6ba8830000 0xfffffffffc3838fb 0xffffffffffc3838f

def z862 : W := mkw 0x00ffb6ba88328007 0xe00ffb6ba8832800 0xfffffffffc3fc00b 0xffffffffffc3fc00

def z863 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x53cc783c3c3838f8 0xb53cc783c3c3838f

def z864 : W := mkw 0x00ffb6ba92828007 0xe00ffb6ba9282800 0xfcffffffe3dfc00d 0xffcffffffe3dfc00

def z865 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x29f07fc01fc03f06 0x729f07fc01fc03f0

def z866 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xffffffffdf27000f 0xfffffffffdf27000

def z867 : W := mkw 0x004fb6ba80000003 0xc004fb6ba8000000 0xf41fffffc0000000 0xff41fffffc000000

def z868 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3df07fcfffc03f07 0xf3df07fcfffc03f0

def z869 : W := mkw 0x00b3b6ba80000007 0xc00b3b6ba8000000 0xa033ffcfc0000000 0x4a033ffcfc000000

def z870 : W := mkw 0x8000490025003c00 0x18000490025003c0 0x1dc07f003c003f03 0x71dc07f003c003f0

def z871 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xfe3b47f303273fff 0xffe3b47f303273ff

def z872 : W := mkw 0xc1b2edc037c2be07 0x3c1b2edc037c2be0 0xfdf7ffc03fdfff0f 0x7fdf7ffc03fdfff0

def z873 : W := mkw 0xd9b127d353c54f55 0x0d9b127d353c54f5 0xa03387c3c3c7c704 0x4a03387c3c3c7c70

def z874 : W := mkw 0x204c182c0c3810a0 0x8204c182c0c3810a 0x5fcc383c3c3818fb 0xa5fcc383c3c3818f

def z875 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffc00020c9 0xffcffffffc00020c

def z876 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffc0c4c004 0xffcffffffc0c4c00

def z877 : W := mkw 0xc1b02d8017801c05 0x0c1b02d8017801c0 0x29e03f001f001f06 0x629e03f001f001f0

def z878 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0xffdcf8fffcfcf8ff 0xfffdcf8fffcfcf8f

def z879 : W := mkw 0x00ffb6ba92828007 0xe00ffb6ba9282800 0xfdffffffffc7c007 0xffdffffffffc7c00

def z880 : W := mkw 0x00b136ba92800005 0xc00b136ba9280000 0x3df07fffffc00007 0xf3df07fffffc0000

def z881 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0xdfccf83c3c3cf8fb 0xbdfccf83c3c3cf8f

def z882 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x31f07fc03fc03f07 0x431f07fc03fc03f0

def z883 : W := mkw 0x0000404020402200 0x1000040402040220 0xf414c0cfe0dce70d 0xdf414c0cfe0dce70

def z884 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xf414c0cfe0d8e7c0 0xdf414c0cfe0d8e7c

def z885 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff80303fffd83f 0x2ffff80303fffd83

def z886 : W := mkw 0x00feb4a880000007 0xc00feb4a88000000 0xfcf4ffcfc0000000 0xffcf4ffcfc000000

def z887 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xee2b47ffc3273fff 0xfee2b47ffc3273ff

def z888 : W := mkw 0x00fea48000000007 0x000fea4800000000 0xfcffffcfc0000000 0xffcffffcfc000000

def z889 : W := mkw 0x08004845644c73c0 0x108004845644c73c 0xf414f8cfe0dcffcd 0xff414f8cfe0dcffc

def z890 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xe01480cfe0dce7cd 0xce01480cfe0dce7c

def z891 : W := mkw 0xc1b02dc017c01e05 0x0c1b02dc017c01e0 0x21f03fc01fc00704 0x421f03fc01fc0070

def z892 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xfdffffffffdfc004 0xffdffffffffdfc00

def z893 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0x34107fffc0000000 0xf34107fffc000000

def z894 : W := mkw 0xc1b06dc437c83e85 0x1c1b06dc437c83e8 0xfdf4ffcfffd83fcf 0xffdf4ffcfffd83fc

def z895 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3df03f003fc03f07 0x23df03f003fc03f0

def z896 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x7fcc783c3c383fff 0xf7fcc783c3c383ff

def z897 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfeffffffe3ffc00f 0xffeffffffe3ffc00

def z898 : W := mkw 0x284f923fc83c41e2 0xc284f923fc83c41e 0xc20f803fc03cc0f8 0x8c20f803fc03cc0f

def z899 : W := mkw 0xd1b3a7d393c50f57 0x4d1b3a7d393c50f5 0xa03387c3c3c70704 0x4a03387c3c3c7070

def z900 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x1014c0cfe0d8c700 0x41014c0cfe0d8c70

def z901 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x29f03fc03fc03f07 0x629f03fc03fc03f0

def z902 : W := mkw 0xc1006dc025403e01 0x1c1006dc025403e0 0x3de07fc03f003f07 0x73de07fc03f003f0

def z903 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xb414c0cfe0dce705 0x5b414c0cfe0dce70

def z904 : W := mkw 0x304f923f883d01f2 0xc304f923f883d01f 0xc20f803fc03f00f8 0x8c20f803fc03f00f

def z905 : W := mkw 0x204ed82c2c3ab0a2 0xb204ed82c2c3ab0a 0xffdff83c3cfff8ff 0xbffdff83c3cfff8f

def z906 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x7df47fcc3fc03f07 0xf7df47fcc3fc03f0

def z907 : W := mkw 0x20b3ee96ac3830a7 0x520b3ee96ac3830a 0xa33387c3fc3838fb 0x4a33387c3fc3838f

def z908 : W := mkw 0xc100494037c03e00 0x1c100494037c03e0 0x3de07f003fc03f07 0x73de07f003fc03f0

def z909 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffc0002705 0xffcffffffc000270

def z910 : W := mkw 0x00b0000012800004 0x000b000001280000 0xffff80003fffc00f 0x0ffff80003fffc00

def z911 : W := mkw 0x10ffb6ba80010017 0xc10ffb6ba8001001 0xfeffffffc0230030 0xffeffffffc023003

def z912 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x5fcc783c3cfcf8ff 0xb5fcc783c3cfcf8f

def z913 : W := mkw 0x204c582c240830a0 0x9204c582c240830a 0x5dcc783c3c0038f3 0xb5dcc783c3c0038f

def z914 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3df07ff03fc03ff7 0xf3df07ff03fc03ff

def z915 : W := mkw 0x204c182c0c3810a0 0x8204c182c0c3810a 0x0bc838301c3818fa 0x20bc838301c3818f

def z916 : W := mkw 0xc9b0494577cc7fc4 0x1c9b0494577cc7fc 0xfdf480003fdcffcf 0x0fdf480003fdcffc

def z917 : W := mkw 0x004e80001ab28002 0x2004e80001ab2800 0xef2f80003fffc00f 0x0ef2f80003fffc00

def z918 : W := mkw 0x00b1269200000005 0x000b126920000000 0xfcffffffc0000000 0xffcffffffc000000

def z919 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xf414c0cfe0dcc704 0xdf414c0cfe0dcc70

def z920 : W := mkw 0x304d123b08350170 0x8304d123b0835017 0xc20b0033002700f8 0x8c20b0033002700f

def z921 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff80303fffc00f 0xbffff80303fffc00

def z922 : W := mkw 0x9001031201010c10 0x09001031201010c1 0x6e2b073003233fff 0xf6e2b073003233ff

def z923 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0x4c087fffc0000000 0xf4c087fffc000000

def z924 : W := mkw 0x004e80001ab28002 0x2004e80001ab2800 0xf71f80003fffc00f 0x0f71f80003fffc00

def z925 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x7fec7f3c3c3838fb 0xf7fec7f3c3c3838f

def z926 : W := mkw 0xc1b06dc437c83e85 0x1c1b06dc437c83e8 0x3df07fc03fd83fcf 0x73df07fc03fd83fc

def z927 : W := mkw 0x284c586c6c7872a0 0x9284c586c6c7872a 0x5fcc783c3cf8f8fb 0xb5fcc783c3cf8f8f

def z928 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xf014c0cfe0dcc7cc 0xcf014c0cfe0dcc7c

def z929 : W := mkw 0x08000045404c43c0 0x008000045404c43c 0xa01480cfc0dcc704 0x4a01480cfc0dcc70

def z930 : W := mkw 0x00b280001ab28006 0x200b280001ab2800 0xf73780003fffc00f 0x0f73780003fffc00

def z931 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xfffffffffffff8ff 0xffffffffffffff8f

def z932 : W := mkw 0xd1b06dc037c13e15 0x1d1b06dc037c13e1 0x3ff07fc03fe33f37 0x73ff07fc03fe33f3

def z933 : W := mkw 0x00feb4a89ab28007 0xe00feb4a89ab2800 0xfffff8cfffffc00f 0xdfffff8cfffffc00

def z934 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0xffcc783c3c3c38ff 0xbffcc783c3c3c38f

def z935 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x7fec783c3f3838ff 0xb7fec783c3f3838f

def z936 : W := mkw 0x0000000100040140 0x0000000010004014 0xf414c0cfe0dce7cd 0xdf414c0cfe0dce7c

def z937 : W := mkw 0xc1ffbfba9fb29c07 0xec1ffbfba9fb29c0 0x0beb3f301f231802 0x20beb3f301f23180

def z938 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x7df47fc03fd83f0f 0x77df47fc03fd83f0

def z939 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xfffff8003fffc00f 0x3fffff8003fffc00

def z940 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xfe3b073323e73fff 0xffe3b073323e73ff

def z941 : W := mkw 0xc1b06dc025403e05 0x1c1b06dc025403e0 0x3df07fc03c003f03 0x73df07fc03c003f0

def z942 : W := mkw 0x2000582c240830a0 0x92000582c240830a 0x5dc4783c3c1838fb 0xb5dc4783c3c1838f

def z943 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xaa2b073303273fff 0x6aa2b073303273ff

def z944 : W := mkw 0x004c000008300000 0x0004c00000830000 0xffff80003fffc00f 0x0ffff80003fffc00

def z945 : W := mkw 0x284c582c6c3870a0 0x9284c582c6c3870a 0x5fccf83cfc38f8fb 0xb5fccf83cfc38f8f

def z946 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xee2b073303233ff2 0xfee2b073303233ff

def z947 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0xffcc783f3c3838fb 0xfffcc783f3c3838f

def z948 : W := mkw 0x00fe90281ab28006 0xa00fe90281ab2800 0xffff803c3fffc00f 0x8ffff803c3fffc00

def z949 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xb1f7ffcfffdfc004 0x4b1f7ffcfffdfc00

def z950 : W := mkw 0x0000248000000001 0x0000024800000000 0x00007fcfc0000000 0xf00007fcfc000000

def z951 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xf0ffffffc0000000 0xcf0ffffffc000000

def z952 : W := mkw 0xc9004945654c7fc0 0x1c9004945654c7fc 0x0000000020dcffcd 0x00000000020dcffc

def z953 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xfc34c7cfe0dce7cd 0xffc34c7cfe0dce7c

def z954 : W := mkw 0xa04c112c09380ca0 0x8a04c112c09380ca 0x6e2c073c03383fff 0xf6e2c073c03383ff

def z955 : W := mkw 0x9001031301050d50 0x09001031301050d5 0x4e2b073303233ffb 0xf4e2b073303233ff

def z956 : W := mkw 0xc1b2edc037c2be07 0x3c1b2edc037c2be0 0x3df37fc03fc33f07 0x73df37fc03fc33f0

def z957 : W := mkw 0x004d123a00000000 0x8004d123a0000000 0xfcffffffc0000000 0xffcffffffc000000

def z958 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xfdffffffdc000000 0xffdffffffdc00000

def z959 : W := mkw 0x00b3b6ba80000007 0xc00b3b6ba8000000 0x0010ffffc0000000 0xf0010ffffc000000

def z960 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xee2b073003273fff 0x2ee2b073003273ff

def z961 : W := mkw 0xc90049457ffeffc0 0x3c90049457ffeffc 0x030000003fffffcf 0x0030000003fffffc

def z962 : W := mkw 0x004c00001ab28000 0x2004c00001ab2800 0xffef00003fffc00f 0x0ffef00003fffc00

def z963 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x11d07fc03fc03f07 0x711d07fc03fc03f0

def z964 : W := mkw 0x90b3a79393878d57 0x690b3a79393878d5 0xa03387c3c3c7c704 0x4a03387c3c3c7c70

def z965 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xe22b073303273ffc 0xfe22b073303273ff

def z966 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfeffffffc020000b 0xffeffffffc020000

def z967 : W := mkw 0x000000001ab28000 0x2000000001ab2800 0xc30b00003fffc00f 0x0c30b00003fffc00

def z968 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0x0beb7fffdf230002 0xf0beb7fffdf23000

def z969 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xee2f8733033fffff 0xfee2f8733033ffff

def z970 : W := mkw 0x204ed82cac3830a2 0xd204ed82cac3830a 0x5fccf83cfc3838fb 0xb5fccf83cfc3838f

def z971 : W := mkw 0x00fe90281ab28006 0xa00fe90281ab2800 0xfffff80c3fffc00f 0x0fffff80c3fffc00

def z972 : W := mkw 0xd9016fd7654d7fd1 0x1d9016fd7654d7fd 0x00007fffc0003ff0 0xf00007fffc0003ff

def z973 : W := mkw 0xc1006dc025403e01 0x1c1006dc025403e0 0x3dd07fc03cc03f07 0x73dd07fc03cc03f0

def z974 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0x5cef7fffc0000000 0xf5cef7fffc000000

def z975 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffffc0c03fffc00f 0x5ffffc0c03fffc00

def z976 : W := mkw 0x00ffb6ba88300007 0xc00ffb6ba8830000 0xfeffffffc0380008 0xffeffffffc038000

def z977 : W := mkw 0x9001031301050d50 0x09001031301050d5 0x2e2b073003273fff 0x72e2b073003273ff

def z978 : W := mkw 0x90ffb7ba9bb38c17 0xe90ffb7ba9bb38c1 0x0beb3f301f231832 0x20beb3f301f23183

def z979 : W := mkw 0xb8015b7f654d7ff0 0x9b8015b7f654d7ff 0x00007fffc0003ff0 0xf00007fffc0003ff

def z980 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xffffffffff3b000b 0xfffffffffff3b000

def z981 : W := mkw 0xc9fec9457ffeffc6 0x3c9fec9457ffeffc 0xffff80003fffffcf 0x0ffff80003fffffc

def z982 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0x10d4ffcfc0000000 0x410d4ffcfc000000

def z983 : W := mkw 0x18004045604d63d0 0x118004045604d63d 0xf614c0cfe0ffe7fd 0xdf614c0cfe0ffe7f

def z984 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3df07fc03cc03f00 0x73df07fc03cc03f0

def z985 : W := mkw 0x51b16ed336c53355 0x151b16ed336c5335 0xd3db78f33ce700f8 0x8d3db78f33ce700f

def z986 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0xfdf4ffcfffdcff0f 0xffdf4ffcfffdcff0

def z987 : W := mkw 0x204c18280c301020 0x8204c18280c30102 0x0bc838301c2038f2 0xb0bc838301c2038f

def z988 : W := mkw 0x304d123f083d01f0 0x8304d123f083d01f 0x420c003f003800f8 0x8420c003f003800f

def z989 : W := mkw 0x9801435661496e90 0x19801435661496e9 0x1a3fc7fce3fbd832 0x21a3fc7fce3fbd83

def z990 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffe0d8c000 0xffcffffffe0d8c00

def z991 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xb0f7ffffc0000000 0xfb0f7ffffc000000

def z992 : W := mkw 0x00b136ba80000005 0xc00b136ba8000000 0x08e07fffc0000000 0xf08e07fffc000000

def z993 : W := mkw 0x00ffb6ba88300007 0xc00ffb6ba8830000 0xffffffffdc200002 0xfffffffffdc20000

def z994 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0x00007fcfc0000000 0x400007fcfc000000

def z995 : W := mkw 0x00ffb6ba92800007 0xc00ffb6ba9280000 0xfcffffffc3c00004 0xffcffffffc3c0000

def z996 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0x5fef00003fffc00f 0x05fef00003fffc00

def z997 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xfeeb7f3303273fff 0xffeeb7f3303273ff

def z998 : W := mkw 0xc1006dc025403e01 0x1c1006dc025403e0 0x09c07fc01c003f02 0x709c07fc01c003f0

def z999 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x0bc8783c3c3838fb 0xb0bc8783c3c3838f

def z1000 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x5fcc783c1c2038f2 0xb5fcc783c1c2038f

def z1001 : W := mkw 0x00b0248000000005 0x000b024800000000 0x3cf07fcfc0000000 0xf3cf07fcfc000000

def z1002 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0x54047fffc0000000 0xf54047fffc000000

def z1003 : W := mkw 0x00ffb6ba88300007 0xc00ffb6ba8830000 0xfffffffffcfcc00f 0xffffffffffcfcc00

def z1004 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfeffffffc02000f8 0xffeffffffc02000f

def z1005 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x1014c0cfe0dce7cd 0xd1014c0cfe0dce7c

def z1006 : W := mkw 0x00ffb6ba88328007 0xe00ffb6ba8832800 0xfeffffffc0230000 0xffeffffffc023000

def z1007 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x09e03f001f003f02 0x209e03f001f003f0

def z1008 : W := mkw 0x41b06cc036c03205 0x141b06cc036c0320 0x3df07fc03cc02705 0x73df07fc03cc0270

def z1009 : W := mkw 0x0003b6ba80000003 0xc0003b6ba8000000 0x8003ffffc0000000 0xf8003ffffc000000

def z1010 : W := mkw 0xe90049457ffc7fe0 0x1e90049457ffc7fe 0x030000003ffcffff 0x0030000003ffcfff

def z1011 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xfdffffffffd8c007 0xffdffffffffd8c00

def z1012 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0x1bff80003fffc00f 0x01bff80003fffc00

def z1013 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3df4ffccffc03f07 0x73df4ffccffc03f0

def z1014 : W := mkw 0xc1b06dc437c83e85 0x1c1b06dc437c83e8 0x3df47fcc3fd83f07 0x73df47fcc3fd83f0

def z1015 : W := mkw 0xb80049456d7d7ff0 0x1b80049456d7d7ff 0x030000003fffffff 0x0030000003ffffff

def z1016 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x5bcc783c3c3818fa 0xa5bcc783c3c3818f

def z1017 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0x3ffb00003fffc00f 0x03ffb00003fffc00

def z1018 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0x1014ffffc0000000 0xf1014ffffc000000

def z1019 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0xee2b7fffc327000f 0xfee2b7fffc327000

def z1020 : W := mkw 0x384d123f483d41f0 0x8384d123f483d41f 0xc20f803fc03fc0f8 0x8c20f803fc03fc0f

def z1021 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xf61cc0ffe0fce7fd 0xdf61cc0ffe0fce7f

def z1022 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3df07fc01f003f02 0x73df07fc01f003f0

def z1023 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0x3cf4ffffc0000000 0xf3cf4ffffc000000

def z1024 : W := mkw 0x00b000001ab28004 0x200b000001ab2800 0xfffb00003fffc00f 0x0fffb00003fffc00

def z1025 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0xfdf4ffc03fc03f07 0x7fdf4ffc03fc03f0

def z1026 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xca2b073303273fff 0xaca2b073303273ff

def z1027 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0xfffff83c3ffff8ff 0xbfffff83c3ffff8f

def z1028 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0xfdfb7fc03fc03f07 0x7fdfb7fc03fc03f0

def z1029 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3df07fc03fdcff0f 0x73df07fc03fdcff0

def z1030 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xd0dfffffc0000000 0xfd0dfffffc000000

def z1031 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xf614c0cfe0fcffff 0xdf614c0cfe0fcfff

def z1032 : W := mkw 0x284c586c6c7872a0 0x9284c586c6c7872a 0xffdcf8fcfcfcf8ff 0xbffdcf8fcfcfcf8f

def z1033 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xb8ffffffc0000000 0x6b8ffffffc000000

def z1034 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x11d07fc03cc00700 0x411d07fc03cc0070

def z1035 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xcbef80003fffc00f 0x0cbef80003fffc00

def z1036 : W := mkw 0x204c586c2c7832a0 0x9204c586c2c7832a 0x5fcc783c3cf83fff 0xb5fcc783c3cf83ff

def z1037 : W := mkw 0x004fb6ba80000003 0xc004fb6ba8000000 0x0004ffffc0000000 0xf0004ffffc000000

def z1038 : W := mkw 0x0000080004001000 0x0000008000400100 0x4fc838301c2038fb 0xb4fc838301c2038f

def z1039 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x1fc8783c3c2038f3 0xb1fc8783c3c2038f

def z1040 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xefeb00003fffc00f 0x0efeb00003fffc00

def z1041 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0x00c07fffc0000000 0xf00c07fffc000000

def z1042 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0xc004ffffc0000000 0xfc004ffffc000000

def z1043 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0xe4007fffc0000000 0xfe4007fffc000000

def z1044 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3df07fc03fc00704 0x73df07fc03fc0070

def z1045 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff87003fffc00f 0x7ffff87003fffc00

def z1046 : W := mkw 0xc9b06dc477c87e85 0x1c9b06dc477c87e8 0xfdf4ffcfffd8ff07 0xffdf4ffcfffd8ff0

def z1047 : W := mkw 0x8000494025403e00 0x18000494025403e0 0x3df07fc03fc03f07 0x73df07fc03fc03f0

def z1048 : W := mkw 0x0000248000000001 0x0000024800000000 0xf414ffcfc0000000 0xff414ffcfc000000

def z1049 : W := mkw 0x284c586c6c7872a0 0x9284c586c6c7872a 0xffdcf8fffcf8f8fb 0xfffdcf8fffcf8f8f

def z1050 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x01c07fc01c003f00 0x701c07fc01c003f0

def z1051 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x5fdcf83c3cf8f8fb 0xb5fdcf83c3cf8f8f

def z1052 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xabfb80003fffc00f 0x0abfb80003fffc00

def z1053 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff800fffffc00f 0x8ffff800fffffc00

def z1054 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xb014c0cfe0dce7cd 0x4b014c0cfe0dce7c

def z1055 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffc0003803 0xffcffffffc000380

def z1056 : W := mkw 0x00ffb6ba92828007 0xe00ffb6ba9282800 0xfeffffffc3e7c00f 0xffeffffffc3e7c00

def z1057 : W := mkw 0x204c586c2c7832a0 0x9204c586c2c7832a 0xffdcf8fc3cfcffff 0xfffdcf8fc3cfcfff

def z1058 : W := mkw 0x00feb4a89ab28007 0xe00feb4a89ab2800 0xffffb8003fffc00f 0x0ffffb8003fffc00

def z1059 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0xa010ffffc0000000 0xfa010ffffc000000

def z1060 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0x5cdcffffc0000000 0xf5cdcffffc000000

def z1061 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0x3cfb7fffc0000000 0xf3cfb7fffc000000

def z1062 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x3414c0cfe0d8e7c5 0xd3414c0cfe0d8e7c

def z1063 : W := mkw 0x9801031341054d50 0x09801031341054d5 0xee2b8733c327ffff 0xfee2b8733c327fff

def z1064 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x01c0783c1c0038f0 0xb01c0783c1c0038f

def z1065 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffc01cc008 0xffcffffffc01cc00

def z1066 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x1bcc783c3c3838fb 0x21bcc783c3c3838f

def z1067 : W := mkw 0x9001031301050d50 0x09001031301050d5 0x4e2b073003273fff 0xb4e2b073003273ff

def z1068 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xfeffffffc3ffc00c 0xffeffffffc3ffc00

def z1069 : W := mkw 0x204ed82c2c3ab0a2 0xb204ed82c2c3ab0a 0x5fcf783c3c3b38fb 0xb5fcf783c3c3b38f

def z1070 : W := mkw 0x00b3b6ba80000007 0xc00b3b6ba8000000 0xbcf3ffffc0000000 0xfbcf3ffffc000000

def z1071 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0xffdcf83c3c3838fb 0xbffdcf83c3c3838f

def z1072 : W := mkw 0x2000582c2c3830a0 0x92000582c2c3830a 0x1fc0783c3c3838fb 0xb1fc0783c3c3838f

def z1073 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x31f07fc03fc03f04 0x731f07fc03fc03f0

def z1074 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffc3000007 0xffcffffffc300000

def z1075 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0xbdf0ffc3ffc03f07 0x7bdf0ffc3ffc03f0

def z1076 : W := mkw 0x00fe90281ab28006 0xa00fe90281ab2800 0xfffff83c3ffff8ff 0xbfffff83c3ffff8f

def z1077 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xd8ffffffc0000000 0xad8ffffffc000000

def z1078 : W := mkw 0x204c18280c301020 0x8204c18280c30102 0x5fcc783c1c2038fb 0xb5fcc783c1c2038f

def z1079 : W := mkw 0x204c58282c303020 0x9204c58282c30302 0x5fc878303c2038fb 0xb5fc878303c2038f

def z1080 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffc3070004 0xffcffffffc307000

def z1081 : W := mkw 0xc9b06dc477c87e85 0x1c9b06dc477c87e8 0x3df07fc03fd8ff07 0x73df07fc03fd8ff0

def z1082 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x39f07fc03fc01f06 0x639f07fc03fc01f0

def z1083 : W := mkw 0xc9b06dc077c07e05 0x1c9b06dc077c07e0 0x3df0ffc0ffc0ff07 0x73df0ffc0ffc0ff0

def z1084 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xfffffffffffbc002 0xffffffffffffbc00

def z1085 : W := mkw 0x000280001ab28002 0x2000280001ab2800 0x830380003fffc00f 0x0830380003fffc00

def z1086 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffcfc0000000 0x4fcffffcfc000000

def z1087 : W := mkw 0x004d36ba80000001 0xc004d36ba8000000 0x10c47fffc0000000 0xf10c47fffc000000

def z1088 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xffffffffdfe7c006 0xfffffffffdfe7c00

def z1089 : W := mkw 0x00ffb6ba80028007 0xe00ffb6ba8002800 0xfcffffffc007c000 0xffcffffffc007c00

def z1090 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x53cc783c3c3838fb 0x853cc783c3c3838f

def z1091 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffe0c00005 0xffcffffffe0c0000

def z1092 : W := mkw 0x00b136ba80000005 0xc00b136ba8000000 0xfcf4ffffc0000000 0xffcf4ffffc000000

def z1093 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0xfdf07fc33fc03f07 0xffdf07fc33fc03f0

def z1094 : W := mkw 0x00ffb6ba9ab28007 0xe00ffb6ba9ab2800 0xfdfffffffcdcc00d 0xffdfffffffcdcc00

def z1095 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0x00007fffc00038f0 0xf00007fffc00038f

def z1096 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xee3b873303e7ffff 0xfee3b873303e7fff

def z1097 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x7fdc783c3cf838ff 0xb7fdc783c3cf838f

def z1098 : W := mkw 0xc1b2edc0b7c03e07 0x5c1b2edc0b7c03e0 0x3df0ffc0ffc03f07 0x73df0ffc0ffc03f0

def z1099 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0xa0237fffc0000000 0xfa0237fffc000000

def z1100 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0xdfccf83ffc3838fb 0xbdfccf83ffc3838f

def z1101 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x5dcc783c3c1838f0 0xb5dcc783c3c1838f

def z1102 : W := mkw 0xc1b02dc017c01e05 0x0c1b02dc017c01e0 0x2df03fc01fc03f07 0x72df03fc01fc03f0

def z1103 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0xbdf0ffc03fc4ff07 0x7bdf0ffc03fc4ff0

def z1104 : W := mkw 0xc1b02d8017801c05 0x0c1b02d8017801c0 0x09e03f001f003f07 0x209e03f001f003f0

def z1105 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xfc3fc0cfe0dce7cd 0xdfc3fc0cfe0dce7c

def z1106 : W := mkw 0x0800404460486280 0x1080040446048628 0xf414c0cfe0d8e705 0xdf414c0cfe0d8e70

def z1107 : W := mkw 0x00b3a69280000007 0x400b3a6928000000 0xfcf7ffcfc0000000 0xffcf7ffcfc000000

def z1108 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0xffef783c3c3838fb 0xbffef783c3c3838f

def z1109 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfeffffffc32738ff 0xffeffffffc32738f

def z1110 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0x082b7fffc0000000 0xf082b7fffc000000

def z1111 : W := mkw 0x004fb6ba88328003 0xe004fb6ba8832800 0xc20fffffc03fc008 0xfc20fffffc03fc00

def z1112 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xf61fc0cfe0ffe7cd 0xdf61fc0cfe0ffe7c

def z1113 : W := mkw 0x00fe90281ab28006 0xa00fe90281ab2800 0xffffb8303fffc00f 0x2ffffb8303fffc00

def z1114 : W := mkw 0x00fe90289ab28006 0xe00fe90289ab2800 0xffff800cffffc00f 0x0ffff800cffffc00

def z1115 : W := mkw 0x284c586c6c7872a0 0x9284c586c6c7872a 0x7fdcf8fcfcf8ffff 0xf7fdcf8fcfcf8fff

def z1116 : W := mkw 0x004c582824003000 0x9004c58282400300 0x5fcc783c3c2038fb 0xb5fcc783c3c2038f

def z1117 : W := mkw 0x004d36ba80000001 0xc004d36ba8000000 0x08c87fffc0000000 0xf08c87fffc000000

def z1118 : W := mkw 0xd900494577cd7fd0 0x1d900494577cd7fd 0x030000003fffffff 0x0030000003ffffff

def z1119 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xbcf7ffcfc0000000 0x7bcf7ffcfc000000

def z1120 : W := mkw 0x61fefcec3efab2a7 0xb61fefcec3efab2a 0x11d4f8cc3cd8c000 0x011d4f8cc3cd8c00

def z1121 : W := mkw 0xc1b02d8017801c05 0x0c1b02d8017801c0 0x3df07fc01f003f07 0x73df07fc01f003f0

def z1122 : W := mkw 0xd1b1279313850d55 0x0d1b1279313850d5 0xa023070303070704 0x4a02307030307070

def z1123 : W := mkw 0x00ffb6ba88328007 0xe00ffb6ba8832800 0xfeffffffc33fc00f 0xffeffffffc33fc00

def z1124 : W := mkw 0x00b0248012800005 0x000b024801280000 0xfdf4ffcfffdcc00f 0xffdf4ffcfffdcc00

def z1125 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xeceb7fffc0000000 0xfeceb7fffc000000

def z1126 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3ffb7fc03fe33f07 0x73ffb7fc03fe33f0

def z1127 : W := mkw 0x204ed82c2c3ab0a2 0xb204ed82c2c3ab0a 0x5fccf83c3c38f8fb 0xb5fccf83c3c38f8f

def z1128 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xfc1cc0ffe0dce7cd 0xffc1cc0ffe0dce7c

def z1129 : W := mkw 0x00b280001ab28006 0x200b280001ab2800 0xbff380003fffc00f 0x0bff380003fffc00

def z1130 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xbbff80003fffc006 0x0bbff80003fffc00

def z1131 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x5fcc783c3f3f38ff 0xb5fcc783c3f3f38f

def z1132 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xb3f780003fffc00f 0x0b3f780003fffc00

def z1133 : W := mkw 0x00b280001ab28006 0x200b280001ab2800 0xa13380003fdfc004 0x0a13380003fdfc00

def z1134 : W := mkw 0xc1b06dc437c83e85 0x1c1b06dc437c83e8 0x7ffc7ffc3ff83fff 0xf7ffc7ffc3ff83ff

def z1135 : W := mkw 0x00ffb6ba92800007 0xc00ffb6ba9280000 0xffffffffffe7000f 0xfffffffffffe7000

def z1136 : W := mkw 0x00fe90281ab28006 0xa00fe90281ab2800 0xfffff8ffffffc00f 0xffffff8ffffffc00

def z1137 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xfc14c0cfe0dcffcf 0xffc14c0cfe0dcffc

def z1138 : W := mkw 0x304f923f083f81f2 0xa304f923f083f81f 0xc20f803f003fc0f8 0x8c20f803f003fc0f

def z1139 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xca2b073303273ffa 0xfca2b073303273ff

def z1140 : W := mkw 0x00b136ba80000005 0xc00b136ba8000000 0x10d07fffc0000000 0xf10d07fffc000000

def z1141 : W := mkw 0x9001031301050d50 0x09001031301050d5 0xfe3f873303273fff 0xffe3f873303273ff

def z1142 : W := mkw 0xc1b02dc017c01e05 0x0c1b02dc017c01e0 0x09e03f001fc01f06 0x209e03f001fc01f0

def z1143 : W := mkw 0x20fe90281ab28026 0xa20fe90281ab2802 0xffff80303fffc03f 0x0ffff80303fffc03

def z1144 : W := mkw 0xc1b2edc037c2be07 0x3c1b2edc037c2be0 0xfffbffc03fe7ff0f 0x7fffbffc03fe7ff0

def z1145 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x09e07fc03fc03f07 0x709e07fc03fc03f0

def z1146 : W := mkw 0x00b3b6ba80000007 0xc00b3b6ba8000000 0x00237fffc0000000 0xf00237fffc000000

def z1147 : W := mkw 0x0000480424083080 0x1000048042408308 0x5fcc783c3c3838fb 0xb5fcc783c3c3838f

def z1148 : W := mkw 0x00ffb6ba88328007 0xe00ffb6ba8832800 0xfeffffffe0ffc00d 0xffeffffffe0ffc00

def z1149 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x35d07fc03cc03f05 0x735d07fc03cc03f0

def z1150 : W := mkw 0x00ffb6ba92828007 0xe00ffb6ba9282800 0xfcffffffc0c0c000 0xffcffffffc0c0c00

def z1151 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xf414c0cfe0dcc70d 0x4f414c0cfe0dcc70

def z1152 : W := mkw 0x00b3b6ba80000007 0xc00b3b6ba8000000 0xec3bffffc0000000 0xfec3bffffc000000

def z1153 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x4fc8783c1c2038fb 0xb4fc8783c1c2038f

def z1154 : W := mkw 0xc1b02dc017c01e05 0x0c1b02dc017c01e0 0x3df07fc01fc01f06 0x73df07fc01fc01f0

def z1155 : W := mkw 0x204c182c0c3810a0 0x8204c182c0c3810a 0x5fcc783c1c3818fa 0xb5fcc783c1c3818f

def z1156 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0xbdf37fc03fc73f07 0x7bdf37fc03fc73f0

def z1157 : W := mkw 0x80b0490037803c04 0x180b0490037803c0 0x3df07f003fc03f07 0x73df07f003fc03f0

def z1158 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0xffffffc03fffff0f 0x7ffffffc03fffff0

def z1159 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xd3df80003fffc00f 0x0d3df80003fffc00

def z1160 : W := mkw 0x004fb6ba80000003 0xc004fb6ba8000000 0xdccfffffc0000000 0xfdccfffffc000000

def z1161 : W := mkw 0x00feb4a81ab28007 0xa00feb4a81ab2800 0xfffffffc3fffc00f 0xffffffffc3fffc00

def z1162 : W := mkw 0x08004845644c73c0 0x108004845644c73c 0xf514c0cffcdcffcf 0xdf514c0cffcdcffc

def z1163 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xf4f7ffcfc0000000 0xdf4f7ffcfc000000

def z1164 : W := mkw 0x000000001ab28000 0x2000000001ab2800 0x0b2b00003fffc00f 0x00b2b00003fffc00

def z1165 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x55c4783c3c1838f9 0xb55c4783c3c1838f

def z1166 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xb014c0cfe0dce7c4 0xdb014c0cfe0dce7c

def z1167 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xf437c0cfe3dfe7cd 0xdf437c0cfe3dfe7c

def z1168 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x5fef783c3f3b38fb 0xb5fef783c3f3b38f

def z1169 : W := mkw 0x00b136ba80000005 0xc00b136ba8000000 0x20307fffc0000000 0xf20307fffc000000

def z1170 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x4bcc383c3c3838fb 0xa4bcc383c3c3838f

def z1171 : W := mkw 0x284c586c6c7872a0 0x9284c586c6c7872a 0x5fcc78fcfc3838fb 0xb5fcc78fcfc3838f

def z1172 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x1dc4783c3c1838f3 0xb1dc4783c3c1838f

def z1173 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff80003ffff8ff 0x0ffff80003ffff8f

def z1174 : W := mkw 0x204ed82c2c3830a2 0x9204ed82c2c3830a 0xdfcff83c3c3838fb 0xbdfcff83c3c3838f

def z1175 : W := mkw 0x08000045404c43c0 0x008000045404c43c 0xe41480cfc0dce7cd 0xde41480cfc0dce7c

def z1176 : W := mkw 0x00fea4801ab28007 0x200fea4801ab2800 0xfffff8c03fffc00f 0x0fffff8c03fffc00

def z1177 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xbdf780003fdfc007 0x0bdf780003fdfc00

def z1178 : W := mkw 0x2000582c240830a0 0x92000582c240830a 0x11c0783c3c0038f0 0xb11c0783c3c0038f

def z1179 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xfe1cc0cfe0fce7cf 0xdfe1cc0cfe0fce7c

def z1180 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xfe3fc0ffe3ffffff 0xffe3fc0ffe3fffff

def z1181 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xfdd4c0cffcdce7cf 0xdfdd4c0cffcdce7c

def z1182 : W := mkw 0xd1b3a7d313c78f57 0x2d1b3a7d313c78f5 0xa03387c303c7c704 0x4a03387c303c7c70

def z1183 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x1fc878303c3838fb 0x31fc878303c3838f

def z1184 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0x1cc07fffc0000000 0xf1cc07fffc000000

def z1185 : W := mkw 0xc1b02d8017801c05 0x0c1b02d8017801c0 0x3df03f003fc03f07 0x73df03f003fc03f0

def z1186 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0xd014c0cfe0dce7c8 0xdd014c0cfe0dce7c

def z1187 : W := mkw 0xc1006dc037c03e01 0x1c1006dc037c03e0 0x1dc07fc03fc03f07 0x71dc07fc03fc03f0

def z1188 : W := mkw 0x08004045604c63c0 0x108004045604c63c 0x5414c0cfe0d8e7c9 0xd5414c0cfe0d8e7c

def z1189 : W := mkw 0x00ffb6ba88300007 0xc00ffb6ba8830000 0xffffffffff3f000f 0xfffffffffff3f000

def z1190 : W := mkw 0x000136ba80000001 0xc000136ba8000000 0xfc3fffffc0000000 0xffc3fffffc000000

def z1191 : W := mkw 0x00ffb6ba92800007 0xc00ffb6ba9280000 0xfdffffffdf000002 0xffdffffffdf00000

def z1192 : W := mkw 0x204c586c2c7832a0 0x9204c586c2c7832a 0x5fcc78fc3c383ffb 0xf5fcc78fc3c383ff

def z1193 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xc8efffffc0000000 0xfc8efffffc000000

def z1194 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x7ff87fc03fe03f0f 0x77ff87fc03fe03f0

def z1195 : W := mkw 0xc1006dc025403e01 0x1c1006dc025403e0 0x11c07fc03c003f00 0x711c07fc03c003f0

def z1196 : W := mkw 0x004d36ba80000001 0xc004d36ba8000000 0xfcdcffffc0000000 0xffcdcffffc000000

def z1197 : W := mkw 0x00ffb6ba80000007 0xc00ffb6ba8000000 0xfcffffffc00038f0 0xffcffffffc00038f

def z1198 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xe33f80003fffc00f 0x0e33f80003fffc00

def z1199 : W := mkw 0xc1b2edc037c03e07 0x1c1b2edc037c03e0 0xbdf3ffc03fc03f07 0x7bdf3ffc03fc03f0

def z1200 : W := mkw 0xc1b06dc037c2be05 0x3c1b06dc037c2be0 0x3df07fc03fc7ff07 0x73df07fc03fc7ff0

def z1201 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x3df07fc03fc00707 0x43df07fc03fc0070

def z1202 : W := mkw 0x8000090005001c00 0x08000090005001c0 0x2de03f001f003f07 0x72de03f001f003f0

def z1203 : W := mkw 0x004fb6ba80000003 0xc004fb6ba8000000 0xec2fffffc0000000 0xfec2fffffc000000

def z1204 : W := mkw 0x00ffb6ba88328007 0xe00ffb6ba8832800 0xfcffffffc018c000 0xffcffffffc018c00

def z1205 : W := mkw 0x00feb4a89ab28007 0xe00feb4a89ab2800 0xfffff8fcffffc00f 0xbfffff8fcffffc00

def z1206 : W := mkw 0x00fe80001ab28006 0x200fe80001ab2800 0xffff80003fffe0cf 0x9ffff80003fffe0c

def z1207 : W := mkw 0x204c582c2c3830a0 0x9204c582c2c3830a 0x1bcc783c3c3838f2 0xb1bcc783c3c3838f

def z1208 : W := mkw 0xc1b06dc037c03e05 0x1c1b06dc037c03e0 0x1de07f003fc03f07 0x31de07f003fc03f0

def z1209 : W := mkw 0x00ffb6ba92800007 0xc00ffb6ba9280000 0xfdfffffffcc00000 0xffdfffffffcc0000

def z1210 : W := mkw 0x08000045404c43c0 0x008000045404c43c 0xf414c0cfc0dcc7cc 0xdf414c0cfc0dcc7c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z8,z2,z4,z5,z6]),(0,[z9,z0,z2,z10,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z11]),(0,[z0,z7,z2,z12,z4,z5,z6]),(0,[z13,z0,z14,z2,z4,z5,z6]),(1,[z15,z7,z2,z4,z5,z6])],[(0,[z0,z7,z2,z4,z16,z5,z6]),(0,[z17,z0,z7,z2,z4,z5,z6])],[(0,[z18,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z19,z20,z5,z6]),(0,[z0,z7,z2,z4,z5,z21,z6]),(0,[z0,z7,z2,z22,z4,z5,z6]),(1,[z0,z7,z23,z4,z5,z24])],[(0,[z0,z7,z25,z2,z4,z5,z6]),(0,[z26,z0,z7,z2,z4,z5,z27])],[(0,[z0,z7,z2,z28,z4,z5,z6]),(0,[z0,z7,z2,z4,z29,z5,z6]),(0,[z30,z0,z7,z2,z4,z5,z6])],[(0,[z31,z0,z7,z2,z4,z5,z6]),(0,[z32,z0,z7,z2,z4,z5,z6]),(0,[z33,z34,z7,z2,z4,z5,z6])],[(0,[z35,z0,z7,z2,z4,z5,z6]),(0,[z7,z2,z4,z36,z5,z37,z6]),(0,[z0,z7,z2,z4,z5,z38,z39]),(0,[z40,z0,z7,z2,z4,z5,z38])],[(0,[z41,z0,z1,z2,z4,z5,z6]),(0,[z42,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z43,z2,z4,z5,z6]),(0,[z0,z7,z2,z44,z4,z5,z6]),(0,[z0,z45,z7,z2,z4,z5,z6])]],
   [[(0,[z46,z47,z7,z2,z4,z5,z6]),(1,[z0,z2,z4,z5,z6,z48])],[(0,[z0,z7,z2,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z49,z5,z6]),(0,[z0,z7,z50,z2,z4,z5,z6]),(0,[z51,z7,z2,z4,z52,z5,z6]),(0,[z0,z7,z53,z4,z5,z54,z6]),(0,[z0,z7,z2,z4,z5,z6,z55]),(1,[z0,z7,z56,z4,z5,z6]),(0,[z57,z0,z7,z2,z4,z58,z6])],[(0,[z59,z0,z7,z2,z4,z5,z6]),(0,[z41,z7,z60,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z61])],[(1,[z62,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z63,z6]),(0,[z0,z1,z2,z4,z5,z58,z6]),(0,[z64,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z65,z5,z6]),(0,[z0,z7,z2,z4,z66,z5,z6]),(0,[z67,z0,z7,z2,z4,z5,z6]),(1,[z0,z7,z2,z4,z5,z68]),(0,[z69,z0,z7,z2,z4,z5,z24]),(0,[z0,z7,z2,z70,z4,z58,z6])],[(0,[z0,z7,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z71]),(1,[z0,z72,z73,z4,z5,z6])],[(0,[z9,z0,z14,z2,z4,z5,z6]),(0,[z0,z72,z73,z2,z4,z5,z6]),(0,[z74,z0,z7,z2,z4,z5,z6]),(0,[z75,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z76])],[(0,[z0,z7,z2,z77,z4,z5,z6]),(0,[z33,z0,z7,z2,z4,z5,z78]),(0,[z79,z0,z7,z2,z4,z80,z6]),(0,[z0,z7,z2,z4,z5,z81,z6]),(0,[z57,z0,z82,z2,z4,z5,z6])],[(0,[z9,z0,z2,z4,z83,z5,z6]),(0,[z9,z0,z23,z2,z4,z5,z6])]],
   [[(0,[z84,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z85,z5,z6]),(0,[z0,z7,z86,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z87,z6]),(0,[z0,z7,z2,z36,z88,z5,z6]),(0,[z0,z7,z2,z4,z89,z5,z6]),(0,[z0,z7,z2,z90,z4,z5,z6])],[(0,[z91,z0,z7,z2,z4,z5,z6])],[(0,[z0,z7,z92,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z93,z94,z6]),(0,[z95,z0,z7,z2,z4,z5,z96]),(1,[z0,z7,z2,z97,z5,z6])],[(0,[z0,z1,z2,z4,z20,z5,z6]),(0,[z98,z0,z7,z2,z4,z5,z6]),(0,[z95,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z99,z5,z58]),(0,[z40,z0,z7,z2,z4,z100,z5])],[(0,[z101,z0,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z83,z5,z6]),(0,[z102,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z103]),(0,[z0,z7,z2,z4,z104,z5,z6]),(0,[z0,z7,z2,z105,z4,z5,z6]),(0,[z0,z7,z23,z2,z4,z5,z6]),(0,[z106,z0,z7,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z26,z0,z1,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z88,z5,z6]),(0,[z0,z7,z2,z4,z5,z27,z6]),(0,[z0,z7,z2,z4,z5,z107,z6]),(0,[z0,z7,z2,z4,z5,z108,z6]),(0,[z0,z7,z2,z109,z4,z5,z6])],[(0,[z110,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z111,z5,z6]),(0,[z0,z7,z53,z4,z5,z6,z39]),(0,[z0,z7,z2,z4,z112,z5,z58])],[(0,[z46,z7,z2,z4,z5,z6,z38]),(0,[z113,z0,z7,z2,z4,z5,z6]),(0,[z62,z0,z114,z2,z4,z5,z6]),(0,[z79,z115,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z116,z4,z5,z6]),(1,[z117,z0,z7,z4,z54,z6])]],
   [[(0,[z0,z0,z7,z2,z4,z5,z6]),(0,[z59,z0,z7,z2,z4,z5,z118]),(0,[z0,z7,z2,z4,z5,z119,z6]),(0,[z117,z0,z7,z2,z4,z94,z6]),(0,[z57,z0,z120,z2,z4,z5,z6]),(0,[z121,z0,z7,z2,z4,z5,z6])],[(0,[z0,z72,z1,z2,z4,z5,z6]),(0,[z33,z122,z0,z2,z4,z5,z6]),(0,[z0,z72,z7,z123,z4,z5,z6]),(0,[z0,z72,z7,z73,z4,z5,z6]),(0,[z0,z7,z2,z124,z4,z5,z6])],[(0,[z0,z1,z2,z125,z4,z5,z6]),(0,[z126,z9,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z127,z4,z5,z6]),(0,[z128,z0,z7,z2,z4,z5,z6]),(0,[z34,z0,z7,z2,z4,z5,z78]),(0,[z129,z0,z7,z2,z4,z5,z6]),(1,[z130,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z88,z5,z6]),(0,[z0,z7,z2,z70,z131,z5,z6])],[(0,[z13,z0,z7,z2,z4,z132,z6]),(0,[z0,z7,z2,z4,z132,z54,z6]),(0,[z95,z0,z2,z4,z5,z6,z133]),(0,[z134,z0,z7,z2,z4,z5,z133]),(0,[z0,z7,z2,z4,z135,z5,z6])],[(0,[z7,z1,z2,z4,z36,z5,z6]),(0,[z0,z7,z2,z136,z70,z5,z6]),(0,[z0,z7,z2,z4,z5,z137,z6]),(0,[z138,z0,z7,z2,z4,z5,z6]),(0,[z139,z0,z7,z2,z4,z5,z6])],[(0,[z0,z7,z2,z4,z5,z6,z140]),(0,[z141,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z142,z5,z6])],[(1,[z1,z2,z4,z52,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z143]),(0,[z0,z144,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z145,z5,z6]),(0,[z0,z7,z2,z4,z5,z24,z38]),(0,[z146,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z147,z5,z6]),(0,[z0,z148,z7,z2,z4,z5,z6]),(0,[z40,z0,z7,z2,z149,z4,z5])],[(0,[z59,z0,z7,z2,z4,z5,z150]),(0,[z151,z152,z7,z2,z4,z5,z6])]],
   [[(0,[z9,z0,z2,z4,z5,z54,z6]),(0,[z153,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z154,z4,z5,z6]),(0,[z155,z14,z7,z2,z4,z5,z6]),(0,[z156,z0,z7,z2,z4,z5,z6])],[(0,[z157,z0,z7,z2,z4,z5,z6]),(1,[z0,z7,z158,z4,z5,z6]),(0,[z26,z0,z7,z158,z4,z5,z6]),(0,[z26,z0,z7,z2,z4,z5,z159]),(0,[z160,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z161]),(0,[z0,z7,z2,z162,z19,z5,z6]),(0,[z0,z163,z7,z2,z4,z5,z6])],[(0,[z164,z0,z7,z2,z4,z5,z6])],[(0,[z165,z0,z1,z2,z4,z5,z6]),(0,[z46,z0,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z166,z5,z6]),(0,[z167,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z168,z4,z5,z6])],[(0,[z79,z169,z7,z2,z4,z5,z6])],[(0,[z47,z7,z1,z2,z4,z5,z6]),(0,[z62,z7,z1,z2,z4,z5,z6]),(0,[z134,z0,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z170,z4,z5,z6]),(0,[z171,z0,z7,z2,z4,z5,z6]),(0,[z172,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z173,z6]),(0,[z0,z7,z23,z4,z88,z5,z6]),(0,[z117,z0,z7,z174,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z54,z6])],[(0,[z79,z9,z0,z2,z4,z5,z6]),(0,[z175,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z176,z4,z5,z6]),(0,[z0,z7,z2,z177,z4,z5,z6]),(1,[z0,z7,z2,z178,z5,z6]),(0,[z179,z0,z7,z2,z4,z5,z6]),(1,[z151,z0,z2,z20,z5,z6]),(0,[z180,z0,z2,z125,z4,z5,z6]),(1,[z69,z0,z7,z4,z5,z39]),(0,[z0,z7,z2,z4,z5,z181,z6])],[(1,[z1,z2,z182,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z38]),(1,[z0,z7,z25,z4,z5,z6]),(1,[z0,z7,z2,z183,z5,z6]),(0,[z184,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z185])]],
   [[(1,[z186,z0,z2,z4,z5,z6]),(0,[z187,z0,z7,z2,z4,z5,z6]),(0,[z0,z188,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z189]),(0,[z0,z2,z4,z5,z6,z48,z39])],[(0,[z0,z7,z2,z4,z5,z6,z190]),(0,[z0,z1,z2,z191,z4,z5,z6]),(0,[z0,z7,z192,z2,z4,z5,z6]),(0,[z193,z0,z7,z2,z4,z5,z6]),(0,[z57,z45,z7,z2,z4,z5,z6]),(0,[z57,z0,z7,z2,z5,z194,z6]),(0,[z0,z7,z2,z5,z6,z195,z196])],[(0,[z0,z7,z2,z4,z197,z5,z6]),(1,[z0,z198,z2,z4,z5,z6]),(0,[z33,z0,z7,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z20,z5,z6]),(0,[z13,z0,z7,z2,z4,z93,z6]),(0,[z199,z0,z7,z2,z4,z5,z6]),(0,[z200,z0,z7,z2,z4,z5,z6])],[(0,[z9,z0,z53,z2,z4,z5,z6]),(0,[z0,z201,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z202]),(0,[z203,z0,z7,z2,z4,z5,z6]),(0,[z0,z204,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z39,z205])],[(0,[z0,z7,z2,z125,z88,z5,z6]),(0,[z199,z0,z7,z2,z88,z5,z6]),(0,[z0,z206,z7,z2,z4,z5,z6])],[(0,[z9,z0,z2,z4,z5,z6,z39]),(0,[z0,z7,z2,z4,z5,z207,z6]),(0,[z0,z7,z2,z4,z208,z5,z6]),(0,[z0,z7,z2,z209,z4,z5,z6]),(0,[z0,z7,z2,z4,z210,z5,z6])],[(0,[z211,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z212,z4,z5,z6]),(1,[z0,z7,z2,z213,z5,z6])],[(1,[z46,z9,z2,z4,z5,z6]),(1,[z0,z7,z2,z4,z214,z6]),(0,[z26,z51,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z215,z6]),(0,[z0,z7,z2,z4,z216,z5,z6]),(0,[z0,z7,z174,z2,z213,z5,z6])]],
   [[(0,[z0,z7,z53,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z217,z5,z6])],[(0,[z47,z0,z7,z2,z4,z5,z6]),(0,[z26,z0,z218,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z219]),(0,[z0,z7,z2,z4,z220,z5,z6]),(0,[z0,z7,z2,z221,z4,z5,z6])],[(1,[z0,z7,z2,z222,z5,z6]),(0,[z26,z0,z7,z2,z222,z5,z6]),(0,[z0,z7,z223,z2,z4,z5,z6]),(0,[z224,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z225,z6]),(0,[z0,z2,z4,z20,z5,z132,z6]),(0,[z0,z7,z174,z2,z4,z94,z6]),(0,[z57,z0,z7,z2,z4,z5,z226]),(0,[z40,z0,z7,z2,z131,z5,z6])],[(0,[z227,z9,z0,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z5,z6,z205]),(1,[z0,z7,z2,z4,z228,z6]),(0,[z7,z60,z2,z182,z4,z5,z6]),(0,[z26,z7,z2,z4,z5,z37,z6]),(0,[z0,z7,z2,z4,z5,z6,z229])],[(0,[z230,z0,z7,z2,z4,z5,z6]),(0,[z231,z0,z7,z2,z4,z5,z6]),(0,[z232,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z233,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z234])],[(0,[z0,z1,z2,z4,z93,z5,z6]),(0,[z26,z0,z235,z2,z4,z5,z6]),(0,[z236,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z237,z4,z5,z6]),(0,[z0,z7,z2,z238,z4,z5,z6]),(0,[z0,z239,z7,z2,z4,z5,z6]),(1,[z0,z7,z2,z4,z5,z240]),(1,[z0,z7,z2,z4,z112,z5]),(0,[z0,z7,z2,z4,z241,z5,z6]),(0,[z242,z0,z7,z2,z4,z5,z6])],[(0,[z151,z243,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z94,z132,z6]),(0,[z0,z7,z2,z4,z244,z5,z6])],[(0,[z26,z9,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z245,z6])]],
   [[(0,[z41,z0,z7,z182,z4,z5,z6]),(0,[z62,z0,z7,z2,z4,z5,z246]),(0,[z0,z247,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z205])],[(0,[z0,z7,z2,z248,z4,z5,z6]),(1,[z33,z7,z2,z4,z5,z78])],[(0,[z0,z1,z2,z4,z5,z194,z6]),(0,[z249,z95,z7,z2,z4,z5,z6]),(0,[z250,z0,z2,z4,z5,z6,z39]),(0,[z0,z7,z2,z4,z5,z194,z39]),(1,[z139,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z5,z194,z6,z205])],[(0,[z251,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z182,z4,z5,z54,z6]),(0,[z186,z34,z0,z2,z4,z5,z6]),(0,[z151,z0,z2,z4,z20,z5,z6]),(0,[z0,z7,z2,z252,z4,z5,z6]),(0,[z199,z0,z7,z4,z88,z5,z6]),(0,[z0,z7,z2,z4,z253,z5,z194])],[(0,[z254,z0,z7,z2,z4,z5,z6]),(0,[z255,z0,z1,z2,z4,z5,z6]),(0,[z40,z0,z1,z2,z4,z5,z6]),(0,[z0,z256,z7,z2,z4,z5,z6]),(0,[z46,z7,z2,z4,z52,z5,z6]),(0,[z0,z235,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z257,z6]),(0,[z151,z180,z0,z2,z4,z5,z6])],[(0,[z13,z0,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z258,z4,z5,z6]),(0,[z0,z7,z2,z4,z259,z5,z6]),(0,[z260,z0,z7,z2,z4,z5,z6]),(0,[z69,z0,z7,z2,z97,z5,z6]),(0,[z57,z0,z7,z2,z5,z58,z6])],[(0,[z261,z0,z7,z2,z4,z5,z6]),(0,[z9,z0,z73,z2,z4,z5,z6]),(0,[z262,z0,z7,z2,z4,z5,z6]),(0,[z263,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z264,z6]),(0,[z265,z0,z7,z2,z4,z5,z6]),(1,[z0,z7,z2,z5,z6,z195])],[(0,[z117,z0,z1,z2,z4,z5,z6]),(0,[z0,z7,z266,z2,z4,z5,z6]),(0,[z51,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z267,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z268,z6]),(0,[z79,z95,z0,z2,z4,z5,z6])]],
   [[(0,[z69,z0,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z80,z5,z6]),(0,[z0,z7,z2,z269,z4,z5,z6]),(0,[z199,z0,z7,z2,z4,z5,z270]),(1,[z0,z7,z2,z4,z5,z271]),(0,[z0,z7,z2,z4,z272,z5,z6])],[(0,[z0,z7,z2,z273,z4,z5,z6]),(0,[z0,z7,z2,z4,z274,z5,z6]),(0,[z275,z0,z7,z2,z4,z5,z6]),(0,[z276,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z174,z2,z4,z5,z271])],[(0,[z277,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z6]),(1,[z0,z7,z2,z278,z5,z6]),(0,[z79,z0,z7,z2,z4,z5,z219]),(0,[z0,z73,z2,z123,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z279]),(0,[z0,z7,z2,z4,z5,z280,z6]),(0,[z281,z0,z7,z2,z4,z5,z6])],[(0,[z9,z165,z0,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z36,z5,z6]),(0,[z0,z7,z73,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z282]),(0,[z0,z7,z2,z4,z283,z5,z6]),(0,[z284,z0,z7,z2,z4,z5,z6])],[(0,[z59,z0,z7,z60,z4,z5,z6]),(0,[z0,z73,z2,z4,z5,z96,z6]),(0,[z285,z0,z7,z2,z4,z5,z6])],[(0,[z46,z9,z0,z2,z4,z5,z6]),(0,[z46,z7,z2,z182,z4,z5,z6]),(0,[z0,z286,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z287,z4,z5,z6]),(0,[z0,z7,z2,z288,z4,z5,z6])],[(0,[z9,z47,z0,z2,z4,z5,z6]),(0,[z0,z7,z60,z2,z4,z5,z6]),(0,[z0,z7,z2,z289,z4,z5,z6]),(1,[z0,z7,z2,z4,z5,z27]),(0,[z79,z0,z7,z2,z4,z268,z6]),(0,[z0,z7,z174,z4,z94,z5,z6]),(0,[z0,z7,z290,z2,z4,z5,z6])],[(0,[z9,z0,z2,z4,z5,z78,z6]),(0,[z126,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z174,z182,z4,z5,z6]),(0,[z291,z0,z7,z2,z4,z5,z6]),(0,[z51,z0,z7,z2,z4,z52,z6]),(0,[z33,z0,z292,z2,z4,z5,z6]),(0,[z0,z2,z125,z4,z20,z5,z6]),(0,[z293,z0,z7,z2,z4,z5,z6]),(1,[z0,z7,z294,z4,z5,z6])]],
   [[(0,[z0,z7,z2,z4,z36,z5,z6]),(1,[z0,z267,z2,z4,z5,z6]),(0,[z0,z7,z295,z2,z4,z5,z6]),(0,[z296,z0,z7,z2,z4,z5,z6]),(0,[z0,z130,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z149,z4,z5,z6])],[(0,[z0,z7,z297,z2,z4,z5,z6]),(0,[z0,z298,z7,z2,z4,z5,z6])],[(0,[z9,z0,z1,z2,z4,z5,z6]),(0,[z299,z41,z0,z2,z4,z5,z6]),(0,[z299,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z300,z4,z5,z6]),(0,[z79,z0,z72,z2,z4,z5,z6]),(0,[z301,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z302,z6]),(0,[z0,z7,z2,z4,z5,z24,z133]),(0,[z0,z7,z2,z4,z5,z303,z6])],[(0,[z0,z7,z2,z4,z304,z5,z6]),(0,[z0,z7,z2,z4,z305,z5,z6])],[(0,[z0,z1,z2,z4,z52,z5,z6]),(0,[z0,z1,z2,z4,z253,z5,z6]),(0,[z0,z7,z2,z4,z5,z5,z6]),(0,[z0,z7,z306,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z78,z6]),(0,[z0,z7,z2,z4,z307,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z308]),(0,[z0,z7,z2,z162,z4,z5,z194])],[(0,[z79,z0,z7,z2,z4,z5,z309]),(0,[z0,z7,z23,z2,z4,z5,z24]),(0,[z0,z7,z2,z4,z310,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z38]),(0,[z311,z0,z7,z2,z4,z5,z6]),(0,[z312,z0,z7,z2,z5,z6,z196]),(0,[z0,z7,z2,z4,z5,z6,z196])],[(0,[z313,z0,z7,z2,z4,z5,z6]),(0,[z314,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z315,z4,z5,z6])]],
   [[(0,[z9,z151,z0,z2,z4,z5,z6]),(0,[z59,z0,z316,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z317,z6]),(0,[z318,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z97,z4,z5,z6]),(0,[z319,z0,z7,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z37,z6])],[(0,[z0,z7,z2,z320,z4,z5,z6]),(0,[z0,z7,z2,z213,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z133]),(0,[z0,z7,z2,z3,z4,z5,z6]),(0,[z79,z0,z7,z2,z4,z5,z6]),(1,[z0,z7,z2,z4,z5,z219]),(1,[z152,z7,z2,z4,z5,z6]),(0,[z0,z7,z321,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z322]),(0,[z323,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z324,z5,z6])],[(0,[z0,z1,z2,z4,z94,z5,z6]),(0,[z0,z7,z2,z4,z5,z325,z6]),(0,[z0,z7,z2,z36,z5,z58,z6]),(0,[z0,z7,z2,z222,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z326,z6]),(0,[z0,z7,z2,z327,z4,z5,z6]),(0,[z0,z7,z2,z149,z4,z5,z196])],[(0,[z0,z1,z2,z182,z4,z5,z6]),(0,[z0,z1,z174,z2,z4,z5,z6]),(1,[z0,z7,z2,z49,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z328]),(1,[z0,z7,z2,z329,z5,z6]),(0,[z0,z2,z4,z93,z5,z132,z6]),(0,[z0,z7,z2,z70,z4,z131,z6]),(0,[z0,z7,z2,z330,z4,z5,z6])],[(0,[z0,z1,z2,z136,z4,z5,z6]),(0,[z0,z1,z2,z4,z100,z5,z6]),(0,[z0,z7,z2,z4,z5,z331,z6]),(0,[z0,z7,z2,z4,z100,z5,z39]),(0,[z0,z7,z2,z4,z5,z6,z332])],[(0,[z0,z7,z2,z4,z5,z6,z150]),(0,[z333,z0,z7,z2,z4,z5,z6]),(0,[z180,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z334,z5,z6]),(0,[z0,z7,z335,z2,z4,z5,z6]),(0,[z0,z7,z336,z2,z4,z5,z6])]],
   [[(0,[z0,z7,z2,z4,z5,z78,z196]),(0,[z0,z7,z2,z4,z337,z5,z6])],[(0,[z338,z0,z7,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z5,z58,z6]),(0,[z0,z7,z2,z4,z339,z5,z6])],[(0,[z340,z0,z7,z2,z4,z5,z6]),(0,[z341,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z56,z2,z4,z5,z6]),(0,[z0,z7,z342,z2,z4,z5,z6])],[(0,[z46,z41,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z4,z5,z6]),(0,[z0,z7,z343,z2,z4,z5,z6]),(0,[z0,z7,z2,z19,z131,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z344]),(0,[z312,z0,z7,z2,z4,z5,z6])],[(0,[z345,z0,z7,z2,z4,z5,z6]),(0,[z346,z0,z7,z2,z4,z5,z6]),(0,[z347,z0,z7,z2,z4,z5,z6])],[(0,[z0,z1,z2,z162,z4,z5,z6]),(0,[z0,z7,z2,z136,z19,z5,z6]),(0,[z348,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z349,z5,z6])],[(0,[z0,z7,z2,z4,z5,z63,z6]),(0,[z255,z9,z0,z2,z4,z5,z6]),(0,[z9,z33,z0,z2,z4,z5,z6]),(0,[z33,z7,z2,z4,z5,z78,z6]),(0,[z0,z7,z350,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z58,z6]),(0,[z0,z7,z2,z149,z162,z4,z5])],[(0,[z0,z7,z2,z4,z5,z6,z351]),(0,[z0,z7,z352,z2,z4,z5,z6])]],
   [[(0,[z227,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z353,z6]),(0,[z354,z0,z7,z2,z4,z5,z6])],[(0,[z33,z7,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z355,z6]),(0,[z117,z9,z0,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z20,z5,z6]),(0,[z356,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z93,z54,z6]),(0,[z357,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z358,z5,z6])],[(0,[z69,z9,z0,z2,z4,z5,z6]),(0,[z9,z180,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z118,z6]),(0,[z0,z7,z60,z4,z5,z54,z6]),(1,[z0,z7,z2,z4,z80,z6]),(0,[z180,z0,z7,z2,z20,z5,z6]),(0,[z0,z14,z7,z2,z4,z5,z6]),(0,[z0,z7,z359,z2,z4,z5,z6]),(0,[z0,z360,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z361,z4,z5,z6])],[(0,[z0,z1,z2,z70,z4,z5,z6]),(0,[z46,z33,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z362,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z363,z6])],[(0,[z26,z0,z7,z2,z4,z5,z6]),(1,[z0,z7,z2,z4,z5,z159])],[(0,[z364,z0,z7,z2,z4,z5,z6]),(0,[z249,z0,z7,z2,z4,z5,z6]),(0,[z365,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z88,z5,z6,z205])],[(1,[z0,z7,z2,z366,z5,z6]),(0,[z0,z7,z367,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z20,z5,z6])],[(0,[z0,z1,z2,z123,z4,z5,z6]),(0,[z169,z0,z7,z2,z4,z5,z6]),(0,[z117,z0,z7,z2,z4,z54,z6]),(0,[z0,z7,z2,z4,z5,z368,z6])]],
   [[(1,[z47,z1,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z197,z5,z6]),(0,[z9,z0,z2,z125,z4,z5,z6]),(0,[z369,z0,z7,z2,z4,z5,z6]),(0,[z370,z0,z7,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z96,z6]),(0,[z0,z7,z2,z4,z5,z96,z39])],[(0,[z0,z7,z2,z4,z5,z371,z6]),(1,[z243,z7,z2,z4,z5,z6]),(0,[z57,z0,z7,z2,z70,z5,z6]),(0,[z0,z7,z2,z4,z99,z5,z6]),(0,[z40,z0,z7,z2,z4,z5,z194])],[(0,[z0,z7,z218,z2,z4,z5,z6]),(1,[z115,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z372,z4,z5,z6])],[(0,[z0,z1,z2,z4,z131,z5,z6]),(0,[z9,z9,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z373,z5,z6]),(0,[z0,z7,z2,z374,z4,z5,z6])],[(0,[z0,z1,z2,z4,z375,z5,z6]),(0,[z0,z7,z2,z125,z4,z5,z6]),(0,[z0,z7,z2,z4,z112,z5,z6])],[(0,[z376,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z377,z6]),(0,[z40,z0,z7,z294,z4,z5,z6])],[(0,[z0,z198,z7,z2,z4,z5,z6]),(0,[z51,z7,z2,z4,z36,z5,z6]),(0,[z79,z0,z2,z123,z4,z5,z6]),(0,[z0,z7,z2,z20,z88,z5,z6]),(0,[z0,z7,z2,z162,z88,z5,z6]),(0,[z378,z0,z7,z2,z4,z5,z6])]],
   [[(0,[z0,z7,z2,z4,z379,z5,z6]),(0,[z380,z0,z7,z2,z4,z5,z6])],[(0,[z46,z9,z7,z2,z4,z5,z6]),(0,[z79,z0,z2,z4,z5,z96,z6]),(0,[z0,z15,z7,z2,z4,z5,z6])],[],[(0,[z7,z1,z2,z4,z52,z5,z6]),(0,[z151,z0,z7,z2,z4,z5,z6])],[(1,[z0,z218,z2,z4,z5,z6]),(0,[z0,z7,z2,z381,z4,z5,z6])],[(0,[z382,z9,z0,z2,z4,z5,z6]),(0,[z95,z0,z73,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z383,z6]),(0,[z0,z7,z2,z4,z5,z6,z384])],[(1,[z0,z7,z2,z70,z131,z6])],[(0,[z95,z0,z7,z2,z4,z5,z133]),(0,[z0,z7,z2,z385,z4,z5,z6]),(0,[z0,z7,z2,z386,z4,z5,z6])]],
   [[(0,[z59,z0,z1,z2,z4,z5,z6]),(0,[z165,z0,z7,z2,z136,z5,z6]),(1,[z0,z235,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z52,z54,z6]),(1,[z169,z7,z2,z4,z5,z6]),(0,[z387,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z388,z5,z6]),(0,[z0,z7,z2,z389,z4,z5,z6]),(0,[z0,z7,z2,z390,z4,z5,z6])],[(0,[z64,z0,z1,z2,z4,z5,z6]),(1,[z0,z7,z2,z4,z5,z150]),(0,[z0,z7,z2,z4,z5,z391,z6]),(0,[z34,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z329,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z392])],[(1,[z9,z0,z2,z4,z5,z6]),(0,[z393,z0,z7,z2,z4,z5,z6]),(1,[z51,z7,z2,z4,z52,z6]),(0,[z0,z7,z2,z4,z5,z6,z38]),(0,[z394,z0,z7,z2,z4,z5,z6])],[(0,[z395,z0,z7,z2,z4,z5,z6])],[(0,[z7,z1,z2,z182,z4,z5,z6]),(0,[z0,z7,z2,z191,z4,z5,z6]),(0,[z396,z0,z7,z2,z4,z5,z6]),(0,[z40,z0,z7,z2,z162,z5,z6])],[(0,[z397,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z398,z4,z5,z6]),(0,[z399,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z226]),(0,[z0,z7,z2,z4,z5,z6,z400])],[(0,[z0,z7,z2,z4,z5,z401,z6]),(0,[z151,z0,z7,z2,z20,z5,z6]),(0,[z0,z7,z402,z2,z4,z5,z6])],[(0,[z69,z0,z7,z2,z4,z5,z39])]],
   [[(0,[z403,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z404,z5,z6]),(0,[z405,z0,z7,z2,z4,z5,z6])],[(0,[z95,z0,z1,z2,z4,z5,z6]),(0,[z406,z9,z0,z2,z4,z5,z6]),(0,[z407,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z408]),(0,[z0,z7,z174,z2,z4,z54,z6]),(0,[z0,z7,z2,z149,z4,z5,z24])],[(0,[z0,z7,z2,z4,z5,z6,z409]),(0,[z0,z7,z410,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z411,z6])],[(0,[z412,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z36,z5,z194,z6]),(0,[z0,z7,z2,z4,z413,z5,z6]),(1,[z0,z7,z2,z4,z5,z143]),(0,[z414,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z253,z5,z78]),(0,[z0,z7,z2,z415,z4,z5,z6])],[(1,[z1,z2,z4,z36,z5,z6]),(0,[z9,z0,z60,z2,z4,z5,z6]),(0,[z0,z7,z53,z174,z4,z5,z6])],[(0,[z0,z7,z2,z4,z5,z78,z24]),(0,[z0,z7,z2,z4,z416,z5,z6]),(0,[z57,z0,z7,z2,z4,z5,z240])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z417,z0,z7,z2,z4,z5,z6]),(0,[z9,z0,z2,z149,z4,z5,z6]),(0,[z95,z130,z7,z2,z4,z5,z6]),(0,[z418,z0,z7,z2,z4,z5,z6])],[(0,[z419,z0,z7,z2,z4,z5,z6]),(1,[z41,z7,z60,z4,z5,z6]),(0,[z420,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z421,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z422])]],
   [[(0,[z0,z1,z2,z4,z5,z132,z6]),(0,[z9,z0,z2,z4,z5,z194,z6]),(0,[z0,z423,z7,z2,z4,z5,z6]),(0,[z424,z0,z7,z2,z4,z5,z6]),(0,[z180,z0,z14,z2,z4,z5,z6]),(0,[z0,z425,z7,z2,z4,z5,z6]),(0,[z0,z7,z426,z2,z4,z5,z6])],[(0,[z427,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z428,z4,z5,z6])],[(0,[z0,z7,z2,z4,z5,z429,z6]),(0,[z0,z7,z2,z4,z430,z5,z6]),(0,[z57,z139,z7,z2,z4,z5,z6])],[(0,[z255,z0,z7,z2,z4,z5,z6]),(0,[z9,z34,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z431,z5,z6]),(0,[z0,z7,z2,z432,z4,z5,z6]),(0,[z0,z7,z433,z2,z4,z5,z6]),(1,[z249,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z434]),(0,[z0,z7,z2,z4,z435,z5,z6]),(0,[z0,z7,z2,z436,z4,z5,z6])],[(0,[z0,z7,z437,z2,z4,z5,z6]),(0,[z438,z9,z0,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z5,z6,z196]),(0,[z0,z7,z2,z4,z5,z439,z6]),(0,[z186,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z440,z5,z6])],[(0,[z59,z0,z198,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z441,z6]),(1,[z0,z7,z2,z4,z5,z189]),(0,[z0,z7,z2,z4,z5,z194,z6])],[(0,[z117,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z174,z2,z4,z5,z189])],[(0,[z0,z7,z2,z4,z5,z442,z6]),(0,[z157,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z54,z6]),(0,[z443,z0,z7,z2,z4,z5,z6]),(0,[z122,z0,z7,z2,z4,z5,z6]),(0,[z0,z14,z2,z4,z93,z5,z6])]],
   [[(0,[z0,z444,z7,z2,z4,z5,z6])],[(0,[z0,z7,z2,z445,z4,z5,z6]),(0,[z40,z0,z7,z2,z136,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z446]),(0,[z0,z7,z2,z4,z447,z5,z6]),(0,[z0,z7,z2,z149,z4,z100,z6])],[(0,[z9,z0,z2,z4,z5,z325,z6]),(0,[z59,z0,z7,z2,z4,z214,z6]),(0,[z448,z0,z7,z2,z4,z5,z6]),(0,[z449,z0,z7,z2,z4,z5,z6]),(1,[z0,z7,z2,z149,z4,z253])],[(0,[z0,z1,z2,z4,z5,z24,z6]),(0,[z0,z7,z2,z4,z5,z6,z450]),(0,[z9,z0,z2,z4,z5,z451,z6]),(0,[z452,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z453,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z454]),(0,[z155,z0,z7,z2,z4,z5,z6])],[(0,[z0,z7,z2,z162,z4,z5,z78]),(0,[z0,z7,z2,z4,z5,z309,z6]),(0,[z0,z7,z2,z4,z455,z5,z6]),(0,[z0,z7,z2,z4,z5,z456,z6]),(0,[z180,z0,z2,z4,z5,z132,z6]),(0,[z0,z7,z2,z4,z457,z5,z6]),(0,[z0,z7,z2,z458,z4,z5,z6])],[(0,[z0,z7,z2,z4,z5,z459,z6]),(0,[z0,z7,z460,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z461,z6]),(0,[z0,z7,z2,z4,z253,z5,z205])],[(0,[z59,z0,z7,z2,z4,z228,z6]),(0,[z462,z0,z7,z2,z4,z5,z6]),(1,[z122,z0,z2,z4,z5,z6]),(0,[z57,z0,z7,z2,z4,z131,z6]),(1,[z0,z7,z2,z4,z99,z5])],[(0,[z51,z0,z7,z2,z4,z37,z6]),(0,[z14,z15,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z463,z4,z5,z6]),(0,[z0,z2,z4,z5,z96,z6,z133]),(0,[z0,z7,z2,z4,z5,z6,z464])]],
   [[(0,[z465,z9,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z451,z6]),(0,[z0,z7,z466,z2,z4,z5,z6]),(0,[z0,z243,z7,z2,z4,z5,z6])],[(0,[z9,z41,z0,z2,z4,z5,z6]),(0,[z41,z0,z7,z2,z4,z5,z6]),(0,[z467,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z194,z196])],[(0,[z26,z46,z7,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z253,z5,z6]),(0,[z0,z7,z2,z4,z468,z5,z6]),(0,[z0,z7,z2,z4,z5,z469,z6]),(1,[z0,z7,z2,z4,z268,z6])],[(0,[z0,z8,z1,z2,z4,z5,z6]),(0,[z26,z7,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z470,z5,z6]),(1,[z40,z0,z7,z2,z5,z205])],[(0,[z0,z1,z2,z4,z5,z6,z39]),(0,[z26,z0,z7,z2,z453,z5,z6]),(0,[z471,z51,z0,z2,z4,z5,z6]),(0,[z57,z0,z7,z56,z4,z5,z6]),(1,[z0,z7,z460,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z472,z6]),(0,[z0,z7,z2,z4,z5,z133,z39]),(0,[z473,z0,z7,z2,z4,z5,z6])],[(0,[z0,z7,z7,z2,z4,z5,z6]),(0,[z474,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z475,z6]),(0,[z476,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z271,z6])],[(0,[z47,z0,z1,z2,z4,z5,z6]),(0,[z62,z0,z1,z2,z4,z5,z6]),(0,[z477,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z478,z4,z5,z6]),(0,[z0,z7,z2,z4,z479,z5,z6]),(0,[z0,z480,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z481,z6]),(1,[z0,z7,z2,z4,z5,z226]),(0,[z0,z7,z2,z4,z482,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z483]),(0,[z0,z7,z2,z4,z253,z5,z6])]],
   [[(0,[z484,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z485,z6])],[(0,[z40,z9,z0,z2,z4,z5,z6]),(1,[z0,z7,z2,z4,z5,z309]),(0,[z0,z7,z486,z2,z4,z5,z6]),(0,[z0,z7,z53,z2,z19,z5,z6]),(0,[z0,z7,z2,z4,z5,z487,z6]),(0,[z0,z7,z2,z4,z253,z6,z196]),(0,[z0,z7,z2,z4,z488,z5,z6])],[(0,[z382,z0,z7,z2,z4,z5,z6]),(0,[z13,z9,z0,z2,z4,z5,z6]),(0,[z165,z0,z7,z2,z36,z5,z6]),(0,[z0,z7,z2,z4,z37,z54,z6]),(0,[z0,z7,z2,z4,z5,z489,z6]),(0,[z0,z7,z2,z4,z5,z490,z6])],[(0,[z0,z7,z2,z4,z491,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z492]),(0,[z0,z1,z2,z19,z4,z5,z6]),(0,[z0,z7,z2,z4,z493,z5,z6]),(0,[z0,z7,z2,z4,z5,z37,z6]),(0,[z0,z7,z2,z4,z494,z5,z6]),(0,[z0,z7,z495,z2,z4,z5,z6])],[(0,[z0,z7,z2,z4,z5,z496,z6]),(0,[z0,z7,z2,z4,z5,z497,z6]),(0,[z33,z0,z7,z2,z4,z5,z38]),(0,[z0,z7,z2,z4,z5,z6,z498]),(0,[z499,z0,z7,z2,z4,z5,z6])],[(0,[z101,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z500,z5,z6]),(0,[z0,z7,z2,z4,z5,z246,z6]),(0,[z0,z7,z2,z4,z501,z5,z6]),(0,[z0,z7,z2,z4,z5,z502,z6]),(0,[z0,z7,z2,z4,z5,z6,z133]),(0,[z0,z7,z2,z4,z5,z6,z68]),(0,[z0,z7,z2,z4,z5,z503,z6]),(0,[z0,z7,z2,z162,z4,z5,z205])],[(1,[z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z504]),(0,[z0,z7,z2,z4,z94,z5,z6]),(0,[z0,z7,z2,z149,z4,z253,z5])]],
   [[(0,[z57,z0,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z182,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z505]),(0,[z0,z7,z2,z4,z5,z38,z196]),(1,[z79,z0,z123,z4,z5,z6]),(0,[z180,z0,z7,z2,z125,z5,z6]),(0,[z0,z7,z2,z4,z5,z506,z6]),(0,[z0,z7,z174,z2,z4,z5,z6])],[(0,[z59,z0,z7,z182,z4,z5,z6]),(1,[z299,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z507,z4,z5,z6]),(0,[z508,z0,z7,z2,z4,z5,z6]),(0,[z509,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z100,z5,z6])],[(0,[z0,z7,z2,z4,z510,z5,z6]),(0,[z0,z7,z2,z4,z5,z511,z6]),(0,[z0,z1,z512,z2,z4,z5,z6]),(0,[z0,z7,z2,z513,z4,z5,z6]),(0,[z117,z0,z7,z4,z5,z54,z6]),(0,[z0,z7,z2,z4,z514,z5,z6])],[(0,[z46,z62,z7,z2,z4,z5,z6]),(0,[z9,z0,z2,z162,z4,z5,z6]),(0,[z165,z62,z7,z2,z4,z5,z6]),(0,[z515,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z136,z88,z5,z6]),(0,[z0,z72,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z516,z5,z6]),(0,[z57,z0,z7,z2,z19,z5,z6]),(0,[z40,z0,z7,z2,z5,z6,z205]),(0,[z0,z7,z2,z149,z4,z253,z6])],[(0,[z517,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z518,z5,z6])],[(0,[z0,z7,z2,z4,z519,z5,z6]),(0,[z51,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z73,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z520,z5,z6]),(0,[z521,z0,z7,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z16,z5,z6]),(0,[z406,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z522,z2,z4,z5,z6]),(0,[z0,z7,z523,z2,z4,z5,z6]),(1,[z0,z7,z90,z4,z5,z6])],[(0,[z26,z0,z7,z2,z4,z52,z6]),(0,[z0,z7,z2,z4,z94,z52,z6]),(0,[z524,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z525,z2,z4,z5,z6])]],
   [[(0,[z9,z0,z0,z2,z4,z5,z6]),(0,[z0,z7,z23,z53,z4,z5,z6]),(0,[z0,z7,z2,z162,z4,z5,z6])],[(0,[z62,z0,z7,z2,z136,z5,z6]),(0,[z34,z0,z7,z2,z4,z5,z38]),(0,[z0,z7,z2,z131,z5,z58,z6]),(0,[z0,z7,z2,z526,z4,z5,z6])],[(0,[z40,z0,z7,z2,z4,z5,z78])],[(0,[z0,z7,z2,z4,z527,z5,z6]),(0,[z0,z7,z2,z4,z5,z528,z6]),(0,[z529,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z530,z5,z6])],[(1,[z134,z0,z2,z4,z5,z96]),(1,[z0,z7,z53,z19,z5,z6])],[(0,[z46,z0,z7,z2,z4,z5,z6]),(0,[z9,z0,z2,z123,z4,z5,z6]),(1,[z0,z7,z2,z4,z5,z118]),(0,[z165,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z531,z4,z5,z6]),(0,[z0,z7,z2,z532,z4,z5,z6]),(0,[z0,z7,z82,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z100,z5,z196]),(0,[z0,z7,z2,z4,z533,z5,z6])],[(1,[z1,z2,z4,z5,z6,z38]),(0,[z0,z1,z2,z4,z5,z78,z6]),(0,[z0,z7,z2,z534,z4,z5,z6]),(0,[z134,z0,z7,z2,z4,z5,z96]),(0,[z0,z7,z2,z4,z535,z5,z6])],[(0,[z536,z0,z7,z2,z4,z5,z6]),(0,[z537,z0,z7,z2,z4,z5,z6]),(0,[z134,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z538,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z539])]],
   [[(0,[z9,z0,z2,z4,z5,z6,z38]),(0,[z59,z0,z7,z2,z49,z5,z6]),(0,[z69,z0,z7,z4,z5,z6,z39]),(0,[z0,z7,z2,z4,z5,z6,z540])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z438,z0,z7,z2,z4,z5,z6]),(0,[z541,z0,z7,z2,z4,z5,z6]),(0,[z62,z51,z7,z2,z4,z5,z6]),(0,[z0,z7,z174,z4,z88,z5,z6]),(0,[z0,z542,z7,z2,z4,z5,z6])],[(0,[z543,z0,z7,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z5,z6,z544]),(0,[z9,z0,z2,z4,z131,z5,z6]),(0,[z471,z0,z7,z2,z4,z5,z6]),(1,[z34,z7,z2,z4,z5,z38]),(0,[z7,z2,z4,z5,z78,z6,z38]),(0,[z0,z7,z2,z4,z5,z6,z545]),(0,[z0,z7,z2,z123,z4,z5,z6])],[(0,[z9,z0,z546,z2,z4,z5,z6]),(0,[z40,z0,z7,z2,z36,z5,z6]),(0,[z0,z7,z292,z2,z4,z5,z6])],[(0,[z26,z0,z7,z2,z4,z37,z6]),(0,[z547,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z548,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z96,z6]),(0,[z0,z7,z2,z4,z549,z5,z6])],[(0,[z62,z7,z2,z4,z5,z37,z6]),(1,[z26,z7,z2,z4,z37,z6]),(0,[z0,z7,z2,z4,z550,z5,z6]),(0,[z0,z7,z2,z4,z551,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z552]),(0,[z0,z7,z2,z4,z5,z6,z553]),(0,[z0,z14,z7,z2,z4,z93,z6]),(1,[z0,z7,z2,z4,z5,z270]),(0,[z0,z7,z2,z4,z554,z5,z6]),(0,[z0,z7,z2,z555,z4,z5,z6])],[(0,[z9,z51,z0,z2,z4,z5,z6]),(0,[z556,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z557]),(1,[z0,z82,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z558,z5,z6])],[(0,[z0,z7,z2,z4,z5,z6,z544]),(0,[z0,z7,z559,z2,z4,z5,z6]),(0,[z560,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z561,z4,z5,z6]),(0,[z0,z7,z2,z4,z131,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z562])]],
   [[(0,[z0,z7,z2,z4,z375,z5,z6]),(0,[z0,z7,z546,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z563,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z564])],[(0,[z0,z1,z23,z2,z4,z5,z6]),(0,[z79,z0,z1,z2,z4,z5,z6]),(0,[z41,z0,z50,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z565,z5,z6]),(0,[z79,z0,z7,z73,z4,z5,z6]),(0,[z79,z0,z7,z123,z4,z5,z6]),(1,[z180,z0,z2,z125,z5,z6]),(0,[z0,z7,z23,z2,z4,z5,z39])],[(0,[z0,z7,z2,z10,z4,z5,z6]),(0,[z62,z7,z2,z136,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z566,z6]),(0,[z0,z7,z2,z4,z567,z5,z6]),(0,[z0,z7,z2,z4,z568,z5,z6])],[(0,[z0,z7,z2,z569,z4,z5,z6]),(1,[z33,z1,z2,z4,z5,z6]),(0,[z0,z7,z570,z2,z4,z5,z6]),(0,[z0,z7,z571,z2,z4,z5,z6]),(0,[z40,z0,z7,z460,z4,z5,z6]),(0,[z0,z7,z572,z2,z4,z5,z6])],[(0,[z0,z573,z7,z2,z4,z5,z6]),(1,[z0,z292,z2,z4,z5,z6]),(0,[z151,z0,z7,z2,z125,z5,z6]),(0,[z0,z7,z2,z574,z4,z5,z6]),(0,[z40,z0,z7,z2,z4,z5,z205])],[(0,[z180,z0,z1,z2,z4,z5,z6]),(0,[z465,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z575,z4,z5,z6]),(0,[z576,z0,z7,z2,z4,z5,z6]),(0,[z33,z0,z7,z2,z278,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z577])],[(0,[z578,z0,z7,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z93,z5,z6]),(0,[z0,z7,z2,z4,z5,z579,z6]),(0,[z0,z7,z2,z158,z4,z5,z6]),(0,[z199,z0,z7,z53,z4,z5,z6]),(0,[z580,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z194,z24]),(0,[z0,z7,z2,z4,z581,z5,z6])],[(0,[z0,z1,z2,z4,z88,z5,z6]),(0,[z0,z7,z114,z2,z4,z5,z6])]],
   [[(0,[z9,z95,z0,z2,z4,z5,z6]),(0,[z582,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z583,z5,z6]),(0,[z0,z7,z19,z4,z88,z5,z6]),(1,[z0,z120,z2,z4,z5,z6]),(0,[z0,z120,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z584,z6]),(0,[z585,z0,z7,z2,z4,z5,z6])],[(0,[z59,z0,z7,z2,z366,z5,z6]),(0,[z586,z0,z7,z2,z4,z5,z6]),(0,[z13,z0,z2,z4,z5,z132,z6])],[(0,[z57,z9,z0,z2,z4,z5,z6]),(0,[z62,z0,z7,z2,z4,z5,z143]),(0,[z34,z0,z223,z2,z4,z5,z6]),(0,[z0,z7,z2,z587,z4,z5,z6])],[(0,[z7,z2,z4,z52,z5,z37,z6]),(0,[z0,z7,z2,z588,z4,z5,z6]),(0,[z589,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z93,z5,z6]),(0,[z0,z7,z2,z4,z5,z590,z6])],[],[],[(1,[z576,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z591,z4,z5,z6]),(0,[z40,z0,z7,z2,z4,z5,z6])],[(1,[z0,z50,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z592,z6]),(0,[z13,z0,z7,z2,z4,z5,z6]),(1,[z13,z0,z2,z4,z132,z6])]],
   [[(0,[z9,z7,z1,z2,z4,z5,z6]),(0,[z41,z7,z1,z2,z4,z5,z6]),(0,[z0,z14,z1,z2,z4,z5,z6]),(1,[z0,z114,z2,z4,z5,z6])],[(1,[z9,z1,z2,z4,z5,z6]),(0,[z199,z0,z7,z2,z4,z5,z68])],[(0,[z576,z62,z0,z2,z4,z5,z6]),(0,[z79,z0,z7,z2,z178,z5,z6]),(0,[z0,z7,z2,z593,z4,z5,z6]),(0,[z69,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z594,z6])],[(1,[z26,z1,z2,z4,z5,z6]),(0,[z9,z0,z72,z2,z4,z5,z6]),(0,[z41,z0,z7,z60,z4,z5,z6]),(0,[z79,z0,z7,z2,z183,z5,z6])],[(0,[z0,z7,z2,z4,z5,z270,z6]),(0,[z0,z7,z2,z4,z5,z6,z595]),(0,[z0,z7,z2,z19,z5,z6,z205]),(0,[z0,z7,z2,z4,z596,z5,z6])],[(0,[z0,z7,z597,z2,z4,z5,z6]),(0,[z134,z0,z2,z4,z5,z96,z6]),(0,[z0,z7,z2,z4,z598,z5,z6])],[(0,[z9,z0,z2,z4,z5,z132,z6]),(0,[z599,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z240,z6])],[(0,[z0,z7,z2,z4,z600,z5,z6]),(0,[z0,z7,z2,z4,z253,z5,z38]),(1,[z0,z7,z2,z435,z5,z6])]],
   [[(0,[z9,z0,z2,z601,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z228,z6]),(0,[z33,z0,z7,z2,z329,z5,z6]),(0,[z602,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z603]),(0,[z0,z604,z7,z2,z4,z5,z6]),(0,[z0,z7,z174,z2,z435,z5,z6])],[(0,[z0,z7,z2,z605,z4,z5,z6]),(0,[z0,z7,z4,z88,z5,z54,z6]),(1,[z45,z7,z2,z4,z5,z6]),(0,[z606,z0,z7,z2,z4,z5,z6])],[(0,[z42,z9,z0,z2,z4,z5,z6]),(0,[z0,z607,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z178,z5,z6])],[(0,[z33,z0,z1,z2,z4,z5,z6]),(0,[z199,z0,z1,z2,z4,z5,z6]),(0,[z608,z0,z7,z2,z4,z5,z6]),(0,[z62,z0,z7,z2,z36,z5,z6]),(0,[z0,z7,z2,z136,z5,z194,z6]),(0,[z34,z7,z2,z4,z5,z6,z38]),(0,[z0,z7,z2,z4,z5,z609,z6]),(0,[z0,z7,z2,z4,z610,z5,z6]),(0,[z0,z7,z2,z4,z5,z132,z6]),(0,[z611,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z53,z19,z4,z5,z6]),(0,[z0,z7,z2,z4,z612,z5,z6]),(0,[z0,z7,z2,z4,z5,z613,z6])],[(0,[z9,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z614]),(1,[z471,z0,z2,z4,z5,z6]),(0,[z0,z115,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z615,z4,z5,z6]),(0,[z616,z0,z7,z2,z4,z5,z6]),(0,[z617,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z24,z205])],[(0,[z0,z1,z53,z2,z4,z5,z6]),(0,[z59,z9,z0,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z52,z5,z6]),(0,[z0,z7,z2,z601,z4,z5,z6]),(0,[z59,z7,z2,z182,z4,z5,z6]),(0,[z0,z7,z2,z4,z618,z5,z6]),(0,[z619,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z4,z5,z24,z6,z39])],[(0,[z0,z620,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z125,z19,z5,z6]),(0,[z199,z0,z7,z2,z19,z5,z6])],[(0,[z211,z0,z1,z2,z4,z5,z6]),(1,[z0,z7,z2,z453,z5,z6]),(0,[z0,z7,z2,z4,z5,z621,z6]),(0,[z0,z622,z7,z2,z4,z5,z6]),(0,[z0,z7,z623,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z624,z6])]],
   [[(0,[z0,z7,z2,z4,z5,z625,z6]),(0,[z51,z0,z267,z2,z4,z5,z6]),(0,[z626,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z627]),(1,[z199,z0,z7,z88,z5,z6]),(0,[z0,z7,z2,z131,z5,z194,z6]),(0,[z628,z0,z7,z2,z4,z5,z6])],[(0,[z151,z0,z1,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z5,z24,z6]),(0,[z0,z7,z2,z4,z5,z6,z629]),(0,[z0,z7,z2,z4,z5,z6,z630]),(0,[z0,z7,z2,z631,z4,z5,z6]),(0,[z632,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z633,z6]),(0,[z0,z7,z2,z4,z634,z5,z6]),(0,[z0,z635,z7,z2,z4,z5,z6])],[(0,[z9,z0,z2,z4,z5,z37,z6]),(0,[z0,z7,z174,z60,z4,z5,z6]),(0,[z636,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z52,z5,z6]),(0,[z0,z7,z2,z4,z100,z5,z24]),(0,[z637,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z162,z5,z194,z6])],[(0,[z0,z7,z2,z4,z214,z5,z6]),(0,[z0,z7,z638,z2,z4,z5,z6])],[(0,[z0,z7,z2,z4,z5,z639,z6]),(0,[z9,z0,z2,z4,z5,z6,z133]),(0,[z0,z7,z316,z2,z4,z5,z6]),(0,[z640,z0,z7,z2,z4,z5,z6]),(1,[z165,z7,z2,z36,z5,z6]),(0,[z0,z7,z2,z19,z36,z5,z6]),(0,[z26,z0,z7,z25,z4,z5,z6]),(1,[z250,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z253,z100,z5])],[(0,[z0,z1,z2,z4,z5,z6,z205]),(0,[z46,z7,z2,z4,z36,z5,z6]),(0,[z9,z0,z2,z4,z94,z5,z6]),(0,[z165,z7,z2,z4,z36,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z641]),(0,[z0,z7,z2,z4,z5,z6,z642])],[(0,[z0,z7,z2,z643,z4,z5,z6]),(0,[z9,z0,z2,z182,z4,z5,z6]),(0,[z9,z0,z174,z2,z4,z5,z6]),(1,[z59,z7,z182,z4,z5,z6]),(0,[z0,z7,z2,z70,z36,z5,z6]),(0,[z134,z95,z0,z2,z4,z5,z6]),(0,[z0,z7,z4,z88,z5,z6,z39]),(0,[z0,z7,z2,z4,z5,z24,z6])],[(0,[z34,z0,z1,z2,z4,z5,z6]),(0,[z644,z0,z7,z2,z4,z5,z6]),(0,[z9,z0,z2,z136,z4,z5,z6]),(0,[z9,z0,z2,z4,z100,z5,z6]),(0,[z0,z7,z2,z4,z5,z645,z6]),(0,[z0,z7,z2,z183,z4,z5,z6]),(0,[z0,z7,z2,z4,z646,z5,z6]),(0,[z0,z7,z2,z4,z647,z5,z6]),(0,[z0,z7,z2,z4,z648,z5,z6]),(0,[z69,z0,z7,z2,z530,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z649])]],
   [[(0,[z7,z2,z136,z4,z36,z5,z6]),(0,[z0,z7,z2,z162,z4,z5,z38]),(0,[z0,z7,z2,z4,z5,z650,z6]),(0,[z651,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z652,z2,z4,z5,z6])],[(0,[z9,z62,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z653,z6]),(0,[z654,z0,z7,z2,z4,z5,z6]),(0,[z250,z0,z7,z2,z4,z5,z6])],[(0,[z9,z134,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z366,z4,z5,z6]),(0,[z0,z7,z2,z4,z655,z5,z6]),(0,[z0,z7,z2,z4,z656,z5,z6]),(0,[z657,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z658,z6])],[(0,[z0,z7,z659,z2,z4,z5,z6]),(0,[z0,z660,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z661,z5,z6]),(0,[z0,z7,z2,z4,z662,z5,z6])],[(1,[z0,z638,z2,z4,z5,z6]),(0,[z0,z7,z2,z136,z4,z5,z6]),(0,[z0,z663,z7,z2,z4,z5,z6]),(0,[z152,z0,z7,z2,z4,z5,z6]),(0,[z664,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z665,z5,z6]),(0,[z0,z7,z2,z88,z131,z5,z6]),(0,[z0,z7,z2,z294,z4,z5,z6])],[(0,[z0,z256,z1,z2,z4,z5,z6]),(1,[z0,z316,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z666,z5,z6])],[(0,[z62,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z667,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z100,z6,z196]),(1,[z312,z0,z7,z2,z5,z6])],[(0,[z0,z7,z2,z136,z5,z58,z6]),(0,[z0,z7,z2,z4,z668,z5,z6]),(0,[z0,z7,z53,z2,z88,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z39]),(0,[z669,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z196,z205])]],
   [[(0,[z0,z7,z2,z4,z5,z472,z6]),(0,[z670,z0,z7,z2,z4,z5,z6]),(1,[z98,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z671,z6]),(0,[z0,z7,z2,z672,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z673,z6]),(0,[z0,z7,z2,z4,z5,z674,z6])],[(0,[z412,z0,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z675,z6]),(0,[z0,z7,z2,z4,z5,z676,z6]),(1,[z0,z7,z2,z4,z5,z246]),(0,[z0,z7,z2,z4,z677,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z678]),(0,[z679,z0,z7,z2,z4,z5,z6]),(0,[z0,z14,z7,z2,z4,z132,z6]),(0,[z0,z7,z23,z4,z5,z24,z6]),(1,[z0,z7,z2,z162,z5,z194])],[(0,[z9,z0,z2,z19,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z680,z6]),(0,[z0,z681,z7,z2,z4,z5,z6]),(0,[z682,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z683,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z195])],[(0,[z0,z1,z60,z2,z4,z5,z6]),(0,[z153,z9,z0,z2,z4,z5,z6]),(0,[z59,z41,z7,z2,z4,z5,z6]),(0,[z684,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z685,z4,z5,z6])],[(0,[z9,z0,z2,z70,z4,z5,z6]),(0,[z686,z0,z7,z2,z4,z5,z6]),(0,[z687,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z688]),(0,[z69,z0,z7,z23,z4,z5,z6])],[(0,[z0,z1,z2,z4,z36,z5,z6]),(0,[z419,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z149,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z96,z24]),(0,[z0,z7,z2,z149,z4,z5,z39]),(0,[z57,z40,z0,z7,z2,z5,z6]),(0,[z0,z7,z2,z162,z4,z100,z5])],[(0,[z0,z7,z2,z4,z689,z5,z6]),(0,[z0,z7,z2,z690,z4,z5,z6]),(0,[z0,z7,z2,z4,z278,z5,z6])],[(0,[z0,z7,z2,z4,z5,z6,z492]),(0,[z691,z0,z7,z2,z4,z5,z6]),(1,[z95,z0,z2,z4,z5,z133]),(0,[z0,z7,z2,z19,z4,z5,z6]),(0,[z57,z0,z7,z2,z4,z5,z6])]],
   [[(1,[z0,z223,z2,z4,z5,z6]),(0,[z0,z7,z4,z94,z5,z54,z6]),(0,[z692,z0,z7,z2,z4,z5,z6])],[(0,[z0,z7,z2,z4,z5,z78,z39]),(0,[z693,z0,z7,z2,z4,z5,z6]),(0,[z0,z7,z694,z2,z4,z5,z6]),(0,[z0,z7,z695,z2,z4,z5,z6]),(0,[z57,z0,z7,z2,z88,z5,z6]),(0,[z0,z7,z2,z70,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z696,z6])],[(0,[z9,z0,z2,z4,z5,z96,z6]),(0,[z165,z0,z638,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z697]),(0,[z698,z0,z7,z2,z4,z5,z6]),(1,[z57,z0,z7,z2,z58,z6])],[(0,[z0,z1,z2,z4,z5,z6,z196]),(0,[z0,z7,z2,z4,z5,z6,z699]),(0,[z0,z7,z2,z4,z5,z700,z6])],[(0,[z701,z0,z7,z2,z4,z5,z6]),(1,[z155,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z702,z5,z6]),(1,[z0,z7,z2,z4,z100,z196])],[(0,[z0,z7,z512,z2,z4,z5,z6]),(0,[z199,z9,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z703])],[(1,[z41,z1,z2,z4,z5,z6]),(0,[z704,z0,z7,z2,z4,z5,z6]),(0,[z165,z98,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z705,z4,z5,z6]),(0,[z0,z7,z2,z4,z706,z5,z6]),(0,[z57,z0,z7,z90,z4,z5,z6])],[(0,[z0,z7,z2,z4,z5,z6,z159]),(0,[z0,z7,z2,z4,z94,z37,z6]),(1,[z0,z7,z2,z530,z5,z6]),(0,[z0,z7,z2,z4,z5,z6,z48])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z115,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z627]),(0,[z0,z1,z90,z4,z5,z6]),(0,[z9,z0,z2,z707,z5,z6]),(0,[z0,z7,z2,z4,z5,z708]),(0,[z0,z7,z2,z4,z5,z709]),(0,[z0,z7,z4,z88,z5,z68]),(0,[z710,z7,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z630]),(0,[z0,z7,z2,z4,z711,z6]),(0,[z0,z7,z2,z4,z712,z5]),(0,[z713,z7,z2,z4,z5,z6])],[(0,[z1,z2,z4,z52,z5,z6]),(0,[z714,z1,z2,z4,z5,z6]),(0,[z620,z1,z2,z4,z5,z6]),(0,[z715,z0,z2,z4,z5,z6]),(0,[z716,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z162,z5,z700]),(0,[z0,z7,z2,z717,z5,z6])],[(0,[z1,z2,z4,z5,z485,z6]),(0,[z0,z7,z2,z718,z4,z5]),(0,[z9,z0,z56,z4,z5,z6]),(0,[z95,z115,z2,z4,z5,z6])],[(0,[z1,z2,z19,z36,z5,z6]),(0,[z347,z1,z2,z4,z5,z6]),(0,[z299,z41,z60,z4,z5,z6]),(0,[z0,z7,z2,z178,z5,z309]),(0,[z79,z130,z2,z4,z5,z6]),(0,[z0,z7,z719,z4,z5,z6]),(0,[z0,z7,z2,z526,z4,z253])],[(0,[z1,z2,z4,z5,z490,z6]),(0,[z0,z7,z158,z4,z5,z159]),(0,[z0,z7,z2,z720,z5,z6])],[(0,[z1,z2,z70,z36,z5,z6]),(0,[z619,z1,z2,z4,z5,z6]),(0,[z130,z2,z4,z5,z6,z133]),(0,[z0,z7,z174,z4,z554,z6]),(0,[z40,z0,z7,z2,z662,z5])],[(0,[z0,z1,z2,z4,z5,z118]),(0,[z1,z2,z4,z493,z5,z6]),(0,[z0,z7,z2,z4,z721,z6]),(0,[z199,z0,z7,z88,z5,z6])]],
   [[(0,[z1,z2,z4,z5,z497,z6]),(0,[z1,z2,z4,z5,z6,z498]),(0,[z0,z7,z2,z49,z228,z6]),(0,[z0,z7,z2,z178,z80,z6]),(1,[z0,z7,z88,z5,z68]),(0,[z0,z7,z4,z5,z722,z39])],[(0,[z670,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z502,z6]),(0,[z0,z7,z2,z4,z5,z723]),(0,[z0,z7,z2,z724,z5,z6]),(0,[z62,z638,z2,z4,z5,z6]),(0,[z0,z7,z192,z19,z5,z6]),(0,[z0,z7,z2,z183,z80,z6]),(0,[z0,z7,z2,z4,z725,z6]),(0,[z726,z0,z2,z4,z5,z6])],[(0,[z0,z7,z4,z727,z5,z6]),(0,[z0,z7,z2,z728,z5,z6]),(0,[z0,z7,z2,z4,z5,z729]),(0,[z0,z7,z2,z178,z5,z6]),(0,[z730,z7,z2,z4,z5,z6]),(0,[z151,z0,z2,z20,z5,z6]),(0,[z0,z7,z294,z4,z5,z194]),(1,[z0,z7,z2,z5,z731])],[(0,[z732,z0,z2,z4,z5,z6]),(0,[z1,z2,z182,z4,z5,z6]),(0,[z141,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z70,z131,z6]),(0,[z0,z7,z25,z4,z5,z6]),(0,[z165,z7,z2,z36,z5,z6]),(0,[z0,z7,z2,z183,z5,z6]),(0,[z312,z0,z7,z2,z5,z205])],[(0,[z34,z1,z2,z4,z5,z38]),(0,[z0,z7,z2,z733,z5,z6]),(0,[z9,z0,z2,z49,z5,z6]),(0,[z9,z0,z2,z329,z5,z6]),(0,[z734,z7,z2,z4,z5,z6]),(0,[z0,z73,z735,z4,z5,z6]),(0,[z0,z2,z4,z5,z96,z736])],[(0,[z1,z2,z4,z510,z5,z6]),(0,[z1,z2,z4,z514,z5,z6]),(0,[z169,z1,z2,z4,z5,z6]),(0,[z59,z7,z182,z4,z5,z6]),(0,[z0,z737,z2,z4,z5,z6]),(0,[z0,z7,z738,z4,z5,z6]),(0,[z739,z7,z2,z4,z5,z6]),(0,[z312,z0,z7,z2,z5,z226])],[(0,[z0,z198,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z150]),(0,[z740,z0,z2,z4,z5,z6]),(0,[z13,z0,z2,z4,z741,z6]),(0,[z0,z7,z2,z162,z5,z731])],[(0,[z742,z1,z2,z4,z5,z6]),(0,[z26,z1,z2,z4,z37,z6]),(0,[z51,z1,z2,z4,z52,z6]),(0,[z0,z1,z2,z4,z5,z270]),(0,[z660,z1,z2,z4,z5,z6]),(0,[z101,z0,z2,z4,z5,z96]),(0,[z0,z7,z743,z4,z5,z6]),(0,[z471,z51,z2,z4,z52,z6]),(0,[z79,z169,z123,z4,z5,z6]),(1,[z0,z735,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z519,z5,z6]),(0,[z299,z169,z2,z4,z5,z6]),(0,[z744,z7,z2,z4,z5,z6]),(0,[z0,z622,z2,z4,z93,z6]),(0,[z0,z2,z4,z745,z5,z6])],[(0,[z117,z0,z1,z4,z54,z6]),(0,[z265,z1,z2,z4,z5,z6]),(0,[z64,z7,z2,z4,z5,z38]),(0,[z301,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z746]),(0,[z599,z0,z7,z4,z5,z39]),(0,[z115,z7,z2,z178,z5,z6]),(0,[z15,z2,z4,z93,z5,z6]),(0,[z0,z747,z2,z4,z5,z6])],[(0,[z1,z2,z4,z94,z52,z6]),(0,[z0,z1,z2,z4,z5,z748]),(0,[z9,z604,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z749,z6]),(0,[z750,z0,z2,z4,z5,z6]),(0,[z751,z0,z7,z2,z5,z6]),(0,[z0,z7,z2,z5,z6,z752]),(0,[z115,z7,z2,z183,z5,z6]),(0,[z753,z0,z7,z2,z4,z5]),(0,[z754,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z755]),(0,[z0,z756,z2,z4,z5,z6])],[(0,[z0,z638,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z214,z6]),(0,[z0,z757,z2,z4,z5,z6]),(0,[z758,z7,z2,z4,z5,z6]),(0,[z0,z7,z23,z4,z5,z326]),(0,[z759,z0,z2,z4,z5,z6]),(0,[z760,z7,z2,z4,z5,z6]),(0,[z761,z7,z2,z4,z5,z6])],[(0,[z122,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z762,z6]),(0,[z0,z7,z2,z4,z763,z6]),(0,[z0,z7,z2,z4,z5,z764]),(0,[z765,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z294,z5,z205])],[(0,[z0,z766,z2,z4,z5,z6]),(0,[z0,z218,z158,z4,z5,z6]),(0,[z0,z218,z2,z4,z5,z159]),(0,[z122,z0,z2,z278,z5,z6]),(0,[z0,z2,z735,z4,z5,z6]),(1,[z0,z7,z767,z5,z6]),(0,[z312,z0,z7,z2,z5,z6]),(0,[z768,z0,z2,z4,z5,z6])],[(0,[z40,z1,z2,z4,z5,z38]),(0,[z293,z1,z2,z4,z5,z6]),(0,[z243,z2,z4,z20,z5,z6]),(0,[z0,z7,z769,z4,z5,z6]),(0,[z57,z0,z82,z2,z58,z6])],[(0,[z98,z0,z2,z4,z5,z6]),(0,[z0,z770,z2,z4,z5,z6]),(0,[z0,z7,z2,z771,z5,z6]),(0,[z275,z0,z7,z4,z5,z39])]],
   [[(0,[z1,z2,z4,z533,z5,z6]),(0,[z79,z115,z123,z4,z5,z6]),(0,[z17,z0,z2,z125,z5,z6]),(0,[z0,z7,z2,z162,z5,z194]),(0,[z0,z7,z2,z4,z662,z196]),(0,[z0,z7,z2,z772,z5,z6])],[(0,[z9,z0,z2,z4,z80,z6]),(0,[z0,z773,z2,z4,z5,z6]),(0,[z75,z7,z60,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z774]),(0,[z0,z235,z158,z4,z5,z6]),(0,[z0,z235,z2,z4,z5,z159]),(0,[z7,z2,z4,z5,z775,z6]),(0,[z0,z7,z2,z776,z5,z6]),(0,[z0,z7,z2,z4,z5,z240]),(0,[z57,z0,z7,z2,z58,z226]),(0,[z0,z777,z2,z4,z5,z6])],[(0,[z9,z152,z2,z4,z5,z6])],[(0,[z778,z0,z7,z2,z4,z5]),(0,[z9,z423,z2,z4,z5,z6]),(0,[z9,z0,z158,z4,z5,z6]),(0,[z9,z0,z2,z4,z5,z159]),(0,[z59,z7,z182,z4,z5,z118]),(0,[z0,z7,z2,z4,z779,z6]),(0,[z0,z7,z2,z780,z5,z6])],[(0,[z41,z1,z60,z4,z5,z6]),(0,[z0,z198,z2,z4,z5,z118]),(0,[z0,z781,z2,z4,z5,z6]),(0,[z0,z7,z2,z530,z5,z24]),(0,[z0,z7,z294,z162,z5,z6]),(0,[z0,z782,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z545]),(0,[z9,z0,z2,z366,z5,z6]),(0,[z0,z7,z2,z4,z5,z783]),(0,[z33,z7,z2,z4,z5,z78]),(0,[z0,z7,z2,z329,z5,z78]),(0,[z199,z0,z7,z88,z5,z270])],[(0,[z139,z7,z2,z4,z5,z6]),(0,[z0,z7,z784,z4,z5,z6]),(0,[z0,z7,z2,z785,z5,z6]),(0,[z13,z15,z2,z4,z5,z6]),(0,[z95,z0,z2,z4,z5,z133]),(0,[z0,z786,z2,z4,z5,z6]),(0,[z40,z0,z7,z2,z5,z624])],[(1,[z732,z2,z4,z5,z6]),(0,[z62,z1,z2,z36,z5,z6]),(0,[z1,z2,z4,z5,z6,z159]),(0,[z0,z223,z2,z4,z5,z6]),(0,[z0,z7,z2,z136,z112,z5]),(0,[z787,z7,z2,z4,z5,z6]),(0,[z788,z7,z2,z4,z5,z6]),(0,[z789,z0,z2,z4,z5,z6])]],
   [[(0,[z69,z0,z1,z4,z5,z39]),(0,[z9,z0,z2,z790,z5,z6]),(0,[z0,z791,z2,z4,z5,z6]),(0,[z0,z792,z2,z4,z5,z6]),(0,[z793,z7,z2,z4,z5,z6]),(0,[z0,z7,z90,z4,z5,z240]),(0,[z0,z7,z2,z162,z549,z5])],[(0,[z0,z7,z2,z4,z214,z118]),(0,[z26,z7,z25,z4,z37,z6]),(0,[z0,z7,z2,z4,z794,z6]),(0,[z795,z7,z2,z4,z5,z6]),(0,[z0,z796,z2,z4,z5,z6]),(0,[z797,z7,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z544]),(0,[z33,z1,z2,z4,z5,z38]),(0,[z1,z2,z561,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z189]),(0,[z0,z7,z2,z4,z5,z798]),(0,[z156,z7,z2,z4,z5,z78])],[(0,[z0,z7,z2,z799,z5,z6]),(0,[z155,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z800]),(0,[z0,z198,z2,z4,z5,z150]),(0,[z40,z0,z7,z2,z5,z614]),(0,[z0,z2,z4,z5,z741,z6])],[(0,[z1,z2,z28,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z801]),(0,[z0,z2,z4,z5,z6,z802])],[(0,[z0,z7,z2,z4,z228,z118]),(0,[z0,z7,z2,z4,z5,z803]),(0,[z139,z7,z90,z4,z5,z6])],[(0,[z0,z1,z804,z4,z5,z6]),(0,[z0,z805,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z806]),(0,[z0,z7,z2,z278,z5,z6]),(0,[z0,z218,z2,z222,z5,z6]),(0,[z0,z7,z2,z807,z5,z6]),(0,[z57,z45,z7,z2,z58,z6])],[(0,[z0,z1,z2,z149,z4,z253]),(0,[z299,z1,z2,z4,z5,z6]),(0,[z15,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z808]),(0,[z0,z7,z2,z4,z5,z809])]],
   [[(0,[z9,z0,z2,z213,z5,z6]),(0,[z9,z249,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z810,z6]),(0,[z0,z7,z2,z4,z214,z150]),(0,[z122,z0,z2,z329,z5,z6]),(0,[z0,z7,z56,z4,z5,z226])],[(0,[z811,z0,z2,z4,z5,z6]),(0,[z9,z370,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z812]),(0,[z0,z7,z23,z4,z5,z24])],[(0,[z0,z7,z2,z4,z813,z6]),(0,[z0,z235,z2,z222,z5,z6]),(0,[z0,z7,z2,z814,z5,z6]),(0,[z0,z7,z2,z4,z5,z815]),(0,[z0,z7,z2,z4,z5,z816]),(0,[z0,z817,z2,z4,z5,z6])],[(0,[z1,z2,z4,z66,z5,z6]),(0,[z818,z0,z1,z2,z5,z6]),(0,[z45,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z99,z5]),(1,[z0,z7,z294,z5,z205])],[(0,[z0,z2,z4,z5,z6,z819]),(0,[z9,z0,z2,z222,z5,z6]),(0,[z0,z7,z2,z4,z820,z6]),(0,[z0,z7,z2,z4,z228,z150]),(0,[z26,z7,z2,z222,z37,z6]),(0,[z250,z0,z2,z4,z5,z133]),(0,[z0,z7,z2,z4,z5,z821]),(0,[z822,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z823,z5,z6]),(0,[z0,z7,z824,z4,z5,z6])],[(0,[z9,z0,z2,z70,z131,z6]),(0,[z0,z7,z2,z707,z5,z6]),(0,[z0,z7,z2,z825,z5,z6]),(0,[z0,z7,z2,z5,z826,z6]),(0,[z0,z7,z2,z827,z4,z5])],[(0,[z1,z2,z588,z4,z5,z6]),(0,[z0,z7,z2,z4,z828,z6])],[(0,[z0,z7,z2,z4,z829,z6]),(0,[z0,z1,z2,z4,z268,z6]),(0,[z9,z0,z2,z4,z112,z5]),(0,[z9,z691,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z830]),(0,[z267,z2,z4,z52,z5,z6])]],
   [[(0,[z0,z7,z831,z4,z5,z6]),(0,[z0,z7,z832,z4,z5,z6]),(0,[z0,z7,z56,z4,z5,z6]),(0,[z260,z0,z7,z2,z5,z205]),(0,[z45,z7,z2,z70,z5,z6]),(0,[z57,z139,z7,z2,z58,z6]),(0,[z0,z82,z2,z4,z5,z240])],[(0,[z0,z1,z2,z453,z5,z6]),(0,[z0,z1,z460,z4,z5,z6]),(0,[z0,z7,z294,z136,z5,z6]),(0,[z833,z0,z2,z4,z5,z6]),(0,[z0,z7,z597,z4,z5,z24]),(0,[z0,z7,z2,z4,z834,z6]),(0,[z180,z243,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z835])],[(0,[z62,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z836]),(0,[z34,z223,z2,z4,z5,z38]),(0,[z0,z7,z2,z4,z5,z68]),(0,[z580,z0,z7,z88,z5,z6])],[(0,[z837,z0,z7,z2,z5,z6]),(0,[z0,z7,z2,z838,z5,z6]),(0,[z0,z7,z2,z839,z5,z6]),(0,[z840,z7,z2,z4,z5,z6]),(0,[z0,z7,z841,z4,z5,z6])],[(0,[z1,z2,z4,z83,z5,z6]),(0,[z1,z2,z4,z5,z6,z103]),(0,[z0,z1,z2,z4,z5,z226])],[(0,[z153,z1,z2,z4,z5,z6]),(0,[z106,z1,z2,z4,z5,z6]),(0,[z186,z34,z2,z4,z5,z38]),(0,[z0,z7,z2,z4,z80,z219]),(0,[z139,z82,z2,z4,z5,z6]),(0,[z842,z7,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z309]),(0,[z26,z9,z2,z4,z37,z6]),(0,[z843,z7,z2,z4,z5,z6]),(0,[z275,z0,z7,z2,z5,z205])],[(0,[z152,z7,z2,z4,z5,z6]),(0,[z26,z1,z25,z4,z5,z6]),(0,[z1,z2,z116,z4,z5,z6]),(0,[z95,z0,z2,z4,z5,z544]),(0,[z9,z474,z2,z4,z5,z6]),(0,[z0,z7,z2,z19,z5,z226])]],
   [[(1,[z7,z844,z4,z5,z6]),(0,[z0,z845,z2,z4,z5,z6]),(1,[z7,z2,z4,z5,z775]),(0,[z846,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z112,z131,z5])],[(0,[z0,z7,z2,z49,z5,z6]),(0,[z847,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z848]),(0,[z849,z7,z2,z4,z5,z6])],[(0,[z850,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z253,z5,z38]),(0,[z9,z0,z2,z4,z5,z143]),(0,[z452,z0,z7,z88,z5,z6]),(0,[z0,z218,z2,z4,z5,z27]),(0,[z33,z292,z2,z4,z5,z78]),(0,[z249,z122,z2,z4,z5,z6]),(0,[z0,z851,z2,z4,z5,z6]),(0,[z0,z120,z2,z4,z5,z240]),(0,[z57,z0,z7,z2,z826,z6])],[(0,[z31,z1,z2,z4,z5,z6]),(0,[z46,z7,z158,z4,z5,z6]),(0,[z9,z243,z2,z4,z5,z6]),(0,[z0,z7,z2,z852,z5,z6]),(0,[z0,z853,z2,z4,z5,z6]),(0,[z0,z7,z2,z854,z5,z6]),(0,[z855,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z856,z5,z6]),(0,[z0,z7,z2,z213,z5,z189]),(0,[z312,z0,z7,z2,z149,z5])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z211,z1,z2,z36,z5,z6]),(0,[z0,z1,z2,z857,z4,z5]),(0,[z0,z7,z2,z4,z858,z5]),(0,[z40,z0,z7,z294,z5,z205])],[(0,[z0,z7,z2,z4,z5,z859]),(0,[z171,z7,z2,z36,z5,z6]),(0,[z0,z7,z2,z4,z5,z860]),(0,[z0,z861,z2,z4,z5,z6]),(0,[z0,z2,z4,z741,z132,z6]),(0,[z0,z862,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z143]),(0,[z0,z235,z2,z4,z5,z27]),(0,[z0,z7,z2,z863,z5,z6]),(0,[z115,z7,z2,z4,z5,z219]),(0,[z0,z864,z2,z4,z5,z6]),(0,[z117,z0,z7,z4,z54,z6])],[(0,[z157,z1,z182,z4,z5,z6]),(0,[z134,z0,z2,z4,z5,z736]),(0,[z139,z120,z2,z4,z5,z6])]],
   [[(0,[z0,z850,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z865]),(0,[z26,z7,z2,z4,z37,z27])],[(0,[z9,z0,z294,z4,z5,z6]),(0,[z0,z7,z2,z183,z268,z6]),(0,[z0,z866,z2,z4,z5,z6])],[(0,[z26,z1,z2,z222,z5,z6]),(0,[z867,z0,z2,z4,z5,z6]),(0,[z7,z2,z854,z36,z5,z6]),(0,[z51,z267,z2,z4,z52,z6]),(0,[z0,z7,z2,z131,z6,z483])],[(0,[z0,z1,z2,z4,z5,z246]),(0,[z9,z0,z2,z4,z5,z868]),(0,[z0,z7,z25,z453,z5,z6]),(0,[z869,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z870,z5]),(0,[z0,z292,z2,z278,z5,z6]),(0,[z0,z7,z2,z4,z871,z6])],[(0,[z1,z2,z4,z634,z5,z6]),(0,[z9,z130,z2,z4,z5,z6]),(0,[z9,z34,z2,z4,z5,z38]),(0,[z9,z0,z2,z4,z5,z189]),(0,[z0,z7,z2,z70,z677,z6]),(0,[z265,z7,z2,z4,z5,z78]),(0,[z0,z7,z530,z5,z6,z39])],[(0,[z664,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z872]),(0,[z0,z7,z2,z5,z6,z873])],[(0,[z0,z7,z2,z874,z5,z6]),(0,[z0,z875,z2,z4,z5,z6])],[(1,[z1,z158,z4,z5,z6]),(1,[z1,z2,z4,z5,z159]),(0,[z0,z7,z2,z49,z5,z118]),(0,[z0,z876,z2,z4,z5,z6]),(0,[z59,z7,z844,z4,z5,z6]),(0,[z0,z82,z56,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z877]),(0,[z0,z7,z2,z5,z6,z731])]],
   [[(0,[z0,z7,z158,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z159]),(0,[z0,z7,z2,z183,z5,z309]),(0,[z0,z7,z23,z530,z5,z6])],[(0,[z1,z2,z643,z4,z5,z6]),(0,[z0,z1,z2,z878,z5,z6]),(0,[z0,z1,z53,z19,z5,z6]),(0,[z9,z0,z2,z149,z4,z253]),(0,[z0,z7,z2,z36,z112,z5]),(0,[z0,z879,z2,z4,z5,z6])],[(0,[z515,z1,z2,z4,z5,z6]),(0,[z880,z1,z2,z4,z5,z6]),(0,[z0,z8,z512,z4,z5,z6]),(0,[z9,z732,z2,z4,z5,z6]),(0,[z0,z7,z2,z366,z5,z6]),(0,[z0,z7,z2,z881,z5,z6]),(0,[z0,z7,z2,z4,z5,z882]),(0,[z57,z0,z7,z2,z112,z58])],[(0,[z1,z2,z162,z4,z5,z38]),(0,[z169,z7,z2,z4,z5,z219]),(0,[z45,z7,z2,z4,z5,z240]),(0,[z0,z7,z294,z5,z6,z205])],[(0,[z883,z0,z1,z4,z5,z6]),(0,[z576,z1,z2,z4,z5,z6]),(0,[z0,z7,z884,z4,z5,z6]),(0,[z885,z7,z2,z4,z5,z6]),(0,[z0,z886,z2,z4,z5,z6])],[(0,[z1,z2,z4,z655,z5,z6]),(0,[z9,z0,z2,z4,z99,z5]),(0,[z0,z7,z2,z790,z5,z6]),(0,[z9,z0,z2,z4,z5,z219]),(0,[z41,z7,z844,z4,z5,z6]),(0,[z7,z2,z453,z5,z37,z6]),(0,[z378,z7,z2,z4,z37,z6]),(0,[z312,z0,z7,z2,z5,z38]),(0,[z115,z7,z2,z4,z80,z6]),(0,[z69,z0,z7,z4,z5,z39]),(1,[z760,z2,z4,z5,z6])],[(0,[z243,z7,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z887,z6]),(0,[z0,z7,z2,z49,z5,z150]),(0,[z0,z888,z2,z4,z5,z6]),(0,[z0,z7,z889,z4,z5,z6]),(0,[z79,z0,z123,z178,z5,z6]),(0,[z180,z15,z2,z4,z5,z6]),(0,[z0,z7,z4,z5,z24,z722])],[(0,[z186,z0,z2,z4,z5,z6]),(0,[z529,z7,z2,z4,z52,z6]),(0,[z169,z7,z2,z4,z268,z6]),(0,[z79,z0,z123,z183,z5,z6]),(0,[z0,z7,z890,z4,z5,z6]),(0,[z0,z7,z433,z19,z5,z6]),(0,[z0,z7,z2,z4,z5,z891]),(0,[z0,z892,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z666,z5,z6]),(0,[z165,z638,z2,z36,z5,z6]),(0,[z0,z7,z158,z4,z52,z6]),(0,[z0,z7,z4,z767,z5,z6]),(0,[z0,z7,z53,z4,z5,z189])],[(0,[z0,z1,z2,z530,z5,z6]),(0,[z406,z0,z2,z4,z451,z6]),(0,[z42,z0,z2,z4,z5,z325]),(0,[z9,z0,z2,z4,z268,z6]),(0,[z0,z7,z60,z4,z228,z6]),(0,[z30,z7,z2,z36,z5,z6]),(0,[z7,z2,z4,z5,z775,z38]),(0,[z893,z0,z2,z4,z5,z6]),(0,[z0,z120,z56,z4,z5,z6])],[(0,[z40,z0,z1,z2,z5,z205]),(0,[z59,z7,z182,z4,z214,z6]),(0,[z0,z7,z294,z4,z5,z78]),(0,[z0,z7,z2,z4,z5,z894])],[(0,[z32,z1,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z5,z895]),(0,[z59,z316,z182,z4,z5,z6]),(0,[z0,z7,z2,z896,z5,z6]),(0,[z0,z897,z2,z4,z5,z6])],[(0,[z449,z1,z2,z4,z5,z6]),(0,[z64,z0,z2,z4,z5,z133]),(0,[z0,z7,z2,z4,z898,z5]),(0,[z0,z7,z2,z5,z6,z899])],[(0,[z0,z7,z900,z4,z5,z6]),(0,[z33,z7,z2,z4,z5,z775]),(0,[z0,z7,z2,z4,z5,z901]),(0,[z0,z7,z2,z213,z5,z6])],[(0,[z46,z9,z2,z4,z5,z6]),(0,[z26,z1,z2,z4,z5,z27]),(0,[z0,z7,z2,z4,z5,z902]),(0,[z0,z292,z2,z329,z5,z6]),(0,[z0,z82,z2,z19,z5,z6])],[(0,[z0,z7,z903,z4,z5,z6])]],
   [[(0,[z560,z1,z2,z4,z5,z6]),(0,[z0,z218,z2,z4,z5,z6]),(0,[z818,z0,z7,z2,z5,z6]),(0,[z9,z15,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z5,z309]),(0,[z0,z7,z2,z366,z5,z118]),(0,[z0,z7,z2,z4,z904,z5]),(0,[z0,z7,z2,z905,z5,z6]),(0,[z57,z0,z7,z2,z461,z6])],[(0,[z1,z2,z4,z278,z5,z6]),(0,[z239,z1,z2,z4,z5,z6]),(0,[z0,z316,z2,z4,z214,z6]),(0,[z0,z7,z2,z222,z5,z6]),(0,[z139,z7,z2,z4,z5,z226])],[(0,[z101,z0,z2,z4,z5,z63]),(0,[z0,z7,z2,z4,z228,z6]),(0,[z169,z7,z2,z4,z80,z6]),(0,[z0,z7,z2,z4,z5,z906]),(0,[z0,z7,z2,z70,z131,z6]),(0,[z312,z0,z7,z2,z100,z5])],[(0,[z211,z0,z2,z16,z5,z6]),(0,[z0,z8,z73,z4,z5,z6]),(0,[z0,z7,z294,z36,z5,z6]),(0,[z40,z0,z7,z2,z5,z103]),(0,[z151,z0,z2,z907,z5,z6]),(0,[z0,z7,z2,z4,z5,z908]),(0,[z365,z0,z7,z4,z5,z39]),(0,[z0,z909,z2,z4,z5,z6]),(0,[z910,z7,z2,z4,z5,z6]),(0,[z0,z2,z911,z4,z5,z6])],[(0,[z169,z7,z2,z4,z5,z6]),(0,[z406,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z912,z5,z6]),(0,[z0,z7,z2,z913,z5,z6]),(0,[z46,z7,z2,z278,z5,z6]),(0,[z0,z7,z2,z4,z5,z914]),(0,[z0,z7,z2,z915,z5,z6]),(0,[z0,z7,z2,z4,z112,z5])],[(0,[z1,z2,z4,z259,z5,z6]),(0,[z585,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z278,z5,z6]),(0,[z0,z2,z4,z5,z6,z916]),(0,[z0,z316,z2,z4,z228,z6]),(0,[z917,z7,z2,z4,z5,z6]),(0,[z918,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z131,z826,z6])],[(0,[z9,z0,z2,z4,z5,z6]),(0,[z26,z7,z2,z4,z355,z6]),(0,[z26,z7,z158,z4,z37,z6]),(0,[z26,z7,z2,z4,z37,z159]),(0,[z0,z7,z919,z4,z5,z6]),(0,[z0,z7,z2,z4,z920,z5]),(0,[z40,z0,z7,z2,z5,z731])],[(0,[z0,z7,z2,z366,z5,z150]),(0,[z921,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z922,z6]),(0,[z57,z0,z7,z2,z621,z6])]],
   [[(0,[z403,z1,z2,z4,z5,z6]),(0,[z235,z1,z2,z4,z5,z6]),(0,[z923,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z731])],[(0,[z1,z2,z705,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z748])],[(0,[z654,z1,z2,z4,z5,z6]),(0,[z40,z9,z0,z2,z5,z205]),(0,[z0,z7,z2,z453,z5,z27]),(0,[z7,z2,z4,z5,z828,z6]),(0,[z924,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z925,z5,z6]),(0,[z69,z0,z7,z530,z5,z39]),(0,[z45,z7,z56,z4,z5,z6])],[(0,[z378,z1,z2,z4,z5,z6]),(0,[z41,z7,z570,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z926]),(0,[z0,z7,z2,z927,z5,z6])],[(0,[z126,z0,z2,z83,z5,z6]),(0,[z760,z2,z4,z5,z6,z39]),(0,[z0,z7,z928,z4,z5,z6]),(0,[z0,z7,z294,z4,z5,z205]),(0,[z312,z0,z7,z929,z5,z6])],[(0,[z9,z0,z90,z4,z5,z6]),(0,[z62,z267,z2,z4,z5,z6]),(0,[z930,z7,z2,z4,z5,z6]),(0,[z0,z7,z767,z88,z5,z6]),(0,[z0,z7,z2,z5,z6,z195])],[(0,[z1,z2,z289,z4,z5,z6]),(1,[z1,z2,z4,z5,z143]),(0,[z0,z931,z2,z4,z5,z6]),(0,[z223,z2,z4,z5,z6,z38]),(0,[z95,z0,z2,z4,z5,z219]),(0,[z0,z7,z2,z4,z5,z932]),(0,[z933,z7,z2,z4,z5,z6])],[(0,[z0,z7,z2,z934,z5,z6]),(0,[z0,z7,z2,z4,z5,z143]),(0,[z0,z7,z2,z935,z5,z6]),(0,[z0,z7,z2,z4,z5,z271])]],
   [[(0,[z1,z2,z4,z36,z5,z6]),(0,[z714,z0,z2,z4,z5,z6]),(1,[z1,z2,z278,z5,z6]),(0,[z57,z0,z7,z2,z99,z58])],[(0,[z1,z2,z4,z5,z38,z39]),(0,[z936,z0,z1,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z937]),(0,[z354,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z938]),(0,[z200,z0,z7,z4,z54,z6]),(0,[z628,z0,z7,z4,z5,z39])],[(0,[z939,z7,z2,z4,z5,z6]),(0,[z312,z0,z7,z2,z100,z196])],[(0,[z1,z2,z4,z304,z5,z6]),(0,[z115,z2,z123,z4,z5,z6]),(0,[z199,z0,z7,z88,z5,z68])],[(0,[z130,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z435,z5,z6]),(0,[z9,z571,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z5,z118]),(0,[z0,z7,z2,z4,z940,z6]),(0,[z698,z0,z2,z4,z132,z6]),(0,[z57,z0,z7,z2,z58,z240]),(0,[z0,z7,z2,z70,z826,z6])],[(0,[z298,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z941]),(0,[z0,z7,z2,z942,z5,z6]),(0,[z0,z7,z2,z4,z5,z27]),(0,[z7,z2,z4,z828,z37,z6]),(0,[z0,z7,z2,z4,z943,z6]),(0,[z0,z7,z2,z4,z268,z219])],[(0,[z1,z2,z4,z65,z5,z6]),(0,[z576,z152,z2,z4,z5,z6]),(0,[z26,z218,z2,z4,z37,z6]),(0,[z0,z7,z294,z4,z5,z6]),(0,[z944,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z945,z5,z6])],[(0,[z249,z7,z2,z4,z5,z6]),(0,[z0,z267,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z946,z6]),(0,[z0,z7,z2,z947,z5,z6]),(0,[z948,z7,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z5,z317,z6]),(0,[z0,z949,z2,z4,z5,z6]),(0,[z950,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z868]),(0,[z499,z7,z2,z4,z5,z78]),(0,[z0,z7,z53,z22,z5,z6]),(0,[z0,z951,z2,z4,z5,z6])],[(0,[z0,z1,z2,z718,z4,z5]),(0,[z638,z2,z4,z36,z5,z6]),(0,[z0,z2,z4,z5,z6,z952]),(0,[z0,z7,z953,z4,z5,z6]),(0,[z45,z7,z2,z19,z5,z6]),(0,[z0,z7,z2,z4,z5,z722]),(0,[z0,z7,z2,z4,z5,z954])],[(0,[z0,z7,z2,z4,z955,z6]),(0,[z26,z235,z2,z4,z37,z6])],[(0,[z251,z1,z2,z4,z5,z6]),(0,[z1,z2,z36,z88,z5,z6]),(0,[z9,z0,z2,z4,z5,z150]),(0,[z0,z7,z2,z4,z5,z956]),(0,[z957,z0,z2,z4,z5,z6])],[(0,[z26,z1,z158,z4,z5,z6]),(0,[z26,z1,z2,z4,z5,z159]),(0,[z9,z0,z2,z4,z5,z270]),(0,[z0,z958,z2,z4,z5,z6]),(0,[z959,z0,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z328]),(0,[z9,z0,z2,z4,z960,z6]),(0,[z0,z2,z4,z5,z6,z961]),(0,[z962,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z741,z6])],[(0,[z0,z7,z2,z4,z5,z963]),(0,[z0,z7,z2,z149,z4,z253])],[(0,[z1,z2,z4,z104,z5,z6]),(0,[z547,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z5,z964,z6]),(0,[z0,z7,z2,z4,z965,z6]),(0,[z0,z2,z907,z20,z5,z6])]],
   [[(0,[z0,z1,z4,z727,z5,z6]),(0,[z1,z2,z109,z4,z5,z6]),(0,[z9,z33,z2,z4,z5,z78]),(0,[z0,z966,z2,z4,z5,z6]),(0,[z199,z0,z7,z767,z5,z6]),(0,[z967,z7,z2,z4,z5,z6])],[(0,[z0,z968,z2,z4,z5,z6]),(0,[z165,z1,z2,z36,z5,z6]),(0,[z883,z0,z7,z4,z5,z6]),(0,[z0,z7,z2,z4,z969,z6]),(0,[z0,z7,z2,z970,z5,z6])],[(0,[z122,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z733,z5,z6]),(0,[z0,z7,z2,z4,z5,z219]),(0,[z971,z7,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z972]),(0,[z0,z7,z2,z4,z99,z5])],[(0,[z59,z1,z182,z4,z5,z6]),(0,[z0,z7,z2,z4,z887,z6]),(0,[z79,z0,z123,z4,z5,z219]),(0,[z628,z0,z7,z88,z5,z6]),(0,[z0,z7,z294,z149,z4,z5])],[(0,[z62,z1,z2,z4,z5,z246]),(0,[z0,z7,z2,z4,z5,z973]),(0,[z0,z7,z2,z329,z5,z6]),(0,[z484,z0,z2,z4,z132,z6]),(0,[z45,z7,z2,z88,z5,z6])],[(0,[z0,z974,z2,z4,z5,z6]),(0,[z975,z7,z2,z4,z5,z6]),(0,[z509,z0,z2,z4,z5,z96])],[(0,[z46,z7,z2,z4,z5,z159]),(0,[z0,z976,z2,z4,z5,z6]),(0,[z7,z2,z4,z854,z5,z6]),(0,[z0,z7,z2,z4,z268,z6])],[(0,[z64,z1,z2,z4,z5,z38]),(0,[z7,z1,z158,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z159]),(0,[z0,z316,z2,z49,z5,z6]),(0,[z0,z7,z2,z4,z977,z6]),(0,[z134,z130,z2,z4,z5,z6]),(0,[z0,z7,z335,z88,z5,z6]),(0,[z40,z0,z7,z2,z5,z205])]],
   [[(0,[z0,z7,z4,z5,z978,z6]),(0,[z0,z7,z2,z4,z5,z895]),(0,[z180,z0,z2,z10,z5,z6]),(0,[z0,z7,z158,z453,z5,z6]),(0,[z0,z7,z2,z453,z5,z159]),(0,[z7,z2,z4,z5,z979,z6]),(0,[z0,z980,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z981])],[(0,[z0,z1,z2,z4,z214,z6]),(0,[z41,z1,z182,z4,z5,z6]),(0,[z1,z2,z4,z5,z24,z38]),(0,[z611,z7,z2,z36,z5,z6]),(0,[z0,z982,z2,z4,z5,z6]),(0,[z0,z7,z983,z4,z5,z6])],[(0,[z0,z7,z2,z4,z5,z984]),(0,[z34,z7,z2,z4,z5,z775]),(0,[z0,z7,z4,z88,z5,z189]),(0,[z0,z7,z2,z149,z4,z985])],[(0,[z1,z2,z154,z4,z5,z6]),(0,[z0,z7,z2,z4,z80,z309])],[(0,[z33,z7,z2,z4,z5,z639])],[(0,[z42,z1,z2,z4,z5,z6]),(0,[z33,z1,z2,z278,z5,z6]),(0,[z0,z7,z2,z4,z5,z986]),(0,[z167,z9,z2,z4,z5,z6]),(0,[z0,z7,z2,z987,z5,z6]),(0,[z0,z7,z2,z4,z988,z5]),(0,[z115,z7,z2,z4,z268,z6]),(0,[z0,z7,z2,z88,z5,z226]),(0,[z117,z0,z7,z4,z989,z6])],[(0,[z0,z1,z2,z162,z5,z194]),(0,[z129,z1,z2,z4,z5,z6]),(0,[z419,z0,z2,z4,z132,z6]),(0,[z0,z990,z2,z4,z5,z6]),(0,[z69,z0,z7,z4,z5,z722])],[(0,[z0,z1,z2,z4,z5,z240]),(0,[z0,z991,z2,z4,z5,z6]),(0,[z296,z0,z7,z88,z5,z6]),(0,[z992,z0,z2,z4,z5,z6]),(1,[z0,z7,z2,z4,z985])]],
   [[(0,[z0,z239,z7,z4,z54,z6])],[(0,[z1,z2,z177,z4,z5,z6]),(0,[z316,z2,z182,z4,z5,z6]),(0,[z0,z993,z2,z4,z5,z6]),(0,[z115,z72,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z80,z6]),(0,[z57,z0,z7,z294,z5,z6])],[(0,[z994,z0,z2,z4,z5,z6]),(0,[z0,z995,z2,z4,z5,z6]),(0,[z996,z7,z2,z4,z5,z6]),(0,[z79,z0,z123,z4,z80,z6]),(0,[z0,z7,z2,z4,z997,z6]),(0,[z0,z7,z2,z4,z5,z998])],[(0,[z0,z7,z2,z4,z5,z6]),(0,[z33,z1,z2,z4,z5,z78]),(0,[z51,z7,z2,z4,z104,z6])],[(0,[z0,z7,z2,z999,z5,z6]),(0,[z1,z2,z4,z5,z6,z190]),(0,[z0,z7,z2,z1000,z5,z6]),(0,[z46,z122,z2,z4,z5,z6]),(0,[z1001,z0,z2,z4,z5,z6]),(0,[z115,z7,z2,z4,z5,z309]),(0,[z1002,z0,z2,z4,z5,z6]),(0,[z0,z1003,z2,z4,z5,z6]),(0,[z0,z1004,z2,z4,z5,z6])],[(0,[z299,z0,z2,z4,z5,z6]),(0,[z0,z7,z1005,z4,z5,z6]),(0,[z1,z2,z4,z197,z5,z6]),(0,[z0,z1006,z2,z4,z5,z6])],[(0,[z357,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1007]),(0,[z9,z0,z2,z435,z5,z6]),(0,[z576,z0,z2,z4,z5,z143]),(0,[z51,z7,z2,z453,z5,z6]),(0,[z79,z0,z548,z4,z5,z6]),(0,[z0,z7,z2,z4,z1008,z5]),(0,[z1009,z0,z2,z4,z5,z6])],[(0,[z47,z1,z2,z4,z5,z6]),(1,[z0,z2,z907,z5,z6]),(0,[z0,z2,z4,z5,z6,z1010]),(0,[z0,z7,z929,z4,z5,z6]),(0,[z0,z1011,z2,z4,z5,z6])]],
   [[(0,[z75,z1,z2,z4,z5,z6]),(0,[z0,z316,z2,z366,z5,z6]),(0,[z59,z198,z182,z4,z5,z6]),(0,[z128,z0,z7,z4,z54,z6]),(0,[z0,z114,z2,z4,z5,z143]),(0,[z0,z218,z2,z453,z5,z6]),(0,[z1012,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z530,z5,z39])],[(0,[z0,z1,z2,z4,z5,z800]),(0,[z0,z1,z2,z4,z100,z196]),(0,[z155,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1013]),(0,[z0,z7,z2,z4,z5,z1014]),(0,[z0,z2,z4,z5,z1015,z6]),(0,[z0,z7,z2,z1016,z5,z6]),(0,[z0,z7,z2,z4,z253,z985])],[(0,[z115,z7,z2,z4,z5,z6]),(0,[z46,z235,z2,z4,z5,z6]),(0,[z1017,z7,z2,z4,z5,z6]),(0,[z0,z7,z559,z4,z5,z24]),(0,[z0,z7,z90,z4,z5,z6]),(0,[z1018,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z5,z194,z731])],[(0,[z1019,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z1020,z5]),(0,[z0,z7,z1021,z4,z5,z6])],[(0,[z1,z2,z4,z220,z5,z6]),(0,[z0,z7,z2,z4,z5,z1022]),(0,[z378,z7,z182,z4,z5,z6]),(0,[z0,z235,z2,z453,z5,z6]),(0,[z0,z1023,z2,z4,z5,z6]),(0,[z1024,z7,z2,z4,z5,z6])],[(0,[z0,z7,z2,z4,z5,z1025]),(0,[z15,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z1026,z6]),(0,[z0,z7,z2,z1027,z5,z6]),(0,[z0,z7,z2,z4,z985,z100])],[(0,[z0,z7,z2,z4,z5,z1028]),(0,[z936,z0,z7,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1029]),(0,[z9,z0,z2,z453,z5,z6]),(0,[z9,z0,z460,z4,z5,z6]),(0,[z0,z198,z2,z4,z214,z6]),(0,[z0,z1030,z2,z4,z5,z6]),(0,[z0,z7,z1031,z4,z5,z6]),(1,[z0,z2,z4,z5,z736]),(0,[z0,z7,z2,z149,z4,z594])],[(0,[z0,z1,z23,z4,z5,z24]),(0,[z0,z7,z2,z1032,z5,z6]),(0,[z0,z1033,z2,z4,z5,z6]),(0,[z0,z7,z2,z435,z5,z271])]],
   [[(0,[z33,z880,z2,z4,z5,z6]),(0,[z33,z1,z2,z329,z5,z6]),(0,[z0,z1,z2,z4,z813,z6]),(0,[z7,z2,z844,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1034]),(0,[z0,z7,z2,z136,z5,z246]),(0,[z1035,z7,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z96,z219]),(0,[z0,z7,z2,z1036,z5,z6]),(0,[z134,z0,z2,z4,z5,z96]),(0,[z0,z7,z88,z5,z6,z68]),(0,[z45,z931,z2,z4,z5,z6]),(0,[z57,z0,z7,z90,z58,z6]),(0,[z1037,z0,z2,z4,z5,z6])],[(0,[z419,z1,z2,z4,z52,z6]),(0,[z9,z0,z2,z4,z5,z226]),(0,[z0,z7,z2,z4,z5,z118]),(0,[z59,z7,z182,z4,z228,z6]),(0,[z169,z7,z2,z4,z5,z309]),(0,[z1038,z0,z7,z2,z5,z6])],[(0,[z46,z576,z2,z4,z5,z6]),(0,[z0,z198,z2,z4,z228,z6]),(0,[z0,z7,z2,z1039,z5,z6]),(0,[z1040,z7,z2,z4,z5,z6]),(0,[z0,z735,z123,z4,z5,z6]),(0,[z0,z2,z4,z5,z736,z6]),(0,[z0,z7,z53,z767,z5,z6]),(0,[z0,z1041,z2,z4,z5,z6]),(0,[z1042,z0,z2,z4,z5,z6])],[],[(0,[z714,z62,z2,z4,z5,z6]),(0,[z412,z0,z2,z125,z5,z6]),(0,[z1043,z0,z2,z4,z5,z6])],[(0,[z732,z47,z2,z4,z5,z6]),(0,[z46,z7,z2,z4,z5,z143]),(0,[z0,z7,z2,z4,z5,z1044]),(0,[z1045,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1046]),(0,[z0,z7,z2,z4,z1047,z5]),(0,[z57,z0,z7,z2,z112,z5])],[(0,[z1,z182,z4,z5,z54,z6]),(0,[z0,z1,z56,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z143]),(0,[z541,z7,z2,z36,z5,z6]),(0,[z34,z7,z2,z4,z5,z38])],[(0,[z0,z235,z2,z4,z5,z6]),(0,[z657,z1,z2,z4,z5,z6]),(0,[z1048,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z1049,z5,z6]),(0,[z0,z7,z2,z4,z5,z1050]),(0,[z0,z7,z2,z149,z4,z142])]],
   [[(0,[z0,z1,z2,z4,z5,z68]),(0,[z0,z7,z2,z4,z5,z150]),(0,[z0,z7,z2,z1051,z5,z6]),(0,[z0,z7,z158,z4,z37,z6]),(0,[z1052,z7,z2,z4,z5,z6]),(0,[z1053,z7,z2,z4,z5,z6]),(0,[z0,z7,z1054,z4,z5,z6])],[(0,[z26,z7,z2,z4,z37,z6]),(0,[z51,z7,z2,z4,z52,z6]),(0,[z0,z72,z735,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z270]),(0,[z0,z7,z56,z19,z5,z6]),(0,[z0,z1055,z2,z4,z5,z6]),(0,[z0,z1056,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z985,z5])],[(0,[z59,z9,z182,z4,z5,z6]),(0,[z0,z7,z2,z4,z960,z6]),(0,[z0,z7,z2,z1057,z5,z6]),(0,[z1058,z7,z2,z4,z5,z6]),(0,[z0,z82,z2,z4,z5,z6]),(0,[z1059,z0,z2,z4,z5,z6])],[(0,[z1,z2,z36,z5,z194,z6]),(0,[z0,z1060,z2,z4,z5,z6]),(0,[z130,z73,z2,z4,z5,z6]),(0,[z0,z7,z2,z19,z5,z68])],[(0,[z0,z1061,z2,z4,z5,z6]),(0,[z0,z7,z1062,z4,z5,z6]),(0,[z0,z2,z4,z907,z5,z6]),(0,[z0,z82,z2,z88,z5,z6]),(0,[z0,z7,z2,z4,z1063,z6])],[(0,[z732,z1,z2,z4,z5,z6]),(0,[z64,z0,z2,z4,z5,z492]),(0,[z399,z7,z2,z4,z5,z38]),(0,[z180,z0,z2,z125,z5,z6]),(0,[z0,z7,z2,z1064,z5,z6]),(0,[z0,z7,z2,z4,z985,z6])],[(0,[z9,z45,z2,z4,z5,z6]),(0,[z0,z1065,z2,z4,z5,z6]),(0,[z113,z0,z7,z2,z58,z6]),(0,[z0,z7,z294,z4,z5,z38]),(0,[z0,z7,z2,z1066,z5,z6]),(0,[z0,z7,z2,z124,z5,z194])],[(0,[z0,z1,z2,z97,z5,z6]),(0,[z199,z9,z0,z88,z5,z6]),(0,[z0,z7,z844,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z775]),(0,[z0,z7,z2,z4,z1067,z6]),(1,[z0,z7,z530,z5,z39]),(0,[z0,z1068,z2,z4,z5,z6])]],
   [[(0,[z0,z292,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z5,z246]),(0,[z0,z14,z2,z4,z447,z6]),(0,[z840,z250,z2,z4,z5,z6])],[(0,[z26,z7,z2,z4,z828,z6]),(0,[z0,z82,z90,z4,z5,z6])],[(0,[z1,z174,z182,z4,z5,z6]),(0,[z0,z1,z2,z4,z858,z5]),(0,[z0,z7,z2,z1069,z5,z6]),(0,[z1070,z0,z2,z4,z5,z6]),(0,[z0,z7,z25,z4,z5,z27]),(0,[z0,z7,z735,z4,z5,z6]),(0,[z0,z2,z4,z5,z96,z282]),(0,[z0,z7,z4,z5,z6,z722])],[(0,[z0,z7,z2,z1071,z5,z6]),(0,[z0,z7,z2,z1072,z5,z6]),(0,[z256,z1,z2,z4,z52,z6]),(0,[z0,z7,z2,z4,z5,z1073]),(0,[z0,z1074,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z655,z196]),(0,[z0,z7,z2,z4,z5,z1075]),(0,[z0,z7,z4,z989,z54,z6])],[(0,[z425,z1,z2,z4,z5,z6]),(0,[z0,z120,z2,z4,z5,z6]),(0,[z15,z2,z4,z20,z5,z6]),(0,[z1076,z7,z2,z4,z5,z6]),(0,[z0,z1077,z2,z4,z5,z6]),(0,[z139,z7,z2,z4,z5,z240])],[(0,[z9,z51,z2,z4,z52,z6]),(0,[z0,z7,z2,z1078,z5,z6]),(0,[z0,z7,z2,z1079,z5,z6]),(0,[z0,z7,z2,z389,z5,z194])],[(0,[z9,z0,z53,z19,z5,z6]),(0,[z41,z7,z60,z4,z5,z6]),(0,[z0,z1080,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1081]),(0,[z180,z0,z2,z463,z5,z6]),(0,[z0,z7,z2,z4,z5,z1082]),(0,[z0,z7,z2,z4,z5,z1083]),(0,[z0,z1084,z2,z4,z5,z6]),(0,[z1085,z7,z2,z4,z5,z6])],[]],
   [[(0,[z880,z0,z2,z4,z5,z6]),(0,[z9,z139,z2,z4,z5,z6]),(0,[z0,z1086,z2,z4,z5,z6]),(0,[z115,z2,z4,z5,z96,z6]),(0,[z180,z0,z2,z907,z5,z6]),(0,[z1087,z0,z2,z4,z5,z6])],[(0,[z0,z7,z2,z162,z5,z545]),(0,[z312,z0,z7,z2,z5,z194]),(0,[z0,z7,z2,z4,z985,z196])],[(0,[z576,z0,z2,z4,z5,z6]),(0,[z376,z1,z2,z4,z5,z6]),(0,[z0,z1088,z2,z4,z5,z6]),(0,[z923,z139,z2,z4,z5,z6])],[(0,[z1,z2,z4,z453,z5,z6]),(0,[z9,z0,z2,z4,z100,z196]),(0,[z13,z0,z2,z4,z451,z6]),(0,[z0,z7,z2,z493,z5,z194]),(0,[z0,z120,z90,z4,z5,z6]),(0,[z0,z7,z294,z4,z100,z5])],[(0,[z0,z114,z2,z4,z5,z6]),(0,[z0,z7,z2,z329,z5,z38]),(0,[z701,z0,z7,z4,z54,z6]),(0,[z0,z7,z2,z4,z5,z189]),(0,[z0,z7,z336,z4,z5,z39]),(0,[z57,z0,z120,z2,z58,z6]),(0,[z0,z7,z2,z5,z731,z205])],[(0,[z312,z9,z0,z2,z5,z6]),(0,[z0,z1089,z2,z4,z5,z6]),(0,[z0,z7,z2,z1090,z5,z6])],[(0,[z0,z1,z158,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z159]),(0,[z9,z0,z2,z530,z5,z6]),(0,[z0,z1091,z2,z4,z5,z6]),(0,[z1092,z0,z2,z4,z5,z6]),(0,[z0,z2,z125,z907,z5,z6])],[(0,[z26,z1,z2,z4,z5,z6]),(0,[z1,z2,z36,z5,z58,z6]),(0,[z157,z0,z123,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1093]),(0,[z250,z0,z2,z4,z5,z219]),(0,[z0,z7,z56,z213,z5,z6]),(0,[z69,z0,z4,z5,z48,z39])]],
   [[(0,[z0,z1,z2,z366,z5,z6]),(0,[z742,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z721,z6]),(0,[z0,z7,z804,z4,z5,z6]),(0,[z151,z0,z2,z83,z5,z6]),(0,[z155,z9,z2,z4,z5,z6]),(0,[z33,z7,z2,z278,z5,z78]),(0,[z616,z0,z7,z88,z5,z6]),(0,[z69,z0,z7,z97,z5,z39])],[],[(0,[z1,z2,z4,z468,z5,z6]),(0,[z41,z316,z2,z4,z5,z6]),(0,[z0,z1094,z2,z4,z5,z6]),(0,[z40,z0,z7,z2,z315,z5])],[(0,[z26,z850,z2,z4,z5,z6]),(0,[z0,z1,z2,z178,z5,z6]),(0,[z59,z7,z182,z49,z5,z6]),(0,[z0,z7,z2,z4,z268,z309]),(0,[z153,z243,z2,z4,z5,z6])],[(0,[z1,z2,z4,z339,z5,z6]),(0,[z582,z1,z2,z4,z5,z6]),(0,[z243,z1,z2,z4,z5,z6]),(0,[z0,z1,z25,z4,z5,z6]),(0,[z157,z0,z191,z4,z5,z6]),(0,[z0,z1,z2,z183,z5,z6]),(0,[z0,z198,z2,z49,z5,z6]),(0,[z7,z2,z36,z5,z87,z6]),(0,[z406,z15,z2,z4,z5,z6]),(0,[z0,z760,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z100,z649]),(0,[z1095,z0,z2,z4,z5,z6])],[(0,[z465,z0,z546,z4,z5,z6]),(0,[z0,z7,z2,z4,z1096,z6]),(0,[z0,z7,z2,z1097,z5,z6]),(0,[z45,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1098])],[(0,[z0,z7,z56,z4,z5,z240]),(0,[z1099,z0,z2,z4,z5,z6])],[(0,[z26,z1,z2,z4,z52,z6]),(1,[z7,z2,z4,z828,z6]),(0,[z0,z7,z2,z1100,z5,z6])]],
   [[(0,[z471,z0,z2,z4,z5,z6]),(0,[z211,z0,z2,z20,z5,z6]),(0,[z45,z7,z2,z5,z58,z6])],[(0,[z1,z2,z4,z5,z487,z6]),(0,[z0,z7,z2,z1101,z5,z6]),(0,[z57,z9,z0,z2,z58,z6]),(0,[z0,z7,z2,z49,z214,z6]),(0,[z95,z130,z2,z4,z5,z133]),(0,[z0,z7,z2,z4,z5,z1102])],[(1,[z1,z2,z453,z5,z6]),(0,[z9,z0,z2,z4,z5,z68]),(0,[z0,z7,z2,z4,z5,z1103]),(0,[z0,z7,z2,z36,z5,z246]),(0,[z79,z0,z123,z4,z268,z6]),(0,[z0,z7,z2,z4,z5,z1104]),(0,[z0,z7,z2,z4,z100,z461])],[(0,[z480,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z213,z5,z6]),(0,[z382,z0,z601,z4,z5,z6]),(0,[z0,z7,z2,z453,z5,z6]),(0,[z0,z7,z460,z4,z5,z6]),(0,[z139,z7,z56,z4,z5,z6])],[(0,[z0,z7,z1105,z4,z5,z6]),(0,[z46,z732,z2,z4,z5,z6]),(0,[z0,z7,z1106,z4,z5,z6]),(0,[z1107,z0,z2,z4,z5,z6]),(0,[z45,z7,z90,z4,z5,z6]),(0,[z40,z0,z7,z2,z5,z226]),(0,[z40,z0,z7,z2,z5,z400])],[(0,[z0,z7,z2,z1108,z5,z6]),(0,[z193,z1,z2,z4,z5,z6]),(0,[z684,z0,z7,z4,z54,z6]),(0,[z0,z1109,z2,z4,z5,z6]),(0,[z1110,z0,z2,z4,z5,z6])],[(0,[z1,z2,z4,z500,z5,z6]),(0,[z1111,z0,z2,z4,z5,z6]),(0,[z524,z1,z2,z4,z5,z6]),(0,[z0,z7,z1112,z4,z5,z6]),(0,[z1113,z7,z2,z4,z5,z6]),(0,[z151,z152,z2,z20,z5,z6]),(0,[z1114,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z226]),(0,[z0,z7,z2,z1115,z5,z6])],[(0,[z0,z1,z2,z222,z5,z6]),(0,[z153,z0,z2,z10,z5,z6]),(0,[z165,z98,z2,z36,z5,z6]),(0,[z1116,z0,z7,z2,z5,z6]),(0,[z250,z0,z2,z4,z5,z96]),(0,[z1117,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1118]),(0,[z0,z1119,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z228,z6]),(0,[z1,z2,z4,z5,z6,z505]),(0,[z1,z2,z4,z5,z38,z196]),(0,[z1,z2,z4,z5,z506,z6]),(0,[z0,z7,z2,z4,z1120,z6]),(0,[z0,z7,z25,z4,z5,z159]),(0,[z0,z7,z2,z4,z5,z309]),(0,[z250,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1121]),(0,[z0,z7,z2,z5,z6,z1122]),(0,[z57,z0,z7,z56,z58,z6]),(0,[z0,z1123,z2,z4,z5,z6])],[(0,[z1124,z0,z2,z4,z5,z6]),(0,[z9,z0,z2,z97,z5,z6]),(0,[z0,z1125,z2,z4,z5,z6]),(0,[z40,z0,z7,z2,z5,z409]),(0,[z79,z0,z123,z4,z5,z309])],[(0,[z1,z2,z513,z4,z5,z6]),(0,[z0,z1,z2,z4,z112,z5]),(0,[z0,z7,z2,z4,z5,z1126]),(0,[z0,z7,z2,z1127,z5,z6]),(0,[z0,z7,z1128,z4,z5,z6]),(0,[z1129,z7,z2,z4,z5,z6])],[(0,[z40,z1,z2,z36,z5,z6]),(0,[z62,z1,z2,z4,z5,z143]),(0,[z33,z7,z2,z329,z5,z78]),(0,[z1130,z7,z2,z4,z5,z6]),(1,[z0,z7,z4,z5,z722])],[(0,[z0,z7,z2,z1131,z5,z6]),(0,[z59,z7,z182,z366,z5,z6]),(0,[z1132,z7,z2,z4,z5,z6]),(0,[z1133,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1134]),(0,[z0,z1135,z2,z4,z5,z6])],[(0,[z0,z198,z2,z366,z5,z6]),(0,[z33,z223,z2,z4,z5,z6]),(0,[z311,z0,z2,z20,z5,z6]),(0,[z1136,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z706,z131,z6]),(0,[z69,z250,z0,z4,z5,z39]),(0,[z0,z7,z90,z4,z5,z226]),(0,[z0,z7,z1137,z4,z5,z6])],[(0,[z211,z7,z2,z36,z5,z6]),(0,[z0,z7,z2,z857,z4,z5]),(0,[z165,z7,z2,z854,z5,z6]),(0,[z0,z7,z2,z4,z1138,z5]),(0,[z347,z7,z2,z4,z5,z38]),(0,[z0,z7,z53,z4,z5,z68])],[(0,[z139,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z1139,z6]),(0,[z79,z0,z123,z4,z5,z6]),(0,[z1140,z0,z2,z4,z5,z6])]],
   [[],[(0,[z0,z7,z2,z4,z1141,z6]),(0,[z157,z7,z182,z4,z5,z6]),(0,[z0,z316,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1142]),(0,[z42,z130,z2,z4,z5,z6]),(0,[z617,z0,z7,z88,z5,z6]),(0,[z7,z2,z4,z1143,z5,z6]),(0,[z40,z45,z7,z2,z5,z6]),(0,[z0,z7,z2,z4,z5,z1144]),(0,[z0,z7,z2,z5,z194,z332])],[(0,[z412,z1,z2,z36,z5,z6]),(0,[z30,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z366,z214,z6]),(0,[z994,z45,z2,z4,z5,z6]),(0,[z0,z7,z294,z131,z5,z6])],[(0,[z0,z7,z2,z4,z5,z1145]),(0,[z0,z1,z2,z5,z6,z195]),(0,[z46,z299,z2,z4,z5,z6]),(0,[z113,z7,z2,z4,z37,z6]),(0,[z449,z7,z2,z36,z5,z6]),(0,[z0,z7,z158,z222,z5,z6]),(0,[z0,z7,z2,z222,z5,z159]),(0,[z285,z0,z2,z20,z5,z6]),(0,[z1146,z0,z2,z4,z5,z6]),(0,[z1147,z0,z7,z2,z5,z6]),(0,[z0,z1148,z2,z4,z5,z6])],[(0,[z684,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1149]),(0,[z0,z1150,z2,z4,z5,z6]),(0,[z45,z82,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z143]),(0,[z1,z2,z532,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z271]),(0,[z9,z41,z60,z4,z5,z6]),(0,[z7,z60,z844,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z246]),(0,[z0,z7,z1151,z4,z5,z6])],[(0,[z0,z7,z2,z366,z228,z6]),(0,[z41,z50,z60,z4,z5,z6]),(0,[z1152,z0,z2,z4,z5,z6]),(0,[z0,z7,z213,z88,z5,z6]),(0,[z0,z7,z23,z4,z5,z722])],[(0,[z0,z1,z2,z278,z5,z6]),(0,[z0,z7,z2,z1153,z5,z6]),(0,[z0,z7,z2,z4,z5,z1154])]],
   [[(0,[z1,z2,z4,z5,z6,z384]),(0,[z227,z0,z2,z4,z5,z544]),(0,[z267,z2,z4,z36,z5,z6]),(0,[z0,z218,z25,z4,z5,z6]),(0,[z0,z73,z4,z5,z6,z688])],[(0,[z0,z7,z25,z222,z5,z6]),(0,[z26,z7,z2,z453,z37,z6])],[(0,[z199,z0,z1,z88,z5,z6]),(0,[z95,z0,z2,z4,z5,z736]),(0,[z0,z7,z88,z5,z39,z205])],[(0,[z0,z1,z2,z4,z5,z27]),(0,[z1,z2,z4,z52,z54,z6]),(0,[z0,z7,z2,z878,z5,z6]),(0,[z7,z2,z4,z5,z78,z775]),(0,[z169,z7,z2,z178,z5,z6]),(0,[z0,z7,z53,z19,z5,z6])],[(0,[z0,z1,z294,z4,z5,z6]),(0,[z0,z235,z25,z4,z5,z6]),(0,[z169,z7,z2,z183,z5,z6]),(0,[z0,z7,z2,z1155,z5,z6])],[(0,[z1,z2,z4,z5,z6,z38]),(0,[z249,z1,z2,z4,z5,z6]),(0,[z9,z0,z2,z178,z5,z6]),(0,[z0,z82,z2,z4,z5,z226])],[(0,[z419,z0,z2,z4,z472,z6]),(0,[z9,z0,z25,z4,z5,z6]),(0,[z117,z9,z0,z4,z54,z6]),(0,[z9,z0,z2,z183,z5,z6]),(0,[z0,z7,z2,z4,z5,z1156]),(0,[z617,z0,z7,z2,z5,z205]),(0,[z45,z120,z2,z4,z5,z6]),(0,[z57,z0,z7,z2,z58,z6])],[(0,[z1,z2,z4,z5,z6,z562]),(0,[z0,z316,z2,z4,z5,z118]),(0,[z59,z7,z182,z4,z5,z150]),(0,[z0,z7,z2,z4,z1157,z5]),(0,[z0,z7,z2,z4,z5,z1158]),(0,[z0,z7,z342,z4,z5,z24])]],
   [[(0,[z1159,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z100,z196])],[(0,[z9,z169,z2,z4,z5,z6])],[(0,[z41,z1,z2,z4,z5,z6]),(0,[z101,z1,z2,z4,z5,z38]),(0,[z1160,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z362,z4,z253]),(0,[z0,z7,z4,z530,z5,z39]),(0,[z250,z760,z2,z4,z5,z6]),(0,[z139,z892,z2,z4,z5,z6]),(0,[z1161,z7,z2,z4,z5,z6])],[(0,[z175,z1,z2,z4,z5,z6]),(0,[z465,z115,z2,z4,z5,z6]),(0,[z0,z7,z1162,z4,z5,z6]),(0,[z0,z7,z2,z530,z5,z6]),(0,[z0,z1163,z2,z4,z5,z6])],[(0,[z517,z1,z2,z4,z5,z6]),(0,[z585,z7,z2,z4,z5,z38]),(0,[z0,z7,z2,z435,z5,z189])],[(0,[z0,z1,z2,z5,z964,z6]),(0,[z1164,z7,z2,z4,z5,z6])],[(0,[z1,z2,z158,z4,z5,z6]),(0,[z9,z0,z2,z4,z214,z6]),(0,[z0,z316,z2,z4,z5,z150]),(0,[z0,z7,z2,z1165,z5,z6]),(0,[z0,z7,z1166,z4,z5,z6]),(0,[z0,z7,z1167,z4,z5,z6]),(0,[z0,z7,z495,z19,z5,z6]),(1,[z0,z7,z2,z826,z6])],[(0,[z0,z7,z2,z1168,z5,z6]),(0,[z0,z7,z158,z4,z5,z27]),(0,[z151,z243,z2,z20,z5,z6]),(0,[z0,z7,z2,z907,z5,z6]),(0,[z0,z120,z2,z4,z5,z226]),(0,[z1169,z0,z2,z4,z5,z6])]],
   [[(0,[z312,z0,z1,z2,z5,z6]),(0,[z573,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z219]),(0,[z152,z1,z2,z4,z5,z6]),(0,[z0,z72,z546,z4,z5,z6]),(0,[z33,z122,z2,z4,z5,z78]),(0,[z0,z7,z2,z1170,z5,z6]),(0,[z0,z7,z2,z100,z195,z196])],[(0,[z113,z1,z2,z4,z5,z6]),(0,[z473,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z1171,z5,z6]),(0,[z0,z7,z2,z1172,z5,z6]),(0,[z1173,z7,z2,z4,z5,z6])],[(0,[z0,z7,z2,z1174,z5,z6]),(0,[z33,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z49,z5,z6]),(0,[z1,z2,z4,z421,z5,z6]),(0,[z0,z1,z2,z329,z5,z6]),(0,[z9,z115,z2,z4,z5,z6]),(0,[z9,z0,z2,z4,z228,z6]),(0,[z26,z267,z2,z4,z5,z6]),(0,[z467,z0,z7,z4,z54,z6]),(0,[z249,z95,z2,z4,z5,z133]),(0,[z0,z7,z1175,z4,z5,z6]),(0,[z40,z0,z7,z460,z5,z205])],[(0,[z9,z0,z2,z162,z5,z194])],[(0,[z9,z0,z2,z4,z5,z240]),(0,[z0,z2,z4,z5,z6,z48]),(0,[z1176,z7,z2,z4,z5,z6]),(0,[z0,z7,z19,z767,z5,z6]),(0,[z1177,z7,z2,z4,z5,z6]),(0,[z0,z7,z2,z826,z58,z6]),(0,[z0,z7,z2,z1178,z5,z6])],[(0,[z69,z9,z0,z4,z5,z39]),(0,[z0,z7,z1179,z4,z5,z6]),(0,[z0,z7,z1180,z4,z5,z6])],[(0,[z778,z0,z1,z2,z4,z5]),(0,[z0,z1,z4,z5,z978,z6]),(0,[z0,z7,z1181,z4,z5,z6]),(0,[z0,z7,z2,z5,z6,z1182]),(0,[z0,z7,z2,z4,z5,z736]),(0,[z0,z7,z2,z4,z989,z6]),(0,[z0,z7,z4,z5,z989,z6]),(0,[z0,z7,z2,z213,z5,z271])],[(0,[z26,z1,z2,z453,z5,z6]),(0,[z156,z1,z2,z4,z5,z6]),(0,[z0,z7,z56,z88,z5,z6]),(0,[z45,z7,z2,z5,z194,z6])]],
   [[(0,[z8,z1,z182,z4,z5,z6]),(0,[z0,z72,z73,z4,z5,z6]),(0,[z0,z7,z486,z4,z94,z6])],[(0,[z465,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z1183,z5,z6]),(0,[z0,z7,z2,z88,z5,z68]),(0,[z0,z7,z53,z213,z5,z6]),(0,[z0,z7,z426,z4,z5,z24]),(0,[z1184,z0,z2,z4,z5,z6])],[(0,[z79,z0,z601,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1185]),(0,[z0,z7,z1186,z4,z5,z6])],[(0,[z0,z7,z2,z4,z5,z1187]),(0,[z0,z1,z2,z4,z5,z986]),(0,[z0,z7,z1188,z4,z5,z6]),(0,[z0,z1189,z2,z4,z5,z6])],[(0,[z732,z7,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z446]),(0,[z57,z0,z1,z2,z58,z6]),(0,[z164,z1,z2,z4,z5,z6]),(0,[z7,z844,z182,z4,z5,z6]),(0,[z1190,z0,z2,z4,z5,z6]),(0,[z0,z1191,z2,z4,z5,z6]),(0,[z0,z7,z2,z1192,z5,z6]),(0,[z155,z235,z2,z4,z5,z6])],[(0,[z742,z41,z2,z4,z5,z6]),(0,[z62,z1,z2,z136,z5,z6]),(0,[z9,z0,z2,z5,z6,z195]),(0,[z0,z1193,z2,z4,z5,z6]),(0,[z0,z7,z2,z4,z5,z1194]),(0,[z0,z7,z2,z4,z5,z1195])],[(0,[z0,z50,z2,z4,z5,z6]),(0,[z1196,z0,z2,z4,z5,z6]),(0,[z13,z0,z2,z4,z132,z6]),(0,[z0,z7,z2,z97,z5,z6])],[(0,[z412,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z4,z80,z6]),(0,[z9,z0,z2,z4,z5,z271])]],
   [[(0,[z9,z1,z2,z4,z5,z6]),(0,[z0,z1197,z2,z4,z5,z6]),(0,[z0,z7,z2,z222,z5,z27]),(0,[z7,z2,z4,z52,z828,z6]),(0,[z1198,z7,z2,z4,z5,z6]),(0,[z45,z7,z2,z4,z5,z226]),(0,[z0,z7,z2,z5,z194,z226]),(0,[z312,z0,z7,z841,z5,z6])],[(0,[z0,z7,z2,z4,z5,z1199]),(0,[z0,z7,z2,z4,z5,z1200]),(0,[z46,z7,z2,z453,z5,z6]),(0,[z9,z0,z2,z278,z5,z6]),(0,[z0,z7,z182,z4,z228,z6]),(0,[z0,z7,z2,z4,z5,z1201]),(0,[z51,z7,z2,z4,z828,z6]),(0,[z312,z0,z7,z2,z5,z78]),(0,[z0,z7,z2,z178,z5,z219]),(0,[z0,z7,z2,z4,z1202,z5]),(0,[z0,z7,z2,z4,z826,z6])],[(0,[z499,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z453,z5,z6]),(0,[z256,z7,z2,z4,z52,z6]),(0,[z1203,z0,z2,z4,z5,z6]),(0,[z0,z7,z2,z183,z5,z219]),(0,[z79,z0,z735,z4,z5,z6])],[(0,[z0,z7,z4,z5,z6,z937]),(0,[z9,z165,z2,z36,z5,z6]),(0,[z0,z1204,z2,z4,z5,z6]),(0,[z1205,z7,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1007]),(0,[z9,z0,z23,z4,z5,z24]),(0,[z576,z0,z2,z4,z5,z246]),(0,[z1206,z7,z2,z4,z5,z6])],[(0,[z1,z2,z601,z4,z5,z6]),(0,[z9,z0,z2,z4,z5,z27]),(0,[z0,z7,z2,z178,z268,z6])],[(0,[z130,z7,z2,z4,z5,z6]),(0,[z9,z681,z2,z4,z5,z6]),(0,[z0,z7,z2,z1207,z5,z6]),(0,[z0,z114,z2,z4,z5,z246]),(0,[z0,z7,z2,z4,z5,z1208]),(0,[z0,z2,z4,z5,z736,z133]),(0,[z0,z7,z2,z767,z5,z6]),(0,[z0,z7,z2,z435,z5,z6]),(0,[z276,z0,z7,z4,z5,z39])],[(0,[z134,z0,z2,z4,z5,z325]),(0,[z0,z1209,z2,z4,z5,z6]),(0,[z0,z7,z1210,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 511) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 511).take 514) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1025).take 240) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1265)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [511, 514, 240] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 77).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 77).take 81).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 158).take 76).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 234).take 22).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [77, 81, 76, 22] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_36334

theorem PEqualNP.Outside.L_meta_36334 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277061824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277061824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36334.solve