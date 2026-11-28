import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36641

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
  Nat.testBit (4008372936 * 2 ^ 32 + 3970476168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x5250a00b28294a55#64 ++ 0x00042613442869aa#64 ++ 0xfff1f03ff8ffffff#64 ++ 0xff463f1fc638ffff#64 : BitVec 256),
   (0xa0a312c051509428#64 ++ 0xd03188c433868615#64 ++ 0xf1ffffc0fff8fe3f#64 ++ 0xffb9c8e47fcf8e3f#64 : BitVec 256),
   (0x01345555009a2682#64 ++ 0xd2c170b869d0d34c#64 ++ 0x01fe7fff00ff3fce#64 ++ 0xd2c1f0f879f0f3cc#64 : BitVec 256),
   (0x340069a69a003903#64 ++ 0x54ee00ee817d02f0#64 ++ 0xfe007fffff003ff3#64 ++ 0x54fe00ff81ff03f0#64 : BitVec 256),
   (0x00007e38e4e40003#64 ++ 0x88dfdd0000fbbc00#64 ++ 0x00007fffffffc003#64 ++ 0x98ffff0001fffc00#64 : BitVec 256),
   (0xc9c8000000000002#64 ++ 0x20fafb7dde000000#64 ++ 0xffff800000000003#64 ++ 0xe0fffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000020040400000 0x0010880000020400 0x00000000ff00c001 0x08380800000f0c00

def z1 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00007fffffffc003 0x98ffff0001fffc00

def z2 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z3 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe007fffff003ff3 0x54fe00ff81ff03f0

def z4 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0xfff1f03ff8ffffff 0xff463f1fc638ffff

def z5 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xf1ffffc0fff8fe3f 0xffb9c8e47fcf8e3f

def z6 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xffff800000000003 0xe0fffffffe000000

def z7 : W := mkw 0x140069268a002903 0x04ce002a807900e0 0x0e007fffff0001c3 0x10fe001b81ff01c0

def z8 : W := mkw 0x5354e51f28ab6ad7 0x02c4763b4c7879ea 0xfff1f03ff8ffffff 0xff463f1fc638ffff

def z9 : W := mkw 0xc8c8000000000000 0x203a8b4596000000 0xfe01800000000001 0x203e0f0786000000

def z10 : W := mkw 0xb4a301c61b10bd28 0x542000eeb30402f5 0xffff800000003ffc 0x670000fffe0003ff

def z11 : W := mkw 0x80a3124041508428 0x8011880032828405 0x01ff800000f8c00c 0xab01c8007e008c0f

def z12 : W := mkw 0xb4a37be6db50bd2b 0xd4ff88eeb3ff86f5 0xfffffffffff8ffff 0xffffc8ffffff8fff

def z13 : W := mkw 0xdbd8a00b28294a57 0x20feff7fde2869aa 0xffff803f000701c3 0xe0fffffffe3071c0

def z14 : W := mkw 0x0124555400922482 0xd2c170b869d09244 0x01fe0fc000000002 0xc0c1f0f879c00000

def z15 : W := mkw 0x0000100000000000 0x8001000000808000 0x00007fc000f80002 0x9081c00001c08000

def z16 : W := mkw 0x0020104000100400 0xd001008021808204 0x000e0fc000000000 0x0081c0e039c00000

def z17 : W := mkw 0x140069268a002903 0x04ce002a807900e0 0x0e00003f000001c0 0x0046001b803001c0

def z18 : W := mkw 0x0000000000000000 0x0000000000000000 0xf1f1800000000003 0xe000080446000000

def z19 : W := mkw 0x202312c051509428 0xd001008021868615 0x00007fc0fff8fe3c 0x1f00000001cf8e3f

def z20 : W := mkw 0x8080000000000000 0x0030884412000000 0xf1ff800000000003 0xe0b9c8e47e000000

def z21 : W := mkw 0xa9ab12c05150942a 0xf0fbd9ecbb868615 0x000e0fc007000000 0x00b9c0e039c70000

def z22 : W := mkw 0xa0a37ef8f5f4942b 0xd8ffddc433ffbe15 0xf1fffffffffffe3f 0xffffffe47ffffe3f

def z23 : W := mkw 0x340069a69a003903 0x04ee006e807d00f0 0xfe00003fff0001f1 0x047e001f803f01f0

def z24 : W := mkw 0xe9eb12c05150942a 0xf0fbfbfdff868615 0xffff8fc007000003 0xe0ffffffffc70000

def z25 : W := mkw 0x0000410400002002 0x50c000a801500240 0x00007fff00003fc2 0x50c000f801f003c0

def z26 : W := mkw 0x35347df79a9a3f83 0xd6ef70fee9fdd3fc 0xfffe7fffffff3fff 0xd6fff0fff9fff3fc

def z27 : W := mkw 0xe8eb12c051509428 0xf03b8bc5b7868615 0xffffffc0fff8fe3f 0xffbfcfe7ffcf8e3f

def z28 : W := mkw 0x00007e38e4e40003 0x88cf040000fbbc00 0x00007fffffffc003 0x18fe000001fffc00

def z29 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0xf1fffffff8ffffff 0xffc1f8fc7ff8ffff

def z30 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0x0e00003f000701c0 0x0046371b803071c0

def z31 : W := mkw 0xf2f3b2cb7979de7d 0xd035aed777aeefbf 0xffffffffffffffff 0xffffffffffffffff

def z32 : W := mkw 0x00345555009a2680 0xd201209061d0d34c 0x01f07fff00ff3fce 0xd240301841f0f3cc

def z33 : W := mkw 0x4948000000000002 0x20ca7339cc000000 0x0e00000000000000 0x0046371b80000000

def z34 : W := mkw 0xa0a300c011109428 0x502000c433040215 0xf1ff800000003e3c 0x670000e47e00023f

def z35 : W := mkw 0x00006c38a4a40003 0x08ce550000793800 0x0000003f00070000 0x0046370000307000

def z36 : W := mkw 0x340001861a003900 0x542000ee810402f0 0xfe007fc0ff003ff3 0x54b800ff81cf03f0

def z37 : W := mkw 0x5040200208000801 0x00042213442800a0 0xfff1f03ff8003ff3 0xf4463f1fc63803f0

def z38 : W := mkw 0x3000208218001801 0x502400c6012c02b0 0xfe007fffff003ff3 0x54fe00ff81ff03f0

def z39 : W := mkw 0x00007c3080800003 0x80cf500000f99000 0x00007fffffff0003 0x90fff00001fff000

def z40 : W := mkw 0x00345555009a2680 0xd201008021d0d34c 0x00007fff00ff3fcc 0x1200000001f0f3cc

def z41 : W := mkw 0x0124555400922482 0xd2c150a829d09244 0x000e0fc000000000 0x0081c0e039c00000

def z42 : W := mkw 0xc9fc1451009a0680 0xa211fb117e80d10c 0x01ff800000ff000c 0xa201ff007e00f00c

def z43 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0007000f8003e33 0x5400000400080230

def z44 : W := mkw 0x0110000100080202 0x00c0703848004108 0x01fe703f00ff3fce 0xd2c1f0f87830f3cc

def z45 : W := mkw 0xcbd8800920294256 0x20faff7dde00690a 0xffff800000ffc00f 0xebfffffffe00fc0f

def z46 : W := mkw 0x00006c38a4a40003 0x08dedd0000793800 0x0000003f00070003 0x80ffff0000307000

def z47 : W := mkw 0x5250fe3beced4a57 0x88dfff1344fbfdaa 0xfff1ffffffffffff 0xffffff1fc7ffffff

def z48 : W := mkw 0x1000610608002803 0x50c400aa017802e0 0xfe007ffff8003ff3 0x54c600ff81f803f0

def z49 : W := mkw 0x0000000000000002 0x00ca002880000000 0x0e00000000000000 0x0046001b80000000

def z50 : W := mkw 0x00006c38a4a40003 0x08ce550000793800 0x0000703ff8ffc003 0x98463f000038fc00

def z51 : W := mkw 0x0000000000000000 0x0000000000000000 0x01fe000000000002 0xc081c0e078000000

def z52 : W := mkw 0x8080000000000000 0x0030884412000000 0xf001800000000001 0x2038080406000000

def z53 : W := mkw 0x1210a00b28294a55 0x00040402002869aa 0x0000703ff8fffffc 0x1f0000000038ffff

def z54 : W := mkw 0x8080000000000002 0x00fa886c92000000 0xffff800000000003 0xe0ffc8fffe000000

def z55 : W := mkw 0x00005e30c4c40002 0x88dbd90000d39400 0x00000fc007000000 0x00b9c00001c70000

def z56 : W := mkw 0xffd8e9afba297b57 0x74feffffdf7d6bfa 0xffffffffffffffff 0xffffffffffffffff

def z57 : W := mkw 0x8080000000000000 0x0010880012000000 0x01ff800000000000 0xa001c8007e000000

def z58 : W := mkw 0xa0a312c05150942a 0xd0fb88ecb3868615 0xffffffc0fff8fe3f 0xffffc8ffffcf8e3f

def z59 : W := mkw 0xa0a312c051509428 0xd011888033868615 0x01ffffc0fff8fe3c 0xbf01c8007fcf8e3f

def z60 : W := mkw 0x340069a69a003901 0x54040082017d02f0 0x00007fffff003ff0 0x1400000001ff03f0

def z61 : W := mkw 0xc9c8000000000000 0x2010fb115e000000 0x01ff800000000000 0xa001ff007e000000

def z62 : W := mkw 0x34007fbefee43903 0xdcffddee81ffbef0 0xfe007ffffffffff3 0xdcffffff81fffff0

def z63 : W := mkw 0x7650e9afba297b57 0x54ee26ffc57d6bfa 0xfff1ffffffffffff 0xfffe3fffc7ffffff

def z64 : W := mkw 0x01144515008a2282 0x02c0703848505148 0x0000003f000701c0 0x00403018003071c0

def z65 : W := mkw 0x25345df5929a3782 0xd6eb70fce9d5d35c 0x01fe7fff07ff3fce 0xd2f9f0f879f7f3cc

def z66 : W := mkw 0x2000008010001000 0x502000c401040210 0xf0007fc0ff003e33 0x54b800e401cf0230

def z67 : W := mkw 0x340069a69a003903 0x54ce00aa817d02f0 0x0e007fffff003ff0 0x1446001b81ff03f0

def z68 : W := mkw 0xa0a300c011109428 0x503088c433040215 0xf1ff800000003e3f 0xe7b9c8e47e00023f

def z69 : W := mkw 0xc9d8000100080202 0x20fafb7dde004108 0xfffff03f00ff3fcf 0xf2fffffffe30f3cc

def z70 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe00000000000003 0x4046001f80000000

def z71 : W := mkw 0xd2f3b24b6979ce7d 0x8015ae1376aaedaf 0xfffff03ff8ffffff 0xff47ff1ffe38ffff

def z72 : W := mkw 0x80a3124041508428 0x8031884432828405 0xf1ff800000f8c00f 0xebb9c8e47e008c0f

def z73 : W := mkw 0xf2c3a28a7961d87d 0x00348e47162e2cb3 0xfe018000ff00c031 0x2d3e0f07860f0c33

def z74 : W := mkw 0xc2f392496179c67c 0x8011ae117682ed0f 0x01ff800000ffc00c 0xab01ff007e00fc0f

def z75 : W := mkw 0x5250aa2bec6d4a55 0x081eaf13442b6daa 0xfff1f03fffffffff 0xff7e3f1fc63fffff

def z76 : W := mkw 0xc9dc4515008a2282 0x22fafb7dde505148 0xffff803f000701c3 0xe0fffffffe3071c0

def z77 : W := mkw 0x0100000000000002 0x00c0703848000000 0x01fe000000000002 0xc0c1f0f878000000

def z78 : W := mkw 0xa1b77ffdf5feb6ab 0xdafffdfc7bffff5d 0xf1ffffffffffffff 0xfffffffc7fffffff

def z79 : W := mkw 0x34006baefe643903 0x5cfe8dee817f2ef0 0xfe007fffff00fff3 0x5cfe0fff81ff0ff0

def z80 : W := mkw 0xb4a369e69b10bd2b 0x54ee00eeb37d02f5 0xffffffffff003fff 0x77fe00ffffff03ff

def z81 : W := mkw 0xc9c8000000000002 0x20d0fb395e000000 0x01ff800000000002 0xe0c1fff87e000000

def z82 : W := mkw 0xdbc8a00a28214857 0x20feff7fde2828a2 0xffff8000f800c033 0xedfffffffe080c33

def z83 : W := mkw 0x0000400000000002 0x00c0000000500000 0x00007fff00000002 0x10c0000001f00000

def z84 : W := mkw 0x0020104000100400 0xd001008021808204 0x01fe7fc000f83e0e 0xd281c0e079c0820c

def z85 : W := mkw 0xa1b757d551dab6aa 0xd2f1f8fc7bd6d75d 0xf1ffffffffffffff 0xfff9f8fc7fffffff

def z86 : W := mkw 0x0000000000000000 0x0000000000000000 0x00007fc0ff000003 0x10b8000001cf0000

def z87 : W := mkw 0x0010410500082202 0x50c020b841504348 0x01f07fff00ff3fce 0xd2c030f841f0f3cc

def z88 : W := mkw 0x34237be6db50bd29 0xd405008221ff86f5 0x00007ffffff8fffc 0x1f00000001ff8fff

def z89 : W := mkw 0x5374f55f28bb6ed7 0xd2c576bb6df8fbee 0x0ffe7fff00ff3fce 0xd2c7f7fbf9f0f3cc

def z90 : W := mkw 0xf2f392c35959de7c 0xd031aad77786c7bf 0xffffffc0fff8ffff 0xffb9c8ffffcf8fff

def z91 : W := mkw 0x01341451009a0680 0x820170106880d10c 0x01fe000000ff000c 0x8201f0007800f00c

def z92 : W := mkw 0x340028a29a001901 0x042e0046802d00b0 0xfe000000ff000031 0x043e0007800f0030

def z93 : W := mkw 0x0010000100080200 0x0000201040004108 0x0000003f000701c0 0x00403018003071c0

def z94 : W := mkw 0xc8c8000000000000 0x203a8b4596000000 0xffff800000000003 0xe0bfcfe7fe000000

def z95 : W := mkw 0x01340145001a2680 0x520020b86900434c 0x01fe703f00ff3fce 0xd24030f87830f3cc

def z96 : W := mkw 0xd9c8200208000803 0x20fefb7fde2800a0 0xfffff03ff8003ff3 0xf4fffffffe3803f0

def z97 : W := mkw 0x0030104100180600 0xd00120906180c30c 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z98 : W := mkw 0x34347df79a9a3f81 0xd605008221fdd3fc 0x00007fffffff3ffc 0x1600000001fff3fc

def z99 : W := mkw 0xa0b312c151589628 0xd031a8d47386c71d 0xf1ffffffffffffff 0xfff9f8fc7fffffff

def z100 : W := mkw 0x0010000100080200 0x0000201040004108 0x01f0703f00ff3fce 0xd24030184030f3cc

def z101 : W := mkw 0xc9fc1451009a0682 0xa2fbfb7dfe80d10c 0xffff800000ff000f 0xe2fffffffe00f00c

def z102 : W := mkw 0x7650e9afba297b55 0x54042693457d6bfa 0xfff1ffffffffffff 0xff463f1fc7ffffff

def z103 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0x000e0fc007000000 0x00b9c0e039c70000

def z104 : W := mkw 0xc9c8000000000000 0x2010fb115e000000 0xffff800000000003 0xe047ff1ffe000000

def z105 : W := mkw 0x40407e38e4e40003 0x88dfff1144fbbc00 0xfff1ffffffffc003 0xf8ffff1fc7fffc00

def z106 : W := mkw 0x5250e10f28296a57 0x50c426bb45786bea 0xfff1fffff8ffffff 0xffc63fffc7f8ffff

def z107 : W := mkw 0x4250800920294254 0x000026114400690a 0x0000000000070000 0x0000370000007000

def z108 : W := mkw 0x4250961964ed4254 0x8811ff114482fd0a 0x01f1800000ffc00c 0xab01ff004600fc0f

def z109 : W := mkw 0xfdfc7df79a9a3f83 0xf6fffbfffffdd3fc 0xffffffffffff3fff 0xf6fffffffffff3fc

def z110 : W := mkw 0x00345555009a2682 0xd2c100a821d0d34c 0x00007fff00ff3fce 0x52c000f801f0f3cc

def z111 : W := mkw 0x8080000000000000 0x0020004412000000 0xf1ff800000000000 0x600000e47e000000

def z112 : W := mkw 0xa0a312c051509428 0xd02100c433868615 0xf1ffffc0fff8fe3c 0x7f0000e47fcf8e3f

def z113 : W := mkw 0x01347f7de4fe2683 0xdac574b869fbff4c 0x01fe7fffffffffce 0xdac1f0f879ffffcc

def z114 : W := mkw 0x5374f55f28bb6ed7 0xd2c576bb6df8fbee 0xfffffffff8ffffff 0xffc7fffffff8ffff

def z115 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xfffff000f8f8fe3f 0xfffffffffe088e3f

def z116 : W := mkw 0xe9eb7ef8f5f4942b 0xf8fffffdffffbe15 0xfffffffffffffe3f 0xfffffffffffffe3f

def z117 : W := mkw 0xe9eb12c05150942a 0xf0fbfbfdff868615 0xffffffc0fff8fe3f 0xffffffffffcf8e3f

def z118 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00007fffffffc000 0x18b9c00001fffc00

def z119 : W := mkw 0x5240800208014854 0x00000203040000a2 0xfe01800000000030 0x2500000786000033

def z120 : W := mkw 0x0023124041508428 0x8001000020828405 0x0000000000f8c00c 0x0b00000000008c0f

def z121 : W := mkw 0xa0a37ef8f5f4942b 0xd8ffddc433ffbe15 0x000e7fffffffc003 0x98ffffe039fffc00

def z122 : W := mkw 0x01340145001a2680 0x520020b86900434c 0x01fe000000003fcc 0x420000f8780003cc

def z123 : W := mkw 0x01347f7de4fe2683 0xdadffdb869fbff4c 0x01fe7fffffffffcf 0xdafffff879ffffcc

def z124 : W := mkw 0x340000821a001900 0x04200046800400b0 0xfe00000000000030 0x0400000780000030

def z125 : W := mkw 0x0000682080000003 0x00ce000000790000 0x00007fffff000003 0x10fe000001ff0000

def z126 : W := mkw 0x01144515008a2282 0x02c0703848505148 0x01fe003f000701c2 0xc0c1f0f8783071c0

def z127 : W := mkw 0xa4a35be4d350b52a 0xd4fb88ecb3d78655 0xf1ffffc0fff8fe3f 0xffb9c8e47fcf8e3f

def z128 : W := mkw 0xc9c8000000000002 0x20dafb39de000000 0x0fff800000000000 0xa047ff1bfe000000

def z129 : W := mkw 0x0000000000000002 0x00ea006c80000000 0xfe00000000000003 0x40fe00ff80000000

def z130 : W := mkw 0x4948000000000002 0x20ca7339cc000000 0x0ffe000000000002 0xc0c7f7fbf8000000

def z131 : W := mkw 0xdac8a00a28214855 0x203e8f47962828a2 0xfe018000f800c031 0x2d3e0f0786080c33

def z132 : W := mkw 0xdbd8a00b28294a57 0x20feff7fde2869aa 0xfffff03ff8ffffff 0xfffffffffe38ffff

def z133 : W := mkw 0xa1a757d451d2b4aa 0xd2f1d8ec3bd69655 0x000e0fc007000000 0x00b9c0e039c70000

def z134 : W := mkw 0xc0c0000000000000 0x0030aa5556000000 0xffff800000000003 0xe0fffffffe000000

def z135 : W := mkw 0x80a3004001108428 0x0000000032000005 0x01ff80000000000c 0x230000007e00000f

def z136 : W := mkw 0xf2f380c31919de7c 0x502022d7770443bf 0xffff800000003ffc 0x670000fffe0003ff

def z137 : W := mkw 0xa0a33ae8f5749429 0xd83f8dc433afae15 0xf1ffffc0fff8fe3f 0xffbfcfe47fcf8e3f

def z138 : W := mkw 0x140001060a002900 0x0400002a800000e0 0x0e000000000001c0 0x0000001b800001c0

def z139 : W := mkw 0x200068a090001003 0x50ee00c4017d0210 0xf0007fffff003e33 0x54fe00e401ff0230

def z140 : W := mkw 0x4250800920294254 0x000026114400690a 0x01f1f03f00ffffce 0xfb403f184630ffcf

def z141 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0x01ff800000000000 0xa0b9ffe07e000000

def z142 : W := mkw 0x8080000000000000 0x0030884412000000 0x000e000000000000 0x00b9c0e038000000

def z143 : W := mkw 0x34237be6db50bd2b 0xd4ef00eea1ff86f5 0xfe007ffffff8ffff 0x5ffe00ff81ff8fff

def z144 : W := mkw 0x14006d3eaea42903 0x0cce552a807938e0 0x0e00003f000701c0 0x0046371b803071c0

def z145 : W := mkw 0x5240a00a28214855 0x00040603042828a2 0xfe018000f800c031 0x2d060f0786080c33

def z146 : W := mkw 0xfdc869a69a003903 0x74fefbffdf7d02f0 0xffffffffff003ff3 0xf4ffffffffff03f0

def z147 : W := mkw 0x0000320860600001 0x80158c0000aaac00 0x00007fffffffc003 0x98ffff0001fffc00

def z148 : W := mkw 0x8988000000000002 0x20fad96c9a000000 0x000e000000000000 0x00b9c0e038000000

def z149 : W := mkw 0x240049a492003102 0x54ea00ec81550250 0x00000fc007000000 0x00b800e001c70000

def z150 : W := mkw 0x1210fe3beced4a55 0x8805040200fbfdaa 0x00007ffffffffffc 0x1f00000001ffffff

def z151 : W := mkw 0x1000200208000801 0x00040002002800a0 0xfe00703ff8003ff3 0x5446001f803803f0

def z152 : W := mkw 0x5250a00b28294a57 0x00deff13442869aa 0xfff1f03ff8ffffff 0xffffff1fc638ffff

def z153 : W := mkw 0xc8c8000000000000 0x203aab55d6000000 0xfff1800000000003 0xe07e3f1fc6000000

def z154 : W := mkw 0x34347df79a9a3f83 0xd6ef00eea1fdd3fc 0xfe007fffffff3fff 0x56fe00ff81fff3fc

def z155 : W := mkw 0xc9c8541000800002 0xa0fbfb7dded09000 0xffffffff00ff0003 0xf0fffffffff0f000

def z156 : W := mkw 0x353469e79a1a3f83 0x56ee20fee97d43fc 0xfffe7fffff003fff 0x56fe00fff9ff03fc

def z157 : W := mkw 0xa083028051409028 0x0030884412060411 0xf0018000ff00c031 0x2d380804060f0c33

def z158 : W := mkw 0xc9fc5555009a2682 0xf2fbfbfdffd0d34c 0xffffffff00ff3fcf 0xf2fffffffff0f3cc

def z159 : W := mkw 0x14007f3eeee42903 0x8cdfdd2a80fbbce0 0x0e007fffffffc1c3 0x98ffff1b81fffdc0

def z160 : W := mkw 0xa0a356d051d0942a 0xd0f1d8c433d69615 0xf1fffffffffffe3f 0xfff9f8e47ffffe3f

def z161 : W := mkw 0x0000161864e40000 0x8811dd000082bc00 0x0000000000ffc000 0x8801ff000000fc00

def z162 : W := mkw 0xc9c8120040400002 0xa0fbfb7dde828400 0xffffffc0fff8c003 0xf8ffffffffcf8c00

def z163 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00000fff07070000 0x00fff70001f77000

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0xf1f1f000f8f8fe3f 0xff00080446088e3f

def z165 : W := mkw 0x340001861a003900 0x542000ee810402f0 0xfe00000000003ff0 0x440000ff800003f0

def z166 : W := mkw 0x01344555009a2682 0x52c070b86950534c 0x01fe003f00073fcc 0x424030f8783073cc

def z167 : W := mkw 0x4250800920294254 0x000026114400690a 0x01f1800000ffc00c 0xab003f004600fc0f

def z168 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000003 0x80463f0000000000

def z169 : W := mkw 0x0020104000100400 0xd001008021808204 0xf1ffffc0f8f8fe3f 0xff81c8e47fc88e3f

def z170 : W := mkw 0x34007fbefee43903 0xdcdfdd8201ffbef0 0x00007ffffffffff3 0x9cffff0001fffff0

def z171 : W := mkw 0xc9c8000000000000 0x203afb55de000000 0xffff800000000001 0xa03fff07fe000000

def z172 : W := mkw 0x5274f55f28bb6ed5 0xd205269365f8fbee 0xfff1fffff8ffffff 0xff463f1fc7f8ffff

def z173 : W := mkw 0x0000000000000000 0x0000000000000000 0x01f1800000f8c00c 0xab00080046008c0f

def z174 : W := mkw 0x5250fe3beced4a57 0x88dfff1344fbfdaa 0x0e007fffffffc1c3 0x98ffff1b81fffdc0

def z175 : W := mkw 0x341069a79a083b03 0x54ee20fec17d43f8 0xfff07fffffff3fff 0xd6fe30ffc1fff3fc

def z176 : W := mkw 0x5374d557089b6ed6 0xd2c172bb6dd0d3ee 0xffffffff00ff3ffe 0xf7c1f0fffff0f3ff

def z177 : W := mkw 0x01145515008a2282 0x82c1703848d0d148 0x00007fff00ff01c2 0x90c1f01801f0f1c0

def z178 : W := mkw 0x340069a69a003903 0x54fed9ee817d02f0 0xfe007fffff003ff3 0xd4ffffff81ff03f0

def z179 : W := mkw 0x0000000000000002 0x00dad90000000000 0x0000000000000003 0x80ffff0000000000

def z180 : W := mkw 0xc9c87e38e4e40003 0xa8ffff7ddefbbc00 0xffffffffffffc003 0xf8fffffffffffc00

def z181 : W := mkw 0xedc849a492003102 0x74fafbfddf550250 0xffff8fc007000003 0xe0ffffffffc70000

def z182 : W := mkw 0x5650e92faa296b57 0x04ce263bc47969ea 0xfff1f03ff8ffffff 0xff463f1fc638ffff

def z183 : W := mkw 0x0000000000000000 0x0000000000000000 0x00007000f8f8fe3c 0x1f00000000088e3f

def z184 : W := mkw 0x5250800308094a54 0x00002213440041aa 0xfff1800000003ffc 0x6700001fc60003ff

def z185 : W := mkw 0x4140000000000002 0x00c072394c000000 0xffff800000000003 0xe0c7fffffe000000

def z186 : W := mkw 0x5350a00b28294a57 0x00c4763b4c2869aa 0xfffff03ff8ffffff 0xffc7fffffe38ffff

def z187 : W := mkw 0x7250a08b38295a55 0x502426d7452c6bba 0xfff1ffffffffffff 0xfffe3fffc7ffffff

def z188 : W := mkw 0x4250800920294254 0x000026114400690a 0xfff1800000ffc00f 0xeb463f1fc600fc0f

def z189 : W := mkw 0x01345555009a2680 0xd201709069d0d34c 0x01fe7fff00ff3fcc 0x9201f00079f0f3cc

def z190 : W := mkw 0x1210a00b28294a55 0x00040402002869aa 0xfe00703ff8ffffff 0x5f46001f8038ffff

def z191 : W := mkw 0x0000541000800002 0x80c1500000d09000 0x00007fff00ff0002 0x90c1f00001f0f000

def z192 : W := mkw 0x0000120040400000 0x8011880000828400 0x0000000000f8c000 0x8801c80000008c00

def z193 : W := mkw 0xa0a300c011109428 0x502000c433040215 0x000e000000000000 0x000000e038000000

def z194 : W := mkw 0x1000200a28200801 0x00040402002828a0 0xfe00703ff8fffff3 0xdc463f1f8038fff0

def z195 : W := mkw 0x4040000000000000 0x0000221144000000 0x01f1800000000000 0xa0003f0046000000

def z196 : W := mkw 0xfcc828a29a001901 0x243e8b47962d00b0 0xfe018000ff000031 0x243e0f07860f0030

def z197 : W := mkw 0x4040000000000000 0x0000221144000000 0xfff1800000000003 0xe0463f1fc6000000

def z198 : W := mkw 0x00003e38e4e40001 0x881fdd0000abbc00 0x00000000ffffc001 0x883fff00000ffc00

def z199 : W := mkw 0x5250800b28294a54 0x00002613440069aa 0xfff1800000fffffc 0xef003f1fc600ffff

def z200 : W := mkw 0x5250b20b68694a55 0x8015ae1344aaedaa 0xfff1ffffffffffff 0xffffff1fc7ffffff

def z201 : W := mkw 0x1210a00b28294a55 0x00040402002869aa 0xf1f1f03ff8ffffff 0xff0008044638ffff

def z202 : W := mkw 0x80a3124041508428 0x8011880032828405 0x000e000000000000 0x0001c00038000000

def z203 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0xfff18000f800fffd 0x6f060f1fc6080fff

def z204 : W := mkw 0x340021861a003901 0x542400ee812c02f0 0xfe00703ff8003ff3 0x544600ff803803f0

def z205 : W := mkw 0x4250800920294254 0x000026114400690a 0xf1f1f000f8fffe3f 0xff003f044608fe3f

def z206 : W := mkw 0x49486c38a4a40003 0x28ce7739cc793800 0x0e00003f00070000 0x0046371b80307000

def z207 : W := mkw 0x01345451009a0682 0x82c1701068d0d10c 0x01fe7fff00ff000e 0x92c1f00079f0f00c

def z208 : W := mkw 0x0000000000000000 0x002a004480000000 0xfe00000000000001 0x003e000780000000

def z209 : W := mkw 0x80a37e78e5f4842b 0x88dfdd0032fbbc05 0x01ffffffffffc00f 0xbbffff007ffffc0f

def z210 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x00007fff00ff3fcc 0x1240301801f0f3cc

def z211 : W := mkw 0x01140105000a2280 0x0200203848004148 0x00000000000001c0 0x00000018000001c0

def z212 : W := mkw 0x0000120040400000 0x8011880000828400 0x00000fc007000000 0x00b9c00001c70000

def z213 : W := mkw 0x1210800308094a54 0x00000002000041aa 0x0000000000003ffc 0x07000000000003ff

def z214 : W := mkw 0x240008a092001100 0x042a004480050010 0x0000000007000000 0x0038000000070000

def z215 : W := mkw 0x1234f55f28bb6ed5 0xd205048221f8fbee 0x00007ffff8fffffc 0x1f00000001f8ffff

def z216 : W := mkw 0x0000120040400000 0x8001000000828400 0x00007fc0fff8c000 0x1800000001cf8c00

def z217 : W := mkw 0x01341145001a2680 0xd20120b86980c34c 0x01fe7fc000f83fce 0xd281c0f879c083cc

def z218 : W := mkw 0x5250800308094a54 0x00002213440041aa 0xfff1f000f8f8ffff 0xff00081fc6088fff

def z219 : W := mkw 0x0000020864640000 0x08108d0000022c00 0x000000000000c000 0x08000f0000000c00

def z220 : W := mkw 0x340001861a003900 0x54000082010402f0 0x0000000000003ff0 0x04000000000003f0

def z221 : W := mkw 0xc9c86c38a4a40003 0x28feff7dde793800 0xffff803f00070003 0xe0fffffffe307000

def z222 : W := mkw 0x01347e79e4fe0683 0x8adffd1068fbfd0c 0x01fe7fffffffc00f 0x9affff0079fffc0c

def z223 : W := mkw 0x342079e69a103d03 0xd4ef00eea1fd82f4 0xfffe7ffffff83fff 0xd6ffc0fff9ff83fc

def z224 : W := mkw 0x0020104000100400 0xd001008021808204 0x00007fc000f83e0c 0x1200000001c0820c

def z225 : W := mkw 0x0000161864e40000 0x8811dd000082bc00 0x00007fc0ffffc003 0x98b9ff0001cffc00

def z226 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0x0e000fff070001c0 0x00fe00fb81f701c0

def z227 : W := mkw 0xa1b757d551dab6aa 0xd2f1f8fc7bd6d75d 0x01fe7fff07ff3fce 0xd2f9f0f879f7f3cc

def z228 : W := mkw 0xc9c82a28e4640003 0x28feff7dde2b2c00 0xffff8000ff00c003 0xe8fffffffe0f0c00

def z229 : W := mkw 0x8080120040400000 0x8031884412828400 0xf1ffffc0fff8c003 0xf8b9c8e47fcf8c00

def z230 : W := mkw 0x01007e38e4e40003 0x88dffd3848fbbc00 0x01fe7fffffffc003 0xd8fffff879fffc00

def z231 : W := mkw 0x0400492482002102 0x04ca002880510040 0x0000000000000000 0x0000000000000000

def z232 : W := mkw 0xa080008010001000 0x503088c413040210 0xf1ffffc0ff003e33 0xf4b9c8e47fcf0230

def z233 : W := mkw 0xdbd8800308094a54 0x2020227fde0041aa 0xffff800000003ffc 0x670000fffe0003ff

def z234 : W := mkw 0x00007e38e4e40001 0x8805040000fbbc00 0x00007fffffffc003 0x98463f0001fffc00

def z235 : W := mkw 0x0000000000000000 0x0010d90000000000 0x0000000000000000 0x8001ff0000000000

def z236 : W := mkw 0x0000200820200001 0x0004040000282800 0x0000703ff8ffc003 0x98463f000038fc00

def z237 : W := mkw 0xa0a35ef0d5d4942a 0xd8fbd9c433d79615 0x000e0fc007000000 0x00b9c0e039c70000

def z238 : W := mkw 0x4040200820200001 0x0004261144282800 0xfff1f03ff8ffc003 0xf8463f1fc638fc00

def z239 : W := mkw 0x1210fe3beced4a57 0x88dfdd0200fbfdaa 0x00007fffffffffff 0x9fffff0001ffffff

def z240 : W := mkw 0xdbd8800308094a56 0x20fafb7fde0041aa 0xffff800000003fff 0xe7fffffffe0003ff

def z241 : W := mkw 0x0100000000000000 0x0000701048000000 0x01fe000000000000 0x8001f00078000000

def z242 : W := mkw 0x8888000000000000 0x203a894492000000 0x0000000000000000 0x0038000000000000

def z243 : W := mkw 0x00006e38e4e40003 0x08dedd00007b3c00 0x0000003fff07c001 0x087e3f00003f7c00

def z244 : W := mkw 0x0124014400122480 0x520000a829000244 0x000e000000000000 0x000000e038000000

def z245 : W := mkw 0x2003028051409028 0x0000000000060411 0x00000000ff00c030 0x0d000000000f0c33

def z246 : W := mkw 0x0000000000000002 0x00fad96c80000000 0xfe00000000000003 0xc0ffffff80000000

def z247 : W := mkw 0xc9c8000000000000 0x2020227dde000000 0xffff800000000000 0x600000fffe000000

def z248 : W := mkw 0x0000541000800002 0x80dbd90000d09000 0x00007fff00ff0003 0x90ffff0001f0f000

def z249 : W := mkw 0x4040000000000002 0x00ea227dc4000000 0xfff1800000000003 0xe0fe3fffc6000000

def z250 : W := mkw 0xc8c8000000000000 0x2020024596000000 0xfe01800000000000 0x2000000786000000

def z251 : W := mkw 0x0000010400002000 0x500000a801000240 0x0000000000003fc0 0x400000f8000003c0

def z252 : W := mkw 0xe8cb028051409028 0x203a8b4596060411 0xfe018000ff00c031 0x2d3e0f07860f0c33

def z253 : W := mkw 0x140069268a002903 0x04ee006e807900e0 0xfe00003f000001c3 0x40fe00ff803001c0

def z254 : W := mkw 0x0000000000000002 0x00dad90000000000 0x0000000000000000 0x00b9c00000000000

def z255 : W := mkw 0x5250a00b28294a55 0x00040603042869aa 0xfe01f03ff8fffffd 0x3f060f078638ffff

def z256 : W := mkw 0xa9ab12c05150942a 0xf0fbd9ecbb868615 0xf1ffffc0fff8fe3f 0xffb9c8e47fcf8e3f

def z257 : W := mkw 0x7273b2cb7979de7d 0xd005269365aeefbf 0xfff1ffffffffffff 0xff463f1fc7ffffff

def z258 : W := mkw 0xa083128051409028 0x8031884412868411 0xf001ffc0fff8c033 0xbdb9c80407cf8c33

def z259 : W := mkw 0x0000561040c00002 0x80d1d80000d29400 0x00007fffffffc003 0x98f9f80001fffc00

def z260 : W := mkw 0x7650a8abba295b55 0x042e2657c42d69ba 0xfff1f03fffffffff 0xff7e3f1fc63fffff

def z261 : W := mkw 0x00002a28e4640001 0x081e8d00002b2c00 0x0000703fffffc003 0x987e3f00003ffc00

def z262 : W := mkw 0x00005e30c4c40002 0x88dbd90000d39400 0x00007fc0fff8c003 0x98b9c80001cf8c00

def z263 : W := mkw 0x8988000000000002 0x20fad96c9a000000 0x000e000000000003 0x80ffffe038000000

def z264 : W := mkw 0xa0a37ef8f5f49429 0xd8358cc433ffbe15 0xf1fffffffffffe3f 0xffb9c8e47ffffe3f

def z265 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xf001ffc0fff8fe3d 0x3f38080407cf8e3f

def z266 : W := mkw 0x213757d551dab6aa 0xd2c170b869d6d75d 0x01fe7ffffffffffe 0xdfc1f0f879ffffff

def z267 : W := mkw 0x00002a28e4640001 0x081e8d00002b2c00 0x00000000ff00c001 0x083e0f00000f0c00

def z268 : W := mkw 0xc9c8000000000000 0x200022115e000000 0x01ff800000000000 0x200000007e000000

def z269 : W := mkw 0x5240a00a28214855 0x00040603042828a2 0xfff1f000f8f8fe3f 0xff060f07c6088e3f

def z270 : W := mkw 0x5250a00b28294a57 0x00ee267fc42869aa 0xfff1f03ff8ffffff 0xfffe3fffc638ffff

def z271 : W := mkw 0xc9c85e30c4c40002 0xa8fbfb7dded39400 0xffff8fc007000003 0xe0ffffffffc70000

def z272 : W := mkw 0x0100000000000002 0x00c0703848000000 0x0000000000000000 0x0040301800000000

def z273 : W := mkw 0x2000418410003002 0x50e000ec01540250 0xf0007fffff003ff3 0x54f800fc01ff03f0

def z274 : W := mkw 0x140069268a002903 0x54ce00aa817902e0 0x0e007fff00003fc2 0x50c600fb81f003c0

def z275 : W := mkw 0x2000008010001000 0x502000c401040210 0x00000fc007000000 0x00b800e001c70000

def z276 : W := mkw 0x0120104000100402 0xd0c170b869808204 0x01fe7fc000f83e0e 0xd2c1f0f879c0820c

def z277 : W := mkw 0x4250fe39e4ed4257 0x88dfff1144fbfd0a 0x01f1ffffffffc00f 0xbbffff0047fffc0f

def z278 : W := mkw 0x1334f55f28bb6ed7 0xd2c574ba69f8fbee 0x01fe7ffff8fffffe 0xdfc1f0f879f8ffff

def z279 : W := mkw 0x0000120040400000 0x8011880000828400 0x00007fc0fff8c003 0x98b9c80001cf8c00

def z280 : W := mkw 0x00144515008a2280 0x0200000000505148 0x0000003f000701c0 0x00000000003071c0

def z281 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0xf1f1fffffffffe3f 0xffffff0447fffe3f

def z282 : W := mkw 0x2000008010001002 0x50ea00ec81040210 0xfe007fc0ff003e33 0x54fe00ff81cf0230

def z283 : W := mkw 0x202312c051509428 0xd001008021868615 0xf1f1ffc0fff8fe3f 0xff00080447cf8e3f

def z284 : W := mkw 0x00345555009a2680 0xd201008021d0d34c 0x01fe7fff00ff3fce 0xd281c0e079f0f3cc

def z285 : W := mkw 0xa1b713c5515ab6a8 0xd231a8fc7b86c75d 0xf1ffffc0fff8ffff 0xffb9c8fc7fcf8fff

def z286 : W := mkw 0xfcc869a69a003903 0x74fe8bef977d02f0 0xfe01ffffff003ff3 0x74fe0fff87ff03f0

def z287 : W := mkw 0x5b58a00b28294a57 0x20ce773bcc2869aa 0xfff1f03ff8ffffff 0xff463f1fc638ffff

def z288 : W := mkw 0x0000161864e40000 0x880104000082bc00 0x0000000000ffc000 0x080000000000fc00

def z289 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01fe0fc000003fcc 0x4281c0f879c003cc

def z290 : W := mkw 0x0000120040400000 0x8011880000828400 0xf1f1ffc0fff8fe3f 0xffb9c80447cf8e3f

def z291 : W := mkw 0x0000200820200001 0x0004040000282800 0xf1f1f03ff8fffe3f 0xff463f044638fe3f

def z292 : W := mkw 0x0000000000000000 0x0000000000000000 0x01f0700000f83e0e 0xd20000004000820c

def z293 : W := mkw 0x0000200820200001 0x0004040000282800 0x00000000f800c001 0x08060f0000080c00

def z294 : W := mkw 0xc9c8000000000002 0x20ea227dde000000 0xffff800000000003 0x60fe00fffe000000

def z295 : W := mkw 0x00006c38a4a40003 0x08ce550000793800 0x00007fffff070003 0x10fe370001ff7000

def z296 : W := mkw 0x0000141000800000 0x8001500000809000 0x0000000000ff0000 0x8001f0000000f000

def z297 : W := mkw 0x5240a00a28214855 0x00040603042828a2 0xfe01f03ff800fff3 0x7d460f1f86380ff3

def z298 : W := mkw 0x7640e9aeba217957 0x54ee06ef857d2af2 0xfe01ffffff00fff3 0x7dfe0fff87ff0ff3

def z299 : W := mkw 0xf2d3a28b7969da7d 0x0034ae57562e6dbb 0xfff1f03fffffffff 0xff7e3f1fc63fffff

def z300 : W := mkw 0x00002a28e4640003 0x08dedd00002b2c00 0x00000000ff00c003 0x88ffff00000f0c00

def z301 : W := mkw 0x00006828a0200003 0x00ce040000792800 0x00007fffffffc003 0x98fe3f0001fffc00

def z302 : W := mkw 0xe9cb02805140902a 0x20fafb7dde060411 0xffff8000ff00c033 0xedfffffffe0f0c33

def z303 : W := mkw 0x4050000100080200 0x0000221144004108 0xfff1f03f00ff3fcf 0xf2463f1fc630f3cc

def z304 : W := mkw 0x340069aeba203903 0x54ee04ee817d2af0 0xfe007ffffffffff3 0xdcfe3fff81fffff0

def z305 : W := mkw 0x4948000000000002 0x20dafb39cc000000 0x0e00000000000003 0x80ffff1b80000000

def z306 : W := mkw 0xdbd8a00b28294a55 0x2024267fde2869aa 0xfffff03ff8ffffff 0xff463ffffe38ffff

def z307 : W := mkw 0xa1b716d151da96a8 0xd231f8d47b86d71d 0xf1ffffc0fffffe3f 0xffb9f8e47fcffe3f

def z308 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xfe01800000000001 0x207e3f1f86000000

def z309 : W := mkw 0x00007e38e4e40001 0x8815dd0000fbbc00 0x00007fffffffc000 0x9801ff0001fffc00

def z310 : W := mkw 0xa0a300c011109428 0x502000c433040215 0xf1ffffc0ff003e3f 0x77b800e47fcf023f

def z311 : W := mkw 0x15146d378a8a2b83 0x06ce703ac87951e8 0x0e00003f000701c0 0x0046301b803071c0

def z312 : W := mkw 0xa1b701c5111ab6a8 0x522020fc7b04435d 0xf1ff800000003ffc 0x670000fc7e0003ff

def z313 : W := mkw 0x0010541100880202 0x80c1701040d0d108 0x01f07fff00ff3fce 0xd2c1f01841f0f3cc

def z314 : W := mkw 0x00005e30c4c40000 0x8801000000d39400 0x00000fc007000000 0x0000000001c70000

def z315 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0x000e7fc0fff8c003 0x98b9c8e039cf8c00

def z316 : W := mkw 0x0000410400002002 0x50c000a801500240 0x00000fc000000000 0x008000e001c00000

def z317 : W := mkw 0x4040000000000000 0x0000221144000000 0x0e00000000000000 0x0046371b80000000

def z318 : W := mkw 0x01144515008a2282 0x02c0703848505148 0x01f0703f00ff3fce 0xd24030184030f3cc

def z319 : W := mkw 0xa1b755d5119ab6aa 0xd2e170fc7bd4d35d 0xf1ffffff00ff3ffe 0xf7c1f0fc7ff0f3ff

def z320 : W := mkw 0x34002aaafe641901 0x0c3e8d46802f2cb0 0xfe000000ff00c031 0x0c3e0f07800f0c30

def z321 : W := mkw 0x34007fbefee43901 0xdc05048201ffbef0 0x00007ffffffffff0 0x1c00000001fffff0

def z322 : W := mkw 0x01341451009a0680 0x820170106880d10c 0x01fe703f00ff3fce 0xd241f0187830f3cc

def z323 : W := mkw 0xad8849a492003102 0x74fad9ec9b550250 0x000e0fc007000000 0x00b9c0e039c70000

def z324 : W := mkw 0x01345555009a2682 0x82c1703868d0d14c 0x01fe003f00ff01cc 0x8241f0187830f1cc

def z325 : W := mkw 0xc9c8000000000000 0x2030fb555e000000 0xf1ff800000000003 0xe0b9ffe47e000000

def z326 : W := mkw 0x01140411008a0280 0x0200701048005108 0x0000000000070000 0x0000300000007000

def z327 : W := mkw 0x202010c010101400 0xd02100c421848214 0xf1fe7fc0fff83e3f 0xd6b9c0e479cf823c

def z328 : W := mkw 0x01341451009a0680 0xd20170906980d30c 0x01fe7fc000ff3e0e 0xd281f0e079c0f20c

def z329 : W := mkw 0x240069a492003103 0x54ee00ec817d0250 0x00007fffff000003 0x10fe00e001ff0000

def z330 : W := mkw 0x0020545000900402 0xd0c1508021d09204 0x01fe7fff00ff3e0e 0xd2c1f0e079f0f20c

def z331 : W := mkw 0x5250ec3bacad4a57 0x08ce7713447979aa 0xfff1f03ff8ffffff 0xff463f1fc638ffff

def z332 : W := mkw 0x00005e38e4e40002 0x88dbdd0000d3bc00 0x00000fc007ffc000 0x88b9ff0001c7fc00

def z333 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01fe0fc000ff000c 0x8281f0e079c0f00c

def z334 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfff1fffffff8ffff 0xfffe08ffc7ff8fff

def z335 : W := mkw 0x5354e51f28ab6ad7 0x02c4763b4c7879ea 0x0e00003f000701c0 0x0046371b803071c0

def z336 : W := mkw 0x0000441000800002 0x00c0500000501000 0x0000003f00070000 0x0040300000307000

def z337 : W := mkw 0x89ac555400922482 0xf2fbd9ecbbd09244 0x000e0fc000000000 0x00b9c0e039c00000

def z338 : W := mkw 0x00004c3084840002 0x08ca510000511000 0x0000000000000000 0x0000000000000000

def z339 : W := mkw 0x0000410400002002 0x00c0002800500040 0x0000003f000001c0 0x00400018003001c0

def z340 : W := mkw 0x0908000000000002 0x20ca512888000000 0x0000000000000000 0x0000000000000000

def z341 : W := mkw 0xa0a353c45150b42a 0xd0f188ec33d68655 0xf1fffffffff8ffff 0xfff9c8fc7fff8fff

def z342 : W := mkw 0xa1a757d451d2b4aa 0xd2f1d8ec3bd69655 0xf1ffffc0fff8fe3f 0xffb9c8e47fcf8e3f

def z343 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0x000e7fc0fff8fe3c 0x1fb9c0e039cf8e3f

def z344 : W := mkw 0xc9eb124041508428 0xa011fb117e828405 0x01ff800000f8c00c 0xab01ff007e008c0f

def z345 : W := mkw 0xc9c8000000000002 0x20e0727dde000000 0xffff800000000002 0xe0c1f0fffe000000

def z346 : W := mkw 0x0010000100080200 0x0000201040004108 0x01f0000000003fcc 0x42000018400003cc

def z347 : W := mkw 0xb5b77ff7dbdabfab 0xd6fff8fefbffd7fd 0xffffffffffffffff 0xfffff8ffffffffff

def z348 : W := mkw 0xa083028051409028 0x0030884412060411 0xf1f1f000fff8fe3f 0xff380804460f8e3f

def z349 : W := mkw 0x353455d71a9a3f82 0xd6e170fee9d4d3fc 0xfffe7fff00ff3ffe 0xd6c1f0fff9f0f3fc

def z350 : W := mkw 0x00007e30c4c40003 0x88dfd90000fb9400 0x00007fffff000003 0x10ffc00001ff0000

def z351 : W := mkw 0xdbd8fe3beced4a57 0xa8ffff7fdefbfdaa 0xffffffffffffffff 0xffffffffffffffff

def z352 : W := mkw 0xc9c8000000000000 0x2030aa7dde000000 0xffff800000000003 0xe0b9c8fffe000000

def z353 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000703f00ff0002 0x904030000030f000

def z354 : W := mkw 0x7774fdffbabb7fd7 0xd6ef76ffedfdfbfe 0xffffffffffffffff 0xffffffffffffffff

def z355 : W := mkw 0x8988000000000002 0x20fad96c9a000000 0xfe0e000000000003 0x40ffc0ffb8000000

def z356 : W := mkw 0x00007e38e4e40003 0x88ffdd6c80fbbc00 0xfe007fffffffc003 0xd8ffffff81fffc00

def z357 : W := mkw 0x202312c051509428 0xd001008021868615 0x01fe7fc0fff8fe3e 0xdf81c0e079cf8e3f

def z358 : W := mkw 0x8988000000000000 0x2010d9001a000000 0x000e000000000000 0x0001c00038000000

def z359 : W := mkw 0x41745555009a2682 0xd2c172b96dd0d34c 0xffffffff00ff3fcf 0xf2c7fffffff0f3cc

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z361 : W := mkw 0xc8c8000000000002 0x20fadb4596000000 0xfe01800000000003 0xa0ffff0786000000

def z362 : W := mkw 0x0000000000000000 0x0000000000000000 0xf1f1800000003e3c 0x670000044600023f

def z363 : W := mkw 0x34007fbefee43903 0xdcef04ee81ffbef0 0xfe007ffffffffff3 0x5cfe00ff81fffff0

def z364 : W := mkw 0x340069a69a003901 0x542400c6017d02f0 0xf0007fffff003ff3 0x54b800e401ff03f0

def z365 : W := mkw 0x0020004000100400 0x5000008021000204 0x01fe000000003e0c 0x420000e07800020c

def z366 : W := mkw 0x3610e9afba297b55 0x54040482017d6bfa 0x00007ffffffffffc 0x1f00000001ffffff

def z367 : W := mkw 0x340028a29a001901 0x542e00c6812d02b0 0xfe007fc0ff003e33 0x54be00e781cf0230

def z368 : W := mkw 0x10007e3aece40803 0x88dfdd0200fbbca0 0xfe007ffffffffff3 0xdcffff1f81fffff0

def z369 : W := mkw 0x765081871a097b54 0x542022ffc50443fa 0xfff1800000003ffc 0x670000ffc60003ff

def z370 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xf00e7fc0ff003e33 0x54b9c0e439cf0230

def z371 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0x0e0e000000000000 0x00fff7fbb8000000

def z372 : W := mkw 0x4848000000000000 0x200a030184000000 0x0e00000000000000 0x0006070380000000

def z373 : W := mkw 0xe9eb12c051509428 0xf031fbd57f868615 0xf1ffffc0fff8fe3f 0xffb9ffe47fcf8e3f

def z374 : W := mkw 0xc9c8000000000002 0x20dafb115e000000 0x01ff800000000003 0xa0ffff007e000000

def z375 : W := mkw 0xf3f7f7df79fbfeff 0xd2f5feff7ffeffff 0xffffffffffffffff 0xffffffffffffffff

def z376 : W := mkw 0x3233b2cb7979de7d 0xd005048221aeefbf 0x00007ffffffffffc 0x1f00000001ffffff

def z377 : W := mkw 0x340041861a003902 0x54e000ee815402f0 0xfe007fff00003ff2 0x54c000ff81f003f0

def z378 : W := mkw 0x0000000000000002 0x00c0500000000000 0x0000000000000002 0x80c1f00000000000

def z379 : W := mkw 0x0010000100080200 0x0000201040004108 0x01f0000000ff000c 0x820030004000f00c

def z380 : W := mkw 0xc9eb12404150842a 0xa0fbfb7dfe828405 0xffff800000f8c00f 0xebfffffffe008c0f

def z381 : W := mkw 0x80a3124041508428 0xd011888033828605 0x01ffffc000f8fe0e 0xfb81c8e07fc08e0f

def z382 : W := mkw 0x240049a492003100 0x5400008001550250 0x00000fc007000000 0x0000000001c70000

def z383 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x0000003f00ffc000 0x8847ff000030fc00

def z384 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0xfff1803f000701c3 0xe0463f1fc63071c0

def z385 : W := mkw 0x35146db79a8a3b83 0x56ee70fec97d53f8 0xfe007fffff073ff3 0x54fe30ff81ff73f0

def z386 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0x0ff1803f00ffc1cc 0xab463f1bc630fdcf

def z387 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xf00f8fc0ff00c031 0x2db9c8e43fcf0c33

def z388 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0x01fe7fc007f83e0e 0xd2b9c0e079c7820c

def z389 : W := mkw 0xfdeb7be6db50bd2b 0xf4fffbffffff86f5 0xfffffffffff8ffff 0xffffffffffff8fff

def z390 : W := mkw 0x24005fb4d6c43102 0xdcfbd9ec81d79650 0x00000fc007000000 0x00b9c0e001c70000

def z391 : W := mkw 0x4250a00920294255 0x000426114428690a 0x01f1f03ff8ffc00f 0xbb463f004638fc0f

def z392 : W := mkw 0x00347f7de4fe2683 0xdadfdd8021fbff4c 0x00007fffffffffcf 0x9affff0001ffffcc

def z393 : W := mkw 0xb4a33ae2db509d29 0xd43f88c6b3af86b5 0xffffffc0fff8fe3f 0xffbfc8e7ffcf8e3f

def z394 : W := mkw 0x340028a29a001901 0x04040002002d00b0 0x00000000ff000030 0x04000000000f0030

def z395 : W := mkw 0x11347557089a2e83 0xd2c570ba69f8d3ec 0xfffe7ffff8ff3fff 0xd6c7f0fff9f8f3fc

def z396 : W := mkw 0x0210800920294254 0x000004000000690a 0x0000000000ffc00c 0x0b0000000000fc0f

def z397 : W := mkw 0xc9fc5555009a2682 0xf2e172fdffd0d34c 0xffffffff00ff3fce 0xf2c1f0fffff0f3cc

def z398 : W := mkw 0x81b7575541daa6aa 0xd2d1f8b87bd2d74d 0x01ffffff00ffffce 0xfbc1f8f87ff0ffcf

def z399 : W := mkw 0x1000682288000803 0x00ce0002007900a0 0xfe007fffff003ff3 0x54fe001f81ff03f0

def z400 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe000fc0ff000031 0x04be00e781cf0030

def z401 : W := mkw 0x00007e38e4e40001 0x8805040000fbbc00 0x00007fffffffc000 0x1800000001fffc00

def z402 : W := mkw 0x5240fe3aece54857 0x88dfdf0304fbbca2 0xfe01ffffffffc033 0xbdffff0787fffc33

def z403 : W := mkw 0x3610e9afba297b57 0x54ee04ee817d6bfa 0xfe007fffffffffff 0x5ffe00ff81ffffff

def z404 : W := mkw 0x7650a18f3a297b55 0x542426ffc52c6bfa 0xfff1f03ff8ffffff 0xff463fffc638ffff

def z405 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xffff800000000000 0x60b9c0fffe000000

def z406 : W := mkw 0x4040000000000002 0x00dafb1144000000 0xfff1800000000003 0xe0ffff1fc6000000

def z407 : W := mkw 0x01345555009a2682 0xd2dbf9b869d0d34c 0x01fe7fff00ff3fcf 0xd2fffff879f0f3cc

def z408 : W := mkw 0x495c4515008a2282 0x22ca7339cc505148 0x0e00003f000701c0 0x0046371b803071c0

def z409 : W := mkw 0x744069a69a003903 0x54ee22ffc57d02f0 0xfff1ffffff003ff3 0xf4fe3fffc7ff03f0

def z410 : W := mkw 0x0020124040500400 0xd011888021828604 0x01fe7fc0fff8fe0f 0xdab9c8e079cf8e0c

def z411 : W := mkw 0x01341555009a2680 0xd20170b86980d34c 0x01fe000000ff3fcc 0xc201f0f87800f3cc

def z412 : W := mkw 0xb0a332c259509c29 0xd03588c633ae86b5 0xfffffffffff8ffff 0xffffc8ffffff8fff

def z413 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0x01ff8fc007f8c00c 0xabb9c8e07fc78c0f

def z414 : W := mkw 0xb4832aa2db409929 0x043e8846922f04b1 0xfe018000ff00c031 0x2d3e0807860f0c33

def z415 : W := mkw 0x1200a00a28214855 0x00040402002828a2 0x00000000f800c030 0x0d00000000080c33

def z416 : W := mkw 0xdad8a00b28294a55 0x203eaf57d62869aa 0xfff1f03ff8ffffff 0xff7e3f1fc638ffff

def z417 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0x0ff0703f00ff3fce 0xd246371bc030f3cc

def z418 : W := mkw 0xe2f392c97179d67c 0xd031aed57786ef1f 0xf1ffffc0fffffe3f 0xffb9ffe47fcffe3f

def z419 : W := mkw 0xbd8869a69a003903 0x74fed9ee9b7d02f0 0xfe0e7fffff003ff3 0x54ffc0ffb9ff03f0

def z420 : W := mkw 0x4240800820214054 0x0000060104002802 0x000180000000c000 0x29000f0006000c03

def z421 : W := mkw 0x240049a492003102 0x54ea00ec81550250 0xfe000fc007000003 0x40fe00ff81c70000

def z422 : W := mkw 0xc9c8000000000002 0x20fadb6d9e000000 0xfe0f800000000001 0x20bfcfe7be000000

def z423 : W := mkw 0x01345555009a2682 0xd2c150a829d0d34c 0x000e7fff00ff3fcc 0x1281c0e039f0f3cc

def z424 : W := mkw 0x2000008010001000 0x502000c401040210 0xf000000000003e30 0x440000e400000230

def z425 : W := mkw 0xa0a35ef0d5d4942a 0xd8fbd9c433d79615 0xf1ffffc0fff8fe3f 0xffb9c8e47fcf8e3f

def z426 : W := mkw 0xfdc828a29a001903 0x24fefb7fde2d00b0 0xffff8000ff000033 0xe4fffffffe0f0030

def z427 : W := mkw 0x00007c38a4a40003 0x88cf550000f9b800 0x00007fff00ff0002 0x90c7f70001f0f000

def z428 : W := mkw 0x35247df69a923d83 0xd6ef50eea9fd92f4 0xfe0e7fffff003ff3 0x54ffc0ffb9ff03f0

def z429 : W := mkw 0x4948000000000000 0x20002239cc000000 0x0e00000000000000 0x0000001b80000000

def z430 : W := mkw 0x5374b45b28bb4ed5 0x820576136ca8f9ae 0xfffff03ff8ffffff 0xff47ff1ffe38ffff

def z431 : W := mkw 0xdbd8a00b28294a55 0x2014ff135e2869aa 0xfffff03ff8ffffff 0xff47ff1ffe38ffff

def z432 : W := mkw 0x0100000000000002 0x00daf93848000000 0x01fe000000000003 0xc0fffff878000000

def z433 : W := mkw 0x2000128050401000 0xd03188c401868610 0xf0007fc0fff8fe33 0xdcb9c8e401cf8e30

def z434 : W := mkw 0x80a3124041508428 0x8011880032828405 0x01ffffc0fff8c00f 0xbbb9c8007fcf8c0f

def z435 : W := mkw 0x0104451400822082 0x02c0502808501040 0x0000000000000000 0x0000000000000000

def z436 : W := mkw 0x00007e38e4e40003 0x88c5540000fbbc00 0x00007fffffffc002 0x98c1f00001fffc00

def z437 : W := mkw 0x1000200208000801 0x00040002002800a0 0x0e00003f000001c0 0x0046001b803001c0

def z438 : W := mkw 0xf6f3fbeffb79ff7f 0xd4ffaefff7ffefff 0xffffffffffffffff 0xffffffffffffffff

def z439 : W := mkw 0x20007eb8f4e41003 0xd8ffddc401ffbe10 0xf0007ffffffffe33 0xdcffffe401fffe30

def z440 : W := mkw 0x01341451009a0682 0x82c170386880d10c 0x01fe000000ff000e 0xc2c1f0f87800f00c

def z441 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xf1ff8fc007000003 0xe0b9c8e47fc70000

def z442 : W := mkw 0x01340041001a0680 0x020020106800410c 0x01fe00000000000c 0x020000007800000c

def z443 : W := mkw 0x0124555400922482 0xd2c150a829d09244 0x01fe7fc000f83e0e 0xd281c0e079c0820c

def z444 : W := mkw 0xa0a310c011109428 0xd02100c433848215 0xf1ffffc000f83e3e 0xf781c0e47fc0823f

def z445 : W := mkw 0x0124145000920480 0x8201500028809004 0x000e000000000000 0x0001c00038000000

def z446 : W := mkw 0x1210a00b28294a55 0x00040402002869aa 0x0000703ff8ffffff 0x9f463f000038ffff

def z447 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0xfff18000f8ffc03d 0xaf063f07c608fc3f

def z448 : W := mkw 0xf2e3b2ca7971dc7d 0xd0358ec737aeaeb7 0xffffffc0fff8fe3f 0xffbfcfe7ffcf8e3f

def z449 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0x00007fffff003ff0 0x14b800e001ff03f0

def z450 : W := mkw 0x34006dbebea43903 0x5cee55ee817d3af0 0xfe007fffff073ff3 0x54fe37ff81ff73f0

def z451 : W := mkw 0x34007db69a803903 0xd4ef50ee81fd92f0 0xfe007fffffff3ff3 0xd4fff0ff81fff3f0

def z452 : W := mkw 0x34007ba6da403903 0xd4ff88ee81ff86f0 0xfe007ffffff8fff3 0xdcffc8ff81ff8ff0

def z453 : W := mkw 0x0010200920280201 0x0004241040286908 0x01f0703ff8ffffcf 0xda463f184038ffcc

def z454 : W := mkw 0x340001861a003902 0x54ea00ee810402f0 0xfe00000000003ff3 0x44fe00ff800003f0

def z455 : W := mkw 0xb4836ba6db40b92b 0x54fe88ee937f06f1 0xfe01ffffff00fff3 0x7dfe08ff87ff0ff3

def z456 : W := mkw 0x350069a69a003903 0x54ee70fec97d02f0 0xfffe7fffff003ff3 0xd4fff0fff9ff03f0

def z457 : W := mkw 0x8988000000000000 0x2020006c9a000000 0x000e000000000000 0x000000e038000000

def z458 : W := mkw 0xe9eb12c051509428 0xf031aafdff868615 0xffffffc0fff8fe3f 0xffb9c8ffffcf8e3f

def z459 : W := mkw 0x5650e92faa296b57 0x04ce263bc47969ea 0x0e00003f000701c0 0x0046371b803071c0

def z460 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe00003f00003ff0 0x444600ff803003f0

def z461 : W := mkw 0x0000200820200001 0x0004040000282800 0x0000703ff8ffc000 0x180000000038fc00

def z462 : W := mkw 0xa083028051409028 0x0030884412060411 0xf1ff8000ff00c033 0xedb9c8e47e0f0c33

def z463 : W := mkw 0x0000120040400002 0x80dbd90000828400 0x00007fc0fff8c003 0x98ffff0001cf8c00

def z464 : W := mkw 0xc9c8682080000003 0x20fefb7dde790000 0xffffffffff000003 0xf0ffffffffff0000

def z465 : W := mkw 0x240049a492003102 0x54ea00ec81550250 0x00007fff07003fc2 0x50f800f801f703c0

def z466 : W := mkw 0xb4a37be6db50bd29 0xd43588c633ff86f5 0xf1fffffffff8ffff 0xffb9c8e47fff8fff

def z467 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xf1ff8fc007003e3c 0x67b9c0e47fc7023f

def z468 : W := mkw 0x8988000000000002 0x20fad96c9a000000 0xf1ff800000000003 0xe0b9c8e47e000000

def z469 : W := mkw 0x00007e38e4e40001 0x88158c0000fbbc00 0x00007fffffffc003 0x98b9c80001fffc00

def z470 : W := mkw 0xa0a302c051509428 0x503088c433060615 0xf1ff8000ff00fe3d 0x6f3808e47e0f0e3f

def z471 : W := mkw 0x7650ffbffeed7b57 0xdcffffffc5fffffa 0xfff1ffffffffffff 0xffffffffc7ffffff

def z472 : W := mkw 0xa0832aa8f5649029 0x083e8d44122f2c11 0xf0018000ff00c031 0x2d3e0f04060f0c33

def z473 : W := mkw 0x34007ebafee41903 0x8cffdd4680ffbcb0 0xfe007fffffffc033 0x9cffff0781fffc30

def z474 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0xfe01803ff807c1f1 0x2d463f1f86387df3

def z475 : W := mkw 0x20237ef8f5f49429 0xd805048021ffbe15 0x00007ffffffffe3c 0x1f00000001fffe3f

def z476 : W := mkw 0xf2f3fefbfdfdde7f 0xd8ffffd777ffffbf 0xffffffffffffffff 0xffffffffffffffff

def z477 : W := mkw 0xc9c8000000000000 0x2020227dde000000 0xffff800000000003 0xe0463ffffe000000

def z478 : W := mkw 0x0100000000000002 0x00c0502808000000 0x000e000000000000 0x0081c0e038000000

def z479 : W := mkw 0x01347d75809a2683 0xd2cf70b869f9d34c 0x01fe7fffffff3fcf 0xd2fff0f879fff3cc

def z480 : W := mkw 0x340069a69a003901 0x542400ee817d02f0 0xfe007fffff003ff0 0x540000ff81ff03f0

def z481 : W := mkw 0xddc869268a002903 0x24fefb7fde7900e0 0xffff803f000001c3 0xe0fffffffe3001c0

def z482 : W := mkw 0x0010000100080200 0x0000000000004108 0x0000703f00ff3fcc 0x120000000030f3cc

def z483 : W := mkw 0xa1a312c05150942a 0xd0f1f8fc7b868615 0xf1ffffc0fff8fe3f 0xfff9f8fc7fcf8e3f

def z484 : W := mkw 0x0000361864e40001 0x8815dd0000aabc00 0x0000703ff8ffc003 0x9847ff000038fc00

def z485 : W := mkw 0x0000682080000003 0x00ee006c80790000 0xfe007fffff000003 0x50fe00ff81ff0000

def z486 : W := mkw 0xdbfcf55f28bb6ed7 0xf2fffffffff8fbee 0xfffffffff8ffffff 0xfffffffffff8ffff

def z487 : W := mkw 0x0000000000000002 0x00c0002800000000 0x0000000000000002 0x40c000f800000000

def z488 : W := mkw 0x5270b04b28394e55 0xd005269365a8ebae 0xfffffffff8ffffff 0xffc7fffffff8ffff

def z489 : W := mkw 0x01245f74c4d62482 0xdadbd9a829d39644 0x000e0fc007000000 0x00b9c0e039c70000

def z490 : W := mkw 0x00345555009a2682 0xd2c1508021d0d34c 0x00007fff00ff3fce 0x92c1f00001f0f3cc

def z491 : W := mkw 0x0020104000100400 0x8001000020808004 0x01fe000000f8000c 0x8201c0007800800c

def z492 : W := mkw 0x340069a69a003901 0x542e00c6817d02f0 0xfe007fffff003ff1 0x143e000781ff03f0

def z493 : W := mkw 0xa0a316d875f49428 0xd831ddc43386be15 0xf1ffffc0fffffe3f 0xffb9ffe47fcffe3f

def z494 : W := mkw 0x0000041824a40000 0x0800550000003800 0x0000000000070000 0x0000370000007000

def z495 : W := mkw 0xa0a37ae0d150942b 0xd0ff88c433ff8615 0xf1fffffffff8fe3f 0xffffc8e47fff8e3f

def z496 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0x0e00703ff8fffffc 0x1f46371b8038ffff

def z497 : W := mkw 0x497c5555009a2682 0xf2cb73b9edd0d34c 0x0ffe7fff00ff3fce 0xd2c7f7fbf9f0f3cc

def z498 : W := mkw 0x0000482080000002 0x00ca000000510000 0x00000fc007000000 0x00b8000001c70000

def z499 : W := mkw 0xe9c8008010001002 0x70fafbfddf040210 0xffffffc0ff003e33 0xf4ffffffffcf0230

def z500 : W := mkw 0x00000a20c4440000 0x081a890000030400 0x0000000007000000 0x0038000000070000

def z501 : W := mkw 0x01345555009a2680 0xd20120b869d0d34c 0x01fe7fff00ff3fcc 0x520000f879f0f3cc

def z502 : W := mkw 0x00007f3ce4e42003 0xd8dfdda801fbbe40 0x00007fffffffffc3 0xd8fffff801ffffc0

def z503 : W := mkw 0xc9fc0145001a2680 0x722022fdff00434c 0xffff800000003fcc 0x620000fffe0003cc

def z504 : W := mkw 0x2000008010001000 0x502000c401040210 0xf1f1ffc0fff8fe3f 0xffb808e447cf8e3f

def z505 : W := mkw 0x00347f7de4fe2681 0xda05048021fbff4c 0x00007fffffffffcc 0x1a00000001ffffcc

def z506 : W := mkw 0x89885e30c4c40002 0xa8fbd96c9ad39400 0x000e0fc007000000 0x00b9c0e039c70000

def z507 : W := mkw 0x0000161864e40002 0x88dbdd000082bc00 0x0000000000ffc003 0x88ffff000000fc00

def z508 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x000e0fff000701c0 0x00c1f0f839f071c0

def z509 : W := mkw 0x5240a00a28214855 0x00040603042828a2 0xfe01f03ff8ffc033 0xbd463f078638fc33

def z510 : W := mkw 0xc9fc0145001a2682 0x72fafbfdff00434c 0xffff800000003fcf 0xe2fffffffe0003cc

def z511 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0x0e00703ff8ffc1c3 0x98463f1b8038fdc0

def z512 : W := mkw 0x0100541000800002 0x80c1703848d09000 0x01fe7fff00ff0002 0xd0c1f0f879f0f000

def z513 : W := mkw 0xfdc801861a003900 0x742022ffdf0402f0 0xffff800000003ff0 0x640000fffe0003f0

def z514 : W := mkw 0x5d4869268a002903 0x24ce733bcc7900e0 0x0e00003f000001c0 0x0046371b803001c0

def z515 : W := mkw 0x89887e38e4e40003 0xa8ffdd6c9afbbc00 0x000e7fffffffc003 0x98ffffe039fffc00

def z516 : W := mkw 0xfdc801861a003902 0x74fafbffdf0402f0 0xffff800000003ff3 0xe4fffffffe0003f0

def z517 : W := mkw 0x0000000000000002 0x00ca510000000000 0x0000000000000000 0x0046370000000000

def z518 : W := mkw 0x1000200208000801 0x00040002002800a0 0xfe000000f8000031 0x0406000780080030

def z519 : W := mkw 0x00006c38a4a40001 0x0804040000793800 0x0000003f00070000 0x0000000000307000

def z520 : W := mkw 0x00005e30c4c40002 0x88dbd90000d39400 0x00000fc007000003 0x80ffff0001c70000

def z521 : W := mkw 0xc9c8000000000002 0x20ea737dde000000 0xffff800000000000 0x604637fffe000000

def z522 : W := mkw 0x202300c011109428 0x5000008021040215 0x0000000000003e3c 0x070000000000023f

def z523 : W := mkw 0x8180000000000002 0x00f0f87c5a000000 0xf1ff800000000003 0xe0f9f8fc7e000000

def z524 : W := mkw 0x01146d3da4ae2283 0x0ace753848797948 0x0000003f000701c0 0x00463718003071c0

def z525 : W := mkw 0x340049a69a003902 0x54ea00ee815502f0 0xfe000fc007003ff0 0x44b800ff81c703f0

def z526 : W := mkw 0x4040000000000000 0x0000221144000000 0xfff1800000000000 0x6000001fc6000000

def z527 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0xfff1803f00073ffc 0x6746371fc63073ff

def z528 : W := mkw 0xc9c8000000000000 0x203aab7dde000000 0xffff800000000001 0x603e0ffffe000000

def z529 : W := mkw 0xb4a37ffefff4bd2b 0xdcffddeeb3ffbef5 0xffffffffffffffff 0xffffffffffffffff

def z530 : W := mkw 0x0134755d20ba2683 0xd2c574b869f8fb4c 0x01fe7ffff8ffffcf 0xdac7fff879f8ffcc

def z531 : W := mkw 0x7640a8aaba215955 0x042e0647842d28b2 0xfe018000ff00c031 0x2d3e0f07860f0c33

def z532 : W := mkw 0x5b58a00b28294a57 0x20ce773bcc2869aa 0x0e00003f000701c0 0x0046371b803071c0

def z533 : W := mkw 0x5250fe3beced4a55 0x8805261344fbfdaa 0xfff1ffffffffffff 0xff463f1fc7ffffff

def z534 : W := mkw 0x4374945920bb46d4 0x820176116c80f90e 0x01ff800000ffc00c 0xab01ff007e00fc0f

def z535 : W := mkw 0x20237ef8f5f4942b 0xd8dfdd8021ffbe15 0x00007ffffffffe3f 0x9fffff0001fffe3f

def z536 : W := mkw 0x340068a29a001903 0x04ee0046807d00b0 0xfe007fffff000033 0x14fe000781ff0030

def z537 : W := mkw 0x80a0104000100400 0xd03188c433808204 0xf1ffffc000f83e0f 0xf2b9c8e47fc0820c

def z538 : W := mkw 0x5250800308094a54 0x00002213440041aa 0xfff1f03f00ff3ffe 0xf740301fc630f3ff

def z539 : W := mkw 0x0100000000000000 0x0000203848000000 0x01fe000000000000 0x400000f878000000

def z540 : W := mkw 0x0000161044c40000 0x8811d90000829400 0x0000000000000000 0x0001c00000000000

def z541 : W := mkw 0x0000000000000000 0x001a890000000000 0x0000000000000001 0x003e0f0000000000

def z542 : W := mkw 0x4040000000000000 0x0000020104000000 0xfe01800000000001 0x20060f0786000000

def z543 : W := mkw 0x0000410400002002 0x50ea00ec81500240 0xfe007fff00003fc3 0x50fe00ff81f003c0

def z544 : W := mkw 0x240049a492003102 0x54ea00ec81550250 0xf0007fc0ff003e33 0x54b800e401cf0230

def z545 : W := mkw 0x340029a69a003901 0x542e00ee812d02f0 0xfe000000ff003ff1 0x443e00ff800f03f0

def z546 : W := mkw 0x0000682080000003 0x00ce000000790000 0x0000003f00000000 0x0046000000300000

def z547 : W := mkw 0x4374d55d20bb66d6 0xd2c176b96dd0fb4e 0x01ffffff00ffffce 0xfbc1fff87ff0ffcf

def z548 : W := mkw 0x5250a00308094a55 0x00042213442841aa 0xfff1f03ff8003fff 0x7746001fc63803ff

def z549 : W := mkw 0x0000282080000001 0x000e000000290000 0x00000000ff000001 0x003e0000000f0000

def z550 : W := mkw 0xc9c8410400002002 0x70fafbfddf500240 0xffffffff00003fc3 0xf0fffffffff003c0

def z551 : W := mkw 0x203757d551dab6a8 0xd201008021d6d75d 0x00007ffffffffffc 0x1f00000001ffffff

def z552 : W := mkw 0x01347d7da4be2683 0xdacf75b869f9fb4c 0x01fe7fff00ff3fce 0xd2c7f7f879f0f3cc

def z553 : W := mkw 0x81b45555009a2682 0xd2f1f8fc7bd0d34c 0xf1ffffff00ff3fcf 0xf2f9f8fc7ff0f3cc

def z554 : W := mkw 0x01340145001a2682 0x52c070b86900434c 0x01fe000000003fce 0xc2c1f0f8780003cc

def z555 : W := mkw 0x00341451009a0680 0x820100002080d10c 0x0000000000ff000c 0x020000000000f00c

def z556 : W := mkw 0x1000200208000801 0x00040002002800a0 0x0000703ff8003ff0 0x14000000003803f0

def z557 : W := mkw 0x4040000000000000 0x0000221144000000 0xfff1f000f8f8fe3f 0xff463f1fc6088e3f

def z558 : W := mkw 0x8080000000000000 0x0030884412000000 0xf1fff000f8f8fe3f 0xffb9c8e47e088e3f

def z559 : W := mkw 0xc9c8161864e40000 0xa811ff115e82bc00 0x01ff800000ffc000 0xa801ff007e00fc00

def z560 : W := mkw 0xa0a332c871709429 0xd0358cc433aeae15 0xf1fffffffffffe3f 0xffffffe47ffffe3f

def z561 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0x01f1f03ff8fffffc 0xbf003f004638ffff

def z562 : W := mkw 0x35347df79a9a3f83 0xd6c570ba69fdd3fc 0x01fe7fffffff3ffe 0xd6c1f0f879fff3fc

def z563 : W := mkw 0x5250ec3bacad4a57 0x08ce7713447979aa 0x0e00003f000701c0 0x0046371b803071c0

def z564 : W := mkw 0x0000000000000000 0x0010880000000000 0x0000000000000003 0x80b9c80000000000

def z565 : W := mkw 0x213455d5109a3682 0xd2e170fc69d4d35c 0xf1fe7fffffff3fff 0xd6f9f0fc79fff3fc

def z566 : W := mkw 0x15347d778a9a2f83 0xd6cf70bae9f9d3ec 0x0ffe7fff00ff3fce 0xd2c7f0fbf9f0f3cc

def z567 : W := mkw 0x0000000000000000 0x0000000000000000 0x00007000f8f8c003 0x9800080000088c00

def z568 : W := mkw 0x00007e38e4e40003 0x88cf550000fbbc00 0x00007fffffffc000 0x1846370001fffc00

def z569 : W := mkw 0xc9e8104000100402 0xf0fbfbfdff808204 0xffffffc000f83e0f 0xf2ffffffffc0820c

def z570 : W := mkw 0x01147f3de4ee2283 0x8adffd3848fbfd48 0x00007fffffffc1c3 0x98ffff1801fffdc0

def z571 : W := mkw 0xc9c8000000000000 0x2030fb7dde000000 0xffff800000000000 0xe001fffffe000000

def z572 : W := mkw 0x2400018412003100 0x542000ec81040250 0x0000000000000000 0x000000e000000000

def z573 : W := mkw 0xc9ec555400922482 0xf2fbfbfdffd09244 0xffff8fc000000003 0xe0ffffffffc00000

def z574 : W := mkw 0x8083020041408028 0x0010880012020401 0x000180000000c000 0x2900080006000c03

def z575 : W := mkw 0xa083028051409028 0x0030884412060411 0x0000000007000000 0x0038000000070000

def z576 : W := mkw 0x7650e9afba297b57 0x54ee26ffc57d6bfa 0xfe007fffff073ff3 0x54fe37ff81ff73f0

def z577 : W := mkw 0xb48069a69a003903 0x54fe88ee937d02f0 0xffffffffff003ff3 0xf4ffc8ffffff03f0

def z578 : W := mkw 0x24007fbcf6e43103 0xdcffddec81ffbe50 0x00007fffffffc003 0x98ffffe001fffc00

def z579 : W := mkw 0xd2d0a00b28294a55 0x0034ae57562869aa 0xfffff03ff8ffffff 0xfffffffffe38ffff

def z580 : W := mkw 0xf2f3a0cb3939de7d 0x502426d7772c6bbf 0xfffff03ff8ffffff 0xff463ffffe38ffff

def z581 : W := mkw 0x0000561864e40002 0x88d1dd0000d2bc00 0x00007fff00ffc002 0x98c1ff0001f0fc00

def z582 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xf1ff800000f8fe3c 0xef01c8e47e008e3f

def z583 : W := mkw 0x01247f7ce4f62483 0xdadfdda829fbbe44 0x000e7fffffffc003 0x98ffffe039fffc00

def z584 : W := mkw 0xe0e312c051509428 0xd031aad577868615 0xffffffc0fff8fe3f 0xffffffffffcf8e3f

def z585 : W := mkw 0x80a3165865f48428 0x8811dd003282bc05 0x01ff800000ffc00c 0xab01ff007e00fc0f

def z586 : W := mkw 0xfdc869a69a003903 0x74ee22ffdf7d02f0 0xffffffffff003ff3 0x74fe00ffffff03f0

def z587 : W := mkw 0x5250f41b28a94a57 0x80c5761344f8f9aa 0xfff1fffff8ffffff 0xffc7ff1fc7f8ffff

def z588 : W := mkw 0x53748147081b6ed4 0x520022bb6d0043ee 0xffff800000003ffc 0x670000fffe0003ff

def z589 : W := mkw 0x340028a29a001903 0x04ee006e802d00b0 0xfe000000ff000033 0x44fe00ff800f0030

def z590 : W := mkw 0x1000200208000803 0x00ee006e802800a0 0xfe00703ff8003ff3 0x54fe00ff803803f0

def z591 : W := mkw 0x00007e38e4e40001 0x881f8d0000fbbc00 0x00007fffffffc001 0x183e0f0001fffc00

def z592 : W := mkw 0x4948000000000000 0x200073114c000000 0x0000000000000000 0x0000370000000000

def z593 : W := mkw 0x25245df492923582 0xd6eb50eca9d59254 0x000e0fc007000000 0x00b9c0e039c70000

def z594 : W := mkw 0xc9fc7f7de4fe2683 0xfafffffdfffbff4c 0xffffffffffffffcf 0xfaffffffffffffcc

def z595 : W := mkw 0xc9c8161864e40002 0xa8fbff7dde82bc00 0xffff800000ffc003 0xe8fffffffe00fc00

def z596 : W := mkw 0xa0a300c011109428 0x502000c433040215 0xf1fff000f8f8fe3f 0xff0008e47e088e3f

def z597 : W := mkw 0x0000000000000002 0x00ea006c80000000 0x0000000000000000 0x00b800e000000000

def z598 : W := mkw 0x202312c051509428 0xd02100c421868615 0xf0007fc0fff8fe3f 0x5fb800e401cf8e3f

def z599 : W := mkw 0x5374a14f283b6ed5 0x520426bb6d286bee 0xfffff03ff8ffffff 0xff463ffffe38ffff

def z600 : W := mkw 0x0000551400802002 0xd0c150a801d09240 0x00007fff00ff3fc2 0xd0c1f0f801f0f3c0

def z601 : W := mkw 0x8080000000000002 0x00fad94412000000 0xf1ff800000000003 0xe0ffffe47e000000

def z602 : W := mkw 0xfdc87fbefee43903 0xfcffffffdfffbef0 0xfffffffffffffff3 0xfcfffffffffffff0

def z603 : W := mkw 0x340069a69a003903 0x54c400aa017d02f0 0x00007fffff003ff2 0x54c000f801ff03f0

def z604 : W := mkw 0x34007fb6dec43903 0xdcffd9ee81ff96f0 0xfe007fffff003ff3 0x54ffc0ff81ff03f0

def z605 : W := mkw 0x0000000000000000 0x0020004400000000 0xf000000000000003 0x40b800e400000000

def z606 : W := mkw 0xc9c8200820200003 0x20feff7dde282800 0xfffff03ff8ffc003 0xf8fffffffe38fc00

def z607 : W := mkw 0x0100000000000002 0x00ea707cc8000000 0xfffe000000000003 0xc0fff0fff8000000

def z608 : W := mkw 0x80a3124041508428 0x8011880032828405 0xf1fff000f8f8fe3f 0xff01c8047e088e3f

def z609 : W := mkw 0xa4a35be4d350b52a 0xd4fb88ecb3d78655 0x000e0fc007000000 0x00b9c0e039c70000

def z610 : W := mkw 0x5250800308094a54 0x00002213440041aa 0x0e000000000001c0 0x0000001b800001c0

def z611 : W := mkw 0x353401c71a1a3f80 0x562020fee90443fc 0xfffe000000003ffc 0x460000fff80003fc

def z612 : W := mkw 0x0000000000000000 0x0000201040000000 0x01f0000000000002 0xc040301840000000

def z613 : W := mkw 0x340069a69a003903 0x54ce0082017d02f0 0x00007fffff003ff3 0x14fe000001ff03f0

def z614 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00000fc0ff00c001 0x08bfcf0001cf0c00

def z615 : W := mkw 0x0134575540da2682 0xd2d1f8b869d2d74c 0x01fe7fffffffffcf 0xdaf9f8f879ffffcc

def z616 : W := mkw 0xa0b757d551dab6a8 0xd23188c433d6d75d 0xf1ffffffffffffff 0xffb9c8e47fffffff

def z617 : W := mkw 0xfbfbb2cb7979de7f 0xf0ffffffffaeefbf 0xffffffffffffffff 0xffffffffffffffff

def z618 : W := mkw 0x0000000820200000 0x0000040000002800 0x0000000000ffc000 0x88003f000000fc00

def z619 : W := mkw 0x81b7165141da86a8 0x8211f8107a82d50d 0x01ff800000ffc00c 0xab01f8007e00fc0f

def z620 : W := mkw 0x1210a00b28294a55 0x00040402002869aa 0x0000003f000701c0 0x00000000003071c0

def z621 : W := mkw 0xa083008011009028 0x0020004412040011 0xf001800000000030 0x2500000406000033

def z622 : W := mkw 0x0000682080000001 0x0004000000790000 0x00007fffff000000 0x1000000001ff0000

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0018000f800c031 0x2d00080406080c33

def z624 : W := mkw 0x5240a00a28214855 0x00042613442828a2 0xfff18000f800c033 0xed463f1fc6080c33

def z625 : W := mkw 0x0100410400002002 0x50c070b849500240 0x01fe7fff00003fc2 0xd0c1f0f879f003c0

def z626 : W := mkw 0x0000741820a00003 0x80c5540000f8b800 0x00007ffff8ffc003 0x98c7ff0001f8fc00

def z627 : W := mkw 0x4948000000000002 0x20ea737dcc000000 0xfe00000000000003 0x40fe37ff80000000

def z628 : W := mkw 0xc9fc5555009a2682 0xf2d1fbb97fd0d34c 0x01ffffff00ff3fce 0xf2c1fff87ff0f3cc

def z629 : W := mkw 0x5250e82ba8294a57 0x00ce2613447969aa 0xfff1ffffffffffff 0xfffe3f1fc7ffffff

def z630 : W := mkw 0xa0a312c051509428 0x8031884432868415 0xf1ff8000fff8c03d 0xaf39c8047e0f8c3f

def z631 : W := mkw 0x00003a28e4640001 0x881f8d0000abac00 0x00007fc0fff8c003 0x98bfcf0001cf8c00

def z632 : W := mkw 0xb2b3b2cb7979de7d 0xd0358cc633aeefbf 0xf1ffffffffffffff 0xffb9c8e47fffffff

def z633 : W := mkw 0x0000200000000001 0x0004000000280000 0x0000703ff8000003 0x1046000000380000

def z634 : W := mkw 0x7d4869a69a003903 0x74ee73ffcd7d02f0 0xfe007fffff003ff3 0x54fe37ff81ff03f0

def z635 : W := mkw 0x1000000208000800 0x00000002000000a0 0xfe00000000003ff0 0x4400001f800003f0

def z636 : W := mkw 0x00007a20c0400003 0x80df880000fb8400 0x00007ffffff8c003 0x98ffc80001ff8c00

def z637 : W := mkw 0xc9c87e38e4e40003 0xa8dfff115efbbc00 0x01ffffffffffc003 0xb8ffff007ffffc00

def z638 : W := mkw 0x01344145001a2682 0x52c020b86950434c 0x01fe7fff00003fce 0x52c000f879f003cc

def z639 : W := mkw 0x01345f75c4de2682 0xdadbf9b869d3d74c 0x01fe7fff07ff3fce 0xd2f9f0f879f7f3cc

def z640 : W := mkw 0x1000200208000801 0x00040002002800a0 0xfff1f03ff8f8ffff 0xff46081fc6388fff

def z641 : W := mkw 0x0124555400922482 0xd2c150a829d09244 0x000e7fff00003fc2 0x50c1c0f839f003c0

def z642 : W := mkw 0x5240a00a28214855 0x00040603042828a2 0x0e00000000000000 0x0006070380000000

def z643 : W := mkw 0xe9ff57d551dab6aa 0xf2fbfbfdffd6d75d 0xffffffffffffffff 0xffffffffffffffff

def z644 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0xfe00703ff8073ff3 0x5446371f803873f0

def z645 : W := mkw 0x5374ff7fecff6ed7 0xdadfffbb6dfbffee 0xffffffffffffffff 0xffffffffffffffff

def z646 : W := mkw 0x1010200308080a01 0x00042012402841a8 0xfff0703ff8ff3fff 0xd646301fc038f3fc

def z647 : W := mkw 0x340069a69a003901 0x54040082017d02f0 0xfe007fffff003ff3 0x5446001f81ff03f0

def z648 : W := mkw 0x0000200820200003 0x00dedd0000282800 0x0000703ff8ffc003 0x98ffff000038fc00

def z649 : W := mkw 0x4250800100094254 0x000022114400410a 0x01f180000000000c 0x230000004600000f

def z650 : W := mkw 0x7650e9a79a097b57 0x54ee22ffc57d43fa 0xfff1ffffff003fff 0x77fe00ffc7ff03ff

def z651 : W := mkw 0x8988000000000002 0x20faf97cda000000 0x01fe000000000002 0xc0f9f0f878000000

def z652 : W := mkw 0x4948000000000002 0x20ca7339cc000000 0xfff1800000000003 0xe0463f1fc6000000

def z653 : W := mkw 0x0000000000000002 0x00ca000000000000 0x0000000000000003 0x00fe000000000000

def z654 : W := mkw 0xc8c8000000000000 0x20108b0116000000 0x0001800000000000 0x20000f0006000000

def z655 : W := mkw 0x49487e38e4e40003 0xa8dfff39ccfbbc00 0x0e007fffffffc003 0x98ffff1b81fffc00

def z656 : W := mkw 0x0000541000800000 0x8001000000d09000 0x00007fff00ff0000 0x1000000001f0f000

def z657 : W := mkw 0x0000000000000000 0x0020006c80000000 0xfe00000000000000 0x400000ff80000000

def z658 : W := mkw 0x00006a28e4640003 0x08de8d00007b2c00 0x00007fffff00c003 0x18fe0f0001ff0c00

def z659 : W := mkw 0x00107e39e4ec0203 0x88dffd1040fbfd08 0x01f07fffffffffcf 0xdaffff1841ffffcc

def z660 : W := mkw 0x5240aa2aec654855 0x081e8f03042b2ca2 0xfe018000ff00c031 0x2d3e0f07860f0c33

def z661 : W := mkw 0x00005e30c4c40002 0x88dbd90000d39400 0x00007fff07ff0002 0x90f9f00001f7f000

def z662 : W := mkw 0x0000000000000000 0x5000008001000200 0x00007fc000003e02 0x508000e001c00200

def z663 : W := mkw 0x0024555400922480 0xd201008021d09244 0x00000fc000000000 0x0000000001c00000

def z664 : W := mkw 0x0000682080000003 0x00ded90000790000 0x00007fffff000003 0x90ffff0001ff0000

def z665 : W := mkw 0x80807e38e4e40003 0x88ffdd4412fbbc00 0xf1ffffffffffc003 0xf8ffffe47ffffc00

def z666 : W := mkw 0xe9eb00c011109428 0x702022fdff040215 0xffff800000003e3c 0x670000fffe00023f

def z667 : W := mkw 0x00340145001a2680 0x520000802100434c 0x0000000000003fcc 0x02000000000003cc

def z668 : W := mkw 0x340028a29a001901 0x042e0046802d00b0 0xfe00703fff003ff3 0x547e001f803f03f0

def z669 : W := mkw 0x0134165964fe0680 0x8a11fd106882fd0c 0x01fe000000ffc00c 0x8a01ff007800fc0c

def z670 : W := mkw 0x0124555400922482 0xd2c150a829d09244 0x000e7fff00ff0002 0x90c1f0e039f0f000

def z671 : W := mkw 0xe9eb00c01110942a 0x70fafbfdff040215 0xffff800000003e3f 0xe7fffffffe00023f

def z672 : W := mkw 0x5250800308094a54 0x00002213440041aa 0xfff1800000003fff 0xe7463f1fc60003ff

def z673 : W := mkw 0x140069268a002901 0x04040002007900e0 0x0000003f000001c0 0x00000000003001c0

def z674 : W := mkw 0xc8c8000000000002 0x20fa8b6d96000000 0xfe01800000000003 0x60fe0fff86000000

def z675 : W := mkw 0x0000692480002003 0x50ce00a801790240 0x00007fffff003fc3 0x50fe00f801ff03c0

def z676 : W := mkw 0x2000008010001000 0x0020004400040010 0xf0000000ff000031 0x04380004000f0030

def z677 : W := mkw 0x140028228a000901 0x040e0002802900a0 0x0e00000000000000 0x0006000380000000

def z678 : W := mkw 0x00207e78e4f40403 0xd8dfdd8021fbbe04 0x01fe7ffffffffe0f 0xdaffffe079fffe0c

def z679 : W := mkw 0x140069268a002903 0x04ce002a807900e0 0xfe00703ff8003ff3 0x5446001f803803f0

def z680 : W := mkw 0xcbd8800920294254 0x2010ff115e00690a 0x01ff800000ffc00c 0xab01ff007e00fc0f

def z681 : W := mkw 0x202312c051509428 0xd011888021868615 0x00007fc0fff8fe3f 0x9fb9c80001cf8e3f

def z682 : W := mkw 0x202312c051509428 0xd001008021868615 0x00000fc007000000 0x0000000001c70000

def z683 : W := mkw 0xc8c82a28e4640001 0x283e8f45962b2c00 0xfe018000ff00c001 0x283e0f07860f0c00

def z684 : W := mkw 0x0000410400002000 0x5000008001500240 0x00007fff00003fc0 0x1000000001f003c0

def z685 : W := mkw 0x0010000100080200 0x0000201040004108 0xf1f1f03ff8ffffff 0xff40381c4638ffff

def z686 : W := mkw 0x5250b61b6ced4a55 0x8815ff1344aafdaa 0xfff1f03ff8ffffff 0xff47ff1fc638ffff

def z687 : W := mkw 0xb4a313c65b50bd28 0xd43188eeb38686f5 0xffffffc0fff8ffff 0xffb9c8ffffcf8fff

def z688 : W := mkw 0xa0837eb8f5e4902b 0x88ffdd4412ffbc11 0xf001ffffffffc033 0xbdffff0407fffc33

def z689 : W := mkw 0x89bc5555009a2682 0xf2fbf9fcfbd0d34c 0x01fe7fff00ff3fce 0xd2f9f0f879f0f3cc

def z690 : W := mkw 0x0000541000800002 0x80c1500000d09000 0x00000fc000000000 0x0081c00001c00000

def z691 : W := mkw 0x35347ffffefe3f83 0xdefffdfee9fffffc 0xfffe7fffffffffff 0xdefffffff9fffffc

def z692 : W := mkw 0x0000200820200001 0x0004040000282800 0x0000003f00070000 0x0046370000307000

def z693 : W := mkw 0xc8c87e38e4e40003 0xa8ffdf4596fbbc00 0xfe01ffffffffc003 0xb8ffff0787fffc00

def z694 : W := mkw 0x01345555009a2682 0xd2eb70fce9d0d34c 0xfffe7fff00ff3fcf 0xd2fff0fff9f0f3cc

def z695 : W := mkw 0x00002828a4240001 0x080e050000292800 0x0000000000000000 0x0006070000000000

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000703f00003fc2 0x50400018003003c0

def z697 : W := mkw 0x01144515008a2282 0x52c070b849505348 0x00007fff00073fc2 0x50c030f801f073c0

def z698 : W := mkw 0x0134575d64fe2682 0xdad1fdb869d2ff4c 0x01fe7fff00ffffce 0xdac1fff879f0ffcc

def z699 : W := mkw 0x0020514400102402 0xd0c100a821d08244 0x01fe7fff00f83fce 0xd2c1c0f879f083cc

def z700 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0xfff1f03ff8fffffc 0x7f00001fc638ffff

def z701 : W := mkw 0xa0a312c05150942a 0xd0fbd9c433868615 0xf1ffffc0fff8fe3f 0xffffffe47fcf8e3f

def z702 : W := mkw 0xa083028051409028 0x503088c413060611 0xf001ffc0ff00fe33 0x7db808e407cf0e33

def z703 : W := mkw 0x2000008010001000 0x5000008001040210 0x00007fc0ff003e30 0x1400000001cf0230

def z704 : W := mkw 0x00002a28e4640001 0x08040400002b2c00 0x00000000ff00c000 0x08000000000f0c00

def z705 : W := mkw 0x1210a00b28294a55 0x00042412402869aa 0x01f0703ff8fffffe 0xdf4030184038ffff

def z706 : W := mkw 0xb4a37be6db50bd2b 0xd4ff88eeb3ff86f5 0xfe0e7fffff003ff3 0x54ffc0ffb9ff03f0

def z707 : W := mkw 0x5250e82388094a57 0x00ce2213447941aa 0xfff1ffffff003fff 0x77fe001fc7ff03ff

def z708 : W := mkw 0xc0c0000000000002 0x00faaa7dd6000000 0xffff800000000003 0xe0fffffffe000000

def z709 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe007fffff003ff3 0xd4fe3fff81ff03f0

def z710 : W := mkw 0xf2f3b2cb7979de7d 0xd035aed777aeefbf 0x0e0e0fff070701c0 0x00fff7fbb9f771c0

def z711 : W := mkw 0x340069a69a003903 0x54ee50ee817d02f0 0xfe007fffff003ff3 0xd4fff0ff81ff03f0

def z712 : W := mkw 0x342369e69b10bd2b 0x54ee00eea17d02f5 0xfe007fffff003fff 0x57fe00ff81ff03ff

def z713 : W := mkw 0x01342b6de47e2681 0x5a1eadb8692b6f4c 0x01fe0000ff00ffcd 0x4a3e0ff8780f0fcc

def z714 : W := mkw 0x340049a69a003902 0x54ea00ee815502f0 0xfe007fc0ff003ff3 0x54b800ff81cf03f0

def z715 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00007fffffffffc3 0xd8ffff1801ffffc0

def z716 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0xfffe7fff00ff3fcf 0xd2c7f0fff9f0f3cc

def z717 : W := mkw 0x340041861a003902 0x54e000ee815402f0 0xfe007fffff003ff3 0x54f800ff81ff03f0

def z718 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0xfff1803f00fffffc 0xef463f1fc630ffff

def z719 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x000e7fff00ff01c2 0x90c1f0f839f0f1c0

def z720 : W := mkw 0xf2c3aaaafd65d87d 0x083e8f47162f2cb3 0xfe018000ff00c031 0x2d3e0f07860f0c33

def z721 : W := mkw 0x340049a69a003902 0x54ea00ee815502f0 0xfe000fc007003ff3 0x44fe00ff81c703f0

def z722 : W := mkw 0x01345555009a2680 0xd20170b869d0d34c 0x01fe7fff00ff3fcc 0xd201f0f879f0f3cc

def z723 : W := mkw 0x340028a29a001901 0x542e00c6812d02b0 0xfe007fffff003ff3 0x54fe00ff81ff03f0

def z724 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xffff800000000000 0xe047fffffe000000

def z725 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xf1ffffc0fff8fe3c 0x7fb9c0e47fcf8e3f

def z726 : W := mkw 0x00003e38e4e40001 0x881fdd0000abbc00 0x00007fc0ffffc003 0x98bfff0001cffc00

def z727 : W := mkw 0x5f58e92faa296b57 0x24ce773bcc7969ea 0x0e00003f000701c0 0x0046371b803071c0

def z728 : W := mkw 0x0137575541daa6aa 0xd2c170b869d2d74d 0x01fe7fff00ffffce 0xdbc1f0f879f0ffcf

def z729 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xf1ff8fc0ff00fe3d 0x6fb9c8e47fcf0e3f

def z730 : W := mkw 0xfec8a8aaba215955 0x243e8f47962d28b2 0xfe018000ff00c031 0x2d3e0f07860f0c33

def z731 : W := mkw 0x696b12c05150942a 0xf0cb73b9ed868615 0x0e007fc0fff8fe3c 0x1f46371b81cf8e3f

def z732 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0x0e0e000000000003 0x80fffffbb8000000

def z733 : W := mkw 0x01345555009a2682 0xd2cb71b869d0d34c 0x01fe7fff00ff3fce 0xd2c7f7f879f0f3cc

def z734 : W := mkw 0x0124555400922482 0xd2c150a829d09244 0x000e7fff00ff3fc2 0xd0c1f0f839f0f3c0

def z735 : W := mkw 0xc9d8000100080202 0x20fafb7dde004108 0xffff800000ff000f 0xe2fffffffe00f00c

def z736 : W := mkw 0x90a3324249508c29 0x8015880232aa84a5 0xfffff03ff8f8ffff 0xff47c81ffe388fff

def z737 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00007fffffffc000 0x98b9ff0001fffc00

def z738 : W := mkw 0xb4832aaaff649929 0x0c3e8d46922f2cb1 0xfe018000ff00c031 0x2d3e0f07860f0c33

def z739 : W := mkw 0xc9c8000000000002 0x20dafb39de000000 0x0fff800000000002 0xe0c7fffbfe000000

def z740 : W := mkw 0x05345d75829a2782 0xd6cb70b8e9d1d34c 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z741 : W := mkw 0xcbd8961964ed4254 0xa811ff115e82fd0a 0x01ff800000ffc00c 0xab01ff007e00fc0f

def z742 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00000fc0ffffc001 0x88bfff0001cffc00

def z743 : W := mkw 0x3d0869a69a003903 0x74ee51ee897d02f0 0xfe007fffff003ff3 0x54fe00ff81ff03f0

def z744 : W := mkw 0xc9c8482080000002 0x20fafb7dde510000 0xffff8fc007000003 0xe0ffffffffc70000

def z745 : W := mkw 0x14007f3eeee42903 0x8cdfdd2a80fbbce0 0x0e00003f00ffc1c0 0x8847ff1b8030fdc0

def z746 : W := mkw 0x80807e38e4e40003 0x88dfdd0012fbbc00 0x01ffffffffffc003 0xb8ffff007ffffc00

def z747 : W := mkw 0x340069a69a003903 0x54ce00aa817d02f0 0x0e007fffff003ff3 0x14fe001b81ff03f0

def z748 : W := mkw 0xc9c8000000000000 0x203afb55de000000 0xffff800000000003 0xe0bfffe7fe000000

def z749 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00000fff07070003 0x80ffff0001f77000

def z750 : W := mkw 0xa0a36cf8b5b4942b 0x58ee55c4337d3a15 0xf1ff803f00073e3c 0x674637e47e30723f

def z751 : W := mkw 0xedc808a092001102 0x24fafb7dde050010 0xffff800007000003 0xe0fffffffe070000

def z752 : W := mkw 0x5364f55e28b36cd7 0xd2c556ab2df8bae6 0xfe0f8fc0f800c031 0x2d87cfe7bfc80c33

def z753 : W := mkw 0x4050000100080200 0x0000221144004108 0xfff1f03ff8ffffff 0xff463f1fc638ffff

def z754 : W := mkw 0x00005e38e4e40002 0x88dbdd0000d3bc00 0x00000fc007070000 0x00b9f70001c77000

def z755 : W := mkw 0xc8c8000000000002 0x20fadb4596000000 0xffff800000000003 0xe0ffffe7fe000000

def z756 : W := mkw 0x0000561040c00002 0x80dbd90000d29400 0x00007fffffffc003 0x98ffff0001fffc00

def z757 : W := mkw 0x340029a69a003901 0x542e00ee812d02f0 0xfe007fc0ff003ff3 0x54be00ff81cf03f0

def z758 : W := mkw 0x4948000000000002 0x20dafb39cc000000 0x0ffe000000000003 0xc0fffffbf8000000

def z759 : W := mkw 0x3400179e7ee43900 0xdc31ddee8186bef0 0xfe00000000fffff0 0xcc01ffff8000fff0

def z760 : W := mkw 0x41745555009a2682 0xd2c172b96dd0d34c 0x01ffffff00ff3fce 0xf2c1fff87ff0f3cc

def z761 : W := mkw 0xb4a369e69b10bd2b 0x54ee00eeb37d02f5 0xfe0e7fffff003ff3 0x54fe00ffb9ff03f0

def z762 : W := mkw 0x9b98a00b28294a57 0x20fedd6e9a2869aa 0x000e703ff8fffffc 0x1fb9c0e03838ffff

def z763 : W := mkw 0x09087e38e4e40003 0xa8dfdd2888fbbc00 0x00007fffffffc003 0x98ffff0001fffc00

def z764 : W := mkw 0x606312c051509428 0xd001229165868615 0xfff1ffc0fff8fe3f 0xff463f1fc7cf8e3f

def z765 : W := mkw 0xa0a316d875f49428 0xd831ddc43386be15 0xf1ff800000fffe3c 0xef01ffe47e00fe3f

def z766 : W := mkw 0x4250e829a0294257 0x00ce26114479690a 0x01f1ffffffffc00f 0xbbfe3f0047fffc0f

def z767 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe000fff070001c3 0x40fe00ff81f701c0

def z768 : W := mkw 0xc9dc0105000a2282 0x22fafb7dde004148 0xffff8000000001c3 0xe0fffffffe0001c0

def z769 : W := mkw 0xd2c0a00a28214855 0x00348e47162828a2 0xfe018000f800c031 0x2d3e0f0786080c33

def z770 : W := mkw 0x34347ffffefe3f81 0xde05048221fffffc 0x00007ffffffffffc 0x1e00000001fffffc

def z771 : W := mkw 0x10007e3aece40803 0x88dfdd0200fbbca0 0x00007ffffffffff3 0x9cffff0001fffff0

def z772 : W := mkw 0x0000200820200001 0x0004040000282800 0x00007fffffffc003 0x98fe3f0001fffc00

def z773 : W := mkw 0x1234ff7fecff6ed5 0xda05048221fbffee 0x00007ffffffffffc 0x1f00000001ffffff

def z774 : W := mkw 0x01247e78e4f60483 0x8adfdd0028fbbc04 0x000e7fffffffc003 0x98ffff0039fffc00

def z775 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xfe0e000000000003 0x40fff7ffb8000000

def z776 : W := mkw 0xdac8a00a28214855 0x203e8f47962828a2 0xfe01800000000001 0x203e0f0786000000

def z777 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe007fffff003ff1 0x147e001f81ff03f0

def z778 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe007ffffff8ffff 0x5ffe00ff81ff8fff

def z779 : W := mkw 0x34237ffefff4bd29 0xdc05048221ffbef5 0x00007ffffffffffc 0x1f00000001ffffff

def z780 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0xf001ffffffffc033 0xbdffff0407fffc33

def z781 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0x0ffe000000000002 0xc0fff7fbf8000000

def z782 : W := mkw 0xc8fc5555009a2680 0xf23b8bc5b7d0d34c 0xfe01ffff00ff3fcd 0x323e0f0787f0f3cc

def z783 : W := mkw 0x4374965964ff46d4 0x8a11ff116c82fd0e 0x01ff800000ffc00c 0xab01ff007e00fc0f

def z784 : W := mkw 0xffd881871a097b54 0x742022ffdf0443fa 0xffff800000003ffc 0x670000fffe0003ff

def z785 : W := mkw 0x94a37b66cb50ad2b 0x84df882ab2fb84e5 0x0fff803f00f8c1cc 0xab47c81bfe308dcf

def z786 : W := mkw 0x01345555009a2682 0xd2cb70b869d0d34c 0x01fe7fff00ff3fcf 0xd2fff0f879f0f3cc

def z787 : W := mkw 0x80a37e78e5f4842b 0x88dfdd0032fbbc05 0xf1fffffffffffe3f 0xffffff047ffffe3f

def z788 : W := mkw 0x00006828a0200003 0x00dedd0000792800 0x00007fffffffc003 0x98ffff0001fffc00

def z789 : W := mkw 0x352469e69a123d83 0x56ee00eea97d02f4 0xfe0e7fffff003ff3 0x54fe00ffb9ff03f0

def z790 : W := mkw 0xe8eb12c051509428 0xf03b8bc5b7868615 0xfe01ffc0fff8fe3d 0x3f3e0f0787cf8e3f

def z791 : W := mkw 0x01345d75809a2682 0xd2cb70b869d1d34c 0x01fe7fff07ff3fce 0xd2f9f0f879f7f3cc

def z792 : W := mkw 0x01340145001a2682 0x52c070b86900434c 0x01fe703f00ff3fce 0xd2c1f0f87830f3cc

def z793 : W := mkw 0xc1c0000000000002 0x00f0fa7d5e000000 0xffff800000000003 0xe0fffffffe000000

def z794 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0xf1f1ffffffffc003 0xf8ffff0447fffc00

def z795 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe000fffff0001f1 0x04fe00ff81ff01f0

def z796 : W := mkw 0xf6c3aaaafb61d97d 0x043e8e47962f2cb3 0xfe018000ff00c031 0x2d3e0f07860f0c33

def z797 : W := mkw 0x300068a298001803 0x50ee00c6017d02b0 0xfe007fffff003ff3 0x54fe00ff81ff03f0

def z798 : W := mkw 0x3233fefbfdfdde7d 0xd805048221ffffbf 0x00007ffffffffffc 0x1f00000001ffffff

def z799 : W := mkw 0xa197479551cab2aa 0x02f0f87c5a565559 0xf001803fff07c1f1 0x2d78381c063f7df3

def z800 : W := mkw 0x4140000000000002 0x00ea727dcc000000 0xffff800000000003 0xe0fffffffe000000

def z801 : W := mkw 0x00007e38e4e40003 0x88cf040000fbbc00 0x00007fffffffc003 0x98fe3f0001fffc00

def z802 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01fe7ffff8ffffcf 0xdac1f8f879f8ffcc

def z803 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe007fffffff3ff3 0xd4fe30ff81fff3f0

def z804 : W := mkw 0xb48069a69a003903 0x54ee00ee937d02f0 0xffffffffff003ff3 0x74fe00ffffff03f0

def z805 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xfffff000f8003e33 0xf4fffffffe080230

def z806 : W := mkw 0x00005e38e4e40002 0x88dbdd0000d3bc00 0x00007fc0ffffc003 0x98b9ff0001cffc00

def z807 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe007fffff003ff0 0x54b800ff81ff03f0

def z808 : W := mkw 0xc0c0000000000000 0x00308a4516000000 0xffff800000000003 0xe0bfcfe7fe000000

def z809 : W := mkw 0x202010c010101400 0xd02100c421848214 0xf1ffffc0fff8fe3f 0xffb9c8e47fcf8e3f

def z810 : W := mkw 0x213757d551dab6aa 0xd2c170b869d6d75d 0xf1ffffffffffffff 0xffc1f8fc7fffffff

def z811 : W := mkw 0x1200fe3aece54857 0x88dfdd0200fbbca2 0x00007fffffffc033 0x9dffff0001fffc33

def z812 : W := mkw 0x6250808930295254 0x502026d545046b1a 0xf1f1ffc0fffffe3f 0xffb83fe447cffe3f

def z813 : W := mkw 0x0000561864e40002 0x88d1dd0000d2bc00 0x00007fffffffc003 0x98f9ff0001fffc00

def z814 : W := mkw 0xe9ff01c5111ab6a8 0x722022fdff04435d 0xffff800000003ffc 0x670000fffe0003ff

def z815 : W := mkw 0x41745555009a2682 0xd2c172b96dd0d34c 0x0ffe7fff00ff3fce 0xd2c7f7fbf9f0f3cc

def z816 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x000e7fff00ff3fcc 0x12c1f0f839f0f3cc

def z817 : W := mkw 0x01345555009a2682 0xd2cb70b8e9d0d34c 0x0ffe7fff00ff3fce 0xd2c7f0fbf9f0f3cc

def z818 : W := mkw 0x01345d75849e2682 0xdacb71b869d1d34c 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z819 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00007fffff070003 0x10fff70001ff7000

def z820 : W := mkw 0xe2f380c11119d67c 0x502022d57704431f 0xf1ff800000003e3c 0x670000e47e00023f

def z821 : W := mkw 0x0010000100080200 0x0000201040004108 0x01fe703f00ff3fce 0xd2c1f0f87830f3cc

def z822 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xffff800000000001 0x60bfcffffe000000

def z823 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0x0e007fffff0001c3 0x10fe00fb81ff01c0

def z824 : W := mkw 0x00005e30c4c40002 0x88dbd90000d39400 0x00007fff07ff0003 0x90ffff0001f7f000

def z825 : W := mkw 0xbd8869a69a003903 0x74ee00ee9b7d02f0 0xfe0e7fffff003ff3 0x54fe00ffb9ff03f0

def z826 : W := mkw 0x01344555009a2682 0x52c070b86950534c 0x01fe003f00073fce 0xc2c1f0f8783073cc

def z827 : W := mkw 0x00003a28e4640001 0x881f8d0000abac00 0x00007fffffffc003 0x98ffff0001fffc00

def z828 : W := mkw 0x35343cf39a9a1f81 0x862f7056e8add1bc 0xfffe0000ffff003d 0x863ff007f80ff03c

def z829 : W := mkw 0x01345555009a2682 0x82c1703868d0d14c 0x01fe003f00ff01ce 0xc2c1f0f87830f1cc

def z830 : W := mkw 0x340069a69a003901 0x542e00ee817d02f0 0xfe007fffff003ff1 0x543e00ff81ff03f0

def z831 : W := mkw 0xb48369a69b00b92b 0x54ee00ee937d02f1 0xfe01ffffff003ff3 0x75fe00ff87ff03f3

def z832 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xffffffc0ff000003 0xf0ffffffffcf0000

def z833 : W := mkw 0xb4a313c65b50bd28 0xd43188eeb38686f5 0xffff800000f8fffc 0xef01c8fffe008fff

def z834 : W := mkw 0x3400218e3a203901 0x542404ee812c2af0 0xfe00703ff8fffff3 0xdc463fff8038fff0

def z835 : W := mkw 0x01144515008a2282 0x02c0703848505148 0x01fe703f00ff3fce 0xd2c1f0f87830f3cc

def z836 : W := mkw 0x140069268a002903 0x04ce002a807900e0 0xfe007fffff003ff3 0x54fe001f81ff03f0

def z837 : W := mkw 0x34006dbebea43903 0x5cee04ee817d3af0 0xfe007fffff073ff3 0x54fe00ff81ff73f0

def z838 : W := mkw 0xc9c87e38e4e40001 0xa825267ddefbbc00 0xffffffffffffc000 0x780000fffffffc00

def z839 : W := mkw 0x4140000000000002 0x00dafb394c000000 0xffff800000000003 0xe0fffffffe000000

def z840 : W := mkw 0x777481c71a1b7fd4 0x562022ffed0443fe 0xffff800000003ffc 0x670000fffe0003ff

def z841 : W := mkw 0xc9dc4515008a2282 0x22fafb7dde505148 0xfe01803f000701c1 0x207e3f1f863071c0

def z842 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0x0e007fff07003fc2 0x50fe00fb81f703c0

def z843 : W := mkw 0xc9c8000000000002 0x20fadb6d9e000000 0x0e0e000000000000 0x00bfc7e3b8000000

def z844 : W := mkw 0xe9c8008010001002 0x20fafb7dde040010 0xffff8000ff000033 0xe4fffffffe0f0030

def z845 : W := mkw 0x04007f3ce6e42103 0x8cdfdd2880fbbc40 0x00007fffffffc003 0x98ffff0001fffc00

def z846 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0xf1ffffff00ff3ffe 0xf7c1f0fc7ff0f3ff

def z847 : W := mkw 0x00007a28e0600003 0x80df8c0000fbac00 0x00007fffffffc003 0x98ffff0001fffc00

def z848 : W := mkw 0x0100551400802002 0xd0c170b849d09240 0x01fe7fff00ff3fc2 0xd0c1f0f879f0f3c0

def z849 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00007fff07ff0002 0x90fff70001f7f000

def z850 : W := mkw 0xa9af57d451d2b4aa 0xf2fbd9ecbbd69655 0x000e0fc007000000 0x00b9c0e039c70000

def z851 : W := mkw 0x01341451009a0680 0xd20170906980d30c 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z852 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfff1ffffff003fff 0x77fe00ffc7ff03ff

def z853 : W := mkw 0x01345f75c4de2682 0xdac170b869d3d74c 0x01fe7fff07ff3fce 0xd2c1f0f879f7f3cc

def z854 : W := mkw 0xfdc869a69a003901 0x7414fb935f7d02f0 0x01ffffffff003ff0 0xb401ff007fff03f0

def z855 : W := mkw 0xcbd8800100094256 0x20fafb7dde00410a 0xffff80000000000f 0xe3fffffffe00000f

def z856 : W := mkw 0x0110541100880202 0x80c1703848d0d108 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z857 : W := mkw 0x8080000000000002 0x00fad96c92000000 0xffff800000000003 0xe0fffffffe000000

def z858 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00000fffff07c001 0x08ffff0001ff7c00

def z859 : W := mkw 0x3600e9aeba217957 0x54ee04ee817d2af2 0xfe007fffff00fff3 0x5dfe00ff81ff0ff3

def z860 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfff07ffffff83fff 0xd6fe00ffc1ff83fc

def z861 : W := mkw 0x340069aeba203903 0x54ee04ee817d2af0 0xfff1ffffffffffff 0xfffe3fffc7ffffff

def z862 : W := mkw 0x5250de33cccd4a56 0x88dbfb1344d3d5aa 0xfff18fc007003ffc 0x67b9c01fc7c703ff

def z863 : W := mkw 0xc2f392414159c67c 0x8011aa117682c50f 0x01ff800000f8c00c 0xab01c8007e008c0f

def z864 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xf1ff8fc0fff8c03d 0xafb9c8e47fcf8c3f

def z865 : W := mkw 0xc9dc4515008a2282 0x22fafb7dde505148 0xfffff03f00ff3fcf 0xf2fffffffe30f3cc

def z866 : W := mkw 0x9290a00b28294a55 0x00348c46122869aa 0xf1fff03ff8ffffff 0xffb9c8e47e38ffff

def z867 : W := mkw 0x497c5555009a2682 0xf2c173b96dd0d34c 0x01fe7fff00ff3fce 0xd2c1f7f879f0f3cc

def z868 : W := mkw 0xfacba28a7961d87d 0x203e8f47962e2cb3 0xfe018000ff00c031 0x2d3e0f07860f0c33

def z869 : W := mkw 0x00007c38a4a40003 0x88cf550000f9b800 0x00007fffffff0003 0x90fff70001fff000

def z870 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xfffff03f00ff0003 0xf0fffffffe30f000

def z871 : W := mkw 0x340021861a003901 0x542400ee812c02f0 0xfe007fffff003ff3 0x54fe00ff81ff03f0

def z872 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01fe7fff00ff3fcc 0x5281c0f879f0f3cc

def z873 : W := mkw 0x4140000000000002 0x00c072394c000000 0x0ffe000000000002 0xc0c7f7fbf8000000

def z874 : W := mkw 0x1000200a28200801 0x00040402002828a0 0xfff1f03ff8ffffff 0xff463f1fc638ffff

def z875 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xfffff000f8f8c003 0xf8fffffffe088c00

def z876 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01fe0fff00ff01cc 0x82c1f0f879f0f1cc

def z877 : W := mkw 0x00237e78e5f4842b 0x88dfdd0020fbbc05 0x00007fffffffc00f 0x9bffff0001fffc0f

def z878 : W := mkw 0x093c5555009a2682 0xf2cb71b8e9d0d34c 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z879 : W := mkw 0xf6f381c71b19ff7c 0x542022fff70443ff 0xffff800000003ffc 0x670000fffe0003ff

def z880 : W := mkw 0xc9c8410400002002 0x20fafb7dde500040 0xffff803f000001c3 0xe0fffffffe3001c0

def z881 : W := mkw 0x8988000000000002 0x20fad96c9a000000 0xfe0e000000000003 0xc0ffffffb8000000

def z882 : W := mkw 0x213755d5119ab6aa 0xd2c170b869d4d35d 0x01fe7fff00ff3ffe 0xd7c1f0f879f0f3ff

def z883 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xf1ffffc0fff8fe3f 0xffffffe47fcf8e3f

def z884 : W := mkw 0x41745555009a2682 0xd2c172b96dd0d34c 0xffffffff00ff3fce 0xf2c1f0fffff0f3cc

def z885 : W := mkw 0xc9c8000000000002 0x20fadb6d9e000000 0xffff800000000003 0xe0bfcfe7fe000000

def z886 : W := mkw 0x0134575540da2682 0xd2c170b869d2d74c 0x01fe7fffffffffce 0xdac1f0f879ffffcc

def z887 : W := mkw 0xc8c8000000000000 0x203aab55d6000000 0xffff800000000003 0xe0fffffffe000000

def z888 : W := mkw 0x01144515008a2282 0x02c0703848505148 0x000e003f000701c0 0x00c1f0f8383071c0

def z889 : W := mkw 0xa0b757d551dab6a8 0xd23188c433d6d75d 0xf001fffffffffffd 0x3f38080407ffffff

def z890 : W := mkw 0xe9cb00801100902a 0x20fafb7dde040011 0xffff800000000033 0xe5fffffffe000033

def z891 : W := mkw 0x0000692480002003 0x50ee00ec81790240 0xfe007fffff003fc3 0x50fe00ff81ff03c0

def z892 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xffff800000000001 0xa0bfffe7fe000000

def z893 : W := mkw 0x4250961964ed4254 0x8811ff114482fd0a 0x0000000000ffc000 0x8801ff000000fc00

def z894 : W := mkw 0xc9fc165964fe0680 0xaa11ff117e82fd0c 0x01ff800000ffc00c 0xaa01ff007e00fc0c

def z895 : W := mkw 0x5250920348494a54 0x8011aa134482c5aa 0xfff1ffc0fff8ffff 0xffb9c81fc7cf8fff

def z896 : W := mkw 0x00007c3080800003 0x80dfd90000f99000 0x00007fffffff0003 0x90ffff0001fff000

def z897 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0xfffff03ff8ffffff 0xffc7fffffe38ffff

def z898 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xfffff00000f83e0f 0xf2fffffffe00820c

def z899 : W := mkw 0xc9cc451400822082 0x22fafb7dde501040 0xffff800000000003 0xe0fffffffe000000

def z900 : W := mkw 0x80837e38e5e4802b 0x88dfdd0012fbbc01 0x0001ffffffffc003 0xb9ffff0007fffc03

def z901 : W := mkw 0x340049a69a003902 0x54ea00ee815502f0 0x0e000fc0070001c0 0x00b800fb81c701c0

def z902 : W := mkw 0x140069268a002903 0x04ee006e807900e0 0xfe007fffff0001c3 0x50fe00ff81ff01c0

def z903 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0xfe01f03ff8fffffd 0x3f463f1f8638ffff

def z904 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfffe7fffff003ff3 0xd4ffc0fff9ff03f0

def z905 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0xf1ffffff00ff3fcf 0xf2c1f8fc7ff0f3cc

def z906 : W := mkw 0xb4a369e69b10bd2b 0x54ee00eeb37d02f5 0xfffffffffff8ffff 0xfffe08ffffff8fff

def z907 : W := mkw 0x4250920960694254 0x8011ae114482ed0a 0x01f1800000ffc00c 0xab01ff004600fc0f

def z908 : W := mkw 0x340069a69a003903 0x04ee006e807d00f0 0xfe007fffff0001f3 0x14fe001f81ff01f0

def z909 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01ffffff00ffffce 0xfbc1f8f87ff0ffcf

def z910 : W := mkw 0x41745555009a2682 0xd2c172b96dd0d34c 0xfffffffff8ffffff 0xffc7fffffff8ffff

def z911 : W := mkw 0xc8d8000100080200 0x203aab55d6004108 0xfff1f03f00ff3fcf 0xf27e3f1fc630f3cc

def z912 : W := mkw 0x00007e38e4e40003 0x88cf550000fbbc00 0x00007fffffffc003 0x18fe370001fffc00

def z913 : W := mkw 0xdac8aa2aec654855 0x283e8f47962b2ca2 0xfe018000ff00c031 0x2d3e0f07860f0c33

def z914 : W := mkw 0x00007c38a0a00003 0x80cf540000f9b800 0x00007fffffffc003 0x98ffff0001fffc00

def z915 : W := mkw 0x00345555009a2682 0xd2c1508021d0d34c 0x01fe7fff00ff3fce 0xd2c1f0e079f0f3cc

def z916 : W := mkw 0x5250a00b28294a55 0x00042613442869aa 0xfff1ffffffffffff 0xfffe3f1fc7ffffff

def z917 : W := mkw 0xc9d8000100080202 0x20fafb7dde004108 0xfffff03ff8ffffff 0xfffffffffe38ffff

def z918 : W := mkw 0x0000161864e40002 0x88dbdd000082bc00 0x00007fc0ffffc003 0x98ffff0001cffc00

def z919 : W := mkw 0x00345555009a2680 0xd201008021d0d34c 0x000e7fff00ff3fcc 0x1281c0e039f0f3cc

def z920 : W := mkw 0xc9c8000000000002 0x20d0fb395e000000 0xffff800000000003 0xe0c7fffffe000000

def z921 : W := mkw 0x01047f3ce4e62083 0x8adfdd2808fbbc40 0x00007fffffffc003 0x98ffff0001fffc00

def z922 : W := mkw 0x0030545100980602 0xd0c1709061d0d30c 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z923 : W := mkw 0x3237f7df79fbfefd 0xd205048221feffff 0x00007ffffffffffc 0x1f00000001ffffff

def z924 : W := mkw 0x4948000000000002 0x20ca7339cc000000 0xffff800000000003 0xe0c7fffffe000000

def z925 : W := mkw 0x00345555009a2680 0xd201209061d0d34c 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z926 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe000fff07003ff0 0x44fe00ff81f703f0

def z927 : W := mkw 0x340069a69a003901 0x542400ee817d02f0 0xfe007fffff003ff3 0x54b800ff81ff03f0

def z928 : W := mkw 0x01345555009a2682 0xd2c150a829d0d34c 0x000e7fff00ff3fce 0x52c1c0f839f0f3cc

def z929 : W := mkw 0x00007e38e4e40001 0x88158c0000fbbc00 0x00007fffffffc003 0x98ffff0001fffc00

def z930 : W := mkw 0xc9c8400000000002 0x20fafb7dde500000 0xffffffff00000003 0xf0fffffffff00000

def z931 : W := mkw 0x340069aeba203903 0x54ee04ee817d2af0 0xfe007fffff073ff3 0x54fe37ff81ff73f0

def z932 : W := mkw 0x5b58ec3bacad4a57 0x28ce773bcc7979aa 0x0e00003f000701c0 0x0046371b803071c0

def z933 : W := mkw 0x01341145001a2680 0xd20120b86980c34c 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z934 : W := mkw 0x80a37e78e5f4842b 0x88dfdd0032fbbc05 0x000e7fffffffc003 0x98ffff0039fffc00

def z935 : W := mkw 0x14007f3eeee42903 0x8cdfdd0200fbbce0 0x00007fffffffc1c3 0x98ffff0001fffdc0

def z936 : W := mkw 0x0130104100180602 0xd0c170b86980c30c 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z937 : W := mkw 0xcbfb92496179c67c 0xa011ff117e82ed0f 0x01ff800000ffc00c 0xab01ff007e00fc0f

def z938 : W := mkw 0xc9d8000100080202 0x20fafb7dde004108 0xffff803f000701c3 0xe0fffffffe3071c0

def z939 : W := mkw 0x00007e38e4e40001 0x8815dd0000fbbc00 0x00007fffffffc003 0x98b9ff0001fffc00

def z940 : W := mkw 0xfdfc01c71a1a3f80 0x762022ffff0443fc 0xffff800000003ffc 0x660000fffe0003fc

def z941 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x000e7fff00073fc2 0x50c1f0f839f073c0

def z942 : W := mkw 0x3000008218001800 0x502000c6010402b0 0xfe007fc0ff003ff3 0x54b800ff81cf03f0

def z943 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01fe7fff00ff3fcc 0x9281f0e079f0f3cc

def z944 : W := mkw 0xa4a35ff4d7d4b52a 0xdcfbd9ecb3d79655 0x000e0fc007000000 0x00b9c0e039c70000

def z945 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0x0fff800000000000 0xa0fffffbfe000000

def z946 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe01ffffff00fff3 0x7dfe08ff87ff0ff3

def z947 : W := mkw 0x0000120860600000 0x80118c000082ac00 0x00007fc0ffffc003 0x98b9ff0001cffc00

def z948 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xf1fffffffff8ffff 0xfff9c8fc7fff8fff

def z949 : W := mkw 0x3000618618003803 0x50e400ee017c02f0 0xfe007fffff003ff3 0x54fe00ff81ff03f0

def z950 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe007ffffff8fff3 0xdcfe08ff81ff8ff0

def z951 : W := mkw 0x00005e38e4e40002 0x88dbdd0000d3bc00 0x00007fff07ffc002 0x98f9ff0001f7fc00

def z952 : W := mkw 0x3223b2ca7971dc7d 0xd005048221aeaeb7 0x00007fc0fff8fe3c 0x1f00000001cf8e3f

def z953 : W := mkw 0x342069e69a103d03 0x54ee00eea17d02f4 0xfffe7fffff003fff 0x56fe00fff9ff03fc

def z954 : W := mkw 0x34006db69e843903 0x5cee51ee817d12f0 0xfe007fffff003ff3 0x54fe00ff81ff03f0

def z955 : W := mkw 0x89887e38e4e40003 0xa8dfdd001afbbc00 0x000e7fffffffc003 0x98ffff0039fffc00

def z956 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01fe003f00ff3fcc 0xc241f0f87830f3cc

def z957 : W := mkw 0xc9dc0411008a0282 0x22fafb7dde005108 0xffff800000070003 0xe0fffffffe007000

def z958 : W := mkw 0x3633fbeffb79ff7d 0xd405048221ffefff 0x00007ffffffffffc 0x1f00000001ffffff

def z959 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xffff8000f800c033 0xedfffffffe080c33

def z960 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00007fffffffc000 0x18fff70001fffc00

def z961 : W := mkw 0x340001861a003900 0x542000ee810402f0 0xfe000fc007003ff0 0x44b800ff81c703f0

def z962 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xf1fffffffffffe3f 0xfff9f8e47ffffe3f

def z963 : W := mkw 0x14007e3aeee40903 0x8cdfdd0280fbbca0 0x0e007fffffffc003 0x98ffff0381fffc00

def z964 : W := mkw 0x6650c9adb2297356 0x54ea26fdc5556b5a 0x01f18fc007ffc00c 0xabb83fe047c7fc0f

def z965 : W := mkw 0x34006dbebea43903 0x5cee55ee817d3af0 0xfe007ffffffffff3 0xdcfe3fff81fffff0

def z966 : W := mkw 0xc9d8000100080202 0x20fafb7dde004108 0xffff800000003fcf 0xe2fffffffe0003cc

def z967 : W := mkw 0x00006c38a4a40003 0x08dedd0000793800 0x00007fffff070003 0x90ffff0001ff7000

def z968 : W := mkw 0x00006828a0200003 0x00ce040000792800 0x00007fffff070003 0x10fe370001ff7000

def z969 : W := mkw 0xfcc82aaafe641901 0x2c3e8f47962f2cb0 0xfe018000ff00c031 0x2c3e0f07860f0c30

def z970 : W := mkw 0x1000692688002803 0x50ce00aa017902e0 0xfe007fffff003ff3 0x54fe00ff81ff03f0

def z971 : W := mkw 0x0000320860600003 0x80dfdd0000aaac00 0x00007fffffffc003 0x98ffff0001fffc00

def z972 : W := mkw 0xb283a28a7961d87d 0x00348c46122e2cb3 0xf0018000ff00c031 0x2d380804060f0c33

def z973 : W := mkw 0x340001861a003902 0x54ea00ee810402f0 0xfe007fc0ff003ff3 0x54fe00ff81cf03f0

def z974 : W := mkw 0x340069a69a003901 0x542e00c6817d02f0 0xfe007fffff003ff3 0x547e001f81ff03f0

def z975 : W := mkw 0x340069a69a003901 0x542400c6017d02f0 0xfe007fffff003ff3 0x54fe00ff81ff03f0

def z976 : W := mkw 0x4948000000000002 0x20ca7339cc000000 0x0e0e000000000000 0x00c7f7fbb8000000

def z977 : W := mkw 0x340068a29a001903 0x04ee0046807d00b0 0xfe007fffff003ff3 0x54fe001f81ff03f0

def z978 : W := mkw 0x00007e38e4e40003 0x88dfdd2800fbbc00 0x00007fffffffc003 0xd8fffff801fffc00

def z979 : W := mkw 0x497c5555009a2682 0xf2cb73b9edd0d34c 0x0e007fff00ff3fcc 0x1246371b81f0f3cc

def z980 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0x0e007fffff003ff0 0x14fe00fb81ff03f0

def z981 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xffff800000003e3f 0xe7fffffffe00023f

def z982 : W := mkw 0x1234f55f28bb6ed5 0xd205048221f8fbee 0x00007fff00ff3fcc 0x1200000001f0f3cc

def z983 : W := mkw 0x35046db69a823983 0x56ee50ee897d12f0 0xfe007fffff003ff3 0x54fe00ff81ff03f0

def z984 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00007ffffffffe3f 0x9fffff0001fffe3f

def z985 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xfffff03f00003fc3 0xf0fffffffe3003c0

def z986 : W := mkw 0x2000418410003002 0x50ea00ec81540250 0xfe007fffff003ff3 0x54fe00ff81ff03f0

def z987 : W := mkw 0x01345555009a2680 0xd201709069d0d34c 0x01fe7fff00ff3fce 0xd281f0e079f0f3cc

def z988 : W := mkw 0xfbfb80c31919de7c 0x702022ffff0443bf 0xffff800000003ffc 0x670000fffe0003ff

def z989 : W := mkw 0x0000161864e40000 0x8811dd000082bc00 0x00000fc007ffc000 0x88b9ff0001c7fc00

def z990 : W := mkw 0x5354ed3facaf6ad7 0x0ace773b4c7979ea 0x0e00003f000701c0 0x0046371b803071c0

def z991 : W := mkw 0x01341555009a2680 0xd20170b86980d34c 0x01fe703f00ff3fce 0xd241f0f87830f3cc

def z992 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0xffffffc0fff8fe3f 0xffffc8ffffcf8e3f

def z993 : W := mkw 0xe9cb02805140902a 0x20fafb7dde060411 0xfffff000fff8fe3f 0xfffffffffe0f8e3f

def z994 : W := mkw 0x00345555009a2682 0xd2c100a821d0d34c 0x01fe7fff00ff3fce 0xd2c1c0f879f0f3cc

def z995 : W := mkw 0x01345555009a2682 0xd2c150a829d0d34c 0x000e7fff00ff3fce 0x92c1f0e039f0f3cc

def z996 : W := mkw 0xa0a312c051509428 0xd03188c433868615 0x01ffffc0fff8fe3c 0xbfb9c8e07fcf8e3f

def z997 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x01f07ffffffffe0f 0xdaffff0041fffe0c

def z998 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00007fffffffc001 0x187e3f0001fffc00

def z999 : W := mkw 0xa080008010001000 0x503088c413040210 0xf1ffffc0fff8fe3f 0xffb9c8e47fcf8e3f

def z1000 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x00000fff07ffc000 0x88ffff0001f7fc00

def z1001 : W := mkw 0xe9cb02805140902a 0x20fafb7dde060411 0xffff800007000003 0xe0fffffffe070000

def z1002 : W := mkw 0xc9c8000000000000 0x203afb7dde000000 0xffff800000000001 0xe03ffffffe000000

def z1003 : W := mkw 0x0110000100080202 0x00c0703848004108 0x01fe003f000701c2 0xc0c1f0f8783071c0

def z1004 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfe000fc0ff003ff1 0x44be00ff81cf03f0

def z1005 : W := mkw 0x0030514500182602 0xd0c120b861d0c34c 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z1006 : W := mkw 0x0110410500082202 0x50c070b849504348 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z1007 : W := mkw 0xc9c8000000000002 0x20e0727dde000000 0xffff800000000003 0xe0c7fffffe000000

def z1008 : W := mkw 0x00006e38e4e40003 0x08dedd00007b3c00 0x00007fffff07c003 0x18fe3f0001ff7c00

def z1009 : W := mkw 0x14007f3eeee42903 0x8cdfdd2a80fbbce0 0xfe007ffffffffff3 0xdcffff1f81fffff0

def z1010 : W := mkw 0x00006c38a4a40003 0x08ce550000793800 0x00000fff07070000 0x00fe370001f77000

def z1011 : W := mkw 0x1000682288000803 0x00ce0002007900a0 0x0e007fffff0001c3 0x10fe001b81ff01c0

def z1012 : W := mkw 0x1000682288000803 0x00ee006e807900a0 0xfe007fffff003ff3 0x54fe00ff81ff03f0

def z1013 : W := mkw 0x00007f3ce4e42003 0x88dfdd2800fbbc40 0x00007fffffffc1c3 0x98ffff1801fffdc0

def z1014 : W := mkw 0xc9c8000000000000 0x203aab7dde000000 0xffff800000000003 0xe0bfcffffe000000

def z1015 : W := mkw 0x10007e3aece40803 0x88dfdd0200fbbca0 0x0e007fffffffc1c3 0x98ffff1b81fffdc0

def z1016 : W := mkw 0xc2f3965965fdc67c 0x8811ff117682fd0f 0x01ff800000ffc00c 0xab01ff007e00fc0f

def z1017 : W := mkw 0xc8c8000000000002 0x20fa8b6d96000000 0xffff800000000003 0xe0ffcffffe000000

def z1018 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x01fe7fffffffc003 0xd8ffffe079fffc00

def z1019 : W := mkw 0x340069a69a003903 0x54ee00ee817d02f0 0xfff1ffffff003ff3 0xf4fe08ffc7ff03f0

def z1020 : W := mkw 0xc0c0000000000002 0x00fafb5556000000 0xffff800000000003 0xe0fffffffe000000

def z1021 : W := mkw 0x10007e3aece40803 0x88dfdd0200fbbca0 0xfe007fffffffc033 0x9cffff0781fffc30

def z1022 : W := mkw 0x140069268a002903 0x04ce002a807900e0 0x0e000fff070001c0 0x00fe001b81f701c0

def z1023 : W := mkw 0x213757d551dab6aa 0xd2c170b869d6d75d 0x01fe7fff07ff3fce 0xd2c1f0f879f7f3cc

def z1024 : W := mkw 0x0020124040500400 0xd011888021828604 0xf1ffffc0fff8fe3f 0xffb9c8e47fcf8e3f

def z1025 : W := mkw 0x00207e78e4f40403 0x88dfdd0020fbbc04 0x01fe7fffffffc00f 0x9affff0079fffc0c

def z1026 : W := mkw 0xcdc8492482002102 0x24fafb7dde510040 0xffff800000000003 0xe0fffffffe000000

def z1027 : W := mkw 0x10007e3aece40803 0x88dfdd0200fbbca0 0xfff1ffffffffffff 0xffffff1fc7ffffff

def z1028 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01fe7fffffff3fcf 0xd2f9f0f879fff3cc

def z1029 : W := mkw 0xc9c8000000000002 0x20fadb6d9e000000 0xfe0f800000000003 0x60ffcfffbe000000

def z1030 : W := mkw 0x765081871a097b54 0x542022ffc50443fa 0xfe00000000003ff0 0x440000ff800003f0

def z1031 : W := mkw 0x213455d5109a3682 0xd2c170b869d4d35c 0x01fe7fffffff3ffe 0xd6c1f0f879fff3fc

def z1032 : W := mkw 0x0030104100180600 0xd00100802180c30c 0x01fe7fff00ff3fce 0xd281c0e079f0f3cc

def z1033 : W := mkw 0x00007e38e4e40001 0x881fdd0000fbbc00 0x00007fffffffc001 0x983fff0001fffc00

def z1034 : W := mkw 0x497c5555009a2682 0xf2cb73b9edd0d34c 0xffffffff00ff3fcf 0xf2c7fffffff0f3cc

def z1035 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xfe0f800000000001 0x20ffffffbe000000

def z1036 : W := mkw 0x340069a69a003903 0x54ce0082017d02f0 0xfe007fffff003ff3 0x54fe001f81ff03f0

def z1037 : W := mkw 0x497c5555009a2682 0xf2c172b9edd0d34c 0x0ffe7fff00ff3fce 0xd2c1f0fbf9f0f3cc

def z1038 : W := mkw 0x340069a69a003903 0x54ee51ee817d02f0 0xfe007fffff003ff3 0x54fe37ff81ff03f0

def z1039 : W := mkw 0xc9c80a20c4440002 0x28fafb7dde030400 0xffff800007000003 0xe0fffffffe070000

def z1040 : W := mkw 0xa093028151489228 0x0030a85452064519 0xf1f1f03fffffffff 0xff78381c463fffff

def z1041 : W := mkw 0xc9c84c3084840002 0x28fafb7dde511000 0xffff800000000003 0xe0fffffffe000000

def z1042 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0xf1fe7ffff8ff3fff 0xd6c1f0fc79f8f3fc

def z1043 : W := mkw 0x0000361864e40001 0x8815dd0000aabc00 0x00007fffffffc003 0x98ffff0001fffc00

def z1044 : W := mkw 0x01345555009a2682 0xd2c150a829d0d34c 0x01fe7fff00ff3fce 0xd281c0e079f0f3cc

def z1045 : W := mkw 0x25345df5929a3782 0xd6c170b869d5d35c 0x01fe7fff07ff3fce 0xd2c1f0f879f7f3cc

def z1046 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xffff800000f8c00f 0xebfffffffe008c0f

def z1047 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01fe7ffff8fffffe 0xdfc1f0f879f8ffff

def z1048 : W := mkw 0x140069268a002903 0x54ce00aa817902e0 0x0e007fffff003fc3 0x50fe00fb81ff03c0

def z1049 : W := mkw 0x01345555009a2680 0xd20120b869d0d34c 0x01fe7fff00ff3fce 0xd281c0f879f0f3cc

def z1050 : W := mkw 0x00006c38a4a40003 0x08ce550000793800 0x00007fffffffc003 0x98fe3f0001fffc00

def z1051 : W := mkw 0x00007e38e4e40003 0x88dfdd2880fbbc00 0x0e007fffffffc003 0x98ffff1b81fffc00

def z1052 : W := mkw 0xc8c8000000000000 0x203a8b4596000000 0xfe0f800000000001 0x20bfcfe7be000000

def z1053 : W := mkw 0x340049a69a003902 0x54ea00ee815502f0 0xfe007fff07003ff2 0x54f800ff81f703f0

def z1054 : W := mkw 0x1000200208000801 0x00040002002800a0 0xfe007fffff003ff3 0x54fe001f81ff03f0

def z1055 : W := mkw 0x350069a69a003903 0x54ee50ee897d02f0 0xfe0e7fffff003ff3 0x54ffc0ffb9ff03f0

def z1056 : W := mkw 0x340069aeba203903 0x54ee04ee817d2af0 0xfe007ffffffffff3 0x5cfe00ff81fffff0

def z1057 : W := mkw 0xc9c8441000800002 0x20fafb7dde501000 0xffff803f00070003 0xe0fffffffe307000

def z1058 : W := mkw 0xc3f7965961fbc6fc 0x8211fe117e82fd0f 0x01ff800000ffc00c 0xab01ff007e00fc0f

def z1059 : W := mkw 0x00005e38e4e40002 0x88dbdd0000d3bc00 0x00000fc007ffc003 0x88ffff0001c7fc00

def z1060 : W := mkw 0xc9c8020040400002 0x20fafb7dde020400 0xffff8000ff00c003 0xe8fffffffe0f0c00

def z1061 : W := mkw 0x0000761860e00003 0x80d5dc0000fabc00 0x00007fffffffc003 0x98ffff0001fffc00

def z1062 : W := mkw 0x01341451009a0682 0x82c170386880d10c 0x01fe703f00ff3fce 0xd2c1f0f87830f3cc

def z1063 : W := mkw 0x340069aeba203903 0x54ee04ee817d2af0 0xfe007fffff00fff3 0x5cfe0fff81ff0ff0

def z1064 : W := mkw 0x8080120040400000 0x8031884412828400 0xf1ffffc0fff8fe3f 0xffb9c8e47fcf8e3f

def z1065 : W := mkw 0x1310a00b28294a57 0x00c4743a482869aa 0x01fe703ff8fffffe 0xdfc1f0f87838ffff

def z1066 : W := mkw 0xc9c8000000000000 0x2030aa7dde000000 0xffff800000000003 0xe0fffffffe000000

def z1067 : W := mkw 0x4948000000000002 0x20ea737dcc000000 0xfffe000000000003 0xc0fff7fff8000000

def z1068 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0xf0007ffffffffe33 0xdcffff0401fffe30

def z1069 : W := mkw 0x34006db69a803903 0x54ee50ee817d12f0 0xfe007fffff073ff3 0x54fe30ff81ff73f0

def z1070 : W := mkw 0x4374d555009b66d6 0xd2c172b96dd0d34e 0x01ffffff00ff3fce 0xf3c1f0f87ff0f3cf

def z1071 : W := mkw 0xc9c8000000000000 0x2030fb555e000000 0xffff800000000003 0xe0fffffffe000000

def z1072 : W := mkw 0x7250808318095a54 0x502022d7450443ba 0xfff1800000003ffc 0x670000ffc60003ff

def z1073 : W := mkw 0xc9c8000000000002 0x20fafb7dde000000 0xffff800000000000 0x60fff7fffe000000

def z1074 : W := mkw 0x3634fdffbabb7fd5 0xd605048221fdfbfe 0x00007ffffffffffc 0x1f00000001ffffff

def z1075 : W := mkw 0x1000361a6ce40801 0x8815dd0200aabca0 0xfe00703ff8fffff3 0xdc47ff1f8038fff0

def z1076 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01fe0fff00073fcc 0x42c1f0f879f073cc

def z1077 : W := mkw 0x00006a28e4640003 0x08de8d00007b2c00 0x00007fffffffc003 0x98fe3f0001fffc00

def z1078 : W := mkw 0x00007e38e4e40001 0x881f8d0000fbbc00 0x00007fffffffc003 0x987e3f0001fffc00

def z1079 : W := mkw 0x5340a00a28214857 0x00c4763b4c2828a2 0xffff8000f800c033 0xedc7fffffe080c33

def z1080 : W := mkw 0xc9c8000000000002 0x20ea737dde000000 0xffff800000000002 0xe0c7f7fffe000000

def z1081 : W := mkw 0x1230b04b28394e55 0xd005048221a8ebae 0x00007ffff8fffffc 0x1f00000001f8ffff

def z1082 : W := mkw 0xc9c8000000000000 0x2030fb7dde000000 0xffff800000000003 0xe047fffffe000000

def z1083 : W := mkw 0x01345555009a2682 0xd2c150a829d0d34c 0x000e0fff000701c0 0x0081c0e039f071c0

def z1084 : W := mkw 0x340069aebe243903 0x5cee05ee817d2af0 0xfe007fffff003ff3 0x54fe07ff81ff03f0

def z1085 : W := mkw 0xc9c8000000000002 0x20fadb6d9e000000 0xfe0f800000000003 0xa0ffffe7be000000

def z1086 : W := mkw 0x4040000000000000 0x0000221144000000 0xffff800000000003 0xe0c7fffffe000000

def z1087 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0xfe007fffffffc003 0xd8ffff1f81fffc00

def z1088 : W := mkw 0x5260b04a28314c55 0xd005068325a8aaa6 0xffffffc0f8f8fe3f 0xff87cfe7ffc88e3f

def z1089 : W := mkw 0x240049a492003102 0x54ea00ec81550250 0xfe007fff07003fc3 0x50fe00ff81f703c0

def z1090 : W := mkw 0x40745555009a2680 0xd201229165d0d34c 0xfff1ffff00ff3fcf 0xf2463f1fc7f0f3cc

def z1091 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01fe0fff000701c2 0xc0c1f0f879f071c0

def z1092 : W := mkw 0x01007e38e4e40003 0x88dfdd2808fbbc00 0x000e7fffffffc003 0x98ffffe039fffc00

def z1093 : W := mkw 0x01144515008a2282 0x52c070b849505348 0x01fe7fff00073fc2 0xd0c1f0f879f073c0

def z1094 : W := mkw 0xc9ff165141da86a8 0xa211fb117e82d50d 0x01ff800000ffc00c 0xab01ff007e00fc0f

def z1095 : W := mkw 0x0020555400902402 0xd0c150a821d09244 0x01fe7fff00ff3fce 0xd2c1f0f879f0f3cc

def z1096 : W := mkw 0x01345555009a2682 0xd2c170b869d0d34c 0x01fe7fff00ff3fcf 0xd2c7fff879f0f3cc

def z1097 : W := mkw 0xc9cb02004140802a 0x20fafb7dde020401 0xffff80000000c003 0xe9fffffffe000c03

def z1098 : W := mkw 0xf3f781c7191bfefc 0x522022ff7f0443ff 0xffff800000003ffc 0x670000fffe0003ff

def z1099 : W := mkw 0x01145515008a2282 0x82c1703848d0d148 0x01fe7fff00ff01c2 0xd0c1f0f879f0f1c0

def z1100 : W := mkw 0x5754ed3faaab6bd7 0x06ce763bcc7979ea 0x0e00003f000701c0 0x0046371b803071c0

def z1101 : W := mkw 0x00007e38e4e40003 0x88dfdd0000fbbc00 0x01f1ffffffffc00f 0xbbffff0047fffc0f

def z1102 : W := mkw 0x0100000000000002 0x00faf97cc8000000 0xfffe000000000003 0xc0fffffff8000000

def z1103 : W := mkw 0x34006dbebea43903 0x5cee55ee817d3af0 0xfe00003f00073ff0 0x444637ff803073f0

def z1104 : W := mkw 0xa0a320c831309429 0x502404c4332c2a15 0xf1fff03ff8fffe3f 0xff463fe47e38fe3f

def z1105 : W := mkw 0x3000208218001803 0x50ee00ee812c02b0 0xfe007fffff003ff3 0x54fe00ff81ff03f0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z6]),(0,[z1,z2,z3,z4,z5,z10,z6]),(0,[z1,z2,z4,z11,z5,z12,z6]),(0,[z1,z2,z3,z4,z5,z6,z13]),(0,[z1,z14,z2,z3,z4,z5,z6])],[(0,[z15,z1,z2,z3,z4,z5,z6]),(0,[z1,z16,z2,z3,z4,z5,z6]),(0,[z1,z2,z17,z3,z4,z11,z6]),(0,[z18,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z21,z6])],[(0,[z1,z2,z3,z4,z5,z22,z6]),(0,[z1,z2,z23,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z24])],[(1,[z25,z1,z26,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z27]),(0,[z28,z1,z2,z3,z4,z5,z6]),(1,[z1,z29,z3,z4,z5,z6]),(0,[z1,z2,z3,z30,z4,z6,z31]),(0,[z1,z32,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z3,z33,z4,z5])],[(0,[z2,z3,z4,z34,z5,z22,z6]),(0,[z35,z1,z2,z36,z4,z5,z6]),(0,[z1,z2,z3,z37,z4,z5,z6]),(0,[z1,z2,z38,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z5,z6])],[(0,[z39,z1,z2,z3,z4,z5,z6]),(0,[z1,z40,z41,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z42]),(0,[z43,z1,z2,z3,z4,z5,z6]),(1,[z1,z44,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z45]),(0,[z46,z1,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z47,z5,z22,z6]),(0,[z1,z2,z48,z3,z4,z5,z6]),(0,[z49,z1,z2,z3,z4,z5,z6]),(0,[z50,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z52,z5,z6]),(0,[z1,z40,z2,z53,z3,z4,z5]),(0,[z1,z2,z3,z4,z54,z5,z6])],[(0,[z55,z1,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z56]),(0,[z1,z2,z3,z4,z57,z5,z6]),(0,[z1,z2,z3,z4,z5,z58,z6]),(0,[z1,z2,z3,z4,z59,z5,z6]),(0,[z1,z2,z60,z4,z5,z61,z6])],[(0,[z1,z2,z62,z4,z63,z5,z6]),(0,[z1,z64,z2,z3,z4,z5,z6]),(0,[z1,z2,z65,z3,z4,z5,z6]),(0,[z1,z2,z66,z3,z4,z12,z6]),(0,[z1,z2,z67,z3,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z68,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z69]),(0,[z70,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z71]),(0,[z1,z2,z3,z4,z72,z5,z6]),(1,[z1,z3,z4,z5,z6,z73]),(0,[z1,z2,z3,z4,z5,z74,z6])],[(0,[z1,z2,z3,z4,z75,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z76]),(0,[z1,z77,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z78,z6]),(0,[z1,z2,z3,z79,z4,z5,z6]),(0,[z1,z2,z4,z34,z5,z80,z6]),(0,[z1,z2,z3,z4,z5,z81,z6])],[(0,[z1,z2,z3,z4,z5,z6,z82])],[(0,[z83,z1,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z84,z3,z4,z85,z6]),(0,[z1,z2,z3,z4,z11,z5,z6]),(1,[z1,z2,z38,z4,z5,z6])],[(0,[z86,z1,z2,z3,z4,z5,z6]),(0,[z1,z87,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z88,z4,z5,z6]),(0,[z1,z2,z3,z4,z89,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z90]),(0,[z1,z91,z92,z3,z4,z5,z6]),(0,[z1,z93,z2,z3,z4,z5,z6]),(0,[z1,z64,z2,z3,z4,z5,z94])],[(0,[z1,z95,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z96]),(0,[z1,z97,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z98,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z99,z6]),(0,[z1,z100,z3,z4,z5,z9,z6])],[(0,[z1,z2,z3,z4,z5,z6,z101]),(0,[z1,z2,z3,z4,z102,z5,z6]),(0,[z1,z2,z3,z30,z4,z103,z6])],[(0,[z1,z2,z3,z4,z5,z104,z6]),(0,[z1,z2,z3,z105,z4,z5,z6])],[(0,[z1,z2,z3,z4,z106,z5,z6]),(0,[z1,z2,z3,z107,z4,z5,z6])]],
   [[(0,[z1,z2,z108,z4,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z109]),(0,[z1,z110,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z111,z5,z6]),(0,[z1,z2,z3,z4,z112,z5,z6]),(0,[z1,z2,z113,z3,z4,z5,z6]),(0,[z25,z1,z2,z26,z4,z5,z6]),(0,[z1,z41,z2,z3,z114,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z115])],[(0,[z1,z2,z3,z4,z5,z6,z116]),(0,[z1,z40,z2,z3,z4,z5,z117]),(0,[z118,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z119,z4,z5,z6]),(0,[z1,z120,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z121,z6])],[(0,[z122,z2,z123,z3,z4,z5,z6]),(0,[z1,z2,z124,z3,z4,z5,z6]),(0,[z125,z1,z2,z3,z4,z5,z6]),(0,[z55,z2,z3,z4,z5,z22,z6]),(0,[z1,z77,z2,z3,z4,z5,z6]),(0,[z1,z126,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z127,z6]),(0,[z1,z2,z3,z4,z5,z128,z6]),(0,[z129,z1,z2,z3,z4,z5,z61])],[(0,[z125,z2,z3,z62,z4,z5,z6]),(0,[z1,z2,z3,z130,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z131,z132])],[(0,[z1,z2,z3,z4,z5,z133,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z3,z4,z5,z134,z6])],[(0,[z1,z2,z3,z4,z135,z5,z6]),(1,[z2,z3,z4,z5,z6,z136])],[(0,[z1,z2,z3,z4,z5,z137,z6]),(0,[z1,z2,z138,z3,z4,z5,z6]),(0,[z55,z35,z2,z3,z4,z5,z6]),(0,[z1,z2,z139,z3,z4,z5,z6]),(0,[z1,z2,z3,z140,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z141,z6]),(0,[z1,z2,z3,z4,z142,z5,z6]),(0,[z1,z2,z3,z4,z20,z5,z117]),(0,[z1,z2,z3,z143,z4,z5,z6])],[(0,[z1,z2,z144,z3,z4,z5,z6]),(0,[z1,z2,z3,z145,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z146]),(0,[z147,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z148,z5,z6,z132])],[(0,[z1,z2,z149,z62,z4,z5,z6]),(0,[z1,z2,z150,z3,z4,z5,z6]),(0,[z1,z2,z151,z149,z4,z5,z6])],[(0,[z1,z2,z3,z4,z152,z5,z6]),(0,[z1,z2,z3,z4,z5,z153,z6]),(0,[z1,z2,z3,z154,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z155]),(0,[z1,z2,z3,z156,z4,z5,z6]),(0,[z1,z3,z4,z157,z5,z6,z158]),(0,[z1,z2,z159,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z160,z6]),(0,[z161,z2,z3,z4,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z162]),(1,[z163,z2,z3,z4,z5,z6]),(0,[z164,z1,z2,z3,z30,z5,z6])]],
   [[(0,[z161,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z165,z3,z4,z5,z6]),(0,[z1,z166,z2,z3,z4,z5,z6]),(0,[z1,z77,z2,z53,z3,z4,z5]),(0,[z1,z2,z17,z4,z63,z5,z6]),(0,[z1,z2,z167,z4,z11,z5,z6]),(0,[z1,z2,z3,z33,z4,z20,z5])],[],[(0,[z168,z1,z2,z3,z4,z5,z6]),(0,[z1,z169,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z170,z4,z5,z6]),(0,[z164,z1,z2,z3,z4,z6,z31])],[(0,[z1,z2,z3,z4,z5,z171,z6]),(0,[z1,z2,z66,z3,z4,z11,z6])],[(0,[z1,z2,z3,z4,z172,z5,z6]),(0,[z173,z1,z2,z3,z4,z5,z6])],[(0,[z161,z2,z3,z4,z34,z5,z6]),(0,[z1,z2,z3,z4,z174,z5,z6])],[(0,[z1,z2,z3,z175,z4,z5,z6])],[]],
   [[(0,[z1,z2,z3,z4,z176,z5,z6]),(0,[z1,z177,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z178,z4,z5,z6]),(0,[z179,z2,z3,z4,z5,z6,z180]),(0,[z1,z2,z3,z4,z5,z6,z181]),(0,[z1,z2,z3,z4,z182,z5,z6]),(0,[z183,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z184,z4,z5,z6]),(0,[z55,z1,z2,z3,z184,z5,z6]),(0,[z1,z2,z3,z185,z4,z114,z5]),(0,[z1,z2,z3,z4,z186,z5,z6]),(0,[z1,z2,z3,z4,z187,z5,z6]),(0,[z1,z2,z3,z188,z4,z5,z6]),(1,[z164,z1,z2,z3,z6,z31])],[(1,[z1,z2,z4,z5,z80,z6]),(0,[z1,z2,z3,z4,z5,z85,z6]),(0,[z1,z189,z2,z3,z4,z5,z6]),(0,[z1,z2,z190,z3,z4,z5,z6])],[(1,[z191,z123,z3,z4,z5,z6]),(0,[z192,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z193,z5,z6])],[(0,[z191,z1,z122,z3,z4,z5,z6]),(0,[z1,z2,z194,z3,z4,z5,z6]),(1,[z1,z2,z3,z185,z4,z5]),(0,[z1,z77,z3,z145,z4,z5,z6]),(0,[z1,z2,z3,z195,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z196]),(0,[z1,z2,z53,z3,z197,z5,z6])],[(0,[z198,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z199,z4,z5,z6]),(0,[z1,z2,z3,z4,z200,z5,z6]),(0,[z1,z2,z201,z3,z4,z5,z6])],[]],
   [[(0,[z191,z1,z123,z3,z4,z5,z6]),(0,[z1,z2,z151,z66,z4,z5,z6]),(0,[z1,z2,z3,z4,z202,z5,z6]),(1,[z1,z3,z4,z5,z6,z131])],[(0,[z1,z2,z3,z203,z4,z5,z6]),(0,[z1,z2,z204,z3,z4,z5,z6]),(0,[z1,z2,z3,z205,z4,z5,z6])],[(0,[z1,z77,z2,z3,z4,z5,z117]),(0,[z1,z2,z149,z167,z4,z5,z6])],[(0,[z1,z2,z3,z206,z4,z5,z6])],[(0,[z1,z207,z2,z3,z4,z5,z6]),(0,[z208,z1,z2,z3,z4,z5,z6]),(0,[z1,z41,z2,z3,z4,z5,z6]),(0,[z1,z84,z2,z3,z4,z85,z6]),(0,[z1,z2,z3,z4,z209,z5,z6]),(0,[z1,z210,z2,z3,z4,z5,z6])],[(0,[z1,z211,z2,z3,z4,z5,z6]),(0,[z212,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z213,z3,z4,z5,z6]),(0,[z1,z2,z214,z3,z4,z5,z6]),(0,[z1,z2,z215,z3,z4,z5,z6])],[(0,[z216,z1,z2,z3,z4,z5,z6]),(0,[z1,z217,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z218,z4,z5,z6])],[(0,[z219,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z220,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z221]),(0,[z1,z2,z222,z3,z4,z5,z6]),(0,[z1,z100,z2,z3,z114,z5,z6]),(0,[z1,z2,z3,z223,z4,z5,z6]),(0,[z1,z224,z2,z3,z4,z5,z6]),(0,[z1,z84,z40,z3,z4,z5,z6]),(0,[z1,z40,z2,z3,z4,z5,z6]),(0,[z225,z2,z17,z3,z4,z5,z6]),(1,[z1,z2,z226,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z227,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z228]),(0,[z1,z2,z3,z4,z229,z5,z6]),(0,[z1,z230,z2,z3,z4,z5,z6]),(0,[z1,z2,z231,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z232,z5,z6]),(0,[z164,z1,z29,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z233]),(0,[z234,z1,z2,z3,z4,z5,z6])],[(0,[z235,z1,z2,z3,z4,z5,z6]),(1,[z236,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z237,z6]),(0,[z1,z2,z3,z238,z4,z5,z6]),(0,[z1,z2,z151,z4,z11,z5,z6]),(0,[z1,z2,z239,z3,z4,z5,z6])],[(0,[z35,z2,z165,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z240]),(0,[z1,z241,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z242,z5,z6]),(0,[z243,z1,z2,z3,z4,z5,z6]),(0,[z1,z77,z3,z4,z5,z85,z6])],[(0,[z1,z244,z2,z3,z4,z5,z6]),(0,[z1,z2,z245,z3,z4,z5,z6]),(0,[z1,z2,z3,z30,z103,z5,z6])],[(0,[z246,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z247,z6,z180]),(0,[z248,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z148,z5,z158]),(0,[z1,z2,z3,z249,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z250,z6]),(0,[z251,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z180]),(0,[z1,z2,z3,z4,z5,z6,z252]),(0,[z1,z2,z253,z3,z4,z5,z6])],[(0,[z254,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z255,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z256,z6]),(0,[z1,z2,z3,z4,z257,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z258,z5,z6]),(0,[z2,z17,z159,z3,z4,z5,z6])],[(0,[z125,z1,z2,z167,z4,z5,z6]),(0,[z259,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z260,z5,z6]),(0,[z261,z1,z2,z3,z4,z5,z6]),(0,[z1,z77,z2,z3,z33,z4,z5]),(0,[z262,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z263,z5,z6]),(0,[z1,z2,z3,z4,z5,z264,z6]),(0,[z1,z2,z3,z4,z265,z5,z6]),(0,[z1,z2,z66,z4,z5,z12,z6]),(0,[z1,z2,z3,z197,z4,z148,z5]),(1,[z1,z266,z3,z4,z5,z6])],[(0,[z267,z1,z2,z3,z4,z5,z6]),(0,[z125,z35,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z268,z6]),(0,[z1,z2,z3,z269,z4,z5,z6]),(0,[z1,z2,z3,z4,z270,z5,z6]),(1,[z1,z2,z3,z4,z20,z117])],[(0,[z1,z2,z3,z4,z5,z6,z271]),(0,[z1,z100,z2,z3,z4,z5,z69]),(0,[z1,z272,z2,z3,z4,z5,z6])],[(0,[z1,z2,z273,z3,z4,z5,z6]),(0,[z1,z2,z274,z3,z4,z5,z6]),(0,[z1,z2,z275,z3,z4,z5,z6]),(0,[z1,z2,z3,z197,z4,z5,z132]),(0,[z1,z276,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z277,z4,z5,z6]),(0,[z1,z2,z278,z3,z4,z5,z6])]],
   [[(0,[z279,z1,z2,z3,z4,z22,z6]),(0,[z1,z280,z2,z3,z4,z5,z6]),(0,[z1,z2,z149,z3,z4,z5,z6]),(1,[z281,z2,z3,z4,z5,z6]),(0,[z1,z2,z282,z3,z4,z5,z6])],[(0,[z236,z2,z3,z4,z47,z5,z6]),(0,[z1,z84,z2,z3,z4,z5,z6]),(0,[z1,z2,z283,z3,z4,z5,z6]),(0,[z1,z284,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z285,z6]),(0,[z236,z1,z2,z3,z4,z5,z6]),(0,[z1,z64,z2,z3,z4,z157,z6]),(0,[z1,z2,z3,z4,z5,z6,z286]),(0,[z1,z2,z3,z4,z287,z5,z6])],[(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z1,z289,z2,z3,z4,z5,z6]),(0,[z290,z1,z2,z3,z4,z5,z6]),(0,[z291,z1,z2,z3,z4,z5,z6]),(0,[z292,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z3,z197,z4,z5])],[(0,[z293,z1,z2,z3,z4,z5,z6]),(0,[z279,z2,z3,z62,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z294,z6]),(0,[z1,z41,z3,z145,z4,z5,z6]),(0,[z295,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z53,z3,z4,z20,z5])],[(0,[z296,z1,z2,z3,z4,z5,z6]),(0,[z161,z1,z2,z167,z4,z5,z6]),(0,[z1,z2,z3,z297,z4,z5,z6]),(0,[z1,z2,z3,z4,z298,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z299]),(0,[z300,z1,z2,z3,z4,z5,z6]),(0,[z301,z2,z3,z4,z63,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z302]),(0,[z1,z2,z3,z303,z4,z5,z6])],[(0,[z236,z1,z2,z304,z4,z5,z6]),(0,[z236,z2,z3,z4,z34,z5,z6]),(0,[z1,z2,z3,z305,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z306]),(0,[z1,z2,z3,z4,z5,z307,z6]),(0,[z1,z2,z3,z4,z5,z308,z6]),(0,[z1,z2,z3,z4,z5,z12,z6]),(0,[z309,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z310,z5,z6]),(0,[z1,z44,z3,z4,z5,z6,z132])],[(0,[z1,z2,z311,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z312,z6]),(1,[z1,z2,z3,z4,z5,z134])],[(0,[z1,z313,z2,z3,z4,z5,z6]),(0,[z314,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z315,z5,z6]),(0,[z316,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z226,z3,z4,z5,z6]),(0,[z1,z2,z3,z317,z4,z5,z6]),(0,[z1,z318,z2,z3,z4,z5,z6])],[(0,[z1,z122,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z319,z6]),(0,[z1,z2,z3,z4,z5,z61,z6])],[(0,[z1,z2,z320,z3,z4,z5,z6]),(0,[z1,z2,z3,z321,z4,z5,z6]),(0,[z1,z322,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z323,z6]),(0,[z1,z19,z266,z3,z4,z5,z6])],[(0,[z1,z324,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z85,z9,z6]),(1,[z1,z77,z3,z4,z5,z158]),(0,[z1,z2,z3,z4,z5,z325,z6])],[(0,[z2,z165,z3,z62,z4,z5,z6]),(0,[z1,z326,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z114,z5,z6,z158]),(0,[z129,z1,z2,z60,z4,z5,z6])]],
   [[(0,[z1,z2,z327,z3,z4,z5,z6]),(0,[z1,z328,z2,z3,z4,z5,z6])],[(0,[z1,z2,z329,z3,z4,z5,z6]),(0,[z1,z330,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z331,z5,z6]),(1,[z332,z2,z3,z4,z5,z6]),(0,[z1,z333,z2,z3,z4,z5,z6]),(0,[z1,z2,z60,z3,z4,z5,z61]),(1,[z1,z2,z334,z4,z5,z6])],[(0,[z1,z100,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z335,z5,z6]),(0,[z332,z1,z2,z3,z4,z5,z6])],[(0,[z336,z1,z2,z3,z4,z5,z6]),(0,[z1,z41,z2,z3,z145,z5,z6]),(0,[z1,z41,z3,z4,z5,z85,z6]),(0,[z1,z2,z3,z4,z337,z5,z6])],[(0,[z338,z1,z2,z3,z4,z5,z6]),(0,[z339,z1,z2,z3,z4,z5,z6]),(0,[z164,z163,z2,z3,z4,z5,z6]),(0,[z1,z2,z340,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z341,z6]),(0,[z1,z2,z3,z4,z5,z342,z6]),(0,[z1,z2,z3,z4,z343,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z344])],[(0,[z1,z2,z3,z4,z5,z345,z6])],[(0,[z1,z346,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z347,z6]),(0,[z1,z2,z3,z185,z4,z5,z6]),(0,[z1,z2,z3,z4,z348,z5,z6])]],
   [[(0,[z1,z2,z3,z349,z4,z5,z6]),(0,[z350,z1,z2,z3,z4,z5,z6])],[(0,[z236,z1,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z351]),(0,[z1,z2,z3,z4,z5,z352,z6]),(0,[z1,z84,z3,z145,z4,z5,z6])],[(0,[z353,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z66,z165,z4,z5,z6]),(0,[z1,z2,z3,z4,z354,z5,z6]),(0,[z1,z2,z3,z4,z355,z5,z6]),(0,[z1,z356,z2,z3,z4,z5,z6]),(0,[z1,z44,z2,z3,z4,z5,z6])],[(0,[z236,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z357,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z358,z5,z6]),(1,[z1,z3,z359,z4,z5,z6])],[(0,[z360,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z361,z6])],[(0,[z362,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z363,z4,z5,z6]),(0,[z1,z40,z2,z3,z33,z4,z5]),(0,[z1,z2,z364,z3,z4,z5,z6])],[(0,[z1,z365,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z366,z4,z5,z6])],[(0,[z1,z2,z367,z3,z4,z5,z6]),(0,[z2,z151,z368,z3,z4,z5,z6]),(1,[z2,z3,z4,z369,z5,z6]),(0,[z1,z2,z3,z4,z370,z5,z6]),(1,[z1,z2,z3,z4,z5,z371])]],
   [[(0,[z1,z2,z3,z372,z4,z5,z6]),(0,[z129,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z373]),(0,[z1,z2,z3,z4,z5,z6,z136]),(0,[z1,z97,z3,z4,z5,z6,z31])],[(0,[z1,z2,z3,z4,z5,z374,z6]),(0,[z1,z2,z3,z4,z5,z6,z375])],[(1,[z1,z2,z3,z4,z5,z69]),(0,[z129,z1,z2,z3,z4,z5,z146]),(0,[z1,z2,z376,z3,z4,z5,z6])],[(0,[z1,z2,z377,z3,z4,z5,z6]),(0,[z1,z3,z145,z4,z157,z5,z6]),(1,[z1,z2,z3,z4,z5,z76])],[(0,[z378,z1,z2,z3,z4,z5,z6]),(0,[z279,z161,z2,z3,z4,z5,z6]),(0,[z1,z2,z165,z4,z11,z5,z6]),(0,[z1,z379,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z380]),(0,[z1,z2,z3,z197,z4,z5,z6])],[(0,[z1,z2,z3,z4,z381,z5,z6]),(0,[z1,z2,z382,z3,z4,z5,z6]),(0,[z383,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z384,z4,z5,z6])],[(0,[z1,z2,z3,z385,z4,z5,z6]),(0,[z1,z2,z4,z63,z5,z12,z6]),(0,[z1,z2,z3,z386,z4,z5,z6])]],
   [[(0,[z161,z2,z165,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z387,z5,z6]),(0,[z1,z2,z3,z4,z388,z5,z6]),(0,[z1,z84,z3,z4,z5,z85,z6]),(0,[z1,z2,z3,z4,z5,z6,z389])],[(0,[z1,z2,z62,z4,z11,z5,z6]),(0,[z1,z2,z390,z3,z4,z5,z6])],[(0,[z1,z2,z3,z391,z4,z5,z6]),(0,[z1,z2,z4,z5,z61,z6,z146])],[(0,[z1,z392,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z393,z6]),(0,[z1,z2,z394,z3,z4,z5,z6]),(0,[z1,z2,z395,z3,z4,z5,z6]),(0,[z1,z2,z396,z3,z4,z5,z6]),(0,[z164,z1,z2,z226,z4,z5,z6])],[(0,[z161,z125,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z397]),(0,[z1,z2,z3,z4,z398,z5,z6])],[(0,[z1,z2,z399,z3,z4,z5,z6]),(0,[z1,z2,z400,z3,z4,z5,z6]),(0,[z332,z2,z151,z3,z4,z5,z6])],[(0,[z401,z1,z2,z3,z4,z5,z247]),(0,[z1,z2,z3,z402,z4,z5,z6]),(0,[z164,z1,z2,z3,z4,z103,z6]),(0,[z1,z2,z3,z403,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z404,z5,z6]),(0,[z1,z2,z3,z4,z5,z405,z6]),(0,[z1,z2,z3,z406,z4,z5,z6]),(0,[z1,z2,z407,z3,z4,z5,z6]),(0,[z1,z2,z3,z408,z4,z5,z6]),(1,[z225,z2,z3,z4,z5,z6]),(0,[z163,z1,z2,z3,z4,z5,z6]),(1,[z1,z97,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z409,z5,z6])],[(0,[z1,z410,z2,z3,z4,z5,z6]),(0,[z1,z411,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z412,z6]),(0,[z1,z2,z3,z4,z413,z5,z6]),(0,[z1,z2,z3,z4,z5,z414,z6]),(1,[z1,z2,z3,z4,z5,z115])],[(0,[z279,z35,z2,z3,z4,z5,z6]),(0,[z401,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z415,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z416])],[],[(1,[z1,z2,z108,z4,z5,z6]),(0,[z1,z2,z3,z417,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z418]),(0,[z1,z2,z3,z4,z5,z419,z6])],[(0,[z1,z2,z3,z420,z4,z5,z6]),(0,[z1,z2,z421,z3,z4,z5,z6]),(0,[z1,z2,z3,z33,z4,z6,z117])],[(0,[z1,z100,z2,z3,z4,z5,z422]),(0,[z1,z2,z29,z3,z4,z5,z6]),(1,[z1,z423,z3,z4,z5,z6])],[(0,[z2,z165,z3,z4,z5,z22,z6]),(0,[z1,z2,z424,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z425,z6]),(0,[z1,z2,z3,z4,z5,z6,z426]),(0,[z427,z1,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z428,z4,z5,z6])],[(0,[z125,z2,z3,z4,z5,z22,z6]),(0,[z1,z2,z3,z429,z4,z5,z6]),(0,[z1,z2,z3,z4,z430,z5,z6]),(0,[z1,z100,z2,z3,z145,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z431])],[(0,[z1,z432,z2,z3,z4,z5,z6]),(0,[z1,z2,z433,z3,z4,z5,z6]),(0,[z225,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z11,z209,z5,z6]),(0,[z1,z423,z2,z3,z4,z5,z6])],[(0,[z1,z2,z66,z62,z4,z5,z6]),(0,[z1,z2,z3,z4,z434,z5,z6]),(0,[z1,z435,z2,z3,z4,z5,z6]),(0,[z436,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z437,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z438]),(0,[z1,z2,z439,z3,z4,z5,z6]),(0,[z1,z440,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z441,z5,z6])],[(0,[z1,z442,z2,z3,z4,z5,z6]),(0,[z301,z1,z2,z3,z4,z5,z6]),(0,[z295,z2,z3,z4,z11,z5,z6]),(0,[z1,z443,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z444,z5,z6]),(1,[z1,z2,z304,z4,z5,z6]),(0,[z1,z445,z2,z3,z4,z5,z6]),(0,[z1,z2,z17,z3,z4,z5,z6]),(1,[z295,z2,z3,z4,z5,z6]),(0,[z129,z1,z2,z4,z5,z6,z146]),(0,[z164,z281,z2,z3,z4,z5,z6]),(1,[z1,z2,z4,z5,z74,z6])],[(0,[z1,z2,z123,z3,z4,z5,z6]),(0,[z55,z2,z3,z184,z4,z5,z6]),(0,[z1,z2,z446,z3,z4,z5,z6]),(0,[z1,z2,z3,z447,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z448]),(0,[z1,z2,z17,z66,z4,z5,z6]),(0,[z1,z2,z449,z3,z4,z5,z6])],[(1,[z1,z2,z450,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z451,z4,z5,z6]),(0,[z1,z2,z3,z452,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z94])],[(0,[z1,z453,z2,z3,z4,z5,z6]),(0,[z236,z1,z2,z3,z184,z5,z6]),(0,[z1,z2,z454,z3,z4,z5,z6]),(0,[z25,z1,z91,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z455,z6]),(0,[z1,z2,z3,z456,z4,z5,z6])],[(0,[z1,z2,z399,z4,z47,z5,z6]),(0,[z1,z2,z3,z4,z457,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z458]),(0,[z1,z2,z3,z4,z459,z5,z6])],[(0,[z161,z1,z2,z151,z4,z5,z6]),(0,[z1,z2,z460,z3,z4,z5,z6])],[(0,[z461,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z462,z5,z6]),(0,[z463,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z464]),(0,[z279,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z465,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z5,z158]),(0,[z1,z2,z3,z4,z5,z466,z6]),(0,[z1,z2,z19,z3,z33,z4,z6])],[(0,[z1,z2,z3,z4,z467,z5,z6]),(0,[z1,z2,z151,z3,z167,z5,z6]),(0,[z1,z2,z3,z4,z468,z5,z6]),(0,[z469,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z470,z5,z6]),(0,[z1,z2,z3,z62,z4,z5,z6]),(0,[z1,z2,z3,z4,z471,z5,z6]),(0,[z1,z2,z3,z4,z472,z5,z6]),(0,[z1,z2,z3,z473,z4,z5,z6]),(0,[z1,z2,z3,z474,z4,z5,z6]),(0,[z1,z64,z3,z4,z157,z5,z6]),(1,[z2,z368,z3,z4,z5,z6]),(0,[z1,z2,z17,z4,z11,z5,z6])]],
   [[(0,[z161,z1,z2,z165,z4,z5,z6]),(0,[z1,z2,z475,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z157,z5,z6]),(1,[z1,z2,z3,z197,z5,z132])],[(0,[z1,z84,z2,z3,z4,z157,z6]),(1,[z1,z2,z66,z4,z12,z6]),(1,[z147,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z476]),(0,[z1,z2,z3,z4,z5,z477,z6]),(1,[z1,z2,z36,z4,z5,z6]),(0,[z1,z77,z2,z3,z197,z4,z5])],[(0,[z1,z2,z36,z3,z4,z5,z6]),(0,[z1,z478,z2,z3,z4,z5,z6])],[(0,[z279,z1,z2,z3,z4,z34,z6]),(0,[z1,z64,z3,z4,z114,z5,z6])],[(0,[z1,z2,z479,z3,z4,z5,z6]),(0,[z1,z2,z480,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z114,z5,z6]),(0,[z1,z2,z17,z3,z4,z12,z6]),(0,[z1,z2,z3,z4,z5,z6,z481]),(1,[z129,z1,z2,z4,z5,z146]),(0,[z1,z2,z3,z4,z5,z132,z117])],[(0,[z1,z482,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z483,z6]),(0,[z484,z1,z2,z3,z4,z5,z6]),(0,[z164,z1,z2,z334,z4,z5,z6]),(0,[z1,z2,z3,z30,z4,z5,z6])],[(0,[z485,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z486]),(0,[z1,z41,z3,z4,z5,z6,z158]),(0,[z1,z2,z3,z4,z5,z371,z6])]],
   [[(0,[z487,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z488,z5,z6]),(0,[z1,z281,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z63,z5,z6])],[(0,[z1,z489,z2,z3,z4,z5,z6]),(0,[z236,z2,z165,z3,z4,z5,z6])],[(0,[z1,z490,z2,z3,z4,z5,z6]),(0,[z1,z491,z2,z3,z4,z5,z6]),(0,[z1,z2,z492,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z493,z6]),(0,[z494,z1,z2,z3,z4,z5,z6]),(0,[z401,z2,z3,z4,z5,z247,z6]),(0,[z1,z2,z3,z4,z148,z5,z9])],[(0,[z1,z2,z3,z4,z5,z495,z6]),(0,[z1,z2,z3,z496,z4,z5,z6]),(0,[z1,z2,z3,z497,z4,z5,z6])],[(0,[z498,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z499]),(0,[z1,z3,z33,z497,z4,z5,z6])],[(0,[z500,z1,z2,z3,z4,z5,z6]),(0,[z1,z501,z2,z3,z4,z5,z6]),(0,[z1,z502,z2,z3,z4,z5,z6]),(0,[z1,z100,z77,z3,z4,z5,z6]),(0,[z1,z3,z4,z157,z5,z85,z6]),(0,[z1,z2,z3,z33,z4,z148,z5])]],
   [[(0,[z401,z1,z2,z3,z4,z5,z180]),(0,[z1,z2,z3,z4,z5,z6,z503]),(0,[z1,z2,z504,z3,z4,z5,z6])],[(0,[z1,z505,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z506,z5,z6]),(0,[z1,z2,z19,z3,z4,z5,z158]),(0,[z507,z1,z2,z3,z4,z5,z6]),(1,[z1,z508,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z103,z5,z6])],[(0,[z1,z2,z3,z509,z4,z5,z6]),(0,[z1,z2,z38,z4,z5,z6,z31]),(0,[z1,z2,z3,z33,z4,z5,z132])],[(0,[z1,z2,z3,z4,z5,z6,z510]),(0,[z1,z2,z3,z511,z4,z5,z6]),(0,[z1,z512,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z513]),(0,[z1,z2,z3,z4,z514,z5,z6])],[(0,[z1,z100,z3,z4,z157,z5,z6]),(0,[z164,z1,z2,z3,z4,z5,z371]),(0,[z1,z2,z3,z4,z5,z6,z31]),(0,[z1,z2,z3,z4,z5,z134,z31])],[(0,[z35,z1,z2,z3,z4,z22,z6]),(0,[z1,z91,z2,z92,z4,z5,z6]),(0,[z1,z77,z2,z3,z4,z5,z158]),(0,[z1,z2,z3,z4,z515,z5,z6])],[(0,[z191,z2,z123,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z516]),(0,[z517,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z92,z3,z4,z5,z6]),(0,[z1,z2,z3,z197,z5,z6,z132])],[(0,[z1,z2,z518,z3,z4,z5,z6])]],
   [[(0,[z125,z1,z2,z4,z5,z12,z6]),(0,[z519,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z80,z6]),(0,[z520,z1,z2,z3,z4,z5,z6])],[(1,[z125,z2,z62,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z521,z6]),(0,[z1,z2,z522,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z523,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z158]),(0,[z164,z1,z2,z3,z5,z6,z31]),(0,[z1,z423,z3,z197,z4,z5,z6])],[(0,[z1,z524,z2,z3,z4,z5,z6]),(0,[z1,z2,z525,z3,z4,z5,z6]),(0,[z1,z2,z3,z526,z4,z5,z6]),(0,[z1,z91,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z130,z4,z5])],[(0,[z1,z2,z3,z527,z4,z5,z6]),(1,[z401,z2,z3,z4,z5,z247])],[(0,[z1,z2,z3,z4,z5,z528,z6]),(0,[z1,z2,z3,z4,z5,z529,z6]),(0,[z1,z2,z530,z3,z4,z5,z6]),(1,[z1,z2,z215,z3,z4,z5]),(0,[z1,z2,z3,z4,z531,z5,z6]),(0,[z1,z2,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z532,z5,z6]),(1,[z1,z126,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z533,z5,z6]),(0,[z1,z2,z3,z534,z4,z5,z6]),(0,[z1,z2,z535,z3,z4,z5,z6])],[(0,[z2,z165,z3,z184,z4,z5,z6]),(0,[z2,z3,z184,z4,z47,z5,z6]),(0,[z35,z1,z2,z450,z4,z5,z6]),(0,[z35,z1,z2,z3,z4,z34,z6])],[(0,[z267,z191,z2,z3,z4,z5,z6]),(0,[z1,z2,z536,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z537,z5,z6]),(0,[z1,z2,z66,z3,z4,z5,z6]),(0,[z1,z2,z60,z3,z4,z5,z146])]],
   [[(0,[z1,z2,z3,z538,z4,z5,z6]),(0,[z1,z539,z2,z3,z4,z5,z6]),(0,[z125,z2,z3,z184,z4,z5,z6]),(0,[z540,z1,z2,z3,z4,z5,z6])],[(0,[z541,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z542,z4,z5,z6]),(0,[z543,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z167,z4,z63,z5,z6]),(0,[z1,z3,z4,z5,z6,z73,z31]),(0,[z1,z2,z544,z3,z4,z5,z6])],[(0,[z1,z2,z545,z3,z4,z5,z6]),(0,[z546,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z547,z4,z5,z6])],[(0,[z1,z2,z3,z548,z4,z5,z6])],[(0,[z549,z1,z2,z3,z4,z5,z6]),(0,[z161,z1,z2,z4,z5,z12,z6]),(0,[z2,z3,z184,z4,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z550]),(0,[z1,z3,z145,z4,z114,z5,z6]),(0,[z1,z2,z551,z3,z4,z5,z6])],[(0,[z1,z40,z2,z3,z197,z4,z5]),(0,[z1,z2,z17,z149,z4,z5,z6]),(1,[z1,z2,z376,z3,z4,z5])],[(0,[z1,z2,z552,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z302]),(0,[z164,z1,z2,z3,z4,z5,z115]),(0,[z1,z2,z3,z4,z553,z5,z6])],[(0,[z1,z2,z3,z108,z4,z5,z6]),(0,[z279,z2,z3,z4,z5,z22,z6]),(0,[z179,z1,z2,z3,z4,z5,z247]),(0,[z1,z554,z2,z3,z4,z5,z6]),(0,[z1,z555,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z158,z132]),(0,[z1,z2,z556,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z369,z5,z6]),(0,[z1,z2,z3,z557,z4,z5,z6])]],
   [[(0,[z1,z2,z149,z165,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z4,z558,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z559])],[(0,[z161,z1,z2,z17,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z560,z6]),(0,[z179,z1,z2,z3,z4,z5,z6]),(0,[z1,z77,z3,z4,z5,z6,z158]),(0,[z1,z2,z3,z561,z4,z5,z6]),(0,[z1,z2,z3,z562,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z165,z4,z63,z5,z6]),(0,[z1,z2,z3,z4,z563,z5,z6]),(0,[z564,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z565,z3,z4,z5,z6]),(0,[z1,z2,z566,z3,z4,z5,z6])],[(0,[z567,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z215,z3,z4,z114,z5]),(0,[z568,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z569]),(0,[z1,z570,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z3,z4,z5,z9]),(0,[z164,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z571,z6]),(0,[z1,z2,z572,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z573])],[(0,[z1,z2,z3,z4,z574,z5,z6]),(0,[z1,z40,z77,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z304,z4,z5,z6]),(0,[z236,z1,z2,z525,z4,z5,z6])],[(0,[z1,z2,z3,z4,z575,z5,z6]),(0,[z1,z2,z3,z4,z5,z94,z6]),(0,[z1,z2,z3,z4,z576,z5,z6]),(0,[z1,z2,z3,z4,z5,z577,z6]),(1,[z1,z284,z3,z4,z5,z6])],[(0,[z125,z1,z2,z151,z4,z5,z6]),(0,[z1,z2,z3,z450,z4,z5,z6]),(0,[z1,z2,z578,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z579])],[(0,[z267,z1,z122,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z580]),(0,[z581,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z103,z5,z6,z31]),(0,[z1,z3,z197,z359,z4,z5,z6])],[(0,[z1,z2,z3,z4,z582,z5,z6]),(0,[z1,z583,z2,z3,z4,z5,z6]),(0,[z1,z40,z3,z4,z157,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z584]),(0,[z1,z2,z3,z197,z4,z20,z5])],[(0,[z1,z2,z3,z4,z585,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z586])],[(0,[z1,z2,z3,z4,z587,z5,z6]),(1,[z279,z2,z3,z4,z22,z6]),(0,[z1,z2,z3,z4,z588,z5,z6]),(0,[z1,z2,z3,z4,z157,z5,z302]),(0,[z1,z2,z589,z3,z4,z5,z6]),(0,[z1,z2,z590,z3,z4,z5,z6]),(0,[z1,z2,z266,z3,z4,z5,z6])],[(0,[z267,z1,z123,z3,z4,z5,z6]),(0,[z267,z122,z2,z3,z4,z5,z6]),(0,[z125,z1,z2,z165,z4,z5,z6]),(0,[z591,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z592,z4,z5,z6])]],
   [[(0,[z1,z2,z593,z3,z4,z5,z6]),(0,[z1,z64,z41,z3,z4,z5,z6]),(0,[z1,z40,z2,z3,z4,z5,z158])],[(0,[z1,z2,z3,z4,z5,z6,z594]),(0,[z1,z2,z3,z4,z5,z6,z595]),(0,[z1,z2,z3,z4,z596,z5,z6]),(0,[z25,z1,z3,z26,z4,z5,z6]),(0,[z1,z40,z3,z4,z114,z5,z6]),(0,[z2,z3,z4,z369,z63,z5,z6]),(0,[z597,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z598,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z73]),(0,[z1,z2,z3,z33,z4,z5,z6])],[(0,[z1,z2,z3,z4,z599,z5,z6]),(0,[z600,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z601,z5,z6]),(1,[z1,z100,z3,z114,z5,z6]),(0,[z1,z2,z151,z4,z63,z5,z6]),(0,[z1,z2,z3,z4,z148,z5,z117])],[(0,[z1,z2,z53,z3,z4,z148,z5])],[(0,[z1,z2,z3,z4,z5,z6,z602]),(0,[z1,z2,z3,z130,z4,z157,z5]),(0,[z1,z2,z603,z3,z4,z5,z6]),(1,[z1,z2,z151,z63,z5,z6]),(0,[z1,z284,z3,z33,z4,z5,z6])],[(0,[z1,z2,z3,z604,z4,z5,z6]),(0,[z1,z2,z151,z3,z63,z5,z6]),(0,[z605,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z606]),(0,[z1,z607,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z608,z5,z6]),(1,[z2,z159,z3,z4,z5,z6]),(0,[z1,z2,z53,z3,z4,z5,z132])],[(0,[z1,z2,z3,z4,z47,z5,z6]),(0,[z1,z2,z7,z4,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z609,z6])]],
   [[(0,[z1,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z610,z4,z5,z6]),(0,[z1,z2,z3,z611,z4,z5,z6]),(0,[z612,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z132])],[(0,[z1,z2,z613,z3,z4,z5,z6]),(0,[z614,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z615,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z616,z6]),(0,[z1,z2,z3,z4,z5,z6,z617])],[(0,[z618,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z145,z4,z5,z9,z6]),(0,[z1,z2,z3,z4,z619,z5,z6]),(0,[z1,z2,z620,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z34,z5,z6])],[(0,[z1,z2,z3,z4,z621,z5,z6]),(0,[z622,z1,z2,z3,z4,z5,z6]),(0,[z623,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z624,z4,z5,z6]),(0,[z1,z625,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z334,z4,z5,z6]),(1,[z1,z3,z497,z4,z5,z6])]],
   [[(0,[z626,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z114,z5,z85,z6]),(1,[z301,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z627,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z628])],[(0,[z1,z2,z3,z4,z629,z5,z6]),(0,[z1,z2,z3,z4,z630,z5,z6]),(0,[z631,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z632,z6])],[(0,[z633,z1,z2,z3,z4,z5,z6]),(0,[z1,z91,z2,z26,z4,z5,z6]),(0,[z1,z92,z3,z26,z4,z5,z6]),(0,[z1,z2,z3,z4,z634,z5,z6])],[(0,[z1,z2,z635,z3,z4,z5,z6]),(0,[z636,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z637])],[(0,[z25,z1,z2,z92,z4,z5,z6]),(0,[z1,z2,z149,z4,z5,z12,z6]),(0,[z1,z2,z66,z167,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z136,z31])],[(0,[z2,z3,z62,z4,z47,z5,z6]),(0,[z1,z638,z2,z3,z4,z5,z6]),(0,[z1,z2,z639,z3,z4,z5,z6]),(0,[z1,z100,z41,z3,z4,z5,z6]),(0,[z1,z2,z640,z3,z4,z5,z6])],[(0,[z1,z641,z2,z3,z4,z5,z6]),(0,[z164,z1,z508,z3,z4,z5,z6]),(0,[z1,z126,z19,z3,z4,z5,z6])],[(0,[z1,z2,z3,z642,z4,z5,z6]),(0,[z1,z84,z64,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z643]),(0,[z1,z2,z368,z3,z4,z5,z6]),(0,[z1,z2,z3,z644,z4,z5,z6])]],
   [[(0,[z179,z1,z2,z3,z4,z5,z180])],[(0,[z1,z2,z3,z4,z645,z5,z6]),(0,[z25,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z646,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z9,z6,z158]),(0,[z1,z2,z647,z3,z4,z5,z6])],[(0,[z236,z125,z2,z3,z4,z5,z6]),(0,[z648,z1,z2,z3,z4,z5,z6])],[(0,[z2,z3,z62,z4,z34,z5,z6]),(0,[z1,z2,z3,z649,z4,z5,z6]),(0,[z1,z2,z3,z4,z650,z5,z6])],[(0,[z1,z2,z3,z4,z651,z5,z6]),(0,[z1,z40,z2,z3,z4,z5,z9]),(1,[z2,z3,z4,z209,z5,z6]),(0,[z1,z2,z3,z652,z4,z5,z6])],[(0,[z653,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z654,z6]),(0,[z1,z2,z3,z655,z4,z5,z6])],[(0,[z279,z2,z3,z184,z4,z5,z6]),(0,[z1,z2,z149,z3,z63,z5,z6]),(0,[z1,z2,z3,z359,z4,z5,z6]),(0,[z1,z2,z53,z19,z3,z4,z5])],[(0,[z656,z1,z2,z3,z4,z5,z6]),(0,[z657,z1,z2,z3,z4,z5,z6]),(0,[z658,z1,z2,z3,z4,z5,z6]),(0,[z1,z659,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z422])]],
   [[(0,[z125,z1,z2,z62,z4,z5,z6]),(0,[z1,z2,z3,z660,z4,z5,z6]),(0,[z179,z401,z2,z3,z4,z5,z6]),(0,[z661,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z167,z4,z5,z6])],[(0,[z35,z2,z3,z4,z47,z5,z6]),(0,[z662,z1,z2,z3,z4,z5,z6]),(0,[z1,z663,z2,z3,z4,z5,z6]),(0,[z1,z40,z3,z4,z5,z9,z6]),(0,[z664,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z74,z6,z31]),(0,[z1,z2,z53,z3,z148,z5,z6]),(0,[z1,z2,z3,z4,z665,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z666])],[(0,[z55,z1,z2,z3,z4,z5,z6]),(0,[z35,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z149,z3,z167,z5,z6])],[(0,[z1,z667,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z26,z4,z5,z6]),(0,[z1,z2,z668,z3,z4,z5,z6]),(0,[z1,z2,z19,z3,z4,z5,z117])],[(0,[z1,z669,z2,z3,z4,z5,z6]),(0,[z55,z2,z3,z62,z4,z5,z6]),(0,[z279,z236,z2,z3,z4,z5,z6]),(0,[z1,z670,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z671]),(0,[z1,z2,z3,z672,z4,z5,z6]),(0,[z1,z100,z3,z4,z114,z5,z6]),(0,[z1,z2,z3,z4,z20,z5,z9]),(0,[z1,z2,z151,z3,z4,z5,z6]),(0,[z1,z2,z673,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z674,z6]),(0,[z1,z64,z2,z3,z4,z85,z6]),(0,[z1,z77,z64,z3,z4,z5,z6])],[(0,[z675,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z676,z3,z4,z5,z6]),(0,[z1,z2,z677,z3,z4,z5,z6]),(0,[z1,z678,z2,z3,z4,z5,z6]),(0,[z1,z64,z2,z3,z4,z5,z76]),(0,[z1,z2,z679,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z680])],[(0,[z35,z2,z3,z4,z34,z5,z6]),(0,[z1,z2,z681,z3,z4,z5,z6]),(0,[z1,z84,z3,z4,z5,z6,z158]),(0,[z147,z2,z3,z4,z5,z6,z31]),(0,[z1,z2,z682,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z148,z5,z6])]],
   [[(0,[z191,z1,z2,z3,z4,z5,z6]),(1,[z179,z2,z3,z4,z5,z180]),(0,[z1,z2,z3,z4,z5,z683,z6]),(0,[z684,z1,z2,z3,z4,z5,z6]),(0,[z1,z685,z2,z3,z4,z5,z6])],[(0,[z125,z1,z2,z17,z4,z5,z6]),(0,[z1,z2,z3,z4,z686,z5,z6]),(0,[z1,z2,z3,z4,z5,z687,z6]),(1,[z1,z2,z399,z4,z5,z6]),(0,[z1,z2,z3,z4,z688,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z132]),(0,[z1,z2,z3,z4,z689,z5,z6])],[(0,[z690,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z691,z4,z5,z6]),(0,[z692,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z247,z6]),(0,[z1,z2,z3,z4,z5,z693,z6]),(0,[z1,z2,z694,z3,z4,z5,z6])],[(0,[z695,z1,z2,z3,z4,z5,z6]),(0,[z696,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z422,z6]),(0,[z1,z697,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z6,z117]),(0,[z1,z2,z3,z4,z5,z6,z117])],[(0,[z161,z1,z2,z62,z4,z5,z6]),(0,[z1,z2,z698,z3,z4,z5,z6]),(0,[z1,z699,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z700,z4,z5,z6]),(0,[z1,z2,z53,z3,z4,z5,z6])],[(0,[z161,z55,z2,z3,z4,z5,z6]),(1,[z1,z2,z525,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z701,z6]),(0,[z1,z2,z3,z4,z702,z5,z6]),(0,[z1,z2,z703,z3,z4,z5,z6]),(0,[z1,z508,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z131])],[(0,[z704,z1,z2,z3,z4,z5,z6]),(0,[z1,z100,z84,z3,z4,z5,z6]),(0,[z1,z64,z3,z4,z5,z9,z6]),(0,[z1,z2,z705,z3,z4,z5,z6]),(0,[z1,z2,z376,z3,z4,z5,z31]),(0,[z1,z2,z3,z4,z5,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z161,z2,z399,z4,z5,z6])],[(0,[z51,z1,z3,z4,z5,z158]),(0,[z1,z2,z3,z4,z20,z584])],[(0,[z2,z3,z4,z707,z5,z6]),(0,[z2,z7,z184,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z708])],[(0,[z1,z2,z709,z4,z5,z6]),(0,[z1,z100,z3,z130,z4,z5]),(0,[z1,z29,z334,z4,z5,z6]),(0,[z164,z1,z2,z3,z6,z710])],[],[(0,[z2,z3,z4,z5,z6,z136]),(0,[z295,z2,z4,z5,z12,z6]),(0,[z163,z2,z226,z4,z5,z6]),(0,[z2,z3,z4,z5,z134,z136])],[(0,[z1,z2,z711,z4,z5,z6]),(0,[z2,z165,z450,z4,z5,z6]),(0,[z1,z2,z712,z4,z5,z6])],[(0,[z713,z123,z3,z4,z5,z6]),(0,[z2,z159,z4,z11,z5,z6]),(0,[z1,z44,z3,z4,z5,z117])]],
   [[(0,[z1,z2,z714,z4,z5,z6]),(0,[z715,z2,z3,z4,z5,z6]),(0,[z1,z716,z3,z4,z5,z6]),(0,[z164,z163,z2,z3,z6,z31])],[(0,[z1,z2,z717,z4,z5,z6]),(0,[z125,z2,z304,z4,z5,z6])],[(0,[z1,z2,z226,z4,z5,z371]),(0,[z1,z2,z3,z6,z710,z31])],[(0,[z1,z2,z3,z718,z5,z6]),(0,[z125,z2,z450,z4,z5,z6]),(0,[z1,z719,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z720])],[(0,[z35,z2,z399,z4,z5,z6]),(0,[z97,z3,z4,z5,z6,z136])],[(0,[z1,z2,z721,z4,z5,z6])],[(0,[z1,z722,z3,z4,z5,z6]),(0,[z1,z2,z723,z4,z5,z6])]],
   [[(0,[z1,z3,z130,z4,z5,z158])],[(0,[z1,z2,z3,z4,z5,z724]),(0,[z1,z2,z4,z310,z12,z6])],[(0,[z1,z2,z3,z4,z725,z6]),(0,[z726,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z727,z6]),(0,[z1,z728,z3,z4,z5,z6]),(0,[z3,z4,z5,z6,z73,z136])],[(0,[z1,z2,z3,z4,z729,z6]),(0,[z1,z40,z3,z359,z4,z5]),(0,[z1,z3,z4,z5,z6,z730])],[(0,[z1,z2,z3,z4,z731,z117])],[(0,[z1,z2,z3,z4,z5,z732]),(0,[z1,z733,z3,z4,z5,z6]),(0,[z164,z1,z2,z3,z6,z31]),(0,[z164,z1,z2,z3,z134,z31])],[(0,[z1,z126,z3,z197,z4,z5])],[(0,[z191,z123,z3,z4,z5,z6]),(0,[z1,z734,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z735]),(0,[z1,z44,z3,z4,z5,z69]),(0,[z1,z2,z4,z736,z5,z6])]],
   [[(0,[z737,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z738,z6])],[(0,[z1,z2,z3,z4,z5,z739]),(0,[z1,z740,z3,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z741]),(0,[z742,z2,z3,z4,z5,z6]),(0,[z1,z2,z743,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z5,z744]),(0,[z1,z2,z745,z4,z5,z6]),(0,[z2,z3,z4,z434,z22,z6]),(0,[z1,z41,z3,z4,z5,z69]),(0,[z1,z2,z3,z303,z5,z132]),(0,[z2,z3,z4,z746,z5,z6]),(0,[z164,z1,z2,z3,z115,z31])],[(0,[z1,z2,z747,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z748]),(0,[z1,z41,z3,z4,z5,z76])],[(0,[z295,z2,z151,z4,z5,z6]),(0,[z749,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z4,z750,z22,z6]),(0,[z1,z2,z3,z4,z5,z751]),(0,[z1,z100,z3,z752,z5,z6])],[(0,[z236,z2,z108,z47,z5,z6]),(0,[z1,z2,z3,z753,z5,z6]),(0,[z754,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z134,z74])],[(0,[z1,z2,z3,z4,z5,z755]),(0,[z2,z194,z3,z47,z5,z6])],[(0,[z756,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z186,z5,z158]),(0,[z1,z2,z226,z4,z5,z6]),(0,[z1,z29,z3,z4,z5,z115])],[(0,[z1,z2,z757,z4,z5,z6]),(0,[z1,z2,z3,z758,z4,z5]),(0,[z295,z2,z165,z4,z5,z6])],[(0,[z2,z759,z3,z4,z5,z6]),(0,[z236,z2,z3,z47,z5,z6])],[(0,[z1,z3,z760,z4,z5,z6])],[(0,[z1,z2,z4,z5,z761,z6]),(0,[z163,z2,z334,z4,z5,z6]),(0,[z1,z2,z3,z4,z762,z5])]],
   [[(0,[z2,z763,z3,z4,z5,z6]),(0,[z1,z3,z359,z4,z5,z132]),(0,[z1,z2,z3,z4,z764,z5])],[(0,[z2,z3,z4,z5,z765,z6]),(0,[z1,z2,z766,z4,z5,z6]),(0,[z2,z399,z62,z4,z5,z6]),(0,[z1,z126,z3,z4,z5,z158])],[(0,[z236,z2,z304,z47,z5,z6]),(0,[z1,z2,z767,z4,z5,z6])],[(0,[z1,z713,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z768]),(0,[z1,z77,z3,z497,z4,z5]),(0,[z1,z3,z4,z5,z6,z769])],[(0,[z1,z2,z3,z770,z4,z5]),(0,[z125,z2,z649,z4,z5,z6]),(0,[z1,z44,z3,z4,z5,z6]),(0,[z1,z64,z3,z130,z4,z5]),(0,[z2,z771,z3,z4,z5,z6]),(0,[z772,z2,z3,z4,z5,z6])],[(0,[z1,z2,z773,z3,z4,z5]),(0,[z774,z2,z3,z4,z5,z6]),(0,[z2,z159,z149,z4,z5,z6])],[(0,[z1,z2,z3,z4,z750,z6]),(0,[z1,z2,z3,z4,z5,z775])],[(0,[z1,z266,z3,z4,z5,z6]),(0,[z164,z1,z508,z3,z6,z31])]],
   [[(0,[z1,z38,z4,z5,z6,z73]),(0,[z1,z3,z4,z5,z6,z776])],[(0,[z1,z2,z777,z4,z5,z6]),(0,[z1,z2,z778,z4,z5,z6])],[(0,[z1,z2,z3,z779,z4,z5]),(0,[z1,z3,z4,z5,z6,z73]),(0,[z780,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z781]),(0,[z1,z77,z3,z4,z5,z782]),(0,[z1,z3,z4,z5,z134,z73]),(0,[z1,z19,z3,z359,z4,z5])],[(0,[z1,z2,z783,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z784]),(0,[z1,z2,z3,z4,z785,z6])],[(0,[z281,z2,z3,z4,z5,z6]),(0,[z1,z40,z278,z3,z4,z5]),(0,[z1,z2,z66,z4,z785,z6])],[(0,[z1,z786,z3,z4,z5,z6]),(0,[z2,z3,z4,z787,z5,z6]),(0,[z163,z2,z3,z4,z5,z371]),(0,[z1,z97,z3,z4,z5,z134])],[(0,[z1,z3,z185,z145,z4,z5]),(0,[z788,z2,z3,z4,z5,z6])],[(0,[z1,z2,z789,z4,z5,z6]),(0,[z1,z84,z3,z4,z85,z6]),(0,[z1,z2,z3,z4,z5,z790])]],
   [[(0,[z1,z791,z3,z4,z5,z6]),(0,[z1,z792,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z793]),(0,[z1,z2,z3,z4,z20,z27]),(0,[z794,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z558,z117])],[(0,[z1,z2,z795,z4,z5,z6]),(0,[z1,z2,z3,z4,z731,z6])],[(0,[z1,z3,z4,z5,z6,z796])],[(0,[z1,z2,z797,z4,z5,z6]),(0,[z1,z2,z798,z3,z4,z5])],[(0,[z1,z84,z3,z4,z799,z6]),(0,[z1,z44,z3,z197,z5,z132])],[(0,[z1,z2,z3,z800,z4,z5]),(0,[z1,z3,z4,z265,z5,z158]),(0,[z801,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z134])],[(0,[z1,z802,z3,z4,z5,z6])],[(0,[z1,z2,z803,z4,z5,z6]),(0,[z1,z2,z4,z5,z804,z6]),(0,[z1,z2,z3,z4,z5,z805]),(0,[z806,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z807,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z808])],[(0,[z1,z2,z809,z3,z4,z6]),(0,[z1,z810,z3,z4,z5,z6])],[(0,[z2,z811,z3,z4,z5,z6]),(0,[z1,z2,z4,z812,z5,z6])],[(0,[z147,z3,z4,z5,z6,z73])],[(0,[z2,z450,z4,z47,z5,z6]),(0,[z813,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z814]),(0,[z1,z508,z226,z4,z5,z6]),(0,[z1,z3,z815,z4,z5,z6])],[(0,[z332,z2,z3,z4,z5,z6]),(0,[z1,z816,z3,z4,z5,z6]),(0,[z1,z2,z3,z762,z5,z132])],[(0,[z1,z817,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z710]),(0,[z2,z38,z4,z5,z6,z136])],[(0,[z163,z2,z3,z4,z5,z115])]],
   [[(0,[z125,z2,z759,z4,z5,z6]),(0,[z1,z818,z3,z4,z5,z6]),(0,[z819,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z820]),(0,[z147,z2,z38,z4,z5,z6]),(0,[z1,z821,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z822]),(0,[z125,z2,z368,z4,z5,z6]),(0,[z1,z2,z823,z4,z5,z6]),(0,[z1,z40,z3,z185,z4,z5])],[(0,[z2,z450,z4,z34,z5,z6]),(0,[z2,z4,z5,z74,z6,z136])],[(0,[z1,z100,z3,z185,z114,z5]),(0,[z824,z2,z3,z4,z5,z6])],[(0,[z1,z2,z4,z5,z825,z6]),(0,[z1,z826,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z9,z69]),(0,[z827,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z9,z76])],[(0,[z163,z2,z3,z4,z5,z6]),(0,[z295,z2,z17,z4,z5,z6])],[(0,[z1,z3,z828,z4,z5,z6]),(0,[z1,z3,z359,z4,z5,z6]),(0,[z1,z3,z4,z5,z9,z82]),(0,[z1,z829,z3,z4,z5,z6]),(0,[z164,z1,z2,z226,z6,z31])]],
   [[(0,[z1,z2,z830,z4,z5,z6]),(0,[z1,z2,z4,z5,z831,z6]),(0,[z1,z2,z3,z4,z5,z832]),(0,[z1,z2,z4,z5,z833,z6]),(0,[z2,z834,z3,z4,z5,z6]),(0,[z281,z2,z334,z4,z5,z6]),(0,[z1,z835,z3,z4,z5,z6])],[(0,[z2,z399,z4,z5,z22,z6]),(0,[z1,z2,z836,z4,z5,z6]),(0,[z1,z2,z837,z4,z5,z6]),(0,[z164,z1,z29,z3,z6,z31])],[(1,[z2,z3,z4,z5,z838])],[(0,[z191,z713,z3,z4,z5,z6]),(0,[z1,z2,z3,z839,z4,z5]),(0,[z2,z3,z4,z369,z5,z6]),(0,[z301,z2,z151,z63,z5,z6]),(0,[z1,z2,z3,z4,z5,z371]),(0,[z1,z3,z197,z5,z131,z132])],[(0,[z279,z2,z3,z4,z493,z6])],[(0,[z2,z3,z4,z840,z5,z6]),(0,[z1,z3,z4,z5,z6,z841]),(0,[z281,z508,z3,z4,z5,z6])],[(0,[z1,z2,z842,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z843])],[(0,[z125,z2,z159,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z844]),(0,[z1,z2,z3,z4,z5,z69]),(0,[z2,z845,z3,z4,z5,z6])]],
   [[(0,[z1,z846,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z76]),(0,[z1,z2,z3,z4,z462,z117]),(0,[z301,z2,z4,z5,z12,z6]),(0,[z847,z2,z3,z4,z5,z6]),(0,[z164,z147,z2,z3,z6,z31]),(0,[z2,z376,z3,z4,z5,z136])],[(0,[z1,z2,z4,z5,z80,z6]),(0,[z1,z848,z3,z4,z5,z6]),(0,[z1,z3,z185,z4,z5,z158]),(0,[z849,z2,z3,z4,z5,z6]),(0,[z2,z368,z4,z63,z5,z6]),(0,[z1,z2,z376,z4,z5,z74])],[(0,[z1,z2,z3,z5,z850,z6]),(0,[z1,z44,z3,z33,z4,z5])],[(0,[z1,z2,z3,z185,z4,z5]),(0,[z1,z851,z3,z4,z5,z6])],[],[(0,[z1,z3,z185,z4,z5,z85]),(0,[z1,z3,z497,z4,z20,z5])],[(0,[z1,z2,z852,z4,z5,z6]),(0,[z281,z2,z3,z4,z5,z371]),(0,[z1,z2,z3,z197,z762,z5])],[(0,[z1,z853,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z131]),(0,[z1,z2,z3,z4,z5,z854]),(0,[z1,z2,z226,z4,z5,z115])]],
   [[(0,[z1,z2,z3,z4,z5,z855]),(0,[z1,z856,z3,z4,z5,z6]),(0,[z1,z100,z3,z114,z5,z422])],[(0,[z1,z2,z3,z4,z857,z5]),(0,[z858,z2,z3,z4,z5,z6]),(0,[z1,z2,z859,z4,z5,z6]),(0,[z1,z126,z53,z3,z4,z5])],[(0,[z1,z2,z66,z4,z687,z6]),(0,[z1,z2,z860,z4,z5,z6]),(0,[z164,z281,z2,z3,z6,z31])],[(0,[z1,z2,z861,z4,z5,z6])],[(0,[z236,z2,z3,z862,z5,z6]),(0,[z1,z97,z3,z4,z5,z6]),(0,[z1,z3,z197,z359,z5,z132])],[(0,[z1,z2,z4,z5,z863,z6]),(0,[z1,z2,z3,z4,z864,z6]),(0,[z1,z2,z3,z4,z5,z865]),(0,[z1,z2,z3,z4,z866,z5])],[(0,[z2,z151,z369,z63,z5,z6]),(0,[z1,z3,z867,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z868])],[(0,[z869,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z870]),(0,[z2,z7,z62,z4,z5,z6]),(0,[z1,z2,z108,z4,z5,z6]),(0,[z1,z2,z871,z4,z5,z6]),(0,[z1,z3,z4,z752,z5,z6]),(0,[z1,z3,z359,z4,z148,z5])],[(0,[z1,z872,z3,z4,z5,z6]),(0,[z1,z2,z3,z873,z4,z5])],[(0,[z1,z2,z874,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z875]),(0,[z1,z423,z3,z4,z5,z6]),(0,[z1,z876,z3,z4,z5,z6]),(0,[z877,z2,z3,z4,z5,z6])],[(0,[z1,z878,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z879]),(0,[z1,z2,z3,z762,z5,z6])],[(0,[z1,z2,z3,z4,z5,z880]),(0,[z1,z19,z3,z497,z4,z5])],[(0,[z1,z2,z3,z4,z881,z5]),(0,[z1,z882,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z883,z6]),(0,[z1,z3,z884,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z885]),(0,[z1,z169,z3,z4,z85,z6]),(0,[z163,z508,z3,z4,z5,z6]),(0,[z1,z2,z334,z4,z5,z371])]],
   [[(0,[z1,z886,z3,z4,z5,z6]),(0,[z281,z2,z3,z4,z5,z115])],[(0,[z1,z2,z304,z4,z5,z6]),(0,[z1,z828,z26,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z887]),(0,[z1,z888,z3,z4,z5,z6])],[(0,[z279,z2,z3,z4,z560,z6]),(0,[z301,z2,z151,z4,z5,z6])],[(0,[z1,z2,z450,z4,z5,z6]),(0,[z1,z3,z4,z5,z889,z6]),(0,[z1,z3,z130,z497,z4,z5]),(0,[z1,z2,z3,z4,z20,z117])],[(0,[z1,z2,z3,z4,z5,z890]),(0,[z891,z1,z2,z4,z5,z6]),(0,[z125,z2,z194,z4,z5,z6]),(0,[z1,z685,z3,z114,z5,z6]),(0,[z1,z2,z3,z4,z5,z94]),(0,[z1,z508,z3,z4,z5,z371])],[(0,[z1,z2,z3,z4,z5,z892]),(0,[z1,z3,z4,z5,z782,z158])],[(0,[z1,z2,z893,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z894]),(0,[z301,z2,z165,z4,z5,z6]),(0,[z2,z3,z895,z4,z5,z6]),(0,[z1,z4,z5,z74,z6,z73])]],
   [[(0,[z896,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z897,z5,z6])],[(0,[z1,z2,z3,z4,z5,z898]),(0,[z164,z1,z97,z3,z6,z31]),(0,[z164,z1,z2,z74,z6,z31])],[(0,[z290,z2,z3,z4,z22,z6]),(0,[z1,z2,z3,z4,z5,z899])],[(0,[z2,z3,z4,z900,z5,z6]),(0,[z1,z2,z3,z557,z5,z132])],[(0,[z1,z2,z901,z4,z5,z6]),(0,[z1,z2,z902,z4,z5,z6]),(0,[z1,z2,z3,z903,z5,z6]),(0,[z1,z77,z3,z408,z4,z5])],[],[(0,[z1,z2,z904,z4,z5,z6]),(0,[z1,z2,z4,z785,z5,z6]),(0,[z1,z905,z3,z4,z5,z6])],[(0,[z236,z2,z399,z4,z5,z6]),(0,[z1,z2,z4,z5,z906,z6]),(0,[z1,z2,z907,z4,z5,z6])]],
   [[(0,[z1,z2,z908,z4,z5,z6]),(0,[z1,z40,z3,z4,z5,z252]),(0,[z1,z909,z3,z4,z5,z6]),(0,[z1,z3,z910,z4,z5,z6])],[(0,[z1,z3,z4,z5,z911,z6]),(0,[z912,z2,z3,z4,z5,z6]),(0,[z1,z2,z334,z4,z5,z115])],[(0,[z1,z3,z4,z5,z6,z913])],[(0,[z914,z2,z3,z4,z5,z6]),(0,[z1,z478,z3,z4,z5,z158])],[(0,[z713,z2,z3,z4,z5,z6]),(0,[z236,z2,z3,z200,z5,z6]),(0,[z1,z126,z3,z4,z5,z76]),(0,[z1,z40,z3,z130,z4,z5])],[(0,[z1,z915,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z838,z180]),(0,[z1,z77,z3,z4,z5,z158]),(0,[z1,z376,z3,z4,z5,z73])],[(0,[z1,z2,z3,z916,z5,z6]),(0,[z1,z2,z3,z4,z5,z917]),(0,[z918,z2,z3,z4,z5,z6]),(0,[z1,z919,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z920]),(0,[z921,z2,z3,z4,z5,z6])]],
   [[(0,[z295,z2,z62,z4,z5,z6]),(0,[z1,z922,z3,z4,z5,z6]),(0,[z1,z2,z923,z3,z4,z5]),(0,[z1,z2,z3,z924,z4,z5]),(0,[z1,z126,z3,z4,z5,z9]),(0,[z1,z2,z334,z4,z5,z6]),(0,[z1,z925,z3,z4,z5,z6])],[(0,[z1,z2,z926,z4,z5,z6]),(0,[z1,z2,z927,z4,z5,z6]),(0,[z1,z928,z3,z4,z5,z6]),(0,[z929,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z930]),(0,[z55,z2,z304,z4,z5,z6]),(0,[z1,z2,z931,z4,z5,z6])],[(0,[z1,z2,z3,z4,z932,z6]),(0,[z1,z933,z3,z4,z5,z6]),(0,[z1,z2,z151,z187,z5,z6]),(0,[z2,z3,z4,z934,z5,z6]),(0,[z2,z935,z3,z4,z5,z6]),(0,[z1,z936,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z937])],[(0,[z55,z2,z450,z4,z5,z6])],[(0,[z236,z2,z7,z4,z5,z6]),(0,[z1,z508,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z938]),(0,[z1,z100,z3,z186,z5,z6]),(0,[z939,z2,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z5,z838]),(0,[z2,z3,z4,z5,z6,z940]),(0,[z1,z941,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z942,z4,z5,z6]),(0,[z1,z943,z3,z4,z5,z6]),(0,[z1,z2,z3,z197,z5,z579])],[(0,[z1,z2,z3,z5,z944,z6]),(0,[z1,z40,z3,z497,z4,z5]),(0,[z1,z2,z3,z4,z5,z945]),(0,[z147,z2,z3,z4,z5,z134])],[(0,[z1,z2,z946,z4,z5,z6])],[(0,[z947,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z948,z6]),(0,[z1,z2,z949,z4,z5,z6]),(0,[z164,z1,z2,z3,z371,z31])],[],[(0,[z1,z2,z950,z4,z5,z6]),(0,[z236,z2,z399,z47,z5,z6]),(0,[z951,z2,z3,z4,z5,z6]),(0,[z1,z2,z952,z3,z4,z5]),(0,[z1,z2,z3,z130,z4,z5])],[(0,[z1,z2,z828,z4,z5,z6])]],
   [[(0,[z1,z2,z953,z4,z5,z6]),(0,[z301,z2,z62,z4,z5,z6]),(0,[z1,z2,z954,z4,z5,z6]),(0,[z1,z2,z215,z3,z4,z5]),(0,[z1,z126,z3,z4,z5,z6]),(0,[z2,z159,z4,z63,z5,z6]),(0,[z2,z3,z4,z955,z5,z6])],[(0,[z1,z77,z415,z3,z4,z5]),(0,[z1,z2,z504,z4,z12,z6]),(0,[z1,z97,z376,z3,z4,z5])],[(0,[z1,z956,z3,z4,z5,z6]),(0,[z2,z399,z368,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z957]),(0,[z1,z2,z3,z958,z4,z5])],[(0,[z236,z2,z525,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z959]),(0,[z1,z2,z4,z5,z854,z146]),(0,[z960,z2,z3,z4,z5,z6]),(0,[z1,z2,z961,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z962,z6]),(0,[z2,z3,z4,z5,z750,z6]),(0,[z2,z963,z3,z4,z5,z6]),(0,[z1,z84,z3,z4,z616,z6]),(0,[z1,z2,z151,z964,z5,z6]),(0,[z1,z2,z965,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z966]),(0,[z295,z2,z167,z4,z5,z6]),(0,[z1,z29,z226,z4,z5,z6])],[(0,[z161,z2,z159,z4,z5,z6]),(0,[z1,z2,z3,z4,z799,z6]),(0,[z967,z2,z3,z4,z5,z6])]],
   [[(0,[z968,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z969]),(0,[z301,z2,z17,z4,z5,z6]),(0,[z1,z2,z376,z3,z4,z5])],[(0,[z1,z2,z970,z4,z5,z6])],[(0,[z164,z1,z3,z6,z73,z31]),(0,[z971,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z972,z6])],[(0,[z1,z2,z973,z4,z5,z6]),(0,[z1,z2,z974,z4,z5,z6]),(0,[z1,z2,z975,z4,z5,z6])],[(0,[z125,z2,z144,z4,z5,z6])],[(0,[z1,z2,z3,z976,z4,z5]),(0,[z1,z3,z359,z4,z20,z5])],[(0,[z1,z2,z977,z4,z5,z6]),(0,[z225,z2,z3,z4,z5,z6]),(0,[z978,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z979,z4,z5]),(0,[z1,z2,z3,z4,z731,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z115]),(0,[z1,z2,z980,z4,z5,z6])],[(0,[z1,z508,z334,z4,z5,z6])],[(0,[z2,z3,z4,z862,z5,z6]),(0,[z1,z2,z3,z4,z5,z981]),(0,[z1,z2,z982,z3,z4,z5]),(0,[z1,z44,z3,z197,z4,z5])],[(0,[z1,z2,z983,z4,z5,z6]),(0,[z984,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z985]),(0,[z1,z2,z986,z4,z5,z6]),(0,[z1,z97,z4,z5,z74,z6])],[(0,[z1,z77,z3,z359,z4,z5]),(0,[z1,z987,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z988]),(0,[z989,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z990,z6]),(0,[z1,z991,z3,z4,z5,z6]),(0,[z2,z151,z368,z63,z5,z6]),(0,[z1,z2,z3,z4,z992,z6])],[(0,[z1,z2,z3,z4,z5,z993]),(0,[z1,z994,z3,z4,z5,z6]),(0,[z281,z29,z3,z4,z5,z6]),(0,[z164,z1,z2,z376,z3,z31])]],
   [[(0,[z1,z995,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z996,z6])],[(0,[z498,z2,z62,z4,z5,z6]),(0,[z2,z3,z862,z47,z5,z6]),(0,[z997,z2,z3,z4,z5,z6]),(0,[z998,z2,z3,z4,z5,z6])],[(0,[z279,z2,z3,z4,z22,z6])],[(0,[z1,z2,z3,z752,z5,z6])],[(0,[z295,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z74,z6]),(0,[z1,z2,z3,z4,z999,z6]),(0,[z129,z1,z2,z4,z5,z854])],[(0,[z1000,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1001]),(0,[z1,z126,z3,z4,z5,z117])],[(0,[z1,z2,z3,z4,z5,z1002]),(0,[z1,z1003,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z1004,z4,z5,z6]),(0,[z1,z1005,z3,z4,z5,z6]),(0,[z1,z1006,z3,z4,z5,z6]),(0,[z147,z97,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1007]),(0,[z279,z2,z3,z4,z750,z6]),(0,[z1008,z2,z3,z4,z5,z6]),(0,[z1,z100,z3,z488,z5,z6]),(0,[z2,z1009,z3,z4,z5,z6])],[(0,[z1010,z2,z3,z4,z5,z6]),(0,[z1,z2,z1011,z4,z5,z6])],[(0,[z1,z2,z1012,z4,z5,z6]),(0,[z295,z2,z450,z4,z5,z6]),(0,[z1,z77,z3,z4,z5,z643])],[(0,[z1,z2,z4,z5,z6,z854])],[(0,[z1,z2,z194,z63,z5,z6]),(0,[z401,z2,z3,z4,z5,z838]),(0,[z1013,z2,z3,z4,z5,z6]),(0,[z1,z44,z3,z4,z5,z158]),(0,[z1,z423,z3,z197,z5,z132])],[(0,[z1,z2,z3,z4,z5,z1014]),(0,[z2,z368,z3,z4,z5,z6])],[(0,[z2,z368,z66,z4,z5,z6]),(0,[z2,z1015,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z710]),(0,[z1,z2,z3,z197,z5,z132])]],
   [[(0,[z147,z2,z3,z4,z5,z6]),(0,[z1,z2,z66,z4,z12,z6]),(0,[z164,z2,z3,z6,z136,z31])],[(0,[z1,z2,z36,z4,z5,z6]),(0,[z2,z165,z304,z4,z5,z6])],[(0,[z1,z2,z3,z862,z5,z6]),(0,[z1,z2,z4,z5,z1016,z6]),(0,[z1,z2,z3,z4,z5,z1017])],[(0,[z2,z399,z184,z4,z5,z6]),(0,[z1018,z2,z3,z4,z5,z6]),(0,[z1,z3,z497,z4,z5,z6]),(0,[z1,z2,z1019,z4,z5,z6])],[(0,[z301,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1020]),(0,[z2,z1021,z3,z4,z5,z6]),(0,[z1,z3,z185,z359,z4,z5]),(0,[z129,z1,z2,z4,z5,z146])],[(0,[z1,z2,z1022,z4,z5,z6]),(0,[z147,z2,z4,z5,z74,z6]),(0,[z1,z2,z38,z4,z5,z134])],[(0,[z1,z1023,z3,z4,z5,z6]),(0,[z1,z126,z3,z33,z4,z5])],[(0,[z1,z1024,z2,z3,z4,z6])]],
   [[(0,[z1,z100,z3,z185,z4,z5]),(0,[z2,z368,z4,z11,z5,z6])],[(0,[z2,z62,z4,z582,z5,z6]),(0,[z301,z2,z304,z4,z5,z6]),(0,[z1025,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1026]),(0,[z2,z1027,z3,z4,z5,z6]),(0,[z163,z29,z3,z4,z5,z6]),(0,[z1,z508,z3,z4,z5,z115])],[(0,[z1,z1028,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1029]),(0,[z1,z551,z3,z4,z5,z9])],[(0,[z161,z2,z7,z4,z5,z6]),(0,[z1,z100,z215,z3,z114,z5]),(0,[z2,z3,z4,z1030,z5,z6])],[(0,[z1,z2,z964,z63,z5,z6]),(0,[z1,z1031,z3,z4,z5,z6]),(0,[z1,z1032,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z731,z20])],[],[(0,[z1033,z2,z3,z4,z5,z6]),(0,[z1,z29,z3,z4,z5,z371]),(0,[z1,z3,z1034,z4,z5,z6])],[]],
   [[(0,[z86,z2,z62,z4,z5,z6]),(0,[z2,z3,z4,z209,z5,z6]),(0,[z1,z2,z3,z4,z5,z1035]),(0,[z1,z77,z3,z303,z4,z5])],[(0,[z1,z2,z1036,z4,z5,z6]),(0,[z1,z3,z1037,z4,z5,z6]),(0,[z1,z2,z1038,z4,z5,z6]),(0,[z1,z3,z130,z4,z5,z85]),(0,[z1,z2,z4,z785,z12,z6])],[(0,[z1,z2,z3,z4,z5,z1039]),(0,[z1,z3,z4,z1040,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1041]),(0,[z2,z7,z4,z5,z22,z6]),(0,[z1,z2,z3,z4,z5,z422]),(0,[z1,z1042,z3,z4,z5,z6])],[(0,[z161,z2,z368,z4,z5,z6]),(0,[z332,z2,z151,z63,z5,z6]),(0,[z1,z2,z640,z63,z5,z6]),(0,[z1043,z2,z3,z4,z5,z6]),(0,[z1,z1044,z3,z4,z5,z6])],[(0,[z1,z1045,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1046]),(0,[z1,z1047,z3,z4,z5,z6])],[(0,[z1,z84,z3,z4,z99,z6])],[(0,[z1,z2,z1048,z4,z5,z6]),(0,[z1,z1049,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z838]),(0,[z1,z3,z303,z114,z5,z6])]],
   [[(0,[z125,z2,z62,z4,z5,z6]),(0,[z35,z2,z7,z4,z5,z6]),(0,[z1050,z2,z3,z4,z5,z6]),(0,[z1051,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1052])],[(0,[z1,z2,z1053,z4,z5,z6]),(0,[z1,z2,z1054,z4,z5,z6]),(0,[z179,z2,z3,z4,z5,z838]),(0,[z1,z2,z1055,z4,z5,z6]),(0,[z1,z44,z3,z4,z5,z9])],[(0,[z1,z2,z1056,z4,z5,z6]),(0,[z401,z2,z3,z4,z5,z247])],[(0,[z1,z3,z4,z5,z799,z6])],[(0,[z1,z2,z3,z4,z5,z1057]),(0,[z179,z2,z3,z4,z5,z180]),(0,[z1,z2,z4,z5,z1058,z6]),(0,[z1059,z2,z3,z4,z5,z6]),(0,[z1,z3,z497,z4,z148,z5])],[(0,[z1,z2,z3,z4,z5,z1060]),(0,[z1,z2,z399,z4,z5,z6])],[(0,[z2,z62,z4,z629,z5,z6])],[(0,[z1,z77,z3,z4,z5,z69]),(0,[z1,z3,z497,z4,z5,z132])]],
   [[(0,[z1061,z2,z3,z4,z5,z6]),(0,[z1,z77,z3,z4,z5,z76]),(0,[z1,z1062,z3,z4,z5,z6])],[(0,[z1,z2,z1063,z4,z5,z6])],[(0,[z1,z2,z525,z4,z5,z6]),(0,[z1,z2,z3,z4,z1064,z6]),(0,[z25,z1,z828,z4,z5,z6])],[(0,[z1,z2,z1065,z3,z4,z5])],[(0,[z1,z3,z4,z157,z5,z69]),(0,[z1,z100,z3,z114,z5,z69]),(0,[z1,z3,z4,z5,z782,z6])],[(0,[z1,z2,z3,z4,z5,z1066]),(0,[z1,z2,z3,z1067,z4,z5]),(0,[z1,z2,z3,z4,z5,z302]),(0,[z1,z3,z4,z157,z5,z76]),(0,[z1,z2,z3,z197,z186,z5])],[(0,[z1068,z2,z3,z4,z5,z6])],[(0,[z2,z7,z159,z4,z5,z6]),(0,[z25,z1,z26,z4,z5,z6]),(0,[z1,z29,z3,z4,z5,z6])]],
   [[(0,[z164,z1,z2,z38,z6,z31]),(0,[z1,z2,z38,z376,z4,z5])],[(0,[z1,z2,z1069,z4,z5,z6]),(0,[z1,z3,z1070,z4,z5,z6]),(0,[z1,z3,z4,z114,z5,z69])],[(0,[z1,z3,z4,z114,z5,z76]),(0,[z1,z2,z66,z4,z412,z6]),(0,[z1,z2,z3,z4,z5,z1071]),(0,[z2,z3,z4,z1072,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6]),(0,[z1,z3,z4,z799,z85,z6]),(0,[z281,z2,z226,z4,z5,z6])],[(0,[z236,z2,z3,z629,z5,z6]),(0,[z1,z2,z4,z964,z5,z6]),(0,[z1,z97,z38,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1073]),(0,[z291,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z1074,z4,z5]),(0,[z1,z3,z130,z145,z4,z5]),(0,[z1,z2,z3,z4,z5,z782]),(0,[z164,z1,z2,z334,z6,z31])],[(0,[z1,z2,z1075,z4,z5,z6]),(0,[z2,z304,z4,z47,z5,z6]),(0,[z1,z1076,z3,z4,z5,z6]),(0,[z2,z368,z149,z4,z5,z6])],[(0,[z1,z2,z3,z964,z5,z6])]],
   [[(0,[z1077,z2,z3,z4,z5,z6]),(0,[z1078,z2,z3,z4,z5,z6]),(0,[z1,z284,z3,z4,z5,z6])],[(0,[z1,z64,z3,z185,z4,z5]),(0,[z1,z3,z4,z1079,z5,z6]),(0,[z301,z2,z167,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z5,z1080]),(0,[z1,z2,z759,z4,z5,z6])],[(0,[z2,z304,z4,z34,z5,z6]),(0,[z2,z3,z4,z5,z247,z838]),(0,[z1,z84,z3,z4,z5,z69]),(0,[z1,z2,z1081,z3,z4,z5]),(0,[z1,z2,z38,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1082]),(0,[z125,z2,z4,z5,z529,z6]),(0,[z1,z84,z3,z4,z5,z76]),(0,[z147,z2,z376,z3,z4,z5]),(0,[z1,z44,z53,z3,z4,z5]),(0,[z1,z1083,z3,z4,z5,z6])],[(0,[z1,z2,z1084,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1085]),(0,[z1,z2,z3,z1086,z4,z5]),(0,[z1087,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z1088,z5,z6]),(0,[z1,z2,z1089,z4,z5,z6]),(0,[z1,z2,z3,z1090,z4,z5]),(0,[z1,z1091,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z151,z629,z5,z6]),(0,[z1092,z2,z3,z4,z5,z6]),(0,[z1,z1093,z3,z4,z5,z6])],[(0,[z2,z759,z62,z4,z5,z6]),(0,[z1,z100,z3,z114,z5,z6]),(0,[z1,z3,z752,z114,z5,z6]),(0,[z1,z2,z4,z5,z6,z1094])],[(0,[z1,z1095,z3,z4,z5,z6]),(0,[z1,z1096,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1097]),(0,[z2,z3,z4,z5,z6,z1098]),(0,[z1,z357,z3,z4,z85,z6])],[(0,[z1,z1099,z3,z4,z5,z6]),(0,[z1,z2,z151,z63,z5,z6])],[(0,[z279,z2,z304,z4,z5,z6])],[(0,[z2,z159,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1100,z6]),(0,[z1101,z2,z3,z4,z5,z6])],[(0,[z279,z2,z450,z4,z5,z6]),(0,[z2,z159,z66,z4,z5,z6])],[(0,[z1,z1102,z2,z3,z4,z5]),(0,[z2,z3,z1103,z4,z5,z6]),(0,[z2,z3,z4,z5,z1104,z6]),(0,[z1,z2,z1105,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 460).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 920).take 116) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1036)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [460, 460, 116] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 200).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 200).take 56).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [200, 56] = true :=
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

end PEqualNP.Outside.L_meta_36641

theorem PEqualNP.Outside.L_meta_36641 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 3970476168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 3970476168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36641.solve