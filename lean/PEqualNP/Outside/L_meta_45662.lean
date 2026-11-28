import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45662

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
  Nat.testBit (4008241824 * 2 ^ 32 + 3938494976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00086e056c2bc2a8#64 ++ 0x00010dc0ad857855#64 ++ 0xfa18fe1ffc7fc7ff#64 ++ 0xff431fc3ff8ff8ff#64 : BitVec 256),
   (0x38e316ece198de62#64 ++ 0x071c62dd9c331bcc#64 ++ 0xfde71fece399fe65#64 ++ 0x9fbce3fd9c733fcc#64 : BitVec 256),
   (0x8605a170b6e16f81#64 ++ 0x10c0b42e16dc2df0#64 ++ 0xbe07e1f0ffe1ff81#64 ++ 0xd7c0fc3e1ffc3ff0#64 : BitVec 256),
   (0x4f7001ba03d40550#64 ++ 0x09ee0037407a80aa#64 ++ 0xdff801ff03fe07fe#64 ++ 0xfbff003fe07fc0ff#64 : BitVec 256),
   (0x67befa00037fb000#64 ++ 0xacf7df40006ff600#64 ++ 0xeffffe0003fff807#64 ++ 0x1dffffc0007fff00#64 : BitVec 256),
   (0x97dfdddfd8000000#64 ++ 0x72fbfbbbfb000000#64 ++ 0xf7fffffffc000000#64 ++ 0x1effffffff800000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [9, 2]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [9, 2]⟩, ⟨.and, [8, 12]⟩, ⟨.and, [13, 5]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00086e056c2bc2a8 0x00010dc0ad857855 0xfa18fe1ffc7fc7ff 0xff431fc3ff8ff8ff

def z1 : W := mkw 0x0020000001100000 0x0004000000220000 0xcde0000003980004 0x19bc000000730000

def z2 : W := mkw 0x20a2120001189000 0x0414424000231200 0xede71e000399f805 0x1dbce3c000733f00

def z3 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0xfde71fece399fe65 0x9fbce3fd9c733fcc

def z4 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z5 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z6 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0xf7fffffffc000000 0x1effffffff800000

def z7 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0xeffffe0003fff807 0x1dffffc0007fff00

def z8 : W := mkw 0x8605a150b4216a81 0x10c0b42a16842d50 0xb607e1f0fc01f801 0x16c0fc3e1f803f00

def z9 : W := mkw 0x968ffd75fee16f81 0x72d1ffaebfdc2df0 0xbe07fff0ffe1ff81 0xd7c0fffe1ffc3ff0

def z10 : W := mkw 0x000868010c230088 0x00010d0021846011 0x0218e0131c66019a 0x60431c02638cc033

def z11 : W := mkw 0x10c316cce008c220 0x021862d99c011844 0xfde71fece019c665 0x9fbce3fd9c0338cc

def z12 : W := mkw 0x0082100000000000 0x0010420000000000 0xe5e71e0000000000 0x1cbce3c000000000

def z13 : W := mkw 0x10c314ccc0000000 0x0218629998000000 0xf5e71fece0000000 0x1ebce3fd9c000000

def z14 : W := mkw 0xbfffdffff998de62 0x77fffbffff331bcc 0xffffffffff99fe65 0x9ffffffffff33fcc

def z15 : W := mkw 0x0604a00002612000 0x00c09400004c2400 0xae07e00003e1f801 0x15c0fc00007c3f00

def z16 : W := mkw 0x079ed80000000000 0x20f3db0000000000 0xe7fffe0000000000 0x1cffffc000000000

def z17 : W := mkw 0x10cb5ccdc8000000 0x02196b99b9000000 0xf7fffffffc000000 0x1effffffff800000

def z18 : W := mkw 0x184104ece0804e62 0x0308209d9c1009cc 0x100001ece0000660 0x8200003d9c0000cc

def z19 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0x05e001e003800000 0x00bc003c00700000

def z20 : W := mkw 0x90494ddfd8000000 0x520929bbfb000000 0xf218fffffc000000 0x1e431fffff800000

def z21 : W := mkw 0x871cc91318000000 0x70e3992263000000 0x0218e0131c000000 0x00431c0263800000

def z22 : W := mkw 0x0600013002c00500 0x00c00026005800a0 0x9e0001f003e00780 0xd3c0003e007c00f0

def z23 : W := mkw 0xcf75a1fab7f56fd1 0x19eeb43f56feadfa 0xffffe1ffffffffff 0xfffffc3fffffffff

def z24 : W := mkw 0x60202200037fb000 0x8c040440006ff600 0x0800000003fff807 0x01000000007fff00

def z25 : W := mkw 0x904105dfd8000000 0x520820bbfb000000 0x100001fffc000000 0x0200003fff800000

def z26 : W := mkw 0x086000a801900440 0x010c001500320088 0xdde001ec03980664 0x9bbc003d807300cc

def z27 : W := mkw 0x471ce80002672000 0xa8e39d00004ce400 0x0218e00000660002 0x00431c00000cc000

def z28 : W := mkw 0x8005a040b4216a81 0x1000b40816842d50 0x2007e000fc01f801 0x0400fc001f803f00

def z29 : W := mkw 0x0750019a00000000 0x00ea003340000000 0xd7f801ff00000000 0x1aff003fe0000000

def z30 : W := mkw 0xdfffddffdbd40550 0x7bfffbbffb7a80aa 0xfffffffffffe07fe 0xffffffffffffc0ff

def z31 : W := mkw 0xdff791fa93d40550 0x7bfef23f527a80aa 0x05e701e003800000 0x00bce03c00700000

def z32 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0x25e7ffe0fc000000 0x04bcfffc1f800000

def z33 : W := mkw 0x00084a00000a8000 0x0001094000015000 0x40181e00001e0006 0x080303c00003c000

def z34 : W := mkw 0x4f7ce9ba03f72550 0xa9ef9d37407ee4aa 0xdff8e1ff03fe07fe 0xfbff1c3fe07fc0ff

def z35 : W := mkw 0x00086a00002b8000 0x00010d4000057000 0x2000fe000001c001 0x04001fc000003800

def z36 : W := mkw 0xe7bffb70b7ffff81 0xbcf7ff6e16fffff0 0xfffffff0ffffff87 0xdffffffe1ffffff0

def z37 : W := mkw 0x30831644e008da22 0x061062c89c011b44 0x20071e00e001f801 0x0400e3c01c003f00

def z38 : W := mkw 0x38eb7eededbbdeea 0x071d6fddbdb77bdd 0xffffffffffffffff 0xffffffffffffffff

def z39 : W := mkw 0x4714800002442000 0xa8e2900000488400 0x0000000000000000 0x0000000000000000

def z40 : W := mkw 0x0008480108000000 0x0001090021000000 0x0218e0131c000000 0x00431c0263800000

def z41 : W := mkw 0x5f7105fee3d44f72 0x0bee20bfdc7a89ee 0xdff801ffe3fe07fe 0xfbff003ffc7fc0ff

def z42 : W := mkw 0x61befa00013fb000 0xac37df400027f600 0x61fffe00001ff807 0x0c3fffc00003ff00

def z43 : W := mkw 0x908fdc45d8000000 0x7211fb88bb000000 0x2007fe00fc000000 0x0400ffc01f800000

def z44 : W := mkw 0x97dfffdffc2bc2a8 0x72fbfffbff857855 0xfffffffffc7fc7ff 0xffffffffff8ff8ff

def z45 : W := mkw 0x1840048c40000062 0x030800918800000c 0x0000000c00000060 0x000000018000000c

def z46 : W := mkw 0x8604a11016612181 0x10c0942202cc2430 0xae07e0101fe1f981 0x55c0fc0203fc3f30

def z47 : W := mkw 0x208efa00002bb000 0xa411df4000057600 0x2007fe000001f801 0x0400ffc000003f00

def z48 : W := mkw 0x00084e05480a8028 0x000109c0a9015005 0x40181e0f001e007e 0x280303c1e003c00f

def z49 : W := mkw 0x860def75feebefa9 0x10c1bdeebfdd7df5 0xfe1fffffffffffff 0xffc3ffffffffffff

def z50 : W := mkw 0xa6a7b370b7f9ff81 0x14d4f66e16ff3ff0 0xffe7fff0fff9ff85 0xdffcfffe1fff3ff0

def z51 : W := mkw 0x00010060a0804e00 0x0000200c141009c0 0xbc0701e0e381fe01 0x9780e03c1c703fc0

def z52 : W := mkw 0x00012060a6e16f81 0x0000240c14dc2df0 0xbc0701e0e3e1ff81 0xd780e03c1c7c3ff0

def z53 : W := mkw 0x000004056c0042a8 0x00000080ad800855 0x1000001ffc0007f8 0xe2000003ff8000ff

def z54 : W := mkw 0x38e312e881989c42 0x071c625d10331388 0xede71fe00399f805 0x1dbce3fc00733f00

def z55 : W := mkw 0x0604800002402000 0x00c0900000480400 0x0407000003803800 0x0080e00000700700

def z56 : W := mkw 0x0796900000000000 0x20f2d20000000000 0x05e7000000000000 0x00bce00000000000

def z57 : W := mkw 0x2082120000089000 0x0410424000011200 0x20071e000001f801 0x0400e3c000003f00

def z58 : W := mkw 0x61ba5a00011e9000 0xac374b400023d200 0x41f81e00001e0006 0x083f03c00003c000

def z59 : W := mkw 0x80010170b4804f81 0x1000202e169009f0 0x100001f0fc000780 0xc200003e1f8000f0

def z60 : W := mkw 0x086000a801900440 0x010c001500320088 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z61 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z62 : W := mkw 0x471ce91202672110 0xa8e39d22404ce422 0x0218e0130066019a 0x60431c02600cc033

def z63 : W := mkw 0x0000000020004200 0x0000000004000840 0xb8000000e001c601 0x970000001c0038c0

def z64 : W := mkw 0x0000002002c02d01 0x00000004005805a0 0x0000000003803800 0x0000000000700700

def z65 : W := mkw 0x471ce80002672000 0xa8e39d00004ce400 0xae1fe00003e7f803 0x15c3fc00007cff00

def z66 : W := mkw 0x00086e056c2bc2a8 0x00010dc0ad857855 0xea18fe00fc7fc007 0x1d431fc01f8ff800

def z67 : W := mkw 0x000ce80000232000 0xa0019d0000046400 0x0000e00000000000 0x00001c0000000000

def z68 : W := mkw 0x67bef80003773000 0xacf7df00006ee600 0x07ffe00003e63802 0x00fffc00007cc700

def z69 : W := mkw 0x0000011200000110 0x0000002240000022 0x0000001300000198 0x6000000260000033

def z70 : W := mkw 0x8604a11016612181 0x10c0942202cc2430 0x0200e0101c600180 0x40401c02038c0030

def z71 : W := mkw 0xe7befb10177fb181 0xbcf7df6202eff630 0xeffffe101ffff987 0x5dffffc203ffff30

def z72 : W := mkw 0x079ef80002612000 0x20f3df00004c2400 0xeffffe0003e1f801 0x1dffffc0007c3f00

def z73 : W := mkw 0x0000202026e16f81 0x0000040404dc2df0 0x0800000003e1ff81 0xc1000000007c3ff0

def z74 : W := mkw 0x11da5c8f48000000 0x623b4b91e9000000 0x41f81e0f00000000 0x083f03c1e0000000

def z75 : W := mkw 0x0000000000000000 0x0000000000000000 0xda18001f007e07fe 0xfb430003e00fc0ff

def z76 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0x25e71fe0e381f801 0x04bce3fc1c703f00

def z77 : W := mkw 0x67befe056f7ff2a8 0xacf7dfc0adeffe55 0xfffffe1fffffffff 0xffffffc3ffffffff

def z78 : W := mkw 0x67b6900003543000 0xacf6d200006a8600 0x05e7000003803800 0x00bce00000700700

def z79 : W := mkw 0x4ffed9ba03d40550 0x29ffdb37407a80aa 0xffffffff03fe07fe 0xffffffffe07fc0ff

def z80 : W := mkw 0xcf7defffffffeff9 0x19efbdfffffffdff 0xffffffffffffffff 0xffffffffffffffff

def z81 : W := mkw 0x97d791da90000000 0x72faf23b52000000 0xd7ff01ff00000000 0x1affe03fe0000000

def z82 : W := mkw 0x7ff317fee3dcdf72 0x0ffe62ffdc7b9bee 0xffff1fffe3ffffff 0xffffe3fffc7fffff

def z83 : W := mkw 0x97dffdfffee16f81 0x72fbffbfffdc2df0 0xffffffffffe1ff81 0xdffffffffffc3ff0

def z84 : W := mkw 0x2820002001901c42 0x0504000400320388 0x0000000003803800 0x0000000000700700

def z85 : W := mkw 0x8605817092c02d01 0x10c0b02e125805a0 0x040701e003803800 0x0080e03c00700700

def z86 : W := mkw 0x00084c0548000000 0x00010980a9000000 0xf218fe1ffc000000 0x1e431fc3ff800000

def z87 : W := mkw 0x97d791da90000000 0x72faf23b52000000 0x05e701e000000000 0x00bce03c00000000

def z88 : W := mkw 0x20a2120001189000 0x0414424000231200 0x41e01e0000180004 0x083c03c000030000

def z89 : W := mkw 0x000006046008c220 0x000000c08c011844 0x20001e00e001c001 0x040003c01c003800

def z90 : W := mkw 0x0000200024214280 0x0000040004842850 0x080000000061c781 0xc1000000000c38f0

def z91 : W := mkw 0x77fffeccc37fb000 0xaeffffd9986ff600 0xffffffece3fff807 0x1ffffffd9c7fff00

def z92 : W := mkw 0x69fa5a8a011e9050 0xad3f4b514023d20a 0x41f81e0f001e007e 0x283f03c1e003c00f

def z93 : W := mkw 0x904105fffc804f81 0x520820bfff9009f0 0x100001fffc000780 0xc200003fff8000f0

def z94 : W := mkw 0x4820222027ffc7f8 0x0904044404fff8ff 0x0800000003ffc7ff 0xe1000000007ff8ff

def z95 : W := mkw 0x0000200024214280 0x0000040004842850 0xba00e010fc61c781 0xd7401c021f8c38f0

def z96 : W := mkw 0x4710011202440110 0x08e2002240488022 0x021800130066019a 0x60430002600cc033

def z97 : W := mkw 0x9fdfddfff8804e62 0x73fbfbbfff1009cc 0xf7fffffffc000660 0x9effffffff8000cc

def z98 : W := mkw 0x4970008a01140050 0x092e00114022800a 0x41f8000f001e007e 0x283f0001e003c00f

def z99 : W := mkw 0xf7ffdfdfd91e9000 0xfefffbfbfb23d200 0xf7fffffffc1e0006 0x1effffffff83c000

def z100 : W := mkw 0x0000020000088000 0x0000004000011000 0xe8001e000019c005 0x1d0003c000033800

def z101 : W := mkw 0x67befa010f7fb088 0xacf7df4021eff611 0xeffffe131ffff99f 0x7dffffc263ffff33

def z102 : W := mkw 0x61ba5a00011e9000 0xac374b400023d200 0xedff1e00039ff807 0x1dbfe3c00073ff00

def z103 : W := mkw 0x30e316ccc1189000 0x061c62d998231200 0xfde71fece399f805 0x1fbce3fd9c733f00

def z104 : W := mkw 0xf7ffffdfdb7fb000 0xfefffffbfb6ff600 0xfffffffffffff807 0x1fffffffffffff00

def z105 : W := mkw 0x00084e05480a8028 0x000109c0a9015005 0x00001e0000000000 0x000003c000000000

def z106 : W := mkw 0x4820002003d40550 0x09040004007a80aa 0xda18001f03fe07fe 0xfb430003e07fc0ff

def z107 : W := mkw 0x8605815090000000 0x10c0b02a12000000 0xb607e1f0fc000000 0x16c0fc3e1f800000

def z108 : W := mkw 0x0001006080800c00 0x0000200c10100180 0x040701e003803800 0x0080e03c00700700

def z109 : W := mkw 0x00002200002b8000 0x0000044000057000 0x08000000007fc007 0x01000000000ff800

def z110 : W := mkw 0x38e316ecc1989c62 0x071c62dd9833138c 0x45e71fec03983864 0x08bce3fd8073070c

def z111 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0x45ff1fef00000000 0x08bfe3fde0000000

def z112 : W := mkw 0x0040008800000000 0x0008001100000000 0xd5e001ec00000000 0x1abc003d80000000

def z113 : W := mkw 0x6820222003ffb550 0x8d040444007ff6aa 0x0800000003ffffff 0xe1000000007fffff

def z114 : W := mkw 0x30831664e088de22 0x061062cc9c111bc4 0xbc071fe0e381fe01 0x9780e3fc1c703fc0

def z115 : W := mkw 0x67bffa60a3fffe00 0xacf7ff4c147fffc0 0xffffffe0e3fffe07 0x9ffffffc1c7fffc0

def z116 : W := mkw 0xe7befb131b7fb000 0xfcf7df62636ff600 0xeffffe131ffff807 0x1dffffc263ffff00

def z117 : W := mkw 0x00086c056c2342a8 0x00010d80ad846855 0x1218e01ffc6607fa 0xe2431c03ff8cc0ff

def z118 : W := mkw 0x7ffffeece3fffe62 0xafffffdd9c7fffcc 0xffffffece3fffe67 0x9ffffffd9c7fffcc

def z119 : W := mkw 0x96c795dcd0000000 0x12d8f2bb9a000000 0xf7e7fffcfc000000 0x1efcffff9f800000

def z120 : W := mkw 0xbee7b7fcf7f9ffe3 0x17dcf6ff9eff3ffc 0xffe7fffcfff9ffe5 0xdffcffff9fff3ffc

def z121 : W := mkw 0xa68ffb70b6ebff81 0xb4d1ff6e16dd7ff0 0xbe07fff0ffe1ff81 0xd7c0fffe1ffc3ff0

def z122 : W := mkw 0x67ba5a00035e9000 0xacf74b40006bd200 0xcff81e0003fe0006 0x19ff03c0007fc000

def z123 : W := mkw 0x8004a00014212081 0x1000940002842410 0x0000e0001c000000 0x00001c0003800000

def z124 : W := mkw 0x6820022023dcdf72 0x0d040044047b9bee 0x0800000003ffffff 0xe1000000007fffff

def z125 : W := mkw 0xf7bffe45db7fb000 0xfef7ffc8bb6ff600 0xeffffe00fffff807 0x1dffffc01fffff00

def z126 : W := mkw 0x86058170b2c06f01 0x10c0b02e16580de0 0xbc0701e0e381fe01 0x9780e03c1c703fc0

def z127 : W := mkw 0x00086e056c2bc2a8 0x00010dc0ad857855 0x2000fe00fc01c001 0x04001fc01f803800

def z128 : W := mkw 0x908ffe45fc2bc2a8 0x7211ffc8bf857855 0x2007fe00fc01c001 0x0400ffc01f803800

def z129 : W := mkw 0x38e2168c41189062 0x071c42d18823120c 0x41e01e0c00180064 0x083c03c18003000c

def z130 : W := mkw 0x000868012c234288 0x00010d0025846851 0xba18e013fc67c79b 0xf7431c027f8cf8f3

def z131 : W := mkw 0x471cea00026fa000 0xa8e39d40004df400 0xea18fe00007fc007 0x1d431fc0000ff800

def z132 : W := mkw 0x0000000000000000 0x0000000000000000 0x4018000f001e007e 0x28030001e003c00f

def z133 : W := mkw 0x38e316cce118da62 0x071c62d99c231b4c 0x61e71e0ce019f865 0x0c3ce3c19c033f0c

def z134 : W := mkw 0x6ffefa8a037fb050 0xadffdf51406ff60a 0xeffffe0f03fff87f 0x3dffffc1e07fff0f

def z135 : W := mkw 0x11da7e8f6c2bc2a8 0x623b4fd1ed857855 0xfbf8fe1ffc7fc7ff 0xff7f1fc3ff8ff8ff

def z136 : W := mkw 0x38e310e881901c42 0x071c621d10320388 0x05e701e003803800 0x00bce03c00700700

def z137 : W := mkw 0x79f2168e411c9072 0x0f3e42d1c823920e 0x41f81e0f001e007e 0x283f03c1e003c00f

def z138 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0x1200e1f0fc600780 0xc2401c3e1f8c00f0

def z139 : W := mkw 0xbee791f893d03d43 0x17dcf23f127a07a8 0x05e701e003803800 0x00bce03c00700700

def z140 : W := mkw 0x71fa5e8f491e9000 0xee3f4bd1e923d200 0x41f81e0f001e0006 0x083f03c1e003c000

def z141 : W := mkw 0x8605817092c02d01 0x10c0b02e125805a0 0x9e0701f003e03f80 0xd3c0e03e007c07f0

def z142 : W := mkw 0x38e314ecc1901c42 0x071c629d98320388 0xf5e71fece3803800 0x1ebce3fd9c700700

def z143 : W := mkw 0x20a31260a198de00 0x0414624c14331bc0 0xfde71fe0e399fe05 0x9fbce3fc1c733fc0

def z144 : W := mkw 0x964585dfd8000000 0x52c8b0bbfb000000 0xb607e1fffc000000 0x16c0fc3fff800000

def z145 : W := mkw 0x67b6900003543000 0xacf6d200006a8600 0xcfff000003fe3806 0x19ffe000007fc700

def z146 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0x0c0701e003e1ff81 0xc180e03c007c3ff0

def z147 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0x2407e1e0ff81f801 0x0480fc3c1ff03f00

def z148 : W := mkw 0x38eb7eece1bbde62 0x071d6fdd9c377bcc 0xffffffece3fffe67 0x9ffffffd9c7fffcc

def z149 : W := mkw 0x60202200277ff2a8 0x8c04044004effe55 0x0800000003ffffff 0xe1000000007fffff

def z150 : W := mkw 0x984105fcf4804fe3 0x130820bf9e9009fc 0x100001fcfc0007e0 0xc200003f9f8000fc

def z151 : W := mkw 0x86058170b0804e00 0x10c0b02e161009c0 0xbe07e1f0ff81fe01 0x97c0fc3e1ff03fc0

def z152 : W := mkw 0x9fdfddffd8800550 0x73fbfbbffb1000aa 0xf7fffffffc0007f8 0xfeffffffff8000ff

def z153 : W := mkw 0x30831644e008da22 0x061062c89c011b44 0xf8071e0ce019fe65 0x9f00e3c19c033fcc

def z154 : W := mkw 0x0000040460004220 0x000000808c000844 0x1000000ce0000660 0x820000019c0000cc

def z155 : W := mkw 0x208efa00002bb000 0xa411df4000057600 0xea1ffe00007ff807 0x1d43ffc0000fff00

def z156 : W := mkw 0x0710011200000000 0x00e2002240000000 0x0218001300000000 0x0043000260000000

def z157 : W := mkw 0x4820002003d40550 0x09040004007a80aa 0x0800000003fe07fe 0xe1000000007fc0ff

def z158 : W := mkw 0x61ba7e056d3fd2a8 0xac374fc0ada7fa55 0xfbf8fe1ffc7fc7ff 0xff7f1fc3ff8ff8ff

def z159 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0xfe1fe1ffffffffff 0xffc3fc3fffffffff

def z160 : W := mkw 0x084000a800800440 0x0108001500100088 0x100001ec00000660 0x8200003d800000cc

def z161 : W := mkw 0x104104ccc0000000 0x0208209998000000 0x100001ece0000000 0x0200003d9c000000

def z162 : W := mkw 0x00086e054c2b80a8 0x00010dc0a9857015 0x4218fe1f1c7e01fe 0x68431fc3e38fc03f

def z163 : W := mkw 0x38e2168c6118d262 0x071c42d18c231a4c 0xf9e01e0ce019c665 0x9f3c03c19c0338cc

def z164 : W := mkw 0x8605815090000000 0x10c0b02a12000000 0x040701e000000000 0x0080e03c00000000

def z165 : W := mkw 0x4f7000a803d40440 0x09ee0015007a8088 0xdff801ec03fe0666 0x9bff003d807fc0cc

def z166 : W := mkw 0x90cfdddfd8000000 0x7219fbbbfb000000 0x3007fffffc000000 0x0600ffffff800000

def z167 : W := mkw 0x4f784dbf4bd40550 0x09ef09b7e97a80aa 0xfff8fffffffe07fe 0xffff1fffffffc0ff

def z168 : W := mkw 0x00002200242bc2a8 0x0000044004857855 0x08000000007fc7ff 0xe1000000000ff8ff

def z169 : W := mkw 0x8e45a1fab6e16fd1 0x11c8b43f56dc2dfa 0xbe07e1ffffe1fff9 0xf7c0fc3ffffc3fff

def z170 : W := mkw 0xdffffdfffff56fd1 0x7bffffbffffeadfa 0xffffffffffffffff 0xffffffffffffffff

def z171 : W := mkw 0xc715a172b6e56f91 0x18e2b42e56dcadf2 0xbe1fe1f3ffe7ff9b 0xf7c3fc3e7ffcfff3

def z172 : W := mkw 0x0001004080000000 0x0000200810000000 0xb40701e0e0000000 0x1680e03c1c000000

def z173 : W := mkw 0x0000000000000000 0x0000000000000000 0xd218001f00000000 0x1a430003e0000000

def z174 : W := mkw 0x4f786fbf6fffc7f8 0x09ef0df7edfff8ff 0xfff8ffffffffc7ff 0xffff1ffffffff8ff

def z175 : W := mkw 0x086006ac6198c660 0x010c00d58c3318cc 0xfde01fece399c665 0x9fbc03fd9c7338cc

def z176 : W := mkw 0x67b6b00003753000 0xacf6d600006ea600 0xafe7e00003e1f801 0x15fcfc00007c3f00

def z177 : W := mkw 0x47bed80003540000 0x28f7db00006a8000 0xeffffe0003fe0006 0x1dffffc0007fc000

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0xb200e010fc000000 0x16401c021f800000

def z179 : W := mkw 0x200002002008da22 0x0400004004011b44 0x000000000001f801 0x0000000000003f00

def z180 : W := mkw 0x00086e056c2bc2a8 0x00010dc0ad857855 0x6018fe0ffc1fc07f 0x2c031fc1ff83f80f

def z181 : W := mkw 0x8001015090000000 0x1000202a12000000 0x100001f0fc000000 0x0200003e1f800000

def z182 : W := mkw 0x000006046008c220 0x000000c08c011844 0xf8001e0ce019c665 0x9f0003c19c0338cc

def z183 : W := mkw 0x90cfdccdd8000000 0x7219fb99bb000000 0xf5e7ffecfc000000 0x1ebcfffd9f800000

def z184 : W := mkw 0x984105fff8804e62 0x530820bfff1009cc 0x100001fffc000660 0x8200003fff8000cc

def z185 : W := mkw 0x000004056c0042a8 0x00000080ad800855 0xda18001ffc7e07fe 0xfb430003ff8fc0ff

def z186 : W := mkw 0x80096f75fcabcfa9 0x10012deebf9579f5 0xfa18fffffc7fc7ff 0xff431fffff8ff8ff

def z187 : W := mkw 0x10cb7ecdec2bc2a8 0x02196fd9bd857855 0xfffffffffc7fc7ff 0xffffffffff8ff8ff

def z188 : W := mkw 0x0000040548000028 0x00000080a9000005 0x0000000f00000078 0x20000001e000000f

def z189 : W := mkw 0x7ff790e883d43c42 0xaffef21d107a8788 0x05e701e003803800 0x00bce03c00700700

def z190 : W := mkw 0x07584d9f48000000 0x00eb09b3e9000000 0xf7f8fffffc000000 0x1eff1fffff800000

def z191 : W := mkw 0x0750019a00000000 0x00ea003340000000 0xdff801ff007e07fe 0xfbff003fe00fc0ff

def z192 : W := mkw 0x4f30013203d40550 0x09e60026407a80aa 0x0a18001303fe07fe 0xe1430002607fc0ff

def z193 : W := mkw 0x90496fdffc2bc2a8 0x52092dfbff857855 0xfa18fffffc7fc7ff 0xff431fffff8ff8ff

def z194 : W := mkw 0x4710011202440110 0x08e2002240488022 0x0000000000000000 0x0000000000000000

def z195 : W := mkw 0x975dcddfd8000000 0x72ebb9bbfb000000 0x1218e1fffc000000 0x02431c3fff800000

def z196 : W := mkw 0x28e212a801989440 0x051c425500331288 0xfde71fec0399fe65 0x9fbce3fd80733fcc

def z197 : W := mkw 0x6ffefbba03ffb550 0xadffdf77407ff6aa 0xffffffff03ffffff 0xffffffffe07fffff

def z198 : W := mkw 0x39fb5eefe998de62 0x673f6bddfd331bcc 0xfdff1fefe399fe65 0x9fbfe3fdfc733fcc

def z199 : W := mkw 0x17d315dec0000000 0x02fa62bbd8000000 0xf7ff1fffe0000000 0x1effe3fffc000000

def z200 : W := mkw 0x6ff213ba03dc9550 0x0dfe4277407b92aa 0xffff1fff03ffffff 0xffffe3ffe07fffff

def z201 : W := mkw 0x26a6b2000379b000 0x04d4d640006f3600 0xefe7fe0003f9f805 0x1dfcffc0007f3f00

def z202 : W := mkw 0x20aa7e056d3bd2a8 0x04154fc0ada77a55 0xfffffe1fffffffff 0xffffffc3ffffffff

def z203 : W := mkw 0x0118480308000000 0x6023090061000000 0x0018000300000000 0x0003000060000000

def z204 : W := mkw 0xbff797fef198de62 0x77fef2ffde331bcc 0xfde71fece399fe65 0x9fbce3fd9c733fcc

def z205 : W := mkw 0x00084e056c0ac2a8 0x000109c0ad815855 0x50181e1ffc1e07fe 0xea0303c3ff83c0ff

def z206 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0x07f801f303e6019a 0x60ff003e607cc033

def z207 : W := mkw 0x7ff317fee3dcdf72 0x0ffe62ffdc7b9bee 0xfde71fece399fe65 0x9fbce3fd9c733fcc

def z208 : W := mkw 0x38e310e8a1905e42 0x071c621d14320bc8 0xbde701e0e381fe01 0x97bce03c1c703fc0

def z209 : W := mkw 0x3ee7b6ece3f9fe62 0x07dcf6dd9c7f3fcc 0xffe7ffece3f9fe65 0x9ffcfffd9c7f3fcc

def z210 : W := mkw 0x97dfffdfd82b8000 0x72fbfffbfb057000 0xfffffffffc7fc007 0x1fffffffff8ff800

def z211 : W := mkw 0xe7b7b170b7f57f81 0xbcf6f62e16feaff0 0xbfe7e1f0ffe1ff81 0xd7fcfc3e1ffc3ff0

def z212 : W := mkw 0x11d2108a00000000 0x623a421140000000 0x01e0000000000000 0x003c000000000000

def z213 : W := mkw 0x8605a15092612000 0x10c0b42a124c2400 0xbe07e1f0ffe1f801 0x17c0fc3e1ffc3f00

def z214 : W := mkw 0x61ba7a00037fb000 0xac374f40006ff600 0x49f81e0003fff807 0x093f03c0007fff00

def z215 : W := mkw 0x8714811210000000 0x70e2902242000000 0x0000000000000000 0x0000000000000000

def z216 : W := mkw 0x61b2100001141000 0xac36420000228200 0x01e0000000000000 0x003c000000000000

def z217 : W := mkw 0x97d7b1fab6e16f81 0x72faf63f56dc2df0 0xbfe7e1f0ffe1ff81 0xd7fcfc3e1ffc3ff0

def z218 : W := mkw 0x875cc99b18000000 0x70eb993363000000 0xd7f8e1ff1c000000 0x1aff1c3fe3800000

def z219 : W := mkw 0x00010060a0804e00 0x0000200c141009c0 0x100001e0e0000600 0x8200003c1c0000c0

def z220 : W := mkw 0x00086e056c2bc2a8 0x00010dc0ad857855 0xf218fe1ffc01c001 0x1e431fc3ff803800

def z221 : W := mkw 0x30c316cce008da22 0x061862d99c011b44 0xf5e71fece001f801 0x1ebce3fd9c003f00

def z222 : W := mkw 0x00086e05482b8028 0x00010dc0a9057005 0xea18fe0f007fc07f 0x3d431fc1e00ff80f

def z223 : W := mkw 0x38ea5e8d491a906a 0x071d4bd1a923520d 0x41f81e0f001e007e 0x283f03c1e003c00f

def z224 : W := mkw 0x67b6b200037fb000 0xacf6d640006ff600 0x0de7000003fff807 0x01bce000007fff00

def z225 : W := mkw 0x6ffefaa803ffb440 0xadffdf55007ff688 0xffffffec03fffe67 0x9ffffffd807fffcc

def z226 : W := mkw 0x984105ffd8800550 0x530820bffb1000aa 0x100001fffc0007f8 0xe200003fff8000ff

def z227 : W := mkw 0x06086f356eebc7a8 0x00c10de6addd78f5 0xfe18ffffffffc7ff 0xffc31ffffffff8ff

def z228 : W := mkw 0x968fdd55d8000000 0x72d1fbaabb000000 0xb607fff0fc000000 0x16c0fffe1f800000

def z229 : W := mkw 0x4110000200040010 0x0822000040008002 0x001800030006001a 0x200300006000c003

def z230 : W := mkw 0x4730000003540000 0x08e60000006a8000 0xcff8000003fe0006 0x19ff0000007fc000

def z231 : W := mkw 0x17dedc8f48000000 0x62fbdb91e9000000 0xe7fffe0f00000000 0x1cffffc1e0000000

def z232 : W := mkw 0x282002202198de62 0x0504004404331bcc 0x080000000399fe65 0x8100000000733fcc

def z233 : W := mkw 0x67befe04637ff220 0xacf7dfc08c6ffe44 0xfffffe0ce3fffe67 0x9fffffc19c7fffcc

def z234 : W := mkw 0x11db5ccfc8000000 0x623b6b99f9000000 0xf5ff1fefe0000000 0x1ebfe3fdfc000000

def z235 : W := mkw 0x00086a00002b8000 0x00010d4000057000 0xea18fe00007fc007 0x1d431fc0000ff800

def z236 : W := mkw 0x20aefa00013bb000 0xa415df4000277600 0xede7fe000399f805 0x1dbcffc000733f00

def z237 : W := mkw 0x0600011002400100 0x00c0002200480020 0x0200001000600180 0x40400002000c0030

def z238 : W := mkw 0xae25a370b7f9ffe3 0x15c4b46e16ff3ffc 0xbe07e1f0fff9ffe5 0xd7c0fc3e1fff3ffc

def z239 : W := mkw 0x086100e8a1904e40 0x010c201d143209c8 0xfde701ece399fe65 0x9fbce03d9c733fcc

def z240 : W := mkw 0x0000200002612000 0x00000400004c2400 0x0800000003e1f801 0x01000000007c3f00

def z241 : W := mkw 0x908ffc45fc216a81 0x7211ff88bf842d50 0x2007fe00fc01f801 0x0400ffc01f803f00

def z242 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0xfffffe1f03ffffff 0xffffffc3e07fffff

def z243 : W := mkw 0x208a5a00000a9000 0xa4114b4000015200 0x00001e0000000000 0x000003c000000000

def z244 : W := mkw 0x07586f9f6c2bc2a8 0x00eb0df3ed857855 0xfff8fffffc7fc7ff 0xffff1fffff8ff8ff

def z245 : W := mkw 0x871ce9131e612181 0x70e39d2263cc2430 0x0218e0131c600180 0x40431c02638c0030

def z246 : W := mkw 0x38e336ece5b9dee2 0x071c66dd9cb73bdc 0xffe7fffcfff9ffe5 0xdffcffff9fff3ffc

def z247 : W := mkw 0x00084e05680ac228 0x000109c0ad015845 0xf8181e0fe01fc67f 0xbf0303c1fc03f8cf

def z248 : W := mkw 0x084001ba00800550 0x01080037401000aa 0x100001ff000007f8 0xe200003fe00000ff

def z249 : W := mkw 0x17da5d9f48000000 0x62fb4bb3e9000000 0xd7f81fff00000000 0x1aff03ffe0000000

def z250 : W := mkw 0x3ff317fee198de62 0x07fe62ffdc331bcc 0xffff1fffe399fe65 0x9fffe3fffc733fcc

def z251 : W := mkw 0x48286e256fffc7f8 0x09050dc4adfff8ff 0xfa18fe1fffffc7ff 0xff431fc3fffff8ff

def z252 : W := mkw 0x000026056c2bc2a8 0x000004c0ad857855 0x1800001ffc7fc7ff 0xe3000003ff8ff8ff

def z253 : W := mkw 0x975105dfd8000000 0x52ea20bbfb000000 0xd7f801fffc000000 0x1aff003fff800000

def z254 : W := mkw 0x97dffffffeebefa9 0x72fbffffffdd7df5 0xffffffffffffffff 0xffffffffffffffff

def z255 : W := mkw 0x871dc95398000000 0x70e3b92a73000000 0xb61fe1f3fc000000 0x16c3fc3e7f800000

def z256 : W := mkw 0x486000a803d40550 0x090c0015007a80aa 0xdde001ec03fe07fe 0xfbbc003d807fc0ff

def z257 : W := mkw 0x00086a00242bc280 0x00010d4004857850 0xfa18fe10fc7fc787 0xdf431fc21f8ff8f0

def z258 : W := mkw 0x67befa2027ffff81 0xacf7df4404fffff0 0xeffffe0003ffff87 0xddffffc0007ffff0

def z259 : W := mkw 0x10010444e0004a22 0x020020889c000944 0x00000000e0000000 0x000000001c000000

def z260 : W := mkw 0x0800002020804e62 0x01000004041009cc 0x0000000000000660 0x80000000000000cc

def z261 : W := mkw 0x9e45a5fcf6e16fe3 0x13c8b4bf9edc2dfc 0xbe07e1fcffe1ffe1 0xd7c0fc3f9ffc3ffc

def z262 : W := mkw 0x0000000000000000 0x0000000000000000 0x9a00001000600780 0xd3400002000c00f0

def z263 : W := mkw 0xb087b644f429faa3 0x1610f6c89e853f54 0x2007fe00fc01f801 0x0400ffc01f803f00

def z264 : W := mkw 0x00086e056c2bc2a8 0x00010dc0ad857855 0x48181e0f007fc7ff 0xe90303c1e00ff8ff

def z265 : W := mkw 0xbffffffffdbbdeea 0x77ffffffffb77bdd 0xffffffffffffffff 0xffffffffffffffff

def z266 : W := mkw 0x8005a040b4216a81 0x1000b40816842d50 0xba07e010fc61ff81 0xd740fc021f8c3ff0

def z267 : W := mkw 0x4730000003540000 0x08e60000006a8000 0xdff8001f03fe07fe 0xfbff0003e07fc0ff

def z268 : W := mkw 0xfffffffffbfffe62 0xffffffffff7fffcc 0xfffffffffffffe67 0x9fffffffffffffcc

def z269 : W := mkw 0x479ef80002672000 0xa8f3df00004ce400 0xe7fffe0000660002 0x1cffffc0000cc000

def z270 : W := mkw 0x20002200002bb000 0x8400044000057600 0x000000000001f801 0x0000000000003f00

def z271 : W := mkw 0x00086e056c2bc2a8 0x00010dc0ad857855 0x2800fe00fc7fc7ff 0xe5001fc01f8ff8ff

def z272 : W := mkw 0x497000aa03d40550 0x092e0015407a80aa 0x49f8000f03fe07fe 0xe93f0001e07fc0ff

def z273 : W := mkw 0x28210260a198de62 0x0504204c14331bcc 0xbc0701e0e399fe65 0x9780e03c1c733fcc

def z274 : W := mkw 0x2020020001189000 0x0404004000231200 0x080000000399f805 0x0100000000733f00

def z275 : W := mkw 0x91db5ddfd8000000 0x723b6bbbfb000000 0x51f81ffffc000000 0x0a3f03ffff800000

def z276 : W := mkw 0xc71ce9131a672000 0xf8e39d22634ce400 0x0218e0131c660002 0x00431c02638cc000

def z277 : W := mkw 0x86058170b6c06f81 0x10c0b02e16d80df0 0x140701f0ff803f80 0xc280e03e1ff007f0

def z278 : W := mkw 0x20a216046118d220 0x041442c08c231a44 0xfde71e0ce399fe65 0x9fbce3c19c733fcc

def z279 : W := mkw 0x60aefa00037fb000 0xac15df40006ff600 0x2807fe0003fff807 0x0500ffc0007fff00

def z280 : W := mkw 0x7ffb7fffefffdffa 0x0fff6ffffdfffbff 0xffffffffffffffff 0xffffffffffffffff

def z281 : W := mkw 0x4f7023ba27ffc7f8 0x09ee047744fff8ff 0xdff801ff03ffc7ff 0xfbff003fe07ff8ff

def z282 : W := mkw 0x0000202026e16f81 0x0000040404dc2df0 0xba00e010ffe1ff81 0xd7401c021ffc3ff0

def z283 : W := mkw 0x90010445d8000000 0x52002088bb000000 0x00000000fc000000 0x000000001f800000

def z284 : W := mkw 0x871de973bee16f81 0x70e3bd2e77dc2df0 0xbe1fe1f3ffe1ff81 0xd7c3fc3e7ffc3ff0

def z285 : W := mkw 0x10c314ece0804e00 0x0218629d9c1009c0 0xfde71fece381fe01 0x9fbce3fd9c703fc0

def z286 : W := mkw 0x0600013002c00500 0x00c00026005800a0 0x040001e003800000 0x0080003c00700000

def z287 : W := mkw 0x97dfdddffc0042a8 0x72fbfbbbff800855 0xf7fffffffc0007f8 0xfeffffffff8000ff

def z288 : W := mkw 0x6f7003ba23dcdf72 0x0dee0077447b9bee 0xdff801ff03ffffff 0xfbff003fe07fffff

def z289 : W := mkw 0x0000000000000000 0x0000000000000000 0xd800000c00180664 0x9b000001800300cc

def z290 : W := mkw 0x38eb5eede998de62 0x071d6bddbd331bcc 0xffffffffff99fe65 0x9ffffffffff33fcc

def z291 : W := mkw 0x184100e880800c42 0x0308201d10100188 0x000001e000000000 0x0000003c00000000

def z292 : W := mkw 0x4f70019a03540150 0x09ee0033406a802a 0x43f8001f007e01fe 0x687f0003e00fc03f

def z293 : W := mkw 0x208efe056c2bf2a8 0xa411dfc0ad857e55 0xfa1ffe1ffc7fffff 0xff43ffc3ff8fffff

def z294 : W := mkw 0x10831444c0000000 0x0210628898000000 0x20071e00e0000000 0x0400e3c01c000000

def z295 : W := mkw 0x308b7e45ec2bdaaa 0x06116fc8bd857b55 0x2007fe00fc01f801 0x0400ffc01f803f00

def z296 : W := mkw 0x0000002002c00500 0x00000004005800a0 0x0800000003e00780 0xc1000000007c00f0

def z297 : W := mkw 0x00086e056c2bc2a8 0x00010dc0ad857855 0xba00fe10fc61c781 0xd7401fc21f8c38f0

def z298 : W := mkw 0x3fffdeece198de62 0x27fffbdd9c331bcc 0xffffffece399fe65 0x9ffffffd9c733fcc

def z299 : W := mkw 0x0000060440088020 0x000000c088011004 0x40001e0c00180064 0x080003c18003000c

def z300 : W := mkw 0x00012060a4a14e80 0x0000240c149429d0 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z301 : W := mkw 0x8000011014000181 0x1000002202800030 0x000000101c000180 0x4000000203800030

def z302 : W := mkw 0xffffffffdbffb550 0xfffffffffb7ff6aa 0xffffffffffffffff 0xffffffffffffffff

def z303 : W := mkw 0xdf7105ffdbd40550 0x5bee20bffb7a80aa 0xdff801fffffe07fe 0xfbff003fffffc0ff

def z304 : W := mkw 0x0750019a00000000 0x00ea003340000000 0x05e001e000000000 0x00bc003c00000000

def z305 : W := mkw 0x4820002003d40550 0x09040004007a80aa 0x0000000003800000 0x0000000000700000

def z306 : W := mkw 0x00086e256eebefa9 0x00010dc4addd7df5 0xfa18fe1fffffffff 0xff431fc3ffffffff

def z307 : W := mkw 0x67beda00035eb000 0xacf7db40006bd600 0x45ff1e00039e3806 0x08bfe3c00073c700

def z308 : W := mkw 0x97d791fa92c02d01 0x72faf23f525805a0 0x05e701e003803800 0x00bce03c00700700

def z309 : W := mkw 0x184104edec804eea 0x0308209dbd9009dd 0x100001fffc0007f8 0xe200003fff8000ff

def z310 : W := mkw 0xdff791fa93d40550 0x7bfef23f527a80aa 0xdfff01ff03fe07fe 0xfbffe03fe07fc0ff

def z311 : W := mkw 0x47186f176e6fc3b8 0x08e30de2edcdf877 0xfa18fe1ffc7fc7ff 0xff431fc3ff8ff8ff

def z312 : W := mkw 0x4f5001ba02c40550 0x09ea0037405880aa 0x121801ff006607fa 0xe243003fe00cc0ff

def z313 : W := mkw 0x00084c0548000000 0x00010980a9000000 0xfa18fe1ffc7e07fe 0xff431fc3ff8fc0ff

def z314 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0xfffffffffc7e07fe 0xffffffffff8fc0ff

def z315 : W := mkw 0x9087904090000000 0x7210f20812000000 0x0007000000000000 0x0000e00000000000

def z316 : W := mkw 0x8604a13036e16f81 0x10c0942606dc2df0 0x0a00e0101fe1ff81 0xc1401c0203fc3ff0

def z317 : W := mkw 0x00084c056c0042a8 0x00010980ad800855 0xf218fe1ffc0007f8 0xfe431fc3ff8000ff

def z318 : W := mkw 0x67befe054b7fb000 0xacf7dfc0a96ff600 0xfffffe1ffffff807 0x1fffffc3ffffff00

def z319 : W := mkw 0x0040019a00000000 0x0008003340000000 0x100001ff00000000 0x0200003fe0000000

def z320 : W := mkw 0x0000200024214280 0x0000040004842850 0xfa18e01ffc7fc7ff 0xff431c03ff8ff8ff

def z321 : W := mkw 0x071cc80000000000 0x20e3990000000000 0x0218e00000000000 0x00431c0000000000

def z322 : W := mkw 0xc71ce91016672181 0xb8e39d2202cce430 0x0218e0101c660182 0x40431c02038cc030

def z323 : W := mkw 0x2820222025bbdeea 0x0504044404b77bdd 0x0800000003ffffff 0xe1000000007fffff

def z324 : W := mkw 0xcf7cc9bb1bd40550 0x79ef9937637a80aa 0xdff8e1ff1ffe07fe 0xfbff1c3fe3ffc0ff

def z325 : W := mkw 0x7ffffae883ffbc42 0xafffff5d107ff788 0xefffffe003fff807 0x1dfffffc007fff00

def z326 : W := mkw 0x97dfd9da90000000 0x72fbfb3b52000000 0xe7ffffe000000000 0x1cfffffc00000000

def z327 : W := mkw 0x00086e056c2bc2a8 0x00010dc0ad857855 0xf800fe0cfc19c665 0x9f001fc19f8338cc

def z328 : W := mkw 0x268efa00026bb000 0xa4d1df40004d7600 0xae07fe0003e1f801 0x15c0ffc0007c3f00

def z329 : W := mkw 0x000868010c230088 0x00010d0021846011 0xda18e01f1c7e07fe 0xfb431c03e38fc0ff

def z330 : W := mkw 0xe625a370b7ffff81 0x9cc4b46e16fffff0 0xbe07e1f0ffffff87 0xd7c0fc3e1ffffff0

def z331 : W := mkw 0x00084e05480a8028 0x000109c0a9015005 0xf218fe1ffc1e007e 0x3e431fc3ff83c00f

def z332 : W := mkw 0x67befb3003ffb500 0xacf7df66007ff6a0 0xfffffff003ffff87 0xdffffffe007ffff0

def z333 : W := mkw 0x97dfddfffc804f81 0x72fbfbbfff9009f0 0xf7fffffffc000780 0xdeffffffff8000f0

def z334 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0x25e7fe000381f801 0x04bcffc000703f00

def z335 : W := mkw 0x8605a150b6616b81 0x10c0b42a16cc2d70 0x2207e010fc61f981 0x4440fc021f8c3f30

def z336 : W := mkw 0xd7dffddfda672000 0xfafbffbbfb4ce400 0xf7fffffffc660002 0x1effffffff8cc000

def z337 : W := mkw 0x871cef177c2bc2a8 0x70e39de2ef857855 0xfa18fe1ffc7fc7ff 0xff431fc3ff8ff8ff

def z338 : W := mkw 0x38e317fee198df72 0x071c62ffdc331bee 0xfde71fffe399fffd 0xffbce3fffc733fff

def z339 : W := mkw 0x075001ba02c00500 0x00ea0037405800a0 0xdff801ff03e00780 0xdbff003fe07c00f0

def z340 : W := mkw 0x8605a575fee16fa9 0x10c0b4aebfdc2df5 0xbe07e1ffffe1fff9 0xf7c0fc3ffffc3fff

def z341 : W := mkw 0x77bffe44e37ffa22 0xaef7ffc89c6fff44 0xeffffe00e3fff807 0x1dffffc01c7fff00

def z342 : W := mkw 0x8005a170b4a16f81 0x1000b42e16942df0 0x3007e1f0fc01ff81 0xc600fc3e1f803ff0

def z343 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000001f000007f8 0xe2000003e00000ff

def z344 : W := mkw 0x860def75feebefa9 0x10c1bdeebfdd7df5 0xbe07fff0ffe1ff81 0xd7c0fffe1ffc3ff0

def z345 : W := mkw 0x97d795dfd8000000 0x72faf2bbfb000000 0x15e701fffc000000 0x02bce03fff800000

def z346 : W := mkw 0x0600000002400000 0x00c0000000480000 0x8e00000003e00000 0x11c00000007c0000

def z347 : W := mkw 0x860ded75fee16f81 0x10c1bdaebfdc2df0 0xfe1fffffffe1ff81 0xdfc3fffffffc3ff0

def z348 : W := mkw 0x18496eedecabceea 0x03092dddbd9579dd 0xfa18fffffc7fc7ff 0xff431fffff8ff8ff

def z349 : W := mkw 0x108a5c0548000000 0x62114b80a9000000 0x00001e0000000000 0x000003c000000000

def z350 : W := mkw 0x38e2168c41189062 0x071c42d18823120c 0xede71e0c0399f865 0x1dbce3c180733f0c

def z351 : W := mkw 0x800cc80118000000 0x7001990023000000 0x0000e0001c000000 0x00001c0003800000

def z352 : W := mkw 0x17dfdcccc0000000 0x22fbfb9998000000 0xf7ffffece0000000 0x1efffffd9c000000

def z353 : W := mkw 0x2086900000003000 0xa410d20000000600 0x0007000000003800 0x0000e00000000700

def z354 : W := mkw 0xb08fde45f808da22 0x7611fbc8bf011b44 0x2007fe00fc01f801 0x0400ffc01f803f00

def z355 : W := mkw 0x00002604642bc2a8 0x000004c08c857855 0xf8001e0ce07fc7ff 0xff0003c19c0ff8ff

def z356 : W := mkw 0x59fa5c8f49140050 0x6b3f4b91e922800a 0x41f81e0f001e007e 0x283f03c1e003c00f

def z357 : W := mkw 0x38e216ac6198de62 0x071c42d58c331bcc 0x49e01e0c0399fe65 0x893c03c180733fcc

def z358 : W := mkw 0x4e20013003d40550 0x09c40026007a80aa 0x9e0001f003fe07fe 0xf3c0003e007fc0ff

def z359 : W := mkw 0x20aa7a00013b9000 0x04154f4000277200 0xeffffe0003fff807 0x1dffffc0007fff00

def z360 : W := mkw 0x97d791da90000000 0x72faf23b52000000 0xb7e7e1f0fc000000 0x16fcfc3e1f800000

def z361 : W := mkw 0x000024056c2142a8 0x00000480ad842855 0xba00e01ffc61c7f9 0xf7401c03ff8c38ff

def z362 : W := mkw 0xcf7581fa93d40550 0x19eeb03f527a80aa 0xffffe1fffffe07fe 0xfffffc3fffffc0ff

def z363 : W := mkw 0x308ffe44e02bfa22 0xa611ffc89c057f44 0x2007fe00e001f801 0x0400ffc01c003f00

def z364 : W := mkw 0x879fd95090000000 0x30f3fb2a12000000 0xf7fffff0fc000000 0x1efffffe1f800000

def z365 : W := mkw 0x6020222027ffff81 0x8c04044404fffff0 0x0800000003ffff87 0xc1000000007ffff0

def z366 : W := mkw 0x4730011203540110 0x08e60022406a8022 0xcff8001303fe019e 0x79ff0002607fc033

def z367 : W := mkw 0x00084e056808c220 0x000109c0ad011844 0xfa18fe1ffc19c665 0x9f431fc3ff8338cc

def z368 : W := mkw 0x0f7001ba01900440 0x01ee003740320088 0xdff801ff03980664 0x9bff003fe07300cc

def z369 : W := mkw 0x00086a00002b8000 0x00010d4000057000 0xfa18fe1f007fc7ff 0xff431fc3e00ff8ff

def z370 : W := mkw 0x86010170b6c04f81 0x10c0202e16d809f0 0x9e0001f0ffe00780 0xd3c0003e1ffc00f0

def z371 : W := mkw 0x0604a02026e16f81 0x00c0940404dc2df0 0xae07e00003e1ff81 0xd5c0fc00007c3ff0

def z372 : W := mkw 0x8604a11036616381 0x10c0942206cc2c70 0xba00e010fc61c781 0xd7401c021f8c38f0

def z373 : W := mkw 0x38eb7eededbbdeea 0x071d6fddbdb77bdd 0xfde7ffecff99fe65 0x9fbcfffd9ff33fcc

def z374 : W := mkw 0x60a23200037fb000 0x8c144640006ff600 0xede71e0003fff807 0x1dbce3c0007fff00

def z375 : W := mkw 0x67b69200035cb000 0xacf6d240006b9600 0xede71e000399f805 0x1dbce3c000733f00

def z376 : W := mkw 0x00086e056c2bc2a8 0x00010dc0ad857855 0x3000fe1ffc01c7f9 0xe6001fc3ff8038ff

def z377 : W := mkw 0x4734a00003752000 0x08e69400006ea400 0xefffe00003fff807 0x1dfffc00007fff00

def z378 : W := mkw 0x8005804090002801 0x1000b00812000500 0x0007000000003800 0x0000e00000000700

def z379 : W := mkw 0x6ff691ba03d43550 0xadfed237407a86aa 0x05e701e003803800 0x00bce03c00700700

def z380 : W := mkw 0x0000002000800400 0x0000000400100080 0x9c0001e003800600 0x9380003c007000c0

def z381 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0xd7f801ff03800000 0x1aff003fe0700000

def z382 : W := mkw 0x286002a82198de62 0x050c005504331bcc 0xdde001ec0399fe65 0x9bbc003d80733fcc

def z383 : W := mkw 0xbffffffffff9ffe3 0x77ffffffffff3ffc 0xfffffffffff9ffe5 0xdfffffffffff3ffc

def z384 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0xffff1fffe3ffffff 0xffffe3fffc7fffff

def z385 : W := mkw 0x0000040548000000 0x00000080a9000000 0x1000001ffc000000 0x02000003ff800000

def z386 : W := mkw 0xcf7581fa93d42d51 0x19eeb03f527a85aa 0x05e701e003803800 0x00bce03c00700700

def z387 : W := mkw 0x0600213026e16f81 0x00c0042604dc2df0 0x9e0001f003e1ff81 0xd3c0003e007c3ff0

def z388 : W := mkw 0x871ccd1758000000 0x70e399a2eb000000 0xf218fe1ffc000000 0x1e431fc3ff800000

def z389 : W := mkw 0x79fa5e8c411e9062 0xaf3f4bd18823d20c 0x41f81e0c001e0066 0x083f03c18003c00c

def z390 : W := mkw 0x086001ba01900550 0x010c0037403200aa 0xdde001ff039807fc 0xfbbc003fe07300ff

def z391 : W := mkw 0x67befe056f7ff2a8 0xacf7dfc0adeffe55 0xeffffe00fffff807 0x1dffffc01fffff00

def z392 : W := mkw 0x000006046008c220 0x000000c08c011844 0xfa181e1fe07fc7ff 0xff4303c3fc0ff8ff

def z393 : W := mkw 0x97dfddfff8804e00 0x72fbfbbfff1009c0 0xffffffffff81fe01 0x9ffffffffff03fc0

def z394 : W := mkw 0x8005a060b6e16f81 0x1000b40c16dc2df0 0x2807e000ffe1ff81 0xc500fc001ffc3ff0

def z395 : W := mkw 0x679efa00026fb000 0xacf3df40004df600 0x221ffe000067f803 0x0443ffc0000cff00

def z396 : W := mkw 0x879ed91318000000 0x70f3db2263000000 0xe7fffe131c000000 0x1cffffc263800000

def z397 : W := mkw 0xb8e317fcf598dfe3 0x171c62ff9eb31bfc 0xfde71ffcff99ffe5 0xdfbce3ff9ff33ffc

def z398 : W := mkw 0x97dedd9f58000000 0x72fbdbb3eb000000 0x43f8fe1f1c000000 0x087f1fc3e3800000

def z399 : W := mkw 0xcf74a1ba17f525d1 0x19ee943742fea4ba 0xdff8e1ff1ffe07fe 0xfbff1c3fe3ffc0ff

def z400 : W := mkw 0x7ff217be43dc9572 0x0ffe42f7c87b92ae 0xdff81fff03fe07fe 0xfbff03ffe07fc0ff

def z401 : W := mkw 0xc735a170b7f56f81 0x18e6b42e16feadf0 0xffffe1f0ffffff87 0xdffffc3e1ffffff0

def z402 : W := mkw 0x00010664e088ce20 0x000020cc9c1119c4 0xfc071fece399fe65 0x9f80e3fd9c733fcc

def z403 : W := mkw 0x00084c0548000000 0x00010980a9000000 0x40181e0f00000000 0x080303c1e0000000

def z404 : W := mkw 0x61ba7a00013f9000 0xac374f400027f200 0xebf8fe00007fc007 0x1d7f1fc0000ff800

def z405 : W := mkw 0x00084e05480a8028 0x000109c0a9015005 0xda181e1f007e07fe 0xfb4303c3e00fc0ff

def z406 : W := mkw 0x00084c0548000000 0x00010980a9000000 0x2000fe00fc000000 0x04001fc01f800000

def z407 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0x9fe001f003e00780 0xd3fc003e007c00f0

def z408 : W := mkw 0x0000200024216a81 0x0000040004842d50 0x000000000001f801 0x0000000000003f00

def z409 : W := mkw 0x0605a060a2e16e00 0x00c0b40c145c2dc0 0xbe07e1e0e3e1fe01 0x97c0fc3c1c7c3fc0

def z410 : W := mkw 0x000006056c08c2a8 0x000000c0ad811855 0xf8001e1ffc19c7fd 0xff0003c3ff8338ff

def z411 : W := mkw 0x8005804090000000 0x1000b00812000000 0x2007e000fc000000 0x0400fc001f800000

def z412 : W := mkw 0x00002200242bc2a8 0x0000044004857855 0x000000000001c001 0x0000000000003800

def z413 : W := mkw 0x4710013202c40510 0x08e20026405880a2 0x9e1801f303e6079a 0xf3c3003e607cc0f3

def z414 : W := mkw 0x97dffddffc216a81 0x72fbffbbff842d50 0xf7fffffffc01f801 0x1effffffff803f00

def z415 : W := mkw 0x10c310c880000000 0x0218621910000000 0x05e701e000000000 0x00bce03c00000000

def z416 : W := mkw 0x7ffefe8c437fb062 0xafffdfd1886ff60c 0xeffffe0c03fff867 0x1dffffc1807fff0c

def z417 : W := mkw 0xbee797fcf198de62 0x17dcf2ff9e331bcc 0xffe7fffcff99fe65 0x9ffcffff9ff33fcc

def z418 : W := mkw 0x9fffddffd9900440 0x73fffbbffb320088 0xffffffffff980664 0x9ffffffffff300cc

def z419 : W := mkw 0x8005a060b4a16e81 0x1000b40c16942dd0 0xbc07e1e0ff81fe01 0x9780fc3c1ff03fc0

def z420 : W := mkw 0x860cef157e6be3a9 0x10c19de2afcd7c75 0xfa18fe1ffc7fc7ff 0xff431fc3ff8ff8ff

def z421 : W := mkw 0x38c316ece088de62 0x071862dd9c111bcc 0x30071fece001fe61 0x8600e3fd9c003fcc

def z422 : W := mkw 0x11da5e8f480a8028 0x623b4bd1e9015005 0x41f81e0f001e007e 0x283f03c1e003c00f

def z423 : W := mkw 0xffffdffffbdcdf72 0x7ffffbffff7b9bee 0xffffffffffffffff 0xffffffffffffffff

def z424 : W := mkw 0x67befb12037fb110 0xacf7df62406ff622 0xeffffe1303fff99f 0x7dffffc2607fff33

def z425 : W := mkw 0xf7ffffdfff7ff2a8 0xfefffffbffeffe55 0xffffffffffffffff 0xffffffffffffffff

def z426 : W := mkw 0x860def55fc2bc2a8 0x10c1bdeabf857855 0xfe1ffffffc7fc7ff 0xffc3ffffff8ff8ff

def z427 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0x15e001ff038007f8 0xe2bc003fe07000ff

def z428 : W := mkw 0x38e316eded98deea 0x071c62ddbdb31bdd 0xfde71fffff99fffd 0xffbce3fffff33fff

def z429 : W := mkw 0x20a2100001101000 0x0414420000220200 0x05e7000003803800 0x00bce00000700700

def z430 : W := mkw 0x97dfd9db98000000 0x72fbfb3b73000000 0x07ffe1f31c000000 0x00fffc3e63800000

def z431 : W := mkw 0x80012170b4a14f81 0x1000242e169429f0 0xba00e1f0fc61c781 0xd7401c3e1f8c38f0

def z432 : W := mkw 0x282006246198de62 0x050400c48c331bcc 0xf8001e0ce399fe65 0x9f0003c19c733fcc

def z433 : W := mkw 0x00086a012c2bc2a8 0x00010d4025857855 0x0a18e0131c7fc7ff 0xe1431c02638ff8ff

def z434 : W := mkw 0x908ffe45fc2bc2a8 0x7211ffc8bf857855 0xfa1ffe1ffc7fc7ff 0xff43ffc3ff8ff8ff

def z435 : W := mkw 0x8605a774f6e9efa1 0x10c0b4ee9edd3df4 0xfe07fffcfff9ffe5 0xdfc0ffff9fff3ffc

def z436 : W := mkw 0x6ff691ba03d43550 0xadfed237407a86aa 0xdfff01ff03fe3ffe 0xfbffe03fe07fc7ff

def z437 : W := mkw 0x97dfddffdac02d01 0x72fbfbbffb5805a0 0xf7ffffffff803800 0x1efffffffff00700

def z438 : W := mkw 0x6fbefa2023fffe62 0xadf7df44047fffcc 0xeffffe0003fffe67 0x9dffffc0007fffcc

def z439 : W := mkw 0xe7bfff75ffffffa9 0xbcf7ffeebffffff5 0xffffffffffffffff 0xffffffffffffffff

def z440 : W := mkw 0x67bed80003543000 0xacf7db00006a8600 0xe7fffe0003803800 0x1cffffc000700700

def z441 : W := mkw 0x0150008a00000000 0x002a001140000000 0x41f8000f00000000 0x083f0001e0000000

def z442 : W := mkw 0x4730000003540000 0x08e60000006a8000 0x05e0000003800000 0x00bc000000700000

def z443 : W := mkw 0x308b7e45ec2bdaaa 0x06116fc8bd857b55 0xfa1ffe1ffc7fffff 0xff43ffc3ff8fffff

def z444 : W := mkw 0x3082160440089022 0x061042c088011204 0x00001e0000000000 0x000003c000000000

def z445 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0xcff801e003fe0006 0x19ff003c007fc000

def z446 : W := mkw 0x0e6001b803d00540 0x01cc0037007a00a8 0xdfe001fc03f807e4 0xdbfc003f807f00fc

def z447 : W := mkw 0xd7ffdddfdb540000 0x7afffbbbfb6a8000 0xfffffffffffe0006 0x1fffffffffffc000

def z448 : W := mkw 0xc71de970b6e76f81 0xb8e3bd2e16dcedf0 0xbe1fe1f0ffe7ff83 0xd7c3fc3e1ffcfff0

def z449 : W := mkw 0x00096e65ecabcea8 0x00012dccbd9579d5 0xfe1fffffffffffff 0xffc3ffffffffffff

def z450 : W := mkw 0x96c7b5fcf6e16f81 0x12d8f6bf9edc2df0 0xffe7fffcffe1ff81 0xdffcffff9ffc3ff0

def z451 : W := mkw 0x279efa00002bb000 0xa4f3df4000057600 0xe7fffe000001f801 0x1cffffc000003f00

def z452 : W := mkw 0x6f7023ba03ffb550 0x8dee0477407ff6aa 0xdff801ff03ffffff 0xfbff003fe07fffff

def z453 : W := mkw 0x38e314ece1905e62 0x071c629d9c320bcc 0x15e701ece3803e60 0x82bce03d9c7007cc

def z454 : W := mkw 0x2820222027f9ffe3 0x0504044404ff3ffc 0x0800000003f9ffe5 0xc1000000007f3ffc

def z455 : W := mkw 0x27beda0001189000 0x24f7db4000231200 0xeffffe000399f805 0x1dffffc000733f00

def z456 : W := mkw 0xa08ffa40b42bfa81 0xb411ff4816857f50 0x2007fe00fc01f801 0x0400ffc01f803f00

def z457 : W := mkw 0x67b21200035c9000 0x0cf64240006b9200 0xefff1e0003fff807 0x1dffe3c0007fff00

def z458 : W := mkw 0x08686ead6dbbc6e8 0x010d0dd5adb778dd 0xfff8ffffffffc7ff 0xffff1ffffffff8ff

def z459 : W := mkw 0x78e336ece3fffe62 0x8f1c66dd9c7fffcc 0xfde71fece3fffe67 0x9fbce3fd9c7fffcc

def z460 : W := mkw 0xdfffffffffffc7f8 0x7bfffffffffff8ff 0xffffffffffffc7ff 0xfffffffffffff8ff

def z461 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0x45f801ef039e007e 0x28bf003de073c00f

def z462 : W := mkw 0x4f784fbf4bde8578 0x09ef09f7e97bd0af 0xdff81fff03fe07fe 0xfbff03ffe07fc0ff

def z463 : W := mkw 0xbee797fcf3d8ff63 0x17dcf2ff9e7b1fec 0xfde71fece399fe65 0x9fbce3fd9c733fcc

def z464 : W := mkw 0x38ea7e8d6d3bd2ea 0x071d4fd1ada77a5d 0xfbf8fe1ffc7fc7ff 0xff7f1fc3ff8ff8ff

def z465 : W := mkw 0x39fa5e8f49189062 0x673f4bd1e923120c 0x41f81e0f00180064 0x083f03c1e003000c

def z466 : W := mkw 0x79f316eee19cde72 0x0f3e62dddc339bce 0xfdff1fefe39ffe7f 0xbfbfe3fdfc73ffcf

def z467 : W := mkw 0x67befe054b7fb028 0xacf7dfc0a96ff605 0xeffffe0f03fff87f 0x3dffffc1e07fff0f

def z468 : W := mkw 0x0820002001900440 0x0104000400320088 0x0800000003980664 0x81000000007300cc

def z469 : W := mkw 0x0710000000000000 0x00e2000000000000 0xc7f8000000000000 0x18ff000000000000

def z470 : W := mkw 0xbee7b1f8b7f17fc3 0x17dcf63f16fe2ff8 0xbfe7e1f0ffe1ff81 0xd7fcfc3e1ffc3ff0

def z471 : W := mkw 0x0000002024804f81 0x00000004049009f0 0x0000000000000780 0xc0000000000000f0

def z472 : W := mkw 0x000026046429c2a0 0x000004c08c853854 0xfa00fe1cfc79c7e5 0xdf401fc39f8f38fc

def z473 : W := mkw 0xf7ffffffffffff81 0xfefffffffffffff0 0xffffffffffffff87 0xdffffffffffffff0

def z474 : W := mkw 0x60286e056f7ff2a8 0x8c050dc0adeffe55 0xfa18fe1fffffffff 0xff431fc3ffffffff

def z475 : W := mkw 0x471ce8010e672088 0xa8e39d0021cce411 0x0218e0131c66019a 0x60431c02638cc033

def z476 : W := mkw 0x860ce9111e632189 0x10c19d2223cc6431 0x0218e0131c66019a 0x60431c02638cc033

def z477 : W := mkw 0x904105dffc0042a8 0x520820bbff800855 0x100001fffc0007f8 0xe200003fff8000ff

def z478 : W := mkw 0x0604a00026616280 0x00c0940004cc2c50 0xbe07e010ffe1ff81 0xd7c0fc021ffc3ff0

def z479 : W := mkw 0x0e4001ba02c00550 0x01c80037405800aa 0x9e0001ff03e007f8 0xf3c0003fe07c00ff

def z480 : W := mkw 0x00086e04602bc220 0x00010dc08c057844 0xfa18fe0ce07fc667 0x9f431fc19c0ff8cc

def z481 : W := mkw 0x8755a1fab6e16f81 0x10eab43f56dc2df0 0xffffe1ffffe1ff81 0xdffffc3ffffc3ff0

def z482 : W := mkw 0x497001ba01940550 0x092e0037403280aa 0x51f801ff001e07fe 0xea3f003fe003c0ff

def z483 : W := mkw 0xdfffdddfd9140050 0x7bfffbbbfb22800a 0xf7fffffffc1e007e 0x3effffffff83c00f

def z484 : W := mkw 0x7ffffeedeffffeea 0xafffffddbdffffdd 0xffffffffffffffff 0xffffffffffffffff

def z485 : W := mkw 0x8604811012402101 0x10c0902202480420 0x0000000000000000 0x0000000000000000

def z486 : W := mkw 0x4f7005bf6fd447f8 0x09ee00b7edfa88ff 0xdff801fffffe07fe 0xfbff003fffffc0ff

def z487 : W := mkw 0xb7ffdfdfd9189000 0x76fffbfbfb231200 0xffffffffff99f805 0x1ffffffffff33f00

def z488 : W := mkw 0x0600213026e14780 0x00c0042604dc28f0 0xbe00e1f0ffe1c781 0xd7c01c3e1ffc38f0

def z489 : W := mkw 0x084001ba00800550 0x01080037401000aa 0xda1801ff007e07fe 0xfb43003fe00fc0ff

def z490 : W := mkw 0x860dcd55d8000000 0x10c1b9aabb000000 0xf61ffffffc000000 0x1ec3ffffff800000

def z491 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0x0de001e003fe07fe 0xe1bc003c007fc0ff

def z492 : W := mkw 0x4130000001140000 0x0826000000228000 0x41f80000001e0006 0x083f00000003c000

def z493 : W := mkw 0x079edc0548000000 0x20f3db80a9000000 0xf7fffe1ffc000000 0x1effffc3ff800000

def z494 : W := mkw 0x0604800000000000 0x00c0900000000000 0xa607e00000000000 0x14c0fc0000000000

def z495 : W := mkw 0x47386a00037f8000 0x08e70d40006ff000 0xeff8fe0003ffc007 0x1dff1fc0007ff800

def z496 : W := mkw 0x908fdc45d8000000 0x7211fb88bb000000 0xf21ffe1ffc000000 0x1e43ffc3ff800000

def z497 : W := mkw 0x0000040440000000 0x0000008088000000 0xf0001e0ce0000000 0x1e0003c19c000000

def z498 : W := mkw 0x07ded99a00000000 0x20fbdb3340000000 0xf7ffffff00000000 0x1effffffe0000000

def z499 : W := mkw 0x4f7021ba27f56fd1 0x09ee043744feadfa 0xdff801ff03ffffff 0xfbff003fe07fffff

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0xac0700000381f801 0x1580e00000703f00

def z501 : W := mkw 0x8604811010000000 0x10c0902202000000 0x0200e0101c000000 0x00401c0203800000

def z502 : W := mkw 0x18e314ecc1900440 0x031c629d98320088 0xfde71fece3980664 0x9fbce3fd9c7300cc

def z503 : W := mkw 0x3083104080001802 0x0610620810000300 0x0007000000003800 0x0000e00000000700

def z504 : W := mkw 0x08486fbf6cabc7f8 0x01090df7ed9578ff 0xfa18fffffc7fc7ff 0xff431fffff8ff8ff

def z505 : W := mkw 0x4f7007be63dcc770 0x09ee00f7cc7b98ee 0xfff81fffe3ffc7ff 0xffff03fffc7ff8ff

def z506 : W := mkw 0x97dffddfdc230088 0x72fbffbbfb846011 0xf7fffffffc66019a 0x7effffffff8cc033

def z507 : W := mkw 0xfff7b7fef7fdfff3 0x1ffef6ffdeffbffe 0xffffffffffffffff 0xffffffffffffffff

def z508 : W := mkw 0x860de971bee36f89 0x10c1bd2e37dc6df1 0xbe1fe1f3ffe7ff9b 0xf7c3fc3e7ffcfff3

def z509 : W := mkw 0xc714a11216652191 0x18e2942242cca432 0x0218e0131c66019a 0x60431c02638cc033

def z510 : W := mkw 0x486001ba03d40550 0x090c0037407a80aa 0x180001ff03fe07fe 0xe300003fe07fc0ff

def z511 : W := mkw 0x38e2108801101042 0x071c421100220208 0x01e0000000000000 0x003c000000000000

def z512 : W := mkw 0x6ffefbba03ffb550 0xadffdf77407ff6aa 0xefffffe003fff807 0x1dfffffc007fff00

def z513 : W := mkw 0x00000000240042a8 0x0000000004800855 0x00000000000007f8 0xe0000000000000ff

def z514 : W := mkw 0x00010040a0004a00 0x0000200814000940 0x20070000e001f801 0x0400e0001c003f00

def z515 : W := mkw 0x30a31644e118da22 0x061462c89c231b44 0xede71e00e399f805 0x1dbce3c01c733f00

def z516 : W := mkw 0x4f70008a03540050 0x09ee0011406a800a 0xcff8000f03fe007e 0x39ff0001e07fc00f

def z517 : W := mkw 0x184105fee0804f72 0x030820bfdc1009ee 0x100001ffe00007f8 0xe200003ffc0000ff

def z518 : W := mkw 0x0604a13002e12500 0x00c09426005c24a0 0xbe07e1f003e1ff81 0xd7c0fc3e007c3ff0

def z519 : W := mkw 0x0600011000000000 0x00c0002200000000 0x960001f000000000 0x12c0003e00000000

def z520 : W := mkw 0x086000a801900440 0x010c001500320088 0x05e001e003800000 0x00bc003c00700000

def z521 : W := mkw 0x7ff311fa83d41d52 0x0ffe623f507a83aa 0xdfff01ff03fe3ffe 0xfbffe03fe07fc7ff

def z522 : W := mkw 0x6020000003543000 0x8c040000006a8600 0x0000000003803800 0x0000000000700700

def z523 : W := mkw 0x4020000003540000 0x08040000006a8000 0x0800000003fe0006 0x01000000007fc000

def z524 : W := mkw 0x079efe056c2bc2a8 0x20f3dfc0ad857855 0xfffffe1ffc7fc7ff 0xffffffc3ff8ff8ff

def z525 : W := mkw 0x00000200000a8028 0x0000004000015005 0x00000000001e007e 0x200000000003c00f

def z526 : W := mkw 0x4710000002440000 0x08e2000000488000 0x0218000000660002 0x00430000000cc000

def z527 : W := mkw 0x8605a17096e12d81 0x10c0b42e12dc25b0 0x0607e1f01fe03980 0x40c0fc3e03fc0730

def z528 : W := mkw 0xbeeffffdfffbffeb 0x17ddffffbfff7ffd 0xffffffffffffffff 0xffffffffffffffff

def z529 : W := mkw 0x4970008a01140050 0x092e00114022800a 0xdbf8001f007e07fe 0xfb7f0003e00fc0ff

def z530 : W := mkw 0x00086a010c2b8088 0x00010d4021857011 0xea18fe131c7fc19f 0x7d431fc2638ff833

def z531 : W := mkw 0x497000aa01940450 0x092e00154032808a 0xddf801ef039e067e 0xbbbf003de073c0cf

def z532 : W := mkw 0xd7dfdddfda440110 0x7afbfbbbfb488022 0xf7fffffffc66019a 0x7effffffff8cc033

def z533 : W := mkw 0x7ff316ece3dcde62 0x0ffe62dd9c7b9bcc 0xffff1fece3fffe67 0x9fffe3fd9c7fffcc

def z534 : W := mkw 0xe7bffa40b77ffa81 0xbcf7ff4816efff50 0xeffffe00fffff807 0x1dffffc01fffff00

def z535 : W := mkw 0x00086c054c230088 0x00010d80a9846011 0xf218fe1ffc66019a 0x7e431fc3ff8cc033

def z536 : W := mkw 0x208efe056c2bf2a8 0xa411dfc0ad857e55 0x2007fe00fc01f801 0x0400ffc01f803f00

def z537 : W := mkw 0x86058170b4804f81 0x10c0b02e169009f0 0xb607e1f0fc000780 0xd6c0fc3e1f8000f0

def z538 : W := mkw 0x00086a00242bc2a8 0x00010d4004857855 0xea18fe00007fc7ff 0xfd431fc0000ff8ff

def z539 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0x43f8fe00007e0006 0x087f1fc0000fc000

def z540 : W := mkw 0xbff791fa91901c42 0x77fef23f52320388 0x05e701e003803800 0x00bce03c00700700

def z541 : W := mkw 0x77fefe8f4b7fb000 0xeeffdfd1e96ff600 0xeffffe0f03fff807 0x1dffffc1e07fff00

def z542 : W := mkw 0x8001017090800d01 0x1000202e121001a0 0x000001e000000000 0x0000003c00000000

def z543 : W := mkw 0xb7dfffdfd82bb000 0xf6fbfffbfb057600 0xf7fffffffc01f801 0x1effffffff803f00

def z544 : W := mkw 0x67befa00277ff280 0xacf7df4004effe50 0xfffffe10ffffff87 0xdfffffc21ffffff0

def z545 : W := mkw 0x0860008801100040 0x010c001100220008 0x41e0000c00180064 0x083c00018003000c

def z546 : W := mkw 0x6ffa5bba03de9550 0xadff4b77407bd2aa 0xdff81fff03fe07fe 0xfbff03ffe07fc0ff

def z547 : W := mkw 0x879ff970b6e16f81 0x30f3ff2e16dc2df0 0xfffffff0ffe1ff81 0xdffffffe1ffc3ff0

def z548 : W := mkw 0x49784e8f491e8078 0x092f09d1e923d00f 0x41f81e0f001e007e 0x283f03c1e003c00f

def z549 : W := mkw 0x38effeece1bbfe62 0xa71dffdd9c377fcc 0xfde7ffece399fe65 0x9fbcfffd9c733fcc

def z550 : W := mkw 0x904101da90000000 0x5208203b52000000 0x000001e000000000 0x0000003c00000000

def z551 : W := mkw 0x871ce9131c230088 0x70e39d2263846011 0x0218e0131c66019a 0x60431c02638cc033

def z552 : W := mkw 0x47386e056f7fc2a8 0x08e70dc0adeff855 0xfff8fe1fffffc7ff 0xffff1fc3fffff8ff

def z553 : W := mkw 0x67fefb9a037fb000 0xacffdf73406ff600 0xffffffff03fff807 0x1fffffffe07fff00

def z554 : W := mkw 0x97dfdfdfd80a8028 0x72fbfbfbfb015005 0xf7fffffffc1e007e 0x3effffffff83c00f

def z555 : W := mkw 0x0000200004230088 0x0000040000846011 0x000000000066019a 0x60000000000cc033

def z556 : W := mkw 0x000004056c0042a8 0x00000080ad800855 0x00000000fc000000 0x000000001f800000

def z557 : W := mkw 0x084001ba00800550 0x01080037401000aa 0x000001e000000000 0x0000003c00000000

def z558 : W := mkw 0x673cea00037fb000 0xace79d40006ff600 0x0a18e00003fff807 0x01431c00007fff00

def z559 : W := mkw 0x184104ece0804e62 0x0308209d9c1009cc 0xbc0701ece381fe61 0x9780e03d9c703fcc

def z560 : W := mkw 0x000002002008c220 0x0000004004011844 0x080000000019c665 0x81000000000338cc

def z561 : W := mkw 0x060cea00026ba000 0x00c19d40004d7400 0xee1ffe0003fff807 0x1dc3ffc0007fff00

def z562 : W := mkw 0x079efa00002b8000 0x20f3df4000057000 0xeffffe00007fc007 0x1dffffc0000ff800

def z563 : W := mkw 0x8604a13016e12581 0x10c0942602dc24b0 0x9e00e1f01fe00780 0xd3c01c3e03fc00f0

def z564 : W := mkw 0x8605a17092e12d01 0x10c0b42e125c25a0 0xae07e1e003e1f801 0x15c0fc3c007c3f00

def z565 : W := mkw 0x019a580000000000 0x20334b0000000000 0x41f81e0000000000 0x083f03c000000000

def z566 : W := mkw 0x38e336ece5bbdeea 0x071c66dd9cb77bdd 0xfde71fece3ffffff 0xffbce3fd9c7fffff

def z567 : W := mkw 0x2820020001189062 0x050400400023120c 0x0000000000180064 0x000000000003000c

def z568 : W := mkw 0x6fbefa2003ffb550 0xadf7df44007ff6aa 0xeffffe0003ffffff 0xfdffffc0007fffff

def z569 : W := mkw 0x471869130e670198 0x08e30d2261cce033 0x0218e0131c66019a 0x60431c02638cc033

def z570 : W := mkw 0x00086c056c214280 0x00010d80ad842850 0xfa18fe1ffc61c781 0xdf431fc3ff8c38f0

def z571 : W := mkw 0x4f7101faa3d44f50 0x09ee203f547a89ea 0xffff01ffe3ffffff 0xffffe03ffc7fffff

def z572 : W := mkw 0x61ba5e05491e9028 0xac374bc0a923d205 0x41f81e0f001e007e 0x283f03c1e003c00f

def z573 : W := mkw 0x0840008a00000050 0x010800114000000a 0x0000000f00000078 0x20000001e000000f

def z574 : W := mkw 0x186104ece1904e62 0x030c209d9c3209cc 0xdde001ece3980664 0x9bbc003d9c7300cc

def z575 : W := mkw 0xf7fffbda937fb000 0xfeffff7b526ff600 0xefffffe003fff807 0x1dfffffc007fff00

def z576 : W := mkw 0x18c314ece0804e62 0x0318629d9c1009cc 0xf5e71fece0000660 0x9ebce3fd9c0000cc

def z577 : W := mkw 0x7ff796ece3dcfe62 0xaffef2dd9c7b9fcc 0xfde71fece399fe65 0x9fbce3fd9c733fcc

def z578 : W := mkw 0x97dffddffc214280 0x72fbffbbff842850 0xfffffffffc61c781 0xdfffffffff8c38f0

def z579 : W := mkw 0x473ce80003772000 0xa8e79d00006ee400 0xcff8e00003fe0006 0x19ff1c00007fc000

def z580 : W := mkw 0x10c2148c40000000 0x0218429188000000 0x41e01e0c00000000 0x083c03c180000000

def z581 : W := mkw 0x8605a15096612181 0x10c0b42a12cc2430 0xb607e1f0fc600180 0x56c0fc3e1f8c0030

def z582 : W := mkw 0x06010170a2c04f00 0x00c0202e145809e0 0xbe0701f0e3e1ff81 0xd7c0e03e1c7c3ff0

def z583 : W := mkw 0x4820202027f56fd1 0x0904040404feadfa 0x0800000003ffffff 0xe1000000007fffff

def z584 : W := mkw 0x60200200011e9000 0x8c0400400023d200 0x00000000001e0006 0x000000000003c000

def z585 : W := mkw 0x00086e05482b8000 0x00010dc0a9057000 0xfa18fe1ffc7fc007 0x1f431fc3ff8ff800

def z586 : W := mkw 0x386106ece198de62 0x070c20dd9c331bcc 0x180001ece399fe65 0x8300003d9c733fcc

def z587 : W := mkw 0xe7bffb7093ffbd01 0xbcf7ff6e127ff7a0 0xefffffe003fff807 0x1dfffffc007fff00

def z588 : W := mkw 0x80010040b4004a81 0x1000200816800950 0x00000000fc000000 0x000000001f800000

def z589 : W := mkw 0x0000013000800500 0x00000026001000a0 0x100001f000000780 0xc200003e000000f0

def z590 : W := mkw 0x4f30002003d40550 0x09e60004007a80aa 0xcff8000003fe07fe 0xf9ff0000007fc0ff

def z591 : W := mkw 0x008ed80000000000 0x2011db0000000000 0x2007fe0000000000 0x0400ffc000000000

def z592 : W := mkw 0x4f7869bb0ff705d8 0x09ef0d3761fee0bb 0xdff8e1ff1ffe07fe 0xfbff1c3fe3ffc0ff

def z593 : W := mkw 0x11da5c8f48000000 0x623b4b91e9000000 0xf3f8fe1ffc000000 0x1e7f1fc3ff800000

def z594 : W := mkw 0xc71cc9131a440110 0x78e3992263488022 0x0218e0131c66019a 0x60431c02638cc033

def z595 : W := mkw 0x4770019a03540000 0x08ee0033406a8000 0xdff801ff03fe0006 0x1bff003fe07fc000

def z596 : W := mkw 0x8605a370b6ebefa9 0x10c0b46e16dd7df5 0xbe07e1f0ffffffff 0xf7c0fc3e1fffffff

def z597 : W := mkw 0x0f5001ba00800550 0x01ea0037401000aa 0xd7f801ff000007f8 0xfaff003fe00000ff

def z598 : W := mkw 0x8000011318000000 0x5000002263000000 0x000000131c000000 0x0000000263800000

def z599 : W := mkw 0x97dfddffdac00500 0x72fbfbbffb5800a0 0xffffffffffe00780 0xdffffffffffc00f0

def z600 : W := mkw 0x78e316ece3dcdf72 0x0f1c62dd9c7b9bee 0xfde71fece3ffffff 0xffbce3fd9c7fffff

def z601 : W := mkw 0x0000000000000000 0x0000000000000000 0x021800130066019a 0x60430002600cc033

def z602 : W := mkw 0xb687b774f6e9ffa3 0x16d0f6ee9edd3ff4 0xbe07fff0ffe1ff81 0xd7c0fffe1ffc3ff0

def z603 : W := mkw 0x4000200002672000 0x88000400004ce400 0x0000000000660002 0x00000000000cc000

def z604 : W := mkw 0x38e316ccc1189062 0x071c62d99823120c 0xf5e71fece0180064 0x1ebce3fd9c03000c

def z605 : W := mkw 0x860deb70b6ebef81 0x10c1bd6e16dd7df0 0xfe1ffff0ffffff87 0xdfc3fffe1ffffff0

def z606 : W := mkw 0xf7ffdddfdb543000 0xfefffbbbfb6a8600 0xf7ffffffff803800 0x1efffffffff00700

def z607 : W := mkw 0x4000000002440110 0x0800000000488022 0x000000000066019a 0x60000000000cc033

def z608 : W := mkw 0x7ffffffee3ffff72 0xafffffffdc7fffee 0xffffffffe3ffffff 0xfffffffffc7fffff

def z609 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0x51e01fece0180664 0x8a3c03fd9c0300cc

def z610 : W := mkw 0x979fdd57d8000000 0x72f3fbaafb000000 0x221ffe13fc000000 0x0443ffc27f800000

def z611 : W := mkw 0xfffffffcf7ffffe3 0xbfffffff9efffffc 0xfffffffcffffffe7 0xdfffffff9ffffffc

def z612 : W := mkw 0x800dee45fc2beaa9 0x1001bdc8bf857d55 0x2007fe00fc01f801 0x0400ffc01f803f00

def z613 : W := mkw 0x0000222026ebefa9 0x0000044404dd7df5 0x0800000003ffffff 0xe1000000007fffff

def z614 : W := mkw 0x38eb5eede99ade6a 0x071d6bddbd335bcd 0xfdff1fefe39ffe7f 0xbfbfe3fdfc73ffcf

def z615 : W := mkw 0xcf7581fa93d42d51 0x19eeb03f527a85aa 0xdfff01ff03fe3ffe 0xfbffe03fe07fc7ff

def z616 : W := mkw 0x80010170b4804f81 0x1000202e169009f0 0xbc0701f0ff81ff81 0xd780e03e1ff03ff0

def z617 : W := mkw 0x38e336ece7f9ffe3 0x071c66dd9cff3ffc 0xfde71fece3f9ffe5 0xdfbce3fd9c7f3ffc

def z618 : W := mkw 0xbfffddffd9901c42 0x77fffbbffb320388 0xf7ffffffff803800 0x1efffffffff00700

def z619 : W := mkw 0x4f786bba03ff8550 0x09ef0d77407ff0aa 0xfff8ffff03ffc7ff 0xffff1fffe07ff8ff

def z620 : W := mkw 0x8605a040b6616a81 0x10c0b40816cc2d50 0xae07e000ffe1f801 0x15c0fc001ffc3f00

def z621 : W := mkw 0x000000010c000088 0x0000000021800011 0x000000131c000198 0x6000000263800033

def z622 : W := mkw 0x97dffddfde612181 0x72fbffbbfbcc2430 0xf7fffffffc600180 0x5effffffff8c0030

def z623 : W := mkw 0x875581da90000000 0x10eab03b52000000 0xf7ffe1fffc000000 0x1efffc3fff800000

def z624 : W := mkw 0x5ff315fec3d40550 0x0bfe62bfd87a80aa 0xffff1fffe3fe07fe 0xffffe3fffc7fc0ff

def z625 : W := mkw 0x0008480108020008 0x0001090021004001 0x001800030006001a 0x200300006000c003

def z626 : W := mkw 0x3ee317fce3d8df62 0x07dc62ff9c7b1bec 0xffe71ffce3f9ffe5 0xdffce3ff9c7f3ffc

def z627 : W := mkw 0x7ff311fa83d41d52 0x0ffe623f507a83aa 0x05e701e003803800 0x00bce03c00700700

def z628 : W := mkw 0x4f74a1ba03f52550 0x09ee9437407ea4aa 0xffffe1ff03ffffff 0xfffffc3fe07fffff

def z629 : W := mkw 0x4f7021ba27f547d0 0x09ee043744fea8fa 0xfff8e1ffffffc7ff 0xffff1c3ffffff8ff

def z630 : W := mkw 0xb8e7b6ecf5b9fee3 0x171cf6dd9eb73fdc 0xfde7ffecff99fe65 0x9fbcfffd9ff33fcc

def z631 : W := mkw 0x97dfdfdff808c220 0x72fbfbfbff011844 0xfffffffffc19c665 0x9fffffffff8338cc

def z632 : W := mkw 0x00086e056c2bc2a8 0x00010dc0ad857855 0x2218fe13fc67c19b 0x64431fc27f8cf833

def z633 : W := mkw 0x38e216ac41989462 0x071c42d58833128c 0xdde01fec03980664 0x9bbc03fd807300cc

def z634 : W := mkw 0xdfffddffdbd40550 0x7bfffbbffb7a80aa 0xf7ffffffff800000 0x1efffffffff00000

def z635 : W := mkw 0x49786e8f6d3fc2f8 0x092f0dd1eda7f85f 0xfbf8fe1ffc7fc7ff 0xff7f1fc3ff8ff8ff

def z636 : W := mkw 0x4820000001140050 0x090400000022800a 0x00000000001e007e 0x200000000003c00f

def z637 : W := mkw 0x0000200006612181 0x0000040000cc2430 0x0000000000600180 0x40000000000c0030

def z638 : W := mkw 0x91dfdccfd8000000 0x723bfb99fb000000 0x61fffe0ffc000000 0x0c3fffc1ff800000

def z639 : W := mkw 0x6820222023fffe62 0x8d040444047fffcc 0x0800000003fffe67 0x81000000007fffcc

def z640 : W := mkw 0x80012170b6e16f81 0x1000242e16dc2df0 0x180001f0ffe1ff81 0xc300003e1ffc3ff0

def z641 : W := mkw 0x884101fab4804fd1 0x1108203f569009fa 0x100001fffc0007f8 0xe200003fff8000ff

def z642 : W := mkw 0x67302200037fb000 0x8ce60440006ff600 0xcff8000003fff807 0x19ff0000007fff00

def z643 : W := mkw 0x9645a5fffee16f81 0x52c8b4bfffdc2df0 0xbe07e1ffffe1ff81 0xd7c0fc3ffffc3ff0

def z644 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0xdde001ec03980664 0x9bbc003d807300cc

def z645 : W := mkw 0xb7dfdfdff808da22 0x76fbfbfbff011b44 0xf7fffffffc01f801 0x1effffffff803f00

def z646 : W := mkw 0x8605817092c00500 0x10c0b02e125800a0 0xbe07e1f0ffe00780 0xd7c0fc3e1ffc00f0

def z647 : W := mkw 0xe7bffb50937fb000 0xbcf7ff6a126ff600 0xfffffff0fffff807 0x1ffffffe1fffff00

def z648 : W := mkw 0x38e312e8a198de62 0x071c625d14331bcc 0x0de701e00399fe65 0x81bce03c00733fcc

def z649 : W := mkw 0x6ffeffbf6ffff7f8 0xadffdff7edfffeff 0xffffffffffffffff 0xffffffffffffffff

def z650 : W := mkw 0x800dee45fc2beaa9 0x1001bdc8bf857d55 0xfa1ffe1ffc7fffff 0xff43ffc3ff8fffff

def z651 : W := mkw 0x4710011202440110 0x08e2002240488022 0xda18001f007e07fe 0xfb430003e00fc0ff

def z652 : W := mkw 0x67beda00011e9000 0xacf7db400023d200 0xe7fffe00001e0006 0x1cffffc00003c000

def z653 : W := mkw 0x0000200004210080 0x0000040000842010 0x0200e0101c600180 0x40401c02038c0030

def z654 : W := mkw 0x0008480000000000 0x0001090000000000 0xe218fe0000000000 0x1c431fc000000000

def z655 : W := mkw 0x4730013003d40500 0x08e60026007a80a0 0xdff801f003fe0786 0xdbff003e007fc0f0

def z656 : W := mkw 0xce25a170b7f56fd1 0x19c4b42e16feadfa 0xbe07e1f0ffffffff 0xf7c0fc3e1fffffff

def z657 : W := mkw 0x28a212202198de62 0x0514424404331bcc 0xede71e000399fe65 0x9dbce3c000733fcc

def z658 : W := mkw 0x8605817092c02d01 0x10c0b02e125805a0 0xb607e1f0ff803800 0x16c0fc3e1ff00700

def z659 : W := mkw 0x0008680000230000 0x00010d0000046000 0x0218e00000660002 0x00431c00000cc000

def z660 : W := mkw 0x4750019a02440110 0x08ea003340488022 0xd7f801ff0066019a 0x7aff003fe00cc033

def z661 : W := mkw 0x5ffa5dbf4bd40550 0x6bff4bb7e97a80aa 0xdff81fff03fe07fe 0xfbff03ffe07fc0ff

def z662 : W := mkw 0x084005bf6c8047f8 0x010800b7ed9008ff 0x100001fffc0007f8 0xe200003fff8000ff

def z663 : W := mkw 0x471cee056e6fe2a8 0xa8e39dc0adcdfc55 0xfa18fe1ffc7fc7ff 0xff431fc3ff8ff8ff

def z664 : W := mkw 0x00002200242bc2a8 0x0000044004857855 0xda18001f007fc7ff 0xfb430003e00ff8ff

def z665 : W := mkw 0x0000200024214280 0x0000040004842850 0x2000e000fc01c001 0x04001c001f803800

def z666 : W := mkw 0x0600013002c00500 0x00c00026005800a0 0xde1801ff03fe07fe 0xfbc3003fe07fc0ff

def z667 : W := mkw 0xbfffdfdfd9189062 0x77fffbfbfb23120c 0xf7fffffffc180064 0x1effffffff83000c

def z668 : W := mkw 0xeffffbfab7ffffd1 0xbdffff7f56fffffa 0xffffffffffffffff 0xffffffffffffffff

def z669 : W := mkw 0x060cee056e6be2a8 0x00c19dc0adcd7c55 0xfe1ffe1fffffffff 0xffc3ffc3ffffffff

def z670 : W := mkw 0x97dffddfda612000 0x72fbffbbfb4c2400 0xffffffffffe1f801 0x1ffffffffffc3f00

def z671 : W := mkw 0xcf7101fab7d44fd1 0x19ee203f56fa89fa 0xdff801fffffe07fe 0xfbff003fffffc0ff

def z672 : W := mkw 0x00002200242bc2a8 0x0000044004857855 0xba00e010fc7fc7ff 0xf7401c021f8ff8ff

def z673 : W := mkw 0x67befa00277ff2a8 0xacf7df4004effe55 0xeffffe0003ffffff 0xfdffffc0007fffff

def z674 : W := mkw 0x979fdc45d8000000 0x72f3fb88bb000000 0xe7fffe00fc000000 0x1cffffc01f800000

def z675 : W := mkw 0x1040048f48000000 0x42080091e9000000 0x0000000f00000000 0x00000001e0000000

def z676 : W := mkw 0x4970008a01140050 0x092e00114022800a 0x01e0000000000000 0x003c000000000000

def z677 : W := mkw 0x4118480000060000 0xa82309000000c000 0x0018000000060002 0x000300000000c000

def z678 : W := mkw 0x0800002000800550 0x01000004001000aa 0x00000000000007f8 0xe0000000000000ff

def z679 : W := mkw 0x000868010c230088 0x00010d0021846011 0x0000e0001c000000 0x00001c0003800000

def z680 : W := mkw 0x38e310e881901c42 0x071c621d10320388 0xdde701ec03983e64 0x9bbce03d807307cc

def z681 : W := mkw 0xf7f791da93543000 0xfefef23b526a8600 0x05e701e003803800 0x00bce03c00700700

def z682 : W := mkw 0x97dfffdffc2bc2a8 0x72fbfffbff857855 0xf7fffffffc01c001 0x1effffffff803800

def z683 : W := mkw 0x80010575fc804fa9 0x100020aebf9009f5 0x100001fffc0007f8 0xe200003fff8000ff

def z684 : W := mkw 0xb8e317fff998de62 0x571c62ffff331bcc 0xfde71fffff99fe65 0x9fbce3fffff33fcc

def z685 : W := mkw 0x0004a00000212000 0x0000940000042400 0x2007e0000001f801 0x0400fc0000003f00

def z686 : W := mkw 0x79fb5eece19ede62 0xaf3f6bdd9c33dbcc 0xfdff1fece39ffe67 0x9fbfe3fd9c73ffcc

def z687 : W := mkw 0xcf75a1fab7f56fd1 0x19eeb43f56feadfa 0xbfe7e1f0ffe1ff81 0xd7fcfc3e1ffc3ff0

def z688 : W := mkw 0x90c315dfd8000000 0x521862bbfb000000 0xf5e71ffffc000000 0x1ebce3ffff800000

def z689 : W := mkw 0x28286e256dbbdeea 0x05050dc4adb77bdd 0xfa18fe1fffffffff 0xff431fc3ffffffff

def z690 : W := mkw 0x97d795ded0000000 0x72faf2bbda000000 0xf5e71fece0000000 0x1ebce3fd9c000000

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000000007e07fe 0xe1000000000fc0ff

def z692 : W := mkw 0x0000000024004280 0x0000000004800850 0x10000010fc000780 0xc20000021f8000f0

def z693 : W := mkw 0x8605a150b4214280 0x10c0b42a16842850 0xbe07e1f0fc61c781 0xd7c0fc3e1f8c38f0

def z694 : W := mkw 0x60286a00037fb000 0x8c050d40006ff600 0xea18fe0003fff807 0x1d431fc0007fff00

def z695 : W := mkw 0xe7b7917093d43d01 0xbcf6f22e127a87a0 0x05e701e003803800 0x00bce03c00700700

def z696 : W := mkw 0xb08ffe45d82bb000 0xf611ffc8bb057600 0x2007fe00fc01f801 0x0400ffc01f803f00

def z697 : W := mkw 0x0000002020804e00 0x00000004041009c0 0x080000000381fe01 0x8100000000703fc0

def z698 : W := mkw 0x0604a00002612000 0x00c09400004c2400 0x0200e00000600000 0x00401c00000c0000

def z699 : W := mkw 0x38a31664e198de62 0x071462cc9c331bcc 0x28071e00e399fe65 0x8500e3c01c733fcc

def z700 : W := mkw 0x0000000000000000 0x0000000000000000 0xca180000007e0006 0x19430000000fc000

def z701 : W := mkw 0x184106ece088ce62 0x030820dd9c1119cc 0xf8001fece019c665 0x9f0003fd9c0338cc

def z702 : W := mkw 0x8e65a1f8b7f16fc1 0x11ccb43f16fe2df8 0xffe7e1fcfff9ffe5 0xdffcfc3f9fff3ffc

def z703 : W := mkw 0x4f70019a01140050 0x09ee00334022800a 0xd7f801ff001e007e 0x3aff003fe003c00f

def z704 : W := mkw 0x0000200000210000 0x0000040000042000 0xaa00e0000061c001 0x15401c00000c3800

def z705 : W := mkw 0x6624a200037fb000 0x8cc49440006ff600 0xae07e00003fff807 0x15c0fc00007fff00

def z706 : W := mkw 0xb8efdeedf998de62 0x771dfbddbf331bcc 0xfde7ffecff99fe65 0x9fbcfffd9ff33fcc

def z707 : W := mkw 0x20a692000118b000 0xa414d24000231600 0xede71e000399f805 0x1dbce3c000733f00

def z708 : W := mkw 0x20a2120001189000 0x0414424000231200 0xfde71e0c0399fe65 0x9fbce3c180733fcc

def z709 : W := mkw 0x67b694056f5472a8 0xacf6d280adea8e55 0x15e7001fff803ff8 0xe2bce003fff007ff

def z710 : W := mkw 0x67ba5a00035e9000 0xacf74b40006bd200 0xefff1e0003fff807 0x1dffe3c0007fff00

def z711 : W := mkw 0x00086e056c2bc2a8 0x00010dc0ad857855 0x5218fe1ffc7e07fe 0xea431fc3ff8fc0ff

def z712 : W := mkw 0x91dfdccfd8000000 0x723bfb99fb000000 0xf5ffffeffc000000 0x1ebffffdff800000

def z713 : W := mkw 0xa6a6b3101779b181 0x14d4d66202ef3630 0xefe7fe101ff9f985 0x5dfcffc203ff3f30

def z714 : W := mkw 0x90cfdccdd8000000 0x7219fb99bb000000 0xf7fffffffc000000 0x1effffffff800000

def z715 : W := mkw 0x38e316ece198df72 0x071c62dd9c331bee 0xfde71fece399fffd 0xffbce3fd9c733fff

def z716 : W := mkw 0x184104efe8804e62 0x4308209dfd1009cc 0x100001efe0000660 0x8200003dfc0000cc

def z717 : W := mkw 0x97dfdddfd8000028 0x72fbfbbbfb000005 0xf7fffffffc000078 0x3effffffff80000f

def z718 : W := mkw 0x86058170b2c04f00 0x10c0b02e165809e0 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z719 : W := mkw 0xc605a170b6e76f81 0x98c0b42e16dcedf0 0xbe07e1f0ffe7ff83 0xd7c0fc3e1ffcfff0

def z720 : W := mkw 0x8715a170b6e16f81 0x10e2b42e16dc2df0 0xffffe1f0ffe1ff81 0xdffffc3e1ffc3ff0

def z721 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0xae07e1e0ffe1f801 0x15c0fc3c1ffc3f00

def z722 : W := mkw 0x5f5105fee2c44f72 0x0bea20bfdc5889ee 0x121801ffe06607fa 0xe243003ffc0cc0ff

def z723 : W := mkw 0xaf3ccb333998de62 0x75e7996667331bcc 0x0a18e0131f99fe65 0x81431c0263f33fcc

def z724 : W := mkw 0x30e316cce118da22 0x061c62d99c231b44 0xfde71fece399f805 0x1fbce3fd9c733f00

def z725 : W := mkw 0x0820222025bbc6e8 0x0104044404b778dd 0x0800000003ffc7ff 0xe1000000007ff8ff

def z726 : W := mkw 0x67befa010f7fb088 0xacf7df4021eff611 0xfffffe1f1fffffff 0xffffffc3e3ffffff

def z727 : W := mkw 0x90cfdddfd8000000 0x7219fbbbfb000000 0xf5e7fffffc000000 0x1ebcffffff800000

def z728 : W := mkw 0x20a23200013b9000 0x0414464000277200 0xede71e0003fff807 0x1dbce3c0007fff00

def z729 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0x53f801ff007e07fe 0xea7f003fe00fc0ff

def z730 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0xffffffffff81f801 0x1ffffffffff03f00

def z731 : W := mkw 0x38eb78e98db31cca 0x071d6f1d31b66399 0x07ffe1f31fe6399a 0x60fffc3e63fcc733

def z732 : W := mkw 0x67beda00035c9000 0x2cf7db40006b9200 0xeffffe0003fff807 0x1dffffc0007fff00

def z733 : W := mkw 0x26a692000358b000 0x04d4d240006b1600 0xede71e000399f805 0x1dbce3c000733f00

def z734 : W := mkw 0x67beda00011e9000 0xacf7db400023d200 0xeffffe00039ff807 0x1dffffc00073ff00

def z735 : W := mkw 0xc975a0cab5356ad1 0x192eb41956a6ad5a 0x61ffe00ffc1ff87f 0x2c3ffc01ff83ff0f

def z736 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0x65e71fece399f865 0x0cbce3fd9c733f0c

def z737 : W := mkw 0x908ffe45fc2beaa9 0x7211ffc8bf857d55 0x2007fe00fc01f801 0x0400ffc01f803f00

def z738 : W := mkw 0x8605a150b6616280 0x10c0b42a16cc2c50 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z739 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0xffe7fffcff99fe65 0x9ffcffff9ff33fcc

def z740 : W := mkw 0x104104ece0804e00 0x0208209d9c1009c0 0x100001ece0000600 0x8200003d9c0000c0

def z741 : W := mkw 0x979fdd55d8000000 0x72f3fbaabb000000 0xf7fffff0fc000000 0x1efffffe1f800000

def z742 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0xbde71fe0e381fe01 0x97bce3fc1c703fc0

def z743 : W := mkw 0x184104ece4804fe3 0x0308209d9c9009fc 0x100001ece00007e0 0xc200003d9c0000fc

def z744 : W := mkw 0x87dfd9da90000000 0x30fbfb3b52000000 0xf7fffffffc000000 0x1effffffff800000

def z745 : W := mkw 0x38e312e881989c42 0x071c625d10331388 0x25e71fe00381f801 0x04bce3fc00703f00

def z746 : W := mkw 0x4f7001ba03d42d51 0x09ee0037407a85aa 0xdff801ff03fe3ffe 0xfbff003fe07fc7ff

def z747 : W := mkw 0x279efa00026bb000 0xa4f3df40004d7600 0xeffffe0003e1f801 0x1dffffc0007c3f00

def z748 : W := mkw 0x10c314ccc0000000 0x0218629998000000 0xfde71fece381f801 0x1fbce3fd9c703f00

def z749 : W := mkw 0x86058170b2c06f01 0x10c0b02e16580de0 0xbe07e1f0ff81fe01 0x97c0fc3e1ff03fc0

def z750 : W := mkw 0x0f5001ba00800550 0x01ea0037401000aa 0xdff801ff007e07fe 0xfbff003fe00fc0ff

def z751 : W := mkw 0x26a6920001189000 0x04d4d24000231200 0xefe7fe000399f805 0x1dfcffc000733f00

def z752 : W := mkw 0x67ba7a00037f9000 0x0cf74f40006ff200 0xeffffe0003fff807 0x1dffffc0007fff00

def z753 : W := mkw 0x4f7000a803d40440 0x09ee0015007a8088 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z754 : W := mkw 0x8005a060b4a16e81 0x1000b40c16942dd0 0x2407e1e0ff81f801 0x0480fc3c1ff03f00

def z755 : W := mkw 0x471ce91202672110 0xa8e39d22404ce422 0x0218e00000660002 0x00431c00000cc000

def z756 : W := mkw 0x00086c056c214280 0x00010d80ad842850 0xfa18fe1ffc7fc7ff 0xff431fc3ff8ff8ff

def z757 : W := mkw 0xbee6b79c5779b1e3 0x17dcd6f38aef363c 0x43e0fe1c1c7801e4 0x487c1fc3838f003c

def z758 : W := mkw 0x904105fffc804fa9 0x520820bfff9009f5 0x100001fffc0007f8 0xe200003fff8000ff

def z759 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0xb7e7fff0fc000000 0x16fcfffe1f800000

def z760 : W := mkw 0x67b21312035c9110 0x0cf64262406b9222 0xefff1e1303fff99f 0x7dffe3c2607fff33

def z761 : W := mkw 0xa08ffe45fc2bfaa9 0xb411ffc8bf857f55 0x2007fe00fc01f801 0x0400ffc01f803f00

def z762 : W := mkw 0xe1bb5b70b59edf81 0xbc376b6e16b3dbf0 0x51f81ff0fc1e0786 0xca3f03fe1f83c0f0

def z763 : W := mkw 0x90c794ccd0000000 0x1218f2999a000000 0xf5e7ffecfc000000 0x1ebcfffd9f800000

def z764 : W := mkw 0x2820222025b9fee3 0x0504044404b73fdc 0x080000000399fe65 0x8100000000733fcc

def z765 : W := mkw 0x67befa010f7fb088 0xacf7df4021eff611 0xeffffe001ffff807 0x1dffffc003ffff00

def z766 : W := mkw 0xc71ce91012672000 0xb8e39d22024ce400 0x0218e0101c660002 0x00431c02038cc000

def z767 : W := mkw 0x4770019a03540000 0x08ee0033406a8000 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z768 : W := mkw 0x30e312c881189000 0x061c625910231200 0xede71fe00399f805 0x1dbce3fc00733f00

def z769 : W := mkw 0x0604a13026e16780 0x00c0942604dc2cf0 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z770 : W := mkw 0x97d7b3dab42bc2a8 0x72faf67b56857855 0x0de701e0007fc7ff 0xe1bce03c000ff8ff

def z771 : W := mkw 0xe7befb131f7fb181 0xfcf7df6263eff630 0xeffffe131ffff987 0x5dffffc263ffff30

def z772 : W := mkw 0xd7dfdddfda442000 0xfafbfbbbfb488400 0xf7fffffffc000000 0x1effffffff800000

def z773 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0xf5e71fece381f801 0x1ebce3fd9c703f00

def z774 : W := mkw 0x10c316ece088ce20 0x021862dd9c1119c4 0xfde71fece399fe65 0x9fbce3fd9c733fcc

def z775 : W := mkw 0x67befa02037fb010 0xacf7df40406ff602 0xeffffe0303fff81f 0x3dffffc0607fff03

def z776 : W := mkw 0xf06127dfdb7fb000 0xde0c24fbfb6ff600 0x180001fffffff807 0x0300003fffffff00

def z777 : W := mkw 0x67b69200035cb000 0xacf6d240006b9600 0xefff1e0003fff807 0x1dffe3c0007fff00

def z778 : W := mkw 0x20aefa00013bb000 0xa415df4000277600 0x25e7fe000381f801 0x04bcffc000703f00

def z779 : W := mkw 0x11da7caf6ee16f81 0x623b4f95eddc2df0 0x49f81e0f03e1ff81 0xc93f03c1e07c3ff0

def z780 : W := mkw 0x20aeda0001189000 0x2415db4000231200 0xede7fe000399f805 0x1dbcffc000733f00

def z781 : W := mkw 0x086001ba01900550 0x010c0037403200aa 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z782 : W := mkw 0x60a21200011e9000 0x8c1442400023d200 0xede71e00039ff807 0x1dbce3c00073ff00

def z783 : W := mkw 0x4f786fbf6fffc7f8 0x09ef0df7edfff8ff 0x25e0ffe0ff81c001 0x04bc1ffc1ff03800

def z784 : W := mkw 0x67befa00037fb110 0xacf7df40006ff622 0xeffffe0003fff99f 0x7dffffc0007fff33

def z785 : W := mkw 0x38e316eded98deea 0x071c62ddbdb31bdd 0xffff1fffffffffff 0xffffe3ffffffffff

def z786 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0x35e7fffffc000000 0x06bcffffff800000

def z787 : W := mkw 0x20a2120001189000 0x0414424000231200 0xffff1e1f03ffffff 0xffffe3c3e07fffff

def z788 : W := mkw 0x67b21200035c9000 0x0cf64240006b9200 0xede71e000399f805 0x1dbce3c000733f00

def z789 : W := mkw 0xc71ce91216672191 0xb8e39d2242cce432 0x0218e0131c66019a 0x60431c02638cc033

def z790 : W := mkw 0x6820222027ffdffa 0x0d04044404fffbff 0x0800000003ffffff 0xe1000000007fffff

def z791 : W := mkw 0x38e316ecc1989c62 0x071c62dd9833138c 0xede71fec0399f865 0x1dbce3fd80733f0c

def z792 : W := mkw 0x20a2120001189000 0x0414424000231200 0xefff1e0003fff807 0x1dffe3c0007fff00

def z793 : W := mkw 0x10c314ccc0000000 0x0218629998000000 0xf7e7fffcfc000000 0x1efcffff9f800000

def z794 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0x53f8fffffc000000 0x0a7f1fffff800000

def z795 : W := mkw 0x61befa00037fb000 0xac37df40006ff600 0x69fffe0003fff807 0x0d3fffc0007fff00

def z796 : W := mkw 0x20e2128801189000 0x041c425100231200 0xfde71fec0399f805 0x1fbce3fd80733f00

def z797 : W := mkw 0x67b23200037fb000 0x8cf64640006ff600 0xefff1e0003fff807 0x1dffe3c0007fff00

def z798 : W := mkw 0x879ef9131e612181 0x70f3df2263cc2430 0xeffffe131fe1f981 0x5dffffc263fc3f30

def z799 : W := mkw 0x38ea5e8d491a906a 0x071d4bd1a923520d 0x41e01e0c00180064 0x083c03c18003000c

def z800 : W := mkw 0x96cfddddd8000000 0x12d9fbbbbb000000 0xf7fffffffc000000 0x1effffffff800000

def z801 : W := mkw 0x9fdfdddfd8000062 0x73fbfbbbfb00000c 0xf7fffffffc000060 0x1effffffff80000c

def z802 : W := mkw 0x471ce91002672100 0xa8e39d22004ce420 0x0218e01000660182 0x40431c02000cc030

def z803 : W := mkw 0x60a21200035c9000 0x0c144240006b9200 0xede71e0003fff807 0x1dbce3c0007fff00

def z804 : W := mkw 0x4750019a02440110 0x08ea003340488022 0xdff801ff007e07fe 0xfbff003fe00fc0ff

def z805 : W := mkw 0x48284c254bd40550 0x09050984a97a80aa 0xfa18fe1ffffe07fe 0xff431fc3ffffc0ff

def z806 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0xfffffffffc600780 0xdfffffffff8c00f0

def z807 : W := mkw 0xe7befb111f7fb189 0xbcf7df6223eff631 0xeffffe131ffff99f 0x7dffffc263ffff33

def z808 : W := mkw 0xd8afdc65dbd40550 0x7b15fb8cbb7a80aa 0x2807fe00fffe07fe 0xe500ffc01fffc0ff

def z809 : W := mkw 0x28a2120001189062 0x051442400023120c 0xede71e000399f865 0x1dbce3c000733f0c

def z810 : W := mkw 0x97dfdddfda402101 0x72fbfbbbfb480420 0xf7fffffffc000000 0x1effffffff800000

def z811 : W := mkw 0xb08ffe45fc2bdaaa 0x7611ffc8bf857b55 0x2007fe00fc01f801 0x0400ffc01f803f00

def z812 : W := mkw 0x884105fffc804ff9 0x110820bfff9009ff 0x100001fffc0007f8 0xe200003fff8000ff

def z813 : W := mkw 0x67befb12037fb000 0xacf7df62406ff600 0xeffffe1303fff807 0x1dffffc2607fff00

def z814 : W := mkw 0x904105fcf4804f81 0x120820bf9e9009f0 0x100001fcfc000780 0xc200003f9f8000f0

def z815 : W := mkw 0x8605a060b6e16e81 0x10c0b40c16dc2dd0 0xbe07e1e0ffe1fe01 0x97c0fc3c1ffc3fc0

def z816 : W := mkw 0x984105fffc804fe3 0x530820bfff9009fc 0x100001fffc0007e0 0xc200003fff8000fc

def z817 : W := mkw 0x00086e056c2bc2a8 0x00010dc0ad857855 0xfe1ffe1fffffffff 0xffc3ffc3ffffffff

def z818 : W := mkw 0x17dfdccdc8000000 0x22fbfb99b9000000 0xf7fffffffc000000 0x1effffffff800000

def z819 : W := mkw 0x184104ece4804ee2 0x0308209d9c9009dc 0x100001fcfc0007e0 0xc200003f9f8000fc

def z820 : W := mkw 0x67b6b200037db000 0x0cf6d640006fb600 0xeffffe0003fff807 0x1dffffc0007fff00

def z821 : W := mkw 0x5f5decece2e76e62 0xabebbd9d9c5cedcc 0x1218e1ece0660662 0x82431c3d9c0cc0cc

def z822 : W := mkw 0x67befa00077fb088 0xacf7df4000eff611 0xeffffe0003fff99f 0x7dffffc0007fff33

def z823 : W := mkw 0x79fa5e8f491e9050 0xef3f4bd1e923d20a 0x41f81e0f001e007e 0x283f03c1e003c00f

def z824 : W := mkw 0x860dcf75dacaad29 0x10c1b9eebb5955a5 0x441f1fef039e387e 0x2883e3fde073c70f

def z825 : W := mkw 0x184104ece4804eea 0x0308209d9c9009dd 0x100001ece00007f8 0xe200003d9c0000ff

def z826 : W := mkw 0x30a31664e198de22 0x061462cc9c331bc4 0xfde71fe0e399fe05 0x9fbce3fc1c733fc0

def z827 : W := mkw 0x80058060b0804e00 0x1000b00c161009c0 0xbc07e1e0ff81fe01 0x9780fc3c1ff03fc0

def z828 : W := mkw 0x875ccd9f58000000 0x70eb99b3eb000000 0xf7f8fffffc000000 0x1eff1fffff800000

def z829 : W := mkw 0x77931756e24cdb32 0x0ef262eadc499b66 0x221f1e13e067f99b 0x6443e3c27c0cff33

def z830 : W := mkw 0x67befb12037fb110 0xacf7df62406ff622 0xfffffe1f03ffffff 0xffffffc3e07fffff

def z831 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0x4dff1e0003fff807 0x09bfe3c0007fff00

def z832 : W := mkw 0x67befa00077fb181 0xacf7df4000eff630 0xeffffe0003fff987 0x5dffffc0007fff30

def z833 : W := mkw 0x184104ece0804e62 0x0308209d9c1009cc 0x000001e0e0000000 0x0000003c1c000000

def z834 : W := mkw 0x67befb10037fb000 0xacf7df62006ff600 0xfffffff003fff807 0x1ffffffe007fff00

def z835 : W := mkw 0x30e316ece198de00 0x061c62dd9c331bc0 0xfde71fece399fe05 0x9fbce3fd9c733fc0

def z836 : W := mkw 0x6020222027ffffa9 0x8c04044404fffff5 0x0800000003ffffff 0xe1000000007fffff

def z837 : W := mkw 0x904105fff8804e00 0x520820bfff1009c0 0x100001fffc000600 0x8200003fff8000c0

def z838 : W := mkw 0x38e316ece598dfe3 0x071c62dd9cb31bfc 0xfde71fece399ffe5 0xdfbce3fd9c733ffc

def z839 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0xffe71ffce3f9ffe5 0xdffce3ff9c7f3ffc

def z840 : W := mkw 0x184105fee0804f72 0x030820bfdc1009ee 0x100001ece0000660 0x8200003d9c0000cc

def z841 : W := mkw 0x28a31260a198de62 0x0514624c14331bcc 0xfde71fe0e399fe65 0x9fbce3fc1c733fcc

def z842 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0x2de71fe0e399fe65 0x85bce3fc1c733fcc

def z843 : W := mkw 0x27b6920001189000 0x24f6d24000231200 0xede71e000399f805 0x1dbce3c000733f00

def z844 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0xeffffe0f03fff87f 0x3dffffc1e07fff0f

def z845 : W := mkw 0x8605a15096612181 0x10c0b42a12cc2430 0xbe07e1f0ffe1f981 0x57c0fc3e1ffc3f30

def z846 : W := mkw 0x20a232000379b000 0x04144640006f3600 0xede71e0003f9f805 0x1dbce3c0007f3f00

def z847 : W := mkw 0x0e6001b803d00540 0x01cc0037007a00a8 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z848 : W := mkw 0x984105fdfc804feb 0x130820bfbf9009fd 0x100001fffc0007f8 0xe200003fff8000ff

def z849 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0x65fffe00039ff807 0x0cbfffc00073ff00

def z850 : W := mkw 0x38e316eded98deea 0x071c62ddbdb31bdd 0xfde71fecff99fe65 0x9fbce3fd9ff33fcc

def z851 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0xf7fffffffc66019a 0x7effffffff8cc033

def z852 : W := mkw 0x28e312e8a198de40 0x051c625d14331bc8 0xfde71fece399fe65 0x9fbce3fd9c733fcc

def z853 : W := mkw 0x0082100000000000 0x0010420000000000 0xede71e000381f801 0x1dbce3c000703f00

def z854 : W := mkw 0x8005a060b4a16e81 0x1000b40c16942dd0 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z855 : W := mkw 0x471ce9130e672198 0xa8e39d2261cce433 0x0218e0131c66019a 0x60431c02638cc033

def z856 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0xfff8e1fffffe07fe 0xffff1c3fffffc0ff

def z857 : W := mkw 0x975dedfffee16f81 0x72ebbdbfffdc2df0 0x1218e1fffc600780 0xc2431c3fff8c00f0

def z858 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0xbe1fe1f3ffe7ff9b 0xf7c3fc3e7ffcfff3

def z859 : W := mkw 0x67befb12037fb110 0xacf7df62406ff622 0xeffffe0003fff807 0x1dffffc0007fff00

def z860 : W := mkw 0xe7befb12137fb000 0xfcf7df62426ff600 0xeffffe0003fff807 0x1dffffc0007fff00

def z861 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0xffff01ff03ffffff 0xffffe03fe07fffff

def z862 : W := mkw 0x8605a170b6e36f89 0x10c0b42e16dc6df1 0xbe07e1f0ffe7ff9b 0xf7c0fc3e1ffcfff3

def z863 : W := mkw 0x00086e05482b8000 0x00010dc0a9057000 0xfa18fe1ffc7fc7ff 0xff431fc3ff8ff8ff

def z864 : W := mkw 0x27befa00013bb000 0xa4f7df4000277600 0xeffffe000399f805 0x1dffffc000733f00

def z865 : W := mkw 0x67b6b200037db000 0xacf6d640006fb600 0xefe7fe0003f9f805 0x1dfcffc0007f3f00

def z866 : W := mkw 0x11db5ccfc8000000 0x623b6b99f9000000 0xf7fffffffc000000 0x1effffffff800000

def z867 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0xbe07e1ffffe1fff9 0xf7c0fc3ffffc3fff

def z868 : W := mkw 0x184104ede8804e62 0x0308209dbd1009cc 0x100001fffc000660 0x8200003fff8000cc

def z869 : W := mkw 0x28cefbba00abb550 0xa519df77401576aa 0x3007ffff0001fff9 0xe600ffffe0003fff

def z870 : W := mkw 0x8605a150b6616a81 0x10c0b42a16cc2d50 0xbe07e1f0ffe1f801 0x17c0fc3e1ffc3f00

def z871 : W := mkw 0xb7dfdddfd8003000 0xf6fbfbbbfb000600 0xf7fffffffc003800 0x1effffffff800700

def z872 : W := mkw 0x184104ede8804e6a 0x0308209dbd1009cd 0x100001efe0000678 0xa200003dfc0000cf

def z873 : W := mkw 0xa7bedb1319189000 0x74f7db6263231200 0xeffffe131f99f805 0x1dffffc263f33f00

def z874 : W := mkw 0x18e314ece1904e40 0x031c629d9c3209c8 0xfde71fece399fe65 0x9fbce3fd9c733fcc

def z875 : W := mkw 0x086106ece198ce60 0x010c20dd9c3319cc 0xfde71fece399fe65 0x9fbce3fd9c733fcc

def z876 : W := mkw 0x00086c054c230088 0x00010d80a9846011 0xfa18fe1ffc7e07fe 0xff431fc3ff8fc0ff

def z877 : W := mkw 0xc71ce9131e652191 0x78e39d2263cca432 0x0218e0131c66019a 0x60431c02638cc033

def z878 : W := mkw 0x27b2120001189000 0x04f6424000231200 0xefff1e000399f805 0x1dffe3c000733f00

def z879 : W := mkw 0x184105fce0804f62 0x030820bf9c1009ec 0x100001fce00007e0 0xc200003f9c0000fc

def z880 : W := mkw 0x8e05a170b6e16fe3 0x11c0b42e16dc2dfc 0xbe07e1f0ffe1ffe1 0xd7c0fc3e1ffc3ffc

def z881 : W := mkw 0x20a2122001989400 0x0414424400331280 0xfde71fe00399fe05 0x9fbce3fc00733fc0

def z882 : W := mkw 0xd7dfdddfd8040010 0x7afbfbbbfb008002 0xf7fffffffc06001a 0x3effffffff80c003

def z883 : W := mkw 0x00831060a0804e00 0x0010620c141009c0 0xfde71fe0e381fe01 0x9fbce3fc1c703fc0

def z884 : W := mkw 0x27befa00013b9000 0x24f7df4000277200 0xeffffe0003fff807 0x1dffffc0007fff00

def z885 : W := mkw 0x20aefa00013bb000 0xa415df4000277600 0xeffffe0003fff807 0x1dffffc0007fff00

def z886 : W := mkw 0x879fd95398000000 0x70f3fb2a73000000 0xf7fffff3fc000000 0x1efffffe7f800000

def z887 : W := mkw 0x984105fef0804e62 0x530820bfde1009cc 0x100001ece0000660 0x8200003d9c0000cc

def z888 : W := mkw 0xe7befa00177fb081 0xbcf7df4002eff610 0xeffffe001ffff807 0x1dffffc003ffff00

def z889 : W := mkw 0x00084e056808c220 0x000109c0ad011844 0xfa18fe1ffc7fc7ff 0xff431fc3ff8ff8ff

def z890 : W := mkw 0x20086e056c2bf2a8 0x84010dc0ad857e55 0xfa18fe1ffc7fffff 0xff431fc3ff8fffff

def z891 : W := mkw 0x38e316ece598dee2 0x071c62dd9cb31bdc 0xfde71ffcff99ffe5 0xdfbce3ff9ff33ffc

def z892 : W := mkw 0x2820222025b9dee2 0x0504044404b73bdc 0x0800000003f9ffe5 0xc1000000007f3ffc

def z893 : W := mkw 0xfff791fa93d43550 0xfffef23f527a86aa 0x05e701e003803800 0x00bce03c00700700

def z894 : W := mkw 0x60aa7a00037fb000 0x8c154f40006ff600 0xeffffe0003fff807 0x1dffffc0007fff00

def z895 : W := mkw 0x8605a170b4a14e80 0x10c0b42e169429d0 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z896 : W := mkw 0x38e316ece598deea 0x071c62dd9cb31bdd 0xfde71fece399fffd 0xffbce3fd9c733fff

def z897 : W := mkw 0x21ba5a0001189000 0x24374b4000231200 0xedff1e000399f805 0x1dbfe3c000733f00

def z898 : W := mkw 0x0605a060a6e16e80 0x00c0b40c14dc2dd0 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z899 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0xffff1fffe399fe65 0x9fffe3fffc733fcc

def z900 : W := mkw 0xb8e316ecf598dee3 0x171c62dd9eb31bdc 0xfde71fecff99fe65 0x9fbce3fd9ff33fcc

def z901 : W := mkw 0x308ffe45ec2bfaaa 0xa611ffc8bd857f55 0x2007fe00fc01f801 0x0400ffc01f803f00

def z902 : W := mkw 0xb08ffe45fc2bfaab 0x1611ffc8bf857f55 0x2007fe00fc01f801 0x0400ffc01f803f00

def z903 : W := mkw 0x20a2120001189000 0x0414424000231200 0x25e71e000381f801 0x04bce3c000703f00

def z904 : W := mkw 0x00084c056c0042a8 0x00010980ad800855 0xfa18fe1ffc7e07fe 0xff431fc3ff8fc0ff

def z905 : W := mkw 0x184105fee0804e62 0x030820bfdc1009cc 0x100001ffe0000660 0x8200003ffc0000cc

def z906 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0xfffffe10fffff807 0x1fffffc21fffff00

def z907 : W := mkw 0xd7dfdddfda440000 0x7afbfbbbfb488000 0xf7fffffffc660002 0x1effffffff8cc000

def z908 : W := mkw 0x26aefa00037bb000 0x04d5df40006f7600 0xeffffe0003fff807 0x1dffffc0007fff00

def z909 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0xede71fe0e399f805 0x1dbce3fc1c733f00

def z910 : W := mkw 0x61ba7a00037fb000 0xac374f40006ff600 0xedff1e0003fff807 0x1dbfe3c0007fff00

def z911 : W := mkw 0x0040008800000000 0x0008001100000000 0xdff801ff007e07fe 0xfbff003fe00fc0ff

def z912 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0xfde71fece3ffffff 0xffbce3fd9c7fffff

def z913 : W := mkw 0x38e316ecc1989440 0x071c62dd98331288 0xfde71fece399fe65 0x9fbce3fd9c733fcc

def z914 : W := mkw 0x28e216ac6198d660 0x051c42d58c331acc 0xfde71fece399fe65 0x9fbce3fd9c733fcc

def z915 : W := mkw 0x20086e056c2bdaaa 0x04010dc0ad857b55 0xfa18fe1ffc7fffff 0xff431fc3ff8fffff

def z916 : W := mkw 0x79fa5e8f491e9062 0xef3f4bd1e923d20c 0x41f81e0f001e0066 0x083f03c1e003c00c

def z917 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0xfffffffffc180664 0x9fffffffff8300cc

def z918 : W := mkw 0x184105ffec804ffa 0x030820bffd9009ff 0x100001fffc0007f8 0xe200003fff8000ff

def z919 : W := mkw 0xc71ce9131a672110 0xf8e39d22634ce422 0x0218e0131c66019a 0x60431c02638cc033

def z920 : W := mkw 0x38e316efe998de62 0x471c62ddfd331bcc 0xfde71fefe399fe65 0x9fbce3fdfc733fcc

def z921 : W := mkw 0x60a21200035cb000 0x8c144240006b9600 0xede71e000399f805 0x1dbce3c000733f00

def z922 : W := mkw 0x8605a170b4a16e81 0x10c0b42e16942dd0 0xbe07e1f0ff81fe01 0x97c0fc3e1ff03fc0

def z923 : W := mkw 0x91dfdddfd8000000 0x723bfbbbfb000000 0x71fffffffc000000 0x0e3fffffff800000

def z924 : W := mkw 0x984104ecf4804ee3 0x1308209d9e9009dc 0x100001ecfc000660 0x8200003d9f8000cc

def z925 : W := mkw 0x38e316ecc1989c42 0x071c62dd98331388 0xfde71fece399f805 0x1fbce3fd9c733f00

def z926 : W := mkw 0x184104ece0804e62 0x0308209d9c1009cc 0x100001ffe00007f8 0xe200003ffc0000ff

def z927 : W := mkw 0x38ea5e8d49189062 0x671d4bd1a923120c 0x41e01e0c00180064 0x083c03c18003000c

def z928 : W := mkw 0x38ea5e8d49189062 0x071d4bd1a923120c 0x41f81e0f00180064 0x083f03c1e003000c

def z929 : W := mkw 0x67befb130f7fb198 0xacf7df6261eff633 0xeffffe131ffff99f 0x7dffffc263ffff33

def z930 : W := mkw 0xc71ce9131e672181 0xf8e39d2263cce430 0x0218e0131c660182 0x40431c02638cc030

def z931 : W := mkw 0x97594ddfd8000000 0x52eb29bbfb000000 0xf7f8fffffc000000 0x1eff1fffff800000

def z932 : W := mkw 0x61befa00013fb000 0xac37df400027f600 0xedfffe00039ff807 0x1dbfffc00073ff00

def z933 : W := mkw 0x17db5ddfc8000000 0x02fb6bbbf9000000 0xf7fffffffc000000 0x1effffffff800000

def z934 : W := mkw 0x97dfd9da90000000 0x72fbfb3b52000000 0xf7fffff0fc000000 0x1efffffe1f800000

def z935 : W := mkw 0x67bef80003753000 0xacf7df00006ea600 0xeffffe0003e1f801 0x1dffffc0007c3f00

def z936 : W := mkw 0x20aa5a0001189000 0x04154b4000231200 0xeffffe000399f805 0x1dffffc000733f00

def z937 : W := mkw 0xd7dfdddfd8060000 0xfafbfbbbfb00c000 0xf7fffffffc060002 0x1effffffff80c000

def z938 : W := mkw 0xe7befb10137fb000 0xbcf7df62026ff600 0xeffffe101ffff807 0x1dffffc203ffff00

def z939 : W := mkw 0x4f7481ba03d40550 0x09ee9037407a80aa 0xffffe1ff03fe07fe 0xfffffc3fe07fc0ff

def z940 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0xe7ffffe0fc000000 0x1cfffffc1f800000

def z941 : W := mkw 0x4f7001ba03d40550 0x09ee0037407a80aa 0x4df801ef03fe07fe 0xe9bf003de07fc0ff

def z942 : W := mkw 0x97dfdccdd8000000 0x72fbfb99bb000000 0xf7ffffecfc000000 0x1efffffd9f800000

def z943 : W := mkw 0x875dcddfd8000000 0x10ebb9bbfb000000 0xf7fffffffc000000 0x1effffffff800000

def z944 : W := mkw 0x6fbefa00037fb062 0xadf7df40006ff60c 0xeffffe0003fff867 0x1dffffc0007fff0c

def z945 : W := mkw 0x61ba7a00013f9000 0xac374f400027f200 0xeffffe0003fff807 0x1dffffc0007fff00

def z946 : W := mkw 0x8605a170b2e16e00 0x10c0b42e165c2dc0 0xbe07e1f0ffe1fe01 0x97c0fc3e1ffc3fc0

def z947 : W := mkw 0x0f7001ba01900440 0x01ee003740320088 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z948 : W := mkw 0x38e316ede998de62 0x071c62ddbd331bcc 0xfde71fffff99fe65 0x9fbce3fffff33fcc

def z949 : W := mkw 0x4730013003d40500 0x08e60026007a80a0 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z950 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0x2c07e1e0ffe1ff81 0xc580fc3c1ffc3ff0

def z951 : W := mkw 0x38e316ede998de6a 0x071c62ddbd331bcd 0xfde71fefe399fe7d 0xbfbce3fdfc733fcf

def z952 : W := mkw 0x20aa7a010d3b9088 0x04154f4021a77211 0xeffffe131ffff99f 0x7dffffc263ffff33

def z953 : W := mkw 0x20aa5a00011a9000 0xa4154b4000235200 0xede71e000399f805 0x1dbce3c000733f00

def z954 : W := mkw 0xcf7481ba13d40550 0x79ee9037427a80aa 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z955 : W := mkw 0x71fa5e8f491e9028 0xee3f4bd1e923d205 0x41f81e0f001e007e 0x283f03c1e003c00f

def z956 : W := mkw 0xc71ce91012672101 0xb8e39d22024ce420 0x0218e00000660002 0x00431c00000cc000

def z957 : W := mkw 0x97d795ded0000000 0x12faf2bbda000000 0xf7fffffffc000000 0x1effffffff800000

def z958 : W := mkw 0xe7befb12177fb191 0xbcf7df6242eff632 0xeffffe131ffff99f 0x7dffffc263ffff33

def z959 : W := mkw 0x47bef80003752000 0x28f7df00006ea400 0xeffffe0003fff807 0x1dffffc0007fff00

def z960 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0xafe7fe0003e1f801 0x15fcffc0007c3f00

def z961 : W := mkw 0x18496cedeca34eea 0x03092d9dbd9469dd 0x1218e1fffc6607fa 0xe2431c3fff8cc0ff

def z962 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0xf7fffffffc1e007e 0x3effffffff83c00f

def z963 : W := mkw 0x20a2320001399000 0x0414464000273200 0xefe7fe0003f9f805 0x1dfcffc0007f3f00

def z964 : W := mkw 0x486000a803d40550 0x090c0015007a80aa 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z965 : W := mkw 0x871ce9131e632189 0x70e39d2263cc6431 0x0218e0131c66019a 0x60431c02638cc033

def z966 : W := mkw 0x2020222027f9ff81 0x0404044404ff3ff0 0x0800000003f9ff85 0xc1000000007f3ff0

def z967 : W := mkw 0x497001ba01940550 0x092e0037403280aa 0xdbf801ff007e07fe 0xfb7f003fe00fc0ff

def z968 : W := mkw 0x31fa5e8f49189000 0x663f4bd1e9231200 0x41f81e0f00180004 0x083f03c1e0030000

def z969 : W := mkw 0x8e05a170b6e16fd1 0x11c0b42e16dc2dfa 0xbe07e1f0ffe1fff9 0xf7c0fc3e1ffc3fff

def z970 : W := mkw 0x984105fffc804fd1 0x530820bfff9009fa 0x100001fffc0007f8 0xe200003fff8000ff

def z971 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0x65ffffeffc000000 0x0cbffffdff800000

def z972 : W := mkw 0x38e316ece19ade6a 0x071c62dd9c335bcd 0xfde71fece39ffe7f 0xbfbce3fd9c73ffcf

def z973 : W := mkw 0x479ef80002672000 0xa8f3df00004ce400 0xeffffe0003e7f803 0x1dffffc0007cff00

def z974 : W := mkw 0x28e212a801989440 0x051c425500331288 0xede71fe00399f805 0x1dbce3fc00733f00

def z975 : W := mkw 0x6820222027ffffd1 0x8d04044404fffffa 0x0800000003ffffff 0xe1000000007fffff

def z976 : W := mkw 0x20a31664e198de20 0x041462cc9c331bc4 0xfde71fece399fe65 0x9fbce3fd9c733fcc

def z977 : W := mkw 0x97dfdddcd0000000 0x32fbfbbb9a000000 0xf7fffffcfc000000 0x1effffff9f800000

def z978 : W := mkw 0x184104ece0804f72 0x0308209d9c1009ee 0x100001ece00007f8 0xe200003d9c0000ff

def z979 : W := mkw 0x984105fcf0804e62 0x130820bf9e1009cc 0x100001fcfc000660 0x8200003f9f8000cc

def z980 : W := mkw 0xe7befb131f7fb088 0xfcf7df6263eff611 0xeffffe131ffff99f 0x7dffffc263ffff33

def z981 : W := mkw 0x67beda00035cb000 0xacf7db40006b9600 0xeffffe000399f805 0x1dffffc000733f00

def z982 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0xfe1fe1ffffe1ff81 0xdfc3fc3ffffc3ff0

def z983 : W := mkw 0x79fa5e8f491c9072 0x6f3f4bd1e923920e 0x41f81e0f001e007e 0x283f03c1e003c00f

def z984 : W := mkw 0xc715a172b6e56f91 0x18e2b42e56dcadf2 0xfe1fe1ffffffffff 0xffc3fc3fffffffff

def z985 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0xfdff1fefe39ffe7f 0xbfbfe3fdfc73ffcf

def z986 : W := mkw 0x000026046429c2a0 0x000004c08c853854 0xfa18fe1ffc7fc7ff 0xff431fc3ff8ff8ff

def z987 : W := mkw 0x20a6b2000139b000 0x0414d64000273600 0xede7fe000399f805 0x1dbcffc000733f00

def z988 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0xbe07e1f0ffffffff 0xf7c0fc3e1fffffff

def z989 : W := mkw 0x38e312e8a198de62 0x071c625d14331bcc 0xede71fe00399fe65 0x9dbce3fc00733fcc

def z990 : W := mkw 0x8605a170b6e16fa9 0x10c0b42e16dc2df5 0xbe07e1f0ffe1fff9 0xf7c0fc3e1ffc3fff

def z991 : W := mkw 0x9e45a5fcf6e16fe3 0x13c8b4bf9edc2dfc 0x1200e1fcfc6007e0 0xc2401c3f9f8c00fc

def z992 : W := mkw 0x8605a17092e12500 0x10c0b42e125c24a0 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z993 : W := mkw 0x6fbefa00037fb050 0xadf7df40006ff60a 0xeffffe0003fff87f 0x3dffffc0007fff0f

def z994 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0xfffffe1003ffff87 0xdfffffc2007ffff0

def z995 : W := mkw 0x184104eee0804e72 0x0308209ddc1009ce 0x100001efe0000678 0xa200003dfc0000cf

def z996 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0x27fffe0003e7f803 0x04ffffc0007cff00

def z997 : W := mkw 0x06012170a6e14f80 0x00c0242e14dc29f0 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z998 : W := mkw 0x69fa5e8f491e9078 0xad3f4bd1e923d20f 0x41f81e0f001e007e 0x283f03c1e003c00f

def z999 : W := mkw 0x8005a170b6e16f81 0x1000b42e16dc2df0 0x3807e1f0ffe1ff81 0xc700fc3e1ffc3ff0

def z1000 : W := mkw 0x879fdd55d8000000 0x30f3fbaabb000000 0xf7fffffffc000000 0x1effffffff800000

def z1001 : W := mkw 0x8687915090000000 0x10d0f22a12000000 0xf7e7fff0fc000000 0x1efcfffe1f800000

def z1002 : W := mkw 0x97dfdddfda402000 0x72fbfbbbfb480400 0xf7ffffffff803800 0x1efffffffff00700

def z1003 : W := mkw 0x984105fffc804eea 0x530820bfff9009dd 0x100001fffc0007f8 0xe200003fff8000ff

def z1004 : W := mkw 0x00084e05480a8028 0x000109c0a9015005 0xfa18fe1ffc7e07fe 0xff431fc3ff8fc0ff

def z1005 : W := mkw 0x6f7001ba03d41d52 0x0dee0037407a83aa 0xdff801ff03fe3ffe 0xfbff003fe07fc7ff

def z1006 : W := mkw 0x38e312e881989c42 0x071c625d10331388 0xfde71fec0399fe65 0x9fbce3fd80733fcc

def z1007 : W := mkw 0x0750239a242bc2a8 0x00ea047344857855 0xdff801ff007fc7ff 0xfbff003fe00ff8ff

def z1008 : W := mkw 0xc71ce91212672000 0xf8e39d22424ce400 0x0218e00000660002 0x00431c00000cc000

def z1009 : W := mkw 0x28e212a82198de62 0x051c425504331bcc 0xfde71fec0399fe65 0x9fbce3fd80733fcc

def z1010 : W := mkw 0x67befa010b7fb000 0xacf7df40216ff600 0xeffffe131ffff807 0x1dffffc263ffff00

def z1011 : W := mkw 0x66a6b200037fb000 0x8cd4d640006ff600 0xefe7fe0003fff807 0x1dfcffc0007fff00

def z1012 : W := mkw 0x8605815090000000 0x10c0b02a12000000 0xbe07e1f0ff81f801 0x17c0fc3e1ff03f00

def z1013 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0xeffffe0003ffffff 0xfdffffc0007fffff

def z1014 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0x35e71fece381fe61 0x86bce3fd9c703fcc

def z1015 : W := mkw 0xe7befa011b7fb000 0xfcf7df40236ff600 0xeffffe001ffff807 0x1dffffc003ffff00

def z1016 : W := mkw 0x8715a172b6e16f81 0x70e2b42e56dc2df0 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z1017 : W := mkw 0x90cfdccdd8000000 0x7219fb99bb000000 0x25e7ffe0fc000000 0x04bcfffc1f800000

def z1018 : W := mkw 0x67befa030b7fb000 0xecf7df40616ff600 0xeffffe0303fff807 0x1dffffc0607fff00

def z1019 : W := mkw 0x86058170b4804f81 0x10c0b02e169009f0 0xbe07e1f0ff81ff81 0xd7c0fc3e1ff03ff0

def z1020 : W := mkw 0x67b6b200037fb000 0xacf6d640006ff600 0xede71e0003fff807 0x1dbce3c0007fff00

def z1021 : W := mkw 0x67beda00035eb000 0xacf7db40006bd600 0xedff1e00039ff807 0x1dbfe3c00073ff00

def z1022 : W := mkw 0x26aefa00037bb000 0xa4d5df40006f7600 0xefe7fe0003f9f805 0x1dfcffc0007f3f00

def z1023 : W := mkw 0x00086a00242bc280 0x00010d4004857850 0xfa18fe1ffc7fc7ff 0xff431fc3ff8ff8ff

def z1024 : W := mkw 0x184104ece0804e62 0x0308209d9c1009cc 0xda1801ffe07e07fe 0xfb43003ffc0fc0ff

def z1025 : W := mkw 0x473cea00037fa000 0x08e79d40006ff400 0xeffffe0003fff807 0x1dffffc0007fff00

def z1026 : W := mkw 0xb8e316edf998de62 0x571c62ddbf331bcc 0xfde71fecff99fe65 0x9fbce3fd9ff33fcc

def z1027 : W := mkw 0xeff791fa93d43d51 0xbdfef23f527a87aa 0x05e701e003803800 0x00bce03c00700700

def z1028 : W := mkw 0x78e316ece19cde72 0x0f1c62dd9c339bce 0xfde71fece39ffe7f 0xbfbce3fd9c73ffcf

def z1029 : W := mkw 0x61b21200011c9000 0x0c36424000239200 0xedff1e00039ff807 0x1dbfe3c00073ff00

def z1030 : W := mkw 0x20a23200013bb000 0x8414464000277600 0xede71e000399f805 0x1dbce3c000733f00

def z1031 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0x3407e1f0ff81ff81 0xc680fc3e1ff03ff0

def z1032 : W := mkw 0x30e316cce118d220 0x061c62d99c231a44 0xfde71fece399fe65 0x9fbce3fd9c733fcc

def z1033 : W := mkw 0x00484c8d48000000 0x00090991a9000000 0xf7f8fffffc000000 0x1eff1fffff800000

def z1034 : W := mkw 0x30c316ece088de22 0x061862dd9c111bc4 0xfde71fece381fe01 0x9fbce3fd9c703fc0

def z1035 : W := mkw 0x97dfdddfd8020008 0x72fbfbbbfb004001 0xf7fffffffc06001a 0x3effffffff80c003

def z1036 : W := mkw 0x497000aa03d40550 0x092e0015407a80aa 0xddf801ef03fe07fe 0xfbbf003de07fc0ff

def z1037 : W := mkw 0x0686b00002612000 0x00d0d600004c2400 0xefe7fe0003e1f801 0x1dfcffc0007c3f00

def z1038 : W := mkw 0x20a3124081189000 0x0414624810231200 0xfde71fe0e399f805 0x1fbce3fc1c733f00

def z1039 : W := mkw 0xcf7481ba13d42551 0x19ee9037427a84aa 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z1040 : W := mkw 0x871ce9131a612000 0x70e39d22634c2400 0x0218e0131c600000 0x00431c02638c0000

def z1041 : W := mkw 0xb7dfdddfd8001802 0x76fbfbbbfb000300 0xf7fffffffc003800 0x1effffffff800700

def z1042 : W := mkw 0x39fa5e8f491a906a 0x673f4bd1e923520d 0x41f81e0f001e007e 0x283f03c1e003c00f

def z1043 : W := mkw 0x96c795dfd8000000 0x52d8f2bbfb000000 0xf7e7fffffc000000 0x1efcffffff800000

def z1044 : W := mkw 0x984104edf8804e62 0x5308209dbf1009cc 0x100001ecfc000660 0x8200003d9f8000cc

def z1045 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0xeffffe1303fff99f 0x7dffffc2607fff33

def z1046 : W := mkw 0x2820222025bbdeea 0x0504044404b77bdd 0x080000000399fe65 0x8100000000733fcc

def z1047 : W := mkw 0xfff791fa93d43d53 0x1ffef23f527a87aa 0x05e701e003803800 0x00bce03c00700700

def z1048 : W := mkw 0x00012060a6e16f81 0x0000240c14dc2df0 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z1049 : W := mkw 0xb08ffe45fc2bf2a8 0xf611ffc8bf857e55 0x2007fe00fc01f801 0x0400ffc01f803f00

def z1050 : W := mkw 0x6f7001ba03d43550 0x8dee0037407a86aa 0xdff801ff03fe3ffe 0xfbff003fe07fc7ff

def z1051 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0xf5e7ffecfc000000 0x1ebcfffd9f800000

def z1052 : W := mkw 0x497001ba03d40550 0x092e0037407a80aa 0x59f801ff03fe07fe 0xeb3f003fe07fc0ff

def z1053 : W := mkw 0x96cfddddd8000000 0x72d9fbbbbb000000 0xf7e7fffcfc000000 0x1efcffff9f800000

def z1054 : W := mkw 0xd7dfdddfda440110 0x7afbfbbbfb488022 0xf7fffffffc000000 0x1effffffff800000

def z1055 : W := mkw 0xc71ce9111e672189 0xb8e39d2223cce431 0x0218e0131c66019a 0x60431c02638cc033

def z1056 : W := mkw 0x6820222027ffffe3 0x8d04044404fffffc 0x0800000003ffffe7 0xc1000000007ffffc

def z1057 : W := mkw 0x4820222027ffeff9 0x0904044404fffdff 0x0800000003ffffff 0xe1000000007fffff

def z1058 : W := mkw 0xfff791fa93d41d52 0x7ffef23f527a83aa 0x05e701e003803800 0x00bce03c00700700

def z1059 : W := mkw 0x07dedd9f48000000 0x20fbdbb3e9000000 0xf7fffffffc000000 0x1effffffff800000

def z1060 : W := mkw 0x184104edec804eea 0x0308209dbd9009dd 0x100001ecfc000660 0x8200003d9f8000cc

def z1061 : W := mkw 0x38e316eee198de72 0x071c62dddc331bce 0xfde71fefe399fe7d 0xbfbce3fdfc733fcf

def z1062 : W := mkw 0xd7dfdddfda440110 0x7afbfbbbfb488022 0xfffffffffc7e07fe 0xffffffffff8fc0ff

def z1063 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0xfffffffffc7e0006 0x1fffffffff8fc000

def z1064 : W := mkw 0xc71ce9131e672199 0x18e39d2263cce433 0x0218e0131c66019a 0x60431c02638cc033

def z1065 : W := mkw 0x079efa00026ba000 0x20f3df40004d7400 0xeffffe0003fff807 0x1dffffc0007fff00

def z1066 : W := mkw 0x00012060a4a14e80 0x0000240c149429d0 0xbc07e1e0ff81fe01 0x9780fc3c1ff03fc0

def z1067 : W := mkw 0x38e216ac41989462 0x071c42d58833128c 0xfde71fec0399fe65 0x9fbce3fd80733fcc

def z1068 : W := mkw 0x184104ece0804e62 0x0308209d9c1009cc 0xd80001ece0180664 0x9b00003d9c0300cc

def z1069 : W := mkw 0x61b21200011c9000 0xac36424000239200 0xede71e000399f805 0x1dbce3c000733f00

def z1070 : W := mkw 0xe7befb131b7fb110 0xfcf7df62636ff622 0xeffffe131ffff99f 0x7dffffc263ffff33

def z1071 : W := mkw 0x18c314ece0804e62 0x0318629d9c1009cc 0xfde71fece381fe61 0x9fbce3fd9c703fcc

def z1072 : W := mkw 0x27befa000379b000 0x24f7df40006f3600 0xeffffe0003f9f805 0x1dffffc0007f3f00

def z1073 : W := mkw 0x6820222027fffeea 0x8d04044404ffffdd 0x0800000003ffffff 0xe1000000007fffff

def z1074 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0xfffffe0c03fffe67 0x9fffffc1807fffcc

def z1075 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0x2de7fe0003fff807 0x05bcffc0007fff00

def z1076 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0x4de71fec0399fe65 0x89bce3fd80733fcc

def z1077 : W := mkw 0xcf7481ba13d40550 0x19ee9037427a80aa 0xdff8e1ff1ffe07fe 0xfbff1c3fe3ffc0ff

def z1078 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0x27fffff3fc000000 0x04fffffe7f800000

def z1079 : W := mkw 0xc715a170b6e56f81 0xb8e2b42e16dcadf0 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z1080 : W := mkw 0x2820222027fbffeb 0x0504044404ff7ffd 0x0800000003ffffff 0xe1000000007fffff

def z1081 : W := mkw 0x20aa7a00013b9000 0x04154f4000277200 0xede7fe000399f805 0x1dbcffc000733f00

def z1082 : W := mkw 0x984105fef4804ff3 0x130820bfde9009fe 0x100001fffc0007f8 0xe200003fff8000ff

def z1083 : W := mkw 0x79fa5e8f491e907a 0x0f3f4bd1e923d20f 0x41f81e0f001e007e 0x283f03c1e003c00f

def z1084 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0xfe1fe1f0ffffff87 0xdfc3fc3e1ffffff0

def z1085 : W := mkw 0x17da5d9f48000000 0x62fb4bb3e9000000 0xf7f8fffffc000000 0x1eff1fffff800000

def z1086 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0x2607e1f0ffe1f981 0x44c0fc3e1ffc3f30

def z1087 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0xbc07e1e0ff81fe01 0x9780fc3c1ff03fc0

def z1088 : W := mkw 0xc605a170b6e56f91 0x18c0b42e16dcadf2 0xbe07e1f0ffe7ff9b 0xf7c0fc3e1ffcfff3

def z1089 : W := mkw 0x78e316ece19ede62 0x8f1c62dd9c33dbcc 0xfde71fece39ffe67 0x9fbce3fd9c73ffcc

def z1090 : W := mkw 0xc715a172b6e56f91 0x18e2b42e56dcadf2 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z1091 : W := mkw 0x90cb5ddfd8000000 0x52196bbbfb000000 0xf7fffffffc000000 0x1effffffff800000

def z1092 : W := mkw 0x97d795ded0000000 0x72faf2bbda000000 0xf7e7fffcfc000000 0x1efcffff9f800000

def z1093 : W := mkw 0x8605a172b6e16f91 0x10c0b42e56dc2df2 0xbe07e1f3ffe1ff99 0xf7c0fc3e7ffc3ff3

def z1094 : W := mkw 0x079ed80000000000 0x20f3db0000000000 0xeffffe000381f801 0x1dffffc000703f00

def z1095 : W := mkw 0x8605a17092e12d01 0x10c0b42e125c25a0 0xbe07e1f0ffe1f801 0x17c0fc3e1ffc3f00

def z1096 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0xfe07e1fcfff9ffe5 0xdfc0fc3f9fff3ffc

def z1097 : W := mkw 0x00010060a0804e00 0x0000200c141009c0 0xbe07e1f0ff81fe01 0x97c0fc3e1ff03fc0

def z1098 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0xede7fe000399f805 0x1dbcffc000733f00

def z1099 : W := mkw 0x97dfdddfd8000000 0x72fbfbbbfb000000 0xf7fffffffc0007f8 0xfeffffffff8000ff

def z1100 : W := mkw 0x67befa00037fb028 0xacf7df40006ff605 0xeffffe0003fff87f 0x3dffffc0007fff0f

def z1101 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0xfde71fffe399fffd 0xffbce3fffc733fff

def z1102 : W := mkw 0x984105fff8804f72 0x530820bfff1009ee 0x100001fffc0007f8 0xe200003fff8000ff

def z1103 : W := mkw 0x97dfdddfd8000110 0x72fbfbbbfb000022 0xf7fffffffc000198 0x7effffffff800033

def z1104 : W := mkw 0xe7befb10137fb101 0xbcf7df62026ff620 0xeffffe0003fff807 0x1dffffc0007fff00

def z1105 : W := mkw 0x67befa00077fb080 0xacf7df4000eff610 0xeffffe101ffff987 0x5dffffc203ffff30

def z1106 : W := mkw 0x108b7e45ec2bc2a8 0x02116fc8bd857855 0x2007fe00fc01c001 0x0400ffc01f803800

def z1107 : W := mkw 0x97dfdddfda400000 0x72fbfbbbfb480000 0xffffffffffe00000 0x1ffffffffffc0000

def z1108 : W := mkw 0x38e312e8a198de42 0x071c625d14331bc8 0xfde71fe0e399fe05 0x9fbce3fc1c733fc0

def z1109 : W := mkw 0x075001ba02c00500 0x00ea0037405800a0 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z1110 : W := mkw 0x97dfdddfd8002801 0x72fbfbbbfb000500 0xf7fffffffc003800 0x1effffffff800700

def z1111 : W := mkw 0xc71ce9131e672088 0xf8e39d2263cce411 0x0218e0131c66019a 0x60431c02638cc033

def z1112 : W := mkw 0x38e316ece198de62 0x071c62dd9c331bcc 0xffff1fece3fffe67 0x9fffe3fd9c7fffcc

def z1113 : W := mkw 0x60aefa00037fb000 0xac15df40006ff600 0xede7fe0003fff807 0x1dbcffc0007fff00

def z1114 : W := mkw 0x20a3126081989c00 0x0414624c10331380 0xede71fe00399f805 0x1dbce3fc00733f00

def z1115 : W := mkw 0x80012170b4a14f81 0x1000242e169429f0 0xbe07e1f0ffe1ff81 0xd7c0fc3e1ffc3ff0

def z1116 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0xfffffe1f03fff807 0x1fffffc3e07fff00

def z1117 : W := mkw 0x67befa00037fb000 0xacf7df40006ff600 0xe7fffe000381f801 0x1cffffc000703f00

def z1118 : W := mkw 0x386106ece198de62 0x070c20dd9c331bcc 0x100001ece0180664 0x8200003d9c0300cc

def z1119 : W := mkw 0x6820222027fdfff3 0x0d04044404ffbffe 0x0800000003ffffff 0xe1000000007fffff

def z1120 : W := mkw 0x67befb10037fb100 0xacf7df62006ff620 0xeffffe1003fff987 0x5dffffc2007fff30

def z1121 : W := mkw 0x9f5dcdfff8804e62 0x73ebb9bfff1009cc 0x1218e1fffc000660 0x82431c3fff8000cc

def z1122 : W := mkw 0x4f7481ba03d42550 0x09ee9037407a84aa 0xdfff01ff03fe3ffe 0xfbffe03fe07fc7ff

def z1123 : W := mkw 0x4f7481ba03d42550 0xa9ee9037407a84aa 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z1124 : W := mkw 0x38e314ece1905e42 0x071c629d9c320bc8 0xfde71fece381fe01 0x9fbce3fd9c703fc0

def z1125 : W := mkw 0x79fa5e8d491e906a 0xaf3f4bd1a923d20d 0x41f81e0f001e007e 0x283f03c1e003c00f

def z1126 : W := mkw 0x67befa010b7fb008 0xacf7df40216ff601 0xeffffe0303fff81f 0x3dffffc0607fff03

def z1127 : W := mkw 0x91db5ddfd8000000 0x723b6bbbfb000000 0xf3f8fffffc000000 0x1e7f1fffff800000

def z1128 : W := mkw 0x38e316ccc1189062 0x071c62d99823120c 0xfde71fece399f865 0x1fbce3fd9c733f0c

def z1129 : W := mkw 0x871ce91016612181 0x30e39d2202cc2430 0x0218e0101c600180 0x40431c02038c0030

def z1130 : W := mkw 0x67b69200035cb000 0xacf6d240006b9600 0x25e71e000381f801 0x04bce3c000703f00

def z1131 : W := mkw 0x8715a172b6e16f81 0x10e2b42e56dc2df0 0xbe1fe1f3ffe1ff81 0xd7c3fc3e7ffc3ff0

def z1132 : W := mkw 0x10cb5ccdc8000000 0x02196b99b9000000 0xf5e7ffecfc000000 0x1ebcfffd9f800000

def z1133 : W := mkw 0x8005a060b6e16f81 0x1000b40c16dc2df0 0xbc07e1e0ffe1ff81 0xd780fc3c1ffc3ff0

def z1134 : W := mkw 0x00086e056c2beaa9 0x00010dc0ad857d55 0xfa18fe1ffc7fffff 0xff431fc3ff8fffff

def z1135 : W := mkw 0x8605a170b6e16f81 0x10c0b42e16dc2df0 0xb607e1f0ff81f801 0x16c0fc3e1ff03f00

def z1136 : W := mkw 0x8005a170b4a16f81 0x1000b42e16942df0 0xbc07e1f0ff81ff81 0xd780fc3e1ff03ff0

def z1137 : W := mkw 0x20aa5a00011a9000 0x04154b4000235200 0xedff1e00039ff807 0x1dbfe3c00073ff00

def z1138 : W := mkw 0xc715a170b6e56f81 0x18e2b42e16dcadf0 0xbe1fe1f0ffe7ff83 0xd7c3fc3e1ffcfff0

def z1139 : W := mkw 0x97dfdddfda400100 0x72fbfbbbfb480020 0xf7fffffffc600180 0x5effffffff8c0030

def z1140 : W := mkw 0x9fdfdddfd8000050 0x73fbfbbbfb00000a 0xf7fffffffc000078 0x3effffffff80000f

def z1141 : W := mkw 0xdff791fa93d42d51 0x7bfef23f527a85aa 0x05e701e003803800 0x00bce03c00700700

def z1142 : W := mkw 0x6820222027fff7f8 0x8d04044404fffeff 0x0800000003ffffff 0xe1000000007fffff

def z1143 : W := mkw 0x471ce91202672000 0xa8e39d22404ce400 0x0218e01300660002 0x00431c02600cc000

def z1144 : W := mkw 0x497000aa01940450 0x092e00154032808a 0xdff801ff03fe07fe 0xfbff003fe07fc0ff

def z1145 : W := mkw 0x984105fcf0804f63 0x130820bf9e1009ec 0x100001ece0000660 0x8200003d9c0000cc

def z1146 : W := mkw 0x4f70019a01140050 0x09ee00334022800a 0xdff801ff007e07fe 0xfbff003fe00fc0ff

def z1147 : W := mkw 0x26a2120003589000 0x04d44240006b1200 0xefe71e0003f9f805 0x1dfce3c0007f3f00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z8,z5,z6]),(0,[z0,z3,z4,z7,z5,z9,z6])],[(0,[z10,z0,z2,z3,z4,z5,z6]),(0,[z0,z11,z3,z4,z7,z5,z6]),(0,[z0,z12,z2,z3,z4,z5,z6]),(0,[z0,z13,z3,z4,z7,z5,z14]),(0,[z0,z15,z16,z3,z4,z5,z6])],[(1,[z0,z17,z3,z4,z7,z5]),(0,[z0,z18,z3,z19,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z20,z6]),(0,[z0,z2,z4,z7,z5,z21,z6]),(0,[z0,z22,z3,z4,z7,z6,z23]),(0,[z0,z3,z4,z24,z5,z25,z6])],[(0,[z0,z26,z27,z4,z7,z5,z6]),(0,[z0,z2,z3,z4,z28,z5,z6]),(0,[z0,z29,z3,z7,z5,z6,z30]),(0,[z0,z3,z4,z7,z5,z6,z31])],[(1,[z0,z3,z4,z7,z5,z32]),(0,[z33,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z34,z7,z5,z6]),(1,[z0,z3,z4,z24,z5,z25])],[(0,[z35,z0,z3,z4,z7,z5,z6]),(1,[z0,z18,z27,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z36])],[(0,[z0,z37,z38,z4,z7,z5,z6]),(0,[z0,z3,z39,z4,z7,z5,z6]),(0,[z40,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z41,z7,z5,z6]),(0,[z0,z3,z4,z42,z7,z5,z6])],[(0,[z0,z3,z4,z7,z5,z43,z44]),(0,[z0,z45,z18,z3,z4,z5,z6]),(0,[z0,z18,z3,z4,z46,z5,z6]),(0,[z0,z47,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z24,z7,z5,z6])]],
   [[(0,[z48,z0,z3,z4,z7,z49,z6]),(0,[z0,z3,z4,z7,z5,z6,z50]),(0,[z51,z0,z27,z4,z7,z5,z6]),(0,[z52,z0,z3,z4,z7,z5,z6]),(0,[z0,z15,z3,z4,z5,z6,z36])],[(0,[z53,z0,z54,z4,z7,z5,z6]),(0,[z0,z55,z3,z4,z7,z5,z6]),(0,[z0,z56,z3,z4,z7,z5,z6]),(0,[z0,z57,z3,z4,z7,z5,z6]),(1,[z0,z3,z4,z58,z59,z6])],[(1,[z0,z60,z3,z7,z5,z6]),(0,[z61,z0,z18,z3,z4,z5,z6]),(0,[z0,z3,z62,z4,z7,z5,z6])],[(0,[z63,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z49,z6,z23]),(0,[z64,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z65,z4,z7,z5,z6]),(0,[z66,z0,z3,z4,z7,z5,z6])],[(0,[z0,z67,z3,z4,z7,z5,z6])],[(0,[z0,z3,z4,z68,z7,z5,z6]),(0,[z69,z0,z3,z4,z7,z5,z6]),(1,[z0,z2,z4,z70,z5,z6]),(1,[z0,z3,z4,z5,z6,z71]),(1,[z0,z72,z3,z4,z5,z6]),(0,[z73,z0,z74,z3,z4,z7,z6])],[(0,[z75,z0,z76,z4,z7,z5,z6]),(0,[z0,z18,z3,z4,z77,z5,z6]),(0,[z0,z2,z3,z4,z78,z5,z6]),(1,[z0,z2,z3,z4,z5,z6]),(0,[z0,z16,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z79,z7,z5,z6])],[(0,[z0,z3,z4,z7,z5,z6,z80]),(0,[z0,z3,z4,z7,z5,z81,z6]),(0,[z0,z3,z4,z7,z82,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z83])]],
   [[(0,[z0,z84,z3,z4,z7,z5,z6]),(0,[z0,z76,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z28,z85,z6]),(0,[z86,z0,z3,z4,z7,z5,z87]),(0,[z0,z3,z4,z7,z5,z44,z30]),(0,[z0,z88,z3,z4,z7,z5,z6])],[(0,[z89,z0,z3,z4,z7,z5,z6]),(0,[z90,z0,z3,z4,z7,z5,z6]),(0,[z0,z18,z3,z4,z5,z6,z23]),(0,[z0,z3,z4,z7,z91,z5,z6]),(0,[z0,z3,z4,z7,z92,z5,z6]),(1,[z0,z3,z4,z5,z93,z6])],[(1,[z0,z3,z94,z4,z7,z5]),(0,[z95,z0,z3,z4,z7,z49,z6]),(0,[z0,z18,z3,z96,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z97]),(0,[z51,z0,z74,z3,z4,z7,z6]),(1,[z0,z3,z98,z7,z28,z6]),(0,[z0,z3,z4,z7,z5,z6,z99])],[(0,[z100,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z101,z5,z6]),(1,[z0,z18,z2,z4,z5,z6]),(0,[z0,z3,z4,z102,z70,z5,z6])],[(0,[z0,z103,z4,z7,z5,z6,z104])],[(0,[z105,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z106,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z107,z6,z83])],[(0,[z108,z0,z3,z4,z7,z5,z6]),(0,[z109,z0,z3,z4,z7,z5,z6]),(0,[z0,z110,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z111,z6]),(0,[z0,z112,z3,z4,z7,z5,z6]),(0,[z0,z26,z2,z3,z4,z5,z6]),(0,[z73,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z113,z5,z6]),(0,[z0,z114,z3,z4,z7,z5,z6]),(1,[z0,z3,z4,z7,z107,z83])],[(0,[z0,z3,z4,z7,z115,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z116])]],
   [[(0,[z117,z0,z2,z3,z4,z5,z6]),(0,[z0,z18,z3,z4,z118,z5,z6]),(0,[z0,z3,z4,z7,z5,z119,z120]),(0,[z0,z3,z4,z7,z5,z6,z121]),(0,[z0,z3,z4,z122,z7,z5,z6])],[(0,[z10,z0,z18,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z123,z5,z6]),(0,[z0,z3,z4,z7,z124,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z125])],[(0,[z0,z3,z4,z7,z126,z5,z6]),(0,[z127,z0,z26,z3,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z128,z6]),(0,[z0,z18,z129,z3,z4,z5,z6]),(0,[z130,z0,z3,z4,z7,z5,z6])],[(0,[z0,z3,z131,z4,z7,z5,z6]),(0,[z132,z0,z3,z4,z7,z5,z6]),(0,[z0,z133,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z134,z5,z6]),(0,[z0,z135,z3,z4,z7,z5,z6])],[(0,[z0,z37,z136,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z137,z5,z6]),(0,[z0,z2,z3,z4,z138,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z139]),(0,[z0,z3,z4,z7,z140,z6,z104])],[(0,[z0,z3,z4,z7,z141,z5,z6]),(0,[z0,z142,z3,z4,z7,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z36])],[(0,[z0,z26,z3,z96,z7,z5,z6]),(1,[z0,z143,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z144,z6])],[(0,[z0,z3,z4,z145,z7,z5,z6]),(0,[z0,z3,z4,z7,z146,z5,z6])]],
   [[(1,[z0,z3,z4,z7,z147,z6]),(0,[z0,z3,z148,z4,z7,z5,z6]),(0,[z0,z3,z4,z149,z7,z5,z6]),(0,[z0,z18,z3,z4,z85,z5,z6]),(1,[z0,z3,z4,z5,z6,z150]),(0,[z0,z3,z4,z7,z151,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z152]),(0,[z0,z3,z4,z7,z107,z5,z83])],[(0,[z75,z0,z29,z3,z7,z5,z6]),(0,[z0,z153,z3,z4,z7,z5,z6]),(0,[z154,z0,z18,z3,z4,z5,z6])],[(0,[z0,z155,z3,z4,z7,z5,z6]),(0,[z0,z3,z7,z5,z128,z6,z44]),(0,[z0,z156,z3,z4,z7,z5,z6]),(0,[z0,z18,z3,z157,z4,z5,z6]),(0,[z0,z3,z4,z158,z7,z5,z6])],[(0,[z0,z15,z3,z4,z58,z5,z6]),(0,[z0,z15,z3,z4,z7,z107,z6])],[(0,[z75,z0,z3,z4,z7,z159,z6]),(0,[z0,z160,z3,z4,z7,z5,z6]),(0,[z0,z161,z3,z4,z7,z5,z6]),(0,[z162,z0,z3,z4,z7,z5,z6])],[(0,[z0,z163,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z164,z5,z6]),(0,[z0,z3,z165,z4,z7,z5,z6]),(0,[z0,z18,z3,z4,z5,z21,z6]),(0,[z0,z3,z4,z7,z5,z166,z6]),(0,[z0,z22,z3,z4,z7,z28,z6])],[(0,[z0,z3,z4,z7,z77,z5,z6]),(0,[z0,z3,z4,z167,z7,z5,z6]),(0,[z168,z0,z3,z4,z7,z5,z87]),(1,[z0,z18,z3,z4,z5,z6]),(0,[z0,z16,z18,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z169,z6]),(0,[z0,z3,z4,z7,z5,z6,z170])],[(0,[z0,z3,z96,z4,z7,z6,z171]),(0,[z0,z2,z3,z4,z5,z6,z83]),(0,[z172,z0,z3,z4,z7,z5,z6])]],
   [[(0,[z173,z0,z3,z4,z7,z5,z6]),(0,[z127,z0,z3,z174,z7,z5,z6]),(0,[z0,z175,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z176,z7,z5,z6]),(0,[z0,z3,z177,z4,z7,z5,z6]),(0,[z73,z0,z3,z4,z7,z5,z83])],[(0,[z178,z0,z3,z4,z7,z5,z6]),(0,[z0,z179,z3,z4,z7,z5,z6]),(0,[z0,z13,z2,z4,z7,z5,z6]),(0,[z180,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z181,z5,z6])],[(0,[z182,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z7,z5,z6]),(1,[z48,z3,z4,z7,z85,z6]),(1,[z0,z3,z4,z7,z5,z183]),(0,[z0,z129,z3,z4,z7,z70,z6]),(0,[z0,z3,z4,z7,z5,z6,z14]),(0,[z0,z3,z4,z7,z5,z6,z184]),(0,[z185,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z186,z5,z6])],[(0,[z51,z0,z3,z4,z7,z6,z120]),(0,[z0,z187,z3,z4,z7,z5,z6])],[(0,[z188,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z189,z5,z6])],[(1,[z0,z190,z3,z4,z7,z5]),(0,[z0,z191,z3,z7,z5,z6,z44]),(0,[z0,z3,z192,z4,z7,z5,z6]),(0,[z0,z15,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z58,z7,z107,z6]),(0,[z0,z16,z3,z4,z5,z6,z104]),(0,[z0,z3,z4,z7,z5,z193,z6])],[(0,[z0,z3,z194,z4,z7,z5,z6]),(0,[z86,z0,z3,z4,z7,z5,z6]),(0,[z0,z26,z18,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z195,z6]),(0,[z73,z0,z18,z3,z4,z5,z6]),(0,[z0,z196,z4,z7,z197,z5,z6]),(0,[z0,z74,z3,z4,z7,z107,z5]),(0,[z0,z3,z198,z4,z7,z5,z6])],[(0,[z0,z199,z3,z4,z7,z5,z6]),(0,[z0,z2,z3,z4,z200,z5,z6]),(0,[z0,z201,z3,z4,z7,z5,z6]),(0,[z0,z13,z4,z7,z70,z5,z6]),(1,[z0,z29,z3,z7,z5,z30])]],
   [[(0,[z0,z2,z202,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z120]),(0,[z0,z203,z3,z4,z7,z5,z6])],[(0,[z0,z3,z4,z7,z5,z6,z204]),(0,[z205,z0,z3,z4,z7,z5,z6])],[(0,[z0,z3,z206,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z207,z5,z6]),(0,[z0,z208,z3,z4,z7,z5,z6]),(0,[z0,z37,z3,z96,z7,z5,z6]),(0,[z0,z18,z27,z4,z7,z5,z6]),(0,[z0,z3,z209,z4,z7,z5,z6])],[(0,[z0,z3,z4,z7,z5,z6,z210]),(0,[z0,z3,z4,z7,z5,z6,z211]),(0,[z0,z212,z3,z4,z7,z5,z6]),(0,[z0,z74,z3,z4,z58,z7,z6]),(0,[z0,z3,z4,z7,z213,z5,z6]),(0,[z0,z3,z4,z214,z7,z5,z6])],[],[(0,[z0,z3,z4,z7,z5,z215,z6]),(0,[z0,z3,z4,z216,z7,z5,z6]),(0,[z86,z3,z4,z7,z5,z6,z44]),(0,[z0,z3,z4,z7,z5,z217,z6]),(0,[z0,z3,z4,z7,z5,z218,z6]),(0,[z61,z0,z2,z3,z4,z5,z6]),(0,[z219,z0,z3,z4,z7,z5,z6])],[(0,[z0,z18,z3,z4,z5,z43,z6]),(0,[z0,z45,z3,z4,z7,z5,z6]),(0,[z220,z0,z3,z4,z7,z5,z6]),(0,[z0,z221,z3,z4,z7,z5,z6]),(0,[z222,z0,z3,z4,z7,z5,z6])],[(0,[z0,z3,z4,z77,z197,z5,z6])]],
   [[(0,[z0,z3,z223,z38,z4,z7,z6]),(0,[z0,z3,z4,z224,z7,z5,z6]),(0,[z0,z3,z4,z7,z225,z5,z6]),(0,[z0,z2,z3,z4,z58,z5,z6]),(0,[z0,z129,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z226])],[(0,[z48,z3,z4,z7,z85,z5,z6]),(0,[z0,z227,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z228,z6])],[(0,[z0,z3,z229,z4,z7,z5,z6]),(1,[z0,z3,z230,z197,z5,z6]),(0,[z0,z231,z3,z4,z7,z5,z6])],[(0,[z127,z0,z3,z19,z7,z5,z6]),(0,[z0,z18,z3,z4,z197,z5,z6]),(0,[z0,z232,z3,z4,z7,z107,z5])],[(0,[z0,z191,z3,z4,z7,z5,z6]),(0,[z0,z3,z7,z5,z43,z6,z30])],[(0,[z0,z3,z4,z7,z233,z5,z6]),(0,[z168,z0,z232,z3,z4,z7,z5]),(0,[z0,z18,z3,z4,z107,z5,z6]),(0,[z0,z234,z3,z4,z7,z5,z6])],[],[(0,[z235,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z28,z49,z6]),(0,[z0,z3,z4,z24,z7,z5,z104])]],
   [[(0,[z0,z3,z4,z7,z5,z87,z6]),(0,[z0,z236,z3,z4,z7,z5,z6]),(0,[z0,z237,z3,z4,z7,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z30]),(0,[z0,z3,z4,z7,z5,z6,z238]),(0,[z0,z239,z3,z4,z7,z5,z6]),(0,[z240,z0,z3,z4,z7,z5,z6]),(1,[z0,z3,z4,z7,z140,z6]),(0,[z0,z3,z4,z7,z5,z241,z6])],[(1,[z0,z3,z4,z242,z5,z6]),(0,[z0,z243,z3,z4,z7,z5,z6]),(0,[z0,z244,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z245,z6])],[(0,[z0,z3,z246,z4,z7,z5,z6]),(0,[z48,z0,z18,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z7,z5,z6])],[(0,[z127,z0,z2,z3,z4,z5,z6]),(0,[z247,z0,z3,z4,z7,z5,z6]),(0,[z0,z248,z3,z4,z7,z5,z6]),(0,[z0,z249,z3,z4,z7,z5,z6]),(0,[z0,z3,z250,z4,z7,z5,z6]),(0,[z0,z3,z251,z4,z7,z5,z6]),(0,[z252,z0,z3,z4,z7,z5,z6])],[(0,[z168,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z253,z6])],[(0,[z0,z136,z3,z4,z7,z5,z6]),(0,[z3,z19,z4,z7,z5,z87,z6]),(0,[z0,z3,z4,z7,z5,z6,z254]),(1,[z0,z26,z7,z82,z5,z6]),(0,[z0,z18,z2,z3,z4,z5,z6]),(0,[z51,z0,z129,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z255,z6]),(0,[z0,z13,z3,z4,z7,z5,z21]),(0,[z0,z3,z4,z7,z59,z5,z6])],[(0,[z0,z47,z3,z4,z77,z5,z6]),(0,[z0,z3,z4,z7,z5,z183,z6]),(0,[z0,z3,z256,z4,z7,z5,z6]),(0,[z257,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z258,z5,z6])],[(0,[z0,z1,z3,z4,z7,z5,z6]),(0,[z0,z259,z18,z3,z4,z5,z6]),(0,[z0,z260,z18,z3,z4,z5,z6])]],
   [[(0,[z10,z0,z3,z4,z7,z5,z6]),(0,[z75,z127,z3,z4,z7,z5,z6]),(0,[z86,z0,z13,z3,z4,z7,z5]),(0,[z0,z12,z3,z4,z7,z5,z6]),(0,[z0,z18,z3,z4,z5,z6,z261])],[(0,[z262,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z263]),(0,[z264,z0,z3,z4,z7,z5,z6])],[(0,[z0,z3,z4,z7,z5,z6,z265]),(0,[z0,z3,z4,z7,z266,z5,z6]),(0,[z0,z3,z267,z4,z7,z5,z6]),(0,[z0,z3,z4,z78,z197,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z268]),(0,[z0,z3,z269,z4,z7,z5,z6]),(0,[z0,z270,z3,z4,z7,z5,z6]),(0,[z271,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z272,z4,z7,z5,z6]),(0,[z0,z273,z3,z4,z7,z5,z6])],[(0,[z168,z3,z4,z7,z5,z87,z6]),(0,[z0,z274,z3,z4,z7,z5,z6]),(0,[z0,z3,z157,z4,z7,z5,z30]),(0,[z0,z3,z4,z7,z5,z275,z6]),(0,[z0,z3,z4,z7,z5,z6,z276])],[(0,[z0,z3,z4,z7,z277,z5,z6]),(0,[z0,z278,z3,z4,z7,z5,z6]),(0,[z95,z0,z18,z3,z4,z5,z6]),(0,[z0,z129,z4,z7,z70,z5,z6]),(0,[z0,z3,z4,z279,z7,z5,z6])],[(0,[z0,z60,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z280,z5,z6]),(0,[z0,z3,z4,z281,z7,z5,z6]),(0,[z282,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z70,z5,z6,z71])],[(1,[z0,z2,z38,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z283,z6])],[(0,[z0,z3,z4,z7,z5,z5,z6]),(0,[z0,z3,z4,z7,z5,z284,z6]),(0,[z0,z285,z3,z4,z7,z5,z6])]],
   [[(0,[z154,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z19,z4,z7,z5,z6])],[(0,[z0,z286,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z287]),(0,[z0,z3,z4,z7,z288,z5,z6])],[(0,[z289,z0,z3,z4,z7,z5,z6]),(0,[z127,z0,z3,z7,z5,z43,z6]),(0,[z235,z0,z3,z4,z78,z5,z6]),(0,[z0,z3,z4,z5,z6,z150,z120]),(0,[z0,z248,z47,z3,z4,z5,z6]),(0,[z0,z3,z4,z58,z59,z5,z6])],[(0,[z0,z3,z290,z4,z7,z5,z6]),(0,[z0,z3,z96,z4,z7,z5,z6]),(0,[z0,z291,z18,z3,z4,z5,z6]),(1,[z73,z0,z74,z3,z4,z7])],[(1,[z95,z3,z4,z7,z49,z6]),(0,[z0,z3,z292,z4,z7,z5,z6]),(0,[z0,z232,z3,z4,z7,z5,z30]),(0,[z0,z293,z3,z4,z7,z5,z6]),(0,[z3,z4,z7,z5,z6,z31,z30])],[(1,[z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z38,z4,z7,z5,z6]),(0,[z0,z129,z3,z4,z7,z6,z23]),(0,[z0,z16,z3,z4,z7,z5,z6])],[(0,[z0,z294,z3,z4,z7,z5,z6]),(0,[z0,z2,z4,z7,z70,z5,z6]),(1,[z51,z0,z4,z7,z6,z120]),(0,[z0,z232,z3,z4,z7,z5,z14])],[(0,[z0,z295,z3,z38,z7,z5,z6]),(0,[z235,z0,z18,z3,z4,z5,z6]),(0,[z296,z0,z3,z4,z7,z5,z6]),(0,[z297,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z298,z4,z7,z5,z6])]],
   [[(0,[z299,z0,z3,z4,z7,z5,z6]),(0,[z300,z0,z3,z4,z7,z5,z6]),(0,[z75,z0,z37,z3,z7,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z44]),(0,[z0,z2,z3,z4,z5,z87,z6]),(0,[z0,z3,z4,z7,z301,z5,z6]),(0,[z0,z196,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z302]),(0,[z0,z3,z98,z4,z7,z6,z23]),(0,[z0,z103,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z303])],[(0,[z75,z3,z4,z174,z7,z5,z6]),(0,[z0,z304,z3,z4,z7,z5,z6]),(0,[z0,z3,z305,z4,z7,z5,z6]),(0,[z0,z18,z3,z27,z4,z5,z6]),(0,[z0,z306,z3,z4,z7,z5,z6])],[(0,[z0,z3,z4,z307,z7,z5,z6]),(0,[z73,z0,z16,z3,z4,z7,z5]),(0,[z0,z3,z4,z7,z5,z308,z6])],[(1,[z0,z309,z3,z4,z5,z6]),(0,[z127,z0,z18,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z310]),(0,[z0,z3,z311,z4,z7,z5,z6]),(0,[z0,z2,z3,z312,z4,z5,z6]),(1,[z313,z3,z4,z7,z5,z6]),(0,[z0,z285,z4,z7,z5,z6,z83])],[(1,[z0,z3,z4,z7,z5,z314]),(0,[z0,z3,z4,z7,z5,z315,z6]),(0,[z0,z3,z4,z7,z316,z5,z6]),(0,[z317,z0,z3,z4,z7,z5,z6]),(0,[z73,z0,z74,z3,z4,z7,z5])],[(0,[z0,z3,z4,z7,z318,z5,z6]),(0,[z0,z26,z3,z4,z7,z5,z6]),(1,[z0,z37,z96,z7,z5,z6]),(0,[z0,z18,z18,z3,z4,z5,z6]),(0,[z0,z319,z3,z4,z7,z5,z6]),(0,[z320,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z98,z7,z28,z5,z6]),(0,[z73,z0,z3,z4,z7,z5,z6])],[(0,[z168,z0,z13,z3,z4,z7,z5]),(0,[z51,z0,z2,z3,z4,z5,z6]),(0,[z0,z321,z3,z4,z7,z5,z6]),(0,[z0,z13,z3,z4,z7,z5,z6]),(0,[z0,z4,z7,z5,z6,z322,z36])],[(0,[z0,z323,z3,z4,z7,z5,z6]),(0,[z0,z74,z2,z3,z4,z5,z6]),(0,[z117,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z324])]],
   [[(0,[z0,z3,z4,z7,z325,z5,z6]),(0,[z0,z3,z4,z7,z5,z326,z6]),(0,[z327,z0,z3,z4,z7,z5,z6]),(0,[z0,z328,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z213,z6,z104])],[(1,[z0,z2,z136,z4,z5,z6]),(0,[z329,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z330]),(0,[z331,z0,z3,z4,z7,z5,z6])],[(0,[z53,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z46,z5,z6]),(0,[z0,z22,z3,z98,z7,z5,z6]),(0,[z0,z3,z4,z7,z332,z5,z6]),(1,[z3,z4,z7,z5,z6,z31]),(0,[z0,z3,z4,z7,z5,z6,z333]),(0,[z0,z3,z4,z24,z7,z5,z25])],[(0,[z0,z3,z4,z334,z7,z5,z6]),(0,[z0,z3,z4,z7,z335,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z50])],[(0,[z0,z2,z3,z4,z174,z5,z6]),(0,[z0,z18,z3,z4,z5,z6,z104]),(0,[z0,z3,z4,z7,z5,z6,z336]),(0,[z0,z3,z4,z7,z5,z337,z6]),(0,[z0,z3,z338,z4,z7,z5,z6]),(0,[z0,z339,z3,z4,z7,z5,z6])],[(0,[z0,z3,z4,z7,z5,z340,z6]),(0,[z0,z3,z4,z7,z341,z5,z6]),(0,[z51,z0,z4,z7,z5,z21,z6])],[(1,[z127,z3,z19,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z171]),(0,[z0,z3,z27,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z342,z5,z6]),(0,[z0,z3,z7,z28,z5,z6,z23]),(0,[z0,z74,z3,z4,z7,z6,z83])],[(0,[z343,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z174,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z344,z6]),(0,[z0,z3,z4,z7,z5,z345,z6]),(0,[z0,z346,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z58,z7,z6,z36])]],
   [[(0,[z0,z3,z4,z7,z5,z347,z6]),(0,[z0,z3,z312,z4,z7,z5,z6]),(1,[z0,z4,z7,z5,z6,z322])],[(0,[z0,z3,z4,z102,z7,z5,z6])],[(0,[z86,z0,z232,z3,z4,z7,z5]),(0,[z0,z2,z3,z4,z82,z5,z6]),(0,[z0,z348,z3,z4,z7,z5,z6]),(0,[z0,z349,z3,z4,z7,z5,z6]),(0,[z0,z350,z3,z4,z7,z5,z6])],[(1,[z53,z3,z4,z78,z5,z6]),(0,[z0,z26,z2,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z351,z5,z6]),(0,[z0,z352,z3,z4,z7,z5,z6])],[(0,[z0,z353,z3,z4,z7,z5,z6]),(1,[z0,z3,z4,z7,z6,z171]),(0,[z0,z3,z4,z7,z5,z6,z354]),(0,[z355,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z23]),(0,[z0,z29,z3,z4,z7,z5,z43]),(0,[z0,z3,z4,z356,z7,z5,z6]),(0,[z0,z357,z3,z4,z7,z5,z6]),(0,[z0,z3,z358,z4,z7,z5,z6])],[(0,[z75,z0,z3,z7,z5,z43,z6]),(0,[z48,z0,z2,z3,z4,z5,z6])],[(1,[z0,z359,z3,z4,z5,z6]),(1,[z0,z3,z4,z334,z5,z6]),(0,[z95,z48,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z360,z6]),(0,[z361,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z362])],[(0,[z0,z363,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z364,z36])]],
   [[(0,[z0,z2,z3,z38,z4,z5,z6]),(0,[z0,z3,z4,z365,z7,z5,z6])],[(0,[z0,z37,z3,z4,z7,z5,z6]),(0,[z0,z3,z366,z4,z7,z5,z6]),(0,[z0,z129,z3,z4,z7,z107,z6]),(0,[z367,z0,z3,z4,z7,z5,z6]),(0,[z0,z368,z3,z4,z7,z5,z6]),(0,[z369,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z370,z5,z6])],[(0,[z51,z48,z0,z3,z4,z7,z6]),(0,[z0,z3,z157,z7,z5,z43,z6]),(0,[z0,z371,z3,z4,z7,z5,z6]),(1,[z0,z285,z4,z7,z5,z6])],[(0,[z0,z323,z3,z38,z4,z7,z5]),(0,[z0,z3,z4,z7,z372,z5,z6]),(0,[z0,z3,z373,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z43,z87]),(0,[z0,z3,z4,z7,z118,z5,z6]),(0,[z0,z232,z4,z7,z5,z21,z6]),(0,[z0,z3,z4,z374,z7,z5,z6])],[(0,[z10,z0,z3,z4,z101,z5,z6])],[(0,[z0,z3,z4,z375,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z32,z6]),(0,[z53,z0,z3,z4,z78,z5,z6]),(0,[z376,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z377,z4,z7,z5,z6])],[(0,[z75,z0,z18,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z378,z5,z6]),(0,[z0,z259,z3,z4,z7,z5,z6]),(1,[z0,z13,z2,z4,z5,z6]),(0,[z51,z0,z18,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z379,z5,z6])],[(0,[z95,z0,z2,z3,z4,z5,z6]),(0,[z380,z0,z3,z4,z7,z5,z6]),(0,[z0,z2,z37,z3,z4,z5,z6]),(0,[z0,z74,z18,z3,z4,z5,z6]),(0,[z73,z0,z13,z3,z4,z7,z5]),(1,[z0,z3,z4,z374,z5,z6])]],
   [[(1,[z0,z295,z3,z7,z5,z6]),(0,[z75,z0,z26,z3,z7,z5,z6]),(0,[z0,z3,z381,z4,z7,z5,z6]),(0,[z0,z129,z3,z4,z7,z28,z6]),(0,[z0,z382,z3,z4,z7,z5,z6])],[(0,[z0,z18,z3,z4,z70,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z383]),(0,[z0,z4,z7,z70,z5,z21,z6]),(0,[z0,z248,z3,z230,z7,z5,z6])],[(1,[z0,z384,z4,z7,z5,z6]),(0,[z53,z0,z18,z3,z4,z5,z6]),(0,[z0,z18,z3,z3,z4,z5,z6]),(0,[z0,z18,z3,z4,z5,z6,z120]),(0,[z0,z3,z4,z5,z21,z6,z116])],[(0,[z385,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z85,z5,z6]),(0,[z95,z51,z0,z3,z4,z7,z6]),(0,[z0,z18,z3,z366,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z386]),(0,[z0,z3,z98,z4,z7,z28,z6]),(0,[z0,z387,z3,z4,z7,z5,z6]),(1,[z0,z15,z3,z4,z6,z36])],[(0,[z61,z0,z3,z4,z7,z5,z6]),(0,[z182,z0,z38,z4,z7,z5,z6]),(0,[z0,z38,z4,z7,z82,z5,z6]),(0,[z0,z3,z4,z7,z5,z388,z6]),(0,[z0,z3,z4,z7,z389,z5,z6]),(0,[z0,z390,z3,z4,z7,z5,z6]),(0,[z0,z3,z230,z4,z197,z5,z6])],[(1,[z182,z38,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z391,z5,z6]),(0,[z168,z0,z3,z157,z4,z7,z5]),(0,[z392,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z393]),(0,[z0,z3,z4,z7,z394,z5,z6])],[(0,[z0,z3,z4,z395,z7,z5,z6]),(0,[z0,z18,z3,z4,z5,z396,z6]),(0,[z0,z3,z98,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z397])],[(0,[z0,z3,z4,z7,z5,z398,z6]),(0,[z0,z3,z4,z7,z5,z6,z399])]],
   [[(1,[z0,z201,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z400,z5,z6]),(0,[z0,z3,z4,z7,z5,z21,z6]),(0,[z0,z3,z4,z7,z5,z6,z401])],[(1,[z0,z3,z4,z101,z5,z6]),(0,[z0,z2,z3,z4,z77,z5,z6]),(0,[z402,z0,z3,z4,z7,z5,z6]),(0,[z403,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z404,z7,z5,z6]),(1,[z0,z13,z4,z7,z5,z14]),(0,[z405,z0,z3,z4,z7,z5,z6])],[(0,[z0,z291,z3,z4,z7,z5,z6]),(0,[z406,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z407,z4,z7,z5,z6]),(0,[z408,z0,z3,z4,z7,z5,z6])],[(0,[z0,z236,z3,z96,z4,z5,z6]),(0,[z0,z409,z3,z4,z7,z5,z6]),(0,[z410,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z411,z5,z6])],[(0,[z412,z0,z3,z4,z7,z5,z6]),(0,[z0,z2,z3,z98,z4,z5,z6])],[(1,[z10,z136,z4,z7,z5,z6]),(0,[z0,z2,z3,z96,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z14]),(0,[z0,z3,z413,z4,z7,z5,z6]),(0,[z0,z13,z4,z7,z5,z6,z14]),(1,[z0,z3,z4,z5,z6,z116]),(0,[z0,z3,z4,z7,z5,z6,z414])],[(0,[z0,z415,z3,z4,z7,z5,z6]),(0,[z75,z0,z3,z174,z7,z5,z6]),(0,[z235,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z416,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z417])],[(0,[z0,z359,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z6]),(0,[z0,z3,z4,z7,z5,z6,z418]),(0,[z0,z3,z96,z4,z7,z419,z6]),(0,[z0,z18,z3,z230,z4,z5,z6]),(0,[z0,z18,z3,z4,z5,z25,z6]),(0,[z0,z3,z4,z7,z5,z119,z6]),(0,[z0,z3,z4,z7,z5,z420,z6]),(0,[z0,z421,z3,z4,z7,z5,z6])]],
   [[(0,[z86,z3,z19,z4,z7,z5,z6]),(0,[z0,z422,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z423]),(0,[z0,z3,z4,z7,z424,z5,z6]),(0,[z0,z22,z3,z7,z5,z6,z23]),(0,[z0,z29,z3,z4,z7,z5,z30])],[(0,[z182,z3,z38,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z425]),(0,[z0,z2,z3,z4,z5,z195,z6]),(0,[z0,z3,z4,z7,z5,z426,z6])],[(0,[z127,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z427,z4,z7,z5,z6]),(1,[z0,z428,z4,z7,z5,z6]),(0,[z0,z429,z2,z3,z4,z5,z6]),(0,[z0,z18,z3,z4,z5,z6,z30])],[(0,[z0,z3,z4,z7,z5,z430,z6]),(0,[z0,z3,z4,z7,z431,z5,z6]),(0,[z0,z18,z3,z4,z5,z49,z6]),(0,[z0,z432,z3,z4,z7,z5,z6]),(0,[z433,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z434,z6])],[(0,[z0,z3,z4,z7,z5,z435,z6]),(0,[z0,z3,z4,z7,z436,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z437]),(0,[z3,z4,z7,z5,z87,z6,z44]),(0,[z0,z18,z3,z4,z41,z5,z6]),(0,[z0,z3,z4,z7,z438,z5,z6])],[(0,[z0,z3,z4,z7,z5,z6,z439]),(0,[z0,z3,z4,z440,z7,z5,z6]),(0,[z0,z441,z3,z4,z7,z5,z6]),(0,[z0,z16,z3,z4,z7,z5,z104])],[(0,[z0,z3,z4,z7,z5,z6,z314]),(0,[z0,z3,z442,z4,z7,z5,z6]),(0,[z0,z443,z3,z4,z7,z5,z6]),(0,[z0,z444,z3,z4,z7,z5,z6])],[(0,[z0,z3,z445,z4,z7,z5,z6]),(0,[z0,z446,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z447]),(0,[z0,z3,z4,z24,z7,z107,z5])]],
   [[(0,[z0,z38,z27,z4,z7,z5,z6]),(0,[z0,z18,z3,z4,z28,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z448])],[(0,[z53,z3,z4,z78,z7,z5,z6]),(0,[z0,z449,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z450,z6]),(0,[z0,z3,z4,z7,z5,z43,z6]),(0,[z0,z451,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z452,z5,z6])],[(0,[z182,z0,z136,z4,z7,z5,z6]),(0,[z0,z453,z3,z4,z7,z5,z6]),(0,[z0,z2,z96,z4,z7,z5,z6]),(0,[z0,z454,z3,z4,z7,z5,z6]),(0,[z0,z455,z3,z4,z7,z5,z6]),(0,[z0,z455,z3,z4,z5,z6,z14]),(0,[z0,z3,z4,z7,z5,z6,z456])],[(1,[z0,z323,z3,z4,z7,z5]),(1,[z0,z3,z4,z457,z5,z6])],[(0,[z0,z136,z4,z7,z82,z5,z6]),(0,[z0,z96,z4,z7,z82,z5,z6]),(1,[z0,z3,z4,z7,z213,z6])],[(0,[z0,z458,z3,z4,z7,z5,z6]),(0,[z0,z4,z7,z5,z21,z6,z14]),(0,[z0,z3,z4,z7,z459,z5,z6])],[(0,[z0,z2,z3,z4,z24,z5,z6]),(0,[z0,z3,z4,z7,z5,z396,z6]),(0,[z0,z3,z4,z7,z197,z5,z6]),(0,[z73,z0,z3,z4,z7,z107,z6])],[(0,[z10,z136,z3,z4,z7,z5,z6]),(0,[z75,z0,z3,z4,z7,z5,z32]),(0,[z0,z3,z4,z7,z5,z6,z460]),(0,[z0,z3,z461,z4,z7,z5,z6]),(0,[z0,z3,z4,z462,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z463]),(1,[z0,z26,z2,z4,z5,z6]),(0,[z51,z0,z3,z4,z7,z70,z6]),(0,[z0,z3,z464,z4,z7,z5,z6]),(1,[z0,z3,z465,z4,z7,z6]),(0,[z0,z3,z4,z7,z466,z5,z6]),(0,[z73,z0,z3,z4,z24,z7,z5]),(0,[z0,z3,z4,z5,z93,z6,z83])]],
   [[(0,[z0,z2,z136,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z467,z5,z6]),(0,[z0,z3,z4,z7,z85,z6,z23]),(0,[z0,z468,z3,z4,z7,z5,z6]),(0,[z0,z2,z232,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z184]),(0,[z0,z469,z3,z4,z7,z5,z6]),(0,[z0,z143,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z107,z5,z6])],[(0,[z0,z3,z4,z7,z5,z6,z470]),(0,[z75,z0,z3,z19,z7,z5,z6]),(0,[z75,z86,z3,z4,z7,z5,z6]),(0,[z73,z0,z232,z3,z4,z7,z5]),(0,[z471,z0,z3,z4,z7,z5,z6])],[(1,[z0,z3,z223,z4,z7,z6]),(0,[z0,z18,z2,z4,z7,z5,z6]),(0,[z472,z0,z3,z4,z7,z5,z6]),(0,[z0,z232,z3,z4,z7,z5,z21]),(0,[z0,z3,z230,z7,z197,z5,z6]),(0,[z0,z15,z74,z3,z4,z7,z6]),(0,[z0,z143,z4,z7,z5,z6,z36]),(0,[z0,z3,z4,z7,z5,z6,z473]),(0,[z0,z3,z4,z474,z7,z5,z6])],[(0,[z0,z3,z4,z78,z7,z5,z6]),(0,[z0,z3,z475,z4,z7,z5,z6]),(0,[z0,z18,z3,z4,z78,z5,z6]),(0,[z0,z3,z4,z7,z5,z476,z6]),(0,[z0,z3,z4,z7,z5,z477,z6])],[(0,[z10,z0,z3,z4,z375,z5,z6]),(0,[z0,z478,z3,z4,z7,z5,z6]),(0,[z0,z479,z3,z4,z7,z5,z6])],[(0,[z480,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z481,z6]),(0,[z0,z3,z482,z4,z7,z5,z6])],[(0,[z0,z3,z4,z7,z5,z87,z30]),(0,[z0,z22,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z483])],[(0,[z0,z3,z4,z7,z484,z5,z6]),(0,[z0,z309,z3,z38,z4,z5,z6]),(0,[z0,z3,z4,z7,z485,z5,z6]),(0,[z0,z3,z4,z486,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z487]),(0,[z0,z3,z4,z7,z5,z6,z71]),(1,[z0,z62,z4,z7,z5,z6])]],
   [[(0,[z0,z29,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z59,z5,z6]),(0,[z0,z13,z3,z4,z7,z5,z43]),(0,[z0,z15,z3,z4,z7,z6,z36])],[(0,[z75,z0,z2,z3,z4,z5,z6]),(0,[z0,z488,z3,z4,z7,z5,z6]),(0,[z0,z489,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z490,z6]),(0,[z0,z3,z491,z4,z7,z5,z6]),(0,[z0,z3,z492,z4,z7,z5,z6])],[(0,[z0,z493,z3,z4,z7,z5,z6]),(0,[z0,z18,z3,z4,z5,z6,z44]),(0,[z0,z494,z3,z4,z7,z5,z6])],[(0,[z0,z3,z495,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z496,z6]),(0,[z0,z26,z3,z7,z82,z5,z6]),(0,[z0,z15,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z261]),(0,[z0,z13,z3,z4,z7,z107,z5]),(0,[z0,z3,z4,z7,z5,z93,z6])],[(0,[z497,z0,z3,z4,z7,z5,z6]),(0,[z86,z0,z3,z4,z7,z5,z44]),(1,[z0,z454,z3,z4,z7,z5]),(0,[z0,z498,z3,z4,z7,z5,z6]),(1,[z0,z16,z3,z4,z5,z104]),(0,[z0,z3,z4,z499,z7,z5,z6])],[(1,[z235,z3,z4,z77,z5,z6]),(0,[z500,z0,z2,z3,z4,z5,z6]),(0,[z51,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z501,z5,z6]),(1,[z0,z455,z3,z4,z5,z6]),(0,[z0,z502,z3,z4,z7,z5,z6])],[(0,[z0,z503,z3,z4,z7,z5,z6]),(1,[z0,z3,z7,z5,z128,z6]),(1,[z0,z2,z96,z4,z5,z6]),(0,[z0,z504,z3,z4,z7,z5,z6]),(0,[z0,z74,z3,z4,z7,z5,z6])],[(0,[z0,z3,z4,z505,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z506]),(0,[z0,z18,z348,z3,z4,z5,z6]),(1,[z0,z248,z47,z3,z5,z6])]],
   [[(0,[z0,z3,z4,z7,z5,z6,z507]),(0,[z0,z96,z27,z4,z7,z5,z6]),(0,[z0,z15,z3,z4,z7,z59,z6])],[(1,[z0,z3,z4,z375,z5,z6]),(0,[z0,z3,z4,z7,z5,z508,z6]),(0,[z53,z0,z3,z4,z7,z5,z6]),(0,[z0,z2,z3,z4,z5,z43,z6]),(0,[z0,z3,z465,z4,z7,z6,z14]),(0,[z0,z3,z4,z7,z5,z6,z509]),(0,[z0,z3,z510,z4,z7,z5,z6]),(0,[z0,z16,z3,z4,z24,z5,z6]),(0,[z0,z4,z7,z5,z245,z6,z83])],[(0,[z0,z511,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z512,z5,z6]),(0,[z513,z0,z3,z4,z7,z5,z6]),(0,[z86,z0,z3,z157,z4,z7,z5]),(0,[z514,z0,z3,z4,z7,z5,z6]),(0,[z0,z18,z3,z4,z5,z6,z36]),(0,[z0,z515,z3,z4,z7,z5,z6]),(0,[z0,z3,z157,z4,z7,z5,z6]),(0,[z0,z3,z516,z4,z7,z5,z6])],[(0,[z3,z4,z7,z85,z5,z49,z6]),(0,[z0,z517,z3,z4,z7,z5,z6]),(1,[z51,z0,z2,z4,z5,z6]),(0,[z0,z518,z3,z4,z7,z5,z6]),(0,[z0,z519,z3,z4,z7,z5,z6]),(1,[z0,z3,z157,z7,z5,z43])],[(0,[z0,z26,z4,z7,z82,z5,z6]),(0,[z0,z3,z4,z457,z7,z5,z6]),(1,[z0,z2,z4,z118,z5,z6]),(0,[z0,z3,z4,z7,z140,z5,z6])],[(0,[z0,z520,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z521,z5,z6]),(0,[z0,z3,z4,z522,z7,z5,z6]),(0,[z0,z3,z523,z4,z7,z5,z6])],[(0,[z0,z18,z3,z4,z174,z5,z6]),(0,[z95,z3,z4,z7,z5,z49,z6]),(0,[z0,z524,z3,z4,z7,z5,z6])],[(0,[z182,z10,z3,z4,z7,z5,z6]),(0,[z3,z19,z4,z174,z7,z5,z6]),(0,[z525,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z526,z4,z7,z5,z6])]],
   [[(0,[z0,z3,z4,z7,z527,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z528]),(0,[z0,z3,z529,z4,z7,z5,z6]),(0,[z0,z2,z3,z4,z107,z5,z6]),(0,[z530,z0,z18,z3,z4,z5,z6]),(0,[z0,z3,z531,z4,z7,z5,z6]),(0,[z0,z16,z3,z4,z7,z5,z25])],[(0,[z0,z3,z96,z4,z424,z5,z6]),(0,[z0,z3,z96,z4,z7,z5,z532]),(1,[z0,z3,z4,z7,z5,z119]),(0,[z0,z3,z4,z7,z533,z5,z6])],[(0,[z0,z3,z4,z7,z5,z6,z150]),(0,[z0,z3,z4,z7,z5,z6,z534]),(0,[z0,z3,z4,z58,z7,z59,z6]),(0,[z0,z3,z4,z59,z5,z25,z6])],[(0,[z75,z0,z3,z4,z7,z147,z6]),(0,[z3,z4,z78,z7,z77,z5,z6]),(1,[z0,z3,z4,z7,z5,z532]),(0,[z51,z0,z2,z4,z7,z5,z6]),(0,[z0,z232,z3,z4,z7,z5,z6]),(0,[z535,z0,z3,z4,z7,z5,z6]),(0,[z0,z16,z3,z4,z59,z5,z6])],[(0,[z0,z309,z3,z4,z7,z5,z6]),(0,[z0,z536,z3,z4,z7,z5,z6]),(0,[z48,z0,z3,z4,z7,z5,z6]),(0,[z0,z18,z3,z4,z82,z5,z6]),(0,[z0,z18,z3,z4,z5,z6,z83]),(0,[z0,z3,z4,z7,z537,z5,z6]),(0,[z538,z0,z3,z4,z7,z5,z6])],[(0,[z0,z359,z3,z38,z4,z5,z6]),(1,[z0,z54,z4,z7,z5,z6]),(0,[z0,z3,z4,z539,z7,z5,z6]),(0,[z0,z3,z4,z5,z6,z184,z14])],[(0,[z0,z3,z223,z4,z7,z5,z6]),(0,[z0,z54,z3,z4,z7,z5,z6]),(0,[z0,z22,z18,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z540]),(0,[z0,z3,z4,z7,z541,z5,z6])],[(0,[z0,z3,z4,z7,z542,z5,z6]),(0,[z0,z37,z3,z7,z82,z5,z6]),(0,[z0,z18,z3,z4,z5,z6,z97]),(0,[z0,z3,z4,z7,z5,z6,z543])]],
   [[(0,[z182,z0,z18,z3,z4,z5,z6]),(1,[z300,z0,z3,z4,z7,z6]),(0,[z0,z2,z3,z19,z4,z5,z6]),(0,[z0,z3,z4,z7,z544,z5,z6]),(0,[z0,z545,z3,z4,z7,z5,z6]),(0,[z0,z29,z18,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z546,z5,z6]),(0,[z0,z3,z4,z7,z5,z547,z6])],[(1,[z0,z2,z4,z5,z21,z6]),(0,[z0,z202,z3,z4,z7,z5,z6]),(0,[z0,z260,z3,z4,z7,z5,z6])],[(0,[z0,z18,z3,z38,z4,z5,z6]),(0,[z0,z3,z548,z4,z7,z5,z6]),(0,[z53,z235,z3,z4,z7,z5,z6]),(0,[z168,z0,z3,z4,z7,z5,z44]),(0,[z51,z0,z4,z7,z5,z6,z120]),(0,[z0,z3,z549,z4,z7,z5,z6])],[(0,[z136,z3,z38,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z550,z6]),(0,[z0,z3,z4,z7,z5,z551,z6]),(0,[z0,z15,z18,z3,z4,z5,z6]),(0,[z0,z3,z552,z4,z7,z5,z6]),(1,[z0,z196,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z553,z5,z6])],[(0,[z0,z13,z3,z4,z7,z5,z30])],[(0,[z0,z3,z4,z7,z5,z6,z554])],[(0,[z555,z0,z3,z4,z7,z5,z6]),(1,[z0,z76,z4,z7,z5,z6]),(0,[z75,z0,z3,z4,z334,z5,z6]),(0,[z556,z0,z3,z4,z7,z5,z6]),(0,[z0,z557,z3,z4,z7,z5,z6]),(0,[z95,z0,z3,z4,z7,z5,z6]),(0,[z0,z129,z3,z4,z7,z6,z120]),(0,[z0,z3,z4,z558,z7,z5,z6]),(0,[z0,z559,z3,z4,z7,z5,z6])],[(0,[z560,z0,z3,z4,z7,z5,z6]),(0,[z0,z561,z3,z4,z7,z5,z6]),(1,[z86,z3,z4,z7,z5,z44]),(0,[z0,z562,z3,z4,z7,z5,z6]),(0,[z0,z47,z3,z230,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z104])]],
   [[(0,[z0,z3,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z563,z5,z6]),(0,[z0,z47,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z7,z5,z364])],[(0,[z0,z3,z4,z7,z564,z5,z6]),(0,[z0,z37,z96,z4,z7,z5,z6]),(0,[z0,z18,z37,z3,z4,z5,z6]),(0,[z0,z274,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z138,z5,z6]),(0,[z0,z13,z27,z4,z7,z5,z6]),(0,[z0,z565,z3,z4,z7,z5,z6])],[(0,[z0,z3,z566,z4,z7,z5,z6]),(0,[z0,z57,z2,z3,z4,z5,z6]),(0,[z51,z0,z3,z4,z7,z6,z23]),(0,[z0,z567,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z568,z5,z6])],[(0,[z0,z3,z569,z4,z7,z5,z6]),(0,[z127,z0,z29,z3,z7,z5,z6]),(0,[z219,z0,z18,z3,z4,z5,z6]),(0,[z570,z0,z3,z4,z7,z5,z6])],[(0,[z0,z3,z4,z571,z7,z5,z6])],[(0,[z235,z0,z3,z4,z77,z5,z6]),(0,[z0,z3,z4,z572,z7,z5,z6]),(1,[z0,z236,z3,z4,z5,z6]),(0,[z0,z18,z3,z4,z58,z5,z6]),(0,[z0,z573,z3,z4,z7,z5,z6]),(0,[z0,z574,z3,z4,z7,z5,z6]),(0,[z0,z72,z3,z4,z5,z6,z83])],[(0,[z0,z3,z4,z7,z5,z6,z575]),(0,[z0,z13,z232,z4,z7,z5,z6]),(0,[z0,z576,z3,z4,z7,z5,z6])],[(0,[z0,z3,z4,z7,z577,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z578]),(0,[z0,z3,z579,z4,z7,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z23]),(0,[z0,z580,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z581,z5,z6])]],
   [[(0,[z0,z582,z3,z4,z7,z5,z6]),(0,[z0,z3,z583,z4,z7,z5,z6]),(0,[z0,z3,z4,z584,z7,z5,z6]),(0,[z585,z0,z3,z4,z7,z5,z6])],[(0,[z0,z3,z4,z4,z7,z5,z6]),(0,[z0,z88,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z374,z5,z21,z6]),(0,[z0,z586,z3,z4,z7,z5,z6])],[(0,[z75,z0,z384,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z587]),(1,[z0,z517,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z588,z5,z6]),(0,[z589,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z590,z4,z7,z5,z6])],[(0,[z0,z74,z129,z3,z4,z7,z6]),(0,[z0,z591,z3,z4,z7,z5,z6])],[(0,[z0,z3,z4,z592,z7,z5,z6]),(0,[z0,z593,z3,z4,z7,z5,z6]),(1,[z0,z3,z4,z7,z419,z6]),(0,[z100,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z27,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z594]),(0,[z0,z3,z595,z4,z7,z5,z6])],[(0,[z0,z3,z4,z7,z5,z596,z6]),(0,[z0,z3,z230,z4,z7,z5,z6]),(0,[z0,z597,z3,z4,z7,z5,z6])],[(0,[z0,z3,z4,z7,z5,z159,z6]),(0,[z0,z2,z3,z4,z118,z5,z6]),(0,[z0,z3,z4,z7,z598,z5,z6]),(0,[z0,z18,z3,z98,z4,z5,z6]),(0,[z0,z4,z7,z70,z5,z6,z120]),(0,[z0,z3,z465,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z599]),(0,[z0,z3,z4,z7,z600,z5,z6])],[(0,[z601,z0,z3,z4,z7,z5,z6]),(0,[z86,z0,z29,z3,z4,z7,z5]),(0,[z0,z3,z4,z7,z5,z6,z602]),(0,[z0,z18,z3,z4,z7,z5,z6]),(0,[z0,z18,z3,z4,z5,z6,z14]),(0,[z0,z3,z603,z4,z7,z5,z6]),(0,[z0,z604,z3,z4,z7,z5,z6])]],
   [[(0,[z0,z3,z4,z7,z5,z605,z6]),(0,[z0,z3,z4,z7,z5,z6,z606]),(0,[z0,z3,z607,z4,z7,z5,z6]),(0,[z0,z2,z129,z3,z4,z5,z6]),(0,[z0,z248,z47,z3,z7,z5,z6])],[(0,[z0,z429,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z608,z5,z6]),(0,[z0,z248,z18,z3,z4,z5,z6]),(0,[z0,z609,z3,z4,z7,z5,z6])],[(0,[z168,z0,z18,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z610,z6]),(0,[z0,z3,z4,z7,z5,z6,z611])],[(0,[z0,z3,z4,z7,z242,z5,z6]),(0,[z0,z47,z3,z4,z78,z5,z6]),(0,[z0,z3,z4,z7,z612,z5,z6]),(0,[z613,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z614,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z615]),(0,[z0,z517,z3,z4,z82,z5,z6]),(0,[z0,z3,z4,z7,z616,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z322]),(0,[z0,z3,z617,z4,z7,z5,z6])],[(0,[z0,z3,z4,z7,z5,z6,z618]),(0,[z75,z0,z3,z4,z242,z5,z6]),(1,[z0,z3,z4,z7,z159,z6]),(0,[z0,z3,z4,z619,z7,z5,z6]),(0,[z0,z3,z4,z457,z82,z5,z6]),(0,[z0,z13,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z200,z5,z6]),(0,[z0,z3,z4,z7,z70,z5,z6]),(0,[z0,z47,z3,z7,z197,z5,z6]),(0,[z0,z3,z4,z7,z620,z5,z6]),(1,[z0,z103,z4,z7,z5,z6])],[(0,[z621,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z120]),(0,[z0,z3,z4,z59,z5,z6,z36])],[(0,[z0,z2,z3,z4,z85,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z622]),(0,[z0,z62,z4,z7,z197,z5,z6]),(0,[z0,z3,z4,z7,z5,z623,z6]),(1,[z0,z4,z7,z5,z245,z6])],[(0,[z0,z2,z38,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z419,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z104]),(0,[z0,z27,z4,z7,z118,z5,z6]),(0,[z0,z3,z4,z624,z7,z5,z6]),(1,[z0,z3,z4,z7,z151,z6]),(1,[z0,z22,z3,z7,z6,z23])]],
   [[(0,[z625,z0,z3,z4,z7,z5,z6]),(0,[z0,z2,z3,z157,z4,z5,z6])],[(0,[z48,z0,z3,z4,z7,z85,z6]),(0,[z48,z0,z129,z3,z4,z7,z6]),(1,[z0,z3,z4,z102,z5,z6]),(0,[z0,z3,z626,z4,z7,z5,z6])],[(0,[z300,z0,z3,z38,z4,z7,z6]),(0,[z0,z3,z4,z7,z627,z5,z6]),(0,[z0,z201,z3,z4,z5,z6,z120])],[(0,[z0,z2,z3,z4,z5,z21,z6]),(0,[z0,z3,z4,z628,z7,z5,z6])],[(0,[z0,z17,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z629,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z630])],[(0,[z0,z3,z4,z7,z5,z6,z631]),(0,[z10,z0,z38,z4,z7,z5,z6]),(0,[z632,z0,z3,z4,z7,z5,z6]),(0,[z0,z633,z3,z4,z7,z5,z6]),(0,[z313,z3,z4,z7,z5,z6,z30]),(0,[z0,z16,z3,z4,z7,z107,z5])],[(0,[z0,z3,z4,z7,z5,z6,z634]),(0,[z53,z0,z428,z4,z7,z5,z6]),(0,[z0,z18,z47,z3,z4,z5,z6]),(0,[z51,z0,z3,z4,z7,z107,z6]),(0,[z0,z3,z635,z4,z7,z5,z6]),(0,[z0,z3,z636,z4,z7,z5,z6])],[(1,[z0,z191,z3,z7,z5,z6]),(0,[z530,z0,z3,z4,z7,z5,z6]),(0,[z637,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z638,z6])]],
   [[(0,[z0,z3,z4,z7,z639,z5,z6]),(0,[z0,z18,z3,z4,z24,z5,z6]),(0,[z0,z454,z3,z4,z7,z5,z120]),(0,[z0,z3,z4,z7,z640,z5,z6]),(1,[z0,z4,z7,z5,z6,z276]),(0,[z0,z72,z3,z4,z7,z5,z6])],[(1,[z168,z3,z4,z7,z5,z87])],[(0,[z0,z18,z136,z3,z4,z5,z6]),(0,[z0,z18,z232,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z25,z6])],[(0,[z182,z0,z2,z3,z4,z5,z6]),(0,[z95,z0,z3,z4,z7,z85,z6]),(0,[z95,z0,z129,z3,z4,z7,z6]),(0,[z0,z4,z7,z5,z6,z276,z104])],[(0,[z0,z3,z94,z4,z7,z5,z6]),(0,[z127,z3,z19,z4,z7,z5,z6]),(0,[z0,z27,z4,z7,z5,z21,z6]),(0,[z0,z3,z4,z7,z5,z641,z6])],[(0,[z0,z3,z384,z4,z7,z5,z6]),(0,[z168,z0,z29,z3,z4,z7,z5]),(0,[z0,z18,z3,z4,z5,z87,z6]),(0,[z0,z3,z4,z7,z5,z6,z532]),(0,[z0,z3,z96,z4,z7,z5,z183]),(0,[z51,z0,z3,z4,z7,z28,z6]),(0,[z0,z22,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z30]),(0,[z0,z3,z4,z642,z7,z5,z6]),(0,[z0,z15,z3,z4,z5,z25,z6]),(0,[z0,z3,z4,z7,z5,z643,z6])],[(0,[z0,z3,z4,z7,z5,z49,z6])],[(0,[z0,z3,z644,z4,z7,z5,z6]),(0,[z86,z0,z2,z3,z4,z5,z6]),(0,[z0,z26,z37,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z645]),(1,[z0,z129,z4,z7,z70,z6]),(1,[z0,z232,z4,z7,z5,z21]),(0,[z0,z29,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z646,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z647])]],
   [[(0,[z75,z0,z3,z4,z7,z5,z6]),(0,[z53,z0,z3,z4,z77,z5,z6]),(0,[z0,z648,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z5,z25,z6,z104])],[(0,[z0,z3,z4,z7,z649,z5,z6]),(0,[z0,z3,z4,z7,z650,z5,z6])],[(0,[z0,z3,z651,z4,z7,z5,z6]),(0,[z0,z18,z3,z4,z59,z5,z6])],[(0,[z0,z136,z27,z4,z7,z5,z6]),(0,[z51,z0,z13,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z28,z5,z6]),(0,[z0,z3,z4,z652,z7,z5,z6])],[(0,[z653,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z94,z4,z174,z7,z5]),(0,[z654,z0,z3,z4,z7,z5,z6]),(0,[z0,z2,z3,z4,z70,z5,z6]),(0,[z500,z0,z3,z4,z7,z5,z6]),(0,[z0,z13,z18,z3,z4,z5,z6]),(0,[z0,z3,z157,z4,z7,z5,z43]),(0,[z0,z3,z655,z4,z7,z5,z6])],[(0,[z0,z2,z136,z4,z7,z5,z6]),(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z656]),(0,[z0,z657,z3,z4,z7,z5,z6])],[(0,[z0,z295,z3,z4,z7,z5,z6]),(1,[z75,z3,z174,z7,z5,z6]),(0,[z0,z3,z4,z7,z658,z5,z6]),(0,[z313,z0,z3,z4,z7,z5,z6]),(1,[z0,z3,z4,z365,z7,z5]),(0,[z0,z3,z4,z365,z7,z5,z36])],[(0,[z659,z0,z3,z4,z7,z5,z6]),(0,[z75,z0,z3,z4,z7,z5,z314]),(0,[z75,z3,z4,z7,z5,z87,z6]),(0,[z0,z3,z660,z4,z7,z5,z6]),(0,[z0,z3,z4,z661,z7,z5,z6])]],
   [[(0,[z0,z17,z3,z38,z4,z7,z5]),(0,[z0,z3,z4,z7,z147,z5,z6]),(0,[z0,z662,z3,z4,z7,z5,z6]),(0,[z0,z3,z663,z4,z7,z5,z6]),(0,[z664,z0,z3,z4,z7,z5,z6])],[(0,[z665,z0,z3,z4,z7,z5,z6]),(0,[z0,z666,z3,z4,z7,z5,z6]),(0,[z0,z2,z3,z4,z197,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z667]),(0,[z0,z3,z4,z7,z5,z6,z668]),(0,[z0,z669,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z670]),(0,[z0,z3,z4,z7,z5,z364,z6]),(0,[z0,z3,z4,z7,z5,z6,z671]),(0,[z672,z0,z3,z4,z7,z5,z6])],[(0,[z0,z190,z3,z4,z7,z5,z6]),(0,[z0,z248,z3,z4,z197,z5,z6])],[(0,[z10,z0,z136,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z673,z5,z6]),(0,[z0,z3,z4,z7,z5,z674,z6]),(0,[z0,z675,z3,z4,z7,z5,z6])],[(0,[z0,z3,z676,z4,z7,z5,z6]),(0,[z0,z3,z677,z4,z7,z5,z6]),(0,[z0,z678,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z58,z7,z5,z6])],[(0,[z679,z0,z3,z4,z7,z5,z6]),(0,[z0,z680,z3,z4,z7,z5,z6]),(0,[z0,z3,z428,z4,z7,z5,z6]),(0,[z168,z86,z3,z4,z7,z5,z6]),(0,[z0,z2,z4,z7,z118,z5,z6]),(0,[z0,z160,z18,z3,z4,z5,z6]),(0,[z0,z161,z18,z3,z4,z5,z6]),(0,[z0,z27,z4,z7,z70,z5,z6]),(0,[z0,z232,z3,z4,z7,z5,z43]),(0,[z0,z3,z4,z7,z5,z6,z681])],[(0,[z0,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z682]),(0,[z0,z3,z4,z7,z683,z5,z6]),(1,[z0,z3,z4,z424,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z684])],[(0,[z685,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z686,z5,z6])]],
   [[(0,[z0,z3,z4,z7,z5,z6,z687]),(0,[z0,z3,z4,z7,z5,z688,z6]),(0,[z0,z689,z3,z4,z7,z5,z6])],[(0,[z0,z60,z3,z38,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z690,z6]),(0,[z691,z0,z3,z4,z7,z5,z6]),(0,[z235,z3,z4,z7,z77,z5,z6]),(0,[z692,z0,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z693,z5,z6]),(0,[z0,z3,z4,z694,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z695]),(0,[z0,z3,z4,z7,z5,z6,z696])],[(0,[z0,z190,z3,z4,z174,z7,z5]),(0,[z127,z0,z37,z3,z7,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z487]),(0,[z0,z2,z3,z230,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z25,z6]),(0,[z697,z0,z3,z4,z7,z5,z6])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z0,z698,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z151,z6,z14]),(0,[z0,z699,z3,z4,z7,z5,z6]),(0,[z0,z29,z3,z157,z7,z5,z6])],[(0,[z0,z248,z2,z3,z4,z5,z6])],[(0,[z700,z0,z3,z4,z7,z5,z6]),(0,[z0,z701,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z44]),(0,[z168,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z702,z6]),(0,[z0,z3,z703,z4,z7,z5,z6])],[(0,[z704,z0,z3,z4,z7,z5,z6]),(0,[z0,z2,z3,z4,z5,z49,z6]),(0,[z0,z3,z4,z705,z7,z5,z6])],[(0,[z86,z0,z18,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z2,z3,z4,z147,z6]),(0,[z0,z707,z3,z4,z5,z6]),(0,[z0,z2,z110,z4,z5,z6]),(0,[z0,z3,z4,z7,z171,z532]),(0,[z0,z3,z4,z102,z5,z6])],[(0,[z0,z708,z3,z4,z5,z6]),(0,[z0,z3,z4,z334,z5,z32]),(0,[z3,z4,z709,z77,z5,z6]),(0,[z0,z3,z4,z710,z5,z6]),(0,[z0,z2,z96,z4,z419,z6]),(0,[z711,z2,z3,z4,z5,z6])],[(0,[z0,z3,z4,z7,z5,z712]),(0,[z0,z2,z4,z5,z6,z713]),(0,[z0,z143,z4,z7,z5,z6]),(0,[z0,z3,z4,z59,z5,z364])],[(0,[z0,z3,z4,z7,z5,z714]),(0,[z0,z2,z428,z4,z5,z6]),(0,[z0,z236,z3,z4,z6,z171]),(0,[z0,z715,z4,z7,z5,z6]),(0,[z0,z716,z3,z4,z5,z6])],[(0,[z182,z60,z38,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z717]),(0,[z0,z3,z4,z7,z718,z6]),(0,[z0,z3,z4,z7,z6,z719]),(0,[z0,z13,z3,z4,z7,z151])],[(0,[z500,z0,z3,z4,z6,z50]),(0,[z0,z3,z4,z7,z720,z6])],[(0,[z0,z3,z4,z7,z721,z6]),(0,[z0,z191,z3,z7,z5,z6]),(0,[z0,z3,z4,z722,z5,z6]),(0,[z0,z3,z4,z7,z5,z723]),(0,[z0,z724,z4,z7,z5,z6]),(1,[z0,z16,z3,z4,z213])],[(0,[z0,z725,z3,z4,z7,z5]),(0,[z0,z96,z34,z7,z5,z6]),(0,[z0,z2,z198,z4,z5,z6]),(0,[z0,z4,z7,z5,z6,z276]),(0,[z313,z3,z7,z5,z43,z6])]],
   [[(0,[z182,z2,z38,z4,z5,z6]),(0,[z0,z3,z4,z726,z5,z6]),(0,[z0,z2,z62,z4,z5,z6]),(0,[z0,z18,z103,z4,z5,z6])],[(0,[z2,z202,z136,z4,z5,z6]),(0,[z95,z18,z3,z4,z49,z6]),(0,[z0,z3,z4,z7,z5,z727]),(0,[z0,z2,z4,z5,z6,z509])],[(0,[z0,z18,z3,z4,z5,z6]),(0,[z0,z2,z614,z4,z5,z6]),(0,[z0,z728,z3,z4,z5,z6]),(0,[z0,z96,z4,z457,z5,z6]),(0,[z0,z2,z3,z4,z5,z183]),(0,[z0,z2,z3,z729,z5,z6]),(0,[z0,z3,z4,z7,z5,z730]),(0,[z0,z3,z660,z7,z5,z30]),(0,[z0,z16,z3,z4,z213,z104])],[(0,[z0,z60,z7,z82,z5,z6]),(1,[z300,z0,z2,z4,z6]),(0,[z0,z455,z3,z4,z151,z6])],[(0,[z182,z731,z4,z7,z5,z6]),(0,[z75,z190,z3,z4,z7,z5]),(0,[z0,z3,z4,z732,z5,z6]),(0,[z0,z4,z70,z5,z6,z713]),(0,[z0,z15,z3,z4,z364,z36])],[(0,[z0,z60,z359,z3,z5,z6]),(0,[z0,z309,z428,z4,z5,z6]),(0,[z10,z2,z136,z4,z5,z6]),(0,[z0,z384,z4,z7,z5,z32]),(0,[z0,z191,z3,z7,z5,z314]),(0,[z0,z733,z3,z4,z5,z6]),(0,[z0,z3,z4,z734,z5,z6]),(0,[z0,z232,z4,z5,z21,z116]),(0,[z0,z3,z7,z6,z735,z23])],[(0,[z0,z736,z4,z7,z5,z6]),(0,[z369,z3,z4,z77,z5,z6]),(0,[z48,z3,z4,z7,z85,z6]),(0,[z0,z3,z7,z5,z737,z6]),(0,[z0,z129,z4,z7,z70,z6])],[(0,[z0,z3,z4,z7,z738,z6]),(0,[z0,z739,z4,z7,z5,z6]),(0,[z117,z429,z3,z4,z5,z6]),(0,[z0,z740,z3,z4,z5,z6]),(0,[z0,z27,z4,z5,z6,z116]),(0,[z0,z3,z4,z7,z5,z741])]],
   [[(0,[z0,z17,z2,z38,z4,z5]),(0,[z0,z742,z4,z7,z5,z6]),(0,[z0,z2,z114,z4,z5,z6]),(0,[z313,z18,z3,z4,z5,z6]),(0,[z51,z0,z4,z7,z5,z119]),(0,[z0,z454,z3,z4,z5,z150]),(1,[z0,z15,z3,z4,z364]),(0,[z0,z743,z3,z4,z5,z6])],[(0,[z0,z18,z3,z4,z5,z314]),(0,[z0,z458,z2,z4,z5,z6]),(0,[z0,z2,z4,z533,z5,z6]),(0,[z51,z0,z13,z4,z7,z107]),(0,[z0,z3,z4,z7,z5,z744]),(0,[z0,z745,z4,z7,z5,z6])],[(0,[z0,z3,z746,z7,z5,z6]),(0,[z0,z26,z517,z82,z5,z6]),(0,[z0,z747,z3,z4,z5,z6]),(0,[z0,z285,z4,z5,z93,z6])],[(0,[z0,z3,z4,z7,z6,z735]),(0,[z0,z29,z3,z7,z5,z30]),(0,[z0,z748,z4,z7,z5,z6])],[(0,[z0,z3,z4,z7,z749,z6]),(0,[z0,z750,z3,z7,z5,z6]),(0,[z0,z12,z3,z4,z5,z487]),(0,[z0,z161,z3,z4,z5,z97]),(0,[z0,z18,z3,z157,z5,z43]),(0,[z0,z751,z3,z4,z5,z6])],[(0,[z0,z3,z4,z752,z5,z6]),(0,[z0,z3,z753,z7,z5,z6]),(0,[z0,z3,z4,z7,z754,z6]),(0,[z0,z755,z4,z7,z5,z6]),(0,[z51,z0,z2,z4,z6,z120]),(0,[z0,z47,z3,z312,z5,z6]),(0,[z756,z3,z4,z7,z5,z6]),(0,[z0,z3,z4,z365,z7,z5])],[(0,[z0,z17,z2,z4,z7,z5]),(0,[z75,z86,z29,z3,z7,z5]),(0,[z0,z4,z7,z70,z6,z757]),(0,[z0,z129,z4,z70,z6,z71])],[(1,[z0,z17,z2,z4,z5]),(0,[z117,z2,z136,z4,z5,z6]),(0,[z0,z3,z4,z242,z5,z32]),(0,[z75,z458,z3,z7,z5,z6]),(0,[z0,z3,z4,z5,z758,z6])]],
   [[(0,[z0,z3,z4,z7,z5,z759]),(0,[z0,z3,z4,z760,z5,z6])],[(0,[z329,z136,z4,z7,z5,z6]),(0,[z0,z4,z7,z5,z21,z336]),(0,[z51,z0,z4,z374,z5,z6]),(0,[z313,z29,z3,z7,z5,z30])],[(0,[z0,z3,z7,z5,z6,z761]),(0,[z168,z3,z251,z4,z7,z5]),(0,[z0,z3,z4,z6,z762,z36])],[(0,[z0,z2,z4,z5,z551,z6]),(0,[z0,z3,z4,z7,z5,z763]),(0,[z0,z764,z3,z4,z7,z5])],[(0,[z0,z3,z4,z765,z5,z6]),(0,[z0,z2,z4,z7,z5,z183]),(0,[z0,z3,z4,z24,z5,z195]),(0,[z0,z4,z7,z5,z6,z766])],[(0,[z0,z3,z4,z334,z147,z6]),(0,[z0,z190,z18,z3,z4,z5]),(0,[z3,z4,z7,z5,z87,z634]),(0,[z0,z3,z767,z7,z5,z6]),(0,[z0,z768,z4,z7,z5,z6])],[(0,[z0,z60,z2,z7,z5,z6]),(0,[z0,z309,z27,z4,z5,z6]),(0,[z0,z769,z3,z4,z7,z6]),(0,[z3,z4,z7,z5,z87,z770]),(0,[z0,z26,z18,z82,z5,z6]),(0,[z0,z237,z2,z4,z5,z6]),(0,[z0,z576,z2,z4,z5,z6]),(0,[z0,z3,z230,z197,z5,z6])],[(0,[z86,z191,z3,z4,z7,z5]),(0,[z0,z3,z4,z7,z107,z670]),(0,[z0,z3,z4,z5,z6,z771])]],
   [[(0,[z182,z18,z38,z4,z5,z6]),(0,[z0,z309,z3,z223,z4,z6]),(0,[z0,z3,z4,z7,z5,z772]),(0,[z0,z773,z4,z7,z5,z6]),(0,[z0,z774,z4,z7,z5,z6]),(0,[z0,z3,z4,z775,z5,z6]),(0,[z73,z0,z74,z18,z3,z4]),(0,[z0,z3,z4,z24,z5,z776])],[(0,[z0,z3,z4,z777,z5,z6]),(0,[z0,z778,z3,z4,z5,z6]),(0,[z0,z76,z4,z7,z159,z6]),(0,[z313,z3,z4,z7,z5,z87]),(0,[z0,z26,z2,z82,z5,z6]),(0,[z0,z26,z4,z457,z5,z6]),(0,[z0,z18,z3,z4,z6,z171]),(0,[z0,z285,z4,z7,z107,z5])],[(0,[z0,z38,z4,z375,z5,z6]),(0,[z0,z136,z4,z457,z5,z6]),(0,[z0,z2,z221,z4,z5,z6]),(0,[z0,z22,z18,z3,z6,z23]),(0,[z0,z779,z3,z4,z7,z5])],[(0,[z0,z60,z309,z3,z5,z6]),(0,[z0,z780,z3,z4,z5,z6]),(0,[z0,z15,z16,z3,z4,z107])],[(0,[z0,z781,z3,z7,z5,z6]),(0,[z3,z4,z7,z5,z770,z44]),(0,[z0,z4,z782,z5,z245,z6])],[(0,[z3,z19,z783,z7,z5,z6]),(0,[z3,z19,z7,z5,z6,z310]),(0,[z0,z3,z4,z784,z5,z6]),(0,[z0,z2,z273,z4,z5,z6]),(0,[z0,z785,z4,z7,z5,z6])],[(0,[z0,z3,z4,z7,z5,z786]),(0,[z0,z787,z3,z4,z5,z6]),(0,[z0,z3,z4,z788,z5,z6]),(0,[z0,z11,z2,z4,z5,z6]),(0,[z0,z2,z4,z760,z5,z6]),(0,[z69,z0,z2,z4,z5,z6]),(0,[z0,z232,z3,z4,z7,z151])],[(1,[z0,z60,z2,z5,z6]),(0,[z0,z2,z4,z577,z5,z6]),(1,[z0,z2,z4,z5,z183]),(0,[z0,z2,z382,z4,z5,z6]),(0,[z0,z3,z4,z46,z6,z36]),(0,[z0,z4,z7,z5,z6,z789])]],
   [[(0,[z0,z3,z4,z7,z790,z5]),(0,[z0,z309,z323,z3,z4,z5]),(0,[z0,z791,z4,z7,z5,z6])],[(0,[z0,z17,z3,z4,z7,z5]),(0,[z0,z792,z384,z4,z5,z6]),(0,[z0,z384,z4,z7,z147,z6]),(0,[z0,z793,z3,z4,z7,z5]),(0,[z0,z26,z7,z82,z5,z6]),(0,[z0,z236,z37,z96,z5,z6]),(0,[z0,z2,z3,z4,z5,z794]),(0,[z0,z232,z4,z7,z5,z594]),(0,[z0,z3,z4,z795,z5,z6]),(0,[z0,z796,z4,z7,z5,z6])],[(0,[z0,z60,z3,z223,z7,z6]),(0,[z0,z191,z18,z3,z5,z6]),(0,[z0,z3,z4,z797,z5,z6]),(0,[z0,z3,z4,z5,z798,z6]),(0,[z0,z143,z4,z7,z5,z364]),(0,[z0,z72,z3,z4,z107,z6])],[(0,[z0,z3,z4,z7,z5,z32]),(0,[z127,z3,z783,z7,z5,z6]),(0,[z0,z2,z96,z4,z5,z532]),(0,[z0,z18,z4,z5,z6,z684]),(0,[z0,z4,z7,z6,z757,z120])],[(0,[z0,z3,z799,z4,z7,z6]),(0,[z3,z4,z78,z709,z5,z6]),(0,[z0,z2,z4,z5,z6,z594])],[(0,[z300,z0,z60,z3,z7,z6]),(0,[z0,z3,z4,z7,z5,z800]),(0,[z86,z191,z3,z7,z5,z44]),(0,[z0,z18,z3,z4,z5,z801]),(0,[z0,z3,z4,z59,z643,z6])],[(1,[z3,z783,z7,z5,z6]),(0,[z0,z2,z4,z600,z5,z6]),(0,[z0,z2,z4,z598,z5,z6]),(0,[z0,z285,z18,z4,z5,z6]),(0,[z0,z802,z4,z7,z5,z6]),(0,[z0,z3,z4,z803,z5,z6])],[(0,[z0,z3,z804,z7,z5,z6]),(0,[z75,z244,z3,z7,z5,z6]),(0,[z0,z3,z805,z4,z7,z5]),(0,[z0,z2,z37,z96,z5,z6]),(0,[z51,z0,z4,z7,z119,z6]),(0,[z0,z15,z143,z4,z6,z36]),(0,[z0,z3,z4,z782,z5,z6])]],
   [[(0,[z0,z17,z2,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z806]),(0,[z0,z3,z4,z5,z6,z807]),(0,[z0,z3,z157,z7,z5,z808]),(0,[z0,z3,z4,z58,z59,z6]),(0,[z0,z809,z3,z4,z5,z6])],[(0,[z0,z3,z4,z7,z5,z810]),(0,[z0,z3,z7,z5,z6,z811]),(0,[z0,z3,z4,z5,z812,z6]),(0,[z0,z3,z4,z813,z5,z6]),(0,[z0,z3,z4,z5,z814,z6]),(0,[z0,z3,z4,z58,z7,z364])],[(0,[z0,z60,z323,z3,z7,z5]),(0,[z0,z3,z4,z7,z815,z6]),(0,[z0,z3,z4,z5,z6,z816])],[(0,[z0,z359,z3,z223,z4,z6]),(0,[z0,z3,z4,z242,z147,z6]),(0,[z817,z2,z3,z4,z5,z6]),(0,[z0,z2,z103,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z322]),(0,[z0,z160,z196,z4,z5,z6])],[(0,[z0,z384,z4,z334,z5,z6]),(0,[z86,z3,z4,z7,z5,z314]),(0,[z95,z2,z3,z4,z49,z6]),(0,[z0,z2,z4,z70,z5,z6]),(0,[z0,z455,z4,z5,z21,z6]),(0,[z0,z72,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z776,z104])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z300,z0,z2,z4,z5,z6]),(0,[z0,z818,z3,z4,z7,z5]),(0,[z0,z819,z3,z4,z5,z6]),(0,[z0,z3,z4,z820,z5,z6]),(0,[z0,z2,z4,z821,z5,z6])],[(0,[z0,z3,z4,z822,z5,z6]),(0,[z0,z2,z366,z4,z5,z6]),(0,[z0,z3,z4,z7,z823,z6])],[(0,[z3,z4,z7,z824,z49,z6]),(1,[z3,z4,z7,z5,z770]),(0,[z0,z825,z3,z4,z5,z6]),(0,[z0,z2,z4,z419,z5,z6]),(0,[z0,z3,z4,z5,z6,z713]),(0,[z0,z2,z3,z465,z4,z6]),(0,[z0,z2,z3,z4,z365,z5]),(0,[z0,z826,z4,z7,z5,z6]),(1,[z0,z3,z7,z6,z735]),(0,[z0,z3,z4,z58,z6,z762]),(0,[z73,z0,z74,z3,z4,z7])]],
   [[(0,[z0,z136,z4,z375,z5,z6]),(0,[z235,z202,z3,z4,z5,z6]),(0,[z0,z3,z4,z424,z5,z532]),(0,[z0,z3,z4,z7,z827,z6])],[(0,[z0,z3,z4,z7,z5,z828]),(0,[z0,z3,z94,z4,z7,z5]),(1,[z0,z7,z829,z5,z6]),(0,[z0,z3,z98,z7,z28,z6])],[(0,[z0,z3,z4,z830,z5,z6]),(0,[z0,z26,z2,z96,z5,z6]),(0,[z0,z2,z311,z4,z5,z6]),(0,[z0,z18,z2,z4,z5,z6]),(0,[z0,z2,z633,z4,z5,z6]),(0,[z0,z13,z4,z7,z5,z706]),(0,[z0,z103,z4,z7,z213,z6])],[(0,[z0,z359,z323,z3,z4,z5]),(0,[z75,z76,z174,z7,z5,z6]),(0,[z0,z18,z76,z4,z5,z6]),(0,[z0,z3,z4,z831,z5,z6])],[(0,[z0,z2,z3,z4,z5,z314]),(0,[z0,z2,z4,z5,z6,z630]),(0,[z0,z18,z657,z4,z5,z6]),(0,[z0,z3,z4,z832,z5,z6])],[(0,[z0,z27,z4,z424,z5,z6]),(0,[z0,z3,z4,z7,z107,z83])],[(0,[z0,z833,z3,z4,z5,z6]),(0,[z0,z3,z7,z829,z5,z6]),(0,[z0,z3,z4,z834,z5,z6]),(0,[z0,z835,z4,z7,z5,z6]),(0,[z0,z16,z4,z5,z276,z104])],[(0,[z0,z309,z3,z4,z5,z6]),(0,[z313,z3,z4,z7,z5,z6]),(0,[z75,z0,z26,z2,z5,z6]),(0,[z0,z3,z4,z836,z7,z5]),(0,[z168,z0,z191,z3,z7,z5]),(0,[z0,z3,z4,z5,z837,z6]),(0,[z0,z838,z4,z7,z5,z6])]],
   [[(0,[z0,z839,z4,z7,z5,z6]),(0,[z0,z840,z3,z4,z5,z6]),(0,[z86,z0,z13,z2,z4,z5]),(0,[z0,z13,z2,z4,z5,z14]),(1,[z0,z4,z7,z6,z757]),(0,[z0,z3,z7,z5,z808,z30]),(0,[z219,z0,z143,z4,z5,z6]),(0,[z0,z841,z4,z7,z5,z6])],[(0,[z0,z842,z4,z7,z5,z6]),(0,[z0,z843,z3,z4,z5,z6]),(0,[z0,z348,z2,z4,z5,z6]),(0,[z0,z18,z338,z4,z5,z6]),(0,[z0,z3,z4,z7,z6,z762])],[(0,[z0,z3,z4,z844,z5,z6]),(0,[z0,z18,z3,z4,z845,z6]),(0,[z0,z846,z3,z4,z5,z6])],[(0,[z3,z731,z4,z7,z5,z6]),(0,[z0,z847,z3,z7,z5,z6]),(0,[z0,z3,z4,z5,z6,z848]),(0,[z0,z3,z4,z849,z5,z6]),(0,[z0,z850,z4,z7,z5,z6])],[(1,[z0,z4,z7,z5,z723]),(0,[z0,z13,z4,z7,z151,z6])],[(0,[z0,z666,z3,z7,z6,z23]),(0,[z0,z3,z4,z7,z6,z757])],[(0,[z313,z3,z4,z7,z5,z314]),(0,[z3,z4,z7,z5,z6,z31]),(0,[z0,z13,z4,z102,z5,z6])],[(0,[z0,z3,z4,z7,z5,z851]),(0,[z0,z3,z4,z7,z147,z6]),(0,[z0,z4,z7,z829,z5,z6]),(0,[z0,z18,z37,z96,z5,z6]),(0,[z0,z3,z4,z5,z6,z150]),(0,[z0,z3,z4,z5,z119,z150]),(0,[z0,z852,z4,z7,z5,z6]),(0,[z0,z74,z779,z3,z4,z7])]],
   [[(0,[z0,z191,z3,z7,z5,z43]),(0,[z0,z26,z2,z312,z5,z6]),(0,[z51,z0,z2,z4,z6,z50]),(0,[z711,z3,z4,z7,z5,z6])],[(0,[z0,z18,z3,z4,z213,z6]),(0,[z0,z853,z285,z4,z5,z6])],[(0,[z0,z3,z4,z7,z854,z6]),(0,[z0,z384,z4,z242,z5,z6]),(0,[z75,z2,z3,z174,z5,z6]),(0,[z0,z855,z4,z7,z5,z6]),(0,[z0,z3,z856,z7,z5,z6]),(0,[z0,z236,z3,z4,z5,z532]),(0,[z0,z2,z604,z4,z5,z6])],[(0,[z0,z3,z7,z5,z43,z314]),(0,[z0,z3,z4,z58,z138,z6]),(0,[z0,z18,z4,z5,z6,z322])],[(0,[z0,z2,z3,z4,z6,z171]),(0,[z0,z2,z256,z4,z5,z6]),(0,[z0,z3,z4,z5,z857,z6]),(0,[z0,z13,z4,z7,z5,z723])],[(0,[z0,z2,z194,z4,z5,z6]),(0,[z0,z3,z4,z7,z858,z6]),(0,[z0,z853,z3,z4,z5,z6]),(0,[z0,z18,z4,z821,z5,z6]),(0,[z51,z0,z454,z4,z7,z120]),(0,[z0,z4,z7,z70,z284,z6]),(0,[z0,z3,z4,z151,z6,z184])],[(0,[z0,z3,z4,z859,z5,z6]),(0,[z0,z3,z4,z5,z6,z860]),(0,[z0,z3,z4,z7,z147,z314]),(0,[z75,z3,z94,z174,z7,z5]),(0,[z0,z2,z3,z4,z5,z119]),(0,[z0,z3,z861,z7,z5,z6]),(0,[z0,z16,z103,z4,z5,z6])],[(0,[z0,z38,z4,z457,z5,z6]),(0,[z0,z3,z4,z7,z862,z6]),(0,[z0,z18,z3,z465,z4,z6]),(0,[z0,z248,z3,z41,z5,z6]),(0,[z0,z18,z3,z4,z365,z5]),(1,[z51,z0,z4,z7,z119]),(0,[z0,z3,z192,z7,z5,z43])]],
   [[(0,[z0,z2,z566,z4,z5,z6]),(0,[z51,z0,z201,z4,z5,z6])],[(0,[z0,z76,z4,z7,z5,z32]),(0,[z75,z3,z174,z7,z159,z6]),(0,[z0,z3,z4,z7,z5,z183]),(0,[z0,z3,z4,z424,z419,z6]),(0,[z0,z3,z4,z7,z419,z532]),(0,[z863,z3,z4,z7,z5,z6])],[(0,[z0,z359,z3,z4,z5,z6]),(0,[z0,z3,z4,z334,z5,z6]),(0,[z0,z3,z4,z7,z183,z171]),(0,[z0,z864,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z25,z333])],[(0,[z0,z3,z4,z865,z5,z6]),(0,[z0,z37,z651,z7,z5,z6]),(0,[z664,z3,z4,z7,z5,z87])],[(0,[z0,z866,z3,z4,z7,z5]),(0,[z0,z3,z4,z7,z867,z6]),(0,[z0,z190,z3,z4,z7,z5]),(0,[z0,z13,z455,z4,z5,z6])],[(0,[z182,z309,z38,z4,z5,z6]),(0,[z0,z60,z18,z3,z5,z6]),(0,[z300,z0,z17,z3,z4,z7]),(0,[z235,z3,z4,z709,z5,z6]),(0,[z0,z868,z3,z4,z5,z6]),(0,[z0,z3,z366,z197,z5,z6]),(0,[z0,z248,z869,z3,z5,z6]),(0,[z0,z15,z3,z4,z547,z6])],[(0,[z0,z27,z4,z7,z419,z6]),(0,[z0,z3,z4,z7,z107,z450]),(0,[z0,z3,z4,z7,z870,z6])],[(0,[z0,z291,z2,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z871]),(0,[z0,z2,z680,z4,z5,z6]),(0,[z0,z872,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z873]),(0,[z0,z2,z4,z686,z5,z6]),(0,[z0,z196,z230,z4,z5,z6]),(0,[z0,z874,z4,z7,z5,z6]),(0,[z0,z15,z3,z4,z5,z364])]],
   [[(0,[z0,z60,z2,z3,z5,z6]),(0,[z0,z875,z4,z7,z5,z6]),(1,[z3,z4,z7,z824,z6]),(0,[z876,z3,z4,z7,z5,z6]),(0,[z0,z4,z7,z5,z6,z877]),(0,[z0,z878,z3,z4,z5,z6])],[(0,[z0,z2,z651,z4,z5,z6]),(0,[z0,z3,z4,z334,z5,z314]),(0,[z0,z37,z96,z7,z5,z183]),(0,[z0,z567,z3,z4,z7,z107]),(0,[z313,z13,z3,z4,z7,z5]),(0,[z0,z879,z3,z4,z5,z6])],[(0,[z0,z2,z290,z4,z5,z6]),(0,[z0,z18,z3,z4,z880,z6]),(0,[z0,z881,z4,z7,z5,z6]),(0,[z0,z285,z4,z7,z107,z83]),(1,[z0,z779,z3,z4,z7])],[(0,[z300,z0,z295,z3,z7,z6]),(0,[z0,z2,z453,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z882]),(0,[z0,z16,z3,z4,z7,z213]),(0,[z0,z779,z3,z4,z7,z83])],[(0,[z86,z2,z3,z4,z5,z44]),(0,[z0,z3,z230,z200,z5,z6]),(0,[z0,z3,z4,z7,z5,z801]),(0,[z51,z0,z4,z6,z150,z120]),(0,[z0,z3,z4,z59,z6,z762])],[(0,[z0,z2,z246,z4,z5,z6]),(0,[z0,z160,z2,z4,z5,z6]),(0,[z0,z4,z821,z7,z5,z6]),(0,[z0,z2,z3,z4,z5,z364]),(0,[z0,z883,z4,z7,z5,z6]),(0,[z0,z72,z4,z5,z245,z6])],[(0,[z2,z136,z38,z4,z5,z6]),(0,[z0,z384,z4,z7,z5,z6]),(0,[z0,z884,z3,z4,z5,z6]),(0,[z0,z57,z3,z312,z5,z6]),(0,[z0,z2,z4,z5,z245,z6])],[(0,[z0,z2,z96,z4,z5,z183]),(0,[z0,z2,z4,z5,z6,z706]),(0,[z0,z3,z292,z7,z28,z6]),(0,[z0,z3,z4,z7,z5,z808])]],
   [[(0,[z0,z885,z3,z4,z5,z6]),(0,[z300,z0,z359,z3,z4,z6]),(0,[z402,z0,z2,z4,z5,z6]),(0,[z530,z291,z3,z4,z5,z6]),(0,[z0,z18,z3,z4,z5,z886]),(0,[z0,z15,z3,z4,z365,z36]),(0,[z0,z143,z4,z59,z5,z6])],[(0,[z0,z3,z4,z5,z6,z887]),(0,[z471,z0,z16,z3,z4,z5])],[(0,[z0,z17,z295,z3,z7,z5]),(0,[z0,z2,z54,z4,z5,z6]),(0,[z75,z18,z3,z174,z5,z6])],[(0,[z127,z0,z190,z3,z7,z5]),(0,[z0,z190,z2,z3,z4,z5]),(0,[z0,z3,z4,z5,z6,z888]),(0,[z889,z3,z4,z7,z5,z6]),(0,[z0,z236,z3,z4,z419,z6]),(0,[z0,z3,z4,z5,z396,z104]),(0,[z0,z201,z4,z70,z5,z6]),(0,[z890,z3,z4,z7,z5,z6]),(0,[z0,z72,z74,z3,z4,z6])],[(0,[z182,z300,z38,z4,z7,z6]),(0,[z0,z891,z4,z7,z5,z6]),(0,[z0,z892,z3,z4,z7,z5]),(0,[z0,z191,z3,z7,z5,z30]),(0,[z0,z201,z3,z4,z5,z6]),(0,[z3,z4,z7,z5,z6,z893]),(0,[z0,z4,z7,z140,z6,z276])],[(0,[z0,z3,z4,z894,z5,z6]),(0,[z0,z384,z4,z7,z5,z314]),(0,[z0,z54,z4,z78,z5,z6]),(0,[z86,z187,z3,z4,z7,z5]),(1,[z0,z4,z821,z5,z6]),(0,[z0,z13,z4,z7,z5,z14]),(0,[z0,z3,z4,z7,z107,z547])],[(0,[z0,z3,z4,z7,z895,z6]),(0,[z0,z2,z76,z4,z5,z6]),(0,[z0,z896,z4,z7,z5,z6]),(0,[z0,z18,z3,z4,z5,z119]),(0,[z0,z3,z4,z5,z6,z762])],[(0,[z0,z17,z359,z3,z4,z5]),(0,[z0,z3,z4,z7,z159,z32]),(0,[z0,z15,z4,z6,z322,z36]),(0,[z0,z3,z4,z7,z140,z6]),(0,[z0,z897,z3,z4,z5,z6])]],
   [[(0,[z182,z359,z38,z4,z5,z6]),(0,[z0,z3,z4,z242,z5,z6]),(0,[z0,z96,z4,z760,z5,z6]),(0,[z51,z0,z2,z4,z138,z6]),(0,[z0,z22,z2,z3,z6,z23]),(0,[z0,z62,z230,z197,z5,z6])],[(0,[z10,z136,z4,z7,z5,z6]),(0,[z0,z898,z3,z4,z7,z6]),(0,[z0,z899,z4,z7,z5,z6]),(0,[z0,z2,z3,z4,z419,z6]),(0,[z0,z88,z3,z4,z138,z6]),(0,[z0,z3,z4,z5,z6,z116]),(0,[z0,z4,z5,z6,z322,z71]),(0,[z0,z4,z7,z5,z6,z900]),(0,[z313,z0,z29,z3,z7,z5])],[(0,[z0,z901,z3,z7,z5,z6]),(0,[z0,z3,z7,z5,z6,z902]),(0,[z0,z903,z3,z4,z5,z6]),(0,[z0,z3,z4,z821,z5,z6]),(0,[z0,z18,z350,z4,z5,z6]),(0,[z904,z3,z4,z7,z5,z6]),(0,[z0,z905,z3,z4,z5,z6])],[(0,[z0,z196,z4,z78,z5,z6]),(0,[z0,z3,z4,z906,z5,z6])],[(0,[z0,z37,z384,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z907]),(0,[z0,z3,z4,z5,z6,z776])],[(0,[z0,z908,z3,z4,z5,z6]),(0,[z0,z909,z4,z7,z5,z6]),(0,[z51,z0,z4,z7,z6,z50])],[(0,[z0,z2,z295,z3,z5,z6]),(0,[z0,z60,z384,z7,z5,z6]),(0,[z530,z3,z4,z77,z5,z6]),(0,[z52,z0,z2,z4,z5,z6]),(0,[z0,z232,z4,z7,z5,z723])],[(0,[z0,z309,z2,z4,z5,z6]),(0,[z0,z833,z76,z4,z5,z6]),(0,[z0,z3,z4,z242,z5,z314]),(0,[z51,z48,z0,z2,z4,z6]),(0,[z0,z3,z4,z910,z5,z6])]],
   [[(0,[z0,z191,z2,z3,z5,z6]),(0,[z0,z2,z549,z4,z5,z6]),(0,[z0,z911,z3,z7,z5,z6])],[(0,[z0,z2,z3,z4,z159,z6]),(0,[z0,z912,z4,z7,z5,z6]),(0,[z0,z2,z4,z91,z5,z6]),(0,[z0,z3,z4,z7,z845,z6]),(0,[z0,z869,z3,z197,z5,z6]),(0,[z0,z913,z4,z7,z5,z6])],[(0,[z182,z295,z38,z7,z5,z6]),(0,[z0,z2,z384,z4,z5,z6])],[(0,[z0,z60,z2,z38,z5,z6]),(0,[z0,z914,z4,z7,z5,z6]),(0,[z915,z3,z4,z7,z5,z6]),(0,[z0,z129,z198,z4,z7,z6]),(0,[z0,z16,z3,z4,z140,z104])],[(0,[z86,z18,z3,z4,z5,z44]),(0,[z0,z2,z3,z4,z151,z6]),(0,[z0,z285,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z213,z6]),(0,[z0,z3,z4,z7,z916,z6]),(0,[z0,z3,z413,z7,z6,z23])],[(0,[z0,z3,z4,z7,z5,z917]),(0,[z0,z2,z38,z4,z5,z6]),(0,[z0,z918,z3,z4,z5,z6]),(0,[z73,z0,z74,z2,z3,z4]),(0,[z0,z18,z3,z4,z5,z364]),(0,[z0,z232,z617,z4,z7,z5]),(0,[z0,z4,z7,z5,z6,z919]),(0,[z0,z920,z4,z7,z5,z6])],[(0,[z300,z0,z309,z3,z4,z6]),(0,[z0,z129,z614,z4,z7,z6]),(0,[z0,z3,z4,z921,z5,z6]),(0,[z0,z3,z4,z7,z922,z6]),(0,[z0,z18,z4,z5,z245,z6]),(0,[z0,z129,z4,z7,z6,z509]),(0,[z0,z3,z4,z7,z5,z923]),(0,[z0,z3,z4,z5,z6,z924])],[(0,[z0,z323,z3,z4,z7,z5]),(0,[z86,z3,z305,z4,z7,z5]),(0,[z0,z925,z4,z7,z5,z6]),(0,[z73,z0,z13,z2,z4,z5]),(0,[z0,z502,z2,z4,z5,z6]),(0,[z0,z2,z4,z115,z5,z6]),(0,[z0,z2,z4,z5,z6,z116]),(0,[z0,z18,z515,z4,z5,z6]),(0,[z0,z3,z4,z24,z258,z5])]],
   [[(0,[z0,z926,z3,z4,z5,z6]),(0,[z127,z443,z3,z7,z5,z6]),(0,[z0,z18,z3,z5,z128,z6]),(0,[z0,z13,z4,z5,z184,z14]),(0,[z0,z22,z3,z7,z6,z735]),(0,[z313,z29,z3,z7,z5,z6]),(0,[z0,z3,z927,z4,z7,z6])],[(0,[z0,z731,z4,z7,z5,z6]),(0,[z0,z3,z928,z4,z7,z6]),(0,[z0,z72,z3,z4,z107,z5])],[(0,[z0,z3,z4,z929,z5,z6]),(0,[z0,z18,z54,z4,z5,z6]),(0,[z817,z3,z4,z7,z5,z6]),(0,[z0,z29,z18,z3,z5,z30]),(0,[z0,z4,z7,z5,z6,z930])],[(0,[z0,z3,z4,z7,z5,z931]),(0,[z95,z3,z4,z7,z49,z6]),(0,[z0,z3,z4,z932,z5,z6]),(0,[z0,z3,z465,z4,z7,z6]),(0,[z0,z4,z102,z5,z21,z6]),(0,[z313,z232,z3,z4,z7,z5])],[(0,[z0,z3,z4,z7,z5,z6]),(0,[z0,z933,z3,z4,z7,z5]),(0,[z0,z175,z2,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z934]),(0,[z0,z3,z4,z935,z5,z6]),(1,[z0,z285,z4,z7,z107])],[(0,[z0,z17,z309,z3,z4,z5]),(0,[z0,z936,z3,z4,z5,z6]),(0,[z0,z29,z2,z3,z5,z30]),(0,[z0,z3,z4,z7,z5,z937]),(0,[z51,z0,z4,z7,z6,z120]),(0,[z51,z0,z4,z7,z119,z120]),(0,[z73,z0,z3,z4,z7,z238])],[(0,[z168,z3,z4,z7,z5,z770]),(0,[z168,z2,z3,z4,z5,z87]),(0,[z0,z3,z4,z5,z6,z938]),(0,[z0,z3,z939,z7,z5,z6])],[(0,[z127,z2,z3,z19,z5,z6])]],
   [[(0,[z168,z689,z3,z4,z7,z5])],[(0,[z0,z3,z4,z7,z5,z940]),(0,[z75,z3,z174,z7,z5,z32]),(0,[z0,z3,z941,z7,z5,z6]),(0,[z0,z18,z3,z4,z419,z6]),(0,[z0,z3,z4,z7,z5,z942]),(0,[z51,z0,z2,z4,z70,z6]),(0,[z29,z3,z7,z5,z31,z30])],[(0,[z0,z3,z4,z7,z5,z943]),(0,[z0,z3,z4,z944,z5,z6])],[(0,[z0,z3,z4,z945,z5,z6]),(0,[z0,z3,z4,z7,z5,z314]),(0,[z0,z3,z529,z7,z28,z6]),(0,[z0,z62,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z946,z6]),(1,[z0,z3,z7,z5,z808])],[(0,[z0,z947,z3,z7,z5,z6]),(0,[z75,z3,z7,z5,z315,z6]),(0,[z0,z948,z4,z7,z5,z6]),(0,[z0,z37,z96,z7,z5,z6]),(0,[z0,z13,z2,z4,z5,z21]),(0,[z51,z0,z4,z7,z6,z630]),(0,[z0,z196,z230,z197,z5,z6]),(0,[z0,z15,z3,z4,z6,z647])],[(0,[z0,z3,z949,z7,z5,z6]),(0,[z0,z37,z7,z829,z5,z6]),(0,[z0,z3,z4,z7,z419,z183])],[(0,[z0,z2,z223,z38,z4,z6]),(0,[z0,z18,z295,z3,z5,z6]),(0,[z0,z3,z4,z7,z950,z6]),(0,[z0,z951,z4,z7,z5,z6]),(0,[z0,z16,z103,z4,z5,z104])],[(0,[z182,z223,z38,z4,z7,z6]),(0,[z0,z952,z3,z4,z5,z6]),(0,[z0,z60,z17,z3,z7,z5]),(0,[z0,z3,z4,z709,z5,z6]),(0,[z320,z3,z4,z7,z49,z6]),(0,[z0,z869,z3,z4,z5,z6]),(0,[z0,z953,z3,z4,z5,z6]),(0,[z0,z161,z103,z4,z5,z6])]],
   [[(0,[z0,z2,z136,z4,z5,z6]),(0,[z0,z3,z7,z5,z6,z954]),(0,[z0,z156,z2,z4,z5,z6]),(0,[z51,z0,z74,z2,z4,z6])],[(0,[z0,z2,z295,z38,z5,z6]),(0,[z410,z38,z4,z7,z5,z6]),(0,[z0,z18,z3,z4,z159,z6]),(0,[z235,z3,z4,z77,z5,z6]),(0,[z0,z3,z4,z7,z955,z6]),(0,[z0,z4,z7,z5,z6,z956]),(0,[z86,z0,z191,z3,z7,z5]),(0,[z0,z3,z4,z7,z5,z957]),(0,[z0,z2,z421,z4,z5,z6]),(0,[z0,z455,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z880,z6]),(0,[z0,z3,z4,z5,z6,z958]),(0,[z0,z3,z959,z4,z5,z6])],[(0,[z731,z38,z4,z7,z5,z6]),(0,[z0,z18,z384,z4,z5,z6]),(0,[z3,z4,z7,z5,z87,z314]),(0,[z0,z3,z7,z5,z128,z6]),(0,[z0,z2,z96,z4,z5,z6])],[(0,[z0,z3,z4,z960,z5,z6]),(0,[z0,z4,z7,z5,z21,z622]),(0,[z0,z248,z47,z3,z5,z6]),(0,[z0,z4,z7,z107,z245,z83])],[(0,[z0,z961,z2,z4,z5,z6]),(0,[z0,z26,z384,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z962]),(0,[z0,z963,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z873]),(0,[z0,z2,z4,z189,z5,z6]),(0,[z0,z18,z3,z4,z151,z6])],[(0,[z0,z3,z4,z375,z5,z6]),(0,[z182,z323,z38,z4,z7,z5]),(0,[z0,z3,z964,z7,z5,z6]),(0,[z127,z3,z19,z7,z5,z6]),(0,[z0,z2,z569,z4,z5,z6]),(0,[z0,z4,z7,z5,z965,z6]),(0,[z0,z966,z3,z4,z7,z5])],[(0,[z0,z415,z2,z4,z5,z6]),(0,[z0,z76,z4,z242,z5,z6]),(0,[z0,z3,z967,z7,z5,z6]),(0,[z0,z96,z7,z829,z5,z6]),(0,[z0,z968,z3,z4,z7,z6]),(0,[z0,z4,z7,z70,z6,z448]),(0,[z0,z3,z4,z7,z969,z6]),(0,[z0,z3,z4,z5,z6,z970]),(0,[z0,z15,z3,z4,z364,z6])],[(0,[z0,z3,z4,z7,z5,z971]),(0,[z0,z972,z4,z7,z5,z6]),(0,[z51,z0,z2,z4,z5,z6]),(0,[z0,z4,z7,z5,z6,z322]),(0,[z0,z3,z4,z7,z5,z886]),(0,[z0,z3,z973,z4,z5,z6]),(0,[z0,z3,z157,z7,z5,z43])]],
   [[(0,[z0,z323,z3,z223,z4,z7]),(0,[z0,z2,z4,z372,z5,z6]),(0,[z0,z974,z4,z7,z5,z6]),(0,[z86,z244,z3,z4,z7,z5]),(0,[z0,z3,z4,z7,z975,z5]),(0,[z0,z3,z98,z7,z6,z735])],[(0,[z75,z3,z167,z7,z5,z6]),(0,[z0,z976,z4,z7,z5,z6]),(0,[z3,z4,z7,z5,z824,z6]),(0,[z0,z3,z4,z7,z5,z977]),(0,[z0,z978,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z979])],[(0,[z53,z3,z4,z78,z5,z6]),(0,[z0,z129,z4,z102,z70,z6]),(0,[z0,z72,z3,z4,z7,z107])],[(0,[z0,z3,z4,z5,z6,z980]),(0,[z0,z3,z4,z7,z6,z171]),(0,[z0,z2,z3,z4,z5,z532]),(0,[z0,z13,z4,z7,z151,z5]),(0,[z0,z3,z4,z584,z7,z107])],[(0,[z392,z38,z4,z7,z5,z6]),(0,[z0,z409,z2,z4,z5,z6]),(0,[z0,z285,z74,z4,z7,z6])],[(0,[z0,z2,z4,z5,z215,z6]),(0,[z10,z136,z4,z101,z5,z6]),(0,[z0,z18,z454,z3,z4,z5]),(0,[z51,z0,z3,z4,z7,z119]),(0,[z0,z3,z4,z7,z5,z119]),(0,[z0,z4,z5,z245,z6,z771])],[(0,[z168,z18,z3,z4,z5,z87]),(0,[z0,z74,z3,z4,z7,z667]),(0,[z0,z4,z374,z70,z5,z6])],[(0,[z0,z3,z4,z981,z5,z6]),(0,[z127,z18,z3,z19,z5,z6]),(0,[z0,z291,z54,z4,z5,z6]),(0,[z0,z27,z4,z5,z6,z71])]],
   [[(0,[z0,z295,z3,z223,z7,z6]),(0,[z0,z3,z4,z7,z982,z6]),(0,[z0,z2,z4,z225,z5,z6]),(0,[z0,z2,z3,z861,z5,z6]),(0,[z0,z29,z3,z7,z5,z808]),(0,[z0,z3,z4,z24,z7,z213]),(1,[z0,z72,z3,z4,z107])],[(0,[z0,z54,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z983,z6]),(0,[z0,z285,z4,z7,z5,z6]),(0,[z0,z3,z7,z5,z6,z735])],[(0,[z0,z3,z4,z7,z6,z984]),(0,[z0,z985,z4,z7,z5,z6]),(0,[z0,z2,z142,z4,z5,z6]),(0,[z986,z3,z4,z7,z5,z6]),(0,[z0,z987,z3,z4,z5,z6]),(0,[z0,z779,z3,z4,z7,z107])],[(0,[z0,z903,z76,z4,z5,z6]),(0,[z0,z37,z96,z7,z6,z171]),(0,[z0,z574,z2,z4,z5,z6]),(0,[z0,z143,z4,z365,z7,z5])],[(0,[z0,z3,z4,z7,z988,z6]),(0,[z0,z966,z2,z3,z4,z5])],[(0,[z0,z13,z2,z4,z5,z6]),(0,[z0,z274,z3,z4,z5,z195]),(0,[z0,z2,z192,z4,z5,z6])],[(0,[z3,z4,z783,z7,z5,z6]),(0,[z127,z3,z7,z5,z434,z6]),(0,[z0,z989,z4,z7,z5,z6]),(0,[z0,z3,z4,z7,z990,z6]),(0,[z53,z348,z3,z4,z5,z6]),(0,[z172,z0,z2,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z991]),(0,[z0,z3,z4,z374,z5,z6]),(0,[z0,z3,z4,z7,z992,z6]),(0,[z0,z3,z4,z993,z5,z6]),(0,[z73,z0,z3,z4,z7,z330])],[(0,[z0,z295,z3,z7,z5,z6]),(0,[z0,z961,z3,z4,z5,z6]),(0,[z0,z196,z4,z7,z5,z6]),(0,[z0,z2,z232,z4,z5,z21]),(0,[z0,z3,z4,z58,z541,z6])]],
   [[(0,[z0,z60,z2,z4,z5,z6]),(0,[z95,z3,z4,z7,z824,z6]),(0,[z219,z0,z2,z4,z5,z6])],[(0,[z0,z112,z2,z4,z5,z6]),(0,[z0,z2,z96,z4,z6,z171]),(0,[z0,z1,z3,z200,z5,z6]),(0,[z2,z3,z4,z5,z6,z31])],[(0,[z0,z76,z4,z7,z5,z6]),(0,[z0,z3,z4,z994,z5,z6]),(0,[z3,z783,z174,z7,z5,z6]),(0,[z0,z995,z3,z4,z5,z6]),(0,[z0,z15,z3,z4,z6,z36]),(0,[z0,z285,z3,z4,z7,z107])],[(0,[z0,z3,z4,z996,z5,z6]),(0,[z0,z997,z3,z4,z7,z6]),(0,[z0,z3,z4,z7,z998,z6]),(0,[z86,z3,z4,z7,z5,z44]),(0,[z0,z2,z3,z5,z128,z6]),(0,[z0,z2,z531,z4,z5,z6]),(0,[z0,z3,z4,z7,z999,z6]),(0,[z0,z103,z4,z7,z140,z6])],[(0,[z182,z38,z4,z7,z5,z6]),(0,[z0,z3,z4,z242,z159,z6]),(0,[z75,z190,z3,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z1000]),(0,[z51,z0,z246,z4,z7,z6]),(0,[z0,z2,z3,z4,z5,z1001]),(0,[z0,z2,z4,z5,z420,z6]),(0,[z0,z259,z3,z366,z5,z6]),(0,[z0,z3,z4,z7,z5,z364])],[(0,[z0,z3,z4,z7,z5,z1002]),(0,[z48,z3,z4,z7,z824,z6]),(0,[z0,z26,z7,z829,z5,z6]),(0,[z0,z2,z4,z424,z5,z6]),(0,[z0,z15,z3,z4,z6,z50])],[(0,[z0,z3,z4,z5,z6,z1003]),(0,[z0,z2,z4,z5,z183,z6]),(1,[z0,z869,z3,z5,z6]),(0,[z1004,z3,z4,z7,z5,z6])],[(0,[z0,z2,z148,z4,z5,z6]),(1,[z3,z4,z709,z5,z6]),(0,[z0,z13,z465,z4,z7,z14])]],
   [[(0,[z0,z3,z4,z101,z5,z6]),(0,[z300,z0,z18,z3,z4,z6]),(0,[z0,z3,z7,z1005,z5,z6]),(0,[z0,z1006,z4,z7,z5,z6]),(0,[z0,z1007,z3,z4,z7,z5]),(0,[z0,z4,z7,z213,z6,z276])],[(0,[z0,z792,z3,z4,z5,z6]),(0,[z0,z76,z4,z7,z5,z314]),(0,[z0,z4,z7,z5,z6,z1008]),(0,[z0,z239,z2,z4,z5,z6]),(0,[z0,z2,z298,z4,z5,z6]),(0,[z0,z4,z7,z70,z5,z119])],[(0,[z0,z1009,z4,z7,z5,z6])],[(0,[z0,z3,z4,z1010,z5,z6]),(0,[z0,z18,z3,z4,z5,z532]),(0,[z0,z16,z3,z4,z5,z487]),(0,[z0,z2,z4,z5,z6,z276]),(0,[z0,z160,z3,z41,z5,z6]),(0,[z0,z45,z3,z4,z46,z6]),(0,[z0,z3,z4,z7,z107,z393]),(0,[z0,z3,z4,z1011,z5,z6])],[(0,[z75,z190,z3,z174,z7,z5]),(0,[z0,z29,z3,z167,z7,z5]),(0,[z0,z3,z106,z7,z5,z43]),(0,[z0,z2,z3,z4,z1012,z6]),(0,[z51,z0,z2,z4,z6,z23]),(0,[z0,z4,z5,z6,z276,z116])],[(0,[z0,z18,z3,z94,z4,z5]),(0,[z185,z3,z4,z78,z5,z6]),(0,[z0,z449,z2,z4,z5,z6])],[(0,[z3,z4,z7,z5,z770,z6]),(0,[z0,z517,z3,z4,z5,z6]),(0,[z0,z4,z5,z245,z93,z6])],[(0,[z0,z60,z37,z7,z5,z6]),(0,[z0,z17,z18,z3,z4,z5]),(0,[z0,z3,z4,z1013,z5,z6]),(0,[z53,z54,z4,z78,z5,z6]),(0,[z0,z3,z4,z424,z5,z183])]],
   [[(0,[z0,z76,z4,z7,z147,z6]),(1,[z86,z191,z3,z7,z5]),(0,[z0,z3,z4,z7,z419,z6])],[(0,[z0,z428,z4,z7,z5,z6]),(0,[z0,z1014,z4,z7,z5,z6]),(0,[z0,z3,z4,z5,z6,z1015]),(0,[z0,z15,z3,z4,z6,z762])],[(0,[z0,z3,z4,z7,z1016,z6]),(0,[z0,z3,z4,z7,z5,z1017]),(0,[z0,z3,z4,z1018,z5,z6]),(0,[z0,z72,z3,z4,z107,z83])],[(0,[z0,z2,z323,z38,z4,z5]),(0,[z0,z3,z7,z5,z43,z682]),(0,[z0,z2,z3,z4,z107,z83]),(0,[z0,z3,z4,z7,z5,z794]),(0,[z0,z2,z209,z4,z5,z6]),(0,[z0,z18,z4,z5,z6,z397]),(0,[z0,z103,z4,z5,z25,z6])],[(0,[z0,z27,z4,z7,z5,z183]),(0,[z0,z3,z4,z7,z1019,z6]),(0,[z0,z4,z7,z5,z723,z14])],[(0,[z0,z3,z4,z1020,z5,z6]),(0,[z313,z3,z4,z7,z5,z44]),(0,[z0,z13,z2,z4,z5,z487]),(1,[z0,z3,z4,z5,z776])],[(0,[z0,z3,z4,z1021,z5,z6]),(0,[z117,z136,z4,z7,z5,z6]),(0,[z0,z1022,z3,z4,z5,z6]),(0,[z1023,z3,z4,z7,z5,z6])],[(0,[z0,z1024,z3,z4,z5,z6]),(0,[z0,z3,z1025,z4,z5,z6]),(0,[z0,z18,z475,z4,z5,z6]),(0,[z86,z191,z3,z7,z5,z6]),(0,[z0,z18,z232,z4,z5,z21]),(0,[z0,z4,z7,z5,z6,z1026]),(0,[z0,z74,z3,z4,z7,z99])]],
   [[(0,[z0,z3,z4,z7,z159,z6]),(0,[z0,z37,z96,z7,z419,z6]),(0,[z0,z2,z4,z301,z5,z6]),(0,[z3,z4,z7,z5,z6,z1027]),(0,[z0,z4,z7,z1028,z5,z6])],[(0,[z0,z18,z3,z4,z5,z32]),(0,[z0,z161,z2,z4,z5,z6]),(0,[z154,z348,z3,z4,z5,z6]),(0,[z0,z3,z4,z1029,z5,z6])],[(0,[z0,z3,z4,z457,z5,z6]),(0,[z0,z129,z3,z4,z7,z119]),(0,[z0,z4,z7,z5,z245,z6])],[(0,[z0,z309,z295,z3,z5,z6]),(0,[z0,z76,z4,z334,z5,z6]),(0,[z75,z0,z190,z3,z7,z5]),(0,[z0,z13,z290,z4,z7,z5]),(0,[z0,z187,z2,z4,z5,z6]),(0,[z0,z3,z4,z7,z151,z6]),(0,[z313,z3,z157,z4,z7,z5]),(0,[z0,z1030,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z213,z6]),(0,[z0,z4,z365,z7,z5,z322])],[(0,[z0,z29,z3,z7,z5,z314]),(0,[z0,z2,z4,z316,z5,z6]),(0,[z0,z15,z143,z4,z5,z6])],[(0,[z300,z0,z323,z3,z4,z7]),(0,[z10,z136,z4,z375,z5,z6]),(0,[z0,z3,z4,z7,z1031,z6]),(0,[z0,z1032,z4,z7,z5,z6]),(0,[z0,z2,z208,z4,z5,z6]),(0,[z3,z4,z7,z85,z824,z6])],[(0,[z300,z0,z27,z4,z7,z6]),(0,[z75,z3,z174,z242,z5,z6]),(0,[z0,z1033,z3,z4,z7,z5]),(0,[z0,z26,z2,z4,z5,z6]),(0,[z0,z2,z4,z7,z419,z6]),(0,[z0,z1034,z4,z7,z5,z6])],[(0,[z0,z3,z4,z7,z5,z1035]),(0,[z0,z3,z4,z7,z159,z314]),(0,[z95,z449,z3,z4,z7,z6]),(0,[z0,z3,z4,z5,z6,z184]),(0,[z0,z3,z4,z5,z25,z97]),(0,[z0,z3,z1036,z7,z5,z6]),(0,[z0,z1037,z3,z4,z5,z6]),(0,[z0,z3,z465,z4,z6,z184]),(0,[z0,z1038,z4,z7,z5,z6])]],
   [[(0,[z0,z2,z4,z325,z5,z6]),(0,[z0,z2,z609,z4,z5,z6]),(0,[z0,z2,z454,z3,z4,z5]),(0,[z51,z0,z4,z7,z6,z757]),(0,[z0,z201,z3,z4,z5,z119])],[(0,[z0,z3,z223,z4,z7,z6]),(0,[z0,z3,z7,z5,z6,z1039]),(0,[z0,z236,z3,z4,z5,z183]),(0,[z0,z13,z4,z7,z5,z417]),(0,[z0,z4,z7,z5,z1040,z6])],[(0,[z0,z3,z4,z7,z5,z1041]),(0,[z3,z4,z709,z7,z5,z6]),(0,[z0,z2,z4,z46,z5,z6]),(0,[z0,z2,z143,z4,z5,z6]),(0,[z0,z2,z4,z501,z5,z6]),(0,[z0,z869,z3,z7,z5,z6])],[(0,[z0,z3,z1042,z4,z7,z6]),(0,[z0,z2,z4,z335,z5,z6]),(0,[z0,z2,z3,z4,z5,z730]),(0,[z0,z18,z4,z5,z6,z276]),(0,[z0,z3,z4,z7,z5,z1043])],[(0,[z0,z2,z4,z5,z337,z6]),(0,[z219,z0,z3,z4,z6,z261]),(0,[z0,z3,z4,z5,z6,z1044])],[(0,[z0,z17,z27,z4,z7,z5]),(0,[z0,z3,z4,z1045,z5,z6]),(0,[z0,z1046,z3,z4,z7,z5]),(0,[z168,z3,z4,z7,z5,z87]),(0,[z3,z4,z7,z5,z6,z1047])],[(0,[z300,z0,z2,z38,z4,z6]),(0,[z1048,z0,z3,z4,z7,z6]),(0,[z75,z3,z783,z7,z5,z6]),(0,[z0,z3,z7,z5,z6,z1049]),(0,[z0,z3,z157,z281,z7,z5]),(0,[z0,z4,z7,z5,z21,z723]),(0,[z0,z3,z4,z107,z93,z83])],[(0,[z53,z428,z4,z78,z5,z6]),(0,[z48,z2,z3,z4,z85,z6]),(0,[z0,z3,z4,z5,z25,z776])]],
   [[(0,[z136,z731,z4,z7,z5,z6]),(0,[z86,z3,z4,z7,z5,z770]),(0,[z51,z0,z2,z4,z107,z6]),(0,[z0,z234,z2,z4,z5,z6]),(0,[z0,z740,z285,z4,z5,z6])],[(0,[z0,z3,z7,z1050,z5,z6]),(1,[z0,z2,z4,z419,z6]),(0,[z0,z2,z586,z4,z5,z6])],[(0,[z0,z3,z4,z7,z5,z1051]),(0,[z0,z18,z278,z4,z5,z6]),(0,[z0,z489,z47,z3,z5,z6]),(1,[z0,z13,z4,z7,z151]),(0,[z0,z4,z7,z151,z21,z6]),(0,[z0,z3,z1052,z7,z5,z6])],[(0,[z0,z3,z783,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z1053]),(0,[z0,z18,z3,z4,z107,z83]),(0,[z0,z454,z3,z4,z7,z5]),(0,[z0,z232,z4,z7,z5,z21]),(0,[z0,z16,z3,z4,z5,z104])],[(0,[z300,z0,z2,z4,z7,z6]),(0,[z0,z3,z4,z7,z5,z1054]),(0,[z0,z47,z869,z3,z5,z6]),(0,[z0,z3,z4,z7,z5,z776]),(0,[z73,z0,z285,z4,z7,z5])],[(0,[z0,z60,z27,z7,z5,z6]),(0,[z0,z18,z196,z4,z5,z6]),(0,[z0,z27,z4,z821,z5,z6]),(0,[z0,z4,z7,z5,z6,z723])],[(0,[z0,z359,z295,z3,z5,z6]),(0,[z0,z4,z7,z5,z6,z1055]),(0,[z48,z3,z464,z4,z7,z6]),(0,[z0,z2,z3,z98,z28,z6]),(0,[z0,z3,z4,z7,z1056,z5]),(0,[z0,z455,z3,z465,z4,z6])],[(0,[z0,z3,z1057,z4,z7,z5]),(0,[z0,z7,z829,z82,z5,z6]),(0,[z3,z4,z7,z5,z6,z1058]),(0,[z51,z0,z2,z4,z28,z6]),(0,[z0,z2,z129,z4,z70,z6]),(0,[z51,z0,z18,z4,z6,z120]),(1,[z313,z29,z3,z7,z5])]],
   [[(0,[z0,z1059,z3,z4,z7,z5])],[(0,[z0,z3,z4,z334,z159,z6]),(0,[z0,z1060,z3,z4,z5,z6]),(0,[z53,z3,z4,z709,z5,z6]),(0,[z95,z51,z0,z2,z4,z6]),(0,[z0,z1061,z4,z7,z5,z6])],[(0,[z75,z3,z174,z7,z5,z6]),(0,[z0,z16,z3,z4,z213,z6]),(0,[z0,z285,z4,z7,z107,z6])],[(0,[z0,z2,z3,z223,z4,z6]),(0,[z0,z3,z4,z7,z5,z1062]),(0,[z0,z3,z4,z7,z5,z1063]),(0,[z0,z4,z7,z5,z6,z1064]),(0,[z0,z1065,z3,z4,z5,z6]),(0,[z0,z232,z566,z4,z7,z5]),(0,[z0,z4,z5,z21,z6,z873]),(0,[z0,z2,z4,z118,z5,z6]),(0,[z0,z779,z3,z4,z7,z6])],[(0,[z190,z3,z19,z4,z7,z5]),(0,[z1066,z0,z3,z4,z7,z6]),(0,[z0,z3,z4,z7,z5,z770]),(0,[z0,z4,z7,z5,z6,z757]),(0,[z0,z1067,z4,z7,z5,z6])],[(0,[z0,z1068,z3,z4,z5,z6]),(0,[z0,z18,z3,z4,z147,z6]),(0,[z0,z2,z165,z4,z5,z6]),(0,[z0,z3,z4,z213,z25,z6])],[(0,[z51,z0,z201,z4,z6,z120])],[(0,[z117,z3,z4,z78,z5,z6]),(0,[z0,z3,z4,z1069,z5,z6]),(0,[z0,z248,z196,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1070]),(0,[z0,z1071,z4,z7,z5,z6])]],
   [[(0,[z0,z2,z3,z94,z4,z5]),(0,[z0,z54,z4,z77,z5,z6]),(0,[z0,z18,z428,z4,z5,z6]),(0,[z0,z869,z3,z230,z5,z6])],[(0,[z75,z3,z174,z7,z5,z314]),(0,[z0,z3,z729,z7,z5,z6]),(0,[z0,z1072,z3,z4,z5,z6])],[(0,[z0,z3,z4,z7,z1073,z5]),(0,[z0,z3,z4,z424,z5,z6]),(0,[z0,z3,z4,z7,z5,z532]),(0,[z0,z13,z4,z7,z5,z487]),(0,[z0,z18,z143,z4,z5,z6]),(0,[z0,z3,z7,z5,z6,z808])],[(0,[z0,z2,z323,z3,z4,z5])],[(0,[z0,z3,z4,z1074,z5,z6]),(1,[z731,z4,z7,z5,z6]),(0,[z0,z2,z4,z5,z388,z6]),(0,[z0,z3,z4,z1075,z5,z6]),(0,[z0,z1076,z4,z7,z5,z6]),(0,[z0,z3,z7,z5,z6,z1077])],[(0,[z0,z3,z4,z7,z5,z1078]),(0,[z0,z384,z4,z7,z159,z6]),(0,[z0,z2,z3,z4,z140,z6]),(0,[z0,z18,z62,z4,z5,z6])],[(0,[z0,z3,z4,z7,z6,z1079]),(0,[z0,z1080,z3,z4,z7,z5]),(0,[z75,z3,z7,z5,z43,z87]),(0,[z0,z1081,z3,z4,z5,z6]),(0,[z0,z196,z4,z77,z5,z6]),(0,[z0,z16,z3,z4,z213,z5])],[(0,[z300,z0,z3,z4,z7,z6]),(0,[z0,z961,z38,z4,z5,z6]),(0,[z48,z18,z3,z4,z85,z6]),(0,[z0,z3,z4,z5,z6,z1082]),(0,[z0,z18,z3,z4,z5,z183]),(0,[z0,z559,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z398,z6]),(0,[z0,z13,z2,z4,z5,z43]),(0,[z73,z0,z779,z3,z4,z7])]],
   [[(0,[z0,z3,z4,z7,z1083,z6]),(0,[z0,z3,z4,z7,z1084,z6]),(0,[z75,z3,z174,z7,z147,z6]),(0,[z0,z1085,z3,z4,z7,z5]),(0,[z0,z2,z648,z4,z5,z6]),(0,[z0,z2,z4,z5,z21,z6]),(0,[z313,z29,z3,z4,z7,z5])],[(0,[z0,z3,z4,z7,z1086,z6]),(0,[z0,z62,z4,z424,z5,z6])],[(0,[z0,z3,z4,z7,z1087,z6]),(0,[z0,z37,z96,z424,z5,z6]),(0,[z0,z37,z96,z7,z5,z532]),(0,[z0,z3,z4,z7,z6,z1088]),(0,[z0,z13,z2,z4,z107,z5]),(0,[z51,z0,z203,z4,z7,z6]),(0,[z0,z4,z7,z1089,z5,z6])],[(0,[z0,z3,z4,z7,z6,z1090]),(0,[z0,z3,z4,z7,z5,z1091]),(0,[z0,z16,z3,z4,z5,z776])],[(0,[z0,z3,z4,z7,z5,z1092]),(0,[z0,z520,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z32]),(0,[z0,z3,z4,z7,z1093,z6]),(0,[z0,z1094,z3,z4,z5,z6]),(0,[z0,z3,z7,z5,z43,z808])],[(0,[z108,z0,z2,z4,z5,z6]),(0,[z0,z3,z4,z7,z1095,z6]),(0,[z405,z3,z4,z7,z85,z6]),(0,[z0,z129,z4,z7,z6,z757])],[(0,[z0,z26,z2,z200,z5,z6]),(0,[z0,z18,z3,z98,z28,z6])],[(0,[z0,z3,z4,z7,z1096,z6]),(0,[z127,z0,z26,z2,z5,z6]),(0,[z1097,z0,z3,z4,z7,z6]),(0,[z0,z18,z129,z4,z70,z6]),(0,[z0,z13,z4,z7,z151,z14]),(1,[z0,z3,z4,z6,z762])]],
   [[(0,[z0,z3,z4,z1098,z5,z6]),(0,[z0,z3,z4,z24,z5,z25]),(0,[z73,z0,z72,z3,z4,z5])],[(0,[z0,z3,z4,z7,z5,z1099]),(0,[z0,z3,z267,z197,z5,z6]),(0,[z0,z3,z4,z1100,z5,z6]),(0,[z0,z13,z2,z4,z5,z195]),(0,[z0,z18,z27,z4,z5,z6]),(0,[z0,z4,z821,z118,z5,z6])],[(0,[z0,z1101,z4,z7,z5,z6]),(0,[z0,z3,z4,z5,z6,z1102]),(0,[z0,z3,z4,z7,z5,z1103])],[(0,[z0,z18,z3,z223,z4,z6]),(0,[z0,z3,z4,z5,z6,z1104]),(0,[z0,z3,z4,z1105,z5,z6]),(0,[z75,z3,z174,z334,z5,z6]),(0,[z0,z3,z4,z7,z5,z1001]),(0,[z18,z3,z4,z5,z6,z31]),(0,[z0,z3,z4,z59,z6,z261]),(0,[z51,z0,z4,z7,z6,z417])],[(0,[z0,z236,z3,z4,z5,z6]),(0,[z0,z1106,z3,z7,z5,z6]),(0,[z0,z3,z4,z7,z5,z1107])],[(0,[z0,z1108,z4,z7,z5,z6]),(0,[z0,z1109,z3,z7,z5,z6]),(0,[z0,z232,z4,z374,z5,z21]),(0,[z0,z72,z285,z4,z5,z6])],[(0,[z0,z60,z3,z7,z5,z6]),(0,[z300,z0,z2,z3,z4,z6]),(0,[z0,z3,z4,z7,z5,z1110]),(0,[z0,z4,z7,z5,z6,z1111]),(0,[z0,z26,z457,z82,z5,z6]),(0,[z0,z26,z7,z200,z5,z6]),(0,[z0,z15,z3,z4,z7,z364])],[(0,[z0,z37,z373,z7,z5,z6]),(0,[z0,z701,z2,z4,z5,z6]),(0,[z380,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z610,z6]),(0,[z0,z201,z454,z3,z4,z5]),(0,[z0,z15,z675,z3,z4,z6])]],
   [[(0,[z0,z1112,z4,z7,z5,z6]),(0,[z0,z3,z4,z1113,z5,z6]),(0,[z637,z0,z13,z4,z7,z5])],[(0,[z0,z1114,z4,z7,z5,z6]),(0,[z0,z3,z4,z424,z6,z171]),(0,[z0,z2,z968,z3,z4,z6]),(0,[z0,z352,z2,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z71]),(0,[z0,z260,z3,z4,z5,z396])],[(0,[z0,z3,z4,z7,z1115,z6]),(0,[z0,z3,z4,z1116,z5,z6]),(0,[z0,z3,z4,z1117,z5,z6]),(0,[z0,z2,z292,z4,z5,z6]),(0,[z0,z2,z617,z4,z5,z6]),(0,[z0,z3,z7,z28,z6,z735]),(0,[z0,z1118,z3,z4,z5,z6])],[(0,[z0,z18,z323,z3,z4,z5]),(0,[z0,z323,z295,z3,z7,z5]),(0,[z0,z3,z4,z7,z1119,z5]),(0,[z0,z3,z4,z1120,z5,z6]),(0,[z100,z202,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1121]),(0,[z0,z3,z4,z7,z1012,z6]),(0,[z0,z16,z3,z4,z5,z647])],[(0,[z0,z3,z1122,z7,z5,z6]),(0,[z86,z3,z7,z5,z128,z44])],[(0,[z0,z17,z2,z3,z4,z5]),(0,[z0,z3,z1123,z7,z5,z6]),(1,[z75,z190,z3,z7,z5]),(0,[z0,z2,z373,z4,z5,z6]),(0,[z0,z3,z4,z7,z824,z6]),(0,[z0,z1124,z4,z7,z5,z6]),(0,[z0,z2,z4,z459,z5,z6]),(0,[z0,z18,z3,z4,z140,z6]),(0,[z0,z3,z4,z5,z93,z6])],[(0,[z0,z3,z4,z7,z1125,z6]),(0,[z0,z3,z4,z1126,z5,z6]),(0,[z0,z3,z4,z7,z147,z32]),(0,[z0,z3,z4,z7,z5,z1127]),(0,[z191,z3,z7,z5,z87,z6]),(0,[z168,z0,z13,z2,z4,z5]),(0,[z0,z2,z4,z5,z396,z6]),(0,[z51,z0,z4,z7,z450,z6]),(0,[z0,z1128,z4,z7,z5,z6]),(0,[z0,z4,z7,z5,z1129,z6])],[(0,[z75,z384,z174,z7,z5,z6]),(0,[z0,z3,z4,z1130,z5,z6]),(0,[z0,z3,z4,z7,z1131,z6]),(0,[z0,z2,z4,z466,z5,z6]),(0,[z0,z13,z455,z4,z5,z14])]],
   [[(0,[z0,z926,z384,z4,z5,z6]),(0,[z0,z2,z196,z4,z5,z6]),(0,[z313,z2,z3,z4,z5,z6])],[(0,[z0,z1132,z3,z4,z7,z5]),(0,[z0,z3,z4,z7,z1133,z6]),(0,[z1134,z3,z4,z7,z5,z6]),(0,[z0,z4,z7,z5,z364,z322])],[(0,[z0,z3,z4,z7,z1135,z6]),(0,[z0,z3,z4,z7,z1136,z6]),(0,[z0,z13,z18,z4,z5,z14])],[(0,[z412,z0,z29,z3,z7,z5]),(0,[z0,z2,z4,z5,z476,z6]),(0,[z0,z1137,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z6,z1138]),(0,[z0,z3,z4,z7,z5,z1139]),(0,[z0,z13,z2,z4,z5,z30]),(0,[z0,z103,z4,z7,z5,z6]),(0,[z0,z13,z4,z7,z5,z393]),(0,[z0,z3,z4,z7,z5,z1140]),(0,[z3,z4,z7,z5,z6,z1141])],[(0,[z182,z17,z38,z4,z7,z5]),(0,[z0,z3,z4,z7,z1142,z5]),(0,[z0,z2,z3,z157,z5,z43]),(0,[z0,z1143,z4,z7,z5,z6])],[(0,[z0,z16,z3,z4,z5,z670])],[(0,[z0,z3,z1144,z7,z5,z6]),(0,[z10,z731,z4,z7,z5,z6]),(0,[z0,z3,z4,z5,z6,z1145]),(0,[z0,z3,z1146,z7,z5,z6]),(0,[z0,z22,z3,z7,z6,z23])],[(0,[z0,z2,z4,z485,z5,z6]),(0,[z0,z2,z4,z484,z5,z6]),(0,[z0,z17,z3,z223,z4,z7]),(0,[z0,z2,z4,z5,z6,z71]),(0,[z0,z1147,z3,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 518) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 518).take 517) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1035).take 193) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1228)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [518, 517, 193] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 83).take 80).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 163).take 86).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 249).take 7).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [83, 80, 86, 7] = true :=
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

end PEqualNP.Outside.L_meta_45662

theorem PEqualNP.Outside.L_meta_45662 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241824 * 2 ^ 32 + 3938494976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241824 * 2 ^ 32 + 3938494976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45662.solve