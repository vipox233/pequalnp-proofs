import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36769

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
  Nat.testBit (4008373984 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0xc1308052c1309052#64 ++ 0x75003623488d22d2#64 ++ 0xc7f1c1ffc7f1f1fe#64 ++ 0xffd27f63cd8f33f3#64 : BitVec 256),
   (0x48520a0548522224#64 ++ 0x7509383860e188b8#64 ++ 0xf8fe7e0ff8fe7e3f#64 ++ 0xf5adb8bc72f1ccfc#64 : BitVec 256),
   (0x008554a000854488#64 ++ 0x8030c0c017005505#64 ++ 0x00fffff000ffffcf#64 ++ 0xbf71c0c07f01ff1f#64 : BitVec 256),
   (0x9200673992007900#64 ++ 0x80b600d6835a0f60#64 ++ 0xff007fffff007ff0#64 ++ 0xd5be00ff83fe0fe0#64 : BitVec 256),
   (0x000079ce24e80000#64 ++ 0xe63fed0003b7f000#64 ++ 0x00007fffffff8000#64 ++ 0xe63fff0003fff000#64 : BitVec 256),
   (0x24e8000000000000#64 ++ 0x983fdbedfc000000#64 ++ 0xffff800000000000#64 ++ 0xf83ffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [2, 11]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [13, 12]⟩, ⟨.and, [8, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000080400400000 0x6409280000a18000 0x00007e0ff8fe0000 0xe42db80002f1c000

def z1 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00007fffffff8000 0xe63fff0003fff000

def z2 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00fffff000ffffcf 0xbf71c0c07f01ff1f

def z3 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffff800000000000 0xf83ffffffc000000

def z4 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe7e0ff8fe7e3f 0xf5adb8bc72f1ccfc

def z5 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff007fffff007ff0 0xd5be00ff83fe0fe0

def z6 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f1c1ffc7f1f1fe 0xffd27f63cd8f33f3

def z7 : W := mkw 0x000079ce24e80000 0x660f2d0003b7f000 0x00007fffffff8000 0x460e3f0003fff000

def z8 : W := mkw 0x6c7a0a0548522224 0x7d0f3b3de8e188b8 0xfffe7e0ff8fe7e3f 0xf5afbfbff2f1ccfc

def z9 : W := mkw 0x0000084624680000 0x66092d0000a5a000 0x0000000000000000 0x00003f0000000000

def z10 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xffffffffffffffff 0xffffc0ffffffffff

def z11 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff00000fff000030 0x408e003f80fe00e0

def z12 : W := mkw 0x9200653892005900 0x80b600c6831a0740 0x070001f0070001c0 0x00120043810e0300

def z13 : W := mkw 0xe5b88052c1309052 0xfd36f7e7dc8d22d2 0xc7f1c1ffc7f1f1fe 0xffd27f63cd8f33f3

def z14 : W := mkw 0x8120805281209052 0x00000603080c2242 0xc701c1ffc701f1f0 0xdfd247638d8e33e3

def z15 : W := mkw 0xd330e57ad330d952 0xf5b636e7cb9f27d2 0xc7f1c1ffc7f1f1fe 0xffd27f63cd8f33f3

def z16 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x00ffffffffffffcf 0xff7fffc07fffff1f

def z17 : W := mkw 0xc9728a57c972b276 0x75093e3b68edaafa 0xffffffffffffffff 0xffffffffffffffff

def z18 : W := mkw 0x4852020148122224 0x11001038604008b8 0xf8fe000000007e3f 0x118000bc70000cfc

def z19 : W := mkw 0x008514a000854488 0x0000c0c014005505 0x00ff800000ffffcf 0x3b41c0c07c01ff1f

def z20 : W := mkw 0x0000000000000000 0x803fc9c480000000 0xff00000000000000 0xf03fffff80000000

def z21 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xfffffff000ffffcf 0xff7fffffff01ff1f

def z22 : W := mkw 0xc1308010c1109052 0x11001223480802d2 0xc7f18000000071fe 0x19c00063cc0003f3

def z23 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xff00000000000000 0x400e3f3f80000000

def z24 : W := mkw 0xc1b5d4f2c1b5d4da 0xf530f6e35f8d77d7 0xc7ffffffc7ffffff 0xfff3ffe3ff8fffff

def z25 : W := mkw 0x48120a0548522224 0x6500201000e188b8 0x00007e0ff8fe7e3f 0x0580000002f1ccfc

def z26 : W := mkw 0x0000508000800000 0x8030c00003005000 0x00007ff000ff8000 0xa631c0000301f000

def z27 : W := mkw 0x24e8000000000000 0x180f1bedfc000000 0xffff800000000000 0x580e3ffffc000000

def z28 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x0000000fff000000 0x400e3f0000fe0000

def z29 : W := mkw 0x24e879ce24e80000 0xfe3fffedffb7f000 0xffffffffffff8000 0xfe3ffffffffff000

def z30 : W := mkw 0x0020000000000000 0x1000122148000000 0xc7f1800000000000 0xf8127f63cc000000

def z31 : W := mkw 0xc1308052c1309052 0x11001623480c22d2 0xc7f181f00701f1fe 0x1bd24763cd0e33f3

def z32 : W := mkw 0x8000001080001000 0x0000000200080240 0x070001f0070001c0 0x00120043810e0300

def z33 : W := mkw 0x0000000000000000 0x803600c480000000 0xff00000000000000 0xd03e00ff80000000

def z34 : W := mkw 0x0000020100002000 0x0000001000400820 0x00007e0ff8007e30 0x0580000002f00ce0

def z35 : W := mkw 0x000079ce24e80000 0x6600240003b7f000 0x00007fffffff8000 0x0600000003fff000

def z36 : W := mkw 0x48d75ea548d766ac 0xf539f8f877e1ddbd 0xf8fffffff8ffffff 0xfffdf8fc7ff1ffff

def z37 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xffffbe00000e0e01 0xf83ffffffe00cc0c

def z38 : W := mkw 0x08420a0508422224 0x0009081820608828 0x38fe7e0038fe7e0f 0xb52d809c7271cc1c

def z39 : W := mkw 0x1200672912006900 0x80b600d483520d20 0x38003e0038000e00 0x002c009c02700c00

def z40 : W := mkw 0xd330e77bd330f952 0xf5b636f7cbdf2ff2 0xfff1fffffff1fffe 0xfffe7fffcfff3ff3

def z41 : W := mkw 0x24e8508000800000 0x983fdbedff005000 0xfffffff000ff8000 0xfe3fffffff01f000

def z42 : W := mkw 0x24e8000000000000 0x1809db297c000000 0x00ff800000000000 0x2801ff007c000000

def z43 : W := mkw 0x0000000000000000 0x803fc90000000000 0x0000000000000000 0xe03fff0000000000

def z44 : W := mkw 0x0000798c24c80000 0x823fc9000332d000 0x00003e00380e0000 0x002d80000270c000

def z45 : W := mkw 0xc1b08052c1309052 0xf530f6e35c8d22d2 0xc7ffc1ffc7f1f1fe 0xfff3ffe3fd8f33f3

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x00f1c1f000f1f1ce 0xbf5040404d013313

def z47 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x0000000000000000 0x0000000000000000

def z48 : W := mkw 0x4130804241308052 0x7500362148852092 0x00f1c1f000f1f1ce 0xbf507f404d013313

def z49 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf80e3e0ff80e0e31 0x40adb8bc32f0ccec

def z50 : W := mkw 0xc1308052c1309052 0x65002603088d22d2 0x0701c1ffc7f1f1fe 0x0fd247438d8f33f3

def z51 : W := mkw 0xd310e77bd330f952 0x6580241203df2ff2 0x00007ffffff1fffe 0x07c0000003ff3ff3

def z52 : W := mkw 0x9285673992057d88 0x80b600d6975a0f65 0xffffffffff007fff 0xddfe00fffffe0fff

def z53 : W := mkw 0x2428000000000000 0x0806030588000000 0x0700000000000000 0x0002070380000000

def z54 : W := mkw 0x08420a0508422224 0x0009081820608828 0x380e3e00380e0e01 0x002d809c3270cc0c

def z55 : W := mkw 0x0085108000850488 0x0000c00014005005 0x00ff800000ff800f 0x2a41c0007c01f01f

def z56 : W := mkw 0x0000000000000000 0x0000000000000000 0x000041ffc7000000 0xc4120000018e0000

def z57 : W := mkw 0x24e8004200200000 0xfc3fffedfc852000 0xffffc1ffc7f18000 0xfe3ffffffd8f3000

def z58 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc700000fc7000030 0x40823f23808e00e0

def z59 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xfff1fffffff1fffe 0xfffe40ffcfff3ff3

def z60 : W := mkw 0x0040000000000000 0x1009182860000000 0xf8fe000000000000 0xf02db8bc70000000

def z61 : W := mkw 0x24a8000000000000 0x8836c3c59c000000 0x0701800000000000 0x081247438c000000

def z62 : W := mkw 0xc1108052c1309052 0x65002402008d22d2 0x000041ffc7f1f1fe 0x07c00000018f33f3

def z63 : W := mkw 0xe5f88052c1309052 0xfd3fffeffc8d22d2 0xffffc1ffc7f1f1fe 0xfffffffffd8f33f3

def z64 : W := mkw 0x6cda0a0548522224 0xfd3ff9fcf4e188b8 0xf8fe7e0ff8fe7e3f 0xf5adb8bc72f1ccfc

def z65 : W := mkw 0xb6e8653892005900 0x98bfdbefff1a0740 0xffff81f0070001c0 0xf83ffffffd0e0300

def z66 : W := mkw 0x000071ca24a80000 0xe636e50003977000 0x000041ffc7f18000 0xe6127f00018f3000

def z67 : W := mkw 0x24e8000000000000 0x180012edfc000000 0xffff800000000000 0x180000fffc000000

def z68 : W := mkw 0x0080000000000000 0x0000c00014000000 0x00ff800000000000 0x2801c0007c000000

def z69 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xfffe000000000000 0xf02fbfbff0000000

def z70 : W := mkw 0x008554a000854488 0x8036c0c497005505 0xfffffff000ffffcf 0xff7fc0ffff01ff1f

def z71 : W := mkw 0x4852080448520224 0x7509382860a18098 0x00fe000000fe000f 0x2001b8007001c01c

def z72 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00ffbe0000ff8e0f 0x2a61c0807e01fc1f

def z73 : W := mkw 0x24ed7dee24ed4488 0xfe3fffedffb7f505 0xffffffffffffffcf 0xff7fffffffffff1f

def z74 : W := mkw 0x0000214a24280000 0x0206050000162000 0x0000000007000000 0x00020700000e0000

def z75 : W := mkw 0x24ed042000054488 0x983fdbedfc000505 0xffff800000007fcf 0xf97ffffffc000f1f

def z76 : W := mkw 0x0085042000054488 0x000000c014000505 0x000e000000000e01 0x0000008030000c0c

def z77 : W := mkw 0x00857dac24cd4488 0x823fc9c01732d505 0x00fffff038ffffcf 0xbf7dc0c07f71ff1f

def z78 : W := mkw 0x0000020100002000 0x0000001000400820 0xf8007e0ff8007e30 0xd5ac00bc02f00ce0

def z79 : W := mkw 0x000554a000854488 0x8030c00003005505 0x00007ff000ffffcf 0xa771c0000301ff1f

def z80 : W := mkw 0xda527ffffefa7b24 0xf7bffdfee3fffff8 0xfffe7fffffffffff 0xf7bffffff3fffffc

def z81 : W := mkw 0x4010000040100000 0x7500302040810090 0xc0f0400fc0f0703e 0xf5803820408100f0

def z82 : W := mkw 0x0000462100006000 0x803000d003400d20 0xf8007ffff8007ff0 0xd5bc00fc03f00fe0

def z83 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffffc1f000f1f1ce 0xff7ffffffd013313

def z84 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x000e3e00000e0e01 0x002180803200cc0c

def z85 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x000e7fffffff8e01 0xe63fff8033fffc0c

def z86 : W := mkw 0x000079ce24e80000 0xe636e50003b7f000 0x00007fffffff8000 0x0612470003fff000

def z87 : W := mkw 0xc0100010c0101000 0x75003022408902d0 0xc7f041ffc7f071fe 0xf5923863c18f03f0

def z88 : W := mkw 0x0000652800004000 0x803600c003120500 0x00007fffff007fc0 0xd53e00c003fe0f00

def z89 : W := mkw 0xc1108010c1109052 0x01000002000802d2 0x00000000000071fe 0x01c00000000003f3

def z90 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf800000ff8000030 0x408c383c00f000e0

def z91 : W := mkw 0x9200673992007900 0x00800012035a0f60 0x00007fffff007ff0 0x0580000003fe0fe0

def z92 : W := mkw 0x24c8000000000000 0x883fc9ccb4000000 0x380e000000000000 0x002d809c30000000

def z93 : W := mkw 0x0000000000000000 0x0000000000000000 0x00007e0000007e00 0x9520008002000c00

def z94 : W := mkw 0xda526f3dda527b24 0xf5bf38fee3fb8ff8 0xfffe7ffffffe7fff 0xf5bfb8fff3ffcffc

def z95 : W := mkw 0x4130804241308052 0x7500362148852092 0x00f1800000f1800e 0x2a407f004c013013

def z96 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xfff1800000000000 0xf81e7f7fcc000000

def z97 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0x07ff800000000000 0x2813ff43fc000000

def z98 : W := mkw 0x48d75ca448d746ac 0xf539f8e877a1d59d 0x00fffff000ffffcf 0xbf71f8c07f01ff1f

def z99 : W := mkw 0x0000508000800000 0x8030c00003005000 0x00fe7ff000fffe0f 0xb731c0807301fc1c

def z100 : W := mkw 0x0000000000000000 0x0000000000000000 0x00fe7e0000fe7e0f 0xb52180807201cc1c

def z101 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff0001ffff0001f0 0x409e007f81fe03e0

def z102 : W := mkw 0x0000442000004000 0x803000c003000500 0x00007ff000007fc0 0x953000c003000f00

def z103 : W := mkw 0x00007dee24e84000 0xe63fedc003b7f500 0x00007fffffffffc0 0xf73fffc003ffff00

def z104 : W := mkw 0x48d71a8548d726ac 0x7509f83874e1d8bd 0xf8fffe0ff8fffe3f 0xffedf8bc7ef1fcff

def z105 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0x38007fffff007ff0 0x05ac009c03fe0fe0

def z106 : W := mkw 0xda526739da127b24 0x91b610fee35a0ff8 0xfffe7fffff007fff 0xd5be00fff3fe0ffc

def z107 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x000e7ff000ff8e01 0xa631c0803301fc0c

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0x00007e0000fe7e0f 0x050000000201cc1c

def z109 : W := mkw 0xfefa6f3dda527b24 0xfdbffbfffffb8ff8 0xfffffffffffe7fff 0xfdbfffffffffcffc

def z110 : W := mkw 0x008554e200a54488 0xe430e4c017857505 0x00ffffffc7ffffcf 0xff73ffc07f8fff1f

def z111 : W := mkw 0x92007fbdb6c87900 0x82bfc9d6837adf60 0xff007fffff0e7ff0 0xd5bf80ff83fecfe0

def z112 : W := mkw 0x0080000000000000 0x8030c0c014000000 0x00ff800000000000 0xb831c0c07c000000

def z113 : W := mkw 0x9200673992007900 0x00860016835a0f60 0xff007fffff007ff0 0x458e003f83fe0fe0

def z114 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x000181f0000181c0 0x0a5040400d003303

def z115 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xff01ffffff01fff0 0xdffe40ff8ffe3fe3

def z116 : W := mkw 0x48522b4f6c7a2224 0x770f3d3860f7a8b8 0xf8fe7e0ffffe7e3f 0xf5afbfbc72ffccfc

def z117 : W := mkw 0xda522b1dda523b24 0x758f383ee0fb8af8 0xfffe7e0ffffe7e3f 0xf5afb8bff2ffccfc

def z118 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00f1fffffffff1ce 0xff7fff404ffff313

def z119 : W := mkw 0xc9728a57c972b276 0x75093e3b68edaafa 0xff00000fff000030 0x408e3f3f80fe00e0

def z120 : W := mkw 0x0085042000054488 0x000000c014000505 0x00ff800000007fcf 0x194000c07c000f1f

def z121 : W := mkw 0x0040000000000000 0x1000102860000000 0xf8fe000000000000 0x100000bc70000000

def z122 : W := mkw 0x008575a800854488 0x8036c0c017125505 0x00ffffffffffffcf 0xff7fc0c07fffff1f

def z123 : W := mkw 0x24ed108000850488 0x1809db297c005005 0x00ff800000ff800f 0x2a41ff007c01f01f

def z124 : W := mkw 0x24cd54a000854488 0x883fc9ccb7005505 0x380e3e00000e0e01 0x002d809c3200cc0c

def z125 : W := mkw 0x24ed108000850488 0x983fdbedfc005005 0xffff800000ff800f 0xfa7ffffffc01f01f

def z126 : W := mkw 0x4010000040100000 0x6500200000810090 0x0000400fc0f0703e 0x05800000008100f0

def z127 : W := mkw 0x48520a0548522224 0xf53f38fce0e188b8 0xfffe7e0ff8fe7e3f 0xf5bfb8fff2f1ccfc

def z128 : W := mkw 0x8120805281209052 0x00000603080c2242 0x070181f0070181c0 0x0a5247438d0e3303

def z129 : W := mkw 0x9200063192007900 0x008000d680480f60 0xff00000000007ff0 0x118000ff80000fe0

def z130 : W := mkw 0x9280673992007900 0x80b6c0d6975a0f60 0xffffffffff007ff0 0xfdbfc0fffffe0fe0

def z131 : W := mkw 0x2cea0a0508422224 0x983fdbfdfc608828 0xffffbe00380e0e01 0xf83ffffffe70cc0c

def z132 : W := mkw 0x920077b992807900 0x80b6c0d6835a5f60 0xff007ffffffffff0 0xf7bfc0ff83ffffe0

def z133 : W := mkw 0x4010004240300000 0x7500342040852090 0xc0f041ffc7f1f03e 0xf7927f20418f30f0

def z134 : W := mkw 0x000554a000854488 0x0000000003005505 0x00007ff000ffffcf 0x074000000301ff1f

def z135 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z136 : W := mkw 0x1200230912002900 0x0086001480520820 0x3800000038000000 0x000c001c00700000

def z137 : W := mkw 0xb6e8063192007900 0x188012fffc480f60 0xffff800000007ff0 0x198000fffc000fe0

def z138 : W := mkw 0x0000718824880000 0x8236c10003125000 0x0000000000000000 0x0000000000000000

def z139 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xfffffe0000fe7e0f 0xfd3ffffffe01cc1c

def z140 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x000041fffff18000 0xe61e7f0001ff3000

def z141 : W := mkw 0x0080000000000000 0x8030c0c014000000 0x00fffe0000fe7e0f 0xbd31c0c07e01cc1c

def z142 : W := mkw 0x24e8000000000000 0x1809db297c000000 0xc7ff800000000000 0xf813ff63fc000000

def z143 : W := mkw 0x00057dee24ed4488 0x6600240003b7f505 0x00007fffffffffcf 0x0740000003ffff1f

def z144 : W := mkw 0x008554a000854488 0x000000c017005505 0x00fffff000ffffcf 0x1f4000c07f01ff1f

def z145 : W := mkw 0x24e8798c24c80000 0x9a3fdbedff32d000 0xffffbe00380e0000 0xf83ffffffe70c000

def z146 : W := mkw 0xb6e8673992007900 0x98bfdbffff5a0f60 0xffffffffff007ff0 0xfdbffffffffe0fe0

def z147 : W := mkw 0xb6a8653892005900 0x88b6c3c79f1a0740 0x070181f0070001c0 0x081247438d0e0300

def z148 : W := mkw 0x00007bcf24e82000 0xe63fed1003f7f820 0xf8007ffffffffe30 0xf7bfffbc03fffce0

def z149 : W := mkw 0x9200063192007900 0x80b600d680480f60 0xff00000000007ff0 0xd1be00ff80000fe0

def z150 : W := mkw 0x24e8000000000000 0x1809dbedfc000000 0xffff800000000000 0x3801fffffc000000

def z151 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00fe7ffffffffe0f 0xf73fff8073fffc1c

def z152 : W := mkw 0xc130d0d2c1b09052 0xf530f6234b8d72d2 0xc7f1ffffc7fff1fe 0xfff3ff63cf8ff3f3

def z153 : W := mkw 0x000071ca24a80000 0x8236c50003167000 0x000001f007018000 0x02124700010e3000

def z154 : W := mkw 0x8000443080005000 0x803000c203080740 0xc7007fffc7007ff0 0xd5b200e3838e0fe0

def z155 : W := mkw 0x0000798c24c80000 0x823fc9000332d000 0x00003e00380e0000 0xe03fff000270c000

def z156 : W := mkw 0x0120804201208052 0x0000060108042002 0x0001800000018000 0x0a4047000c003003

def z157 : W := mkw 0x6cfa0a0548522224 0xfd3ffbfdfce188b8 0xfffffe0ff8fe7e3f 0xfdbffffffef1ccfc

def z158 : W := mkw 0x246879ce24e80000 0xfe3fff2debb7f000 0xff007fffffff8000 0xe63fff3f83fff000

def z159 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x000001ffff018000 0x421e7f0001fe3000

def z160 : W := mkw 0x0000000000000000 0x0000000000000000 0x00f0400000f0700e 0xb500000040010010

def z161 : W := mkw 0x92007fffb6e87900 0xe6bfedd683ffff60 0xff007ffffffffff0 0xf7bfffff83ffffe0

def z162 : W := mkw 0x24e818c624e80000 0xfe3fffedfca5f000 0xffff800000ff8000 0xfa3ffffffc01f000

def z163 : W := mkw 0x9200231992003900 0x80b600d6805a0a60 0xff00000fff000030 0xd0be00ff80fe00e0

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0x00fffff000ffffcf 0xbf71c0c07f01ff1f

def z165 : W := mkw 0xd330fffff7f8f952 0xf7bffff7cbfffff2 0xfff1fffffffffffe 0xffffffffcffffff3

def z166 : W := mkw 0x24ad54a000854488 0x8836c3c59f005505 0x070181f0000181c0 0x0a5247438d003303

def z167 : W := mkw 0xe5788052c1309052 0x7d0f3f2fe88d22d2 0xfff1c1ffc7f1f1fe 0xffde7f7fcd8f33f3

def z168 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc70181ffc70181f0 0x4ad27f638d8e33e3

def z169 : W := mkw 0x4852080448520224 0x7509382860a18098 0x0000000000000000 0x0000380000000000

def z170 : W := mkw 0x000079ce24e80000 0xe63fedc483b7f000 0xff007fffffff8000 0xf63fffff83fff000

def z171 : W := mkw 0xc110f9dee5f89052 0xe73fed0203bff2d2 0x00007ffffffff1fe 0xe7ffff0003fff3f3

def z172 : W := mkw 0x24e818c624e80000 0x7e09ff297ca5f000 0x00ff800000ff8000 0x2a01ff007c01f000

def z173 : W := mkw 0x4110804241308052 0x6500240000852092 0x0000000000f1800e 0x0240000000013013

def z174 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f0400fc7f0703e 0xf5823f23c08f00f0

def z175 : W := mkw 0x48527bcf6cfa2224 0xf73ffd3863f7f8b8 0xf8007fffffff8030 0xe6bfff3c03fff0e0

def z176 : W := mkw 0x0000210800000000 0x0006000000120000 0x0000000fff000000 0x400e000000fe0000

def z177 : W := mkw 0xe5f8f9dee5f89052 0xff3fffefffbff2d2 0xfffffffffffff1fe 0xfffffffffffff3f3

def z178 : W := mkw 0xd330e739d310f952 0x91b612f7cb5a0ff2 0xfff1ffffff007ffe 0xddfe00ffcffe0ff3

def z179 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x00007e0ffffe0000 0xe42fbf0002ffc000

def z180 : W := mkw 0x00857dac24cd4488 0x823fc9c01732d505 0x000e3e00380e0e01 0x002d80803270cc0c

def z181 : W := mkw 0xc1308010c1109052 0x11001223480802d2 0xc700000000000030 0x00800023800000e0

def z182 : W := mkw 0x24c8000000000000 0x080000ccb4000000 0x380e000000000000 0x0000009c30000000

def z183 : W := mkw 0x0000004200200000 0x6400240000852000 0x000041ffc7f18000 0xe6127f00018f3000

def z184 : W := mkw 0x0000610800000000 0x8036000003120000 0x00007fffff000000 0xc43e000003fe0000

def z185 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xff0e7fffff0e7ff1 0xd5bf80ffb3fecfec

def z186 : W := mkw 0x0000000000000000 0x803600c480000000 0x3800000000000000 0x002c009c00000000

def z187 : W := mkw 0x08020a0508422224 0x0000001000608828 0x00003e00380e0e01 0x000000000270cc0c

def z188 : W := mkw 0x48520a0548522224 0x6509281820e188b8 0x380e7e0ff8fe7e3f 0x05ad809c32f1ccfc

def z189 : W := mkw 0x008556a100856488 0x8030c0d017405d25 0xf8fffffff8ffffff 0xfffdc0fc7ff1ffff

def z190 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00f1c1f000f1f1ce 0xbf5040404d013313

def z191 : W := mkw 0x000554a000854488 0x0000000003005505 0x000001f0000181c0 0x0240000001003303

def z192 : W := mkw 0xc1108052c1309052 0x65002402008d22d2 0x00f1c1ffc7f1f1fe 0xbfd040404d8f33f3

def z193 : W := mkw 0x08420a0508422224 0x0009081820608828 0xf80e7e0ff80e7e31 0xd5ad80bc32f0ccec

def z194 : W := mkw 0x08420a0508422224 0x0009081820608828 0x3800000038000000 0x000c001c00700000

def z195 : W := mkw 0x24c879ce24e80000 0xee3fedccb7b7f000 0x380e7fffffff8000 0xe63fff9c33fff000

def z196 : W := mkw 0x08420a0508422224 0x1009183860608828 0xf8fe3e00380e0e01 0xf02db8bc7270cc0c

def z197 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8007e0ff8fe0030 0xe4adb83c02f1c0e0

def z198 : W := mkw 0xb6e87fffb6e87900 0xfebfffffffffff60 0xfffffffffffffff0 0xffbfffffffffffe0

def z199 : W := mkw 0x0020000000000000 0x1000122148000000 0xc700000000000000 0x40023f2380000000

def z200 : W := mkw 0x9200273992007900 0x008600d6805a0f60 0xff00000fff007ff0 0x518e00ff80fe0fe0

def z201 : W := mkw 0x000018c624e80000 0x6609ed0000a5f000 0x0000000000ff8000 0x2201ff000001f000

def z202 : W := mkw 0x0085042000054488 0x000000c014000505 0x00ffc1f000f1ffcf 0xbf5040c07d013f1f

def z203 : W := mkw 0x24e8442000004000 0x983fdbedff000500 0xfffffff000007fc0 0xfd3fffffff000f00

def z204 : W := mkw 0x0000718800800000 0x8036c00003125000 0x00007fffffff8000 0xe63fc00003fff000

def z205 : W := mkw 0x9285063192057d88 0x008000d694480f65 0xffff800000007fff 0x19c000fffc000fff

def z206 : W := mkw 0x000018c624e80000 0x6609ed0000a5f000 0x000041ffc7ff8000 0xe613ff00018ff000

def z207 : W := mkw 0x008579ce24ed0488 0xe63fed0017b7f005 0x00ffffffffff800f 0xee7fff007ffff01f

def z208 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff003e0fff000e30 0x40ae00bf82fe0ce0

def z209 : W := mkw 0xc1308010c1109052 0x11001223480802d2 0xc7f1c1f000f1f1fe 0xbfd04063cd0133f3

def z210 : W := mkw 0x0000000000000000 0x0000000000000000 0x000e3e00000e0e01 0x002180803200cc0c

def z211 : W := mkw 0xb6ed77b992857d88 0x98bfdbffff5a5f65 0xffffffffffffffff 0xffffffffffffffff

def z212 : W := mkw 0x928575b892855d88 0x80b6c0c6971a5745 0x070181f0070181c0 0x0a5240438d0e3303

def z213 : W := mkw 0x1200652812004900 0x80b600c483120500 0x0000000000000000 0x0000000000000000

def z214 : W := mkw 0xd2106739d2107900 0xf5b630f6c3db0ff0 0xfff07ffffff07ffe 0xf5be38ffc3ff0ff0

def z215 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0x38ff800000000000 0x282dff9c7c000000

def z216 : W := mkw 0x0000610800000000 0x803600c483120000 0xff007fffff000000 0xd43e00ff83fe0000

def z217 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x000fbff0000f8fc1 0x0a71c0c03f00ff0f

def z218 : W := mkw 0xc9728211c912b276 0x1100123b68480afa 0xffff800000007fff 0x19c000fffc000fff

def z219 : W := mkw 0x0040000000000000 0x903fd92860000000 0xf8fe000000000000 0xf03fffbc70000000

def z220 : W := mkw 0x8120805281209052 0x10001623480c2242 0xc7f181f0070181c0 0xfa527f63cd0e3303

def z221 : W := mkw 0x0000000000000000 0x6400200000810000 0x0000400fc0f00000 0xe400380000810000

def z222 : W := mkw 0x0040000000000000 0x1009182860000000 0x00fe000000000000 0x2001b80070000000

def z223 : W := mkw 0x0000610800000000 0x803fc90003120000 0x00007fffff000000 0xe43fff0003fe0000

def z224 : W := mkw 0x008518c624ed0488 0x6609ed0014a5f005 0x00ff800000ff800f 0x2a41ff007c01f01f

def z225 : W := mkw 0xc130f9dee5f89052 0xf73fff234bbff2d2 0xc7f1fffffffff1fe 0xffffff63cffff3f3

def z226 : W := mkw 0x48d77fef6cff66ac 0xf73ffdf877f7fdbd 0xf8ffffffffffffff 0xfffffffc7fffffff

def z227 : W := mkw 0x0080000000000000 0x8030c0c014000000 0x000e000000000000 0x0021808030000000

def z228 : W := mkw 0x1200672912006900 0x0080001003520d20 0x00003e0038000e00 0x0000000002700c00

def z229 : W := mkw 0x65f8804241308052 0x7d09ff297c852092 0x00ff800000f1800e 0x2a41ff007c013013

def z230 : W := mkw 0x4130804241308052 0x7500362148852092 0xc0f1c00fc0f1f03e 0xffc07f204c8130f3

def z231 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8007e0ff8fe7e3f 0x458c383c02f1ccfc

def z232 : W := mkw 0x000039ce24e80000 0x660fed0000b7f000 0x0000000fffff8000 0x620fff0000fff000

def z233 : W := mkw 0x0080000000000000 0x000000c014000000 0x00ff800000000000 0x180000c07c000000

def z234 : W := mkw 0x92857fffb6ed7d88 0xe6bfedd697ffff65 0xffffffffffffffff 0xffffffffffffffff

def z235 : W := mkw 0x128577a912856d88 0x80b6c0d497525d25 0x380e3e00380e0e01 0x002d809c3270cc0c

def z236 : W := mkw 0x24a8000000000000 0x0800c3011c000000 0x0001800000000000 0x080047000c000000

def z237 : W := mkw 0x0000020100002000 0x0000001000400820 0xf8fe7e0ff8fe7e3f 0xf5ad80bc72f1ccfc

def z238 : W := mkw 0x0000004200200000 0x6400240000852000 0x00f1c1ffc7f1f1ce 0xff527f404d8f3313

def z239 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe000000fe7e3f 0x3181b8bc7001ccfc

def z240 : W := mkw 0x000554a000854488 0x0000000003005505 0x00003e00000e0e01 0x000000000200cc0c

def z241 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7ffffffc7ffffff 0xfff3ffe3ff8fffff

def z242 : W := mkw 0x0020000000000000 0x0000020108000000 0x0701800000000000 0x081247438c000000

def z243 : W := mkw 0x48127bcf6cfa2224 0xe73fed1003f7f8b8 0x00007ffffffffe3f 0xe7bfff0003fffcfc

def z244 : W := mkw 0x000554a000854488 0x803000c003005505 0x00007ff000ffffcf 0x977000c00301ff1f

def z245 : W := mkw 0x24e8000000000000 0x1809db297c000000 0xf8ff800000000000 0xf82dffbc7c000000

def z246 : W := mkw 0x48520a0548522224 0x7500303860e188b8 0xf8fe7e0ff8fe7e3f 0x158000bc72f1ccfc

def z247 : W := mkw 0x9200043092005900 0x008000c680080740 0x07000000000001c0 0x0000004380000300

def z248 : W := mkw 0x8000001080001000 0x0000000200080240 0xc70041ffc70071f0 0xd5920063818e03e0

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x00fe000000000000 0xb021808070000000

def z250 : W := mkw 0x4010000040100000 0x7500302040810090 0xc0f1c1ffc0f1f1fe 0xffd078604d8133f3

def z251 : W := mkw 0x24e8000000000000 0x9830d2edfc000000 0xffff800000000000 0xb831c0fffc000000

def z252 : W := mkw 0x24ed54a000854488 0x9830d2edff005505 0xfffffff000ffffcf 0xbf71c0ffff01ff1f

def z253 : W := mkw 0x00855ce624ed4488 0xe639edc017a5f505 0x00fffff000ffffcf 0xbf71ffc07f01ff1f

def z254 : W := mkw 0x48520a0548522224 0x11091838606088b8 0xf8fe3e00380e7e3f 0x11ad80bc7270ccfc

def z255 : W := mkw 0x48527b8d6cda2224 0xf73ff93863f3d8b8 0xf8fe7e0ff8fe7e3f 0xf5adb8bc72f1ccfc

def z256 : W := mkw 0xe5fdd4f2c1b5d4da 0xfd3fffefff8d77d7 0xffffffffc7ffffff 0xffffffffff8fffff

def z257 : W := mkw 0x4010000040100000 0x7500302040810090 0x00f0000000f0000e 0x2000380040010010

def z258 : W := mkw 0xd3308631d310f952 0x118012f7c8480ff2 0xfff1800000007ffe 0x19c000ffcc000ff3

def z259 : W := mkw 0x4852020148122224 0x11001038604008b8 0xf8fe7e0000fe7e3f 0xb5a180bc7201ccfc

def z260 : W := mkw 0x0080508000800000 0x8030c0c017005000 0x00fffff000ff8000 0xbe31c0c07f01f000

def z261 : W := mkw 0x0000000000000000 0x0000000000000000 0x00007e0ff8000000 0xc42c000002f00000

def z262 : W := mkw 0xc1308010c1109052 0x75003223488902d2 0xc7f1c00fc0f071fe 0xfdc03863cc8103f3

def z263 : W := mkw 0x0000188424c80000 0x0209c9000020d000 0x00000000000e0000 0x000180000000c000

def z264 : W := mkw 0x1200062112006900 0x008000d480400d20 0x3800000000000e00 0x0000009c00000c00

def z265 : W := mkw 0x0000000000000000 0x0000000000000000 0x00fe000000fe000f 0x200180007001c01c

def z266 : W := mkw 0x000071ca24a80000 0x8236c50003167000 0x00007ff007ff8000 0xa633c700030ff000

def z267 : W := mkw 0x2468000000000000 0x18091b2968000000 0x0000000000000000 0x00003f0000000000

def z268 : W := mkw 0x2488000000000000 0x8836c1c494000000 0x0000000000000000 0x0000000000000000

def z269 : W := mkw 0xda526f3dda527b24 0x7589383a63fb8ff8 0xf8fe7ffffffe7fff 0xf5adb8bc73ffcffc

def z270 : W := mkw 0x000079ce24e80000 0x6609ed0003b7f000 0x00007fffffff8000 0x2601ff0003fff000

def z271 : W := mkw 0x000079ce24e80000 0xe630e40003b7f000 0x00007fffffff8000 0xa631c00003fff000

def z272 : W := mkw 0x9200653892005900 0x80b600c6831a0740 0x07007ff007007fc0 0x953200c3830e0f00

def z273 : W := mkw 0x24c8000000000000 0x983fd9ecf4000000 0xf8fe000000000000 0xf02db8bc70000000

def z274 : W := mkw 0x0842020108022224 0x0000001820400828 0x380e000000000e01 0x0000009c30000c0c

def z275 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8007e0ff8007e30 0xd5ac38bc02f00ce0

def z276 : W := mkw 0xc9728a57c972b276 0x75093e3b68edaafa 0xfffe7e0ffffe7e3f 0xf5afbfbff2ffccfc

def z277 : W := mkw 0x2468000000000000 0x983fdb2de8000000 0xff00000000000000 0xe03fff3f80000000

def z278 : W := mkw 0x0000798c24c80000 0x020000000332d000 0x00003e00380e0000 0x000000000270c000

def z279 : W := mkw 0x0020000000000000 0x1000122148000000 0xc7f1800000000000 0x18000063cc000000

def z280 : W := mkw 0xb6e8063192007900 0x98bfdbfffc480f60 0xffff800000007ff0 0xf9bffffffc000fe0

def z281 : W := mkw 0x48527bcf6cfa2224 0xf73ffd3863f7f8b8 0xf8fe7ffffffffe3f 0xf7bfffbc73fffcfc

def z282 : W := mkw 0x24a871ca24a80000 0x8a36c7c59f167000 0x070181f007018000 0x0a1247438d0e3000

def z283 : W := mkw 0x92007fffb6e87900 0x6680241203ffff60 0x00007ffffffffff0 0x0780000003ffffe0

def z284 : W := mkw 0x004079ce24e80000 0xf63ffd2863b7f000 0xf8fe7fffffff8000 0xf63fffbc73fff000

def z285 : W := mkw 0x4852020148122224 0x7500303860c108b8 0xf8fe400fc0f07e3f 0xf58038bc70810cfc

def z286 : W := mkw 0x0000000000000000 0x0006000480000000 0xff00000000000000 0x400e003f80000000

def z287 : W := mkw 0x8120805281209052 0x00000603080c2242 0x0700000007000000 0x00020703800e0000

def z288 : W := mkw 0x0000000000000000 0x0000000000000000 0x00f18000000071ce 0x194000404c000313

def z289 : W := mkw 0xc1108052c1309052 0x65002402008d22d2 0x000041ffc7f1f1fe 0xe7d27f00018f33f3

def z290 : W := mkw 0x9200021192003900 0x0080001680480a60 0xff00000000000030 0x0080003f800000e0

def z291 : W := mkw 0x4852020148122224 0x11091838604008b8 0xf8fe000000007e3f 0xf1adb8bc70000cfc

def z292 : W := mkw 0xc195d4f2c1b5d4da 0xe530e4c2178d77d7 0x00ffffffc7ffffff 0xbff1c0c07f8fffff

def z293 : W := mkw 0x0000614a00200000 0xe436240003972000 0x00007ffffff18000 0xe63e7f0003ff3000

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0x00f1800000000000 0xb81040404c000000

def z295 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f1800fc7000030 0xf8927f63cc8e00e0

def z296 : W := mkw 0x0000000000000000 0x1000102040000000 0xc0f0000000000000 0xf000382040000000

def z297 : W := mkw 0x48520a4748722224 0x75093c3860e5a8b8 0xf8fe7ffffffffe3f 0xf7bfffbc73fffcfc

def z298 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xfffe7ffffffe7fff 0xf5bf80fff3ffcffc

def z299 : W := mkw 0x0000690c00400000 0xe43f280003b38000 0x00007ffffffe0000 0xe43fb80003ffc000

def z300 : W := mkw 0x24a8000000000000 0x080002c59c000000 0x0701800000000000 0x080000438c000000

def z301 : W := mkw 0x0060000000000000 0x10091a2968000000 0xffff800000000000 0xf83ffffffc000000

def z302 : W := mkw 0x24e8000000000000 0x18091aedfc000000 0xffff800000000000 0xf82db8fffc000000

def z303 : W := mkw 0x24e8610800000000 0x983fdbedff120000 0xffffffffff000000 0xfc3ffffffffe0000

def z304 : W := mkw 0x000071ca24a80000 0x823fcd0003167000 0x000001f007018000 0xe23fff00010e3000

def z305 : W := mkw 0xb6c8673992007900 0x88bfc9deb75a0f60 0xff0e7fffff007ff0 0xd5bf80ffb3fe0fe0

def z306 : W := mkw 0x0005042000054488 0x0000000000000505 0x0000000000007fcf 0x0140000000000f1f

def z307 : W := mkw 0x48526b0d48522224 0xf53f383863f388b8 0xf8fe7ffffffe7e3f 0xf5bfb8bc73ffccfc

def z308 : W := mkw 0xda126f3dda527b24 0x6580201203fb8ff8 0x00007ffffffe7fff 0x0580000003ffcffc

def z309 : W := mkw 0x0080000000000000 0x803fc9c014000000 0x00ff800000000000 0xf83fffc07c000000

def z310 : W := mkw 0x0000000000000000 0x8036000000000000 0x0000000000000000 0xc03e000000000000

def z311 : W := mkw 0x48120a0548522224 0x6509281000e188b8 0x00007e0ff8fe7e3f 0xe5adb80002f1ccfc

def z312 : W := mkw 0x0020000000000000 0x1000122148000000 0x00f1800000000000 0x28007f004c000000

def z313 : W := mkw 0x0000290c24480000 0x020f090000328000 0x0000000038000000 0x000c000000700000

def z314 : W := mkw 0x000079ce24e80000 0x66092c0003b7f000 0x00007fffffff8000 0xe62db80003fff000

def z315 : W := mkw 0x9200653892005900 0x80b600c6831a0740 0xff0001f0070001c0 0xd03e00ff810e0300

def z316 : W := mkw 0x0085108000850488 0x0000c00014005005 0x00ffc1f000fff1cf 0xbf51c0407d01f31f

def z317 : W := mkw 0x0085000000050488 0x0000000014000005 0x00ff80000000000f 0x084000007c00001f

def z318 : W := mkw 0x0080000000000000 0x8030c0c014000000 0x00ffc1f000f1f1ce 0xbf71c0c07d013313

def z319 : W := mkw 0x49728a474972a276 0x75093e3968e5a8ba 0xf8fffe0ff8fffe3f 0xffedffbc7ef1fcff

def z320 : W := mkw 0x48120a0548522224 0x6500201000e188b8 0x00fe7e0ff8fe7e3f 0xb5a1808072f1ccfc

def z321 : W := mkw 0x2468000000000000 0x983f1bede8000000 0xff00000000000000 0xd03e3fff80000000

def z322 : W := mkw 0x92006f7fb6687900 0xe6bf2dd683ffaf60 0xff007fffff007ff0 0xd5be3fff83fe0fe0

def z323 : W := mkw 0x00000a0500402000 0x6409281000e18820 0xf8007e0ff8fe7e30 0xf5adb8bc02f1cce0

def z324 : W := mkw 0x8000611880001000 0x80360002031a0240 0xc7007fffff0071f0 0xd5be006383fe03e0

def z325 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fffffff8ffffff 0xfffdf8fc7ff1ffff

def z326 : W := mkw 0x41b590c241b584da 0x7500f6215c857097 0x00ff800000ff800f 0x2a41ff007c01f01f

def z327 : W := mkw 0x0000080400400000 0xe43fe90000a18000 0x00007e0ff8fe0000 0xe43fff0002f1c000

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0xe0127f0000000000

def z329 : W := mkw 0x000554a000854488 0x0000000003005505 0x00f1fff000ffffcf 0xbf5040404f01ff1f

def z330 : W := mkw 0x0000610800000000 0x0000000003120000 0x00007fffff000000 0x0400000003fe0000

def z331 : W := mkw 0x4130800041108052 0x1100122148000092 0x00f180000000000e 0x084000004c000013

def z332 : W := mkw 0x401079ce64f80000 0xf73ffd2043b7f090 0xc0f07ffffffff03e 0xf7bfff2043fff0f0

def z333 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00fe7e0000fe7e0f 0xb52180807201cc1c

def z334 : W := mkw 0x8120805281209052 0x64002603088d2242 0x0701c1ffc7f181c0 0xee527f438d8f3303

def z335 : W := mkw 0x0085508000850488 0x8030c00017005005 0x00fffff000ff800f 0xae71c0007f01f01f

def z336 : W := mkw 0x48120a0548522224 0x6500201000e188b8 0x0000000ff8000030 0x0080000000f000e0

def z337 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f1800fc7f1803e 0x6ac27f23cc8f30f3

def z338 : W := mkw 0x9240673992007900 0x90bf18fee35a0f60 0xfffe7fffff007ff0 0xf5bfb8fff3fe0fe0

def z339 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f1c1ffc7f1f1fe 0x1fc00063cd8f33f3

def z340 : W := mkw 0xda520e35da527b24 0x758938fee0e98ff8 0xfffe7e0ff8fe7fff 0xf5adb8fff2f1cffc

def z341 : W := mkw 0x4852080448520224 0x7509382860a18098 0x00fe7e0ff8fe000f 0xe42db80072f1c01c

def z342 : W := mkw 0xc9328a57c972b276 0x7500363348edaafa 0xc7f1ffffffffffff 0xffd27f63cfffffff

def z343 : W := mkw 0x0020000000000000 0x903612e5c8000000 0xfff1800000000000 0xf83e7fffcc000000

def z344 : W := mkw 0x65f8804241308052 0xfd3fffedfc852092 0xffff800000f1800e 0xfa7ffffffc013013

def z345 : W := mkw 0xb6e8231992003900 0x98bfdbfffc5a0a60 0xffff800fff000030 0xf8bffffffcfe00e0

def z346 : W := mkw 0x1200672912006900 0x80b600d483520d20 0x38007ff038007fc0 0x953c00dc03700f00

def z347 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc70041ffc7f18030 0xe6927f23818f30e0

def z348 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f1800000f1f1fe 0x3bc07f63cc0133f3

def z349 : W := mkw 0x00c0000000000000 0x9039d8e874000000 0xf8ff800000000000 0xf83df8fc7c000000

def z350 : W := mkw 0x0000000000000000 0x0000000000000000 0x00f1800000f1800e 0x2a4040004c013013

def z351 : W := mkw 0xc1b590d2c1b594da 0x7500f6235c8d72d7 0xc7ffc1ffc7fff1ff 0xffd3ff63fd8ff3ff

def z352 : W := mkw 0xda522b1dda523b24 0x758f383ee0fb8af8 0xff00000fff000030 0x408e383f80fe00e0

def z353 : W := mkw 0x000018c624e80000 0x6609ed0000a5f000 0x00007e0ff8ff8000 0xe62dff0002f1f000

def z354 : W := mkw 0x9200673992007900 0x80b60012035a0f60 0x00007fffff007ff0 0xc5be000003fe0fe0

def z355 : W := mkw 0x48d75ea548d766ac 0xf539f8f877e1ddbd 0xf8fe7e0ff8fe7e3f 0xf5adb8bc72f1ccfc

def z356 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x0001ffffffff81c0 0xee7fff400ffff303

def z357 : W := mkw 0x24e8000000000000 0x9839dbe97c000000 0x00ff800000000000 0xb831ffc07c000000

def z358 : W := mkw 0x48127bcf6cfa2224 0x6700241003f7f8b8 0x00007ffffffffe3f 0x0780000003fffcfc

def z359 : W := mkw 0x0040000000000000 0x1009182860000000 0xf800000000000000 0x400c383c00000000

def z360 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff007e0fff007e30 0xd5ae00bf82fe0ce0

def z361 : W := mkw 0x008079ce24e80000 0xe63fedc017b7f000 0x00ffffffffff8000 0xfe3fffc07ffff000

def z362 : W := mkw 0xc9f7def7c9f7f6fe 0xf539fefb7fedffff 0xffffffffffffffff 0xffffffffffffffff

def z363 : W := mkw 0x8000021180003000 0x0000001200480a60 0xff007fffff007ff0 0xd5be00ff83fe0fe0

def z364 : W := mkw 0x6cfa0a0548522224 0x7d093afdfce188b8 0xfffffe0ff8fe7e3f 0xfdadb8fffef1ccfc

def z365 : W := mkw 0xc1b5fdfee5fdd4da 0xf73fffe35fbff7d7 0xc7ffffffffffffff 0xffffffe3ffffffff

def z366 : W := mkw 0x9200673992007900 0x80b000d2035a0f60 0x00007fffff007ff0 0x95b000c003fe0fe0

def z367 : W := mkw 0x8000001080001000 0x0000000200080240 0xc7f1c1ffc7f1f1fe 0xffd24063cd8f33f3

def z368 : W := mkw 0x0000084600600000 0x64092c0000a5a000 0x00007fffffff8000 0xe63fff0003fff000

def z369 : W := mkw 0xc972fbdfedfab276 0xf73fff3b6bfffafa 0xffffffffffffffff 0xffffffffffffffff

def z370 : W := mkw 0xc1308052c1309052 0xf53fff23488d22d2 0xc7f1c1ffc7f1f1fe 0xffffff63cd8f33f3

def z371 : W := mkw 0x92007bdfb6e83900 0xe6bfed1683fffa60 0xff007fffffff8030 0xe6bfff3f83fff0e0

def z372 : W := mkw 0x9320e77b9320f952 0x80b606d78b5e2f62 0xff01ffffff01fff0 0xdffe47ff8ffe3fe3

def z373 : W := mkw 0x4130804241308052 0x7500362148852092 0x0000000000000000 0x00003f0000000000

def z374 : W := mkw 0x0000610800000000 0x8036000003120000 0x000001f007000000 0x00120000010e0000

def z375 : W := mkw 0x0085108000850488 0x8030c0c014005005 0x00ff800000ff800f 0xba71c0c07c01f01f

def z376 : W := mkw 0xc8520a15c8523224 0x7509383a60e98af8 0xfffe7ffffffe7fff 0xf5bfb8fff3ffcffc

def z377 : W := mkw 0xc9728a15c952b276 0x75093a3b68e98afa 0xfffffe0ff8fe7fff 0xfdedb8fffef1cfff

def z378 : W := mkw 0x0000442000004000 0x803000c003000500 0x000001f0000001c0 0x0010004001000300

def z379 : W := mkw 0x8000001080001000 0x0000000200080240 0x000041ffc70071f0 0x05800000018e03e0

def z380 : W := mkw 0xd330a35bd330b952 0x75863637c8df2af2 0xff00000fff000030 0x408e3f3f80fe00e0

def z381 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xffff81f0000181c0 0xfa7ffffffd003303

def z382 : W := mkw 0xc1308052c1309052 0xf53636e7c88d22d2 0xfff1c1ffc7f1f1fe 0xfffe7fffcd8f33f3

def z383 : W := mkw 0x12007fef36e86900 0xe6bfedd483f7fd20 0x38007fffffff8e00 0xe63fff9c03fffc00

def z384 : W := mkw 0x0000000000000000 0x000f090000000000 0x0000000000000000 0x400e3f0000000000

def z385 : W := mkw 0x08c75ea508c766ac 0x8039c8d83760dd2d 0x380e3e00380e0e01 0x002d809c3270cc0c

def z386 : W := mkw 0x9200653892005900 0x00800002031a0740 0x000001f0070001c0 0x00000000010e0300

def z387 : W := mkw 0x002079ce24e80000 0xf63fff214bb7f000 0xc7f1ffffffff8000 0xfe3fff63cffff000

def z388 : W := mkw 0x9200653892005900 0x80b600c6831a0740 0xc70041ffc70071f0 0xd5920063818e03e0

def z389 : W := mkw 0x4010080440500000 0x7509382040a18090 0xc0f07e0ff8fe703e 0xf5adb82042f1c0f0

def z390 : W := mkw 0xc1108052c1309052 0x65002402008d22d2 0x0000000fc7000030 0x00800000008e00e0

def z391 : W := mkw 0x000050c200a00000 0xe430e40003857000 0x00007fffc7ff8000 0xe633ff00038ff000

def z392 : W := mkw 0x000018c624e80000 0xe63fed0000a5f000 0x0000000000ff8000 0xe23fff000001f000

def z393 : W := mkw 0x2468294e24680000 0x7e0f3f2de8b7a000 0xff00000fff000000 0x400e3f3f80fe0000

def z394 : W := mkw 0x000054a000804000 0x8030c0c003005500 0x00007ff000ffffc0 0xb731c0c00301ff00

def z395 : W := mkw 0x1200672912006900 0x80b600d483520d20 0x38007fffff000e00 0xc43e009c03fe0c00

def z396 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00007fffffff8000 0x062d800003fff000

def z397 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0x3f003ff03f000fc0 0x003e00df837e0f00

def z398 : W := mkw 0x000071ca24a80000 0x0200040003167000 0x000001f007018000 0x02000000010e3000

def z399 : W := mkw 0x0020000000000000 0x1000122148000000 0xc7f1c1f000f1f1ce 0xff527f63cd013313

def z400 : W := mkw 0x48175ea548d766ac 0x6500201003e1ddbd 0x00007ffff8ffffff 0x07c0000003f1ffff

def z401 : W := mkw 0x0000694e24680000 0xe63f2d0003b7a000 0x00007fffff000000 0xc43e3f0003fe0000

def z402 : W := mkw 0x0000000000000000 0x8036c10000000000 0x0000000000000000 0x0012470000000000

def z403 : W := mkw 0x0000020100002000 0x0000001000400820 0xf800000000007e30 0x118000bc00000ce0

def z404 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x0001fff000ffffcf 0x0f5040400f01ff1f

def z405 : W := mkw 0x4030000040100000 0x7500322148810090 0xc7f1c00fc0f0703e 0xfd927f63cc8100f0

def z406 : W := mkw 0x9200463192007900 0x80b000d683480f60 0xff007ff000007ff0 0x95b000ff83000fe0

def z407 : W := mkw 0x24e8020100002000 0x983fdbfdfc400820 0xfffffe0ff8007e30 0xfdbffffffef00ce0

def z408 : W := mkw 0x0000400000000000 0x8030000003000000 0x00007ff000000000 0x8430000003000000

def z409 : W := mkw 0x0000080400400000 0x6400200000a18000 0x00007e0ff8fe0000 0x0400000002f1c000

def z410 : W := mkw 0x00057dee24ed4488 0xe63fed0003b7f505 0x00007fffffffffcf 0xe77fff0003ffff1f

def z411 : W := mkw 0x0000294e24680000 0xe63fed0000b7a000 0x0000000fff000000 0xe03fff0000fe0000

def z412 : W := mkw 0x4852080448520224 0x7509382860a18098 0xf8fe000000fe000f 0xf02db8bc7001c01c

def z413 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x000e7ff0000e7fc1 0x953180c03300cf0c

def z414 : W := mkw 0xc1308856c1709052 0x75093e2348ada2d2 0xc7f1fffffffff1fe 0xffffff63cffff3f3

def z415 : W := mkw 0xd3308673d330f952 0x758036f7c8cd2ff2 0xfff1c1ffc7f1fffe 0xffd27fffcd8f3ff3

def z416 : W := mkw 0x9200063192007900 0x008000d680480f60 0xff0041ffc7007ff0 0xd59200ff818e0fe0

def z417 : W := mkw 0x48d7188448d706ac 0x7509f82874a1d09d 0x00ff800000ff800f 0x2a41f8007c01f01f

def z418 : W := mkw 0xe5f88052c1309052 0x7d09ff2b7c8d22d2 0xc7ffc1ffc7f1f1fe 0xffd3ff63fd8f33f3

def z419 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x0001fff00001ffc0 0x9f7040c00f003f03

def z420 : W := mkw 0x24e8000000000000 0x180012297c000000 0x00ff800000000000 0x080000007c000000

def z421 : W := mkw 0x920075fab6a85900 0x82b6c5c6831e7740 0x070001f0070181c0 0x02124743810e3300

def z422 : W := mkw 0x000010c224a80000 0x0200c50000047000 0x0000000000018000 0x0200470000003000

def z423 : W := mkw 0x24c8000000000000 0x883fc9ccb4000000 0x380e000000000000 0xe03fff9c30000000

def z424 : W := mkw 0x4972884649728276 0x75093e2968a5a09a 0x00ff800000ff800f 0x2a41ff007c01f01f

def z425 : W := mkw 0x00c554a000854488 0x9039d8e877005505 0xf8fffff000ffffcf 0xff7df8fc7f01ff1f

def z426 : W := mkw 0x48720a0548522224 0x75093a3968e188b8 0xfffffe0ff8fe7e3f 0xfdbffffffef1ccfc

def z427 : W := mkw 0xe5f88010c1109052 0x993fdbeffc0802d2 0xffff8000000071fe 0xf9fffffffc0003f3

def z428 : W := mkw 0x6cfa080448520224 0xfd3ffbedfca18098 0xffff800000fe000f 0xf83ffffffc01c01c

def z429 : W := mkw 0x0842080408420224 0x0009080820208008 0x000e0000000e0001 0x000180003000c00c

def z430 : W := mkw 0x5a526f2d5a526b24 0xf5bf38fce3f38db8 0xf8fe7e0ff8fe7e3f 0xf5adb8bc72f1ccfc

def z431 : W := mkw 0xe5f88052c1309052 0x7d0036effc8d22d2 0xffffc1ffc7f1f1fe 0xffd27ffffd8f33f3

def z432 : W := mkw 0x0085108000850488 0x0000c00014005005 0x00fffe0000fffe0f 0xbf61c0807e01fc1f

def z433 : W := mkw 0x48d70621481766ac 0x110010f874400dbd 0xf8ff800000007fff 0x19c000fc7c000fff

def z434 : W := mkw 0xd330a35bd330b952 0x75863637c8df2af2 0xfff1c1fffff1f1fe 0xffde7f7fcdff33f3

def z435 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff0041ffff0071f0 0xd59e007f81fe03e0

def z436 : W := mkw 0x6c7a0a0548522224 0x7d0f3b3de8e188b8 0xff00000ff8000030 0x408e3f3f80f000e0

def z437 : W := mkw 0x0000000000000000 0x803600c480000000 0x0700000000000000 0x0012004380000000

def z438 : W := mkw 0x4130804241308052 0x7500362148852092 0xc7f1800000f1800e 0xfa527f63cc013013

def z439 : W := mkw 0x9200673992007900 0x00800012035a0f60 0xc7007fffff007ff0 0xd592006383fe0fe0

def z440 : W := mkw 0x1200672912006900 0x80b600d483520d20 0xff003e0038000e00 0xd03e00ff82700c00

def z441 : W := mkw 0x0000080400400000 0x6409280000a18000 0x00fe7e0ff8fe7e0f 0xf52db88072f1cc1c

def z442 : W := mkw 0x0000080400400000 0x6409280000a18000 0x0000000ff8000000 0x400c380000f00000

def z443 : W := mkw 0x1200672912006900 0x80b600d483520d20 0xf8007e0ff8007e30 0xd5ac00bc02f00ce0

def z444 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff0001f007007ff0 0x119200ff810e0fe0

def z445 : W := mkw 0x6cfa0a0548522224 0xfd3ffbfdfce188b8 0xffff800ff8000030 0xf8bffffffcf000e0

def z446 : W := mkw 0x0000004200200000 0xe43fed0000852000 0x000041ffc7f18000 0xe63fff00018f3000

def z447 : W := mkw 0xdb72ef7fdb72fb76 0xf5bf3effebffaffa 0xffffffffffffffff 0xffffffffffffffff

def z448 : W := mkw 0x24a8000000000000 0x8836c3c59c000000 0xff01800000000000 0xd83e47ff8c000000

def z449 : W := mkw 0xc130e15ac1309052 0xf53636234b9f22d2 0xc7f1fffffff1f1fe 0xfffe7f63cfff33f3

def z450 : W := mkw 0x4130804241308052 0x7500362148852092 0x00f1c1ffc7f1800e 0xee527f004d8f3013

def z451 : W := mkw 0x8000001080001000 0x0000000200080240 0xc700000fc7000030 0x40820023808e00e0

def z452 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xff0e000000000000 0x402fbfbfb0000000

def z453 : W := mkw 0x48527bcf6cfa2224 0x77093c3863f7f8b8 0xf8fe7ffffffffe3f 0xf7adb8bc73fffcfc

def z454 : W := mkw 0x24e8294e24680000 0xfe3fffedfcb7a000 0xffff800fff000000 0xf83ffffffcfe0000

def z455 : W := mkw 0x4852080448520224 0x7509382860a18098 0x00fe7e0000fe7e0f 0xb521b8807201cc1c

def z456 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0x38fe3e0038fe0e0f 0x202db89c7271cc1c

def z457 : W := mkw 0x485218c66cfa0224 0x7709fd2860a5f098 0x00fe000000ff800f 0x2201ff007001f01c

def z458 : W := mkw 0x0080000000000000 0x8036c0c494000000 0xffff800000000000 0xf83fc0fffc000000

def z459 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x000001f007ff8000 0x2213ff00010ff000

def z460 : W := mkw 0x4852020148122224 0x11001038604008b8 0xf8fe7e0ff8007e3f 0xd5ac00bc72f00cfc

def z461 : W := mkw 0x0040000000000000 0x0009080820000000 0x380e000000000000 0x002d809c30000000

def z462 : W := mkw 0x8120805281209052 0x00000603080c2242 0x07f1c1f007f1f1ce 0xbf524743cd0f3313

def z463 : W := mkw 0x24c8000000000000 0x883fc9ccb4000000 0x38ff800000000000 0xb83dc0dc7c000000

def z464 : W := mkw 0x6cfa7bcf6cfa2224 0xff3ffffdfff7f8b8 0xfffffffffffffe3f 0xffbffffffffffcfc

def z465 : W := mkw 0x9200677b92207900 0xe4b624d683df2f60 0xff007ffffff1fff0 0xf7be7fff83ff3fe0

def z466 : W := mkw 0xc9128a57c972b276 0x6500241200edaafa 0x00007fffffffffff 0x07c0000003ffffff

def z467 : W := mkw 0x9200063192007900 0x008000d680480f60 0xff007e0ff8007ff0 0xd5ac00ff82f00fe0

def z468 : W := mkw 0x8000001080001000 0x803600c680080240 0xff0041ffc70071f0 0xd5be00ff818e03e0

def z469 : W := mkw 0x920577b992857d88 0x00800012035a5f65 0x00007fffffffffff 0x07c0000003ffffff

def z470 : W := mkw 0x00a0000000000000 0x9030d2e15c000000 0xc7ff800000000000 0xf833ffe3fc000000

def z471 : W := mkw 0xd330e77bd330f952 0x758036334bdf2ff2 0xc7f1fffffff1fffe 0xffd27f63cfff3ff3

def z472 : W := mkw 0x000018c624e80000 0x6600240000a5f000 0x0000000000ff8000 0x020000000001f000

def z473 : W := mkw 0xc1108052c1309052 0x75003422408d22d2 0xc0f041ffc7f1f1fe 0xf7c03820418f33f3

def z474 : W := mkw 0x000079ce24e80000 0x823fcd000336f000 0x00003ff03f0f8000 0x023fc700037ef000

def z475 : W := mkw 0x24c8000000000000 0x0809c90834000000 0x000e000000000000 0x0001800030000000

def z476 : W := mkw 0xc130a95ee5789052 0x770f3f2348bfa2d2 0xc7f1c1fffff1f1fe 0xffde7f63cdff33f3

def z477 : W := mkw 0x0040080400400000 0x7409382860a18000 0xf8fe7e0ff8fe0000 0xf42db8bc72f1c000

def z478 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffff800000000000 0x182d80fffc000000

def z479 : W := mkw 0xb6a8673992007900 0x88b6c3d79f5a0f60 0xff01ffffff007ff0 0xddbe47ff8ffe0fe0

def z480 : W := mkw 0x92007fffb6e87900 0xe6bfed1203ffff60 0x00007ffffffffff0 0xe7bfff0003ffffe0

def z481 : W := mkw 0x0000610800000000 0x8036000003120000 0x00003e0038000000 0x002c000002700000

def z482 : W := mkw 0x0085442000054488 0x803000c017000505 0x00fffff000007fcf 0x9d7000c07f000f1f

def z483 : W := mkw 0x0080442000004000 0x8030c0c017000500 0x00fffff000007fc0 0xbd31c0c07f000f00

def z484 : W := mkw 0x000058c624e80000 0xe639ed0003a5f000 0x00007ff000ff8000 0xa631ff000301f000

def z485 : W := mkw 0xe5f88052c1309052 0xfd3fffeffc8d22d2 0xffff800fc7000030 0xf8bffffffc8e00e0

def z486 : W := mkw 0x6cfa020148122224 0x190012fdfc4008b8 0xffff800000007e3f 0x198000fffc000cfc

def z487 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff003e0038007ff0 0x11ac00ff82700fe0

def z488 : W := mkw 0x008554a000854488 0x803fc9c017005505 0x00fffff000ffffcf 0xff7fffc07f01ff1f

def z489 : W := mkw 0x0000442000004000 0x803000c003000500 0x00003e0000000e00 0x0020008002000c00

def z490 : W := mkw 0x6cfa080448520224 0x7d09fb297ca18098 0x00ff800000fe000f 0x2801ff007c01c01c

def z491 : W := mkw 0x8120f9dea5e89052 0xe63fef030bbff242 0x0701ffffffff81c0 0xee7fff438ffff303

def z492 : W := mkw 0x0020004200200000 0x7400362148852000 0xc7f1c1ffc7f18000 0xfe127f63cd8f3000

def z493 : W := mkw 0xc13098d6e5f89052 0x7709ff2348adf2d2 0xc7f1c1ffc7fff1fe 0xffd3ff63cd8ff3f3

def z494 : W := mkw 0x24a8000000000000 0x883fcbc59c000000 0x0701800000000000 0xe83fff438c000000

def z495 : W := mkw 0x9200653892005900 0x80b600c6831a0740 0x07007fffff0001c0 0xc43e004383fe0300

def z496 : W := mkw 0x0000020100002000 0x0000001000400820 0xf800000ff8000030 0x408c003c00f000e0

def z497 : W := mkw 0x48524e2548526224 0xf53938f863e18db8 0xf8fe7ffff8fe7fff 0xf5bdb8fc73f1cffc

def z498 : W := mkw 0x0020000000000000 0x903fdb2148000000 0xc7f1800000000000 0xf83fff63cc000000

def z499 : W := mkw 0x24e8000000000000 0x180fdb2dfc000000 0xffff800000000000 0x680fff3ffc000000

def z500 : W := mkw 0x36c8672912006900 0x88bfc9dcb7520d20 0x380e3e0038000e00 0x002d809c32700c00

def z501 : W := mkw 0x9220673992007900 0x90b612f7cb5a0f60 0xfff1ffffff007ff0 0xfdbe7fffcffe0fe0

def z502 : W := mkw 0x008575ea24ad4488 0x8236c5c017167505 0x000181f0070181c0 0x0a5247400d0e3303

def z503 : W := mkw 0x8000005280201000 0x64002402008d2240 0xc70041ffc7f1f1f0 0xf7927f63818f33e0

def z504 : W := mkw 0xa5a8805281209052 0x8836c7c79c0c2242 0x070181f0070181c0 0x0a5247438d0e3303

def z505 : W := mkw 0x0000000000000000 0x0000000000000000 0x00007e0000fe0000 0xa42180000201c000

def z506 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00ff81f00001ffcf 0x1b5040c07d003f1f

def z507 : W := mkw 0x24e8000000000000 0x180012edfc000000 0xffff800000000000 0xf8127ffffc000000

def z508 : W := mkw 0x24ed042000054488 0x180012edfc000505 0xffff800000007fcf 0x194000fffc000f1f

def z509 : W := mkw 0x9200211892001900 0x00860006801a0240 0x0700000007000000 0x00020003800e0000

def z510 : W := mkw 0x0000004200200000 0x6400240000852000 0x000041ffc7f18000 0x06000000018f3000

def z511 : W := mkw 0x00855ca400c54488 0xe439e8c017a1d505 0x00fffffff8ffffcf 0xff7df8c07ff1ff1f

def z512 : W := mkw 0x9200231992003900 0x00800012005a0a60 0x0000000fff000030 0x0080000000fe00e0

def z513 : W := mkw 0x0000000000000000 0x0000000000000000 0xf800000000000000 0xd02c00bc00000000

def z514 : W := mkw 0x9200631992003900 0x80b60016835a0a60 0xff007fffff000030 0xc4be003f83fe00e0

def z515 : W := mkw 0x24e8080400400000 0xfc3ffbedfca18000 0xfffffe0ff8fe0000 0xfc3ffffffef1c000

def z516 : W := mkw 0x6cfa020148122224 0x993fdbfdfc4008b8 0xffff800000007e3f 0xf9bffffffc000cfc

def z517 : W := mkw 0x48d756a1489766ac 0x9130d0f877405dbd 0xf8fffff000ffffff 0xbff1c0fc7f01ffff

def z518 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f1800fc70071fe 0x59c23f63cc8e03f3

def z519 : W := mkw 0x0000000000000000 0x0000000000000000 0x00fe000000007e0f 0x1100008070000c1c

def z520 : W := mkw 0x48520a0548522224 0xf53ff93860e188b8 0xf8fe7e0ff8fe7e3f 0xf5bfffbc72f1ccfc

def z521 : W := mkw 0x4852020148122224 0x11001038604008b8 0xf800000000000030 0x0080003c000000e0

def z522 : W := mkw 0x48525a8548d22224 0xf539f83863e1d8b8 0xf8fe7ffff8fffe3f 0xf7bdf8bc73f1fcfc

def z523 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc70041ffc70071f0 0xd5923f63818e03e0

def z524 : W := mkw 0x0085042000054488 0x000000c014000505 0x00018000000001c0 0x084000400c000303

def z525 : W := mkw 0x24cd54a000854488 0x883fc9ccb7005505 0x38fffff000ffffcf 0xbf7dc0dc7f01ff1f

def z526 : W := mkw 0x0000000000000000 0x8030c00000000000 0x0000000000000000 0xa031c00000000000

def z527 : W := mkw 0x0000588400c00000 0xe439e80003a1d000 0x00007ffff8ff8000 0xe63df80003f1f000

def z528 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00ffbe00000e0e01 0xb831c0c07e00cc0c

def z529 : W := mkw 0x0000442000004000 0x803000c003000500 0x00fe7ff000fe7fcf 0xb53180c07301cf1c

def z530 : W := mkw 0x0000508000800000 0x8030c00003005000 0x00f1fff000fff1ce 0xbf71c0404f01f313

def z531 : W := mkw 0x92006f3d92407900 0xe4bf28d683fb8f60 0xff007ffffffe7ff0 0xf5bfb8ff83ffcfe0

def z532 : W := mkw 0xdad77fbddad77fac 0xf5bff8fef7fbdffd 0xffffffffffffffff 0xfffff8ffffffffff

def z533 : W := mkw 0x00a554a000854488 0x9030d2e15f005505 0xc7fffff000ffffcf 0xff73ffe3ff01ff1f

def z534 : W := mkw 0x0000020100002000 0x0000001000400820 0x38003e0038000e00 0x002c009c02700c00

def z535 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xff01800000000000 0x481e7f7f8c000000

def z536 : W := mkw 0x48120a0548522224 0x6500201000e188b8 0xf8007e0ff8fe7e3f 0xd5ac00bc02f1ccfc

def z537 : W := mkw 0x0000000000000000 0x0009080000000000 0x0000000000000000 0xe02db80000000000

def z538 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x0001fff000ff81c0 0xae71c0400f01f303

def z539 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00ffbe00000e7fcf 0x196180c07e00cf1f

def z540 : W := mkw 0x08427bcf2cea2224 0xe63fed1823f7f828 0x380e7fffffff8e01 0xe63fff9c33fffc0c

def z541 : W := mkw 0x0000000000000000 0x0000000000000000 0x000041f000f18000 0xa610400001013000

def z542 : W := mkw 0x24e8000000000000 0x9836d3edfc000000 0xffff800000000000 0x181247fffc000000

def z543 : W := mkw 0x92007fffb6e87900 0xe6b624d683ffff60 0xff007ffffffffff0 0xd7be00ff83ffffe0

def z544 : W := mkw 0x0040000000000000 0x1009182860000000 0xf8fe7e0000fe7e0f 0xf52db8bc7201cc1c

def z545 : W := mkw 0x0000080400400000 0x0009080000208000 0x00003e00380e0000 0x002d80000270c000

def z546 : W := mkw 0x6cff5ea548d766ac 0xfd3ffbfdffe1ddbd 0xfffffffff8ffffff 0xfffffffffff1ffff

def z547 : W := mkw 0x48975ea548d766ac 0xe530e0d017e1ddbd 0x00fffffff8ffffff 0xbff1c0c07ff1ffff

def z548 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00003e0038ff8000 0x222dff000271f000

def z549 : W := mkw 0x41b5d4e241b5c4da 0xf530f6e15f857597 0x00fffff000ffffcf 0xbf71ffc07f01ff1f

def z550 : W := mkw 0x000554a000854488 0x0000000003005505 0x00fe7ff000ffffcf 0xb76180807301ff1f

def z551 : W := mkw 0x48522b4f6c7a2224 0x770f3d3860f7a8b8 0xf800000fff000030 0x408e3f3c00fe00e0

def z552 : W := mkw 0xb668673992007900 0x98bf1bffeb5a0f60 0xff007fffff007ff0 0xd5be3fff83fe0fe0

def z553 : W := mkw 0x4010000040100000 0x7500302040810090 0xc0fe7e0fc0fe7e3f 0xf5a1b8a07281ccfc

def z554 : W := mkw 0xc1b58472c135d4da 0x750036e35c8d27d7 0xc7ffc1ffc7f1ffff 0xffd27fe3fd8f3fff

def z555 : W := mkw 0x08420a0508422224 0x6409281820e18828 0x380e7e0ff8fe0e01 0xe42db89c32f1cc0c

def z556 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc70041ffc7f1f1fe 0x47c23f23818f33f3

def z557 : W := mkw 0xc9728253c932b276 0x7500363b68cd2afa 0xffffc1ffc7f1ffff 0xffd27ffffd8f3fff

def z558 : W := mkw 0x0000508000800000 0x803fc90003005000 0x00007ff000ff8000 0xe63fff000301f000

def z559 : W := mkw 0x4010000040100000 0x7500302040810090 0xc000000fc0000030 0x40803820008000e0

def z560 : W := mkw 0x2cca0a0508422224 0x883fc9dcb4608828 0x380e3e00380e0e01 0x002d809c3270cc0c

def z561 : W := mkw 0x8020001080001000 0x1000122348080240 0xc7f1c1ffc70071f0 0xfd927f63cd8e03e0

def z562 : W := mkw 0xda520631da127b24 0x118010fee0480ff8 0xfffe000000007fff 0x118000fff0000ffc

def z563 : W := mkw 0x920577b992857d88 0x80b600d6835a5f65 0xff007fffffffffff 0xd7fe00ff83ffffff

def z564 : W := mkw 0x24a879ce24e80000 0xee3fefc59fb7f000 0x0701ffffffff8000 0xee3fff438ffff000

def z565 : W := mkw 0x81a5d4f281a5d4da 0x8030c6c31f0c7747 0x07fffff007ffffcf 0xbf73c7c3ff0fff1f

def z566 : W := mkw 0x0000508000800000 0x8030c00003005000 0x00003e00000e0000 0x002180000200c000

def z567 : W := mkw 0xc130c472c130d052 0xf53036e34b8d27d2 0xc7f1ffffc7f1fffe 0xfff27fe3cf8f3ff3

def z568 : W := mkw 0xd3b5f7fbd3b5fdda 0xf5b6f6f7dfdf7ff7 0xffffffffffffffff 0xffffffffffffffff

def z569 : W := mkw 0x4130f9ce65f88052 0xf73fff214bb7f092 0x00f1ffffffff800e 0xee7fff004ffff013

def z570 : W := mkw 0x48d20a0548522224 0xf539f8f874e188b8 0xf8fffe0ff8fe7e3f 0xfdbdf8fc7ef1ccfc

def z571 : W := mkw 0x0000798c24c80000 0x823fc9000332d000 0x00007ff038ff8000 0xa63dc0000371f000

def z572 : W := mkw 0x008554a000854488 0x0000c00017005505 0x00fffff000ffffcf 0x2f41c0007f01ff1f

def z573 : W := mkw 0x008575ea24ad4488 0x8236c5c017167505 0x00fffff007ffffcf 0xbf73c7c07f0fff1f

def z574 : W := mkw 0xb668231992003900 0x188f1b3fe85a0a60 0xff00000fff000030 0x408e3f3f80fe00e0

def z575 : W := mkw 0x0000442000004000 0x803600c483000500 0xff007ff000007fc0 0xd53e00ff83000f00

def z576 : W := mkw 0x24a8000000000000 0x8836c3c59c000000 0x07ff800000000000 0xb833c7c3fc000000

def z577 : W := mkw 0x928577b992857d88 0x80b0c0d2175a5f65 0x00ffffffffffffff 0xbff1c0c07fffffff

def z578 : W := mkw 0x24a8000000000000 0x9836d3e5dc000000 0xc7f1800000000000 0xf8127f63cc000000

def z579 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe000ff8fe003f 0x608db83c70f1c0fc

def z580 : W := mkw 0xe5788052c1309052 0x7d0f3f2fe88d22d2 0xff00000fc7000030 0x408e3f3f808e00e0

def z581 : W := mkw 0x4852080448520224 0x7509382860a18098 0xc0fe400fc0fe703f 0xf581b8207081c0fc

def z582 : W := mkw 0x0000508000800000 0x0000000003005000 0x00007ff000ff8000 0x060000000301f000

def z583 : W := mkw 0x0085042000054488 0x8030c0c014000505 0x00ff800000007fcf 0xb971c0c07c000f1f

def z584 : W := mkw 0x24e871ca24a80000 0x9a3fdfedff167000 0xffff81f007018000 0xfa3ffffffd0e3000

def z585 : W := mkw 0xedfa8a57c972b276 0xfd3ffffffcedaafa 0xffffffffffffffff 0xffffffffffffffff

def z586 : W := mkw 0x9200673992007900 0x00800012035a0f60 0xf8007fffff007ff0 0xd5ac00bc03fe0fe0

def z587 : W := mkw 0x1a426f2d1a426b24 0x80bf08dca3728d28 0x380e3e00380e0e01 0x002d809c3270cc0c

def z588 : W := mkw 0x24e8000000000000 0x983612edfc000000 0xffff800000000000 0xd83e00fffc000000

def z589 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0x00f1c1ffc7f1f1fe 0x2fc07f004d8f33f3

def z590 : W := mkw 0x0000004200200000 0x0000040000042000 0x000001f007018000 0x02124700010e3000

def z591 : W := mkw 0xc115d4f2c1b5d4da 0x65002402038d77d7 0x00007fffc7ffffff 0x07c00000038fffff

def z592 : W := mkw 0x2448000000000000 0x080f090ca0000000 0x3800000000000000 0x000c001c00000000

def z593 : W := mkw 0xda526f3dda527b24 0xf5bf38fee3fb8ff8 0xff007fffff007ff0 0xd5be38ff83fe0fe0

def z594 : W := mkw 0x0000630900002000 0x8036001003520820 0xf8007fffff007e30 0xd5be00bc03fe0ce0

def z595 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00003e0fff0e0000 0x402fbf0002fec000

def z596 : W := mkw 0xc1b58430c115d4da 0x110012e35c0807d7 0xc7ff800000007fff 0x19c000e3fc000fff

def z597 : W := mkw 0x4812020148122224 0x01000010004008b8 0x0000000000007e3f 0x0180000000000cfc

def z598 : W := mkw 0x24e8000000000000 0x983fdb297c000000 0x00ff800000000000 0xe83fff007c000000

def z599 : W := mkw 0xc135d4f2c1b5d4da 0x750036234b8d77d7 0xc7f1ffffc7ffffff 0xffd27f63cf8fffff

def z600 : W := mkw 0x00857dee24ed4488 0xe630e4c017b7f505 0x00ffffffffffffcf 0xbf71c0c07fffff1f

def z601 : W := mkw 0x0000442000004000 0x803000c003000500 0x00f1fff000f1ffce 0xbf7040c04f013f13

def z602 : W := mkw 0x0000508000800000 0x8030c00003005000 0x000001f000018000 0x0210400001003000

def z603 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0x07007fffff007ff0 0x0592004383fe0fe0

def z604 : W := mkw 0x0080000000000000 0x8030c0c014000000 0x0001800000000000 0x081040400c000000

def z605 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe000ff8000030 0xf0adb8bc70f000e0

def z606 : W := mkw 0x928575b892855d88 0x80b6c0c6971a5745 0x07fffff007ffffcf 0xbf73c0c3ff0fff1f

def z607 : W := mkw 0x92002b5fb6683900 0x668f2d1680ffaa60 0xff00000fff000030 0x408e3f3f80fe00e0

def z608 : W := mkw 0x8120f1daa5a89052 0x8236c7030b1e7242 0x070181f0070181c0 0x0a5247438d0e3303

def z609 : W := mkw 0x24e8000000000000 0x883fcbcdbc000000 0x3f0f800000000000 0x083fc7dfbc000000

def z610 : W := mkw 0x0000000000000000 0x803fc90000000000 0x0000000000000000 0x002d800000000000

def z611 : W := mkw 0xe5f88010c1109052 0x190012effc0802d2 0xffff8000000071fe 0x19c000fffc0003f3

def z612 : W := mkw 0x000071ca24a80000 0x8236c50003167000 0x00007fffff018000 0xc63e470003fe3000

def z613 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0x00fe7e0ff8fe7e3f 0x2581b80072f1ccfc

def z614 : W := mkw 0x4050000040100000 0x7509382860810090 0xf8fe400fc0f0703e 0xf5adb8bc708100f0

def z615 : W := mkw 0x0040000000000000 0x903f18ece0000000 0xfffe000000000000 0xf03fb8fff0000000

def z616 : W := mkw 0x4852000048120224 0x1100102860000098 0x00fe00000000000f 0x000000007000001c

def z617 : W := mkw 0x0000000000000000 0x803000c000000000 0x0000000000000000 0x903000c000000000

def z618 : W := mkw 0xc1108052c1309052 0x65002402008d22d2 0xc70041ffc7f1f1fe 0xd7d20063818f33f3

def z619 : W := mkw 0x0000798c24c80000 0x823fc9000332d000 0x00007fffff0e0000 0xc43f800003fec000

def z620 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x000e7ff000ffffcf 0x076180803301ff1f

def z621 : W := mkw 0x000079ce24e80000 0x6600240003b7f000 0x00007fffffff8000 0xe6127f0003fff000

def z622 : W := mkw 0xa5e8805281209052 0x983fdfeffc0c2242 0xffff81f0070181c0 0xfa7ffffffd0e3303

def z623 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe000ff8007e3f 0x518c38bc70f00cfc

def z624 : W := mkw 0x0000000000000000 0x000000c480000000 0xff00000000000000 0x100000ff80000000

def z625 : W := mkw 0xda126f3dda527b24 0xe5b620d683fb8ff8 0xff007ffffffe7fff 0xd5be00ff83ffcffc

def z626 : W := mkw 0x2468000000000000 0x1800122de8000000 0xff00000000000000 0x0000003f80000000

def z627 : W := mkw 0xd330e77bd330f952 0xf5b636f7cbdf2ff2 0xff007fffff007ff0 0xd5be3fff83fe0fe0

def z628 : W := mkw 0x0000294e24680000 0x6600240000b7a000 0x0000000fff000000 0x0000000000fe0000

def z629 : W := mkw 0x0000000000000000 0x0009c90000000000 0x0000000000000000 0x2001ff0000000000

def z630 : W := mkw 0x24c8798c24c80000 0x8a3fc9ccb732d000 0x380e3e00380e0000 0x002d809c3270c000

def z631 : W := mkw 0x0000000000000000 0x0000000000000000 0x000181f0000181c0 0x0a5040400d003303

def z632 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0x07f181f007f181ce 0x2a527f43cd0f3313

def z633 : W := mkw 0xc1708052c1309052 0x75093e2b688d22d2 0xffffc1ffc7f1f1fe 0xfffffffffd8f33f3

def z634 : W := mkw 0x8100805281209052 0x00000402000c2242 0x000001f0070181c0 0x02400000010e3303

def z635 : W := mkw 0x48120a0548522224 0x7500303040e188b8 0xc0f07e0ff8fe7e3f 0xf580382042f1ccfc

def z636 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00ff81f000ff81cf 0x2a51c0407d01f31f

def z637 : W := mkw 0x48521ac76cfa2224 0x7709fd3860e5f8b8 0xf8fe7e0ff8fffe3f 0xf7adffbc72f1fcfc

def z638 : W := mkw 0x928556b192857d88 0x80b0c0d697485f65 0xfffffff000ffffff 0xbff1c0ffff01ffff

def z639 : W := mkw 0xc1b5d4b0c195d4da 0x9130d2e35f0857d7 0xc7fffff000ffffff 0xbff1c0e3ff01ffff

def z640 : W := mkw 0x0000000000000000 0x0000000000000000 0x000041f0000071c0 0x9510004001000300

def z641 : W := mkw 0x24c8000000000000 0x883fc9ccb4000000 0xff0e000000000000 0xd03f80ffb0000000

def z642 : W := mkw 0x0000020100002000 0x803600d480400820 0xff007e0ff8007e30 0xd5be00ff82f00ce0

def z643 : W := mkw 0xc1b5d4f2c1b5d4da 0xf530f6e35f8d77d7 0xc7f1c1ffc7f1f1fe 0xffd27f63cd8f33f3

def z644 : W := mkw 0x24ad54a000854488 0x8836c3c59f005505 0x07fffff000ffffcf 0xbf73c7c3ff01ff1f

def z645 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00ff81f0000181c0 0xba71c0c07d003303

def z646 : W := mkw 0x24e879ce24e80000 0xfe3fff297fb7f000 0x00ffffffffff8000 0xee3fff007ffff000

def z647 : W := mkw 0x409554a040954488 0xf530f0e057815595 0xc0ffffffc0ffffff 0xfff1f8e07f81ffff

def z648 : W := mkw 0x64f8000040100000 0xfd3ffbedfc810090 0xffffc00fc0f0703e 0xfdbffffffc8100f0

def z649 : W := mkw 0x800079dea4e81000 0xe63fed0203bff240 0xc7007ffffffff1f0 0xf7bfff6383fff3e0

def z650 : W := mkw 0x8120801081009052 0x0000020308080242 0x07018000000001c0 0x084000438c000303

def z651 : W := mkw 0xc1308010c1109052 0x11001223480802d2 0xc7f1c1ffc70071fe 0xddd20063cd8e03f3

def z652 : W := mkw 0xc130f1dae5b89052 0xf736f7234b9f72d2 0xc7f1c1ffc7f1f1fe 0xffd27f63cd8f33f3

def z653 : W := mkw 0x0000442000004000 0x0000000003000500 0x00007ff000007fc0 0x0500000003000f00

def z654 : W := mkw 0x000079ce24e80000 0xe636240003b7f000 0x00007fffffff8000 0xc63e000003fff000

def z655 : W := mkw 0xc1308010c1109052 0x11001223480802d2 0xc7f18000000071fe 0xf9d27f63cc0003f3

def z656 : W := mkw 0x4010000040100000 0x1100102040000090 0xc0f000000000703e 0x11800020400000f0

def z657 : W := mkw 0xc130a95ee5789052 0x770f3f2348bfa2d2 0xc700000fff000030 0x408e3f2380fe00e0

def z658 : W := mkw 0x12007fad36c86900 0x82bfc9d48372dd20 0x38003e00380e0e00 0x002d809c0270cc00

def z659 : W := mkw 0x24ed54a000854488 0x9839dbe97f005505 0x00fffff000ffffcf 0xbf71ffc07f01ff1f

def z660 : W := mkw 0xc9528a57c972b276 0x75093c3a60edaafa 0xf8fe7fffffffffff 0xf7edb8bc73ffffff

def z661 : W := mkw 0x9320e57a9320d952 0x80b606c78b1e2742 0x070181f0070181c0 0x0a5247438d0e3303

def z662 : W := mkw 0x0000004200200000 0x6400240000852000 0x0000000000f18000 0x22007f0000013000

def z663 : W := mkw 0x485279ce6cfa0224 0xf73ffd2863b7f098 0x00fe7fffffff800f 0xe63fff0073fff01c

def z664 : W := mkw 0x4010020140102000 0x7500303040c108b0 0xf8f07e0ff8f07e3e 0xf5ac38bc42f10cf0

def z665 : W := mkw 0x9200673992007900 0x80bfc9d6835a0f60 0xff007fffff007ff0 0xf5bfffff83fe0fe0

def z666 : W := mkw 0x8000001080001000 0x0000000200080240 0xc7000000000071f0 0x11800063800003e0

def z667 : W := mkw 0x0085108000850488 0x0000c00014005005 0x000e0000000e0001 0x000180003000c00c

def z668 : W := mkw 0x48575ea548d766ac 0x7509383863e1ddbd 0xf8fe7ffff8ffffff 0xf7edb8bc73f1ffff

def z669 : W := mkw 0x0085108000850488 0x0000c00014005005 0x0001800000018000 0x0a4040000c003003

def z670 : W := mkw 0x92007dfeb6e85900 0xe6bfedc683bff740 0x07007fffffff81c0 0xe63fff4383fff300

def z671 : W := mkw 0x0000080400400000 0x6409280000a18000 0x0000000000fe0000 0x2001b8000001c000

def z672 : W := mkw 0x0005108000850488 0x0000000000005005 0x0000000000ff800f 0x024000000001f01f

def z673 : W := mkw 0x08427b8d2cca2224 0x823fc9182372d828 0x380e3e00380e0e01 0x002d809c3270cc0c

def z674 : W := mkw 0x6cfa0a0548522224 0x7d09fb397ce188b8 0xf8fffe0ff8fe7e3f 0xfdadffbc7ef1ccfc

def z675 : W := mkw 0x128577a912856d88 0x80b6c0d497525d25 0x38fffff038ffffcf 0xbf7dc0dc7f71ff1f

def z676 : W := mkw 0x920077fbb6a87900 0x82b6c5d6835e7f60 0xff007fffff01fff0 0xd7be47ff83fe3fe0

def z677 : W := mkw 0x9200673992007900 0x008000d6835a0f60 0xff007fffff007ff0 0x158000ff83fe0fe0

def z678 : W := mkw 0x0000000000000000 0x0000000000000000 0x000041f000f1f1ce 0x0740000001013313

def z679 : W := mkw 0x81a5d4f281a5d4da 0x8030c6c31f0c7747 0x070181f0070181c0 0x0a5247438d0e3303

def z680 : W := mkw 0xc1308253c130b052 0x7500363348cd2af2 0xfff1fffffff1fffe 0xfffe7fffcfff3ff3

def z681 : W := mkw 0x9200063192007900 0x0080001200480f60 0x0000000000007ff0 0x0180000000000fe0

def z682 : W := mkw 0x0085042000054488 0x000000c014000505 0x00fffe0000fe7fcf 0xbd6180c07e01cf1f

def z683 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8f0400ff8f0703e 0xf58c383c40f100f0

def z684 : W := mkw 0xc110f9dee5f89052 0x6700240203bff2d2 0x00007ffffffff1fe 0x07c0000003fff3f3

def z685 : W := mkw 0x0000798c24c80000 0xe63fe90003b3d000 0x00007e0ff8fe0000 0xe42db80002f1c000

def z686 : W := mkw 0x0000108000800000 0x0000c00000005000 0x0000000000ff8000 0x2201c0000001f000

def z687 : W := mkw 0xc130f9dee5f89052 0x770036234bbff2d2 0xc7f1fffffffff1fe 0xffd27f63cffff3f3

def z688 : W := mkw 0x0040020100002000 0x1009183860400820 0xf8fe7e0ff8007e30 0xf5adb8bc72f00ce0

def z689 : W := mkw 0xa4e8001080001000 0x983fdbeffc080240 0xffffc1ffc70071f0 0xfdbffffffd8e03e0

def z690 : W := mkw 0x0000004200200000 0x6400240000852000 0x0000000fc7000000 0x40023f00008e0000

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000400fc0007030 0xd5800020008000e0

def z692 : W := mkw 0xc9728856c9729276 0x75093e2b68ada2da 0xc7ffc1ffc7fff1ff 0xffd3ff63fd8ff3ff

def z693 : W := mkw 0x36e8672912006900 0x98bfdbfdff520d20 0xffffbe0038000e00 0xf83ffffffe700c00

def z694 : W := mkw 0xb6e8673992007900 0x98b612ffff5a0f60 0xffffffffff007ff0 0xddbe00fffffe0fe0

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0xc700000000000000 0xd012006380000000

def z696 : W := mkw 0xf7f8e77bd330f952 0xfdbfffffffdf2ff2 0xfffffffffff1fffe 0xffffffffffff3ff3

def z697 : W := mkw 0x808554b080855488 0x8030c0c217085745 0xc7ffffffc7ffffff 0xfff3c0e3ff8fffff

def z698 : W := mkw 0x413098c665f88052 0x7709ff2148a5f092 0x00f1800000ff800e 0x2a41ff004c01f013

def z699 : W := mkw 0xc9728a57c972b276 0x75093e3b68edaafa 0xfff1c1fffff1f1fe 0xffde7f7fcdff33f3

def z700 : W := mkw 0x4812080448520224 0x6500200000a18098 0x0000000000fe000f 0x000000000001c01c

def z701 : W := mkw 0xc130f9dee5f89052 0xf73fff234bbff2d2 0xc7007fffffff8030 0xe6bfff2383fff0e0

def z702 : W := mkw 0x08c75ea508c766ac 0x8039c8d83760dd2d 0x38fffff038ffffcf 0xbf7dc0dc7f71ff1f

def z703 : W := mkw 0x0000042000004000 0x000000c000000500 0x0000000000007fc0 0x110000c000000f00

def z704 : W := mkw 0xd310e77bd330f952 0xe5b624d683df2ff2 0xff007ffffff1fffe 0xd7fe00ff83ff3ff3

def z705 : W := mkw 0x48d70e25485766ac 0x750938f874e18dbd 0xf8fffe0ff8fe7fff 0xfdedb8fc7ef1cfff

def z706 : W := mkw 0x9a426f3d9a427b24 0x80bf08dea37a8f68 0xff0e7fffff0e7ff1 0xd5bf80ffb3fecfec

def z707 : W := mkw 0x008575a800854488 0x8036c0c497125505 0xffffffffffffffcf 0xff7fc0ffffffff1f

def z708 : W := mkw 0x8000021180003000 0x0000001200480a60 0xffffffffffffffff 0xffffc0ffffffffff

def z709 : W := mkw 0x9200273992007900 0x80b600d6805a0f60 0xff00000fff007ff0 0xd1be00ff80fe0fe0

def z710 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x0000000fff000000 0x400e3f0000fe0000

def z711 : W := mkw 0x92057fffb6ed7d88 0x6680241203ffff65 0x00007fffffffffff 0x07c0000003ffffff

def z712 : W := mkw 0x49f7dce649f7c6fe 0xf539fee97fa5f59f 0x00fffff000ffffcf 0xbf71ffc07f01ff1f

def z713 : W := mkw 0x0000294e24680000 0xe63f2dc480b7a000 0xff00000fff000000 0xd03e3fff80fe0000

def z714 : W := mkw 0x24e8000000000000 0x983fdb2dfc000000 0xffff800000000000 0xe83fff3ffc000000

def z715 : W := mkw 0x000079ce24e80000 0xe63fedc483b7f000 0x38007fffffff8000 0xe63fff9c03fff000

def z716 : W := mkw 0x000079ce24e80000 0x66092d0003b7f000 0x00007fffffff8000 0x06003f0003fff000

def z717 : W := mkw 0x24e8000000000000 0x1809db297c000000 0xffff800000000000 0xf83ffffffc000000

def z718 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xffffffffff0e7fff 0xddff80fffffecfff

def z719 : W := mkw 0x000071ca24a80000 0x823fcd0003167000 0x00007fffff018000 0xe63fff0003fe3000

def z720 : W := mkw 0xc130f99ce5d89052 0x933fdb234b3ad2d2 0xc7f1be00380e71fe 0x19ed8063ce70c3f3

def z721 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffff800000000000 0x681fff7ffc000000

def z722 : W := mkw 0x8000005280201000 0x64002402008d2240 0xc7f1c1ffc7f1f1fe 0xffd27f63cd8f33f3

def z723 : W := mkw 0xd310a35bd330b952 0x6580241200df2af2 0x0000000fff000030 0x0080000000fe00e0

def z724 : W := mkw 0x0000294e24680000 0x660fed0000b7a000 0x0000000fff000000 0x600fff0000fe0000

def z725 : W := mkw 0x24e879ce24e80000 0x7e0036edffb7f000 0xffffffffffff8000 0x1e0000fffffff000

def z726 : W := mkw 0x000079ce24e80000 0xe630e40003b7f000 0x00007fffffff8000 0xe633ff0003fff000

def z727 : W := mkw 0x0060000000000000 0x903f1aede8000000 0xffff800000000000 0xf83ffffffc000000

def z728 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x000e7fffffff8e01 0xe63fff8033fffc0c

def z729 : W := mkw 0x49f798c649f786fe 0x7509fe297ca5f09f 0x00ff800000ff800f 0x2a41ff007c01f01f

def z730 : W := mkw 0x4972884649728276 0x75093e2968a5a09a 0x00fffff000ffffcf 0xbf71ffc07f01ff1f

def z731 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffff800000000000 0x581e7ffffc000000

def z732 : W := mkw 0x9200673992007900 0x80b6c0d6835a0f60 0xff007fffff007ff0 0xf5bfc0ff83fe0fe0

def z733 : W := mkw 0x5330e76b5330e952 0xf5b636f5cbd72db2 0x38f1be0038f18e0e 0x2a6c7f9c4e713c13

def z734 : W := mkw 0x24ed7dac24cd4488 0x9a3fdbedff32d505 0xffffbe00380e0e01 0xf83ffffffe70cc0c

def z735 : W := mkw 0x000579ce24ed0488 0xe63fed0003b7f005 0x00007fffffff800f 0xe67fff0003fff01f

def z736 : W := mkw 0x0000294e24680000 0x6600240000b7a000 0x0000000fff000000 0x40023f0000fe0000

def z737 : W := mkw 0x49728a474972a276 0x75093e3968e5a8ba 0xf8fffffffffffe3f 0xffffffbc7ffffcff

def z738 : W := mkw 0x0000000000000000 0x803fc90480000000 0xff00000000000000 0xe03fff3f80000000

def z739 : W := mkw 0x2468000000000000 0x1800122de8000000 0xfff1800000000000 0xf8127f7fcc000000

def z740 : W := mkw 0x0000630900002000 0x803600d483520820 0xff007fffff007e30 0xd5be00ff83fe0ce0

def z741 : W := mkw 0x000554a000854488 0x0000000003005505 0x00fffff000ffffcf 0xbf71c0c07f01ff1f

def z742 : W := mkw 0x008554a000854488 0x8030c0c017005505 0xc0ffffffc0ffffff 0xfff1c0e07f81ffff

def z743 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe3e0ff80e7e3f 0x51adb8bc72f0ccfc

def z744 : W := mkw 0x0020000000000000 0x10061225c8000000 0xfff1800000000000 0xf81e7f7fcc000000

def z745 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xff0f800000000000 0x483fffffbc000000

def z746 : W := mkw 0x48720a0548522224 0x75093a3968e188b8 0xf8fffe0ff8fe7e3f 0xfdadffbc7ef1ccfc

def z747 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00ffbff000ff8fcf 0x2a71c0c07f01ff1f

def z748 : W := mkw 0x0000718800800000 0x803fc90003125000 0x00007fffffff8000 0xe63fff0003fff000

def z749 : W := mkw 0x000079ce24e80000 0xe639ed0003b7f000 0x00007fffffff8000 0xa631ff0003fff000

def z750 : W := mkw 0xb6e8463192007900 0x98b0d2ffff480f60 0xfffffff000007ff0 0xbdb1c0ffff000fe0

def z751 : W := mkw 0x2468000000000000 0x983fdb2de8000000 0xfffe000000000000 0xf03fffbff0000000

def z752 : W := mkw 0x000039ce24e80000 0x660fed0000b7f000 0x000041ffffff8000 0xe61fff0001fff000

def z753 : W := mkw 0x48520a0548522224 0x6509281820e188b8 0x380e3e0ff80e0e31 0x00ad809c32f0ccec

def z754 : W := mkw 0xb6ed063192057d88 0x188012fffc480f65 0xffff800000007fff 0x19c000fffc000fff

def z755 : W := mkw 0x9285673992057d88 0x80b6c0d6975a0f65 0xffffffffff007fff 0xfdffc0fffffe0fff

def z756 : W := mkw 0x2468442000004000 0x983f1bedeb000500 0xff007ff000007fc0 0xd53e3fff83000f00

def z757 : W := mkw 0xf7f88631d310f952 0x198012fffc480ff2 0xffff800000007ffe 0x19c000fffc000ff3

def z758 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xff0e000000000000 0xe03fffbfb0000000

def z759 : W := mkw 0x24ed042000054488 0x983fdbedfc000505 0xffff800000000e01 0xf83ffffffc000c0c

def z760 : W := mkw 0x0000294e24680000 0x66092d0000b7a000 0x0000000fff000000 0x00003f0000fe0000

def z761 : W := mkw 0x008554a000854488 0x8036c0c497005505 0x07fffff000ffffcf 0xbf73c0c3ff01ff1f

def z762 : W := mkw 0x00857dee24ed4488 0xe63fed0017b7f505 0x00ffffffffffffcf 0xef7fff007fffff1f

def z763 : W := mkw 0x00006d6e24684000 0xe63f2dc003b7a500 0x00007fffff007fc0 0xd53e3fc003fe0f00

def z764 : W := mkw 0xc972ab5fed7ab276 0x770f3f3b68ffaafa 0xff00000fff000030 0x408e3f3f80fe00e0

def z765 : W := mkw 0x0000694e24680000 0xe63f2d0003b7a000 0x00003e0fff000000 0x402e3f0002fe0000

def z766 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f181f007f1f1fe 0x3bd27f63cd0f33f3

def z767 : W := mkw 0x24e8000000000000 0x1809db2dfc000000 0xffff800000000000 0x2801ff3ffc000000

def z768 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffffbe00000e0e01 0xf83ffffffe00cc0c

def z769 : W := mkw 0xfefa0631da127b24 0x198012fffc480ff8 0xffff800000007fff 0x198000fffc000ffc

def z770 : W := mkw 0x0000694e00600000 0xe43f2c0003b7a000 0x00007fffffff8000 0xe63fff0003fff000

def z771 : W := mkw 0x36cd77a912856d88 0x88bfc9dcb7525d25 0x380e3e00380e0e01 0x002d809c3270cc0c

def z772 : W := mkw 0x0000084600600000 0x6400240000a5a000 0x00007fffffff8000 0xe6127f0003fff000

def z773 : W := mkw 0x4972884649728276 0x75093e2968a5a09a 0x00f1800000f1800e 0x2a407f004c013013

def z774 : W := mkw 0x92001ef7b6e87900 0x6689edd680edff60 0xff00000000fffff0 0x3381ffff8001ffe0

def z775 : W := mkw 0x92007fffb6e87900 0xe6b0e4d203ffff60 0x00007ffffffffff0 0xb7b1c0c003ffffe0

def z776 : W := mkw 0x24ed042000054488 0x180012edfc000505 0xffffc1f000f1ffcf 0xff527ffffd013f1f

def z777 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xff0fffffff0ffff1 0xdfffc0ffbffeffef

def z778 : W := mkw 0x008554a000854488 0x0000c00017005505 0x00fffff000ffffcf 0xbf61c0807f01ff1f

def z779 : W := mkw 0x9285673992057d88 0x80b600d6975a0f65 0xff0e7fffff007ff1 0xd5be00ffb3fe0fec

def z780 : W := mkw 0x00857dee24ed4488 0xe630e4c017b7f505 0x00ffffffffffffcf 0xff73ffc07fffff1f

def z781 : W := mkw 0x48520a0548522224 0x11091838606088b8 0xf80e3e00380e0e31 0x00ad80bc3270ccec

def z782 : W := mkw 0x0000084600600000 0x64092c0000a5a000 0x00ffffffffffffcf 0xff7fffc07fffff1f

def z783 : W := mkw 0x24e8718800800000 0x983fdbedff125000 0xffffffffffff8000 0xfe3ffffffffff000

def z784 : W := mkw 0x000079ce24e80000 0xe63f2d0003b7f000 0x00007fffffff8000 0xc63e3f0003fff000

def z785 : W := mkw 0x246d54a000854488 0x180f1b2deb005505 0xff007ff000ffffcf 0x474e3f3f8301ff1f

def z786 : W := mkw 0xc1708052c1309052 0x7500362b688d22d2 0xffffc1ffc7f1f1fe 0xffd27ffffd8f33f3

def z787 : W := mkw 0x00007dee24e84000 0xe63fedc003b7f500 0x00007fffffff81c0 0xe63fff4003fff300

def z788 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xfffffff00001ffc0 0xff7fffffff003f03

def z789 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xfffffff000ffffcf 0xff7fffffff01ff1f

def z790 : W := mkw 0x92857fffb6ed7d88 0xe6b0e4d217ffff65 0x00ffffffffffffff 0xbff1c0c07fffffff

def z791 : W := mkw 0xd330c631d310f952 0x91b012f7cb480ff2 0xfff1fff000f1fffe 0xbff040ffcf013ff3

def z792 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x00f1c1fffff1f1ce 0xff5e7f404dff3313

def z793 : W := mkw 0x0000000000000000 0x803f09c480000000 0xff00000000000000 0xd03e3fff80000000

def z794 : W := mkw 0x49528a474972a276 0x75093c3860e5a8ba 0xf8fe7e0ff8fffe3f 0xf7edb8bc72f1fcff

def z795 : W := mkw 0x008079ce24e80000 0xe63fedc017b7f000 0x000e7fffffff8000 0xe63fff8033fff000

def z796 : W := mkw 0x24e8442000004000 0x983fdbedff000500 0xffff81f0000001c0 0xf83ffffffd000300

def z797 : W := mkw 0x08420a0508422224 0x0009081820608828 0x380e7e0ff80e7e31 0x05ad809c32f0ccec

def z798 : W := mkw 0x2468290c24480000 0x1a0f1b2de8328000 0xff00000038000000 0x400e3f3f80700000

def z799 : W := mkw 0x0000084600600000 0x64092c0000a5a000 0x0000000fff000000 0x400e3f0000fe0000

def z800 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x000e3e0fff0e0e01 0x402fbf8032fecc0c

def z801 : W := mkw 0x8020001080001000 0x1000122348080240 0xc7f1c1ffc7f1f1fe 0xffd27f63cd8f33f3

def z802 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00ffffffc7ffffcf 0xff73c0c07f8fff1f

def z803 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xffffffffff01fff0 0xffffc0fffffe3fe3

def z804 : W := mkw 0x24e8290c24480000 0x9a3fdbedfc328000 0xffff800038000000 0xf83ffffffc700000

def z805 : W := mkw 0xd3b58631d315fdda 0x118012f7dc480ff7 0xffff800000007fff 0x19c000fffc000fff

def z806 : W := mkw 0xb6e8021192003900 0x188012fffc480a60 0xffff800000000030 0x188000fffc0000e0

def z807 : W := mkw 0x008554a000854488 0x8030c0c017005505 0xc7fffff000ffffcf 0xff73c0e3ff01ff1f

def z808 : W := mkw 0x008579ce24ed0488 0xe63fed0017b7f005 0x0001ffffffff8000 0xee7fff000ffff003

def z809 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xff0e3e0fff0e0e31 0x40af80bfb2feccec

def z810 : W := mkw 0x00000a0500402000 0x6409281000e18820 0xf8fe7e0ff8fe7e3f 0xf5adb8bc72f1ccfc

def z811 : W := mkw 0x9200631992003900 0x80b60016835a0a60 0xff007fffff007e30 0xd5be00bf83fe0ce0

def z812 : W := mkw 0x9285339992853d88 0x0086c016945a5a65 0xffff800fffff803f 0x6acfc03ffcfff0ff

def z813 : W := mkw 0xe5d88052c1309052 0xed3fedceb48d22d2 0x380e41ffc7f1f1fe 0x07ed809c318f33f3

def z814 : W := mkw 0x24e8652800004000 0x983fdbedff120500 0xffffffffff007fc0 0xfd3ffffffffe0f00

def z815 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f1ffffc7ffffff 0xffd27f63cf8fffff

def z816 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff01ffffff01fff0 0xdffe40ff8ffe3fe3

def z817 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xff007fffff007ff0 0xd5be00ff83fe0fe0

def z818 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00fffff000ffffcf 0x2f61c0807f01ff1f

def z819 : W := mkw 0x9200631992003900 0x00860016835a0a60 0xff007fffff000030 0x448e003f83fe00e0

def z820 : W := mkw 0x9200063192007900 0x008000d680480f60 0xff007fffff007ff0 0xd5be00ff83fe0fe0

def z821 : W := mkw 0xc9128a57c972b276 0x6500241200edaafa 0x00ffffffffffffff 0xbff1c0c07fffffff

def z822 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffffc1f0000071c0 0xfd3ffffffd000300

def z823 : W := mkw 0xd315f7fbd3b5fdda 0x6580241203df7ff7 0x00007fffffffffff 0x07c0000003ffffff

def z824 : W := mkw 0x920577b992857d88 0x80b600d6835a5f65 0xff007fffff0e7ff1 0xd5be00ff83fecfec

def z825 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffffc00fc0007030 0xfdbffffffc8000e0

def z826 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00ffffffffffffcf 0xff7fffc07fffff1f

def z827 : W := mkw 0x0020000000000000 0x100012e5c8000000 0xfff1800000000000 0xf8127fffcc000000

def z828 : W := mkw 0x48120a0548522224 0x6500201000e188b8 0xf8fe7e0ff8fe7e3f 0xf5ad80bc72f1ccfc

def z829 : W := mkw 0x24e8400000000000 0x983fdbedff000000 0xfffffff000000000 0xfc3fffffff000000

def z830 : W := mkw 0x0080000000000000 0x803fc9c494000000 0xffff800000000000 0xf83ffffffc000000

def z831 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff007fffff007ff0 0xd5be00ff83fe0fe0

def z832 : W := mkw 0x0000614a00200000 0xe43fed0003972000 0x00007ffffff18000 0xe63fff0003ff3000

def z833 : W := mkw 0x24ed108000850488 0x983fdbedfc005005 0xffff8000000e0001 0xf83ffffffc00c00c

def z834 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffff800000000000 0x3813fffffc000000

def z835 : W := mkw 0x4010020140102000 0x7500303040c108b0 0xf8fe7e0ff8fe7e3f 0xf5adb8bc72f1ccfc

def z836 : W := mkw 0x485273cb6cba2224 0x9336d538635678b8 0xf8fe01f00701fe3f 0x139247bc710e3cfc

def z837 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xfff1c1ffc7f1f1fe 0xfffe7fffcd8f33f3

def z838 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0x3fff800000000000 0x283fffdffc000000

def z839 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xffff81f000ff81cf 0xfa7ffffffd01f31f

def z840 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xfffffff0000e7fc1 0xfd3fffffff00cf0c

def z841 : W := mkw 0x248d54a000854488 0x8836c1c497005505 0x00fffff000ffffcf 0xbf71c0c07f01ff1f

def z842 : W := mkw 0x24e8000000000000 0x180fdbedfc000000 0xffff800000000000 0x780ffffffc000000

def z843 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00003e0fff0e0000 0xe03fff0002fec000

def z844 : W := mkw 0x00857dee24ed4488 0xe63fedc497b7f505 0xffffffffffffffcf 0xff7fffffffffff1f

def z845 : W := mkw 0x92002b5fb6683900 0x6680241200ffaa60 0x0000000fff000030 0x0080000000fe00e0

def z846 : W := mkw 0x000039ce24e80000 0x6609ed0000b7f000 0x0000000fffff8000 0x2201ff0000fff000

def z847 : W := mkw 0x9285273992057d88 0x008600d6945a0f65 0xffff800fff007fff 0x59ce00fffcfe0fff

def z848 : W := mkw 0x9280231992003900 0x80b6c0d6945a0a60 0xffff800fff000030 0xf8bfc0fffcfe00e0

def z849 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00003e0fffff8000 0x622fff0002fff000

def z850 : W := mkw 0x2468000000000000 0x983fdb2de8000000 0xfff1800000000000 0xf83fff7fcc000000

def z851 : W := mkw 0x00057dee24ed4488 0xe63fed0003b7f505 0x00007fffffff81c0 0xe67fff0003fff303

def z852 : W := mkw 0x9200673992007900 0x00800012035a0f60 0xff007fffff007ff0 0xd5be00ff83fe0fe0

def z853 : W := mkw 0x00057dee24ed4488 0xe63fed0003b7f505 0x00007fffffff8e01 0xe63fff0003fffc0c

def z854 : W := mkw 0x000071ca00a00000 0xe436e40003977000 0x00007fffffff8000 0xe63fff0003fff000

def z855 : W := mkw 0x00855ce600e54488 0xe439ecc017a5f505 0x00ffffffffffffcf 0xff7fffc07fffff1f

def z856 : W := mkw 0xd310a35bd330b952 0x6580241200df2af2 0x000041fffff1f1fe 0x07c0000001ff33f3

def z857 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xff01800000000000 0xe83fff7f8c000000

def z858 : W := mkw 0x92007bdfb6e83900 0x6680241203fffa60 0x00007fffffff8030 0x0680000003fff0e0

def z859 : W := mkw 0xc1308052c1309052 0x65002603088d22d2 0x0701c1ffc7f1f1fe 0xefd27f438d8f33f3

def z860 : W := mkw 0x9200677b92207900 0x6480241203df2f60 0x00007ffffff1fff0 0x0780000003ff3fe0

def z861 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xffff81f00001ffcf 0xfb7ffffffd003f1f

def z862 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xfffe7e0ff8fe7e3f 0xf5bfb8fff2f1ccfc

def z863 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00003ff03fff8000 0x223fff00037ff000

def z864 : W := mkw 0x24ed7dac24cd4488 0x9a3fdbedff32d505 0xfffffff038ffffcf 0xff7fffffff71ff1f

def z865 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x00fe7e0ffffe7e0f 0xf52fbf8072ffcc1c

def z866 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xfffffff000ff81c0 0xfe7fffffff01f303

def z867 : W := mkw 0x000039ce24e80000 0x660f2d0000b7f000 0x0000000fffff8000 0x420e3f0000fff000

def z868 : W := mkw 0x0000614a00200000 0xe436240003972000 0x00007fffff000000 0xc43e3f0003fe0000

def z869 : W := mkw 0x08420a0508422224 0x0009081820608828 0xf80e3e00380e7e31 0x11ad80bc3270ccec

def z870 : W := mkw 0x6dfa884649728276 0x7d09ff297ca5a09a 0x00ff800000ff800f 0x2a41ff007c01f01f

def z871 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xfff07ffffff07ffe 0xf5be00ffc3ff0ff0

def z872 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xff00000000000000 0x400e3f3f80000000

def z873 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00fffff000ffffcf 0x1f6180c07f01ff1f

def z874 : W := mkw 0x008514a000854488 0x8030c0c014005505 0x00ff800000ffffcf 0xbb71c0c07c01ff1f

def z875 : W := mkw 0x0020000000000000 0x903612e5c8000000 0xff00000000000000 0xd03e3fff80000000

def z876 : W := mkw 0xc1b5d4f2c1b5d4da 0xf530f6e35f8d77d7 0xc70e3e0fc70e0e31 0x40a3bfa3b28eccec

def z877 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff00000fff000030 0xd09e007f80fe00e0

def z878 : W := mkw 0x9200673992007900 0x008600d6835a0f60 0xff007fffff007ff0 0x558e00ff83fe0fe0

def z879 : W := mkw 0x65f8800041108052 0x993fdbedfc000092 0xffff80000000000e 0xf87ffffffc000013

def z880 : W := mkw 0x24e8000000000000 0x180012edfc000000 0xffff800000000000 0x58023ffffc000000

def z881 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff007fffff007ff0 0x15ac00ff83fe0fe0

def z882 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff0001ffff0001f0 0xd0be00ff81fe03e0

def z883 : W := mkw 0x24ed108000850488 0x983fdbedfc005005 0xffff800000018000 0xfa7ffffffc003003

def z884 : W := mkw 0x928575fab6ad5d88 0x82b6c5c6971e7745 0x070181f0070181c0 0x0a5247438d0e3303

def z885 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff00000fff007e30 0x518e00bf80fe0ce0

def z886 : W := mkw 0x24ed042000054488 0x983fdbedfc000505 0xffffc1f000f1ffcf 0xff7ffffffd013f1f

def z887 : W := mkw 0x48720a0548522224 0x75093a3968e188b8 0xfffe7e0ff8fe7e3f 0xf5afbfbff2f1ccfc

def z888 : W := mkw 0x000079ce24e80000 0x6609ed0003b7f000 0x00007fffffff8000 0xe62dff0003fff000

def z889 : W := mkw 0x24e8718824880000 0x9a3fdbedff125000 0xffff800000000000 0xf83ffffffc000000

def z890 : W := mkw 0x24e8000000000000 0x18091aedfc000000 0xffff800000000000 0xf83ffffffc000000

def z891 : W := mkw 0x2468000000000000 0x983fdbede8000000 0xff00000000000000 0xf03fffff80000000

def z892 : W := mkw 0x0040020100002000 0x1009183860400820 0xf8fe7e0ff8fe7e3f 0xf5adb8bc72f1ccfc

def z893 : W := mkw 0x0000294e24680000 0xe63fed0000b7a000 0x0000000fff000000 0x401e7f0000fe0000

def z894 : W := mkw 0x008554a000854488 0x0000c00017005505 0x00fffff000ffffcf 0xbf51c0407f01ff1f

def z895 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x000fffffffff8fc1 0xee7fffc03fffff0f

def z896 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xff00000000000000 0xd01e3f7f80000000

def z897 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff007fffff007ff0 0x459e007f83fe0fe0

def z898 : W := mkw 0x2468610800000000 0x983f1b2deb120000 0xff007fffff000000 0xc43e3f3f83fe0000

def z899 : W := mkw 0x24e854a000804000 0x983fdbedff005500 0xfffffff000ffffc0 0xff3fffffff01ff00

def z900 : W := mkw 0x2468000000000000 0x983f1bede8000000 0xfff1800000000000 0xf83e7fffcc000000

def z901 : W := mkw 0x008579ce24ed0488 0xe63fed0017b7f005 0x00fffffffffffe0f 0xff7fff807ffffc1f

def z902 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xfffe000000000000 0xf02fbfbff0000000

def z903 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xff0e3e00000e0e01 0x402fbfbfb200cc0c

def z904 : W := mkw 0x9200231992003900 0x80b600d6805a0a60 0xff0041ffff0071f0 0xd5be00ff81fe03e0

def z905 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f1ffffc7fff1fe 0xfff3ff63cf8ff3f3

def z906 : W := mkw 0x928575b892855d88 0x80b6c0c6971a5745 0x070001f0070001c0 0x00120043810e0300

def z907 : W := mkw 0xd395f7fbd3b5fdda 0xe5b0e4d217df7ff7 0x00ffffffffffffff 0xbff1c0c07fffffff

def z908 : W := mkw 0x92006f7fb6687900 0x6680241203ffaf60 0x00007fffff007ff0 0x0580000003fe0fe0

def z909 : W := mkw 0x2468210800000000 0x180f1b2de8120000 0xff00000fff000000 0x400e3f3f80fe0000

def z910 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffff81f0000181c0 0xfa7ffffffd003303

def z911 : W := mkw 0x9200739992803900 0x80b6c016835a5a60 0xff007fffffff8030 0xe6bfc03f83fff0e0

def z912 : W := mkw 0x920577b992857d88 0x00860016835a5f65 0xff007fffffffffff 0x47ce003f83ffffff

def z913 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00007fffff0e0000 0xc43fbf0003fec000

def z914 : W := mkw 0x0000084600600000 0x64092c0000a5a000 0x000041fffff18000 0xe61e7f0001ff3000

def z915 : W := mkw 0xc9728052c9329276 0x7500362b688d22da 0xc7ffc1ffc7f1f1ff 0xffd27f63fd8f33ff

def z916 : W := mkw 0x24e8210800000000 0x983fdbedfc120000 0xffff800fff000000 0xf83ffffffcfe0000

def z917 : W := mkw 0x248879ce24e80000 0xee3fedc497b7f000 0x00007fffffff8000 0xe63fff0003fff000

def z918 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00007fffffff8000 0x462fbf0003fff000

def z919 : W := mkw 0x0000694e24680000 0xe63f2d0003b7a000 0x00007ffffffe0000 0xe43fbf0003ffc000

def z920 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x0000400ffff00000 0xe40e3f0000ff0000

def z921 : W := mkw 0x2468000000000000 0x983fdb2de8000000 0xff00000000000000 0x401e7f3f80000000

def z922 : W := mkw 0x000079ce24e80000 0x6600240003b7f000 0x00007fffffff8000 0x26007f0003fff000

def z923 : W := mkw 0x0060000000000000 0x10091a2968000000 0xfff1800000000000 0xf81e7f7fcc000000

def z924 : W := mkw 0x9280673992007900 0x80b6c0d6975a0f60 0xfffffffffff1fffe 0xffffc0ffffff3ff3

def z925 : W := mkw 0x9200673992007900 0x80b6c1d6835a0f60 0xff007fffff007ff0 0xd5be47ff83fe0fe0

def z926 : W := mkw 0x00857dee24ed4488 0xe639edc017b7f505 0x00ffffffffffffcf 0xbf71ffc07fffff1f

def z927 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff003e0fff000e30 0x40ae00bf82fe0ce0

def z928 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xffffbff0000f8fc1 0xfa7fffffff00ff0f

def z929 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xffffffffffffffff 0xffffc0ffffffffff

def z930 : W := mkw 0x008554a000854488 0x8036c1c017005505 0x00fffff000ffffcf 0xbf73c7c07f01ff1f

def z931 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xfffe7ffffffe7fff 0xf5bf80fff3ffcffc

def z932 : W := mkw 0x008575ea00a54488 0xe436e4c017977505 0x00ffffffffffffcf 0xff7fffc07fffff1f

def z933 : W := mkw 0x0080294e24680000 0xe63fedc014b7a000 0x00ff800fff000000 0xf83fffc07cfe0000

def z934 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7ffc1ffc7f1f1fe 0xfff3ffe3fd8f33f3

def z935 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00fffff000ffffcf 0x2f51c0407f01ff1f

def z936 : W := mkw 0x24e8000000000000 0x180fdb2dfc000000 0xffff800000000000 0xf82fffbffc000000

def z937 : W := mkw 0x93a5f5fa93a5ddda 0x80b6c6c79f1e7747 0x070181f0070181c0 0x0a5247438d0e3303

def z938 : W := mkw 0x0000084600600000 0x64092c0000a5a000 0x00007e0ffffe0000 0xe42fbf0002ffc000

def z939 : W := mkw 0x000079ce24e80000 0x660f2d0003b7f000 0x000001ffff018000 0x420e3f0001fe3000

def z940 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff007ffffffe7fff 0xd5be00ff83ffcffc

def z941 : W := mkw 0x6c7a0a0548522224 0x7d093b3968e188b8 0xf8fe7e0ff8fe7e3f 0xf5adbfbc72f1ccfc

def z942 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7ffc1ffc7f1ffff 0xffd27fe3fd8f3fff

def z943 : W := mkw 0x24c8000000000000 0x883fc9ccb4000000 0xff0e000000000000 0xf03fffffb0000000

def z944 : W := mkw 0x0000294e24680000 0xe63fed0000b7a000 0x000041fffff18000 0xe63fff0001ff3000

def z945 : W := mkw 0x000039ce24e80000 0x660fed0000b7f000 0x00007e0fffff8000 0xe62fff0002fff000

def z946 : W := mkw 0x0000214a00200000 0x6406240000972000 0x0000000fff000000 0x400e3f0000fe0000

def z947 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xfff1800000000000 0xf81e7f7fcc000000

def z948 : W := mkw 0x00007dee24e84000 0xe63fedc003b7f500 0x00007fffffff8e00 0xe63fff8003fffc00

def z949 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xfff1c1fffff1f1fe 0xffde407fcdff33f3

def z950 : W := mkw 0x6cfa000048120224 0x993fdbedfc000098 0xffff80000000000f 0xf83ffffffc00001c

def z951 : W := mkw 0x000079ce24e80000 0xe63624c483b7f000 0xff007fffffff8000 0xd63e00ff83fff000

def z952 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x00007fffffff8000 0xe63fff0003fff000

def z953 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff003e0fff000e30 0xd0be00ff82fe0ce0

def z954 : W := mkw 0xb6ad75b892855d88 0x88b6c3c79f1a5745 0x070181f0070181c0 0x0a5247438d0e3303

def z955 : W := mkw 0xb688673992007900 0x88b6c1d6975a0f60 0xff007fffff007ff0 0xd5be00ff83fe0fe0

def z956 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x00007e0fff000000 0xc42e3f0002fe0000

def z957 : W := mkw 0xc912fbdfedfab276 0x6700241203fffafa 0x00007fffffffffff 0x07c0000003ffffff

def z958 : W := mkw 0x008579ce24ed0488 0xe63fed0017b7f005 0x000e7fffffff8001 0xe63fff0033fff00c

def z959 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x000e7fffffffffcf 0xe77fff8033ffff1f

def z960 : W := mkw 0x008554a000854488 0x8030c0c497005505 0xfffffff000ffffcf 0xbf71c0ffff01ff1f

def z961 : W := mkw 0xed7a8a57c972b276 0x7d0f3f3fe8edaafa 0xff00000fff000030 0x408e3f3f80fe00e0

def z962 : W := mkw 0x24ed108000850488 0x983fdbedfc005005 0xffffc1f000fff1cf 0xff7ffffffd01f31f

def z963 : W := mkw 0x24ed042000054488 0x180f1bedfc000505 0xffff800000007fcf 0x594e3ffffc000f1f

def z964 : W := mkw 0x2468000000000000 0x1800122de8000000 0xff00000000000000 0x40023f3f80000000

def z965 : W := mkw 0x0085108000850488 0x0000c00014005005 0x00fffff000ffffcf 0xbf71c0c07f01ff1f

def z966 : W := mkw 0x65f898c665f88052 0x7f09ff297ca5f092 0x00ff800000ff800e 0x2a41ff007c01f013

def z967 : W := mkw 0x00007dee24e84000 0xe63fedc483b7f500 0xff007fffffffffc0 0xf73fffff83ffff00

def z968 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xff01800000000000 0xd83e7fff8c000000

def z969 : W := mkw 0x08420a0508422224 0x0009081820608828 0xf8fe7e0ff8fe7e3f 0xf5ad80bc72f1ccfc

def z970 : W := mkw 0x48520a0548522224 0x11091838606088b8 0xf8fe3e00380e7e3f 0xf1adb8bc7270ccfc

def z971 : W := mkw 0x24ed75a800854488 0x983fdbedff125505 0xffffffffffffffcf 0xff7fffffffffff1f

def z972 : W := mkw 0x920077b992807900 0x80b6c0d6835a5f60 0xfff1fffffffffffe 0xffffc0ffcffffff3

def z973 : W := mkw 0x24ed508000850488 0x983fdbedff005005 0xfffffff000ff800f 0xfe7fffffff01f01f

def z974 : W := mkw 0x008079ce24e80000 0xe63fedc497b7f000 0xffffffffffff8000 0xfe3ffffffffff000

def z975 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x00007e0ffffe0000 0x440e3f0002ffc000

def z976 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x00ffffffffff8e01 0xfe3fffc07ffffc0c

def z977 : W := mkw 0x24cd7dee24ed4488 0xee3fedccb7b7f505 0x380e7fffffff8e01 0xe63fff9c33fffc0c

def z978 : W := mkw 0x9200673992007900 0x00860016835a0f60 0xff007fffff007ff0 0xd5ae00bf83fe0fe0

def z979 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe7e0ff8fe7e3f 0xf5bfffbc72f1ccfc

def z980 : W := mkw 0xd3308631d310f952 0x118012f7c8480ff2 0xff00000000007ff0 0x118000ff80000fe0

def z981 : W := mkw 0xda526d3cda525b24 0xf5bf38eee3bb87d8 0x07fe01f007fe01cf 0x2013b843f10fc31c

def z982 : W := mkw 0x24e8000000000000 0x9830d2edfc000000 0xffff800000000000 0xf833fffffc000000

def z983 : W := mkw 0x48520a4748722224 0x75093c3860e5a8b8 0xf8fe7e0ff8fffe3f 0xf7adffbc72f1fcfc

def z984 : W := mkw 0x24e8000000000000 0x1809dbedfc000000 0xffff800000000000 0xf813fffffc000000

def z985 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x0000000fff000000 0xe02fbf0000fe0000

def z986 : W := mkw 0xc9328856c9729276 0x7500362348ada2da 0xc7f1c1ffc7fff1ff 0xffd27f63cd8ff3ff

def z987 : W := mkw 0x49728a474972a276 0x75093e3968e5a8ba 0xfffffe0ff8fffe3f 0xfffffffffef1fcff

def z988 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffff800000000000 0x582fbffffc000000

def z989 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xffffbe00000e7fcf 0xf97ffffffe00cf1f

def z990 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x00f1fffffffff1ce 0xff7fff404ffff313

def z991 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf80e7e0ff8fe0e31 0xe4adb8bc32f1ccec

def z992 : W := mkw 0x000039ce24e80000 0x660fed0000b7f000 0x0000000fff0e0000 0x400fbf0000fec000

def z993 : W := mkw 0x920077b992807900 0x80b600d6835a5f60 0xff007ffffffffff0 0xd7be00ff83ffffe0

def z994 : W := mkw 0x24e8108000800000 0x983fdbedfc005000 0xffff800000ff8000 0xfa3ffffffc01f000

def z995 : W := mkw 0x9200631992003900 0x80b60016835a0a60 0xff007fffff0071f0 0xd5be007f83fe03e0

def z996 : W := mkw 0x9200673992007900 0x80b60016835a0f60 0xff007fffff007ff0 0xc5be003f83fe0fe0

def z997 : W := mkw 0x9200231992003900 0x80b600d6805a0a60 0xff00000fff000030 0x40ae00bf80fe00e0

def z998 : W := mkw 0x008579ce24ed0488 0xe63fed0017b7f005 0x00fffffffffff1cf 0xff7fff407ffff31f

def z999 : W := mkw 0x4110f9ce65f88052 0xe73fed0003b7f092 0x00007fffffff800e 0xe67fff0003fff013

def z1000 : W := mkw 0x00057dee24ed4488 0x660f2d0003b7f505 0x00007fffffffffcf 0x474e3f0003ffff1f

def z1001 : W := mkw 0x000079ce24e80000 0x660f2d0003b7f000 0x00007fffffff8000 0xe61e7f0003fff000

def z1002 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f1fffffff1f1fe 0xfffe7f63cfff33f3

def z1003 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x0000000ffffe0000 0x600fbf0000ffc000

def z1004 : W := mkw 0x24e8508000800000 0x983fdbedff005000 0xfffffff000fffe0f 0xff3fffffff01fc1c

def z1005 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xffff800000000000 0xf83ffffffc000000

def z1006 : W := mkw 0x8000021180003000 0x0000001200480a60 0xff007e0fff007e30 0xd5ae00bf82fe0ce0

def z1007 : W := mkw 0xdb12ef7fdb72fb76 0x6580241203ffaffa 0x00007fffffffffff 0x07c0000003ffffff

def z1008 : W := mkw 0x24e8188424c80000 0x9a3fdbedfc20d000 0xffff8000000e0000 0xf83ffffffc00c000

def z1009 : W := mkw 0x89628a578962b276 0x00090e1b286caa6a 0x3f0fbff03f0f8fc1 0x0a7fc7dfbf7eff0f

def z1010 : W := mkw 0x24cd7dee24ed4488 0xee3fedccb7b7f505 0x38ffffffffffffcf 0xff7fffdc7fffff1f

def z1011 : W := mkw 0x928577b992857d88 0x80b600d6975a5f65 0xffffffffffffffff 0xdffe00ffffffffff

def z1012 : W := mkw 0x48520a4748722224 0x75093c3860e5a8b8 0xf8fe7e0ffffe7e3f 0xf5afbfbc72ffccfc

def z1013 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x000001ffff018000 0x421e7f0001fe3000

def z1014 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00007fffffff8000 0x2613ff0003fff000

def z1015 : W := mkw 0x12007dee36e84900 0xe6bfedc483b7f500 0x00007fffffff8000 0xe63fff0003fff000

def z1016 : W := mkw 0xc1308856c1709052 0x7500362348ada2d2 0xc7f1fffffffff1fe 0xffd27f63cffff3f3

def z1017 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f181ffc70181f0 0xfad27f63cd8e33e3

def z1018 : W := mkw 0xc9728211c912b276 0x1100123b68480afa 0xff00000000000030 0x0080003f800000e0

def z1019 : W := mkw 0x008514a000854488 0x0000c0c014005505 0x00ffc1f000ffffcf 0xbf51c0c07d01ff1f

def z1020 : W := mkw 0x24ed54a000854488 0x9830d2edff005505 0xfffffff000ffffcf 0xff73ffffff01ff1f

def z1021 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff007ffffff1fff0 0xf7be40ff83ff3fe0

def z1022 : W := mkw 0xc9128a57c972b276 0x6500241200edaafa 0x00007e0ffffe7e3f 0x0580000002ffccfc

def z1023 : W := mkw 0x2468000000000000 0x18091b2de8000000 0xff00000000000000 0x00003f3f80000000

def z1024 : W := mkw 0x48520a0548522224 0x01090818206088b8 0x380e3e00380e7e3f 0x01ad809c3270ccfc

def z1025 : W := mkw 0x2468000000000000 0x180fdb2de8000000 0xff00000000000000 0x600fff3f80000000

def z1026 : W := mkw 0x244879ce24e80000 0xee3fed0ca3b7f000 0x38007fffffff8000 0xe63fff1c03fff000

def z1027 : W := mkw 0x9200673992007900 0x008000d6835a0f60 0xff007fffff007ff0 0xd5ac00ff83fe0fe0

def z1028 : W := mkw 0xc9728211c912b276 0x1100123b68480afa 0xfff18000000071fe 0x19c0007fcc0003f3

def z1029 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x00003e0fff0e0000 0x402fbf0002fec000

def z1030 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x00fe7ffffffffe0f 0xf73fff8073fffc1c

def z1031 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xfff1800000000000 0x680e7f3fcc000000

def z1032 : W := mkw 0x24ed108000850488 0x180fdb2dfc005005 0xffff800000ff800f 0x6a4fff3ffc01f01f

def z1033 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff00400fff007030 0xd58e003f80fe00e0

def z1034 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0xc7007fffffff8000 0xf63fff6383fff000

def z1035 : W := mkw 0x000054a000804000 0x803fc9c483005500 0xff007ff000ffffc0 0xf73fffff8301ff00

def z1036 : W := mkw 0x0000694e24680000 0x660f2d0003b7a000 0x00007fffff000000 0x440e3f0003fe0000

def z1037 : W := mkw 0x128575a812854d88 0x80b6c0c497125505 0x00fffff000ffffcf 0xbf71c0c07f01ff1f

def z1038 : W := mkw 0x9285673992057d88 0x80b600d6975a0f65 0xfffffffffff1ffff 0xfffe40ffffff3fff

def z1039 : W := mkw 0x000079ce24e80000 0xe63fed0483b7f000 0xff007fffffff8000 0xe63fff3f83fff000

def z1040 : W := mkw 0x0000294e24680000 0xe63f2d0000b7a000 0x0000000fff000000 0xc03e3f0000fe0000

def z1041 : W := mkw 0x24e8000000000000 0x180fdb2dfc000000 0xffff800000000000 0xf81fff7ffc000000

def z1042 : W := mkw 0x2468798c24c80000 0x9a3fdb2deb32d000 0xff003e00380e0000 0x402fbf3f8270c000

def z1043 : W := mkw 0x000079ce24e80000 0x823fcd000336f000 0x00003ff03f0f8000 0xe23fff00037ef000

def z1044 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff00000fff0071f0 0x518e007f80fe03e0

def z1045 : W := mkw 0x9200273992007900 0x00860016805a0f60 0xff00000fff007ff0 0x418e003f80fe0fe0

def z1046 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f181ffc701f1fe 0x5bd27f63cd8e33f3

def z1047 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff0041ffff000030 0xc49e003f81fe00e0

def z1048 : W := mkw 0xc1308211c110b052 0x1100123348480af2 0xfff1800000007ffe 0x19c000ffcc000ff3

def z1049 : W := mkw 0x2468000000000000 0x983f1bede8000000 0xfffe000000000000 0xf03fbffff0000000

def z1050 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff00000fff000030 0x408e003f80fe00e0

def z1051 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffff8000000071ce 0xf97ffffffc000313

def z1052 : W := mkw 0x0000210800000000 0x803fc90000120000 0x0000000fff000000 0xe03fff0000fe0000

def z1053 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00ff81f000ffffcf 0x3b51c0c07d01ff1f

def z1054 : W := mkw 0x2468000000000000 0x983fdb2de8000000 0xff00000000000000 0x402fbf3f80000000

def z1055 : W := mkw 0x9200231992003900 0x80b600d6805a0a60 0xff007e0fff007e30 0xd5be00ff82fe0ce0

def z1056 : W := mkw 0x008514a000854488 0x0000c0c014005505 0x00fffe0000ffffcf 0xbf61c0c07e01ff1f

def z1057 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff007e0fff000030 0xc4ae003f82fe00e0

def z1058 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x000181ffff0181c0 0x4a5e7f400dfe3303

def z1059 : W := mkw 0x9200631992003900 0x80b60016835a0a60 0xff003e0fff000030 0x40ae003f82fe00e0

def z1060 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf80e7e0ff8fe7e3f 0x45adb8bc32f1ccfc

def z1061 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xfff1fffffff1fffe 0xfffe40ffcfff3ff3

def z1062 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xff0e7ffffffffff1 0xf7bfc0ffb3ffffec

def z1063 : W := mkw 0x920577b992857d88 0x80b600d6835a5f65 0xfff1ffffffffffff 0xfffe40ffcfffffff

def z1064 : W := mkw 0x0000442000004000 0x803000c003000500 0x00fffff000ffffcf 0xbf71c0c07f01ff1f

def z1065 : W := mkw 0xc917def7c9f7f6fe 0x6500241203edffff 0x00007fffffffffff 0x07c0000003ffffff

def z1066 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xff0181f0000181c0 0x4a5e7f7f8d003303

def z1067 : W := mkw 0x24e8000000000000 0x983612edfc000000 0xffff800000000000 0xf83e7ffffc000000

def z1068 : W := mkw 0xb6e8673992007900 0x1889db3b7f5a0f60 0x00ffffffff007ff0 0x2d81ff007ffe0fe0

def z1069 : W := mkw 0xc1108253c130b052 0x6500241200cd2af2 0x00007ffffff1fffe 0x07c0000003ff3ff3

def z1070 : W := mkw 0x24c8294e24680000 0xee3fedccb4b7a000 0x380e000fff000000 0x402fbf9c30fe0000

def z1071 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff007ffffffe7ff0 0xf5bf80ff83ffcfe0

def z1072 : W := mkw 0x24e8000000000000 0x180f1bedfc000000 0xffff800000000000 0xf81e7ffffc000000

def z1073 : W := mkw 0xd3308211d310b952 0x11801237c8480af2 0xff00000000000030 0x0080003f800000e0

def z1074 : W := mkw 0x9205673992057d88 0x80b600d6835a0f65 0xff007fffff007fff 0xd5fe00ff83fe0fff

def z1075 : W := mkw 0x9200063192007900 0x80bfc9d680480f60 0xff00000000007ff0 0xf1bfffff80000fe0

def z1076 : W := mkw 0x000079ce24e80000 0xe636e50003b7f000 0x00007fffffff8000 0xe6127f0003fff000

def z1077 : W := mkw 0xc9128253c932b276 0x6500241200cd2afa 0x000041ffc7f1ffff 0x07c00000018f3fff

def z1078 : W := mkw 0xd3308211d310b952 0x11801237c8480af2 0xfff18000000071fe 0x19c0007fcc0003f3

def z1079 : W := mkw 0x24e8000000000000 0x180fdb2dfc000000 0xff01800000000000 0x480e7f3f8c000000

def z1080 : W := mkw 0x9285673992057d88 0x80b600d6975a0f65 0xff01ffffff007ff0 0xddfe00ff8ffe0fe3

def z1081 : W := mkw 0x4852020148122224 0x11001038604008b8 0xf8fe7e0ff8fe7e3f 0xf5ad80bc72f1ccfc

def z1082 : W := mkw 0x9280673992007900 0x80b600d6975a0f60 0xffffffffff007ff0 0xddbe00fffffe0fe0

def z1083 : W := mkw 0x48d75ea548d766ac 0xf539f8f877e1ddbd 0xf80181fff80181f0 0x4adc787c0df033e3

def z1084 : W := mkw 0x24ed042000054488 0x983fdbedfc000505 0xfffffe0000fe7fcf 0xfd7ffffffe01cf1f

def z1085 : W := mkw 0x0060000000000000 0x10091a2968000000 0xff00000000000000 0x400e3f3f80000000

def z1086 : W := mkw 0x008554a000854488 0x803fc9c497005505 0xfffffff000ffffcf 0xff7fffffff01ff1f

def z1087 : W := mkw 0x00857dee24ed4488 0x6609ed0017b7f505 0x00ffffffffffffcf 0x2f41ff007fffff1f

def z1088 : W := mkw 0xc9128a57c972b276 0x6500241200edaafa 0x0000000fff000030 0x0080000000fe00e0

def z1089 : W := mkw 0x9285673992057d88 0x80b600d6975a0f65 0xfffffffffffe7fff 0xfdff80ffffffcfff

def z1090 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff007e0fff007e30 0xd5ae00bf82fe0ce0

def z1091 : W := mkw 0x24c879ce24e80000 0xee3fedccb7b7f000 0x38ffffffffff8000 0xfe3fffdc7ffff000

def z1092 : W := mkw 0x48520a0548522224 0x6509281820e188b8 0xf80e7e0ff8fe7e3f 0xd5ad80bc32f1ccfc

def z1093 : W := mkw 0x0080000000000000 0x8030c0c014000000 0x00fffff000ffffcf 0xbf71c0c07f01ff1f

def z1094 : W := mkw 0x9200273992007900 0x008600d6805a0f60 0xff0041ffff007ff0 0xd59e00ff81fe0fe0

def z1095 : W := mkw 0x24e8508000800000 0x983fdbedff005000 0xffff81f000018000 0xfa3ffffffd003000

def z1096 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xfffe7e0000fe7e0f 0xf52fbfbff201cc1c

def z1097 : W := mkw 0x2468000000000000 0x983f1bede8000000 0xff00000000000000 0x402e3fbf80000000

def z1098 : W := mkw 0x24e8798c24c80000 0x9a3fdbedff32d000 0xfffffff038ff8000 0xfe3fffffff71f000

def z1099 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff0001ffff007ff0 0x519e00ff81fe0fe0

def z1100 : W := mkw 0x48520a0548522224 0x6509281820e188b8 0x380e7e0ff8fe7e3f 0xe5adb89c32f1ccfc

def z1101 : W := mkw 0x08420a0508422224 0x1009183860608828 0xf8fe7e0ff80e7e31 0xf5adb8bc72f0ccec

def z1102 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00ffbe0000ffffcf 0x3b61c0c07e01ff1f

def z1103 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe7e0ff8fe7e3f 0x15ad80bc72f1ccfc

def z1104 : W := mkw 0x000079ce24e80000 0x660fed0003b7f000 0x00007fffffff8000 0x660fff0003fff000

def z1105 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f181ffc7f181fe 0x6ad27f63cd8f33f3

def z1106 : W := mkw 0x49728a474972a276 0x75093e3968e5a8ba 0xf8fe7e0ff8fe7e3f 0xf5adbfbc72f1ccfc

def z1107 : W := mkw 0x0000000000000000 0x000f090480000000 0xff00000000000000 0x400e3f3f80000000

def z1108 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe7ffff8ffffff 0xf7edb8bc73f1ffff

def z1109 : W := mkw 0x9200273992007900 0x008600d6805a0f60 0xff007e0fff007ff0 0xd5ae00ff82fe0fe0

def z1110 : W := mkw 0x008575a800854488 0x8036c0c017125505 0x00fffff038ffffcf 0xbf7dc0c07f71ff1f

def z1111 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xff0e000000000000 0xd03fbfffb0000000

def z1112 : W := mkw 0x0080652800004000 0x803fc9c017120500 0x00ffffffff007fc0 0xfd3fffc07ffe0f00

def z1113 : W := mkw 0x004079ce24e80000 0xe63fed0823b7f000 0x380e7fffffff8000 0xe63fff9c33fff000

def z1114 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0x38fe7e0ff8fe7e3f 0x25adb89c72f1ccfc

def z1115 : W := mkw 0x000039ce24e80000 0xe63fed0000b7f000 0x0000000fffff8000 0xe23fff0000fff000

def z1116 : W := mkw 0x00057dee24ed4488 0xe63fed0003b7f505 0x00f1ffffffffffcf 0xff7fff404fffff1f

def z1117 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff003e0fff007ff0 0x51ae00ff82fe0fe0

def z1118 : W := mkw 0xd310fffff7f8f952 0x6780241203fffff2 0x00007ffffffffffe 0x07c0000003fffff3

def z1119 : W := mkw 0x24e8000000000000 0x180012edfc000000 0xffff800000000000 0x38007ffffc000000

def z1120 : W := mkw 0x24e8000000000000 0x983f1bedfc000000 0xffff800000000000 0xd83e3ffffc000000

def z1121 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff007fffff000e30 0xc4be00bf83fe0ce0

def z1122 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00007ffffffff1c0 0xf73fff4003fff300

def z1123 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x000041fffff18000 0xe61e7f0001ff3000

def z1124 : W := mkw 0x0000610800000000 0x8036000003120000 0x00007fffff000000 0xe43e7f0003fe0000

def z1125 : W := mkw 0x0000004200200000 0x6400240000852000 0x00007ffffff18000 0xe63e7f0003ff3000

def z1126 : W := mkw 0xda127ffffefa7b24 0x6780241203fffff8 0x00007fffffffffff 0x0780000003fffffc

def z1127 : W := mkw 0x48520a0548522224 0x6509281820e188b8 0x38fe7e0ff8fe7e3f 0xb5ad809c72f1ccfc

def z1128 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7f1ffffc7f1fffe 0xfff27fe3cf8f3ff3

def z1129 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xff01ffffffffffff 0xdffe40ff8fffffff

def z1130 : W := mkw 0x920577b992857d88 0x80b600d6835a5f65 0xff007fffff01fff0 0xd7fe00ff83fe3fe3

def z1131 : W := mkw 0x401079ce64f80000 0xe73fed0003b7f090 0x00007ffffffff03e 0xe7bfff0003fff0f0

def z1132 : W := mkw 0x0000294e24680000 0x660f2d0480b7a000 0xff00000fff000000 0x400e3f3f80fe0000

def z1133 : W := mkw 0x0000614a00200000 0x6400240003972000 0x00007ffffff18000 0xe6127f0003ff3000

def z1134 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xfffffff000ff8e01 0xfe3fffffff01fc0c

def z1135 : W := mkw 0x000058c600e00000 0xe439ec0003a5f000 0x00007fffffff8000 0xe63fff0003fff000

def z1136 : W := mkw 0x008514a000854488 0x0000c00014005505 0x00ff800000ffffcf 0x2b41c0007c01ff1f

def z1137 : W := mkw 0x0020000000000000 0x10061225c8000000 0xff00000000000000 0x400e3f3f80000000

def z1138 : W := mkw 0x481279ce6cfa0224 0xe73fed0003b7f098 0x00007fffffff800f 0xe63fff0003fff01c

def z1139 : W := mkw 0x24e8610800000000 0x983fdbedff120000 0xffffbe0038000000 0xf83ffffffe700000

def z1140 : W := mkw 0x0020442000004000 0x903612e5cb000500 0xfff1fff000f1ffce 0xff7e7fffcf013f13

def z1141 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff003fffff000ff0 0x40be00ff83fe0fe0

def z1142 : W := mkw 0x8000021180003000 0x0000001200480a60 0xff0041ffff0071f0 0xd59e007f81fe03e0

def z1143 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00007e0ffffe0000 0xe42fbf0002ffc000

def z1144 : W := mkw 0x9200631992003900 0x80b60016835a0a60 0xff0001ffff000030 0x409e003f81fe00e0

def z1145 : W := mkw 0x6cba0a0548522224 0xed36e3d59ce188b8 0x0701fe0ff8fe7e3f 0x0d9247438ef1ccfc

def z1146 : W := mkw 0xdb728631db12fb76 0x118012ffe8480ffa 0xffff800000007fff 0x19c000fffc000fff

def z1147 : W := mkw 0x08420a0508422224 0x0009081820608828 0xf80e3e0ff80e0e31 0x40ad80bc32f0ccec

def z1148 : W := mkw 0xc9f78631c917f6fe 0x110012fb7c480fff 0xffff800000007fff 0x19c000fffc000fff

def z1149 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0xc0007ffffffff030 0xf7bfff2003fff0e0

def z1150 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00007fffff018000 0xc63e7f0003fe3000

def z1151 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fffe0ff8fffe3f 0xffedf8bc7ef1fcff

def z1152 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00fffffff8ffffcf 0xff7dc0c07ff1ff1f

def z1153 : W := mkw 0x0060000000000000 0x903fdb2968000000 0xffff800000000000 0xf83ffffffc000000

def z1154 : W := mkw 0x0000656a00204000 0xe43624c003972500 0x00f1fffffff1ffce 0xff7e7fc04fff3f13

def z1155 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xfff1ffffff007ff0 0xfdbe40ffcffe0fe0

def z1156 : W := mkw 0x008079ce24e80000 0xe63fedc017b7f000 0x00fffffffffff1ce 0xff7fffc07ffff313

def z1157 : W := mkw 0x24e8000000000000 0x18091bedfc000000 0xffff800000000000 0x18003ffffc000000

def z1158 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff0001ffff0001f0 0x409e007f81fe03e0

def z1159 : W := mkw 0x008079ce24e80000 0xe63fedc017b7f000 0x00fffffffffffe0f 0xff3fffc07ffffc1c

def z1160 : W := mkw 0x0000694e24680000 0xe63f2d0003b7a000 0x00007ffffff18000 0xe63e7f0003ff3000

def z1161 : W := mkw 0x0060000000000000 0x10091a2968000000 0xfffe000000000000 0xf02fbfbff0000000

def z1162 : W := mkw 0xd310e77bd330f952 0xe5b024d203df2ff2 0x00f1fffffff1fffe 0xbff040c04fff3ff3

def z1163 : W := mkw 0x000018c624e80000 0x6609ed0000a5f000 0x00007fffffff8000 0xe63fff0003fff000

def z1164 : W := mkw 0x008554a000854488 0x8030c0c017005505 0x00fffff000ffffcf 0xff73ffc07f01ff1f

def z1165 : W := mkw 0x24e8000000000000 0x9836d3edfc000000 0xffff800000000000 0xf8127ffffc000000

def z1166 : W := mkw 0x0000508000800000 0x8030c00003005000 0x00fffff000ffffcf 0xbf71c0c07f01ff1f

def z1167 : W := mkw 0xc9328211c912b276 0x1100123348480afa 0xc7f1800000007fff 0x19c00063cc000fff

def z1168 : W := mkw 0x24e8610800000000 0x983fdbedff120000 0xffff81f007000000 0xf83ffffffd0e0000

def z1169 : W := mkw 0x0020000000000000 0x1000122148000000 0xfff1800000000000 0xf83e7fffcc000000

def z1170 : W := mkw 0x8000611880001000 0x803600c6831a0240 0xff007fffff0071f0 0xd5be00ff83fe03e0

def z1171 : W := mkw 0x000079ce24e80000 0x6609ed0003b7f000 0x00007fffffff8000 0xe613ff0003fff000

def z1172 : W := mkw 0x00807dee24e84000 0xe63fedc017b7f500 0x00ffffffffffffc0 0xff3fffc07fffff00

def z1173 : W := mkw 0x008579ce24ed0488 0xe63fedc017b7f005 0x00ffffffffff800f 0xfe7fffc07ffff01f

def z1174 : W := mkw 0x8000021180003000 0x0000001200480a60 0xff00000fff000030 0x408e003f80fe00e0

def z1175 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xfffe7fffff007fff 0xd5be00fff3fe0ffc

def z1176 : W := mkw 0x008554a000854488 0x8030c00017005505 0x00fffff000ffffcf 0xaf71c0007f01ff1f

def z1177 : W := mkw 0xc9128a57c972b276 0x6500241200edaafa 0x000041fffff1f1fe 0x07c0000001ff33f3

def z1178 : W := mkw 0xc9f7d6b1c997f6fe 0x9130d2fb7f485fff 0xfffffff000ffffff 0xbff1c0ffff01ffff

def z1179 : W := mkw 0x9200673992007900 0x00860016835a0f60 0xff007fffff007ff0 0xd59e007f83fe0fe0

def z1180 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x000001ffff018000 0xe23fff0001fe3000

def z1181 : W := mkw 0xb668021192003900 0x1880123fe8480a60 0xff00000000000030 0x0080003f800000e0

def z1182 : W := mkw 0x9200273992007900 0x008600d6805a0f60 0xff00000fff000e30 0x408e00bf80fe0ce0

def z1183 : W := mkw 0x00a0000000000000 0x9036d2e5dc000000 0xffff800000000000 0xf83ffffffc000000

def z1184 : W := mkw 0x0000084600600000 0xe43fed0000a5a000 0x00007fffffff8000 0xe63fff0003fff000

def z1185 : W := mkw 0x00007dee24e84000 0xe63fedc003b7f500 0x00fe7fffffffffcf 0xf73fffc073ffff1c

def z1186 : W := mkw 0xc1308052c1309052 0x11001623480c22d2 0xc7f181f00701f1fe 0xfbd27f63cd0e33f3

def z1187 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00f07ffffffff00e 0xf73fff0043fff010

def z1188 : W := mkw 0x48520a476c7a2224 0x77093d3860e5a8b8 0xf8fe7e0ff8fe7e3f 0xf5adbfbc72f1ccfc

def z1189 : W := mkw 0x0040000000000000 0x903fd9ece0000000 0xfffe000000000000 0xf03ffffff0000000

def z1190 : W := mkw 0x008575a8248d4488 0x8236c1c017125505 0x00fffff000ffffcf 0xbf71c0c07f01ff1f

def z1191 : W := mkw 0x8000021180003000 0x803600d680480a60 0xff007fffff007ff0 0xd5be00ff83fe0fe0

def z1192 : W := mkw 0x24c879ce24e80000 0xee3fedccb7b7f000 0xff0e7fffffff8000 0xf63fffffb3fff000

def z1193 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xff0e000000000000 0x402fbfbfb0000000

def z1194 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x0001ffffffffffcf 0xef7fff400fffff1f

def z1195 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xff0181ffff0181f0 0x4ade407f8dfe33e3

def z1196 : W := mkw 0x9200673992007900 0x00860016835a0f60 0xff0001ffff0001f0 0x408e003f81fe03e0

def z1197 : W := mkw 0x24ed042000054488 0x983fdbedfc000505 0xffff8000000001c0 0xf87ffffffc000303

def z1198 : W := mkw 0x000079ce24e80000 0x660f2d0003b7f000 0x00003e0fff0e0000 0x400e3f0002fec000

def z1199 : W := mkw 0x24a8000000000000 0x9836d3e5dc000000 0xfff1800000000000 0xf83e7fffcc000000

def z1200 : W := mkw 0x0000694e24680000 0xe63f2d0003b7a000 0x000001ffff000000 0x401e3f0001fe0000

def z1201 : W := mkw 0x24ed442000054488 0x983fdbedff000505 0xfffffff000007fcf 0xfd7fffffff000f1f

def z1202 : W := mkw 0x9200631992003900 0x80b600d6835a0a60 0xff007fffff000030 0xd4be00ff83fe00e0

def z1203 : W := mkw 0x8000463180007000 0x803000d203480f60 0xff007fffff007ff0 0xd5be00ff83fe0fe0

def z1204 : W := mkw 0x000079ce24e80000 0x6600240003b7f000 0x00007fffffff8000 0x46023f0003fff000

def z1205 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0xf8007fffffff8000 0xf63fffbc03fff000

def z1206 : W := mkw 0xedfa8211c912b276 0x190012fffc480afa 0xffff800000007fff 0x19c000fffc000fff

def z1207 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffffc1f000f18000 0xfe3ffffffd013000

def z1208 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf80e7e0ff80e7e31 0xd5adb8bc32f0ccec

def z1209 : W := mkw 0x64f8000040100000 0x993fdbedfc000090 0xffff80000000703e 0xf9bffffffc0000f0

def z1210 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xffffffffff0e7ff1 0xfdbfc0fffffecfec

def z1211 : W := mkw 0x24e8000000000000 0x180f1bedfc000000 0xffff800000000000 0xf82fbffffc000000

def z1212 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe7ffff8fffe3f 0xf7bdf8bc73f1fcfc

def z1213 : W := mkw 0x2468508000800000 0x983fdb2deb005000 0xff007ff000ff8000 0xe63fff3f8301f000

def z1214 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffff800000000000 0x382dfffffc000000

def z1215 : W := mkw 0x9280673992007900 0x80b6c0d6975a0f60 0xff01ffffff007ff0 0xddbe40ff8ffe0fe0

def z1216 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff0041ffff0071f0 0x458e003f81fe03e0

def z1217 : W := mkw 0x008554a000854488 0x8036c0c017005505 0x00fffff000ffffcf 0xff7fc0c07f01ff1f

def z1218 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x0001ffffffffffc0 0xff7fffc00fffff03

def z1219 : W := mkw 0x8000631980003000 0x80360012035a0a60 0xff007fffff007ff0 0xd5be00ff83fe0fe0

def z1220 : W := mkw 0x00a554a000854488 0x9036d2e5df005505 0xfffffff000ffffcf 0xff7fffffff01ff1f

def z1221 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc701c1ffc701f1f0 0xdfd27f638d8e33e3

def z1222 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fffe0ff8fe7fff 0xfdedb8fc7ef1cfff

def z1223 : W := mkw 0x9280673992007900 0x80b6c0d6975a0f60 0xfffffffffffe7fff 0xfdbfc0ffffffcffc

def z1224 : W := mkw 0x000039ce24e80000 0x660fed0000b7f000 0x0000000fff018000 0x420e7f0000fe3000

def z1225 : W := mkw 0x008554a000854488 0x000000c017005505 0x00fffff000ffffcf 0xbf6180c07f01ff1f

def z1226 : W := mkw 0x920577b992857d88 0x80b600d6835a5f65 0xfffe7fffffffffff 0xf7ff80fff3ffffff

def z1227 : W := mkw 0xb668063192007900 0x188012ffe8480f60 0xff00000000007ff0 0x118000ff80000fe0

def z1228 : W := mkw 0x0000294e24680000 0x6600240000b7a000 0x000041fffff18000 0xe6127f0001ff3000

def z1229 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff007ffffff1fffe 0xd7fe00ff83ff3ff3

def z1230 : W := mkw 0x00852d6e246d4488 0x660f2dc014b7a505 0x00ff800fff007fcf 0x594e3fc07cfe0f1f

def z1231 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x0000000ffff18000 0x620e7f0000ff3000

def z1232 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff007fffff007ff0 0xf5be7fff83fe0fe0

def z1233 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xff01800000000000 0x481e7f7f8c000000

def z1234 : W := mkw 0x4972884649728276 0x75093e2968a5a09a 0x0000000000000000 0x00003f0000000000

def z1235 : W := mkw 0x24e8000000000000 0x180fdb2dfc000000 0xff0e000000000000 0x400fbf3fb0000000

def z1236 : W := mkw 0xd3b5d6b1d395fdda 0x91b0d2f7df485ff7 0xfffffff000ffffff 0xbff1c0ffff01ffff

def z1237 : W := mkw 0x008554a000854488 0x0000c0c017005505 0x00fffff000ffffcf 0x3f41c0c07f01ff1f

def z1238 : W := mkw 0x12857fad36cd6d88 0x82bfc9d49772dd25 0x380e3e00380e0e01 0x002d809c3270cc0c

def z1239 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00007ffffffff1ce 0xe77fff0003fff313

def z1240 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff0041ffff0071f0 0xd59e007f81fe03e0

def z1241 : W := mkw 0x00057dee24ed4488 0xe63fed0003b7f505 0x00fe7fffffffffcf 0xf77fff8073ffff1f

def z1242 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00007ffffffffe0f 0xe73fff0003fffc1c

def z1243 : W := mkw 0x24e8080400400000 0x983fdbedfc208000 0xffffbe00380e0000 0xf83ffffffe70c000

def z1244 : W := mkw 0x0000294e24680000 0xe63fed0000b7a000 0x0000000fff000000 0x402fbf0000fe0000

def z1245 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xff00000000000000 0xe01e7f3f80000000

def z1246 : W := mkw 0x4972884649728276 0x75093e2968a5a09a 0x00fe000000fe000f 0x2001bf007001c01c

def z1247 : W := mkw 0xc9728211c912b276 0x1100123b68480afa 0xfffffff000ffffff 0xbff1c0ffff01ffff

def z1248 : W := mkw 0x2468000000000000 0x983f1b2de8000000 0xff00000000000000 0xc03e3f3f80000000

def z1249 : W := mkw 0x0000798c24c80000 0x823fc9000332d000 0x00007fffff0e0000 0xe43fff0003fec000

def z1250 : W := mkw 0xdb72ab5fdb72bb76 0x758f3e3fe8ffaafa 0xff00000fff000030 0x408e3f3f80fe00e0

def z1251 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00f1ffffffff8000 0xfe3fff404ffff000

def z1252 : W := mkw 0x00007dee24e84000 0xe63fed0003b7f500 0x00007fffffffffc0 0xe73fff0003ffff00

def z1253 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00007fffffff8000 0x461e7f0003fff000

def z1254 : W := mkw 0x920077b992807900 0x80b6c0d6835a5f60 0xff007fffff01fff0 0xd7be40ff83fe3fe0

def z1255 : W := mkw 0x497298c66dfa8276 0x7709ff2968a5f09a 0x00ff800000ff800f 0x2a41ff007c01f01f

def z1256 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xfffe7e0ffffe7e3f 0xf5af80bff2ffccfc

def z1257 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x00ffffffffff8e0f 0xee7fff807ffffc1f

def z1258 : W := mkw 0x9200673992007900 0x00860016835a0f60 0xff003e0fff000e30 0x408e003f82fe0ce0

def z1259 : W := mkw 0x00e554a000854488 0x9039dae97f005505 0xfffffff000ffffcf 0xff7fffffff01ff1f

def z1260 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00007ffffffffe00 0xf73fff8003fffc00

def z1261 : W := mkw 0x920577b992857d88 0x80b6c0d6835a5f65 0xff007fffffffffff 0xf7ffc0ff83ffffff

def z1262 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffffc00000f0700e 0xfd3ffffffc010010

def z1263 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xfffe000000000000 0x600fbf3ff0000000

def z1264 : W := mkw 0x9200231992003900 0x008600d6805a0a60 0xff00000fff000030 0x508e00ff80fe00e0

def z1265 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xff01fffffffffff0 0xffffc0ff8fffffe3

def z1266 : W := mkw 0x000079ce24e80000 0xe636240003b7f000 0x00007fffffff8000 0xe63e7f0003fff000

def z1267 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xfff1c1f000f1f1ce 0xff5e7f7fcd013313

def z1268 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xfffe000000000000 0x500e3fbff0000000

def z1269 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00fe7fffffff800f 0xe63fff0073fff01c

def z1270 : W := mkw 0x0000020100002000 0x0000001000400820 0xf80e7e0ff80e7e31 0xd5ad80bc32f0ccec

def z1271 : W := mkw 0xd310e77bd330f952 0x6580241203df2ff2 0x00007fffff007ff0 0x0580000003fe0fe0

def z1272 : W := mkw 0xc9728211c912b276 0x1100123b68480afa 0xfffe000000007e3f 0x118000bff0000cfc

def z1273 : W := mkw 0x48520a4748722224 0x75093c3860e5a8b8 0xf8ffffffffffffff 0xfffffffc7fffffff

def z1274 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff007fffff0001f0 0xc4be007f83fe03e0

def z1275 : W := mkw 0x24e8610800000000 0x983612edff120000 0xffffffffff000000 0xdc3e00fffffe0000

def z1276 : W := mkw 0x24e8000000000000 0x180f1bedfc000000 0xff0e000000000000 0x400e3fbfb0000000

def z1277 : W := mkw 0x48720a0548522224 0x75093a3968e188b8 0xfffffffff8ffffff 0xfffffffffff1ffff

def z1278 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xfffffe0000fe7e0f 0xfd3ffffffe01cc1c

def z1279 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc701c1ffc7f181f0 0xeed27f638d8f33e3

def z1280 : W := mkw 0x0000000000000000 0x803600c480000000 0xff00000000000000 0xf03e7fff80000000

def z1281 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x000001ffffff8000 0x621fff0001fff000

def z1282 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe7ffff8fe7fff 0xf5bdb8fc73f1cffc

def z1283 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff007fffff007ff0 0x45ae00bf83fe0fe0

def z1284 : W := mkw 0x9200231992003900 0x80b600d6805a0a60 0xff00000fff000030 0x409e007f80fe00e0

def z1285 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xff0e7fffffffffff 0xd7ff80ffb3ffffff

def z1286 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xff0e7fffff0e7ff1 0xd5bf80ffb3fecfec

def z1287 : W := mkw 0x00007dee24e84000 0xe63fedc003b7f500 0x00f1ffffffffffce 0xff7fffc04fffff13

def z1288 : W := mkw 0x49728a054952a276 0x75093a3968e188ba 0xf8fffe0ff8fe7e3f 0xfdedb8bc7ef1ccff

def z1289 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0x07f1c1ffc7f1f1fe 0x2fd27f43cd8f33f3

def z1290 : W := mkw 0x0060000000000000 0x10091a2968000000 0xfffffff000ffffcf 0xff7fffffff01ff1f

def z1291 : W := mkw 0x24ed000000050488 0x983fdbedfc000005 0xffff80000000000f 0xf87ffffffc00001f

def z1292 : W := mkw 0x2468000000000000 0x983f1bede8000000 0xff00000000000000 0x401e3f7f80000000

def z1293 : W := mkw 0x24e8798c24c80000 0x9a3fdbedff32d000 0xffffffffff0e0000 0xfc3ffffffffec000

def z1294 : W := mkw 0x48520a0548522224 0x11091838606088b8 0xf8fe7e0038fe7e3f 0xb5ad80bc7271ccfc

def z1295 : W := mkw 0x0000294e24680000 0xe63fed0000b7a000 0x00007e0ffffe0000 0xe43fff0002ffc000

def z1296 : W := mkw 0x24e8508000800000 0x983fdbedff005000 0xffffbe00000e0000 0xf83ffffffe00c000

def z1297 : W := mkw 0x9220063192007900 0x108012f7c8480f60 0xfff1800000007ff0 0x198000ffcc000fe0

def z1298 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x0001ffffffff81c0 0xee7fff400ffff303

def z1299 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe3e0ff8fe0e3f 0x60adb8bc72f1ccfc

def z1300 : W := mkw 0x08420a0508422224 0x6409281820e18828 0xf80e7e0ff8fe7e31 0xf5adb8bc32f1ccec

def z1301 : W := mkw 0x24ed14a000854488 0x983fdbedfc005505 0xffff800000ffffcf 0xfb7ffffffc01ff1f

def z1302 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffffc1ffc7000000 0xfc3ffffffd8e0000

def z1303 : W := mkw 0x00e0000000000000 0x9039dae97c000000 0xffff800000000000 0xf83ffffffc000000

def z1304 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00003fffff0f8000 0x423fff0003fef000

def z1305 : W := mkw 0x24e8042000004000 0x983fdbedfc000500 0xffff800000007fc0 0xf93ffffffc000f00

def z1306 : W := mkw 0x24e8000000000000 0x883fcbcdbc000000 0x3f0f800000000000 0xe83fffdfbc000000

def z1307 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xfffe7fffff007ff0 0xf5bf80fff3fe0fe0

def z1308 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x0000000fff000000 0xe01e7f0000fe0000

def z1309 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc7ffc1ffc7fff1ff 0xffd3ff63fd8ff3ff

def z1310 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffff800000007e0f 0xf93ffffffc000c1c

def z1311 : W := mkw 0x0000610800000000 0x803f090003120000 0x00007fffff000000 0xc43e3f0003fe0000

def z1312 : W := mkw 0x24e8442000004000 0x983fdbedff000500 0xffffbe0000000e00 0xf83ffffffe000c00

def z1313 : W := mkw 0x0000214a00200000 0x6406240000972000 0x000041fffff18000 0xe61e7f0001ff3000

def z1314 : W := mkw 0xd3308631d310f952 0x1180123348480ff2 0xc7f1800000007ffe 0x19c00063cc000ff3

def z1315 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffff800000000000 0x682fffbffc000000

def z1316 : W := mkw 0x000071ca24a80000 0xe636e50003977000 0x00007ffffff18000 0xe63e7f0003ff3000

def z1317 : W := mkw 0x0060000000000000 0x1000122968000000 0xffff800000000000 0xf8127ffffc000000

def z1318 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe7ffffffe7e3f 0xf5bfb8bc73ffccfc

def z1319 : W := mkw 0x24e8000000000000 0x180f1b2dfc000000 0xffff800000000000 0x480e3f3ffc000000

def z1320 : W := mkw 0x24e8000000000000 0x9839dbedfc000000 0xffff800000000000 0xb831fffffc000000

def z1321 : W := mkw 0xd3108673d330f952 0x6580241200cd2ff2 0x000041ffc7f1fffe 0x07c00000018f3ff3

def z1322 : W := mkw 0x000079ce24e80000 0xe63fedc483b7f000 0x07007fffffff8000 0xe63fff4383fff000

def z1323 : W := mkw 0x48520a4748722224 0x75093c3860e5a8b8 0xf8fe7ffffffffe3f 0xf7adb8bc73fffcfc

def z1324 : W := mkw 0x9200273992007900 0x008600d6805a0f60 0xff00000fff0001f0 0x408e007f80fe03e0

def z1325 : W := mkw 0x920077b9b6887900 0x82b6c1d6835a5f60 0xff007fffff007ff0 0xd5be00ff83fe0fe0

def z1326 : W := mkw 0x000079ce24e80000 0x660f2d0003b7f000 0x00007fffffff8000 0xe62fbf0003fff000

def z1327 : W := mkw 0x48520a0548522224 0x11091838606088b8 0xf8fe7e0ff80e7e3f 0xd5ad80bc72f0ccfc

def z1328 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xfffffe0000007e00 0xfd3ffffffe000c00

def z1329 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffff800000f1800e 0xfa7ffffffc013013

def z1330 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x00ffffffffff81cf 0xee7fff407ffff31f

def z1331 : W := mkw 0x24e8442000004000 0x983fdbedff000500 0xfffffff000f1ffce 0xff7fffffff013f13

def z1332 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x000e7fffffffffc1 0xf73fffc033ffff0c

def z1333 : W := mkw 0x24e8000000000000 0x1809dbedfc000000 0xffff800000000000 0xf82dfffffc000000

def z1334 : W := mkw 0x48720a0548522224 0x75093a3968e188b8 0xfffffe0ff8fe7e3f 0xfdadb8fffef1ccfc

def z1335 : W := mkw 0x0020000000000000 0x903fdbe5c8000000 0xfff1800000000000 0xf83fffffcc000000

def z1336 : W := mkw 0x008554a000854488 0x8036c0c497005505 0x38fffff000ffffcf 0xbf7dc0dc7f01ff1f

def z1337 : W := mkw 0x008079ce24e80000 0xe63fed0017b7f000 0x00ffffffffff8000 0xee3fff007ffff000

def z1338 : W := mkw 0x0000690c00400000 0xe43fe90003b38000 0x00007ffffffe0000 0xe43fff0003ffc000

def z1339 : W := mkw 0x24a8000000000000 0x883fcbc59c000000 0xff01800000000000 0xf83fffff8c000000

def z1340 : W := mkw 0x00057dee24ed4488 0xe63fedc003b7f505 0x00007fffffffffcf 0xf77fffc003ffff1f

def z1341 : W := mkw 0x084279ce2cea0224 0xe63fed0823b7f008 0x000e7fffffff8001 0xe63fff0033fff00c

def z1342 : W := mkw 0xc997def7c9f7f6fe 0xe530e4d217edffff 0x00ffffffffffffff 0xbff1c0c07fffffff

def z1343 : W := mkw 0x920077b992807900 0x80b6c0d6835a5f60 0xfffe7fffffffffff 0xf7bfc0fff3fffffc

def z1344 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff00000fff000030 0xd0ae00bf80fe00e0

def z1345 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xffffbe0000ff8e0f 0xfa7ffffffe01fc1f

def z1346 : W := mkw 0x000079ce24e80000 0x66092c0003b7f000 0x00007fffffff8000 0xe63fff0003fff000

def z1347 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xfff1800000000000 0x580e3f7fcc000000

def z1348 : W := mkw 0x36e8652812004900 0x98bfdbedff120500 0xffff800000000000 0xf83ffffffc000000

def z1349 : W := mkw 0x928077b992807900 0x80b6c0d6975a5f60 0xfffffffffffffff0 0xffbfc0ffffffffe0

def z1350 : W := mkw 0x0000694e24680000 0xe63fed0003b7a000 0x00007fffff000000 0xe43fff0003fe0000

def z1351 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe3e0ff80e0e31 0xf0adb8bc72f0ccec

def z1352 : W := mkw 0x928577b992857d88 0x80b6c0d6975a5f65 0xffffffffff01ffff 0xdffe40fffffe3fff

def z1353 : W := mkw 0x24e8000000000000 0x180f1bedfc000000 0xff01800000000000 0x480e3f7f8c000000

def z1354 : W := mkw 0x00857dee24ed4488 0xe63fedc017b7f505 0x00ffffffffff81c0 0xfe7fffc07ffff303

def z1355 : W := mkw 0x9200231992003900 0x00860016805a0a60 0xff007e0fff007e30 0x458e003f82fe0ce0

def z1356 : W := mkw 0xb6ed56b192857d88 0x98b0d2ffff485f65 0xfffffff000ffffff 0xbff1c0ffff01ffff

def z1357 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xfff0000000000000 0xf00e3f3fc0000000

def z1358 : W := mkw 0x9200231992003900 0x80b60016805a0a60 0xff00000fff000030 0xc0be003f80fe00e0

def z1359 : W := mkw 0x008575a800854488 0x8036c0c017125505 0x00fffff007ffffcf 0xbf73c0c07f0fff1f

def z1360 : W := mkw 0x008079ce24e80000 0xe63fedc017b7f000 0x0001ffffffff8000 0xee3fff400ffff000

def z1361 : W := mkw 0x9280673992007900 0x80b6c0d6975a0f60 0xff0e7fffff007ff0 0xd5bf80ffb3fe0fe0

def z1362 : W := mkw 0x9200673992007900 0x80b600d6835a0f60 0xfff1ffffff007ffe 0xddfe00ffcffe0ff3

def z1363 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xfffffe0ff8000000 0xfc3ffffffef00000

def z1364 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00f1ffffffff800e 0xee7fff004ffff013

def z1365 : W := mkw 0x24ed108000850488 0x983fdbedfc005005 0xfffffe0000fffe0f 0xff7ffffffe01fc1f

def z1366 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x000041ffff000000 0xc41e3f0001fe0000

def z1367 : W := mkw 0x24ed54a000854488 0x9839dbedff005505 0xfffffff000ffffcf 0xbf71ffffff01ff1f

def z1368 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xff00000000000000 0xe02fbf3f80000000

def z1369 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00fe7fffffff8000 0xf63fff8073fff000

def z1370 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x000041fffff18000 0x460e3f0001ff3000

def z1371 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xffff800000000000 0xf83ffffffc000000

def z1372 : W := mkw 0x24ed14a000854488 0x1809dbedfc005505 0xffff800000ffffcf 0x3b41fffffc01ff1f

def z1373 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xffff800000fe000f 0xf83ffffffc01c01c

def z1374 : W := mkw 0x2468000000000000 0x180f1b2de8000000 0xff00000000000000 0xd02e3fbf80000000

def z1375 : W := mkw 0x49728a474972a276 0x75093e3968e5a8ba 0xf8fffffff8ffffff 0xfffdfffc7ff1ffff

def z1376 : W := mkw 0x24e8442000004000 0x983fdbedff000500 0xfffffff000fe7fcf 0xfd3fffffff01cf1c

def z1377 : W := mkw 0x2468000000000000 0x180f1bede8000000 0xff00000000000000 0x500e3fff80000000

def z1378 : W := mkw 0x008554a000854488 0x8030c0c017005505 0xf8fffff000ffffcf 0xff7dc0fc7f01ff1f

def z1379 : W := mkw 0x008575a800854488 0x803fc9c017125505 0x00ffffffffffffcf 0xff7fffc07fffff1f

def z1380 : W := mkw 0x2448294e24680000 0x6e0f2d0ca0b7a000 0x3800000fff000000 0x400e3f1c00fe0000

def z1381 : W := mkw 0x2cea080408420224 0x983fdbedfc208008 0xffff8000000e0001 0xf83ffffffc00c00c

def z1382 : W := mkw 0x008539ce24ed0488 0x660fed0014b7f005 0x00ff800fffff800f 0x6a4fff007cfff01f

def z1383 : W := mkw 0x9200673992007900 0x80bfc912035a0f60 0x00007fffff007ff0 0xe5bfff0003fe0fe0

def z1384 : W := mkw 0x8120805281209052 0x64002603088d2242 0xc701c1ffc7f1f1f0 0xffd27f638d8f33e3

def z1385 : W := mkw 0x008575a800854488 0x8030c0c017125505 0x00ffffffffffffcf 0xbf71c0c07fffff1f

def z1386 : W := mkw 0x0085042000054488 0x000000c014000505 0x00fffff000ffffcf 0xbf71c0c07f01ff1f

def z1387 : W := mkw 0x00057dee24ed4488 0x6600240003b7f505 0x00f1ffffffffffcf 0xff527f404fffff1f

def z1388 : W := mkw 0x000079ce24e80000 0xe63fedc003b7f000 0x00007fffffff8000 0xf63fffc003fff000

def z1389 : W := mkw 0x0000294e24680000 0x660f2d0000b7a000 0x00007fffffff8000 0xe63fff0003fff000

def z1390 : W := mkw 0x0000210800000000 0x000f090000120000 0x0000000fff000000 0x400e3f0000fe0000

def z1391 : W := mkw 0x000079ce24e80000 0xe63fed0003b7f000 0x00007fffffff8000 0x262dff0003fff000

def z1392 : W := mkw 0xc1308052c1309052 0x75003623488d22d2 0xc701c1ffc7f1f1fe 0x4fd27f638d8f33f3

def z1393 : W := mkw 0x808556b180857488 0x8030c0d217485f65 0xffffffffffffffff 0xffffc0ffffffffff

def z1394 : W := mkw 0x24ed54a000854488 0x983fdbedff005505 0xffffc1f000f1f1ce 0xff7ffffffd013313

def z1395 : W := mkw 0x24c879ce24e80000 0xee3fed0837b7f000 0x000e7fffffff8000 0xe63fff0033fff000

def z1396 : W := mkw 0x24e8000000000000 0x983fdbedfc000000 0xfffffe0000fe0000 0xfc3ffffffe01c000

def z1397 : W := mkw 0x920077b992807900 0x80b6c0d6835a5f60 0xff007fffff0e7ff0 0xd5bf80ff83fecfe0

def z1398 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fe3e0038fe7e3f 0x31adb8bc7271ccfc

def z1399 : W := mkw 0x6cfa18c66cfa0224 0x7f09ff297ca5f098 0x00ff800000ff800f 0x2a01ff007c01f01c

def z1400 : W := mkw 0x48720a4748722224 0x75093e3968e5a8b8 0xfffffffffffffe3f 0xffbffffffffffcfc

def z1401 : W := mkw 0x24e8508000800000 0x983fdbedff005000 0xfffffff000fff1ce 0xff7fffffff01f313

def z1402 : W := mkw 0x48520a0548522224 0x7509383860e188b8 0xf8fffe0ff8fe7e3f 0xfdbdf8fc7ef1ccfc

def z1403 : W := mkw 0x8120805281209052 0x10001623480c2242 0xc7f1c1ffc701f1f0 0xffd27f63cd8e33e3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z5,z6]),(0,[z9,z1,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z11,z12,z6]),(0,[z1,z2,z3,z4,z5,z6,z13]),(0,[z1,z2,z3,z4,z14,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z15])],[(0,[z2,z16,z3,z4,z5,z6,z17]),(0,[z1,z2,z3,z18,z4,z11,z6]),(0,[z1,z19,z2,z3,z4,z5,z6]),(1,[z20,z1,z2,z4,z5,z6]),(0,[z1,z2,z21,z4,z5,z22,z6]),(0,[z1,z2,z23,z4,z5,z6,z24]),(0,[z1,z2,z3,z25,z4,z5,z6])],[(0,[z26,z1,z2,z27,z4,z5,z6]),(0,[z28,z2,z23,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z11,z6]),(0,[z1,z30,z2,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z31,z6]),(1,[z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z32,z5,z6])],[(0,[z33,z1,z2,z3,z4,z11,z6]),(0,[z34,z1,z2,z3,z4,z5,z6])],[(0,[z35,z2,z3,z4,z5,z22,z6]),(0,[z1,z2,z3,z4,z36,z10,z6]),(1,[z1,z2,z37,z4,z5,z6]),(0,[z1,z2,z38,z3,z4,z5,z6]),(0,[z1,z2,z39,z3,z4,z5,z40])],[(1,[z1,z2,z41,z4,z5,z6]),(0,[z2,z16,z42,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z11,z6]),(0,[z44,z1,z2,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z45]),(0,[z46,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z23,z4,z12,z5,z6]),(0,[z1,z47,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z48,z4,z5,z6]),(0,[z1,z2,z3,z49,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z50,z6]),(1,[z1,z2,z4,z5,z6,z51])],[(0,[z28,z1,z2,z3,z4,z10,z6]),(1,[z1,z2,z3,z4,z52,z6]),(0,[z1,z2,z53,z3,z4,z5,z6]),(0,[z1,z30,z2,z3,z4,z10,z6]),(0,[z1,z2,z54,z3,z4,z5,z17])],[(0,[z1,z55,z16,z3,z4,z5,z6]),(0,[z56,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z57,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z58,z6]),(0,[z1,z2,z3,z4,z5,z59,z6]),(0,[z1,z60,z2,z61,z4,z5,z6]),(0,[z1,z2,z4,z5,z62,z6,z63]),(0,[z1,z2,z3,z4,z64,z5,z6]),(0,[z1,z2,z3,z4,z5,z65,z6]),(0,[z66,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z28,z26,z2,z3,z4,z5,z6]),(1,[z35,z2,z67,z4,z5,z6]),(0,[z1,z68,z2,z3,z4,z5,z6]),(0,[z1,z2,z69,z3,z4,z5,z6]),(1,[z1,z70,z3,z4,z5,z6]),(0,[z1,z2,z3,z71,z12,z5,z6]),(0,[z1,z72,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z73,z4,z5,z6]),(0,[z74,z28,z2,z3,z4,z5,z6]),(1,[z1,z2,z75,z4,z5,z6]),(0,[z1,z76,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z77,z3,z4,z5,z6]),(0,[z33,z1,z70,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z4,z12,z6])],[(0,[z1,z79,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z80]),(0,[z1,z2,z21,z81,z4,z5,z6]),(0,[z82,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z25,z4,z11,z6]),(1,[z1,z2,z83,z4,z5,z6]),(0,[z84,z2,z85,z3,z4,z5,z6]),(0,[z86,z1,z2,z3,z4,z5,z6]),(0,[z1,z30,z2,z25,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z87,z6])],[(0,[z88,z2,z16,z3,z4,z5,z6]),(0,[z46,z28,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z89,z6]),(0,[z1,z3,z90,z4,z5,z58,z6]),(0,[z1,z2,z4,z91,z5,z62,z6]),(0,[z1,z2,z92,z3,z4,z5,z63])],[(0,[z26,z1,z16,z3,z4,z5,z6]),(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z54,z3,z25,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z94])],[(0,[z28,z2,z3,z95,z4,z5,z6]),(0,[z1,z84,z2,z96,z4,z5,z6]),(0,[z1,z2,z97,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z98,z5,z6])],[(0,[z2,z16,z3,z4,z5,z22,z6]),(0,[z99,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z4,z5,z10,z6]),(0,[z100,z1,z2,z3,z4,z101,z6]),(0,[z102,z103,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z95,z4,z10,z6]),(0,[z1,z2,z3,z4,z104,z5,z6]),(0,[z1,z2,z3,z48,z4,z11,z6]),(0,[z1,z2,z3,z4,z105,z5,z6])],[(1,[z28,z2,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z106]),(0,[z1,z107,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z108,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z71,z4,z5,z6]),(0,[z1,z84,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z6,z109]),(0,[z1,z2,z39,z3,z95,z4,z6])]],
   [[(0,[z1,z2,z110,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z111,z6]),(0,[z1,z112,z2,z3,z4,z113,z6]),(0,[z1,z114,z2,z3,z4,z115,z6]),(0,[z102,z1,z55,z3,z4,z5,z6]),(0,[z33,z1,z2,z4,z5,z62,z6])],[(0,[z114,z2,z16,z3,z4,z5,z6]),(0,[z28,z2,z3,z4,z116,z5,z6]),(0,[z1,z2,z3,z4,z11,z6,z117]),(0,[z46,z118,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z119])],[(0,[z1,z16,z3,z4,z5,z10,z6]),(0,[z1,z120,z2,z3,z4,z11,z6]),(0,[z1,z121,z2,z3,z4,z5,z6]),(1,[z1,z122,z3,z4,z5,z6]),(0,[z1,z2,z123,z21,z4,z5,z6]),(0,[z1,z2,z124,z3,z4,z5,z6]),(1,[z1,z2,z125,z4,z5,z6]),(0,[z1,z2,z3,z126,z4,z5,z6]),(0,[z1,z2,z3,z4,z127,z5,z6]),(0,[z1,z2,z3,z95,z71,z4,z6]),(0,[z1,z2,z3,z4,z128,z5,z6])],[(0,[z28,z2,z3,z90,z4,z5,z6]),(0,[z43,z2,z3,z4,z129,z5,z6]),(1,[z1,z2,z3,z4,z130,z6]),(0,[z78,z1,z2,z3,z95,z4,z6]),(0,[z1,z2,z3,z131,z4,z5,z6])],[(0,[z26,z1,z2,z3,z4,z132,z6]),(0,[z28,z2,z39,z3,z4,z5,z6]),(0,[z28,z35,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z133,z4,z5,z6]),(0,[z1,z134,z55,z3,z4,z5,z6]),(0,[z135,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z90,z4,z10,z6]),(0,[z1,z2,z136,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z137,z6]),(0,[z1,z30,z2,z92,z4,z5,z6])],[(0,[z138,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z21,z4,z5,z6]),(0,[z100,z1,z2,z139,z4,z5,z6]),(0,[z1,z2,z39,z3,z4,z10,z6]),(0,[z140,z84,z2,z3,z4,z5,z6]),(0,[z1,z141,z2,z3,z4,z5,z6]),(0,[z1,z2,z142,z3,z4,z5,z6])],[(0,[z1,z143,z2,z3,z4,z5,z6]),(0,[z28,z114,z2,z3,z4,z5,z6]),(0,[z1,z144,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z145,z4,z5,z6]),(0,[z33,z1,z2,z21,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z146,z6]),(0,[z100,z1,z2,z3,z36,z5,z6]),(0,[z1,z2,z3,z4,z5,z147,z6]),(0,[z1,z148,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z149,z5,z6]),(1,[z1,z2,z150,z4,z5,z6]),(1,[z151,z2,z3,z4,z5,z6]),(0,[z1,z114,z2,z3,z4,z10,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z152]),(0,[z28,z2,z3,z21,z4,z5,z6]),(0,[z43,z1,z2,z21,z4,z5,z6]),(0,[z153,z2,z3,z18,z4,z5,z6]),(0,[z1,z2,z3,z4,z154,z5,z6]),(0,[z155,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z156,z3,z4,z5,z6])],[(0,[z28,z2,z3,z4,z157,z5,z6]),(0,[z1,z2,z21,z18,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z10,z6]),(0,[z1,z2,z158,z3,z4,z5,z6]),(0,[z159,z1,z2,z3,z4,z5,z6]),(0,[z160,z1,z2,z3,z4,z5,z6])],[(0,[z100,z2,z16,z3,z4,z5,z6]),(0,[z135,z28,z2,z3,z4,z5,z6]),(0,[z28,z2,z3,z4,z5,z161,z6]),(0,[z1,z2,z3,z162,z4,z5,z6]),(1,[z1,z2,z3,z4,z163,z6]),(0,[z1,z2,z3,z4,z157,z10,z6]),(0,[z1,z2,z3,z4,z10,z62,z6]),(0,[z46,z1,z2,z3,z4,z11,z6]),(0,[z164,z1,z2,z3,z4,z5,z6])],[(0,[z2,z16,z3,z4,z5,z10,z6]),(0,[z28,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z165]),(0,[z1,z2,z166,z21,z4,z5,z6]),(1,[z1,z134,z3,z4,z10,z6])],[(0,[z0,z1,z2,z21,z4,z5,z6]),(0,[z1,z112,z2,z23,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z6,z167]),(0,[z1,z2,z23,z4,z5,z6,z17]),(0,[z1,z2,z3,z4,z5,z168,z6]),(0,[z1,z2,z3,z169,z4,z10,z6]),(0,[z1,z55,z2,z3,z4,z10,z6])],[(0,[z1,z2,z67,z3,z4,z11,z6]),(0,[z1,z2,z136,z3,z4,z11,z6]),(1,[z170,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z171,z6])],[(0,[z1,z2,z3,z172,z4,z5,z6]),(1,[z1,z2,z21,z4,z11,z6]),(0,[z1,z2,z3,z4,z11,z6,z24]),(0,[z1,z2,z3,z173,z4,z5,z6])],[(0,[z28,z2,z54,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z174,z6]),(0,[z1,z2,z3,z4,z175,z5,z6]),(1,[z33,z1,z2,z4,z146,z6])]],
   [[(0,[z135,z1,z2,z3,z4,z5,z6]),(0,[z176,z28,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z177]),(0,[z1,z2,z3,z4,z5,z6,z178]),(1,[z179,z2,z3,z4,z5,z6])],[(0,[z26,z1,z2,z3,z4,z10,z6]),(0,[z2,z180,z16,z3,z4,z5,z6]),(0,[z30,z2,z16,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z181,z6]),(0,[z28,z1,z2,z23,z4,z5,z6]),(0,[z33,z43,z1,z2,z4,z5,z6]),(0,[z1,z30,z2,z23,z4,z5,z6]),(0,[z164,z1,z3,z4,z5,z6,z17])],[(0,[z84,z2,z16,z3,z4,z5,z6]),(0,[z1,z2,z182,z3,z4,z5,z6]),(0,[z183,z0,z2,z3,z4,z5,z6]),(0,[z184,z2,z3,z4,z5,z161,z6]),(0,[z46,z1,z2,z83,z4,z5,z6]),(1,[z1,z2,z3,z4,z185,z6]),(0,[z1,z2,z61,z3,z4,z5,z6]),(0,[z186,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z42,z3,z4,z11,z6]),(0,[z1,z2,z187,z3,z4,z5,z6]),(1,[z1,z2,z3,z188,z5,z6]),(0,[z1,z2,z189,z3,z4,z5,z6]),(0,[z1,z190,z2,z3,z4,z5,z6])],[(0,[z43,z1,z2,z67,z4,z5,z6]),(0,[z1,z191,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z192,z6]),(0,[z1,z2,z193,z3,z95,z5,z6])],[(0,[z1,z2,z194,z3,z4,z5,z6]),(0,[z2,z92,z195,z3,z4,z5,z6]),(0,[z1,z2,z196,z3,z4,z5,z6])],[(0,[z2,z16,z3,z18,z4,z5,z6]),(0,[z1,z2,z16,z3,z4,z10,z6]),(0,[z1,z2,z3,z197,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z198,z6]),(0,[z1,z199,z2,z23,z4,z5,z6])],[(1,[z1,z2,z3,z4,z200,z6]),(0,[z2,z16,z3,z29,z4,z5,z6]),(0,[z9,z1,z2,z3,z4,z5,z6]),(0,[z201,z35,z2,z3,z4,z5,z6]),(0,[z1,z202,z2,z3,z4,z5,z6]),(0,[z100,z78,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z203,z4,z5,z6]),(0,[z204,z1,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z205,z10,z6]),(0,[z206,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z67,z3,z4,z129,z5,z6]),(0,[z1,z112,z2,z3,z4,z5,z6]),(0,[z1,z2,z207,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z208,z5,z6])],[(0,[z28,z2,z3,z4,z5,z209,z6]),(0,[z1,z2,z23,z4,z5,z22,z6]),(0,[z210,z1,z2,z3,z4,z5,z6]),(0,[z102,z1,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z10,z211,z6]),(0,[z1,z2,z3,z4,z212,z10,z6]),(0,[z1,z2,z3,z4,z5,z212,z6]),(0,[z135,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z213,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z214]),(0,[z1,z2,z215,z3,z4,z5,z6])],[(0,[z216,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z73,z4,z5,z6]),(0,[z1,z217,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z218])],[(0,[z1,z219,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z36,z5,z6]),(0,[z1,z2,z61,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z220,z5,z6]),(0,[z78,z1,z2,z3,z71,z5,z6])],[(0,[z1,z2,z3,z4,z200,z5,z6]),(0,[z221,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z113,z5,z6]),(0,[z1,z222,z2,z3,z4,z5,z6]),(0,[z1,z2,z61,z3,z157,z5,z6]),(0,[z223,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z81,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z51,z40])],[(0,[z28,z1,z2,z3,z4,z5,z6]),(0,[z224,z2,z16,z3,z4,z5,z6]),(0,[z184,z2,z16,z3,z4,z5,z6]),(0,[z2,z16,z3,z4,z5,z6,z225]),(0,[z1,z2,z3,z4,z226,z5,z6]),(0,[z1,z227,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z21,z4,z5,z6]),(0,[z1,z2,z21,z4,z5,z6,z94]),(0,[z1,z2,z228,z3,z4,z5,z6]),(0,[z1,z30,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z229,z5,z6]),(0,[z1,z2,z3,z230,z4,z5,z6])],[(0,[z1,z2,z3,z231,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z130,z6]),(0,[z1,z2,z124,z21,z4,z5,z6]),(1,[z232,z2,z3,z4,z5,z6])],[(0,[z2,z16,z3,z25,z4,z5,z6]),(0,[z1,z233,z2,z3,z4,z5,z6]),(0,[z2,z67,z3,z29,z4,z5,z6]),(0,[z183,z2,z3,z18,z4,z5,z6]),(0,[z1,z2,z3,z4,z10,z234,z6]),(0,[z1,z2,z235,z3,z4,z10,z6]),(0,[z176,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z37,z4,z5,z6]),(0,[z1,z2,z236,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z41,z4,z5,z6]),(0,[z183,z2,z3,z29,z4,z5,z6]),(1,[z237,z1,z2,z3,z10,z6]),(0,[z1,z2,z3,z4,z5,z6,z51])],[(0,[z238,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z239,z4,z5,z6]),(0,[z44,z2,z3,z4,z5,z22,z6]),(0,[z1,z112,z2,z3,z4,z11,z6]),(0,[z1,z240,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z241]),(0,[z1,z242,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z243,z4,z5,z6]),(0,[z1,z2,z3,z4,z91,z5,z6]),(0,[z1,z244,z2,z3,z4,z5,z6]),(0,[z1,z2,z245,z3,z4,z5,z6]),(1,[z164,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z246,z4,z5,z6]),(0,[z1,z2,z3,z4,z247,z5,z6]),(0,[z1,z199,z2,z3,z4,z5,z6]),(0,[z1,z114,z2,z3,z36,z5,z6]),(0,[z1,z2,z3,z4,z248,z6,z40])],[(0,[z1,z134,z112,z3,z4,z5,z6]),(0,[z249,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z4,z128,z5,z6]),(0,[z1,z2,z3,z250,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z146,z6])],[(0,[z28,z2,z251,z3,z4,z5,z6]),(0,[z1,z2,z3,z252,z4,z5,z6]),(0,[z1,z2,z253,z3,z4,z5,z6]),(0,[z201,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z254,z4,z5,z6]),(0,[z1,z2,z3,z4,z255,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z256]),(0,[z1,z2,z3,z4,z36,z11,z6]),(0,[z1,z55,z3,z4,z11,z5,z6]),(0,[z1,z2,z3,z257,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z258,z40])],[(0,[z28,z2,z3,z259,z4,z5,z6]),(0,[z1,z260,z2,z3,z4,z5,z6]),(0,[z261,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z262,z6]),(0,[z263,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z264,z3,z4,z5,z6]),(0,[z1,z2,z3,z81,z4,z11,z6]),(0,[z1,z2,z85,z3,z4,z5,z6])],[(0,[z28,z2,z3,z4,z5,z58,z6]),(0,[z183,z2,z3,z4,z5,z6,z225]),(0,[z1,z2,z23,z4,z5,z10,z6]),(0,[z265,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z212,z10,z6]),(0,[z1,z30,z2,z3,z4,z11,z6]),(1,[z1,z2,z3,z4,z208,z6])],[(0,[z2,z16,z3,z73,z4,z5,z6]),(0,[z0,z1,z2,z3,z18,z5,z6]),(0,[z266,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z267,z3,z4,z10,z6]),(0,[z1,z2,z268,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z269])]],
   [[(0,[z78,z2,z16,z3,z4,z5,z6]),(0,[z100,z159,z2,z3,z4,z5,z6]),(1,[z270,z2,z3,z4,z5,z6])],[(0,[z271,z1,z2,z23,z4,z5,z6]),(1,[z1,z2,z69,z4,z5,z6]),(0,[z1,z2,z3,z4,z272,z5,z6]),(0,[z1,z2,z3,z4,z11,z6,z17]),(0,[z33,z270,z2,z3,z4,z5,z6]),(0,[z1,z2,z273,z3,z4,z5,z6])],[(0,[z2,z16,z3,z4,z5,z6,z94]),(0,[z201,z28,z2,z3,z4,z5,z6]),(0,[z1,z2,z274,z3,z4,z5,z6]),(0,[z100,z1,z3,z4,z5,z58,z6]),(0,[z1,z2,z3,z275,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z276]),(0,[z1,z30,z2,z4,z91,z5,z6]),(0,[z1,z2,z3,z4,z5,z62,z6])],[(0,[z1,z2,z277,z3,z4,z5,z6]),(0,[z2,z3,z4,z129,z5,z22,z6]),(1,[z1,z21,z4,z5,z10,z6]),(0,[z1,z2,z54,z3,z36,z5,z6])],[(0,[z26,z1,z2,z23,z4,z5,z6]),(0,[z278,z1,z2,z3,z4,z5,z6]),(0,[z1,z279,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z161,z10,z6]),(0,[z1,z2,z3,z4,z5,z280,z6]),(0,[z135,z1,z2,z21,z4,z5,z6])],[(0,[z28,z2,z3,z4,z281,z5,z6]),(0,[z1,z2,z282,z3,z4,z5,z6]),(1,[z1,z2,z4,z5,z283,z6]),(0,[z1,z2,z3,z4,z5,z185,z6]),(0,[z1,z284,z2,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z4,z248,z6]),(0,[z1,z2,z3,z71,z4,z248,z6])],[(0,[z1,z2,z3,z4,z281,z10,z6]),(0,[z1,z2,z3,z285,z4,z5,z6]),(0,[z1,z2,z61,z21,z4,z5,z6]),(0,[z286,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z287,z5,z6])],[(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z289,z6]),(0,[z100,z1,z2,z3,z4,z5,z241]),(0,[z2,z3,z4,z5,z137,z146,z6]),(0,[z1,z2,z3,z81,z4,z128,z5])]],
   [[(0,[z26,z2,z16,z3,z4,z5,z6]),(0,[z2,z16,z3,z4,z128,z5,z6]),(0,[z1,z2,z3,z4,z290,z5,z6]),(0,[z1,z2,z3,z291,z4,z5,z6]),(0,[z201,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z128,z5,z58]),(0,[z1,z2,z3,z4,z5,z6,z292]),(0,[z293,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z16,z23,z4,z5,z6]),(0,[z1,z2,z23,z18,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z119,z17])],[(0,[z28,z2,z3,z4,z248,z5,z6]),(0,[z1,z2,z23,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z161,z6]),(0,[z294,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z295,z6]),(0,[z296,z1,z2,z3,z4,z5,z6])],[(0,[z28,z84,z2,z3,z4,z5,z6]),(0,[z1,z120,z2,z277,z4,z5,z6]),(0,[z183,z1,z2,z3,z297,z5,z6]),(1,[z1,z2,z3,z4,z298,z6]),(0,[z1,z2,z3,z4,z248,z10,z6]),(0,[z1,z2,z92,z3,z4,z5,z62]),(0,[z299,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z300,z3,z4,z5,z6]),(0,[z1,z112,z2,z21,z4,z5,z6]),(0,[z102,z1,z2,z23,z4,z5,z6]),(0,[z1,z301,z2,z3,z4,z5,z6])],[(0,[z271,z1,z2,z3,z4,z5,z6]),(0,[z1,z60,z2,z3,z25,z5,z6]),(0,[z33,z1,z30,z2,z4,z5,z6])],[(0,[z1,z2,z302,z3,z4,z5,z6]),(0,[z1,z2,z3,z303,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z22,z6]),(1,[z1,z3,z21,z4,z10,z6]),(0,[z1,z2,z23,z3,z4,z10,z6]),(0,[z232,z1,z2,z3,z4,z5,z6]),(0,[z304,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z305,z6])],[(0,[z1,z306,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z307,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z308])]],
   [[(0,[z26,z1,z2,z3,z4,z5,z6]),(0,[z102,z2,z16,z3,z4,z5,z6]),(0,[z1,z309,z2,z3,z4,z5,z6]),(0,[z310,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z22,z6]),(0,[z1,z2,z23,z4,z5,z6,z225]),(0,[z1,z134,z2,z23,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z218,z17])],[(0,[z28,z1,z2,z21,z4,z5,z6]),(0,[z1,z2,z3,z311,z4,z5,z6]),(0,[z201,z1,z2,z3,z4,z11,z6]),(0,[z1,z30,z2,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z211,z6]),(0,[z1,z2,z23,z4,z8,z5,z6]),(0,[z1,z2,z3,z4,z290,z11,z6]),(0,[z1,z312,z2,z3,z4,z5,z6])],[(0,[z313,z28,z2,z3,z4,z5,z6]),(0,[z286,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z25,z4,z5,z6]),(0,[z314,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z315,z5,z6]),(0,[z1,z316,z2,z3,z4,z5,z6])],[(0,[z1,z317,z2,z3,z4,z5,z6]),(0,[z183,z184,z2,z3,z4,z5,z6]),(0,[z1,z318,z2,z3,z4,z5,z6])],[(0,[z1,z2,z21,z4,z36,z5,z6]),(0,[z1,z2,z3,z71,z4,z12,z6]),(1,[z1,z2,z3,z319,z5,z6])],[(0,[z1,z2,z16,z3,z4,z5,z6]),(0,[z28,z2,z3,z4,z5,z6,z24]),(0,[z1,z2,z3,z320,z4,z5,z6]),(1,[z1,z2,z321,z4,z5,z6])],[(0,[z28,z2,z3,z4,z5,z322,z6]),(0,[z35,z1,z2,z29,z4,z5,z6]),(0,[z323,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z324,z5,z6]),(0,[z204,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z325,z5,z6]),(0,[z46,z1,z2,z3,z4,z208,z6]),(0,[z1,z2,z3,z326,z4,z5,z6]),(0,[z327,z1,z2,z3,z4,z5,z6])],[(0,[z2,z16,z3,z4,z5,z181,z6]),(0,[z328,z1,z2,z3,z4,z5,z6]),(0,[z237,z1,z2,z3,z5,z10,z6]),(0,[z1,z329,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z16,z61,z3,z4,z5,z6]),(0,[z313,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z29,z4,z5,z22,z6]),(0,[z330,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z331,z4,z5,z6]),(0,[z102,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z332,z4,z5,z6]),(0,[z1,z333,z2,z3,z4,z5,z6])],[(0,[z28,z2,z3,z4,z12,z5,z6]),(0,[z1,z2,z3,z4,z334,z5,z6]),(0,[z1,z2,z3,z18,z5,z6,z17]),(0,[z184,z1,z2,z3,z4,z10,z6]),(0,[z1,z335,z2,z3,z4,z5,z6]),(0,[z1,z23,z3,z21,z4,z5,z6]),(0,[z1,z2,z3,z336,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z337,z6]),(0,[z1,z2,z3,z4,z5,z338,z6])],[(0,[z28,z2,z3,z4,z11,z5,z6]),(0,[z1,z2,z3,z4,z5,z339,z6]),(0,[z1,z2,z3,z4,z5,z6,z340]),(0,[z1,z2,z3,z341,z4,z5,z6]),(0,[z1,z2,z21,z4,z91,z5,z6]),(0,[z1,z2,z267,z23,z4,z5,z6]),(0,[z1,z3,z90,z4,z36,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z342])],[(1,[z1,z16,z3,z4,z10,z6]),(0,[z102,z1,z2,z203,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z10,z6]),(0,[z286,z1,z2,z3,z4,z11,z6]),(1,[z1,z343,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z344,z5,z6])],[(0,[z26,z1,z2,z41,z4,z5,z6]),(0,[z1,z134,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z92,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z345,z6]),(1,[z140,z2,z3,z4,z5,z6]),(0,[z1,z2,z346,z3,z4,z5,z6])],[(1,[z26,z16,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z347,z6]),(0,[z1,z2,z3,z4,z5,z348,z6]),(0,[z1,z2,z21,z4,z5,z6,z256]),(0,[z1,z2,z23,z4,z5,z6,z94]),(0,[z1,z2,z349,z3,z4,z5,z6]),(0,[z350,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z351]),(0,[z1,z2,z3,z4,z5,z6,z352]),(0,[z353,z1,z2,z3,z4,z5,z6])],[(0,[z2,z2,z16,z3,z4,z5,z6]),(0,[z1,z2,z16,z3,z4,z11,z6]),(0,[z88,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z354,z5,z6]),(0,[z1,z2,z21,z95,z4,z5,z6]),(0,[z1,z103,z2,z3,z4,z5,z6]),(0,[z1,z2,z235,z3,z4,z5,z6]),(0,[z1,z2,z96,z3,z4,z5,z6])],[(0,[z184,z1,z2,z303,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z201,z2,z3,z4,z129,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(1,[z237,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z355,z5,z6]),(0,[z1,z30,z2,z3,z188,z5,z6])]],
   [[(0,[z28,z60,z2,z3,z4,z5,z6]),(0,[z1,z2,z356,z3,z4,z5,z6]),(0,[z1,z2,z357,z3,z4,z5,z6]),(1,[z1,z2,z96,z4,z5,z6]),(0,[z78,z1,z2,z3,z5,z6,z94])],[(0,[z2,z16,z3,z4,z36,z5,z6]),(0,[z28,z2,z3,z4,z5,z6,z63]),(0,[z1,z2,z3,z358,z4,z5,z6]),(0,[z100,z1,z2,z23,z4,z5,z6]),(0,[z1,z359,z2,z23,z4,z5,z6]),(1,[z1,z2,z3,z4,z360,z6]),(0,[z1,z60,z2,z3,z4,z10,z6])],[(0,[z2,z16,z3,z81,z4,z5,z6]),(0,[z1,z361,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z362]),(0,[z1,z2,z3,z25,z5,z6,z17]),(0,[z1,z2,z3,z4,z363,z5,z6])],[(0,[z2,z16,z3,z4,z226,z5,z6]),(0,[z28,z2,z3,z71,z4,z5,z6]),(0,[z28,z120,z2,z3,z4,z5,z6]),(0,[z1,z2,z29,z4,z5,z62,z6]),(0,[z1,z2,z3,z4,z364,z5,z6]),(0,[z1,z2,z21,z4,z5,z62,z6]),(0,[z1,z2,z23,z4,z128,z5,z6]),(0,[z1,z2,z4,z91,z5,z146,z6])],[(0,[z1,z2,z3,z4,z5,z6,z365]),(0,[z201,z1,z2,z3,z4,z129,z6]),(0,[z201,z1,z2,z21,z4,z5,z6]),(0,[z7,z112,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z366,z5,z6]),(0,[z1,z2,z3,z4,z367,z10,z6]),(0,[z78,z1,z2,z3,z4,z10,z6])],[(0,[z43,z2,z3,z29,z4,z5,z6]),(0,[z184,z1,z19,z3,z4,z5,z6]),(0,[z1,z134,z2,z3,z4,z11,z6])],[(0,[z1,z2,z267,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z298,z6]),(0,[z1,z2,z3,z4,z128,z11,z6]),(1,[z368,z2,z3,z4,z5,z6])],[(2,[z16,z3,z4,z10,z6]),(0,[z2,z16,z3,z4,z91,z5,z6]),(0,[z100,z28,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z369])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z370]),(0,[z1,z2,z3,z4,z5,z371,z6]),(0,[z1,z2,z3,z4,z5,z58,z17]),(0,[z33,z1,z2,z4,z5,z146,z6]),(0,[z1,z343,z2,z4,z5,z6,z40])],[(0,[z28,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z29,z21,z4,z5,z6]),(0,[z1,z2,z21,z21,z4,z5,z6]),(0,[z1,z2,z23,z23,z4,z5,z6]),(0,[z232,z102,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z10,z6,z63]),(0,[z1,z2,z357,z3,z4,z11,z6]),(0,[z223,z2,z3,z4,z5,z146,z6]),(0,[z1,z2,z3,z4,z5,z372,z6])],[(0,[z28,z2,z3,z4,z5,z146,z6]),(0,[z1,z2,z21,z4,z157,z5,z6]),(0,[z1,z2,z23,z4,z366,z5,z6]),(0,[z1,z2,z3,z373,z4,z10,z6])],[(0,[z2,z16,z3,z95,z4,z5,z6]),(0,[z374,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z4,z5,z161,z6]),(0,[z1,z2,z54,z3,z4,z10,z6]),(0,[z1,z375,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z376])],[(0,[z26,z1,z2,z21,z4,z5,z6]),(0,[z143,z2,z16,z3,z4,z5,z6]),(0,[z9,z28,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z52,z6]),(0,[z1,z2,z3,z4,z5,z6,z377]),(0,[z378,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z379,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z380])],[(0,[z1,z2,z3,z4,z11,z6,z225]),(0,[z1,z359,z2,z3,z4,z5,z6]),(0,[z100,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z381,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z382]),(0,[z1,z2,z54,z3,z128,z5,z6])],[(0,[z35,z2,z3,z4,z5,z161,z6]),(1,[z100,z1,z3,z36,z5,z6]),(0,[z1,z2,z383,z3,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z384,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z385,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z386,z5,z6]),(0,[z1,z387,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z388,z5,z6])]],
   [[(1,[z55,z16,z3,z4,z5,z6]),(0,[z2,z16,z3,z4,z5,z62,z6]),(0,[z28,z2,z3,z4,z5,z6,z17]),(0,[z1,z2,z3,z4,z5,z283,z6]),(0,[z1,z2,z3,z389,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z390,z6]),(0,[z391,z1,z2,z3,z4,z5,z6]),(0,[z392,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z16,z21,z4,z5,z6]),(0,[z1,z2,z393,z3,z4,z5,z6]),(0,[z394,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z395,z3,z4,z5,z6]),(0,[z396,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z397,z5,z6])],[(0,[z28,z28,z2,z3,z4,z5,z6]),(0,[z398,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z4,z5,z211,z6]),(0,[z1,z2,z3,z4,z10,z146,z6])],[(1,[z1,z2,z3,z81,z5,z17])],[(0,[z28,z2,z42,z3,z4,z5,z6]),(0,[z184,z1,z2,z23,z4,z5,z6]),(0,[z102,z1,z2,z21,z4,z5,z6]),(0,[z1,z399,z2,z21,z4,z5,z6]),(0,[z100,z1,z2,z3,z4,z298,z6])],[(0,[z153,z2,z16,z3,z4,z5,z6]),(0,[z384,z28,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z297,z5,z6]),(0,[z1,z2,z23,z3,z4,z5,z6]),(0,[z1,z2,z3,z400,z4,z5,z6]),(0,[z401,z55,z2,z3,z4,z5,z6])],[(0,[z2,z16,z3,z21,z4,z5,z6]),(0,[z2,z16,z3,z4,z290,z5,z6]),(0,[z402,z1,z2,z3,z4,z5,z6]),(0,[z403,z1,z2,z3,z4,z5,z6]),(0,[z201,z1,z2,z3,z4,z161,z6]),(0,[z100,z1,z2,z3,z4,z11,z6]),(0,[z78,z1,z114,z2,z3,z5,z6]),(0,[z1,z404,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z405,z4,z5,z6])],[(0,[z28,z2,z3,z4,z406,z5,z6]),(0,[z1,z2,z3,z407,z4,z5,z6]),(0,[z1,z2,z3,z12,z5,z6,z17])]],
   [[(1,[z1,z2,z27,z4,z5,z6]),(0,[z2,z16,z3,z4,z5,z161,z6]),(0,[z1,z134,z2,z21,z4,z5,z6]),(0,[z270,z1,z2,z3,z4,z5,z6]),(0,[z33,z1,z2,z3,z4,z146,z6])],[(0,[z35,z2,z16,z3,z4,z5,z6]),(0,[z28,z2,z3,z4,z5,z6,z40]),(0,[z1,z2,z23,z42,z4,z5,z6]),(0,[z102,z1,z3,z4,z5,z10,z6])],[(0,[z408,z1,z2,z3,z4,z5,z6]),(0,[z409,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z336,z4,z5,z6]),(0,[z1,z410,z2,z3,z4,z5,z6]),(0,[z411,z134,z2,z3,z4,z5,z6]),(0,[z237,z1,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z11,z6,z94]),(0,[z46,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z412,z4,z5,z6]),(0,[z1,z413,z2,z3,z4,z5,z6])],[(1,[z16,z3,z4,z5,z10,z6]),(0,[z1,z2,z180,z3,z4,z5,z6]),(0,[z384,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z414]),(0,[z1,z2,z3,z4,z5,z6,z415]),(0,[z1,z2,z3,z4,z416,z5,z6]),(0,[z1,z2,z39,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z417,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z418]),(0,[z78,z1,z2,z54,z3,z5,z6]),(0,[z1,z419,z2,z3,z4,z5,z6])],[(1,[z28,z16,z3,z4,z5,z6]),(0,[z1,z2,z420,z3,z4,z5,z6]),(0,[z2,z3,z18,z4,z5,z22,z6]),(0,[z1,z2,z3,z4,z5,z421,z6]),(0,[z1,z2,z23,z4,z36,z5,z6]),(0,[z1,z60,z2,z23,z4,z5,z6])],[(0,[z28,z2,z3,z4,z5,z22,z6]),(0,[z422,z1,z2,z3,z4,z5,z6]),(0,[z183,z44,z2,z3,z4,z5,z6]),(0,[z1,z2,z423,z3,z4,z5,z6]),(0,[z1,z134,z2,z3,z4,z163,z6]),(0,[z1,z134,z3,z4,z5,z10,z6]),(0,[z1,z114,z2,z23,z4,z5,z6]),(0,[z1,z2,z23,z81,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z91,z6]),(1,[z2,z3,z4,z5,z137,z6]),(0,[z1,z2,z3,z4,z424,z5,z6])],[(0,[z28,z2,z92,z3,z4,z5,z6]),(1,[z1,z2,z277,z4,z5,z6]),(0,[z1,z2,z425,z3,z4,z5,z6]),(1,[z1,z2,z3,z426,z5,z6])],[(0,[z1,z2,z3,z75,z4,z5,z6]),(0,[z1,z2,z150,z3,z4,z5,z6]),(0,[z183,z1,z2,z3,z4,z5,z225]),(0,[z1,z2,z3,z4,z5,z6,z427]),(0,[z78,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z92,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z428,z5,z6]),(0,[z1,z2,z429,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z430,z5,z6])]],
   [[(0,[z43,z184,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z431]),(0,[z184,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z83,z4,z5,z6]),(0,[z1,z432,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z95,z4,z5,z6])],[(0,[z28,z1,z2,z3,z4,z11,z6]),(0,[z201,z184,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z433,z5,z6]),(0,[z1,z2,z3,z4,z10,z6,z40]),(0,[z1,z2,z3,z4,z5,z6,z434])],[(0,[z1,z2,z67,z4,z5,z146,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(1,[z0,z2,z3,z281,z5,z6]),(0,[z1,z55,z2,z23,z4,z5,z6]),(0,[z1,z2,z23,z4,z91,z5,z6]),(0,[z1,z84,z2,z3,z4,z435,z6]),(0,[z1,z2,z3,z4,z436,z5,z6]),(0,[z437,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z438,z4,z5,z6]),(0,[z1,z2,z3,z4,z439,z5,z6]),(0,[z1,z2,z440,z3,z4,z5,z6])],[(0,[z2,z16,z16,z3,z4,z5,z6]),(0,[z441,z2,z16,z3,z4,z5,z6]),(0,[z442,z28,z2,z3,z4,z5,z6]),(0,[z46,z1,z84,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z4,z6,z94]),(0,[z1,z2,z443,z3,z4,z5,z6]),(0,[z1,z2,z3,z95,z4,z248,z5])],[(0,[z1,z2,z3,z4,z116,z5,z6]),(0,[z1,z2,z3,z4,z444,z5,z6]),(0,[z1,z2,z3,z4,z445,z5,z6]),(0,[z446,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z447]),(0,[z1,z2,z448,z3,z4,z5,z6])],[(0,[z2,z16,z3,z4,z5,z234,z6]),(0,[z78,z28,z2,z3,z4,z5,z6]),(0,[z28,z1,z120,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z449]),(1,[z1,z2,z3,z4,z5,z168])],[(0,[z1,z2,z3,z450,z4,z5,z6]),(0,[z1,z2,z54,z23,z4,z5,z6]),(0,[z1,z2,z23,z95,z4,z5,z6]),(0,[z1,z2,z3,z90,z4,z5,z6]),(0,[z1,z2,z3,z4,z451,z5,z6]),(0,[z1,z2,z452,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z453,z5,z6]),(0,[z44,z1,z2,z3,z4,z10,z6]),(0,[z1,z2,z39,z3,z4,z5,z6])]],
   [[(1,[z1,z3,z4,z11,z10,z6]),(0,[z1,z2,z3,z4,z5,z205,z6]),(0,[z1,z2,z3,z125,z4,z5,z6]),(0,[z1,z60,z2,z3,z4,z5,z6]),(0,[z1,z2,z54,z3,z81,z5,z6])],[(0,[z112,z2,z16,z3,z4,z5,z6]),(0,[z442,z1,z2,z3,z4,z5,z6]),(0,[z184,z1,z2,z3,z4,z11,z6]),(0,[z100,z1,z2,z21,z4,z5,z6]),(0,[z1,z114,z2,z3,z4,z5,z6]),(0,[z100,z1,z3,z4,z36,z5,z6]),(0,[z1,z2,z3,z4,z10,z58,z6]),(0,[z1,z2,z3,z95,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z6,z63])],[(0,[z28,z2,z3,z454,z4,z5,z6]),(0,[z28,z2,z3,z4,z5,z10,z6]),(0,[z0,z153,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z455,z4,z5,z6]),(0,[z1,z2,z3,z456,z4,z5,z6])],[(0,[z1,z2,z3,z4,z457,z5,z6]),(0,[z1,z2,z23,z4,z5,z62,z6]),(0,[z100,z151,z2,z3,z4,z5,z6]),(0,[z1,z458,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z367,z5,z6]),(0,[z1,z84,z3,z4,z5,z58,z6]),(0,[z459,z1,z2,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z4,z5,z6])],[(0,[z183,z2,z16,z3,z4,z5,z6]),(0,[z1,z2,z3,z460,z4,z5,z6]),(0,[z1,z2,z3,z123,z4,z5,z6]),(0,[z1,z461,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z157,z5,z6]),(0,[z293,z2,z3,z4,z5,z6,z40])],[(0,[z1,z2,z3,z81,z5,z6,z17]),(0,[z1,z2,z3,z4,z5,z6,z258])],[(0,[z1,z120,z55,z3,z4,z5,z6]),(0,[z35,z1,z2,z4,z91,z5,z6]),(0,[z1,z2,z21,z4,z281,z5,z6]),(0,[z100,z1,z114,z3,z4,z5,z6]),(0,[z1,z2,z3,z169,z4,z5,z6]),(0,[z1,z2,z3,z4,z462,z5,z6]),(0,[z1,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z193,z3,z4,z5,z6])],[(1,[z2,z16,z3,z4,z10,z6]),(0,[z28,z2,z3,z4,z129,z5,z6]),(0,[z1,z2,z3,z90,z4,z11,z6]),(0,[z1,z84,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z451,z11,z6]),(0,[z1,z2,z463,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z129,z10,z6]),(1,[z1,z2,z3,z4,z115,z6]),(0,[z1,z2,z39,z3,z4,z11,z6]),(0,[z1,z2,z3,z95,z319,z5,z6])],[(0,[z1,z2,z3,z4,z464,z5,z6]),(0,[z1,z2,z3,z4,z5,z465,z6]),(0,[z1,z2,z23,z21,z4,z5,z6]),(0,[z1,z2,z21,z4,z5,z390,z6]),(1,[z102,z1,z3,z4,z10,z6]),(0,[z1,z2,z3,z373,z4,z5,z6]),(1,[z2,z207,z3,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z466])],[(0,[z2,z16,z3,z4,z5,z6,z365]),(0,[z1,z2,z3,z4,z467,z5,z6]),(0,[z1,z2,z23,z4,z157,z5,z6]),(0,[z1,z114,z2,z3,z4,z11,z6]),(0,[z1,z60,z2,z3,z157,z5,z6]),(0,[z1,z30,z2,z4,z5,z6,z63]),(0,[z1,z2,z3,z4,z468,z5,z6]),(0,[z1,z2,z54,z3,z4,z5,z6])],[(0,[z28,z102,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z161,z6]),(0,[z1,z2,z21,z4,z248,z5,z6]),(0,[z1,z2,z3,z4,z5,z469,z6]),(0,[z1,z2,z3,z455,z4,z11,z6]),(0,[z1,z2,z470,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z471])],[(0,[z472,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z11,z6]),(0,[z134,z410,z2,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z473,z6]),(0,[z474,z1,z2,z3,z4,z5,z6])],[(0,[z28,z2,z3,z18,z4,z5,z6]),(0,[z1,z2,z3,z4,z469,z10,z6]),(0,[z1,z2,z3,z4,z157,z11,z6])],[(0,[z28,z2,z3,z29,z4,z5,z6]),(0,[z43,z1,z2,z29,z4,z5,z6]),(0,[z112,z361,z2,z3,z4,z5,z6]),(1,[z1,z2,z452,z4,z5,z6])],[(0,[z1,z55,z2,z3,z4,z11,z6]),(0,[z1,z2,z475,z3,z4,z5,z6])]],
   [[(0,[z28,z2,z3,z4,z5,z6,z476]),(0,[z1,z477,z2,z3,z4,z5,z6]),(0,[z1,z2,z478,z3,z4,z5,z6]),(0,[z183,z1,z2,z3,z254,z5,z6]),(0,[z1,z2,z3,z4,z5,z479,z6]),(0,[z1,z2,z42,z3,z4,z146,z6]),(0,[z1,z2,z3,z4,z5,z480,z6])],[(0,[z153,z1,z2,z3,z4,z10,z6]),(0,[z184,z1,z122,z3,z4,z5,z6]),(0,[z481,z1,z2,z3,z4,z5,z6]),(0,[z1,z482,z2,z3,z4,z5,z6]),(0,[z44,z1,z2,z3,z4,z5,z225]),(0,[z1,z483,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z234,z6]),(0,[z43,z1,z2,z3,z4,z10,z6]),(0,[z484,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z485]),(0,[z1,z2,z3,z4,z486,z5,z6])],[(0,[z2,z16,z3,z4,z281,z5,z6]),(0,[z1,z2,z3,z4,z487,z5,z6]),(0,[z1,z399,z2,z3,z4,z5,z6]),(0,[z1,z2,z54,z3,z4,z11,z6])],[(0,[z26,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z209,z6]),(0,[z28,z2,z3,z4,z5,z6,z225]),(0,[z1,z2,z488,z3,z4,z5,z6]),(0,[z184,z1,z2,z3,z4,z129,z6]),(0,[z184,z1,z2,z21,z4,z5,z6]),(0,[z489,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z54,z3,z157,z5,z6]),(0,[z1,z2,z3,z4,z490,z5,z6])],[(0,[z35,z1,z2,z3,z4,z10,z6]),(0,[z179,z114,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z12,z10,z6]),(0,[z1,z2,z3,z4,z491,z5,z6])],[(0,[z28,z2,z3,z25,z4,z5,z6]),(0,[z1,z492,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z10,z6]),(0,[z184,z1,z2,z150,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z493]),(2,[z1,z21,z4,z10,z6]),(0,[z1,z2,z23,z320,z4,z5,z6]),(1,[z2,z85,z3,z4,z5,z6]),(0,[z1,z60,z2,z4,z5,z62,z6]),(0,[z1,z2,z195,z3,z4,z5,z6])],[(0,[z1,z2,z494,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z495,z5,z6]),(0,[z1,z3,z21,z4,z5,z10,z6]),(0,[z496,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z497,z5,z6]),(0,[z1,z2,z3,z25,z4,z10,z6])]],
   [[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z26,z1,z120,z3,z4,z5,z6]),(0,[z2,z16,z3,z4,z248,z5,z6]),(0,[z1,z30,z2,z67,z4,z5,z6]),(0,[z1,z498,z2,z3,z4,z5,z6]),(0,[z44,z1,z2,z145,z4,z5,z6]),(0,[z1,z2,z3,z4,z10,z6,z24]),(0,[z1,z118,z2,z3,z4,z5,z6])],[(0,[z1,z2,z27,z3,z4,z5,z6]),(1,[z1,z2,z499,z4,z5,z6]),(0,[z1,z84,z2,z3,z4,z5,z58]),(0,[z1,z2,z3,z4,z5,z6,z40])],[(0,[z1,z30,z2,z3,z4,z5,z63])],[(0,[z2,z16,z23,z3,z4,z5,z6]),(0,[z1,z2,z21,z4,z11,z5,z6]),(0,[z1,z2,z39,z21,z4,z5,z6]),(0,[z1,z2,z3,z500,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z501,z6]),(0,[z1,z2,z39,z3,z95,z4,z5])],[(0,[z2,z502,z16,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z503,z5,z6]),(0,[z1,z2,z3,z4,z10,z6,z225]),(0,[z1,z112,z3,z21,z4,z5,z6]),(0,[z1,z60,z2,z21,z4,z5,z6]),(0,[z100,z1,z2,z3,z90,z5,z6]),(0,[z102,z1,z2,z3,z4,z11,z6])],[(0,[z2,z3,z4,z129,z5,z161,z6]),(0,[z1,z114,z2,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z504,z6]),(0,[z1,z2,z54,z3,z4,z128,z5])],[(0,[z44,z2,z16,z3,z4,z5,z6]),(0,[z1,z2,z92,z3,z4,z5,z6])],[(0,[z505,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z251,z3,z4,z5,z6]),(0,[z1,z120,z2,z3,z4,z10,z6]),(0,[z1,z506,z2,z3,z4,z5,z6]),(0,[z44,z1,z2,z507,z4,z5,z6]),(0,[z1,z2,z21,z90,z4,z5,z6]),(0,[z78,z1,z2,z21,z4,z5,z6]),(0,[z1,z2,z3,z508,z4,z5,z6]),(0,[z1,z2,z3,z4,z509,z5,z6]),(0,[z1,z2,z3,z71,z4,z10,z6]),(0,[z1,z55,z2,z125,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z259,z4,z5,z6]),(0,[z510,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z511,z3,z4,z5,z6]),(0,[z1,z2,z21,z4,z512,z5,z6]),(0,[z1,z2,z3,z4,z11,z62,z6]),(0,[z496,z1,z2,z3,z4,z11,z6]),(0,[z513,z1,z2,z3,z4,z5,z6])],[(0,[z28,z2,z3,z4,z5,z6,z94]),(0,[z1,z120,z2,z3,z4,z514,z6]),(0,[z201,z2,z3,z29,z4,z5,z6]),(0,[z1,z2,z3,z515,z4,z5,z6]),(0,[z1,z2,z3,z4,z516,z5,z6]),(0,[z1,z2,z3,z4,z5,z58,z6])],[(1,[z2,z16,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z517,z5,z6]),(0,[z1,z55,z2,z21,z4,z5,z6]),(0,[z1,z2,z21,z4,z5,z6,z63]),(0,[z1,z84,z2,z23,z4,z5,z6]),(1,[z1,z2,z3,z4,z101,z6]),(0,[z1,z2,z3,z128,z5,z6,z17])],[(0,[z1,z2,z3,z4,z5,z518,z6]),(0,[z519,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z520,z5,z6]),(1,[z184,z2,z3,z4,z161,z6]),(0,[z1,z2,z3,z188,z4,z5,z6]),(0,[z368,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z521,z4,z5,z6]),(0,[z1,z2,z61,z3,z25,z5,z6])],[(0,[z1,z2,z3,z4,z514,z5,z6]),(0,[z1,z2,z3,z4,z163,z5,z6]),(0,[z1,z2,z2,z3,z4,z10,z6])],[(0,[z1,z2,z3,z4,z522,z5,z6]),(0,[z184,z1,z2,z3,z4,z161,z6]),(0,[z1,z2,z54,z21,z4,z5,z6]),(0,[z46,z1,z2,z452,z4,z5,z6])],[(0,[z100,z1,z2,z3,z12,z5,z6]),(0,[z1,z2,z3,z4,z5,z523,z6])]],
   [[(0,[z2,z16,z3,z4,z11,z5,z6]),(0,[z1,z524,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z281,z5,z6]),(0,[z183,z1,z2,z3,z4,z10,z6]),(0,[z1,z2,z507,z3,z4,z5,z6]),(1,[z1,z2,z3,z212,z10,z6]),(1,[z1,z2,z3,z5,z212,z6]),(0,[z1,z2,z3,z4,z509,z11,z6]),(0,[z1,z2,z525,z3,z4,z5,z6]),(0,[z1,z2,z3,z12,z5,z6,z94]),(0,[z1,z2,z3,z81,z4,z5,z17])],[(0,[z526,z1,z2,z3,z4,z5,z6]),(0,[z28,z2,z67,z3,z4,z5,z6]),(0,[z28,z184,z2,z3,z4,z5,z6]),(1,[z1,z2,z139,z4,z5,z6]),(0,[z527,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z59,z6]),(0,[z1,z2,z3,z4,z435,z5,z6]),(0,[z1,z528,z2,z3,z4,z5,z6]),(0,[z529,z1,z2,z3,z4,z5,z6])],[(0,[z134,z2,z16,z3,z4,z5,z6]),(0,[z1,z2,z67,z3,z4,z10,z6]),(0,[z530,z1,z2,z3,z4,z5,z6]),(0,[z1,z30,z2,z3,z426,z5,z6])],[(0,[z1,z2,z29,z4,z5,z146,z6]),(0,[z1,z2,z3,z4,z5,z531,z6]),(0,[z1,z2,z21,z4,z5,z146,z6]),(0,[z1,z2,z3,z4,z10,z6,z532]),(0,[z1,z2,z3,z4,z5,z6,z117]),(1,[z1,z301,z2,z4,z5,z6])],[(0,[z2,z16,z3,z90,z4,z5,z6]),(0,[z1,z2,z42,z29,z4,z5,z6]),(0,[z153,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z533,z3,z4,z5,z6]),(0,[z534,z1,z2,z3,z4,z5,z6])],[(0,[z2,z16,z39,z3,z4,z5,z6]),(1,[z1,z2,z535,z4,z5,z6]),(0,[z1,z2,z3,z536,z4,z5,z6]),(1,[z1,z2,z3,z4,z363,z6]),(0,[z1,z2,z3,z4,z248,z5,z6])],[(1,[z2,z16,z3,z4,z5,z6]),(0,[z28,z1,z16,z3,z4,z5,z6]),(0,[z537,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z4,z281,z5,z6]),(0,[z1,z538,z2,z3,z4,z5,z6]),(0,[z20,z1,z2,z3,z4,z5,z6]),(0,[z1,z539,z2,z3,z4,z5,z6]),(0,[z1,z84,z2,z3,z4,z5,z6]),(0,[z1,z2,z540,z3,z4,z5,z6])],[(0,[z541,z1,z2,z3,z4,z5,z6]),(0,[z33,z2,z16,z3,z4,z5,z6]),(0,[z2,z16,z3,z4,z5,z6,z63]),(0,[z28,z153,z2,z3,z4,z5,z6]),(0,[z1,z2,z542,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z129,z5,z6]),(1,[z1,z2,z507,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z543,z6]),(0,[z35,z1,z2,z23,z4,z5,z6]),(0,[z1,z544,z2,z3,z4,z5,z6]),(0,[z1,z2,z42,z3,z4,z10,z6])],[(0,[z43,z2,z16,z3,z4,z5,z6]),(0,[z184,z2,z67,z3,z4,z5,z6]),(0,[z545,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z281,z11,z6]),(0,[z1,z2,z3,z4,z546,z5,z6]),(0,[z1,z2,z3,z4,z547,z5,z6]),(1,[z1,z30,z2,z4,z5,z63]),(0,[z548,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z549,z4,z5,z6])],[(0,[z2,z16,z3,z4,z157,z5,z6]),(0,[z2,z3,z29,z4,z5,z161,z6]),(0,[z1,z550,z2,z3,z4,z5,z6]),(0,[z33,z1,z2,z3,z4,z91,z6])],[(0,[z1,z2,z3,z4,z551,z5,z6]),(0,[z1,z2,z23,z4,z248,z5,z6]),(0,[z1,z2,z3,z4,z5,z552,z6]),(0,[z1,z2,z3,z4,z10,z6,z17]),(0,[z1,z2,z3,z553,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z554]),(0,[z1,z2,z92,z4,z5,z62,z6])],[(0,[z0,z2,z16,z3,z4,z5,z6]),(0,[z1,z2,z555,z3,z4,z5,z6]),(0,[z1,z2,z25,z4,z5,z62,z6])],[(0,[z183,z35,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z556,z6]),(1,[z1,z23,z21,z4,z5,z6]),(0,[z135,z1,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z248,z11,z6]),(0,[z1,z2,z3,z4,z128,z5,z24])],[(1,[z2,z16,z3,z4,z11,z6]),(0,[z28,z2,z61,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z557]),(0,[z2,z3,z4,z5,z22,z6,z225]),(0,[z558,z1,z2,z21,z4,z5,z6]),(0,[z1,z2,z3,z559,z4,z5,z6]),(1,[z103,z2,z3,z4,z5,z6]),(0,[z1,z84,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z560,z4,z5,z6]),(0,[z1,z2,z3,z4,z561,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z562])]],
   [[(0,[z2,z16,z54,z3,z4,z5,z6]),(0,[z153,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z54,z3,z281,z5,z6]),(1,[z1,z2,z3,z4,z563,z6]),(0,[z1,z114,z2,z3,z90,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z24]),(0,[z1,z2,z564,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z565,z5,z6])],[(0,[z26,z1,z2,z3,z4,z200,z6]),(0,[z566,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z322,z6]),(0,[z1,z2,z23,z3,z4,z11,z6]),(1,[z2,z356,z3,z4,z5,z6]),(0,[z1,z84,z2,z37,z4,z5,z6])],[(0,[z1,z120,z2,z23,z4,z5,z6]),(1,[z1,z2,z3,z254,z5,z6]),(0,[z1,z2,z21,z4,z5,z6,z40]),(0,[z1,z2,z92,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z567]),(0,[z1,z2,z3,z4,z10,z6,z568]),(0,[z1,z2,z3,z95,z4,z6,z40]),(0,[z1,z2,z3,z569,z4,z5,z6])],[(0,[z1,z2,z3,z281,z5,z6,z17]),(1,[z361,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z570,z5,z6]),(0,[z571,z1,z2,z3,z4,z5,z6]),(1,[z1,z572,z3,z4,z5,z6])],[(0,[z35,z1,z2,z3,z4,z5,z6]),(1,[z43,z2,z29,z4,z5,z6]),(0,[z1,z2,z573,z3,z4,z5,z6]),(0,[z1,z2,z25,z4,z157,z5,z6]),(0,[z1,z170,z2,z3,z4,z5,z6]),(0,[z33,z1,z572,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z574,z6]),(0,[z1,z2,z3,z4,z12,z5,z6])],[(0,[z28,z112,z2,z3,z4,z5,z6]),(0,[z575,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z576,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z5,z6]),(0,[z1,z2,z3,z4,z5,z577,z6]),(0,[z1,z2,z578,z3,z4,z5,z6])],[(0,[z1,z112,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z579,z4,z5,z6]),(0,[z55,z2,z207,z3,z4,z5,z6]),(1,[z401,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z580]),(0,[z1,z2,z3,z71,z4,z6,z94]),(1,[z1,z2,z3,z4,z424,z6]),(0,[z1,z2,z3,z581,z4,z5,z6])],[(0,[z582,z1,z2,z3,z4,z5,z6]),(0,[z1,z583,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z584,z4,z5,z6]),(0,[z1,z2,z23,z158,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z585]),(0,[z1,z2,z3,z4,z586,z5,z6]),(0,[z1,z2,z587,z3,z4,z5,z6])]],
   [[(0,[z28,z2,z3,z4,z36,z5,z6]),(0,[z184,z2,z3,z4,z5,z22,z6]),(0,[z1,z2,z3,z4,z10,z22,z6]),(0,[z1,z2,z2,z23,z4,z5,z6])],[(0,[z28,z2,z3,z81,z4,z5,z6]),(0,[z153,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z54,z3,z18,z5,z6]),(0,[z1,z2,z588,z3,z4,z5,z6]),(0,[z1,z114,z2,z69,z4,z5,z6]),(0,[z1,z2,z54,z3,z90,z5,z6]),(0,[z46,z1,z2,z3,z4,z59,z6]),(0,[z1,z2,z3,z4,z5,z589,z6])],[(0,[z28,z30,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z4,z5,z58,z6]),(0,[z1,z2,z3,z4,z512,z5,z6]),(0,[z1,z2,z3,z81,z4,z10,z6]),(0,[z401,z1,z2,z3,z4,z5,z6])],[(0,[z590,z1,z2,z3,z4,z5,z6]),(0,[z183,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z23,z4,z11,z5,z6]),(0,[z1,z114,z2,z3,z12,z5,z6]),(0,[z46,z1,z3,z90,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z591,z6])],[(0,[z1,z2,z592,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z593])],[(1,[z1,z2,z3,z4,z132,z6]),(0,[z35,z1,z2,z3,z4,z11,z6]),(1,[z1,z2,z3,z4,z435,z6])],[(0,[z1,z120,z2,z3,z4,z5,z6]),(0,[z46,z2,z16,z3,z4,z5,z6]),(0,[z441,z1,z2,z3,z4,z5,z6]),(0,[z28,z2,z3,z4,z91,z5,z6]),(0,[z43,z1,z2,z4,z91,z5,z6]),(0,[z594,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z23,z4,z10,z6]),(0,[z1,z2,z3,z4,z11,z371,z6]),(0,[z1,z2,z3,z4,z11,z11,z6]),(0,[z595,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z596]),(0,[z1,z2,z3,z71,z4,z5,z6])],[(0,[z2,z16,z3,z4,z5,z6,z40]),(0,[z1,z2,z3,z597,z4,z5,z6]),(0,[z1,z2,z598,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z599]),(0,[z1,z2,z23,z90,z4,z5,z6]),(0,[z1,z2,z3,z4,z91,z10,z6])]],
   [[(0,[z1,z2,z600,z3,z4,z5,z6]),(1,[z1,z2,z3,z49,z5,z6]),(0,[z601,z1,z2,z3,z4,z5,z6])],[(0,[z602,z1,z2,z3,z4,z5,z6]),(0,[z183,z28,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z603,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z218])],[(1,[z2,z16,z21,z4,z5,z6]),(0,[z1,z604,z2,z3,z4,z5,z6]),(0,[z1,z84,z2,z21,z4,z5,z6]),(0,[z1,z2,z3,z605,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z6,z63]),(1,[z1,z60,z2,z157,z5,z6]),(0,[z1,z2,z3,z4,z5,z606,z6])],[(0,[z1,z2,z3,z4,z607,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z532]),(0,[z1,z2,z3,z4,z512,z11,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z2,z16,z92,z3,z4,z5,z6]),(1,[z28,z2,z3,z4,z10,z6]),(0,[z74,z1,z2,z3,z4,z5,z6]),(0,[z20,z1,z2,z4,z5,z161,z6]),(0,[z1,z2,z3,z4,z608,z5,z6]),(0,[z1,z544,z2,z21,z4,z5,z6]),(1,[z159,z2,z3,z4,z5,z6]),(0,[z1,z2,z535,z3,z4,z5,z6]),(0,[z1,z60,z2,z3,z4,z11,z6]),(0,[z1,z2,z54,z3,z12,z5,z6]),(0,[z1,z2,z609,z3,z4,z5,z6])],[(0,[z610,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z281,z5,z6]),(0,[z46,z100,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z10,z10,z6]),(1,[z1,z2,z3,z325,z5,z6]),(1,[z223,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z146,z6]),(0,[z1,z2,z3,z4,z5,z6,z611]),(0,[z612,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z319,z5,z6])],[(0,[z1,z2,z3,z613,z4,z5,z6]),(0,[z1,z2,z3,z614,z4,z5,z6]),(0,[z1,z615,z2,z3,z4,z5,z6])],[(0,[z2,z16,z3,z4,z5,z58,z6]),(0,[z1,z224,z2,z3,z4,z5,z6]),(0,[z28,z2,z3,z4,z5,z62,z6]),(0,[z183,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z71,z4,z11,z6])]],
   [[(0,[z1,z2,z3,z616,z4,z5,z6]),(0,[z1,z2,z21,z4,z129,z5,z6]),(1,[z183,z2,z3,z4,z5,z225]),(0,[z617,z1,z2,z3,z4,z5,z6]),(0,[z1,z134,z2,z3,z4,z563,z6]),(0,[z1,z2,z592,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z618,z6]),(0,[z619,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z67,z3,z4,z5,z6]),(0,[z1,z2,z3,z18,z4,z10,z6]),(0,[z1,z620,z2,z3,z4,z5,z6]),(1,[z621,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z622,z6])],[(0,[z1,z2,z3,z623,z4,z5,z6]),(0,[z2,z16,z3,z521,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z10,z6]),(0,[z624,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z4,z546,z5,z6]),(1,[z1,z2,z3,z4,z10,z6]),(0,[z1,z3,z4,z5,z58,z6,z24]),(0,[z1,z2,z3,z4,z5,z6,z625]),(0,[z1,z2,z42,z3,z4,z91,z6]),(0,[z1,z30,z2,z3,z4,z5,z62])],[(0,[z2,z16,z626,z3,z4,z5,z6]),(0,[z28,z44,z2,z3,z4,z5,z6]),(0,[z1,z120,z2,z3,z4,z52,z6]),(1,[z410,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z563,z6]),(0,[z1,z2,z3,z4,z5,z6,z167]),(1,[z1,z2,z3,z4,z5,z241]),(0,[z1,z2,z3,z381,z4,z5,z6]),(0,[z33,z1,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z5,z6,z627]),(0,[z1,z2,z3,z4,z5,z6,z17])],[(0,[z309,z2,z16,z3,z4,z5,z6]),(0,[z628,z28,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z514,z6]),(0,[z629,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z630,z3,z4,z5,z6]),(0,[z153,z1,z2,z21,z4,z5,z6]),(0,[z1,z2,z4,z5,z283,z161,z6]),(0,[z1,z2,z3,z139,z4,z5,z6])],[(0,[z135,z2,z16,z3,z4,z5,z6]),(0,[z1,z2,z67,z42,z4,z5,z6]),(1,[z1,z55,z21,z4,z5,z6]),(0,[z631,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z2,z3,z4,z11,z6]),(0,[z1,z2,z4,z5,z6,z466,z17])],[(0,[z1,z120,z2,z75,z4,z5,z6]),(0,[z201,z1,z2,z3,z4,z10,z6]),(0,[z100,z1,z2,z535,z4,z5,z6]),(0,[z1,z2,z3,z4,z363,z6,z17])],[(0,[z33,z35,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z90,z5,z6,z17]),(0,[z1,z84,z2,z3,z4,z185,z6]),(0,[z1,z2,z42,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z632,z6])]],
   [[(0,[z35,z1,z2,z21,z4,z5,z6]),(0,[z1,z2,z23,z67,z4,z5,z6]),(1,[z1,z2,z303,z4,z5,z6]),(0,[z183,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z6,z633]),(0,[z1,z2,z3,z4,z634,z5,z6]),(0,[z1,z2,z3,z635,z4,z5,z6])],[(0,[z1,z2,z21,z4,z5,z6,z24]),(0,[z575,z1,z2,z21,z4,z5,z6]),(0,[z114,z2,z356,z3,z4,z5,z6])],[(0,[z628,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z406,z5,z6]),(0,[z1,z2,z3,z4,z101,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z568]),(0,[z1,z55,z2,z321,z4,z5,z6]),(0,[z1,z636,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z637,z5,z6]),(0,[z1,z2,z3,z4,z5,z638,z6]),(0,[z1,z2,z3,z4,z5,z6,z639]),(0,[z1,z2,z3,z4,z5,z192,z6]),(1,[z595,z2,z3,z4,z5,z6]),(0,[z33,z170,z2,z3,z4,z5,z6]),(0,[z1,z2,z70,z3,z4,z5,z6]),(1,[z293,z2,z3,z4,z5,z6])],[(0,[z1,z2,z626,z23,z4,z5,z6]),(0,[z640,z1,z2,z3,z4,z5,z6]),(0,[z237,z1,z2,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z5,z6,z17]),(0,[z1,z2,z641,z3,z4,z5,z6])],[(0,[z2,z16,z3,z4,z129,z5,z6]),(0,[z1,z2,z502,z3,z4,z5,z6]),(0,[z1,z2,z21,z4,z5,z6,z225]),(0,[z44,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z21,z4,z12,z5,z6]),(0,[z642,z1,z2,z3,z4,z5,z6])],[(1,[z1,z19,z3,z4,z5,z6]),(0,[z558,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z643]),(0,[z484,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z644,z3,z4,z5,z6]),(0,[z368,z2,z3,z4,z5,z6,z17])],[(1,[z1,z120,z3,z4,z10,z6]),(0,[z1,z2,z21,z25,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z6,z434]),(0,[z1,z645,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z646,z4,z5,z6]),(0,[z1,z2,z3,z647,z4,z5,z6]),(0,[z1,z2,z3,z4,z648,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z132,z6]),(0,[z1,z2,z3,z4,z5,z22,z6]),(0,[z1,z3,z4,z11,z5,z10,z6]),(0,[z46,z1,z2,z3,z49,z5,z6]),(0,[z1,z60,z2,z4,z157,z5,z6]),(0,[z1,z2,z3,z4,z649,z5,z6])],[(0,[z1,z2,z3,z4,z650,z5,z6]),(0,[z183,z1,z2,z3,z4,z5,z22]),(1,[z1,z2,z3,z4,z113,z6]),(0,[z1,z114,z2,z3,z4,z360,z6]),(1,[z1,z2,z193,z3,z5,z6])],[(0,[z28,z2,z16,z3,z4,z5,z6]),(0,[z1,z120,z2,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z651,z6]),(0,[z1,z2,z23,z4,z5,z6,z40])],[(0,[z55,z2,z16,z3,z4,z5,z6]),(0,[z176,z1,z2,z3,z4,z5,z6]),(0,[z43,z35,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z652]),(0,[z653,z1,z2,z3,z4,z5,z6])],[(0,[z35,z1,z2,z67,z4,z5,z6]),(0,[z654,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z42,z4,z91,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z119])],[(0,[z1,z2,z3,z4,z5,z655,z6]),(0,[z1,z2,z122,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z325,z5,z6]),(0,[z1,z2,z3,z157,z5,z6,z17])],[(0,[z2,z16,z3,z4,z5,z6,z24]),(0,[z238,z2,z16,z3,z4,z5,z6]),(0,[z153,z1,z2,z3,z281,z5,z6]),(0,[z1,z2,z3,z656,z4,z5,z6]),(0,[z183,z2,z3,z4,z129,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z657]),(0,[z1,z2,z3,z4,z5,z115,z6]),(0,[z1,z2,z499,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z258])],[(1,[z28,z2,z23,z4,z5,z6]),(0,[z1,z120,z3,z4,z5,z10,z6]),(0,[z1,z2,z67,z4,z5,z62,z6]),(0,[z1,z2,z658,z3,z4,z5,z6]),(0,[z1,z2,z21,z71,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z6,z63]),(0,[z1,z2,z3,z659,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z660]),(0,[z1,z2,z3,z4,z5,z661,z6])]],
   [[(0,[z1,z2,z626,z3,z4,z5,z6]),(0,[z662,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z2,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z663,z5,z6]),(0,[z1,z2,z3,z664,z4,z5,z6])],[(0,[z28,z134,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z665,z6]),(0,[z1,z2,z3,z4,z666,z5,z6]),(0,[z44,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z508,z21,z4,z5,z6]),(0,[z100,z1,z2,z3,z4,z5,z168]),(0,[z1,z667,z2,z3,z4,z5,z6]),(1,[z46,z1,z3,z4,z5,z24])],[(0,[z2,z16,z3,z4,z12,z5,z6]),(0,[z28,z2,z3,z4,z128,z5,z6]),(0,[z1,z2,z3,z4,z668,z5,z6]),(0,[z1,z134,z2,z3,z4,z10,z6]),(0,[z1,z2,z23,z4,z5,z58,z6]),(0,[z1,z669,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z10,z6]),(0,[z1,z2,z92,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z670,z6])],[(0,[z120,z2,z16,z3,z4,z5,z6]),(0,[z671,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z281,z5,z6]),(0,[z1,z2,z3,z4,z11,z161,z6]),(0,[z183,z1,z2,z21,z4,z5,z6]),(1,[z1,z2,z145,z4,z5,z6]),(0,[z1,z672,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z128,z10,z6]),(0,[z621,z1,z2,z3,z4,z5,z6]),(0,[z1,z343,z2,z3,z4,z5,z6])],[(0,[z1,z2,z673,z3,z4,z5,z6]),(1,[z411,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z10,z6,z94]),(0,[z1,z2,z3,z4,z674,z5,z6]),(0,[z1,z2,z675,z3,z4,z5,z6])],[(0,[z1,z2,z3,z454,z4,z5,z6]),(0,[z1,z2,z67,z21,z4,z5,z6]),(1,[z1,z2,z23,z4,z5,z6]),(0,[z1,z114,z2,z381,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z10,z6]),(0,[z1,z458,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z17])],[(0,[z1,z2,z3,z4,z5,z676,z6]),(0,[z1,z2,z3,z4,z297,z5,z6]),(1,[z1,z2,z21,z4,z10,z6]),(0,[z33,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z321,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z345,z6])],[(0,[z1,z2,z3,z4,z677,z5,z6]),(0,[z153,z1,z2,z3,z18,z5,z6]),(0,[z678,z1,z2,z3,z4,z5,z6]),(0,[z179,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z679,z5,z6]),(0,[z1,z572,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z248,z5,z40])]],
   [[(0,[z43,z1,z2,z23,z4,z5,z6]),(0,[z1,z114,z3,z90,z4,z5,z6]),(0,[z102,z1,z2,z499,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z680])],[(0,[z1,z2,z3,z4,z681,z5,z6]),(0,[z621,z2,z92,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z424,z6,z17])],[(0,[z44,z1,z2,z3,z4,z11,z6])],[(1,[z28,z2,z3,z4,z5,z6]),(0,[z1,z682,z2,z3,z4,z5,z6]),(0,[z1,z2,z42,z21,z4,z5,z6]),(0,[z46,z595,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z683,z4,z5,z6]),(0,[z1,z301,z2,z4,z5,z6,z17])],[(0,[z2,z16,z3,z71,z4,z5,z6]),(0,[z33,z28,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z23,z4,z5,z6]),(1,[z1,z112,z21,z4,z5,z6]),(0,[z1,z2,z21,z4,z5,z6,z17]),(0,[z1,z2,z23,z61,z4,z5,z6]),(0,[z1,z30,z60,z2,z4,z5,z6])],[(0,[z201,z2,z16,z3,z4,z5,z6]),(0,[z35,z2,z67,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z684,z6]),(0,[z1,z134,z23,z3,z4,z5,z6]),(0,[z685,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z248,z40])],[(0,[z686,z1,z2,z3,z4,z5,z6]),(0,[z43,z28,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z687]),(0,[z628,z1,z2,z21,z4,z5,z6]),(1,[z1,z2,z23,z4,z11,z6]),(0,[z1,z688,z2,z3,z4,z5,z6]),(1,[z78,z1,z2,z3,z6,z94]),(0,[z1,z2,z3,z4,z5,z689,z6]),(0,[z1,z2,z39,z3,z4,z248,z6])],[(0,[z60,z2,z16,z3,z4,z5,z6]),(0,[z690,z28,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z360,z5,z6]),(0,[z1,z2,z3,z4,z426,z5,z6]),(1,[z2,z195,z3,z4,z5,z6]),(0,[z691,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z692]),(0,[z1,z2,z3,z4,z5,z6,z466]),(0,[z1,z2,z3,z693,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z694,z6]),(0,[z1,z2,z3,z18,z4,z5,z6]),(0,[z1,z2,z23,z4,z129,z5,z6]),(0,[z695,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z696]),(0,[z1,z2,z3,z4,z697,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z5,z6]),(0,[z2,z3,z18,z4,z281,z5,z6]),(0,[z1,z2,z3,z698,z4,z5,z6]),(0,[z411,z1,z2,z3,z4,z5,z6]),(0,[z1,z151,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z699]),(1,[z118,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z700,z4,z5,z6])],[(0,[z0,z28,z2,z3,z4,z5,z6]),(0,[z1,z55,z3,z21,z4,z5,z6]),(0,[z1,z2,z53,z23,z4,z5,z6]),(0,[z33,z1,z2,z3,z4,z5,z6])],[(0,[z2,z16,z3,z4,z5,z146,z6]),(0,[z1,z2,z3,z4,z5,z6,z476]),(0,[z1,z2,z3,z4,z129,z11,z6]),(0,[z44,z1,z2,z3,z4,z5,z22]),(0,[z100,z1,z2,z3,z4,z10,z6]),(0,[z1,z2,z61,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z5,z6,z701])],[(1,[z28,z2,z3,z4,z11,z6]),(0,[z43,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z552,z6]),(1,[z1,z2,z203,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z58])],[(0,[z690,z1,z2,z3,z4,z5,z6]),(0,[z46,z1,z3,z4,z5,z6,z24]),(0,[z1,z2,z702,z3,z4,z5,z6])],[(0,[z703,z1,z2,z3,z4,z5,z6]),(0,[z33,z1,z2,z42,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z704])],[(0,[z2,z16,z67,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z705,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z225]),(0,[z1,z112,z2,z3,z4,z130,z6]),(0,[z1,z2,z166,z3,z4,z5,z6]),(0,[z1,z2,z3,z36,z5,z6,z17]),(0,[z1,z2,z3,z4,z11,z6,z40]),(0,[z140,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z61,z25,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z28,z2,z3,z4,z185,z6]),(0,[z1,z707,z3,z4,z5,z6]),(0,[z183,z2,z3,z4,z11,z225]),(0,[z1,z2,z3,z4,z708,z6])],[(0,[z1,z2,z3,z4,z709,z6]),(0,[z28,z2,z3,z188,z5,z6]),(0,[z401,z2,z21,z4,z5,z6]),(0,[z1,z2,z21,z4,z424,z6])],[(0,[z16,z3,z4,z10,z6,z24]),(0,[z28,z2,z193,z3,z5,z6]),(0,[z1,z70,z4,z5,z62,z6]),(0,[z710,z2,z3,z4,z5,z6])],[(0,[z2,z16,z3,z4,z200,z6]),(0,[z1,z2,z4,z5,z711,z6]),(0,[z1,z112,z21,z4,z113,z6]),(0,[z1,z2,z3,z4,z712,z6])],[(0,[z713,z2,z3,z4,z5,z6]),(0,[z1,z2,z714,z4,z5,z6]),(0,[z2,z207,z321,z4,z5,z6]),(0,[z715,z2,z3,z4,z5,z6])],[(0,[z1,z19,z3,z4,z5,z6]),(0,[z1,z166,z21,z4,z10,z6]),(0,[z716,z2,z3,z4,z10,z6]),(0,[z170,z2,z42,z4,z5,z6]),(1,[z1,z70,z4,z146,z6]),(0,[z1,z2,z717,z4,z5,z6])],[(0,[z1,z120,z3,z4,z10,z6]),(0,[z2,z16,z3,z297,z5,z6]),(0,[z1,z2,z3,z4,z718,z6]),(0,[z1,z2,z3,z4,z185,z6]),(0,[z719,z2,z3,z4,z5,z6])],[(1,[z16,z3,z4,z132,z6]),(0,[z184,z2,z3,z4,z607,z6]),(0,[z1,z2,z3,z188,z5,z6])],[(0,[z1,z70,z21,z4,z5,z6]),(0,[z1,z2,z21,z4,z435,z6])],[(0,[z16,z21,z90,z4,z5,z6]),(0,[z16,z3,z71,z4,z10,z6]),(0,[z183,z2,z3,z4,z5,z720]),(0,[z1,z2,z721,z4,z5,z6]),(0,[z164,z1,z3,z36,z5,z6]),(0,[z2,z356,z381,z4,z5,z6])],[(0,[z2,z16,z3,z4,z722,z5]),(0,[z19,z16,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z723]),(0,[z1,z2,z321,z4,z10,z6]),(0,[z601,z1,z3,z4,z10,z6]),(0,[z724,z2,z3,z4,z5,z6])],[(0,[z43,z2,z725,z4,z5,z6]),(0,[z726,z2,z23,z4,z5,z6]),(0,[z1,z727,z2,z4,z5,z6])],[(0,[z237,z16,z3,z5,z10,z6]),(0,[z28,z2,z145,z4,z5,z6]),(0,[z2,z725,z29,z4,z5,z6]),(0,[z728,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z729,z6]),(0,[z1,z2,z3,z4,z730,z6]),(0,[z1,z301,z2,z426,z5,z6])],[(0,[z78,z1,z21,z4,z10,z6])],[(0,[z28,z2,z23,z4,z5,z6]),(0,[z1,z2,z731,z4,z5,z6]),(0,[z2,z303,z4,z5,z161,z6]),(0,[z1,z2,z23,z4,z208,z6])],[(0,[z1,z2,z3,z4,z732,z6]),(0,[z2,z16,z3,z426,z5,z6]),(0,[z2,z16,z277,z4,z5,z6]),(0,[z1,z506,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z113,z6]),(0,[z1,z2,z3,z4,z733,z5])]],
   [[(0,[z1,z2,z734,z4,z5,z6]),(0,[z735,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z4,z248,z40]),(0,[z1,z620,z3,z4,z10,z6]),(0,[z1,z2,z3,z188,z11,z6])],[(0,[z736,z2,z3,z4,z5,z6]),(0,[z35,z2,z588,z4,z5,z6]),(0,[z1,z2,z3,z737,z5,z6]),(0,[z1,z21,z4,z10,z6,z225]),(0,[z100,z1,z3,z36,z5,z168]),(0,[z140,z2,z3,z4,z10,z6]),(0,[z738,z1,z2,z4,z5,z6]),(0,[z1,z2,z193,z3,z11,z6]),(0,[z1,z2,z37,z4,z185,z6])],[(0,[z1,z2,z739,z4,z5,z6]),(0,[z740,z1,z2,z3,z4,z6]),(0,[z1,z741,z3,z4,z5,z6]),(0,[z1,z30,z2,z426,z5,z63])],[(0,[z79,z16,z3,z4,z5,z6]),(0,[z183,z2,z21,z4,z5,z225]),(0,[z1,z742,z3,z4,z5,z6])],[(0,[z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z743,z5,z6]),(0,[z44,z1,z21,z4,z10,z6])],[(0,[z16,z3,z4,z10,z6,z532]),(0,[z204,z16,z3,z4,z5,z6]),(0,[z232,z2,z203,z4,z5,z6]),(0,[z1,z2,z96,z4,z10,z6]),(0,[z1,z744,z2,z4,z5,z6])],[(0,[z16,z533,z3,z4,z5,z6]),(0,[z28,z2,z3,z4,z248,z40]),(0,[z1,z21,z4,z5,z6,z119]),(0,[z1,z2,z745,z4,z5,z6]),(0,[z1,z2,z4,z11,z6,z466])],[(0,[z16,z3,z4,z10,z146,z6]),(0,[z335,z16,z3,z4,z5,z6]),(0,[z28,z2,z23,z4,z11,z6]),(0,[z1,z2,z21,z4,z514,z6]),(0,[z726,z2,z3,z4,z5,z6]),(0,[z151,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z746,z5,z6]),(0,[z1,z747,z3,z4,z5,z6])],[(0,[z1,z122,z303,z4,z5,z6]),(0,[z1,z124,z21,z4,z10,z6]),(0,[z748,z2,z21,z4,z5,z6]),(0,[z151,z2,z3,z4,z5,z241])],[(0,[z78,z16,z3,z4,z10,z6]),(0,[z28,z21,z4,z5,z10,z6]),(0,[z749,z2,z23,z4,z5,z6])],[(0,[z28,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z750,z6]),(0,[z1,z2,z751,z4,z5,z6]),(0,[z1,z2,z3,z4,z208,z6]),(0,[z752,z2,z3,z4,z5,z6]),(0,[z738,z1,z2,z4,z11,z6])],[(0,[z1,z2,z21,z753,z5,z6]),(0,[z1,z321,z21,z4,z5,z6]),(0,[z1,z2,z23,z4,z298,z6]),(0,[z2,z3,z4,z10,z754,z6]),(0,[z368,z2,z3,z4,z10,z6])],[(0,[z1,z2,z3,z4,z755,z6]),(0,[z1,z2,z3,z4,z248,z40])],[(0,[z16,z3,z4,z10,z6,z17]),(0,[z46,z28,z3,z4,z5,z24]),(0,[z1,z2,z23,z4,z11,z6]),(0,[z1,z756,z21,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z757])],[(0,[z35,z16,z3,z4,z10,z6]),(0,[z1,z2,z758,z4,z5,z6]),(0,[z1,z2,z759,z4,z5,z6]),(0,[z1,z253,z3,z4,z10,z6]),(0,[z1,z21,z4,z10,z6,z94]),(0,[z1,z744,z2,z4,z11,z6])],[(0,[z60,z16,z3,z4,z10,z6]),(0,[z760,z2,z3,z4,z5,z6]),(0,[z1,z21,z4,z5,z10,z6]),(0,[z1,z761,z3,z4,z5,z6]),(0,[z572,z762,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z27,z4,z132,z6]),(0,[z114,z16,z3,z4,z10,z6]),(0,[z763,z55,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z764]),(0,[z765,z2,z3,z4,z5,z6])],[(0,[z28,z2,z3,z4,z298,z6]),(0,[z1,z2,z23,z4,z52,z6]),(0,[z1,z2,z3,z4,z5,z766]),(0,[z1,z19,z21,z4,z5,z6]),(0,[z1,z482,z3,z4,z10,z6]),(1,[z1,z21,z212,z10,z6]),(0,[z1,z458,z2,z4,z146,z6]),(0,[z1,z60,z2,z426,z5,z6])],[(0,[z1,z2,z767,z4,z5,z6]),(0,[z1,z120,z21,z4,z10,z6]),(0,[z7,z112,z21,z4,z5,z6]),(0,[z1,z2,z21,z4,z185,z6]),(0,[z1,z2,z768,z4,z5,z6])],[(0,[z28,z2,z3,z4,z11,z6]),(0,[z1,z2,z21,z188,z5,z6]),(0,[z100,z1,z3,z36,z10,z6]),(0,[z2,z3,z4,z5,z6,z769]),(0,[z770,z2,z3,z4,z5,z6])],[(0,[z16,z3,z4,z10,z6,z568]),(0,[z1,z2,z3,z771,z4,z5]),(0,[z384,z2,z158,z4,z5,z6]),(0,[z1,z2,z23,z319,z5,z6]),(0,[z1,z2,z4,z711,z10,z6])],[(0,[z43,z16,z3,z4,z10,z6]),(0,[z749,z2,z3,z4,z5,z6]),(0,[z772,z2,z3,z4,z5,z6])],[(0,[z286,z1,z2,z4,z146,z6]),(0,[z1,z2,z3,z4,z773,z6])],[(0,[z28,z2,z3,z4,z52,z6]),(0,[z43,z122,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z774,z6]),(0,[z1,z2,z3,z4,z298,z6])],[(0,[z2,z16,z3,z319,z5,z6]),(0,[z20,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z775,z6]),(0,[z183,z2,z3,z297,z5,z225]),(0,[z1,z2,z776,z4,z5,z6]),(0,[z1,z61,z21,z4,z10,z6])],[(0,[z1,z2,z3,z4,z11,z6]),(0,[z28,z70,z3,z4,z5,z6])],[(0,[z1,z21,z4,z697,z5,z6])],[(0,[z16,z626,z3,z4,z10,z6]),(0,[z28,z2,z83,z4,z5,z6]),(1,[z410,z3,z4,z10,z6]),(0,[z1,z2,z3,z771,z4,z10]),(0,[z1,z2,z3,z4,z777,z6])],[(0,[z237,z1,z16,z3,z10,z6]),(0,[z33,z1,z2,z4,z552,z6]),(0,[z78,z1,z2,z3,z298,z6]),(0,[z2,z356,z3,z4,z115,z6]),(0,[z164,z1,z3,z325,z5,z6]),(0,[z1,z778,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z52,z6]),(0,[z1,z2,z27,z4,z10,z6]),(0,[z26,z16,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z779,z6]),(0,[z2,z780,z3,z4,z5,z6])],[(0,[z88,z16,z3,z4,z10,z6]),(0,[z2,z16,z3,z781,z5,z6]),(0,[z782,z2,z3,z4,z5,z6]),(0,[z2,z67,z4,z5,z280,z6]),(0,[z183,z2,z303,z4,z5,z6]),(0,[z749,z2,z3,z4,z11,z6]),(0,[z760,z70,z3,z4,z5,z6])],[(0,[z35,z2,z67,z4,z5,z6]),(0,[z2,z21,z4,z5,z6,z218]),(0,[z1,z2,z783,z4,z10,z6])]],
   [[(0,[z35,z2,z4,z5,z480,z6]),(0,[z1,z122,z3,z4,z290,z6]),(0,[z784,z2,z3,z4,z5,z6]),(0,[z1,z2,z785,z4,z5,z6]),(0,[z1,z2,z3,z319,z5,z6])],[(0,[z1,z2,z3,z4,z5,z786]),(0,[z20,z1,z2,z4,z11,z6]),(0,[z1,z2,z83,z4,z5,z6]),(0,[z787,z2,z3,z4,z5,z6]),(0,[z1,z2,z788,z4,z5,z6])],[(0,[z2,z16,z499,z4,z5,z6]),(0,[z628,z2,z508,z4,z5,z6]),(0,[z164,z1,z3,z4,z5,z241]),(1,[z1,z203,z4,z10,z6])],[(0,[z176,z2,z3,z4,z322,z6]),(0,[z28,z2,z125,z4,z5,z6]),(0,[z237,z1,z2,z3,z6,z94]),(0,[z1,z2,z789,z4,z5,z6])],[(0,[z16,z3,z4,z5,z606,z6]),(0,[z411,z2,z3,z4,z163,z6])],[(0,[z16,z3,z4,z607,z5,z6]),(0,[z16,z3,z4,z129,z10,z6]),(0,[z2,z600,z67,z4,z5,z6]),(0,[z1,z2,z4,z5,z790,z6]),(0,[z1,z112,z21,z4,z130,z6]),(0,[z33,z1,z2,z4,z574,z6])],[(0,[z28,z2,z21,z4,z5,z6]),(0,[z16,z23,z21,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z791]),(0,[z1,z114,z21,z4,z10,z6]),(0,[z1,z2,z21,z4,z208,z6]),(0,[z100,z1,z3,z36,z101,z6]),(0,[z1,z572,z321,z4,z5,z6]),(0,[z1,z30,z2,z4,z5,z382]),(0,[z33,z223,z2,z4,z5,z6])],[(0,[z1,z55,z756,z4,z5,z6])],[(0,[z792,z2,z3,z4,z5,z6]),(0,[z793,z1,z2,z4,z5,z6]),(0,[z28,z2,z150,z4,z5,z6]),(0,[z35,z2,z67,z4,z11,z6]),(0,[z2,z67,z303,z4,z5,z6]),(0,[z1,z2,z21,z4,z248,z40]),(0,[z1,z413,z3,z4,z10,z6]),(0,[z1,z70,z3,z4,z11,z6])],[(0,[z26,z16,z3,z4,z5,z6]),(0,[z1,z2,z125,z4,z5,z6]),(0,[z1,z2,z69,z4,z10,z6]),(0,[z1,z2,z3,z794,z5,z6])],[(0,[z1,z375,z21,z4,z5,z6]),(0,[z1,z2,z83,z4,z11,z6])],[(0,[z795,z2,z3,z4,z5,z6]),(0,[z1,z2,z796,z4,z5,z6]),(0,[z103,z2,z499,z4,z5,z6]),(0,[z1,z2,z797,z3,z5,z6])],[(0,[z1,z2,z21,z4,z5,z6]),(0,[z16,z3,z29,z4,z10,z6]),(0,[z184,z2,z4,z283,z161,z6]),(0,[z1,z2,z798,z4,z5,z6]),(0,[z799,z3,z4,z5,z6,z119])],[(0,[z1,z244,z3,z4,z10,z6])],[(0,[z432,z16,z3,z4,z5,z6]),(0,[z301,z2,z16,z4,z5,z6])],[(0,[z2,z800,z3,z4,z5,z6]),(0,[z28,z2,z21,z4,z11,z6]),(0,[z1,z2,z3,z4,z801,z5])]],
   [[(0,[z55,z16,z23,z4,z5,z6]),(0,[z1,z120,z277,z4,z10,z6]),(0,[z1,z260,z21,z4,z5,z6]),(0,[z1,z802,z3,z4,z5,z6]),(0,[z1,z544,z21,z4,z10,z6]),(0,[z1,z21,z95,z4,z10,z6]),(0,[z1,z2,z21,z771,z4,z5]),(0,[z1,z2,z3,z4,z803,z6]),(0,[z1,z2,z3,z4,z733,z6])],[(0,[z2,z16,z381,z4,z5,z6]),(0,[z2,z16,z3,z212,z10,z6]),(0,[z7,z2,z3,z4,z130,z6])],[(0,[z1,z2,z23,z4,z200,z6]),(0,[z28,z2,z804,z4,z5,z6]),(0,[z2,z3,z4,z10,z6,z805]),(0,[z1,z2,z125,z4,z11,z6]),(0,[z2,z3,z4,z11,z806,z6]),(0,[z1,z807,z3,z4,z5,z6])],[(0,[z16,z21,z4,z5,z6,z24]),(0,[z143,z2,z626,z4,z5,z6]),(0,[z1,z2,z21,z4,z298,z6]),(0,[z237,z1,z21,z5,z10,z6]),(0,[z2,z808,z3,z4,z5,z6]),(0,[z102,z1,z3,z212,z10,z6]),(0,[z1,z2,z3,z4,z809,z6])],[(0,[z16,z3,z25,z4,z10,z6]),(0,[z441,z2,z3,z226,z5,z6]),(0,[z810,z2,z16,z3,z5,z6]),(0,[z1,z2,z3,z4,z811,z6]),(0,[z1,z3,z4,z812,z10,z6]),(0,[z1,z2,z4,z5,z813,z63]),(0,[z1,z301,z2,z81,z5,z17])],[(0,[z2,z16,z814,z4,z5,z6]),(0,[z88,z2,z3,z4,z161,z6]),(0,[z1,z2,z23,z297,z5,z6]),(0,[z1,z2,z21,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z815]),(0,[z1,z2,z3,z4,z816,z6])],[(0,[z2,z16,z535,z4,z5,z6]),(0,[z1,z21,z4,z10,z6,z256]),(0,[z1,z2,z3,z4,z801,z10]),(0,[z1,z3,z4,z10,z6,z352]),(0,[z1,z2,z3,z81,z363,z17])],[(0,[z122,z16,z3,z4,z10,z6]),(0,[z2,z16,z3,z81,z5,z17]),(0,[z1,z2,z150,z4,z11,z6]),(0,[z1,z2,z3,z4,z817,z6]),(0,[z1,z818,z3,z4,z5,z6])],[(0,[z28,z2,z3,z4,z200,z6]),(0,[z1,z2,z804,z4,z5,z6]),(0,[z1,z2,z3,z4,z819,z6]),(0,[z1,z2,z3,z4,z820,z6]),(0,[z1,z2,z4,z5,z6,z821])],[(0,[z16,z3,z4,z10,z6,z225]),(0,[z88,z1,z3,z4,z10,z6]),(0,[z1,z2,z21,z4,z52,z6]),(0,[z155,z2,z29,z4,z5,z6]),(0,[z237,z1,z2,z21,z10,z6]),(0,[z232,z2,z23,z4,z5,z6]),(0,[z1,z2,z822,z4,z5,z6]),(0,[z1,z2,z4,z10,z6,z823]),(0,[z1,z675,z3,z4,z11,z6])],[(0,[z1,z2,z3,z4,z824,z6])],[(1,[z16,z23,z4,z10,z6]),(0,[z28,z2,z3,z297,z5,z6]),(0,[z1,z29,z21,z4,z10,z6]),(1,[z1,z21,z4,z10,z6]),(0,[z1,z21,z21,z4,z10,z6]),(0,[z1,z2,z825,z4,z5,z6]),(0,[z164,z826,z3,z4,z5,z6])],[(0,[z55,z16,z3,z4,z5,z6]),(0,[z28,z144,z3,z4,z5,z6]),(0,[z1,z2,z21,z319,z5,z6]),(0,[z1,z21,z4,z157,z10,z6]),(0,[z1,z21,z4,z10,z62,z6])],[(0,[z84,z16,z3,z4,z10,z6])],[(0,[z1,z2,z3,z4,z200,z6]),(0,[z1,z827,z2,z4,z5,z6]),(0,[z1,z21,z169,z4,z10,z6]),(0,[z1,z2,z23,z426,z5,z6]),(0,[z1,z2,z3,z828,z10,z6])],[(0,[z1,z2,z829,z4,z5,z6]),(0,[z830,z2,z16,z4,z5,z6]),(0,[z2,z29,z4,z5,z665,z6]),(0,[z1,z2,z4,z11,z6,z51])]],
   [[(0,[z1,z2,z3,z4,z831,z6]),(0,[z832,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z297,z5,z6]),(0,[z1,z2,z833,z4,z5,z6])],[(0,[z88,z2,z3,z4,z234,z6]),(0,[z1,z2,z834,z4,z5,z6]),(0,[z0,z2,z23,z281,z5,z6]),(0,[z1,z3,z4,z11,z638,z6]),(0,[z1,z2,z3,z835,z5,z6])],[(0,[z33,z28,z2,z4,z146,z6]),(0,[z2,z3,z836,z281,z5,z6]),(0,[z2,z85,z3,z4,z10,z6]),(0,[z1,z343,z2,z4,z10,z6]),(0,[z1,z2,z3,z4,z5,z837]),(0,[z33,z2,z4,z137,z146,z6]),(0,[z1,z2,z838,z4,z5,z6])],[(0,[z28,z2,z3,z426,z5,z6]),(0,[z1,z2,z139,z4,z5,z168]),(0,[z1,z2,z839,z4,z5,z6]),(0,[z1,z2,z840,z4,z5,z6])],[(0,[z232,z2,z3,z4,z5,z6]),(0,[z26,z16,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z722,z5]),(0,[z35,z1,z21,z4,z10,z6]),(0,[z1,z122,z3,z4,z129,z6]),(0,[z1,z3,z4,z10,z6,z380]),(0,[z1,z841,z3,z4,z5,z6])],[(0,[z1,z2,z842,z4,z5,z6]),(0,[z78,z2,z16,z3,z6,z94]),(0,[z2,z67,z725,z4,z5,z6]),(0,[z843,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z424,z6,z119])],[(1,[z16,z3,z4,z10,z6]),(0,[z16,z67,z3,z4,z10,z6]),(0,[z28,z77,z3,z4,z5,z6]),(0,[z28,z2,z3,z4,z208,z6]),(0,[z33,z1,z2,z4,z501,z6]),(0,[z1,z2,z3,z81,z424,z17])],[],[(0,[z2,z16,z3,z4,z5,z168]),(0,[z2,z844,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z137,z6]),(0,[z1,z2,z4,z845,z5,z6]),(0,[z1,z21,z4,z205,z10,z6])],[(0,[z1,z2,z277,z4,z5,z6]),(0,[z35,z170,z2,z4,z5,z6]),(0,[z1,z2,z3,z297,z11,z6]),(0,[z846,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z426,z5,z6]),(0,[z368,z3,z4,z5,z6,z119]),(0,[z1,z2,z3,z424,z319,z6])],[(0,[z1,z2,z3,z4,z847,z6]),(0,[z1,z2,z3,z4,z848,z6]),(0,[z1,z21,z4,z212,z10,z6]),(0,[z1,z2,z21,z4,z801,z5]),(0,[z103,z55,z3,z4,z5,z6]),(0,[z849,z2,z3,z4,z5,z6])],[(0,[z1,z2,z850,z4,z5,z6]),(0,[z43,z1,z21,z4,z10,z6]),(0,[z1,z21,z336,z4,z10,z6]),(0,[z2,z21,z4,z5,z754,z6]),(0,[z1,z675,z21,z4,z5,z6]),(0,[z851,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z722,z10])],[(0,[z1,z2,z3,z4,z852,z6])],[(0,[z2,z16,z3,z4,z132,z6]),(0,[z28,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z281,z5,z6]),(0,[z853,z2,z3,z4,z5,z6]),(0,[z232,z2,z3,z4,z11,z6]),(0,[z854,z2,z3,z4,z5,z6]),(0,[z2,z855,z3,z4,z5,z6])],[(0,[z2,z16,z23,z4,z10,z6]),(0,[z1,z141,z21,z4,z5,z6]),(0,[z1,z2,z4,z11,z6,z856])]],
   [[(0,[z1,z2,z857,z4,z5,z6]),(0,[z159,z2,z139,z4,z5,z6]),(0,[z1,z425,z3,z4,z10,z6])],[(0,[z1,z3,z75,z4,z10,z6]),(0,[z1,z134,z3,z4,z848,z6]),(0,[z102,z1,z23,z4,z10,z6]),(0,[z1,z2,z4,z5,z858,z6])],[(0,[z16,z3,z4,z697,z5,z6]),(0,[z309,z2,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z859]),(0,[z184,z2,z3,z4,z371,z6]),(0,[z1,z2,z4,z5,z860,z6])],[(0,[z1,z2,z861,z4,z5,z6]),(0,[z1,z3,z90,z325,z5,z6]),(0,[z1,z2,z3,z426,z11,z6]),(0,[z1,z2,z3,z862,z5,z6]),(0,[z863,z2,z3,z4,z5,z6])],[(0,[z2,z16,z3,z4,z115,z6]),(0,[z237,z28,z2,z3,z10,z6]),(0,[z43,z216,z2,z4,z5,z6]),(0,[z1,z2,z864,z4,z5,z6])],[(0,[z865,z2,z3,z4,z5,z6]),(0,[z55,z16,z125,z4,z5,z6]),(0,[z120,z16,z3,z4,z10,z6]),(0,[z164,z28,z3,z4,z5,z6]),(0,[z1,z2,z866,z4,z5,z6]),(0,[z867,z2,z3,z4,z5,z6])],[(0,[z16,z3,z4,z5,z322,z6]),(0,[z183,z16,z3,z4,z10,z6]),(0,[z401,z16,z3,z4,z5,z6]),(0,[z1,z2,z139,z4,z10,z6]),(0,[z868,z2,z3,z4,z5,z6])],[(0,[z1,z122,z3,z4,z161,z6]),(0,[z1,z2,z869,z3,z5,z6]),(0,[z1,z2,z139,z4,z5,z241]),(0,[z100,z1,z3,z36,z5,z241]),(0,[z33,z1,z2,z4,z345,z6]),(0,[z1,z2,z3,z4,z870,z6]),(0,[z170,z2,z4,z5,z146,z6]),(0,[z1,z2,z81,z5,z466,z17])],[(0,[z55,z16,z21,z4,z5,z6]),(0,[z183,z122,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z871,z6]),(0,[z1,z301,z2,z4,z10,z6]),(0,[z164,z1,z872,z4,z5,z6])],[(0,[z35,z2,z626,z4,z5,z6]),(0,[z1,z873,z3,z4,z5,z6]),(0,[z1,z2,z3,z12,z298,z6])],[(0,[z1,z2,z21,z4,z200,z6]),(0,[z2,z16,z452,z4,z5,z6]),(0,[z1,z874,z3,z4,z5,z6]),(0,[z1,z682,z3,z4,z10,z6]),(0,[z1,z875,z2,z4,z5,z6])],[(0,[z2,z16,z3,z4,z10,z6]),(0,[z1,z2,z4,z283,z10,z6])],[(0,[z184,z19,z3,z4,z161,z6]),(0,[z1,z2,z507,z4,z10,z6]),(0,[z1,z2,z3,z4,z5,z876]),(0,[z1,z2,z3,z4,z877,z6])],[(0,[z1,z2,z3,z4,z878,z6]),(0,[z16,z3,z4,z10,z22,z6]),(0,[z28,z2,z3,z319,z5,z6]),(0,[z1,z2,z4,z879,z5,z6]),(0,[z1,z2,z21,z297,z5,z6]),(0,[z102,z1,z3,z4,z10,z6]),(0,[z1,z2,z880,z4,z5,z6])],[(0,[z686,z16,z3,z4,z5,z6]),(0,[z1,z21,z4,z161,z10,z6]),(0,[z1,z30,z2,z4,z10,z63]),(0,[z1,z2,z83,z4,z208,z6])],[(0,[z1,z600,z3,z4,z10,z6]),(0,[z2,z3,z4,z424,z6,z218])]],
   [[(0,[z16,z3,z4,z226,z10,z6]),(0,[z1,z2,z3,z4,z881,z6]),(0,[z368,z2,z3,z281,z5,z6]),(0,[z1,z399,z21,z4,z10,z6]),(0,[z1,z2,z3,z4,z882,z6]),(0,[z102,z1,z203,z4,z10,z6])],[(0,[z232,z2,z21,z4,z5,z6]),(0,[z78,z1,z2,z3,z115,z6]),(0,[z1,z2,z883,z4,z5,z6])],[(0,[z237,z16,z3,z4,z10,z6]),(0,[z2,z16,z3,z5,z884,z6]),(0,[z1,z2,z3,z4,z885,z6]),(0,[z1,z2,z886,z4,z5,z6]),(0,[z1,z21,z4,z5,z6,z292]),(0,[z1,z2,z23,z887,z5,z6]),(0,[z888,z2,z3,z4,z5,z6])],[(1,[z16,z21,z4,z10,z6]),(0,[z1,z2,z889,z4,z5,z6]),(0,[z1,z2,z890,z4,z5,z6])],[(0,[z538,z16,z3,z4,z5,z6]),(0,[z103,z2,z3,z4,z10,z6])],[(0,[z35,z2,z251,z4,z5,z6]),(0,[z0,z2,z3,z116,z5,z6]),(0,[z183,z2,z3,z4,z5,z449]),(0,[z1,z21,z4,z248,z10,z6]),(0,[z1,z3,z90,z5,z58,z17])],[(0,[z1,z2,z891,z4,z5,z6]),(0,[z846,z2,z21,z4,z5,z6]),(0,[z1,z2,z21,z426,z5,z6]),(0,[z2,z356,z3,z4,z10,z6])],[(0,[z28,z2,z499,z4,z5,z6]),(0,[z1,z2,z3,z254,z10,z6]),(0,[z410,z55,z3,z4,z5,z6]),(0,[z1,z103,z3,z4,z10,z6]),(0,[z1,z3,z4,z11,z577,z6])],[(0,[z1,z2,z277,z4,z514,z6]),(0,[z361,z2,z3,z4,z10,z6]),(0,[z1,z892,z2,z3,z10,z6]),(0,[z893,z2,z3,z4,z5,z6]),(0,[z1,z894,z3,z4,z5,z6]),(0,[z2,z895,z3,z4,z5,z6]),(0,[z1,z2,z896,z4,z5,z6])],[(0,[z180,z16,z3,z4,z10,z6]),(0,[z1,z2,z3,z781,z5,z6]),(0,[z35,z2,z478,z4,z5,z6]),(0,[z1,z2,z3,z4,z897,z6]),(0,[z1,z2,z139,z4,z101,z6]),(0,[z30,z2,z195,z4,z5,z6])],[(0,[z0,z2,z21,z281,z5,z6]),(0,[z1,z2,z898,z4,z5,z6]),(0,[z1,z2,z899,z4,z5,z6])],[(0,[z184,z2,z23,z4,z161,z6]),(0,[z401,z2,z3,z4,z10,z6]),(0,[z1,z2,z900,z4,z5,z6]),(0,[z2,z901,z3,z4,z5,z6])],[(0,[z1,z2,z902,z4,z5,z6]),(0,[z1,z2,z3,z319,z11,z6])],[(0,[z1,z2,z499,z4,z5,z6]),(0,[z1,z2,z903,z4,z5,z6])],[(0,[z2,z16,z3,z4,z101,z6]),(0,[z1,z2,z3,z4,z904,z6]),(0,[z1,z2,z3,z887,z5,z6]),(0,[z237,z1,z2,z3,z5,z6])],[(0,[z1,z217,z3,z4,z10,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z905]),(0,[z1,z110,z21,z4,z5,z6]),(0,[z1,z2,z23,z212,z10,z6]),(0,[z1,z2,z3,z906,z185,z6]),(0,[z1,z2,z4,z5,z6,z907])],[(0,[z28,z2,z4,z5,z908,z6]),(0,[z1,z2,z909,z4,z5,z6])],[],[(0,[z16,z3,z4,z290,z10,z6]),(0,[z1,z2,z910,z4,z5,z6])],[(0,[z1,z2,z3,z4,z911,z6]),(0,[z16,z3,z4,z10,z62,z6]),(0,[z2,z16,z3,z5,z212,z6]),(0,[z1,z2,z3,z4,z912,z6]),(0,[z913,z2,z3,z4,z5,z6])],[(0,[z26,z16,z3,z4,z11,z6]),(0,[z2,z16,z3,z4,z59,z6]),(0,[z1,z21,z4,z11,z10,z6]),(0,[z1,z39,z21,z4,z10,z6]),(0,[z1,z399,z2,z4,z5,z63]),(0,[z237,z1,z2,z3,z298,z6]),(0,[z1,z2,z3,z212,z115,z6]),(0,[z914,z2,z3,z4,z5,z6])],[(0,[z28,z2,z381,z4,z5,z6]),(0,[z28,z2,z3,z212,z10,z6]),(0,[z1,z2,z3,z4,z5,z915]),(0,[z1,z2,z23,z81,z5,z17]),(0,[z1,z2,z499,z4,z11,z6])],[(0,[z2,z16,z21,z4,z10,z6]),(0,[z28,z2,z916,z4,z5,z6]),(0,[z1,z2,z4,z5,z908,z6]),(0,[z184,z2,z3,z4,z161,z6]),(0,[z361,z2,z3,z4,z113,z6]),(0,[z179,z2,z69,z4,z5,z6]),(0,[z237,z1,z2,z3,z11,z6]),(0,[z1,z60,z2,z157,z10,z6]),(0,[z1,z70,z267,z4,z5,z6])],[(0,[z2,z917,z3,z4,z5,z6])],[(0,[z918,z2,z3,z4,z5,z6]),(0,[z102,z1,z21,z4,z10,z6])],[(0,[z1,z79,z3,z4,z10,z6]),(0,[z1,z511,z3,z4,z10,z6]),(0,[z919,z2,z3,z4,z5,z6]),(0,[z223,z2,z3,z4,z10,z6]),(0,[z920,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z733,z248])],[(0,[z28,z2,z535,z4,z5,z6]),(0,[z1,z2,z921,z4,z5,z6]),(0,[z922,z2,z3,z4,z5,z6])],[(0,[z458,z16,z3,z4,z10,z6]),(0,[z28,z2,z3,z81,z5,z17]),(0,[z1,z30,z2,z4,z5,z431]),(1,[z1,z21,z4,z130,z6]),(0,[z1,z2,z381,z4,z5,z6]),(0,[z1,z923,z2,z4,z5,z6]),(0,[z1,z2,z3,z212,z10,z6]),(0,[z1,z2,z70,z4,z146,z6]),(0,[z1,z2,z3,z4,z924,z6])],[(0,[z16,z3,z4,z5,z132,z6]),(0,[z1,z2,z916,z4,z5,z6]),(0,[z1,z2,z3,z4,z925,z6]),(0,[z183,z2,z3,z4,z10,z225]),(0,[z237,z1,z3,z11,z10,z6]),(0,[z2,z926,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z927,z6])],[(0,[z1,z23,z252,z4,z5,z6]),(0,[z1,z21,z4,z367,z10,z6]),(0,[z1,z2,z928,z4,z5,z6])],[(0,[z28,z16,z23,z4,z5,z6]),(0,[z2,z423,z29,z4,z5,z6]),(0,[z411,z2,z3,z4,z563,z6]),(0,[z1,z2,z3,z4,z929,z6])]],
   [[(0,[z16,z16,z3,z4,z10,z6]),(1,[z237,z16,z3,z10,z6]),(0,[z1,z2,z814,z4,z5,z6]),(0,[z1,z930,z3,z4,z5,z6]),(0,[z223,z2,z303,z4,z5,z6]),(0,[z410,z2,z3,z4,z10,z6]),(0,[z1,z2,z4,z10,z6,z466])],[(0,[z16,z3,z4,z5,z6,z119]),(0,[z16,z3,z4,z205,z10,z6]),(0,[z35,z2,z252,z4,z5,z6]),(0,[z1,z2,z535,z4,z5,z6]),(0,[z1,z2,z3,z4,z931,z6]),(0,[z2,z932,z3,z4,z5,z6])],[(0,[z933,z2,z3,z4,z5,z6]),(0,[z690,z2,z3,z4,z5,z476]),(0,[z1,z2,z3,z4,z5,z934]),(0,[z1,z2,z3,z81,z5,z17])],[(0,[z16,z3,z4,z212,z10,z6]),(0,[z1,z21,z4,z10,z6,z63]),(0,[z1,z572,z23,z4,z5,z6]),(0,[z1,z935,z3,z4,z5,z6]),(0,[z164,z710,z3,z4,z5,z6])],[(0,[z184,z2,z3,z4,z234,z6]),(0,[z1,z2,z936,z4,z5,z6]),(0,[z1,z2,z3,z10,z937,z6]),(0,[z938,z2,z3,z4,z5,z6])],[(0,[z102,z16,z3,z4,z10,z6]),(0,[z78,z1,z2,z23,z6,z94]),(0,[z1,z2,z381,z4,z11,z6]),(0,[z939,z2,z3,z4,z5,z6])],[(0,[z1,z393,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z940,z6]),(0,[z1,z2,z3,z941,z10,z6]),(0,[z1,z2,z916,z4,z11,z6])],[(0,[z28,z2,z277,z4,z5,z6]),(0,[z176,z2,z3,z4,z371,z6]),(0,[z140,z2,z96,z4,z5,z6])],[(0,[z1,z2,z23,z4,z5,z168]),(0,[z293,z2,z3,z4,z10,z6])],[(0,[z16,z235,z3,z4,z10,z6]),(0,[z16,z3,z4,z10,z6,z94]),(0,[z28,z572,z3,z4,z5,z6]),(0,[z1,z488,z23,z4,z5,z6]),(0,[z35,z1,z70,z4,z5,z6])],[(0,[z16,z3,z4,z5,z10,z6]),(0,[z70,z16,z3,z4,z5,z6]),(0,[z100,z28,z3,z36,z5,z6]),(0,[z1,z2,z3,z4,z5,z942]),(0,[z1,z2,z943,z4,z5,z6]),(0,[z944,z2,z3,z4,z5,z6]),(0,[z1,z2,z535,z4,z11,z6]),(0,[z945,z2,z3,z4,z5,z6]),(0,[z1,z550,z3,z4,z10,z6])],[(0,[z28,z16,z3,z4,z5,z6]),(0,[z946,z2,z3,z4,z5,z6]),(0,[z1,z19,z3,z4,z10,z6]),(0,[z1,z2,z947,z4,z5,z6]),(0,[z1,z3,z549,z4,z10,z6]),(0,[z1,z2,z3,z81,z11,z17])],[(0,[z948,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z949,z6])],[(0,[z1,z2,z23,z4,z132,z6]),(0,[z183,z1,z21,z4,z10,z6])],[(0,[z2,z16,z41,z4,z5,z6]),(0,[z28,z2,z3,z4,z5,z168]),(0,[z1,z2,z4,z950,z5,z6]),(0,[z100,z1,z189,z3,z5,z6]),(0,[z1,z2,z193,z3,z10,z6])],[(0,[z951,z1,z2,z4,z5,z6]),(0,[z1,z572,z3,z4,z5,z6]),(0,[z2,z952,z3,z4,z5,z6])]],
   [[(0,[z16,z23,z4,z5,z10,z6]),(0,[z43,z2,z29,z4,z5,z6]),(0,[z43,z1,z70,z4,z5,z6]),(0,[z1,z2,z3,z4,z953,z6]),(0,[z1,z2,z23,z49,z5,z6]),(0,[z1,z55,z203,z4,z5,z6])],[(0,[z810,z1,z2,z3,z10,z6])],[(0,[z703,z1,z3,z4,z10,z6]),(0,[z2,z23,z4,z5,z137,z6]),(0,[z1,z2,z3,z10,z954,z6]),(0,[z1,z2,z3,z4,z955,z6]),(0,[z956,z2,z3,z4,z5,z6])],[(0,[z28,z2,z3,z4,z132,z6]),(0,[z1,z2,z4,z5,z6,z957]),(0,[z184,z2,z21,z4,z161,z6]),(0,[z1,z21,z4,z5,z130,z6]),(0,[z1,z2,z23,z4,z115,z6]),(0,[z2,z958,z3,z4,z5,z6]),(0,[z33,z170,z2,z4,z146,z6]),(0,[z2,z959,z3,z4,z5,z6])],[(0,[z28,z16,z3,z4,z11,z6]),(0,[z2,z16,z3,z49,z5,z6]),(0,[z20,z2,z16,z4,z5,z6]),(0,[z28,z2,z23,z4,z10,z6]),(0,[z43,z170,z2,z4,z5,z6]),(0,[z1,z960,z3,z4,z5,z6]),(0,[z159,z2,z23,z4,z5,z6]),(0,[z2,z207,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z168])],[(0,[z184,z2,z150,z4,z161,z6]),(0,[z1,z3,z4,z5,z6,z961]),(0,[z1,z2,z962,z4,z5,z6])],[(0,[z16,z3,z4,z10,z6,z365]),(0,[z1,z2,z277,z4,z11,z6]),(0,[z122,z3,z4,z5,z161,z6])],[(0,[z1,z2,z963,z4,z5,z6]),(0,[z184,z1,z21,z4,z10,z6]),(0,[z1,z2,z964,z4,z5,z6]),(0,[z179,z2,z3,z4,z360,z6]),(0,[z1,z965,z3,z4,z5,z6]),(0,[z2,z3,z4,z248,z258,z40])],[(0,[z1,z2,z3,z4,z966,z6]),(0,[z394,z1,z3,z4,z10,z6]),(0,[z1,z2,z145,z4,z10,z6]),(0,[z1,z2,z21,z212,z10,z6]),(0,[z967,z2,z3,z4,z5,z6]),(0,[z1,z2,z968,z4,z5,z6]),(0,[z237,z1,z2,z3,z373,z6]),(0,[z1,z2,z969,z3,z5,z6])],[(0,[z1,z2,z3,z4,z132,z6]),(0,[z2,z16,z3,z325,z5,z6]),(0,[z28,z2,z3,z4,z115,z6]),(0,[z43,z2,z29,z4,z11,z6]),(0,[z2,z3,z725,z4,z5,z6]),(0,[z1,z2,z3,z970,z5,z6]),(0,[z1,z2,z971,z4,z5,z6]),(0,[z1,z2,z3,z4,z972,z6]),(0,[z237,z1,z21,z4,z10,z6]),(0,[z1,z3,z4,z848,z10,z6]),(0,[z621,z2,z23,z4,z5,z6])],[(0,[z26,z16,z3,z4,z200,z6]),(0,[z1,z2,z277,z4,z52,z6]),(0,[z0,z2,z3,z281,z11,z6]),(0,[z1,z2,z23,z4,z10,z6]),(0,[z1,z2,z3,z5,z906,z6])],[(0,[z1,z2,z973,z4,z5,z6]),(0,[z2,z3,z4,z5,z720,z225]),(0,[z1,z21,z4,z10,z6,z40]),(0,[z1,z2,z3,z4,z298,z168])],[(0,[z2,z303,z4,z5,z22,z6]),(0,[z1,z3,z4,z512,z10,z6]),(0,[z237,z1,z3,z21,z10,z6]),(0,[z974,z2,z3,z4,z5,z6]),(0,[z975,z2,z3,z4,z5,z6]),(0,[z2,z976,z3,z4,z5,z6])],[(0,[z189,z16,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z168])],[(0,[z1,z2,z21,z81,z5,z17]),(0,[z2,z977,z3,z4,z5,z6])],[(0,[z2,z16,z3,z4,z5,z241]),(0,[z28,z2,z452,z4,z5,z6]),(0,[z1,z2,z3,z4,z978,z6]),(0,[z1,z2,z3,z4,z115,z6])]],
   [[(0,[z28,z2,z3,z4,z10,z6]),(0,[z159,z2,z3,z4,z5,z6]),(0,[z2,z207,z3,z4,z5,z6]),(0,[z1,z2,z3,z979,z5,z6])],[(0,[z2,z3,z18,z297,z5,z6]),(0,[z1,z533,z23,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z980]),(0,[z1,z2,z3,z5,z6,z981])],[(0,[z232,z2,z499,z4,z5,z6])],[(0,[z184,z16,z3,z4,z10,z6]),(0,[z1,z2,z982,z4,z5,z6]),(0,[z1,z2,z3,z983,z5,z6]),(0,[z1,z21,z4,z10,z58,z6]),(0,[z595,z2,z23,z4,z5,z6])],[(0,[z2,z16,z303,z4,z5,z6]),(0,[z238,z2,z3,z4,z5,z225]),(0,[z2,z3,z4,z774,z161,z6]),(0,[z2,z195,z3,z4,z10,z6])],[(0,[z572,z16,z3,z4,z5,z6]),(0,[z621,z2,z3,z4,z5,z6]),(0,[z1,z2,z984,z4,z5,z6]),(0,[z1,z2,z452,z4,z5,z6]),(0,[z985,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z986])],[(0,[z1,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z987,z5,z6])],[(0,[z1,z2,z988,z4,z5,z6]),(0,[z28,z16,z21,z4,z5,z6]),(0,[z237,z2,z16,z3,z5,z6]),(0,[z1,z2,z989,z4,z5,z6]),(0,[z2,z990,z3,z4,z5,z6])],[(0,[z1,z143,z3,z4,z10,z6]),(0,[z1,z2,z3,z991,z5,z6]),(0,[z2,z29,z4,z5,z339,z6])],[(0,[z361,z2,z3,z4,z130,z6]),(0,[z1,z55,z21,z4,z5,z6]),(0,[z2,z23,z195,z4,z5,z6]),(0,[z1,z2,z203,z4,z10,z6]),(0,[z102,z1,z3,z4,z812,z6]),(0,[z2,z207,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z248,z434]),(0,[z164,z3,z4,z5,z6,z218]),(0,[z992,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z993,z6]),(0,[z1,z2,z994,z4,z5,z6]),(0,[z1,z2,z3,z4,z995,z6])],[(0,[z16,z3,z95,z4,z10,z6]),(0,[z1,z2,z3,z4,z996,z6]),(0,[z1,z572,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z997,z6]),(0,[z2,z998,z3,z4,z5,z6])],[(0,[z176,z2,z3,z4,z161,z6]),(0,[z1,z21,z4,z546,z10,z6]),(0,[z78,z1,z2,z3,z5,z241]),(0,[z103,z3,z4,z5,z10,z6]),(0,[z2,z3,z999,z4,z5,z6])],[(0,[z2,z16,z3,z4,z113,z6]),(0,[z1,z2,z3,z5,z884,z6]),(0,[z1,z2,z23,z4,z101,z6])],[(0,[z1000,z2,z3,z4,z5,z6]),(0,[z20,z1,z2,z4,z10,z6]),(0,[z1,z539,z21,z4,z5,z6]),(0,[z1001,z2,z3,z4,z5,z6]),(0,[z1,z2,z452,z4,z11,z6]),(0,[z223,z2,z4,z91,z5,z6])],[(0,[z595,z2,z3,z4,z5,z6]),(0,[z9,z16,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1002]),(0,[z1,z21,z4,z469,z10,z6]),(0,[z1,z2,z3,z4,z812,z6]),(0,[z2,z3,z4,z11,z137,z6]),(0,[z1003,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z1004,z4,z5,z6]),(0,[z1,z2,z21,z4,z5,z168]),(0,[z1,z2,z69,z4,z360,z6])],[(0,[z0,z1,z21,z4,z10,z6]),(0,[z401,z55,z21,z4,z5,z6]),(0,[z1,z2,z1005,z4,z5,z6]),(0,[z1,z830,z2,z4,z10,z6]),(0,[z1,z2,z37,z4,z10,z6]),(0,[z237,z1,z2,z3,z12,z6]),(0,[z1,z2,z3,z4,z1006,z6]),(0,[z1,z2,z4,z5,z6,z1007])],[(0,[z204,z2,z3,z4,z161,z6]),(0,[z1,z2,z1008,z4,z5,z6]),(0,[z1,z2,z3,z1009,z5,z6])],[(0,[z28,z2,z3,z4,z101,z6]),(0,[z1,z2,z3,z133,z5,z17]),(0,[z1,z2,z23,z5,z212,z6]),(0,[z1,z2,z193,z23,z5,z6])],[(0,[z967,z2,z21,z4,z5,z6]),(0,[z411,z2,z23,z4,z5,z6]),(0,[z1,z2,z23,z4,z59,z6])],[(0,[z1,z2,z21,z4,z132,z6]),(0,[z35,z2,z67,z4,z10,z6]),(0,[z1,z70,z3,z4,z10,z6])],[(0,[z16,z3,z21,z4,z10,z6]),(0,[z2,z1010,z3,z4,z5,z6])],[(0,[z16,z3,z4,z157,z10,z6]),(0,[z28,z573,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1011,z6]),(0,[z1,z21,z4,z12,z10,z6]),(0,[z1,z2,z4,z11,z858,z6])],[(0,[z1,z2,z3,z1012,z5,z6]),(0,[z1,z2,z21,z49,z5,z6]),(0,[z1,z644,z3,z4,z10,z6]),(0,[z595,z2,z3,z4,z11,z6]),(0,[z1013,z2,z3,z4,z5,z6])],[(0,[z16,z3,z169,z4,z10,z6]),(0,[z28,z2,z3,z5,z212,z6]),(0,[z1,z2,z3,z4,z101,z6]),(0,[z1,z3,z647,z4,z10,z6]),(0,[z1,z2,z4,z10,z6,z51]),(0,[z2,z207,z125,z4,z5,z6]),(0,[z826,z2,z3,z4,z5,z6])],[(0,[z28,z2,z3,z4,z59,z6]),(0,[z2,z3,z4,z5,z6,z258]),(0,[z2,z977,z21,z4,z5,z6]),(0,[z1014,z2,z3,z4,z5,z6]),(0,[z2,z1015,z3,z4,z5,z6])],[(0,[z1,z2,z21,z4,z115,z6]),(0,[z1,z2,z3,z81,z1009,z5])],[(0,[z30,z16,z3,z4,z10,z6]),(0,[z28,z2,z21,z4,z10,z6]),(0,[z1,z2,z3,z4,z5,z1016]),(0,[z159,z2,z21,z4,z5,z6]),(0,[z2,z207,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z367,z40]),(0,[z1,z2,z3,z405,z5,z17])],[(0,[z16,z54,z3,z4,z10,z6]),(0,[z0,z16,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z5,z1017]),(0,[z78,z1,z2,z3,z706,z6]),(0,[z3,z4,z5,z6,z1018,z119])],[(0,[z1,z267,z21,z4,z5,z6]),(0,[z1,z2,z4,z424,z6,z466])],[(0,[z1,z1019,z3,z4,z5,z6]),(0,[z1,z2,z1020,z4,z5,z6]),(0,[z1,z2,z3,z5,z212,z6]),(0,[z204,z2,z3,z4,z234,z6]),(0,[z1,z2,z125,z4,z10,z6])]],
   [[(0,[z411,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1021,z6]),(0,[z1,z2,z3,z4,z59,z6]),(0,[z595,z2,z83,z4,z5,z6])],[(0,[z621,z2,z21,z4,z5,z6]),(0,[z118,z2,z23,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1022])],[(0,[z1,z122,z1023,z4,z5,z6]),(0,[z1,z2,z21,z4,z10,z6]),(0,[z1,z419,z3,z4,z10,z6]),(0,[z368,z2,z4,z5,z6,z466])],[(0,[z2,z3,z4,z5,z6,z1018]),(0,[z1,z2,z3,z1024,z5,z6]),(0,[z1,z2,z1025,z4,z5,z6]),(0,[z1,z508,z21,z4,z10,z6])],[(0,[z1,z583,z21,z4,z5,z6]),(0,[z1,z2,z150,z4,z10,z6]),(0,[z1,z892,z2,z21,z5,z6]),(0,[z1,z2,z3,z4,z6,z981])],[(0,[z107,z16,z3,z4,z5,z6]),(0,[z1,z134,z3,z212,z10,z6]),(0,[z2,z1026,z23,z4,z5,z6]),(0,[z748,z2,z3,z4,z10,z6])],[(0,[z2,z16,z4,z5,z283,z6])],[(0,[z28,z23,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z1027,z6]),(0,[z1,z67,z21,z4,z10,z6]),(0,[z2,z3,z4,z5,z6,z1028]),(0,[z1029,z2,z3,z4,z5,z6]),(0,[z2,z1030,z3,z4,z5,z6])],[(0,[z2,z3,z4,z129,z694,z6]),(0,[z0,z2,z3,z836,z5,z6]),(0,[z410,z3,z4,z5,z10,z6]),(0,[z410,z2,z3,z4,z163,z6]),(0,[z3,z4,z5,z6,z218,z119]),(0,[z1,z2,z1031,z4,z5,z6])],[(0,[z1,z2,z1032,z4,z5,z6]),(0,[z2,z85,z96,z4,z5,z6]),(0,[z78,z1,z2,z3,z6,z981]),(0,[z1,z2,z3,z4,z1033,z6])],[(0,[z620,z16,z3,z4,z5,z6]),(0,[z1,z2,z725,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z720]),(0,[z1034,z2,z3,z4,z5,z6])],[(0,[z595,z2,z21,z4,z5,z6]),(0,[z1,z2,z535,z4,z298,z6])],[(0,[z1035,z1,z2,z4,z5,z6]),(0,[z1036,z2,z3,z4,z5,z6]),(0,[z1,z1037,z3,z4,z5,z6])],[(0,[z100,z16,z21,z4,z5,z6]),(0,[z118,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1038,z6]),(0,[z1,z23,z21,z4,z5,z6]),(0,[z2,z356,z69,z4,z5,z6])],[(0,[z384,z2,z454,z4,z5,z6]),(0,[z1039,z2,z23,z4,z5,z6])],[(0,[z628,z2,z67,z4,z5,z6]),(0,[z1,z2,z3,z325,z5,z58])]],
   [[(0,[z1,z2,z3,z188,z10,z6]),(0,[z1040,z2,z3,z4,z5,z6])],[(0,[z1,z70,z21,z4,z10,z6]),(0,[z2,z1026,z3,z4,z5,z6]),(0,[z1,z2,z1041,z4,z5,z6]),(0,[z1,z2,z83,z4,z59,z6])],[(0,[z28,z488,z3,z4,z5,z6]),(0,[z204,z1,z21,z4,z10,z6]),(0,[z33,z1,z70,z4,z146,z6])],[(0,[z1,z2,z1042,z4,z5,z6]),(0,[z1,z21,z4,z547,z5,z6])],[(0,[z16,z267,z3,z4,z10,z6]),(0,[z1,z19,z303,z4,z5,z6])],[(0,[z343,z2,z16,z4,z5,z6]),(0,[z2,z16,z75,z4,z5,z6]),(0,[z271,z2,z67,z4,z5,z6]),(0,[z1,z2,z21,z4,z101,z6]),(0,[z33,z1,z21,z4,z10,z6]),(0,[z1,z2,z3,z230,z5,z17])],[(0,[z1,z23,z21,z4,z11,z6]),(0,[z100,z159,z3,z36,z5,z6]),(0,[z118,z2,z3,z4,z11,z6]),(0,[z1043,z2,z3,z4,z5,z6])],[(0,[z1,z30,z2,z4,z5,z167]),(0,[z1,z2,z3,z553,z5,z17])],[(0,[z1,z2,z3,z4,z1044,z6]),(0,[z1,z2,z23,z325,z5,z6]),(0,[z1,z2,z3,z835,z10,z6]),(0,[z164,z1,z4,z5,z6,z466])],[(0,[z1,z2,z41,z4,z5,z6]),(0,[z16,z3,z4,z161,z10,z6]),(0,[z28,z2,z3,z49,z5,z6]),(0,[z1,z2,z3,z4,z1045,z6]),(0,[z1,z573,z21,z4,z5,z6]),(0,[z1,z2,z3,z49,z208,z6])],[(0,[z1,z2,z3,z4,z5,z1046]),(0,[z1,z2,z3,z4,z1047,z6]),(0,[z1039,z2,z3,z4,z5,z6])],[(0,[z1,z2,z23,z4,z130,z6]),(0,[z1,z2,z21,z5,z212,z6]),(0,[z232,z2,z3,z4,z10,z6]),(0,[z2,z3,z4,z5,z6,z1048])],[(0,[z1,z2,z21,z4,z59,z6]),(0,[z411,z2,z21,z4,z5,z6]),(0,[z1,z23,z525,z4,z5,z6]),(0,[z1,z2,z1049,z4,z5,z6])],[],[(0,[z204,z16,z3,z4,z10,z6]),(0,[z28,z2,z3,z325,z5,z6]),(0,[z183,z2,z3,z4,z5,z687]),(0,[z1,z2,z23,z4,z5,z241]),(0,[z151,z2,z139,z4,z5,z6]),(0,[z164,z1,z3,z4,z1050,z6])],[(0,[z2,z16,z3,z4,z130,z6]),(0,[z1,z2,z1051,z4,z5,z6]),(0,[z1,z21,z4,z5,z577,z6]),(0,[z1,z2,z3,z49,z5,z6]),(0,[z1052,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z813])]],
   [[(0,[z16,z3,z4,z248,z10,z6]),(0,[z28,z2,z982,z4,z5,z6]),(0,[z654,z2,z67,z4,z5,z6]),(0,[z1,z1053,z3,z4,z5,z6]),(0,[z1,z21,z4,z5,z6,z580]),(0,[z1,z70,z42,z4,z5,z6])],[(0,[z33,z16,z3,z4,z10,z6]),(0,[z2,z16,z96,z4,z5,z6]),(0,[z1,z2,z1054,z4,z5,z6]),(0,[z1,z2,z3,z4,z1055,z6])],[(0,[z122,z67,z3,z4,z5,z6]),(0,[z1,z1056,z3,z4,z5,z6]),(0,[z1,z544,z2,z157,z5,z6]),(0,[z1,z2,z452,z4,z208,z6])],[(0,[z16,z23,z3,z4,z10,z6]),(0,[z1,z77,z3,z4,z10,z6]),(0,[z1,z134,z23,z4,z10,z6])],[(0,[z28,z2,z3,z4,z5,z241]),(0,[z1,z2,z3,z4,z1057,z6]),(0,[z1,z21,z81,z4,z10,z6]),(0,[z1,z2,z3,z325,z5,z6]),(0,[z368,z301,z2,z4,z5,z6])],[(0,[z46,z16,z3,z4,z5,z24]),(0,[z170,z2,z23,z4,z5,z6]),(0,[z237,z1,z2,z3,z248,z6]),(0,[z1,z301,z4,z5,z6,z119])],[(0,[z2,z16,z3,z4,z163,z6]),(0,[z2,z1058,z3,z4,z5,z6]),(0,[z28,z55,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z451,z434]),(0,[z368,z2,z3,z4,z363,z6])],[(0,[z1,z2,z3,z4,z1059,z6]),(0,[z1,z2,z3,z4,z130,z6]),(0,[z1,z2,z3,z1060,z5,z6]),(0,[z1,z3,z4,z98,z10,z6]),(0,[z78,z1,z2,z3,z212,z6]),(0,[z1,z2,z3,z4,z1061,z6])],[(0,[z1,z645,z21,z4,z5,z6]),(0,[z1,z2,z3,z49,z11,z6]),(0,[z1052,z2,z3,z4,z11,z6])],[(0,[z28,z134,z3,z4,z10,z6]),(0,[z28,z2,z303,z4,z5,z6]),(0,[z1,z2,z3,z4,z1062,z6]),(0,[z118,z2,z21,z4,z5,z6])],[(0,[z1,z75,z4,z5,z10,z6]),(0,[z1,z110,z3,z4,z10,z6]),(0,[z1,z2,z193,z21,z5,z6]),(0,[z159,z2,z3,z4,z298,z6]),(0,[z1,z2,z3,z4,z5,z241]),(0,[z1,z2,z3,z4,z1063,z6]),(0,[z1064,z1,z3,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z1065]),(0,[z46,z1,z3,z4,z5,z876])],[(0,[z1,z2,z23,z4,z113,z6]),(0,[z1,z123,z21,z4,z10,z6]),(0,[z1,z60,z21,z4,z10,z6]),(0,[z159,z2,z3,z4,z11,z6]),(0,[z595,z2,z3,z4,z208,z6]),(0,[z2,z762,z3,z4,z5,z6])],[(0,[z1,z2,z1066,z4,z5,z6]),(0,[z2,z356,z3,z4,z360,z6]),(0,[z1,z2,z3,z325,z11,z6])],[(0,[z1,z2,z1067,z4,z5,z6]),(0,[z183,z2,z145,z4,z5,z6]),(0,[z33,z1,z2,z4,z1068,z6]),(0,[z1,z2,z4,z5,z1069,z6])],[(0,[z2,z1070,z3,z4,z5,z6]),(0,[z1,z2,z303,z4,z5,z6]),(0,[z1,z134,z3,z4,z10,z6]),(0,[z1,z21,z4,z10,z10,z6])]],
   [[(0,[z1,z2,z3,z4,z1071,z6]),(0,[z1,z2,z1072,z4,z5,z6]),(0,[z16,z3,z4,z11,z10,z6]),(0,[z558,z2,z73,z4,z5,z6]),(0,[z1,z3,z21,z212,z10,z6]),(0,[z1,z203,z4,z5,z10,z6]),(0,[z1,z2,z83,z49,z5,z6])],[(0,[z2,z3,z4,z5,z6,z1073]),(0,[z170,z2,z3,z4,z5,z6]),(0,[z122,z3,z4,z5,z22,z6]),(0,[z1,z2,z3,z4,z298,z241]),(0,[z621,z2,z3,z4,z11,z6])],[(0,[z28,z2,z3,z4,z113,z6]),(0,[z1,z2,z3,z4,z1074,z6])],[(0,[z2,z3,z4,z1075,z5,z6]),(0,[z1,z21,z18,z4,z10,z6]),(0,[z1,z2,z3,z4,z11,z241]),(0,[z1076,z2,z3,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z1077]),(0,[z46,z1,z23,z4,z5,z24])],[(0,[z26,z16,z3,z4,z132,z6]),(0,[z28,z2,z3,z1012,z5,z6]),(0,[z628,z1,z21,z4,z10,z6]),(0,[z33,z1,z2,z4,z211,z6]),(0,[z2,z3,z4,z5,z6,z1078]),(0,[z1,z2,z83,z325,z5,z6]),(0,[z1,z2,z1079,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1080,z6])],[(0,[z368,z2,z3,z4,z424,z6])],[(0,[z1,z2,z3,z1081,z5,z6]),(0,[z1,z2,z3,z4,z1082,z6]),(0,[z1,z2,z303,z4,z11,z6]),(0,[z1,z2,z3,z4,z113,z6]),(0,[z237,z1,z134,z3,z10,z6]),(0,[z1,z2,z3,z1083,z5,z6]),(0,[z1,z70,z3,z4,z512,z6])],[(0,[z16,z3,z4,z367,z10,z6]),(0,[z1,z2,z1084,z4,z5,z6]),(0,[z529,z1,z3,z4,z10,z6]),(0,[z1,z2,z3,z319,z10,z6]),(0,[z1,z1085,z4,z5,z6,z119])],[(0,[z112,z16,z21,z4,z5,z6]),(0,[z1,z2,z1086,z4,z5,z6]),(0,[z1,z2,z83,z4,z10,z6]),(0,[z170,z2,z3,z4,z11,z6])],[(0,[z1,z2,z75,z4,z514,z6]),(0,[z1,z410,z3,z4,z10,z6])],[(0,[z135,z16,z3,z4,z10,z6]),(0,[z2,z1087,z3,z4,z5,z6]),(0,[z164,z1,z3,z4,z363,z6]),(0,[z1,z4,z5,z6,z1088,z119])],[(0,[z1,z16,z3,z212,z10,z6]),(0,[z1,z2,z3,z4,z1089,z6]),(0,[z1,z21,z4,z5,z638,z6]),(0,[z1,z2,z3,z4,z1090,z6]),(0,[z102,z1,z499,z4,z10,z6]),(0,[z2,z1091,z3,z4,z5,z6]),(0,[z1,z2,z3,z1092,z5,z6])],[(0,[z16,z3,z4,z10,z6,z63]),(0,[z112,z361,z21,z4,z5,z6]),(0,[z1,z1093,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1094,z6]),(0,[z1,z112,z785,z4,z5,z6]),(0,[z78,z1,z2,z21,z6,z94])]],
   [[(0,[z1,z2,z1095,z4,z5,z6]),(0,[z316,z16,z3,z4,z5,z6]),(0,[z1,z2,z1096,z4,z5,z6]),(0,[z1,z2,z21,z325,z5,z6]),(0,[z270,z2,z23,z4,z5,z6]),(0,[z46,z1,z3,z4,z5,z24]),(0,[z170,z70,z3,z4,z5,z6]),(0,[z1,z2,z1097,z4,z5,z6])],[(0,[z72,z16,z3,z4,z5,z6]),(0,[z1,z3,z203,z4,z10,z6]),(0,[z1,z2,z1098,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1099,z6]),(0,[z26,z16,z3,z4,z10,z6]),(0,[z1,z2,z3,z1100,z5,z6]),(0,[z1,z3,z4,z697,z11,z6]),(0,[z1,z2,z1101,z3,z5,z6])],[(0,[z1,z1102,z3,z4,z5,z6]),(0,[z1,z2,z21,z4,z130,z6]),(0,[z2,z23,z4,z5,z6,z258])],[(0,[z1,z21,z73,z4,z10,z6]),(0,[z237,z1,z2,z3,z10,z6])],[(0,[z2,z16,z69,z4,z5,z6]),(0,[z28,z112,z21,z4,z5,z6]),(0,[z1,z2,z3,z1103,z5,z6]),(0,[z1,z2,z535,z4,z5,z168])],[(0,[z1,z120,z75,z4,z10,z6]),(0,[z20,z184,z2,z4,z161,z6]),(0,[z1,z2,z21,z4,z5,z241])],[(0,[z1,z335,z21,z4,z5,z6]),(0,[z1104,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1105]),(0,[z1,z2,z3,z1106,z5,z6]),(0,[z170,z2,z4,z5,z62,z6]),(0,[z2,z3,z81,z5,z218,z17])],[(0,[z1107,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z1108,z5,z6]),(0,[z1,z2,z3,z4,z1009,z5])],[(0,[z1,z2,z3,z4,z1109,z6]),(0,[z1,z1110,z3,z4,z5,z6]),(0,[z1,z2,z1111,z4,z5,z6]),(0,[z46,z1,z3,z4,z11,z24]),(0,[z293,z343,z2,z4,z5,z6])],[(0,[z1112,z2,z3,z4,z5,z6]),(0,[z118,z2,z3,z4,z208,z6]),(0,[z1113,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1114,z5,z6])],[(0,[z28,z2,z4,z5,z283,z6]),(0,[z7,z2,z23,z4,z5,z6]),(0,[z1,z112,z21,z4,z5,z6]),(0,[z1,z134,z21,z4,z10,z6]),(0,[z1115,z2,z3,z4,z5,z6]),(0,[z1,z2,z381,z4,z115,z6]),(0,[z1116,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1117,z6]),(0,[z223,z2,z67,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1118]),(0,[z411,z2,z3,z4,z11,z6]),(0,[z1,z2,z1119,z4,z5,z6])],[(0,[z43,z2,z158,z4,z5,z6]),(0,[z1,z21,z4,z128,z10,z6]),(0,[z170,z2,z21,z4,z5,z6]),(0,[z1,z483,z21,z4,z5,z6]),(0,[z164,z1,z3,z4,z424,z6])],[(0,[z1,z2,z1120,z4,z5,z6]),(0,[z1,z2,z3,z4,z1121,z6]),(0,[z1,z3,z252,z4,z10,z6])],[(0,[z1122,z2,z3,z4,z5,z6])]],
   [[(0,[z1123,z2,z3,z4,z5,z6]),(0,[z1124,z2,z3,z4,z5,z6])],[(0,[z1,z2,z4,z5,z283,z6]),(0,[z46,z1,z83,z4,z5,z24]),(0,[z1125,z2,z3,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z1126]),(0,[z1,z2,z381,z4,z10,z6])],[],[(0,[z16,z92,z3,z4,z10,z6]),(0,[z799,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z836,z5,z6]),(0,[z1,z2,z21,z4,z113,z6]),(0,[z1,z112,z21,z4,z11,z6]),(0,[z1,z72,z21,z4,z5,z6]),(0,[z1,z2,z23,z1127,z5,z6])],[(0,[z55,z16,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z5,z1128]),(0,[z1,z2,z3,z4,z1129,z6])],[(0,[z28,z2,z41,z4,z5,z6]),(0,[z16,z3,z4,z10,z6,z40]),(0,[z1,z2,z3,z4,z1130,z6]),(0,[z2,z3,z1131,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6]),(0,[z1,z3,z11,z212,z10,z6]),(0,[z1132,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z81,z10,z17]),(0,[z46,z118,z3,z4,z5,z24]),(0,[z1133,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z6,z981,z94])],[(0,[z2,z16,z321,z4,z5,z6])],[(0,[z1,z16,z3,z4,z132,z6]),(0,[z46,z16,z3,z4,z10,z6]),(0,[z1,z3,z4,z290,z10,z6]),(0,[z78,z28,z2,z3,z6,z94]),(0,[z28,z2,z75,z4,z5,z6]),(0,[z1,z2,z3,z297,z10,z6]),(0,[z1,z2,z1134,z4,z5,z6]),(0,[z1,z3,z21,z4,z10,z6]),(0,[z1,z458,z21,z4,z5,z6]),(0,[z1135,z2,z3,z4,z5,z6])],[(0,[z1,z16,z23,z4,z10,z6]),(0,[z1,z144,z3,z4,z10,z6]),(0,[z270,z70,z3,z4,z5,z6])],[(0,[z1,z1136,z3,z4,z5,z6]),(0,[z46,z1,z21,z4,z5,z24]),(0,[z140,z2,z23,z4,z5,z6]),(0,[z1,z1137,z2,z4,z5,z6]),(0,[z2,z3,z1138,z4,z5,z6])],[(0,[z1,z122,z23,z4,z5,z6]),(0,[z1,z2,z1139,z4,z5,z6]),(0,[z1,z1140,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z1141,z6]),(0,[z1,z2,z3,z4,z1142,z6])],[(0,[z16,z3,z4,z10,z58,z6]),(0,[z184,z2,z3,z4,z665,z6]),(0,[z301,z2,z4,z5,z6,z218])],[(0,[z1143,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z75,z4,z5,z6]),(0,[z1,z2,z3,z4,z1144,z6]),(0,[z7,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z1127,z5,z6]),(0,[z2,z3,z4,z11,z6,z258]),(0,[z1,z60,z2,z1145,z5,z6]),(0,[z2,z3,z4,z5,z6,z1146]),(0,[z1,z2,z872,z4,z5,z6])],[(0,[z28,z16,z3,z4,z10,z6]),(0,[z1,z2,z3,z90,z5,z241]),(0,[z118,z2,z83,z4,z5,z6]),(0,[z1,z2,z3,z325,z208,z6]),(0,[z1,z2,z4,z5,z62,z342]),(0,[z78,z1,z2,z3,z6,z376])],[(0,[z28,z3,z4,z5,z6,z119]),(1,[z237,z1,z21,z10,z6]),(0,[z151,z2,z23,z4,z5,z6])],[(0,[z28,z122,z3,z4,z5,z6]),(0,[z1,z2,z277,z4,z10,z6]),(0,[z1,z2,z3,z426,z10,z6]),(0,[z1,z2,z1147,z3,z5,z6])],[(0,[z28,z2,z3,z4,z130,z6]),(0,[z2,z3,z4,z5,z6,z1148])],[(0,[z1,z2,z41,z4,z11,z6]),(0,[z2,z16,z3,z4,z360,z6]),(0,[z20,z28,z2,z4,z5,z6]),(0,[z1,z2,z23,z4,z163,z6]),(0,[z1,z2,z3,z11,z212,z6])],[(0,[z1,z21,z4,z36,z10,z6]),(0,[z368,z2,z23,z4,z5,z6]),(0,[z1039,z2,z3,z4,z11,z6]),(0,[z1149,z2,z3,z4,z5,z6])],[(0,[z16,z3,z4,z10,z10,z6]),(0,[z1,z16,z3,z4,z10,z6]),(0,[z0,z2,z3,z281,z10,z6]),(0,[z854,z2,z3,z4,z10,z6])],[(0,[z140,z2,z3,z4,z5,z6]),(0,[z270,z2,z21,z4,z5,z6]),(0,[z1150,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z119])],[(0,[z530,z16,z3,z4,z5,z6]),(0,[z1,z122,z3,z4,z5,z6]),(0,[z1,z2,z75,z4,z11,z6]),(0,[z237,z1,z2,z23,z5,z6]),(0,[z2,z3,z4,z10,z137,z6]),(0,[z401,z2,z321,z4,z5,z6]),(0,[z1,z2,z3,z1151,z5,z6])],[(0,[z16,z3,z4,z469,z10,z6]),(0,[z1,z1152,z3,z4,z5,z6]),(0,[z1,z1153,z2,z4,z5,z6]),(0,[z1,z2,z535,z4,z101,z6]),(0,[z1,z2,z3,z4,z10,z168]),(0,[z1,z30,z2,z4,z5,z813]),(0,[z1,z4,z5,z6,z466,z119])],[(0,[z1154,z2,z3,z4,z5,z6]),(0,[z16,z3,z18,z4,z10,z6]),(0,[z28,z2,z3,z4,z163,z6]),(0,[z1,z2,z3,z4,z1155,z6]),(0,[z179,z2,z23,z4,z5,z6]),(0,[z1156,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z363,z6,z119])],[(0,[z1,z2,z96,z4,z5,z6]),(0,[z1,z84,z21,z4,z10,z6]),(0,[z1,z21,z4,z91,z10,z6]),(0,[z1,z2,z3,z12,z5,z241]),(0,[z1,z2,z1157,z4,z5,z6]),(0,[z1,z2,z1147,z3,z11,z6]),(0,[z1,z2,z3,z4,z1158,z6])],[(0,[z164,z16,z3,z4,z5,z6]),(0,[z1,z2,z75,z4,z52,z6]),(0,[z100,z1,z139,z36,z5,z6]),(0,[z1159,z2,z3,z4,z5,z6])],[(0,[z151,z2,z3,z4,z5,z6]),(0,[z1160,z2,z3,z4,z5,z6]),(0,[z1,z1161,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z1068,z6])],[(1,[z1,z75,z4,z10,z6]),(0,[z35,z2,z508,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1162]),(0,[z1163,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z1164,z3,z4,z5,z6]),(0,[z1,z2,z1165,z4,z5,z6]),(0,[z1166,z1,z3,z4,z5,z6]),(0,[z1,z134,z3,z4,z130,z6]),(0,[z2,z3,z4,z5,z6,z1167])],[(0,[z1,z2,z1168,z4,z5,z6]),(0,[z1,z202,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z163,z6]),(0,[z1,z636,z21,z4,z5,z6]),(0,[z1,z23,z659,z4,z5,z6]),(0,[z140,z2,z3,z4,z11,z6]),(0,[z1,z3,z4,z11,z606,z6]),(0,[z1,z1169,z2,z4,z5,z6])],[(0,[z2,z16,z139,z4,z5,z6]),(0,[z16,z3,z4,z12,z10,z6]),(0,[z368,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z836,z5,z6]),(0,[z1,z122,z3,z4,z11,z6]),(0,[z164,z78,z1,z3,z5,z6])],[(0,[z28,z120,z21,z4,z5,z6]),(0,[z7,z2,z21,z4,z5,z6]),(0,[z135,z1,z21,z4,z10,z6]),(0,[z55,z207,z21,z4,z5,z6]),(0,[z140,z2,z37,z4,z5,z6]),(0,[z164,z1,z3,z4,z5,z58])],[(1,[z122,z3,z4,z161,z6]),(0,[z496,z1,z2,z3,z6,z117])],[(0,[z26,z16,z41,z4,z5,z6]),(0,[z793,z28,z2,z4,z5,z6]),(0,[z28,z2,z3,z1081,z5,z6]),(0,[z1,z2,z3,z4,z1170,z6])],[(0,[z1,z21,z90,z4,z10,z6]),(0,[z46,z1,z3,z4,z5,z241]),(0,[z2,z207,z3,z4,z10,z6]),(0,[z33,z1,z2,z4,z146,z6]),(0,[z1171,z2,z3,z4,z5,z6]),(0,[z1172,z2,z3,z4,z5,z6]),(0,[z2,z1173,z3,z4,z5,z6]),(0,[z1,z3,z4,z1174,z6,z119])],[(0,[z179,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1175,z6]),(0,[z1,z1176,z3,z4,z5,z6]),(0,[z151,z2,z3,z4,z11,z6]),(0,[z140,z2,z3,z4,z435,z6])],[(0,[z16,z644,z3,z4,z5,z6]),(0,[z442,z2,z3,z116,z5,z6]),(0,[z1,z2,z4,z5,z6,z1177])],[(0,[z26,z1,z21,z4,z10,z6]),(0,[z2,z3,z4,z5,z6,z1178])],[(0,[z1,z3,z4,z5,z812,z6])],[(0,[z1,z2,z3,z4,z1179,z6]),(0,[z1180,z2,z3,z4,z5,z6]),(0,[z1,z2,z452,z4,z10,z6]),(0,[z368,z2,z3,z4,z11,z6]),(0,[z1,z2,z96,z4,z435,z6])],[(0,[z2,z16,z27,z4,z5,z6]),(0,[z16,z3,z73,z4,z10,z6]),(0,[z2,z3,z4,z5,z1181,z6]),(0,[z1,z2,z3,z4,z1182,z6]),(0,[z1,z528,z21,z4,z5,z6]),(0,[z164,z1,z23,z4,z5,z6]),(0,[z170,z30,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z101,z168]),(0,[z1,z2,z1183,z4,z5,z6]),(0,[z46,z1,z3,z4,z208,z24]),(0,[z1184,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1068,z6])],[(0,[z16,z3,z4,z517,z5,z6]),(0,[z286,z1,z2,z4,z552,z6]),(0,[z1185,z2,z3,z4,z5,z6])]],
   [[(0,[z179,z2,z3,z4,z11,z6]),(0,[z237,z1,z2,z3,z212,z6])],[(0,[z2,z16,z3,z4,z563,z6]),(0,[z2,z3,z4,z5,z6,z218])],[(0,[z1,z2,z3,z4,z5,z1186]),(0,[z1187,z2,z3,z4,z5,z6])],[(0,[z1,z16,z21,z4,z10,z6]),(0,[z28,z2,z3,z1188,z5,z6]),(0,[z1,z1189,z2,z4,z5,z6]),(0,[z232,z102,z3,z4,z10,z6]),(0,[z2,z4,z5,z6,z466,z218])],[(0,[z238,z2,z3,z4,z5,z365]),(0,[z1,z1190,z3,z4,z5,z6]),(0,[z140,z2,z21,z4,z5,z6]),(1,[z103,z3,z4,z10,z6]),(0,[z595,z2,z452,z4,z5,z6]),(0,[z1,z2,z3,z4,z1191,z6]),(0,[z1,z301,z2,z25,z5,z6]),(0,[z2,z3,z4,z363,z6,z218])],[(0,[z1,z122,z21,z4,z5,z6]),(0,[z1,z2,z3,z325,z5,z24]),(0,[z2,z1192,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z720]),(0,[z1,z2,z499,z4,z10,z6]),(0,[z33,z270,z2,z4,z146,z6]),(0,[z1,z2,z1193,z4,z5,z6])],[(0,[z396,z2,z67,z4,z5,z6]),(0,[z9,z122,z3,z4,z5,z6]),(0,[z1,z122,z150,z4,z5,z6]),(0,[z2,z1194,z3,z4,z5,z6])],[(0,[z201,z2,z303,z4,z5,z6]),(0,[z164,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1195,z6]),(0,[z237,z1,z2,z3,z95,z6]),(0,[z1,z2,z3,z4,z1196,z6])],[(0,[z1,z2,z3,z1188,z5,z6]),(0,[z1,z2,z1197,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1088])],[(0,[z1,z2,z41,z4,z200,z6]),(0,[z28,z2,z69,z4,z5,z6]),(0,[z151,z2,z21,z4,z5,z6])],[(0,[z28,z102,z3,z4,z10,z6]),(0,[z2,z145,z4,z5,z22,z6]),(0,[z1,z21,z4,z10,z211,z6])],[(0,[z1,z235,z21,z4,z10,z6])],[(0,[z16,z42,z3,z4,z10,z6]),(0,[z1,z2,z21,z4,z163,z6]),(0,[z1198,z2,z3,z4,z5,z6]),(0,[z1,z2,z1199,z4,z5,z6]),(0,[z1200,z2,z3,z4,z5,z6]),(0,[z2,z4,z5,z6,z51,z258])],[(0,[z368,z2,z21,z4,z5,z6]),(0,[z1,z404,z3,z4,z10,z6])],[(0,[z270,z2,z3,z4,z5,z6]),(0,[z1,z2,z1201,z4,z5,z6])]],
   [[(0,[z763,z2,z3,z4,z5,z6]),(0,[z16,z3,z4,z551,z5,z6]),(0,[z1,z2,z3,z4,z1202,z6]),(0,[z1,z2,z69,z4,z5,z6])],[(0,[z1,z21,z4,z10,z234,z6]),(0,[z46,z1,z21,z4,z10,z6]),(0,[z1,z2,z3,z4,z1203,z6]),(0,[z1,z2,z3,z559,z5,z17]),(0,[z164,z1,z3,z4,z11,z6]),(0,[z140,z2,z3,z4,z185,z6]),(0,[z1204,z2,z3,z4,z5,z6]),(0,[z1205,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1206]),(0,[z70,z844,z3,z4,z5,z6])],[(0,[z1,z2,z1207,z4,z5,z6]),(0,[z33,z1,z2,z4,z665,z6]),(0,[z1,z544,z2,z546,z5,z6]),(0,[z271,z2,z626,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z805]),(0,[z1,z2,z4,z248,z51,z40])],[(0,[z179,z2,z21,z4,z5,z6]),(0,[z1,z2,z3,z1208,z5,z6])],[(0,[z1,z2,z4,z1209,z5,z6]),(0,[z1,z267,z21,z4,z10,z6]),(0,[z159,z2,z535,z4,z5,z6]),(0,[z1,z2,z3,z4,z1210,z6]),(0,[z78,z1,z2,z3,z319,z6])],[(0,[z16,z61,z3,z4,z10,z6]),(0,[z2,z16,z4,z5,z6,z466]),(0,[z237,z102,z1,z3,z10,z6]),(0,[z1,z2,z452,z4,z59,z6]),(0,[z1,z2,z96,z4,z185,z6])],[(0,[z1,z2,z1211,z4,z5,z6]),(0,[z1,z2,z3,z1212,z5,z6]),(0,[z1,z2,z1213,z4,z5,z6]),(0,[z238,z16,z3,z4,z10,z6]),(0,[z184,z2,z303,z4,z161,z6]),(0,[z1,z2,z1214,z4,z5,z6]),(0,[z1,z2,z3,z4,z1215,z6]),(0,[z1,z2,z3,z250,z5,z17]),(0,[z1,z2,z3,z4,z1216,z6])],[(0,[z28,z3,z21,z4,z10,z6])],[(0,[z628,z2,z251,z4,z5,z6]),(0,[z28,z1,z21,z4,z10,z6]),(0,[z1,z1217,z3,z4,z5,z6]),(0,[z1,z21,z5,z212,z10,z6]),(0,[z270,z2,z3,z4,z11,z6]),(0,[z2,z1218,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1219,z6]),(0,[z558,z1,z21,z4,z10,z6]),(0,[z1,z2,z69,z4,z11,z6]),(0,[z1,z2,z3,z1145,z5,z6]),(0,[z1,z2,z1220,z4,z5,z6])],[(0,[z16,z3,z4,z5,z577,z6]),(0,[z1,z2,z535,z4,z10,z6]),(0,[z1,z2,z3,z4,z5,z1221]),(0,[z1,z2,z3,z4,z1174,z6])],[(0,[z16,z3,z4,z10,z181,z6]),(0,[z1,z2,z3,z1222,z5,z6]),(0,[z183,z2,z3,z4,z5,z414]),(0,[z1,z2,z535,z4,z5,z241]),(0,[z2,z3,z4,z11,z6,z1078]),(0,[z164,z1,z789,z4,z5,z6])],[(0,[z375,z16,z3,z4,z5,z6]),(0,[z1,z3,z1083,z36,z5,z6])],[(0,[z1,z60,z2,z8,z5,z6]),(0,[z1,z2,z3,z4,z1223,z6]),(0,[z1224,z2,z3,z4,z5,z6])],[(0,[z16,z3,z4,z36,z10,z6]),(0,[z224,z16,z3,z4,z10,z6]),(0,[z122,z16,z3,z4,z5,z6]),(0,[z28,z2,z321,z4,z5,z6]),(0,[z575,z1,z2,z4,z211,z6]),(0,[z2,z85,z23,z4,z5,z6])],[(0,[z16,z3,z81,z4,z10,z6]),(0,[z1,z1225,z3,z4,z5,z6]),(0,[z716,z2,z3,z4,z5,z6]),(0,[z595,z2,z3,z4,z59,z6])]],
   [[(0,[z1,z21,z4,z281,z10,z6]),(0,[z237,z1,z2,z21,z5,z6]),(0,[z1,z3,z4,z5,z876,z24]),(0,[z1,z2,z3,z4,z1226,z6])],[(0,[z2,z3,z4,z5,z1227,z6])],[(0,[z100,z16,z3,z36,z5,z6]),(0,[z309,z2,z73,z4,z5,z6]),(0,[z1228,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1229,z6]),(0,[z118,z2,z452,z4,z5,z6])],[(0,[z1230,z2,z3,z4,z5,z6]),(0,[z1,z23,z21,z4,z10,z6]),(0,[z1,z2,z3,z4,z248,z680]),(0,[z1231,z2,z3,z4,z5,z6])],[(0,[z16,z3,z4,z91,z10,z6]),(0,[z28,z343,z2,z4,z5,z6]),(0,[z1,z2,z321,z4,z5,z6]),(0,[z164,z1,z21,z4,z5,z6]),(0,[z1,z2,z23,z4,z360,z6])],[(0,[z1,z2,z3,z4,z1232,z6]),(0,[z575,z1,z3,z4,z10,z6]),(0,[z1,z2,z1233,z4,z5,z6])],[(0,[z410,z2,z3,z4,z563,z6]),(0,[z1,z2,z3,z4,z1234,z6]),(0,[z1,z343,z2,z4,z248,z40]),(0,[z1,z2,z1235,z4,z5,z6])],[(0,[z1,z2,z756,z4,z5,z6]),(0,[z2,z23,z4,z5,z1227,z6]),(0,[z159,z2,z3,z4,z5,z168]),(0,[z2,z3,z4,z5,z6,z1236])],[(0,[z16,z21,z4,z5,z10,z6]),(0,[z550,z16,z3,z4,z5,z6]),(0,[z1,z1237,z3,z4,z5,z6]),(0,[z328,z2,z29,z4,z5,z6]),(0,[z1,z572,z3,z4,z10,z6])],[(0,[z2,z16,z1238,z3,z4,z5]),(0,[z28,z2,z96,z4,z5,z6]),(0,[z43,z2,z29,z4,z10,z6]),(0,[z368,z2,z3,z18,z5,z6]),(0,[z1239,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1240,z6]),(0,[z78,z1,z2,z3,z6,z117])],[(0,[z2,z85,z3,z4,z5,z6]),(0,[z28,z2,z3,z4,z360,z6]),(0,[z20,z2,z4,z129,z5,z6]),(0,[z1,z21,z4,z10,z390,z6]),(0,[z2,z21,z4,z5,z137,z6]),(0,[z1241,z2,z3,z4,z5,z6]),(0,[z1,z343,z2,z4,z5,z6])],[(0,[z1,z539,z3,z4,z10,z6]),(0,[z1242,z2,z3,z4,z5,z6]),(0,[z1,z425,z23,z4,z5,z6])],[(0,[z1,z2,z1243,z4,z5,z6]),(0,[z1244,z2,z3,z4,z5,z6])],[(0,[z1,z2,z1245,z4,z5,z6]),(0,[z1,z2,z321,z4,z11,z6]),(0,[z1,z2,z3,z4,z1246,z6])],[(0,[z1,z488,z3,z4,z10,z6]),(0,[z2,z3,z4,z5,z754,z6])],[(0,[z2,z3,z4,z5,z6,z1247]),(0,[z237,z1,z120,z3,z10,z6])]],
   [[(0,[z1,z19,z1248,z4,z5,z6]),(0,[z1,z30,z21,z4,z10,z6]),(0,[z1,z2,z3,z4,z360,z6]),(0,[z1,z189,z3,z4,z11,z6])],[(0,[z100,z1,z23,z36,z5,z6]),(0,[z1,z23,z4,z5,z6,z119]),(0,[z1,z2,z969,z3,z10,z6]),(0,[z1249,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1009,z5,z17])],[(0,[z28,z253,z3,z4,z5,z6]),(0,[z100,z151,z3,z36,z5,z6])],[(0,[z1,z343,z2,z4,z11,z6]),(0,[z1,z3,z4,z5,z6,z1250])],[(0,[z60,z2,z16,z157,z5,z6]),(0,[z2,z16,z145,z4,z5,z6]),(0,[z1251,z2,z3,z4,z5,z6]),(0,[z1252,z2,z3,z4,z5,z6]),(0,[z1,z2,z452,z49,z5,z6])],[(0,[z20,z170,z2,z4,z5,z6]),(0,[z1253,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z4,z363,z6]),(0,[z1,z2,z3,z49,z10,z6]),(0,[z974,z2,z3,z4,z10,z6]),(0,[z2,z85,z37,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1254,z6]),(0,[z223,z2,z29,z4,z5,z6]),(0,[z2,z3,z4,z774,z5,z6]),(0,[z1,z301,z2,z4,z363,z6])],[(0,[z1,z2,z3,z4,z1255,z6]),(0,[z1,z2,z4,z11,z283,z6]),(0,[z1,z2,z3,z4,z1256,z6]),(0,[z2,z1257,z3,z4,z5,z6])],[(0,[z16,z3,z4,z5,z638,z6]),(0,[z16,z3,z4,z5,z6,z639]),(0,[z43,z2,z393,z4,z5,z6]),(0,[z151,z2,z3,z4,z298,z6]),(0,[z1,z2,z96,z4,z11,z6]),(0,[z1,z2,z3,z4,z1258,z6]),(0,[z164,z1,z301,z4,z5,z6]),(0,[z1,z2,z1259,z4,z5,z6])],[(0,[z26,z1230,z3,z4,z5,z6]),(0,[z2,z16,z3,z4,z363,z6]),(0,[z1,z3,z508,z4,z10,z6]),(0,[z159,z2,z3,z4,z10,z6]),(0,[z1,z2,z452,z325,z5,z6]),(0,[z2,z85,z3,z4,z435,z6])],[(0,[z1,z21,z4,z512,z10,z6]),(0,[z159,z2,z3,z4,z5,z241]),(0,[z1260,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z325,z10,z6]),(0,[z286,z1,z2,z4,z345,z6])],[(0,[z2,z16,z507,z4,z5,z6]),(0,[z237,z28,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z1261,z6]),(0,[z1,z2,z1262,z4,z5,z6])],[(0,[z9,z1,z21,z4,z10,z6]),(0,[z1,z2,z1263,z4,z5,z6])],[(0,[z1,z2,z139,z4,z5,z6]),(0,[z100,z1,z3,z36,z5,z6]),(0,[z118,z2,z3,z4,z59,z6])],[(0,[z1,z2,z3,z4,z1264,z6]),(0,[z100,z1,z21,z4,z10,z6]),(0,[z1228,z2,z21,z4,z5,z6]),(0,[z621,z2,z3,z4,z10,z6]),(0,[z595,z2,z3,z49,z5,z6])],[(0,[z28,z30,z2,z4,z5,z63]),(0,[z1,z3,z4,z514,z10,z6]),(0,[z1,z2,z3,z4,z1265,z6]),(0,[z1,z3,z4,z163,z10,z6]),(0,[z103,z2,z23,z4,z5,z6]),(0,[z164,z1,z3,z90,z5,z6]),(0,[z1266,z2,z3,z4,z5,z6])]],
   [[(0,[z84,z16,z21,z4,z5,z6]),(0,[z237,z2,z16,z3,z10,z6]),(0,[z1,z54,z21,z4,z10,z6]),(0,[z1,z2,z1267,z4,z5,z6]),(0,[z653,z1,z3,z4,z10,z6]),(0,[z1,z2,z23,z4,z563,z6]),(0,[z1,z2,z3,z4,z10,z241])],[(0,[z28,z2,z27,z4,z5,z6]),(0,[z1,z583,z3,z4,z10,z6]),(0,[z1,z2,z1268,z4,z5,z6]),(0,[z575,z1,z21,z4,z10,z6]),(0,[z2,z356,z23,z4,z5,z6]),(0,[z1269,z2,z3,z4,z5,z6]),(0,[z1270,z1,z2,z3,z185,z6]),(0,[z343,z2,z4,z5,z6,z258])],[(0,[z201,z122,z3,z4,z5,z6]),(0,[z1,z55,z21,z4,z10,z6]),(0,[z102,z103,z3,z4,z10,z6]),(0,[z1,z525,z3,z4,z10,z6]),(0,[z46,z595,z3,z4,z5,z24]),(0,[z1,z2,z4,z5,z6,z1271])],[(0,[z16,z3,z4,z5,z6,z657]),(0,[z361,z2,z23,z4,z5,z6]),(0,[z1,z189,z21,z4,z5,z6]),(0,[z595,z2,z3,z325,z5,z6]),(0,[z2,z3,z4,z5,z6,z1272]),(0,[z1,z2,z1145,z157,z5,z6])],[(0,[z2,z16,z3,z1273,z5,z6]),(0,[z30,z2,z16,z4,z5,z63]),(0,[z43,z2,z454,z4,z5,z6]),(0,[z1,z2,z3,z4,z1274,z6]),(0,[z1,z21,z373,z4,z10,z6]),(0,[z100,z1,z3,z36,z298,z6])],[(0,[z2,z16,z203,z4,z5,z6]),(0,[z2,z3,z1275,z4,z5,z6]),(0,[z1,z2,z303,z4,z10,z6]),(0,[z1,z2,z1276,z4,z5,z6]),(0,[z1,z2,z3,z1277,z5,z6]),(0,[z1,z70,z4,z5,z146,z6]),(0,[z1,z30,z2,z4,z5,z63])],[(0,[z2,z16,z3,z254,z5,z6]),(0,[z28,z2,z3,z4,z563,z6]),(0,[z2,z85,z21,z4,z5,z6]),(0,[z100,z1,z3,z36,z11,z6]),(0,[z1,z533,z3,z4,z10,z6]),(0,[z1,z2,z1278,z4,z5,z6])],[(0,[z1,z2,z27,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1279]),(0,[z1280,z1,z2,z4,z5,z6]),(0,[z1,z483,z3,z4,z10,z6]),(0,[z1,z301,z2,z4,z424,z6])],[(0,[z9,z16,z3,z4,z10,z6]),(0,[z16,z3,z4,z128,z10,z6]),(0,[z43,z2,z4,z681,z5,z6]),(0,[z1281,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1282,z5,z6]),(0,[z595,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z647,z5,z17])],[(0,[z16,z675,z3,z4,z5,z6]),(0,[z1,z120,z3,z212,z10,z6]),(0,[z1,z2,z783,z4,z5,z6]),(0,[z1,z301,z2,z157,z5,z6])],[(0,[z100,z16,z3,z4,z10,z6]),(0,[z2,z16,z3,z4,z424,z6]),(0,[z99,z16,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1283,z6]),(0,[z2,z23,z4,z5,z6,z218]),(0,[z1,z2,z3,z4,z1284,z6]),(0,[z164,z1,z3,z12,z5,z6])],[(0,[z103,z2,z3,z4,z5,z6]),(1,[z28,z21,z4,z10,z6]),(0,[z2,z122,z3,z4,z161,z6]),(0,[z1,z2,z1248,z4,z5,z6]),(0,[z1,z2,z3,z4,z1285,z6])],[(0,[z1,z2,z3,z4,z563,z6]),(0,[z1,z2,z21,z4,z360,z6]),(0,[z159,z2,z3,z4,z101,z6]),(0,[z1,z2,z3,z4,z1286,z6]),(0,[z1287,z2,z3,z4,z5,z6])],[(0,[z2,z16,z37,z4,z5,z6]),(0,[z2,z356,z3,z4,z5,z6]),(0,[z1,z2,z3,z1288,z5,z6]),(0,[z1,z458,z2,z4,z211,z6]),(0,[z1,z2,z3,z4,z5,z1289])],[(0,[z16,z3,z252,z4,z5,z6]),(0,[z2,z16,z4,z5,z6,z51]),(0,[z1,z1290,z2,z4,z5,z6]),(0,[z103,z2,z203,z4,z5,z6]),(0,[z1,z30,z2,z4,z11,z63]),(0,[z1,z3,z4,z11,z6,z119])],[(0,[z361,z2,z3,z4,z5,z6]),(0,[z1,z2,z1291,z4,z5,z6]),(0,[z1,z892,z2,z3,z5,z6]),(0,[z1,z2,z3,z49,z59,z6])]],
   [[(0,[z1,z2,z27,z4,z11,z6]),(0,[z55,z16,z321,z4,z5,z6]),(0,[z636,z16,z3,z4,z5,z6]),(0,[z184,z122,z3,z4,z161,z6]),(0,[z1,z2,z1292,z4,z5,z6])],[(0,[z2,z16,z3,z4,z435,z6]),(0,[z28,z3,z4,z11,z10,z6]),(0,[z1,z2,z1293,z4,z5,z6])],[(0,[z1040,z572,z3,z4,z5,z6])],[(0,[z184,z2,z3,z4,z774,z6]),(0,[z1,z2,z3,z4,z101,z241]),(0,[z2,z85,z3,z4,z185,z6])],[(0,[z28,z2,z3,z1294,z5,z6]),(0,[z1,z92,z21,z4,z10,z6]),(0,[z103,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z325,z59,z6])],[(0,[z1295,z2,z3,z4,z5,z6]),(0,[z223,z2,z23,z4,z5,z6]),(0,[z1,z329,z3,z4,z10,z6]),(0,[z237,z1,z2,z3,z367,z6]),(0,[z46,z1,z452,z4,z5,z24]),(0,[z1,z70,z3,z4,z146,z6])],[(0,[z1,z573,z3,z4,z10,z6]),(0,[z2,z356,z3,z4,z11,z6]),(0,[z46,z1,z3,z4,z10,z24])],[(0,[z1,z2,z1296,z4,z5,z6]),(0,[z1,z3,z4,z11,z10,z6]),(0,[z2,z3,z4,z5,z1297,z6]),(0,[z78,z1,z2,z3,z424,z6])],[(0,[z28,z60,z2,z157,z5,z6]),(0,[z361,z2,z3,z4,z11,z6])],[(0,[z100,z1,z21,z36,z5,z6]),(0,[z411,z2,z3,z4,z10,z6]),(0,[z1,z30,z2,z4,z5,z633])],[(0,[z28,z2,z4,z5,z6,z466]),(0,[z1,z2,z3,z1294,z5,z6]),(0,[z2,z3,z4,z10,z6,z258])],[(0,[z28,z511,z3,z4,z5,z6]),(0,[z216,z2,z3,z4,z161,z6]),(0,[z410,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z36,z5,z241]),(0,[z1298,z2,z3,z4,z5,z6]),(0,[z1270,z1,z2,z3,z5,z6])],[(0,[z1,z21,z4,z436,z5,z6]),(0,[z1,z2,z23,z828,z5,z6]),(0,[z1,z2,z3,z1299,z5,z6]),(0,[z1,z2,z4,z5,z6,z823]),(0,[z118,z2,z3,z49,z5,z6]),(0,[z33,z223,z2,z4,z146,z6])],[(0,[z558,z2,z29,z4,z5,z6]),(0,[z1,z2,z1300,z3,z5,z6]),(0,[z1,z2,z21,z4,z363,z6]),(0,[z1,z23,z4,z11,z10,z6]),(0,[z1,z3,z4,z10,z574,z6]),(0,[z1,z2,z3,z1106,z10,z6])],[(0,[z1,z1230,z3,z4,z5,z6]),(0,[z2,z488,z29,z4,z5,z6]),(0,[z1,z3,z21,z4,z130,z6]),(0,[z1,z60,z2,z157,z5,z6]),(0,[z1,z3,z4,z1234,z6,z119])],[(0,[z1,z19,z1301,z4,z5,z6]),(0,[z1,z2,z1302,z4,z5,z6]),(0,[z575,z1,z2,z4,z146,z6]),(0,[z1,z2,z1303,z4,z5,z6])]],
   [[(0,[z2,z16,z3,z4,z514,z6]),(0,[z43,z2,z73,z4,z5,z6]),(0,[z2,z16,z150,z4,z5,z6]),(0,[z1,z23,z644,z4,z5,z6]),(0,[z1304,z2,z3,z4,z5,z6]),(0,[z100,z1,z3,z325,z5,z6]),(0,[z1,z2,z4,z5,z6,z466])],[(0,[z1,z2,z1305,z4,z5,z6]),(0,[z223,z2,z3,z4,z5,z6]),(0,[z1,z2,z1306,z4,z5,z6]),(0,[z1,z2,z3,z4,z1307,z6]),(0,[z1,z112,z21,z4,z10,z6]),(0,[z1,z2,z21,z1277,z5,z6]),(0,[z1,z2,z23,z941,z5,z6]),(0,[z1308,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1309])],[(0,[z293,z2,z23,z4,z5,z6]),(0,[z179,z2,z381,z4,z5,z6]),(0,[z1,z2,z4,z363,z6,z466])],[(0,[z1,z2,z1310,z4,z5,z6]),(0,[z1,z432,z21,z4,z5,z6]),(0,[z368,z2,z3,z81,z5,z17])],[(0,[z1,z2,z41,z4,z132,z6]),(0,[z143,z16,z3,z4,z10,z6]),(0,[z1,z3,z4,z607,z10,z6]),(0,[z1311,z2,z23,z4,z5,z6])],[(0,[z1,z120,z3,z4,z132,z6]),(0,[z368,z2,z3,z297,z5,z6]),(0,[z1,z3,z4,z1083,z5,z6]),(0,[z118,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z1050,z6])],[(0,[z410,z2,z3,z4,z5,z6]),(0,[z103,z2,z21,z4,z5,z6]),(0,[z1,z2,z1312,z4,z5,z6]),(0,[z1,z60,z2,z157,z11,z6]),(0,[z2,z3,z4,z11,z6,z218])],[(0,[z2,z16,z4,z5,z711,z6]),(0,[z183,z2,z3,z254,z5,z225]),(0,[z1,z2,z21,z4,z563,z6]),(0,[z1,z2,z3,z828,z5,z6])],[(0,[z153,z16,z3,z4,z10,z6]),(0,[z1,z2,z1023,z4,z5,z6]),(0,[z2,z356,z21,z4,z5,z6]),(0,[z1313,z2,z3,z4,z5,z6]),(0,[z164,z1,z3,z4,z5,z24]),(0,[z2,z3,z4,z5,z6,z1314])],[(0,[z1,z21,z4,z129,z10,z6])],[(0,[z2,z16,z3,z4,z185,z6]),(0,[z361,z2,z21,z4,z5,z6]),(0,[z1,z785,z21,z4,z5,z6]),(0,[z293,z2,z3,z4,z248,z40])],[(0,[z2,z16,z3,z188,z5,z6]),(0,[z1,z2,z1315,z4,z5,z6]),(0,[z1316,z2,z3,z4,z5,z6])],[(0,[z2,z16,z193,z3,z5,z6]),(0,[z7,z2,z3,z4,z10,z6]),(0,[z1,z2,z3,z941,z5,z6])],[(0,[z1,z1317,z2,z4,z5,z6]),(0,[z1,z2,z3,z1318,z5,z6]),(0,[z1,z2,z1319,z4,z5,z6])],[(0,[z441,z2,z3,z281,z5,z6]),(0,[z28,z2,z1320,z4,z5,z6]),(0,[z293,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z1145,z5,z6]),(0,[z1,z30,z2,z188,z5,z63])]],
   [[(0,[z1,z2,z4,z5,z6,z1321]),(0,[z1,z458,z21,z4,z10,z6]),(0,[z410,z2,z3,z4,z11,z6]),(0,[z1,z572,z3,z4,z163,z6]),(0,[z46,z1,z3,z4,z59,z24]),(0,[z1322,z2,z3,z4,z5,z6])],[(0,[z16,z3,z90,z4,z10,z6]),(0,[z1,z2,z3,z1323,z5,z6]),(0,[z35,z2,z725,z4,z5,z6]),(0,[z1311,z2,z3,z4,z5,z6])],[(0,[z1,z2,z41,z4,z10,z6]),(0,[z16,z39,z3,z4,z10,z6]),(0,[z33,z2,z16,z4,z146,z6]),(0,[z1,z2,z3,z4,z1324,z6]),(0,[z1,z2,z3,z4,z1325,z6]),(0,[z1,z122,z971,z4,z5,z6]),(0,[z1326,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z954,z6]),(0,[z151,z2,z3,z4,z5,z168]),(0,[z1313,z2,z3,z4,z11,z6]),(0,[z1,z2,z4,z1068,z146,z6])],[(0,[z170,z572,z3,z4,z5,z6])],[(0,[z1,z2,z1238,z3,z4,z5]),(0,[z20,z2,z29,z4,z5,z6]),(0,[z1,z2,z3,z1327,z5,z6]),(0,[z100,z1,z3,z1083,z5,z6]),(0,[z1,z30,z70,z4,z5,z6])],[(0,[z1,z2,z27,z4,z200,z6]),(0,[z2,z16,z734,z4,z5,z6]),(0,[z1,z2,z1320,z4,z5,z6]),(0,[z1,z2,z1328,z4,z5,z6]),(0,[z1,z2,z3,z884,z10,z6]),(0,[z1,z2,z1329,z4,z5,z6]),(0,[z1,z2,z193,z3,z5,z6]),(0,[z1,z2,z3,z4,z733,z40])],[(0,[z143,z2,z67,z4,z5,z6]),(0,[z1,z2,z75,z4,z10,z6]),(0,[z2,z85,z3,z4,z11,z6])],[(0,[z112,z16,z3,z4,z10,z6]),(0,[z2,z16,z739,z4,z5,z6]),(0,[z201,z1,z21,z4,z10,z6]),(0,[z134,z410,z3,z4,z10,z6]),(0,[z2,z1330,z3,z4,z5,z6]),(0,[z164,z1,z3,z4,z929,z6])],[(0,[z810,z1,z2,z3,z5,z6]),(0,[z1,z318,z21,z4,z5,z6]),(0,[z293,z2,z3,z4,z11,z6]),(0,[z1,z2,z1331,z4,z5,z6]),(0,[z2,z1332,z3,z4,z5,z6])],[(0,[z2,z16,z23,z4,z5,z6]),(0,[z1,z2,z1333,z4,z5,z6]),(0,[z1,z21,z25,z4,z10,z6])],[(0,[z28,z2,z139,z4,z5,z6]),(0,[z1,z2,z3,z1334,z5,z6]),(0,[z401,z19,z3,z4,z5,z6]),(0,[z1,z2,z1301,z4,z5,z6]),(0,[z1,z1335,z2,z4,z5,z6]),(0,[z1,z21,z4,z10,z6,z24]),(0,[z1,z2,z3,z4,z367,z568]),(0,[z1,z1336,z3,z4,z5,z6]),(0,[z164,z1,z3,z81,z5,z17])],[(0,[z1337,z2,z3,z4,z5,z6]),(0,[z1,z2,z1238,z3,z4,z10]),(0,[z1338,z2,z3,z4,z5,z6]),(0,[z293,z2,z4,z5,z6,z51])],[(0,[z16,z3,z373,z4,z10,z6]),(0,[z28,z301,z2,z4,z5,z6])],[(0,[z1,z2,z1339,z4,z5,z6]),(0,[z223,z2,z21,z4,z5,z6])],[(0,[z28,z2,z3,z4,z363,z6]),(0,[z184,z2,z3,z4,z465,z6]),(0,[z1,z2,z1320,z4,z11,z6]),(0,[z1340,z2,z3,z4,z5,z6])],[(0,[z2,z16,z3,z4,z208,z6]),(0,[z1,z122,z3,z4,z10,z6]),(0,[z1,z2,z145,z4,z5,z6]),(0,[z237,z1,z2,z23,z10,z6]),(0,[z1,z3,z4,z5,z58,z241]),(0,[z2,z1341,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1342])]],
   [[(0,[z28,z2,z507,z4,z5,z6]),(0,[z1,z3,z4,z911,z10,z6]),(0,[z1,z2,z3,z4,z1343,z6]),(0,[z1,z2,z3,z4,z1344,z6]),(0,[z1,z2,z1345,z4,z5,z6])],[(0,[z2,z16,z3,z4,z248,z40]),(0,[z1,z21,z71,z4,z10,z6]),(0,[z1,z316,z21,z4,z5,z6]),(0,[z1,z3,z659,z4,z10,z6])],[(0,[z2,z16,z23,z4,z11,z6]),(0,[z1,z359,z2,z8,z5,z6]),(0,[z1,z2,z1157,z4,z10,z6]),(0,[z1,z301,z2,z4,z5,z6]),(0,[z1346,z2,z3,z4,z5,z6])],[(0,[z16,z393,z3,z4,z5,z6]),(0,[z201,z16,z3,z4,z10,z6]),(0,[z28,z600,z3,z4,z5,z6]),(0,[z1,z2,z1347,z4,z5,z6]),(0,[z410,z2,z21,z4,z5,z6]),(0,[z1,z2,z1348,z4,z5,z6])],[(0,[z1,z120,z3,z4,z911,z6]),(0,[z1,z2,z3,z4,z1349,z6]),(0,[z1,z2,z3,z4,z363,z6])],[(0,[z2,z16,z3,z4,z5,z6]),(0,[z20,z35,z2,z4,z5,z6]),(0,[z1,z2,z23,z254,z5,z6]),(0,[z1350,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1351,z5,z6]),(0,[z1,z3,z4,z10,z6,z119])],[(0,[z16,z3,z4,z10,z211,z6]),(0,[z1,z2,z507,z4,z5,z6]),(0,[z1,z2,z3,z4,z1352,z6]),(0,[z179,z2,z3,z4,z115,z6])],[(0,[z2,z16,z767,z4,z5,z6]),(0,[z1,z2,z1353,z4,z5,z6]),(0,[z1,z2,z139,z4,z298,z6])],[(0,[z1,z2,z145,z4,z11,z6]),(0,[z2,z1354,z3,z4,z5,z6])],[(0,[z401,z2,z23,z4,z5,z6]),(0,[z1,z2,z23,z4,z424,z6]),(0,[z1,z2,z139,z4,z11,z6]),(0,[z1,z2,z3,z4,z1355,z6]),(0,[z2,z3,z4,z5,z1356,z6])],[(0,[z28,z2,z203,z4,z5,z6]),(0,[z1,z306,z3,z4,z10,z6]),(0,[z170,z2,z3,z4,z10,z6]),(0,[z78,z1,z2,z3,z6,z94])],[(0,[z28,z2,z3,z254,z5,z6]),(0,[z2,z195,z3,z4,z5,z6]),(0,[z293,z2,z21,z4,z5,z6]),(0,[z1,z301,z2,z4,z11,z6]),(0,[z1,z2,z1357,z4,z5,z6])],[(0,[z2,z16,z3,z4,z298,z6]),(0,[z16,z3,z4,z10,z234,z6]),(0,[z1,z2,z3,z4,z1358,z6]),(0,[z1,z1359,z3,z4,z5,z6]),(0,[z1360,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1361,z6]),(0,[z2,z3,z4,z5,z806,z6])],[(0,[z44,z16,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z1362,z6]),(0,[z1,z68,z21,z4,z5,z6]),(0,[z1,z21,z4,z10,z6,z532]),(0,[z1,z42,z21,z4,z10,z6]),(0,[z179,z2,z3,z4,z10,z6])],[(0,[z2,z16,z3,z4,z11,z6]),(0,[z1,z2,z1363,z4,z5,z6]),(0,[z1,z2,z21,z5,z954,z6]),(0,[z1,z3,z4,z371,z10,z6]),(0,[z1364,z2,z3,z4,z5,z6]),(0,[z270,z572,z3,z4,z5,z6]),(0,[z1,z2,z1365,z4,z5,z6])],[(0,[z1,z2,z3,z1273,z5,z6]),(0,[z28,z2,z3,z4,z424,z6]),(0,[z629,z2,z29,z4,z5,z6]),(0,[z1,z2,z507,z4,z11,z6]),(0,[z1,z21,z4,z10,z146,z6]),(0,[z1,z3,z4,z10,z345,z6]),(0,[z46,z1,z3,z49,z5,z24]),(0,[z1,z2,z4,z5,z6,z813]),(0,[z1366,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z19,z3,z4,z514,z6]),(0,[z1,z19,z150,z4,z5,z6]),(0,[z1,z2,z203,z4,z5,z6]),(0,[z1,z2,z23,z4,z435,z6]),(0,[z1,z70,z23,z4,z5,z6])],[(0,[z763,z16,z3,z4,z5,z6]),(0,[z1,z2,z3,z254,z5,z6]),(0,[z1,z2,z1367,z4,z5,z6]),(0,[z1,z2,z3,z1081,z10,z6])],[(0,[z2,z16,z3,z4,z52,z6]),(0,[z28,z2,z37,z4,z5,z6]),(0,[z1,z785,z3,z4,z5,z6])],[(0,[z16,z3,z5,z212,z10,z6]),(0,[z28,z2,z4,z5,z6,z51]),(0,[z1,z2,z1368,z4,z5,z6]),(0,[z1369,z2,z3,z4,z5,z6]),(0,[z1,z2,z1183,z4,z10,z6])],[(0,[z2,z195,z3,z4,z11,z6]),(0,[z46,z1,z3,z325,z5,z24]),(0,[z1370,z2,z3,z4,z5,z6])],[(0,[z401,z2,z3,z4,z5,z6]),(0,[z1,z21,z4,z5,z552,z6]),(0,[z1,z21,z4,z10,z6,z17]),(0,[z1,z2,z3,z4,z424,z6]),(0,[z1,z3,z81,z5,z119,z17])],[(0,[z2,z16,z83,z4,z5,z6]),(0,[z28,z2,z3,z4,z435,z6]),(0,[z1,z1085,z2,z4,z5,z6]),(0,[z1,z2,z1371,z4,z5,z6]),(0,[z33,z1,z572,z4,z146,z6])],[(0,[z309,z16,z3,z4,z10,z6]),(0,[z16,z3,z521,z4,z10,z6]),(0,[z0,z2,z3,z297,z5,z6]),(0,[z151,z2,z3,z4,z101,z6]),(0,[z1,z70,z3,z4,z91,z6])],[(0,[z1,z830,z2,z4,z5,z6]),(0,[z20,z184,z2,z4,z5,z6]),(0,[z1,z2,z1372,z4,z5,z6]),(0,[z1,z2,z37,z4,z5,z6]),(0,[z1,z2,z1373,z4,z5,z6]),(0,[z1,z2,z1374,z4,z5,z6])],[(0,[z216,z1,z2,z4,z146,z6]),(0,[z1,z2,z203,z4,z11,z6]),(0,[z1,z2,z4,z5,z6,z51])],[(1,[z16,z3,z212,z10,z6]),(0,[z384,z2,z29,z4,z5,z6]),(0,[z1,z2,z3,z254,z11,z6])],[(0,[z441,z16,z3,z4,z10,z6]),(0,[z16,z3,z4,z281,z10,z6]),(0,[z183,z2,z23,z4,z5,z225]),(0,[z2,z21,z4,z5,z6,z258]),(0,[z1,z2,z3,z1375,z5,z6]),(0,[z1,z2,z1376,z4,z5,z6])],[(0,[z1,z21,z4,z10,z6,z568]),(0,[z1,z70,z3,z4,z5,z6]),(0,[z1,z2,z381,z4,z360,z6]),(0,[z1,z2,z3,z4,z435,z6])],[(0,[z43,z2,z303,z4,z5,z6]),(0,[z1,z2,z1377,z4,z5,z6]),(0,[z1,z1378,z3,z4,z5,z6]),(0,[z2,z1379,z3,z4,z5,z6])],[(0,[z2,z16,z125,z4,z5,z6]),(0,[z1,z21,z4,z5,z574,z6]),(0,[z2,z3,z4,z10,z6,z218]),(0,[z164,z1,z3,z4,z10,z6]),(0,[z401,z2,z3,z4,z11,z6]),(0,[z2,z1380,z3,z4,z5,z6])],[(0,[z1,z2,z23,z4,z514,z6]),(0,[z1,z2,z69,z4,z115,z6]),(0,[z1,z2,z3,z1188,z10,z6]),(0,[z1,z2,z1381,z4,z5,z6])]],
   [[(0,[z1382,z2,z3,z4,z5,z6]),(0,[z1,z55,z75,z4,z5,z6]),(0,[z1,z2,z4,z5,z1383,z6]),(0,[z1,z682,z21,z4,z5,z6]),(0,[z153,z1,z21,z4,z10,z6]),(0,[z1,z2,z3,z4,z1384,z5])],[(0,[z2,z16,z21,z4,z5,z6]),(0,[z1,z1385,z3,z4,z5,z6]),(0,[z1,z2,z37,z4,z11,z6]),(0,[z2,z195,z4,z5,z62,z6])],[(0,[z1,z1386,z3,z4,z5,z6]),(0,[z1,z21,z4,z10,z22,z6]),(0,[z411,z134,z3,z4,z10,z6]),(0,[z151,z2,z535,z4,z5,z6]),(0,[z237,z1,z2,z3,z6,z532])],[(0,[z26,z16,z27,z4,z5,z6]),(0,[z134,z16,z3,z4,z10,z6]),(0,[z1387,z2,z3,z4,z5,z6]),(0,[z1,z3,z73,z4,z10,z6]),(0,[z183,z2,z3,z4,z5,z476])],[(0,[z1230,z16,z3,z4,z5,z6]),(0,[z502,z16,z3,z4,z10,z6]),(0,[z1388,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1375,z11,z6]),(0,[z118,z2,z3,z325,z5,z6]),(0,[z1,z2,z25,z426,z5,z6])],[(0,[z28,z2,z3,z4,z514,z6]),(0,[z1,z600,z21,z4,z5,z6]),(0,[z1,z399,z2,z4,z5,z256]),(0,[z1389,z2,z3,z4,z5,z6]),(0,[z270,z2,z3,z4,z10,z6])],[(0,[z1390,z2,z3,z4,z5,z6]),(0,[z1391,z2,z3,z4,z5,z6]),(0,[z164,z368,z3,z4,z5,z6])],[(0,[z394,z16,z3,z4,z5,z6]),(0,[z183,z2,z3,z4,z5,z225]),(0,[z1,z2,z3,z4,z5,z1392]),(0,[z2,z195,z21,z4,z5,z6]),(0,[z1,z2,z3,z5,z937,z6]),(0,[z1,z3,z4,z5,z6,z876]),(0,[z1,z2,z37,z4,z435,z6]),(0,[z1,z2,z3,z4,z1393,z6]),(0,[z1,z2,z1394,z4,z5,z6])],[(0,[z2,z1395,z3,z4,z5,z6])],[(0,[z1,z2,z1396,z4,z5,z6]),(0,[z1,z2,z3,z4,z1397,z6]),(0,[z1,z19,z23,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z856])],[(0,[z2,z16,z21,z4,z11,z6]),(0,[z1,z120,z23,z4,z10,z6]),(1,[z2,z725,z4,z5,z6]),(0,[z1,z2,z3,z1398,z5,z6]),(0,[z1,z2,z23,z4,z185,z6])],[(0,[z1,z2,z3,z4,z514,z6]),(0,[z260,z16,z3,z4,z5,z6]),(0,[z1,z2,z150,z4,z5,z6]),(0,[z1,z2,z3,z4,z1399,z6]),(0,[z1,z2,z3,z1400,z5,z6]),(0,[z1,z2,z1401,z4,z5,z6]),(0,[z1,z2,z23,z188,z5,z6])],[(0,[z1,z2,z3,z1402,z5,z6]),(0,[z1,z21,z4,z5,z606,z6]),(0,[z748,z2,z3,z4,z5,z6])],[(0,[z1,z2,z21,z254,z5,z6]),(0,[z223,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z1403,z5])],[(0,[z184,z2,z3,z4,z322,z6]),(0,[z1,z199,z2,z4,z5,z167]),(0,[z100,z1,z535,z36,z5,z6]),(0,[z401,z2,z125,z4,z5,z6])],[(0,[z1,z2,z3,z753,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 460).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 920).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1380).take 206) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1586)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [460, 460, 460, 206] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 85).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 85).take 85).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 170).take 102).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 272).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 370).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 458).take 54).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [85, 85, 102, 98, 88, 54] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

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

end PEqualNP.Outside.L_meta_36769

theorem PEqualNP.Outside.L_meta_36769 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36769.solve