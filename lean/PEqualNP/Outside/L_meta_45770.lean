import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45770

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
  Nat.testBit (4008241888 * 2 ^ 32 + 4008216704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0xb08016504a0ab5ae#64 ++ 0x0811615a310c36b6#64 ++ 0xf1e07ff1fe3fffff#64 ++ 0xfd19f1fe398e3fff#64 : BitVec 256),
   (0x522580a214455986#64 ++ 0x10c45c638461856d#64 ++ 0xfe7f81fe3fc7ffef#64 ++ 0xfee67e63c671c7ff#64 : BitVec 256),
   (0x656aaa0026906228#64 ++ 0xa3028b816f8168c3#64 ++ 0xfffffe003ff9f2ba#64 ++ 0xbf078f83ff81f8c7#64 : BitVec 256),
   (0x00734d3480018228#64 ++ 0xc3a80fb407da00d8#64 ++ 0x007fffffc001ff2c#64 ++ 0xc3f80ffc07fe00f8#64 : BitVec 256),
   (0x005c71c939200241#64 ++ 0x037fb00002b6db00#64 ++ 0x007ffffffffe03cf#64 ++ 0x03fff00007ffff00#64 : BitVec 256),
   (0x88000000000003d0#64 ++ 0x03fff6eed8000000#64 ++ 0xff800000000003f0#64 ++ 0x03fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [6, 13]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0004008010000000 0x0044100000208100 0x007f81fe3fc603cf 0x02e670000671c700

def z1 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0x007ffffffffe03cf 0x03fff00007ffff00

def z2 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z3 : W := mkw 0x5221802204455986 0x10804c638441046d 0xfe0000000001fc20 0xfc000e63c00000ff

def z4 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0xfffffe003ff9f2ba 0xbf078f83ff81f8c7

def z5 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xff800000000003f0 0x03fffffff8000000

def z6 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0xf1e07ff1fe3fffff 0xfd19f1fe398e3fff

def z7 : W := mkw 0x5221802204455986 0x10804c638441046d 0xfe7f80003fc1feaa 0xfe060e63c601c0ff

def z8 : W := mkw 0x522580a214455986 0x10c45c638461856d 0xfe7f81fe3fc7ffef 0xfee67e63c671c7ff

def z9 : W := mkw 0x8800000000000250 0x03bba6ac58000000 0x0180000000000330 0x03f98ffc38000000

def z10 : W := mkw 0x4204808214444800 0x1044100180218101 0x0e00000001c00000 0x00060001c001c000

def z11 : W := mkw 0x9000000000001186 0x0011604a10000424 0xf1e001f03e07ffff 0xfd19f1fe380007ff

def z12 : W := mkw 0xfaa596f25e4ffffe 0x1bfffffffd6db7ff 0xffffffffffffffff 0xffffffffffffffff

def z13 : W := mkw 0x6020820006006028 0x00000901250120c3 0xfffffe003ff9f2ba 0xbf078f83ff81f8c7

def z14 : W := mkw 0xf2a596f25e4ffdae 0x18d57d7bb56db7ff 0xffffffffffffffff 0xffffffffffffffff

def z15 : W := mkw 0x0050410000000200 0x0328000002920000 0x001f800e00000000 0x02e0000006700000

def z16 : W := mkw 0x005c71c939200001 0x0000000002b6db00 0x007ffffffffe000f 0x0000000007ffff00

def z17 : W := mkw 0x085c618931200251 0x03ee96a4cab2c900 0x0e1f800e01c00000 0x02e60e01c671c000

def z18 : W := mkw 0x885c71c9392003d1 0x03fff6eedab6db00 0xfffffffffffe03ff 0x03ffffffffffff00

def z19 : W := mkw 0x88000000000001d0 0x0057f04ad8000000 0xff800000000000d0 0x0007f003f8000000

def z20 : W := mkw 0xed6aaa00269063f8 0xa3ffffefff8168c3 0xfffffe003ff9f3fa 0xbfffffffff81f8c7

def z21 : W := mkw 0x5221802204455986 0x10c45c638441046d 0xfe0000000001ffe0 0xfee67e63c00000ff

def z22 : W := mkw 0xb0800610420ab5ae 0x0811615a310824b6 0xf18000000001fff0 0xfd19f1fe380000ff

def z23 : W := mkw 0x527de1ab35655bc7 0x13eedc6386f3cd6d 0xfe7f81fe3fc7ffef 0xfee67e63c671c7ff

def z24 : W := mkw 0x4021802004014000 0x00800c2104410049 0xfe7f81fe3fc1ffae 0xfee60e63c671c0ff

def z25 : W := mkw 0x657bef34a691e228 0xe3aa8fb56fdb68db 0xfffffffffff9ffbe 0xffff8ffffffff8ff

def z26 : W := mkw 0xb08012404a0a3586 0x0811604a30043626 0xf18000003e3e00d3 0x3c01f00238003f07

def z27 : W := mkw 0xb0f35f74ca0bb7ae 0xcbb96ffe37de36fe 0xf1fffffffe3fffff 0xfff9fffe3ffe3fff

def z28 : W := mkw 0x0000000000000000 0x0044100000000000 0x00000000000003c0 0x02e6700000000000

def z29 : W := mkw 0x0058610921200241 0x032a800002924800 0x0000000000000000 0x0000000000000000

def z30 : W := mkw 0x0000000000000240 0x037fb00000000000 0x00000000000003c0 0x03fff00000000000

def z31 : W := mkw 0x0011453480018000 0x40a80434005a0018 0x000001ffc0000d04 0x40f8007c007e0038

def z32 : W := mkw 0xda04808214445bd6 0x13fff6efd8218525 0xff8000003fc603f3 0x3ffffffff801c707

def z33 : W := mkw 0x00230c3480018028 0xc0800fb4054800d8 0x007f81fe0001ff2c 0xc2e00ffc067000f8

def z34 : W := mkw 0x4020800004004000 0x0000080104010041 0xfe7f80003fc1f2aa 0xbe060e03c601c0c7

def z35 : W := mkw 0x4073cd348401c228 0xc3a80fb507db00d9 0xfe7fffffffc1ffae 0xfffe0fffc7ffc0ff

def z36 : W := mkw 0x72a596f25e4ffc2e 0x18000911256db7ff 0x007ffffffffffc0f 0xfc00000007ffffff

def z37 : W := mkw 0x000c30c939200041 0x0057b0000024db00 0x000000003ffe00c3 0x0007f0000001ff00

def z38 : W := mkw 0x00230c3480018028 0xc0800fb4054800d8 0x000000000001fc20 0xc0000ffc000000f8

def z39 : W := mkw 0x8800000000000250 0x033ba28c58000000 0x0180000000000010 0x0119819c38000000

def z40 : W := mkw 0x522580a214455806 0x100008010461856d 0x007f81fe3fc7fc0f 0xfc0000000671c7ff

def z41 : W := mkw 0x885c71c9392003d1 0x037ff04adab6db00 0xfffffffffffe03df 0x03fff003ffffff00

def z42 : W := mkw 0xd22580a214455986 0x10d57c6b9461856d 0xffff81fe3fc7ffff 0xfffffffffe71c7ff

def z43 : W := mkw 0x880c30c9392003d1 0x03fff6eed824db00 0xff8000003ffe03f3 0x03fffffff801ff00

def z44 : W := mkw 0x0048200020000200 0x030282804a804800 0xfffffe003ff802ba 0x03078f83ff81f800

def z45 : W := mkw 0x522580a214455806 0x104418010461856d 0x007f81fe3fc7ffcf 0xfee670000671c7ff

def z46 : W := mkw 0x8800000000000190 0x008046eed8000000 0xff80000000000030 0x00000ffff8000000

def z47 : W := mkw 0x005c618931200241 0x036e900002b2c900 0x001f800e01c00000 0x02e600000671c000

def z48 : W := mkw 0x8800000000000190 0x009166eed8000000 0xff800000000003f0 0x0119fffff8000000

def z49 : W := mkw 0x208016504a0aa428 0x08000110210c3292 0x00007e01c0380000 0x00000000018e3800

def z50 : W := mkw 0x308016504a0ab42e 0x08000110210c36b6 0x00607ff1fe3ffc0f 0xfc000000018e3fff

def z51 : W := mkw 0x0000000000000200 0x0302828048000000 0xff800000000002b0 0x03078f83f8000000

def z52 : W := mkw 0x005c71c939200201 0x0302800002b6db00 0x007ffffffffe028f 0x0307800007ffff00

def z53 : W := mkw 0x90801450480a9586 0x0811605a100c1634 0x000001f1c0060d45 0x4018707c000e0738

def z54 : W := mkw 0xf5eabe506e9af7ae 0xab13ebdb7f8d7ef7 0xfffffff1ffffffff 0xff1fffffff8fffff

def z55 : W := mkw 0x0000000000000000 0x0000000000000000 0x007f80003fc0028a 0x020600000601c000

def z56 : W := mkw 0x00734d3480018028 0xc000091007da00d8 0x007fffffc001fc0c 0xc000000007fe00f8

def z57 : W := mkw 0xad4a2a0022902278 0xa33ba38c7b806882 0x01807e0000380010 0x0119819c39803800

def z58 : W := mkw 0x0050410000000200 0x0328000002920000 0x007fffffc000030c 0x03f8000007fe0000

def z59 : W := mkw 0x1204008210441986 0x1044504280208524 0x0000000000060041 0x0000700000000700

def z60 : W := mkw 0x2000020002002028 0x0000010021002082 0xf1e07e003e39f2ba 0xbd018182398038c7

def z61 : W := mkw 0x0010514909200041 0x0039200000161200 0x00000001c0000000 0x00180000000e0000

def z62 : W := mkw 0x6508a20026906000 0x2002800168016803 0xff8000003ff80092 0x3c078003f801f807

def z63 : W := mkw 0x65228a0006906028 0xa0000b816d0120c3 0xff8000000001f030 0xbc000f83f80000c7

def z64 : W := mkw 0x0000000000000000 0x008006a400000000 0x0000000000000020 0x00000ffc00000000

def z65 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0xff9f800001c1f030 0xbe060f83fe01c0c7

def z66 : W := mkw 0x5204808214445986 0x1044504380218525 0xfe0000003fc600c3 0x3c067003c001c707

def z67 : W := mkw 0x8000000000000180 0x0011604a10000000 0xf1800000000003f0 0x0119f1fe38000000

def z68 : W := mkw 0x0800000000000250 0x03ee96a4c8000000 0x0e00000000000000 0x02e60e01c0000000

def z69 : W := mkw 0xda2580a214455bd6 0x13fffeefdc61856d 0xffff81fe3fc7ffff 0xfffffffffe71c7ff

def z70 : W := mkw 0x0008304929200041 0x0013a00000045a00 0x0000000000380000 0x0001800000003800

def z71 : W := mkw 0x52278cb69445d9ae 0xd0c45ff7856985fd 0xfe7f81fe3fc7ffef 0xfee67fffc671c7ff

def z72 : W := mkw 0xa08016504a0aa428 0x08112118310c3292 0x01e07ff1fe3e03df 0x0119f19c398e3f00

def z73 : W := mkw 0x776faaa236d57bae 0xb3c6dfe3efe1edef 0xfffffffe3fffffff 0xffe7ffe3fff1ffff

def z74 : W := mkw 0xb0dc73c97b2a37c7 0x0b7ff04a32b6ff26 0xf1fffffffffe03df 0x3ffff0023fffff07

def z75 : W := mkw 0xb0800200420a3586 0x0800404a30002426 0xf180000000000010 0x3c00000238000007

def z76 : W := mkw 0x527df1eb3d655bc7 0x13fffc6386f7df6d 0xfe7fffffffffffef 0xfffffe63c7ffffff

def z77 : W := mkw 0x8000104008000180 0x0011604a10041200 0xf1e07ff1fe3e03ff 0x0119f1fe398e3f00

def z78 : W := mkw 0x1004008010001186 0x0044504200208524 0xf07f81fe3fc7ffef 0xfee670620671c7ff

def z79 : W := mkw 0x88000000000001d0 0x00fd746e90000000 0x0000000000000140 0x00f8707c00000000

def z80 : W := mkw 0x456aa80024904228 0xa3028b814f8148c1 0x0e7ffe0001c1f228 0x83060f81c781c0c0

def z81 : W := mkw 0xff6faaa236d57bfe 0xb3ffffefffe1edef 0xfffffffe3fffffff 0xfffffffffff1ffff

def z82 : W := mkw 0xb88016504a0ab7fe 0x0bfff7fef90c36b6 0xffe07ff1fe3fffff 0xfffffffff98e3fff

def z83 : W := mkw 0x0048200020000200 0x0302800002804800 0x007ffe003ff8028a 0x030780000781f800

def z84 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x001f800e0001fc20 0xc2e00ffc067000f8

def z85 : W := mkw 0x0000104008000000 0x0011200000041200 0x00607ff1fe3e03cf 0x0119f000018e3f00

def z86 : W := mkw 0xb0dc77d97b2ab7ef 0x0b7ff15a33beffb6 0xf1ffffffffffffff 0xfffff1fe3fffffff

def z87 : W := mkw 0x254a2a0022902228 0xa30283806b806882 0x01807e0000380010 0x0101818039803800

def z88 : W := mkw 0x121551eb196519c7 0x10fd74628076972c 0x000001ffc0060d45 0x40f87060007e0738

def z89 : W := mkw 0x8858714929200251 0x033ba28c5a965a00 0x01807e01c0380010 0x0119819c398e3800

def z90 : W := mkw 0x90dc75d9792a97c7 0x0b7ff05a12bedf34 0x007ffffffffe0fcf 0x43fff07c07ffff38

def z91 : W := mkw 0x0058714929200241 0x033ba00002965a00 0x00007e01c0380000 0x01198000018e3800

def z92 : W := mkw 0x007b6d34a0018228 0xc3aa8fb407da48d8 0x007ffffffff9ffae 0xc3ff8ffc07fff8f8

def z93 : W := mkw 0x120500a210451986 0x10c454628060852c 0x007f81fe3fc60fcf 0x42e670600671c738

def z94 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z95 : W := mkw 0x80801450480a8400 0x08112018100c1210 0x00000001c0000000 0x0018001c000e0000

def z96 : W := mkw 0xed228a00069061b8 0xa0804feffd0120c3 0xff8000000001f030 0xbc000ffff80000c7

def z97 : W := mkw 0x88230c34800183f8 0xc3fffffedd4800d8 0xff8000000001fff0 0xc3fffffff80000f8

def z98 : W := mkw 0x88482000200003d0 0x03fff6eeda804800 0xfffffe003ff803fa 0x03ffffffff81f800

def z99 : W := mkw 0x0000000000000240 0x037fb28048000000 0xff800000000003f0 0x03ffff83f8000000

def z100 : W := mkw 0x30800610420ab42e 0x08000110210824b6 0x000000000001fc00 0xfc000000000000ff

def z101 : W := mkw 0x0000000000000180 0x00c4546280000000 0xfe000000000003e0 0x02e67e63c0000000

def z102 : W := mkw 0xa08012404a0a2400 0x0811200830043202 0x0180000000380010 0x0001800038003800

def z103 : W := mkw 0x004c208030000200 0x0346900002a0c900 0x007ffffe3ffe03cf 0x03e7f00007f1ff00

def z104 : W := mkw 0x00734d3480018228 0xc3280b9407da00d8 0x007fffffc001fc0c 0xc118019c07fe00f8

def z105 : W := mkw 0xda2580a214455996 0x10c45eefdc61856d 0xffff81fe3fc7ffff 0xfee67ffffe71c7ff

def z106 : W := mkw 0x0000000000000200 0x03aa86a448000000 0xff800000000003b0 0x03ff8ffff8000000

def z107 : W := mkw 0x0050410000000240 0x037fb00002920000 0x007fffffc00003cc 0x03fff00007fe0000

def z108 : W := mkw 0x8000000000000180 0x0011604a10000000 0xf1800000000000d0 0x0001f00238000000

def z109 : W := mkw 0xb88016504a0ab7fe 0x0b3be3de790c36b6 0xf1e07ff1fe3fffff 0xfd19f1fe398e3fff

def z110 : W := mkw 0x001451c919200041 0x007d300000369300 0x00607ffffe3e03cf 0x01f9f00001fe3f00

def z111 : W := mkw 0x0004008010000000 0x0044100000208100 0x000001fe00060145 0x00e0700000700700

def z112 : W := mkw 0x0000000000000000 0x0000028048000000 0xff80000000000030 0x00000f83f8000000

def z113 : W := mkw 0xf2f7dff6de4fffae 0xdbfd7fffb7ffb7ff 0xffffffffffffffff 0xffffffffffffffff

def z114 : W := mkw 0x0000041000008028 0x0000011001080090 0x00607ff1c001ff2c 0xc11801fc018e00f8

def z115 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0x00007fffc03e0145 0x01f9f00001fe3f00

def z116 : W := mkw 0x0000104008000000 0x0000000000041200 0x00607ff1fe3e000f 0x00000000018e3f00

def z117 : W := mkw 0x120500a210451986 0x10c454628060852c 0x000001fe00060d45 0x40e0706000700738

def z118 : W := mkw 0x456aa80024904200 0xa3028a814e814841 0x0e1f800001c00000 0x02060e01c601c000

def z119 : W := mkw 0x8000000000000180 0x00d5746a90000000 0xff800000000003f0 0x03fffffff8000000

def z120 : W := mkw 0x005c71c939200041 0x007d300002b6db00 0x007ffffffffe014f 0x00f8700007ffff00

def z121 : W := mkw 0x522580a214455bc6 0x13fffc638461856d 0xfe7f81fe3fc7ffef 0xfffffe63c671c7ff

def z122 : W := mkw 0x657aeb0026906228 0xa32a8b816f9368c3 0xfffffffffff9f3be 0xbfff8f83fffff8c7

def z123 : W := mkw 0x4522880004904000 0xa0000a814c010041 0x0e00000000000000 0x00000e01c0000000

def z124 : W := mkw 0x88734d34800183f8 0xc3fffffedfda00d8 0xffffffffc001fffc 0xc3fffffffffe00f8

def z125 : W := mkw 0xed6aaa00269063f8 0xa357fbcbff8168c3 0xfffffe003ff9f2fa 0xbf07ff83ff81f8c7

def z126 : W := mkw 0x005c71c939200241 0x037fb2804ab6db00 0xfffffffffffe03ff 0x03ffff83ffffff00

def z127 : W := mkw 0x00734d3480018228 0xc3000b9007da00d8 0x007fffffc001fe2c 0xc3000f8007fe00f8

def z128 : W := mkw 0x001555fd99218041 0x40fd3434007e9318 0x000001ffc0060d45 0x40f8707c007e0738

def z129 : W := mkw 0x0004008010000000 0x0000000000208100 0x007f81fe3fc6000f 0x000000000671c700

def z130 : W := mkw 0x6573cf348691e228 0xe3a80fb56fdb20db 0xffffffffc001ff3c 0xfff80ffffffe00ff

def z131 : W := mkw 0x00524d1480008228 0xc3280394039a0090 0x00007e01c0000000 0x0118019c018e0000

def z132 : W := mkw 0x657bef34a691e028 0xe000091127db68db 0x007ffffffff9fc0e 0xfc00000007fff8ff

def z133 : W := mkw 0x772da2a236d57986 0x30c6dc63ec61ed6f 0xffff81fe3fffffff 0xfee7fe63fe71ffff

def z134 : W := mkw 0xf0a096504e0af5ae 0x0811695b350d36f7 0xfffffff1ffffffff 0xff1fffffff8fffff

def z135 : W := mkw 0x005c71c939200241 0x033ba00002b6db00 0x007ffffffffe000f 0x0119800007ffff00

def z136 : W := mkw 0x8800000000000390 0x03a846eed8000000 0xff80000000000330 0x03f80ffff8000000

def z137 : W := mkw 0x527df1eb3d655807 0x1000080106f7df6d 0x007ffffffffffc0f 0xfc00000007ffffff

def z138 : W := mkw 0x88587149292003d1 0x03fff6eeda965a00 0xff807e01c03803f0 0x03fffffff98e3800

def z139 : W := mkw 0x65228a0006906228 0xa3028b816d0120c3 0xff8000000001f2b0 0xbf078f83f80000c7

def z140 : W := mkw 0x000c30c939200041 0x0057b0000024db00 0x00607ff1fffe03cf 0x011ff000018fff00

def z141 : W := mkw 0x885c71c939200251 0x037fb28c5ab6db00 0x01fffffffffe03df 0x03fff19c3fffff00

def z142 : W := mkw 0x457bed34a491c228 0xe3aa8fb54fdb48d9 0x0e7fffffc1c1ff2c 0xc3fe0ffdc7ffc0f8

def z143 : W := mkw 0xda21802204455bd6 0x13fffeefdc41046d 0xff8000000001fff0 0xfffffffff80000ff

def z144 : W := mkw 0x90801040480a1586 0x0811604a10041624 0x0000000000060041 0x0000700000000700

def z145 : W := mkw 0x004c30c939200241 0x0357b00002a4db00 0x007ffe003ffe02cb 0x0307f0000781ff00

def z146 : W := mkw 0x88000000000001d0 0x00d7f6eed8000000 0xff800000000000f0 0x0007fffff8000000

def z147 : W := mkw 0x8800000000000250 0x033ba28c58000000 0xff800000000002b0 0x031f8f9ff8000000

def z148 : W := mkw 0x456aa80024904200 0xa3028a814e814841 0xff9f800001c002b0 0x03078f83fe01c000

def z149 : W := mkw 0x657efbc93fb06029 0xa000090127b7fbc3 0x007ffffffffff00f 0xbc00000007ffffc7

def z150 : W := mkw 0x407cf1c93d204241 0x037fb80106b7db41 0xfe7ffffffffff3ef 0xbffffe03c7ffffc7

def z151 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0x001ffe0fc1f80000 0x03ff800007fff800

def z152 : W := mkw 0x0011453480018028 0x40a80534015a0098 0x00607fffc001ff2c 0xc1f801fc01fe00f8

def z153 : W := mkw 0xb08416d05a0ab5ae 0x0855715a312cb7b6 0xf1ffffffffffffff 0xfffff1fe3fffffff

def z154 : W := mkw 0x00630c3480018228 0xc3800fb407c800d8 0x007ffe000001fe28 0xc3000ffc078000f8

def z155 : W := mkw 0xb08c32c97b2a35c7 0x0857f04a3024ff26 0xf18000003ffe00d3 0x3c07f0023801ff07

def z156 : W := mkw 0x00734d3480018028 0xc000091007da00d8 0x007fffffc001ff2c 0xc11801fc07fe00f8

def z157 : W := mkw 0x88620800000003f8 0x83ffffeedf8000c0 0xfffffe000001f3f8 0x83ffffffff8000c0

def z158 : W := mkw 0xb8f35f74ca0bb7fe 0xcbfffffeffde36fe 0xfffffffffe3fffff 0xfffffffffffe3fff

def z159 : W := mkw 0x10801450480a9406 0x08000010000c1634 0x000001f1c0060c05 0x40000000000e0738

def z160 : W := mkw 0x1000000000001186 0x0000404200000424 0xf06001f03e07ffef 0xfc007062000007ff

def z161 : W := mkw 0x000c30c939200241 0x037fb0000024db00 0x000000003ffe03c3 0x03fff0000001ff00

def z162 : W := mkw 0x0021002000010000 0x00800c2004400048 0x007f81fe0001ff2c 0xc2e00e60067000f8

def z163 : W := mkw 0x4062880004004228 0x83000b81078100c1 0xfe7ffe003fc1f2aa 0xbf060f83c781c0c7

def z164 : W := mkw 0x0000000000000028 0x0000010001000080 0x00607e000001f228 0x81000180018000c0

def z165 : W := mkw 0xed08a200269063d0 0x23fff6eff8016803 0xff8000003ff803f2 0x3ffffffff801f807

def z166 : W := mkw 0x00734d3480018200 0xc3a80eb406da0058 0x001f81ffc0000d04 0x42f80e7c067e0038

def z167 : W := mkw 0x8000000000000380 0x0313e2ca58000000 0xff800000000003f0 0x031ffffff8000000

def z168 : W := mkw 0xf588b6506e9af5ae 0x2813e15b790d7eb7 0xffe07ff1ffffffff 0xfd1ff1fff98fffff

def z169 : W := mkw 0xb0a30e34c20bb5ae 0xc8804ffe354824fe 0xf18000000001fc30 0xfc000ffe380000ff

def z170 : W := mkw 0x88001040080003d0 0x03fff6eed8041200 0xffe07ff1fe3e03ff 0x03fffffff98e3f00

def z171 : W := mkw 0x0073492480010200 0xc3a80ea406d20048 0x001f800e00000000 0x02e00e0006700000

def z172 : W := mkw 0xa5ca3e506a9aa628 0xab13a3987b8c7a92 0x01807e01c0380010 0x0119819c398e3800

def z173 : W := mkw 0x0000000000000040 0x0057b00000000000 0x00000000000000c0 0x0007f00000000000

def z174 : W := mkw 0xb0800610420ab5ae 0x0800415a310824b6 0xf1e07ff1c001ff3c 0xfd1801fe398e00ff

def z175 : W := mkw 0xb8dc77d97b2ab7ff 0x0bfff7fefbbeffb6 0xffffffffffffffff 0xffffffffffffffff

def z176 : W := mkw 0xb0d25f54ca0ab7ae 0xcb3963de339e36b6 0xf1e07ff1fe3fffff 0xfd19f1fe398e3fff

def z177 : W := mkw 0x0000000000000200 0x0300028000000000 0x0000000000000220 0x03000f8000000000

def z178 : W := mkw 0x88114534800183d0 0x43fff6fed85a0018 0xff8001ffc0000ff4 0x43fffffff87e0038

def z179 : W := mkw 0xb0915774ca0bb5ae 0x48b9657e315e36be 0xf1e07ffffe3fffff 0xfdf9f1fe39fe3fff

def z180 : W := mkw 0x308012404a0a3406 0x0800000020043626 0x000000003e3e0003 0x3c00000000003f07

def z181 : W := mkw 0x1000000000001186 0x00c4546280000424 0xfe6001f03e07ffef 0xfee67e63c00007ff

def z182 : W := mkw 0x422580a214454800 0x10c41c2184618149 0x0e1f800e01c00000 0x02e60e01c671c000

def z183 : W := mkw 0xb0d057504a0ab7ae 0x0b39615a339e36b6 0xf1fffffffe3fffff 0xfff9f1fe3ffe3fff

def z184 : W := mkw 0x88000000000003d0 0x03bbe6eed8000000 0xff80000000000030 0x01198ffff8000000

def z185 : W := mkw 0x001451c919200041 0x007d300000369300 0x000001ffc0060145 0x00f87000007e0700

def z186 : W := mkw 0x881451c9192003d1 0x03fff6eed8369300 0xff8001ffc00603f5 0x03fffffff87e0700

def z187 : W := mkw 0x88734d34800183b8 0xc3a84ffedfda00d8 0xffffffffc001ff3c 0xc3f80ffffffe00f8

def z188 : W := mkw 0x005c71c939200001 0x0011200002b6db00 0x007ffffffffe03cf 0x0119f00007ffff00

def z189 : W := mkw 0x776baa2226d57bae 0xb382cfe3efc16cef 0xfffffe003ff9feba 0xff078fe3ff81f8ff

def z190 : W := mkw 0xa0f35f74ca0ba628 0xcbb92fbc37de32da 0x01ffffffc039ff3c 0xc3f98ffc3ffe38f8

def z191 : W := mkw 0x30dc77d97b2ab42f 0x0800011023beffb6 0x007ffffffffffc0f 0xfc00000007ffffff

def z192 : W := mkw 0x5277cdb69445dbae 0xd3ec5ff787fb85fd 0xfe7fffffffc7ffef 0xfffe7fffc7ffc7ff

def z193 : W := mkw 0x657aef14a690e228 0xe32a8b956f9b68d3 0xfffffe01fff9f2ba 0xbf1f8f9fff8ff8c7

def z194 : W := mkw 0xa08016504a0aa428 0x08112118310c3292 0x01e07ff1c039ff3c 0xc11981fc398e38f8

def z195 : W := mkw 0xda048082144459d6 0x1057f04bd8218525 0xff8000003fc600d3 0x3c07f003f801c707

def z196 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0xf1807e01c039fc30 0xfd1981fe398e38ff

def z197 : W := mkw 0x8000000000000180 0x0000404a10000000 0xf180000000000030 0x000001fe38000000

def z198 : W := mkw 0x5224808214445986 0x1044584384218565 0xfe7f80003fc7f2eb 0xbe067e03c601c7c7

def z199 : W := mkw 0x8800000000000190 0x0000404ad8000000 0xff80000000000010 0x00000003f8000000

def z200 : W := mkw 0xb0800610420ab5ae 0x0800415a310824b6 0xf18000000001fc30 0xfc0001fe380000ff

def z201 : W := mkw 0x00230c3480018028 0xc0000910054800d8 0x000000000001fc00 0xc0000000000000f8

def z202 : W := mkw 0x00734d3480018228 0xc328091007da00d8 0x007fffffc001ff0c 0xc3f8000007fe00f8

def z203 : W := mkw 0x007d71e939210241 0x03ffbc2006f6db48 0x007fffffffffffef 0xc3fffe6007fffff8

def z204 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0xf18001f1c007fd75 0xfc1871fe380e07ff

def z205 : W := mkw 0x8800000000000050 0x0013a00858000000 0x0180000000000010 0x0001800038000000

def z206 : W := mkw 0x522580a214455986 0x10c45c638461856d 0xfe0000003fc7fce3 0xfc067e63c001c7ff

def z207 : W := mkw 0x007e79c939200269 0x837fbb8007b6dbc0 0x007ffffffffff3ef 0x83ffff8007ffffc0

def z208 : W := mkw 0x0000000000000200 0x03a806a400000000 0x0000000000000320 0x03f80ffc00000000

def z209 : W := mkw 0x656aaa0026906028 0xa0000901278168c3 0x007ffe003ff9f00a 0xbc0000000781f8c7

def z210 : W := mkw 0x0000000000000000 0x00a8042400000000 0x0000000000000100 0x00f8007c00000000

def z211 : W := mkw 0x0000000000000180 0x00c4546280000000 0x0000000000000140 0x00e0706000000000

def z212 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0x0e00000000000140 0x02fe7e7dc0000000

def z213 : W := mkw 0x90f35d74c80b97ae 0xcbb96ffe17de16fc 0x007fffffc007ff6d 0xc3f87ffc07fe07f8

def z214 : W := mkw 0x308016504a0ab42e 0x08112110210c36b6 0x00607ff1fe3fffcf 0xfd19f000018e3fff

def z215 : W := mkw 0x0010451480008000 0x40280014001a0010 0x00000001c0000000 0x0018001c000e0000

def z216 : W := mkw 0x88000000000003d0 0x03fd76ee90000000 0x0000000000000360 0x03f87ffc00000000

def z217 : W := mkw 0x90801450480a95ae 0x0811615a110c16b4 0x00607ff1c007ff6d 0xc11871fc018e07f8

def z218 : W := mkw 0x8000000000000000 0x0011200810000000 0x0180000000000010 0x0119819c38000000

def z219 : W := mkw 0x526da0a234455b86 0x13c6dc6386e1cd6d 0xfe7ffffe3fffffef 0xffe7fe63c7f1ffff

def z220 : W := mkw 0x00734d3480018028 0xc0800fb407da00d8 0x007fffffc001fc2c 0xc0000ffc07fe00f8

def z221 : W := mkw 0x88000000000001d0 0x00fff46ed8000000 0xff800000000001d0 0x00fff07ff8000000

def z222 : W := mkw 0x122500a210451986 0x10c45c628460856c 0x007f81fe0007ff6d 0xc2e07e60067007f8

def z223 : W := mkw 0x0050410000000200 0x0328000002920000 0x00007e01c0000000 0x01180000018e0000

def z224 : W := mkw 0x8800000000000190 0x00c456eed8000000 0xff800000000003f0 0x02e67ffff8000000

def z225 : W := mkw 0x885c6189312003d1 0x03fff6eedab2c900 0xff9f800e01c003f0 0x03fffffffe71c000

def z226 : W := mkw 0x000410c919200041 0x0055300000249300 0x0000000000060041 0x0000700000000700

def z227 : W := mkw 0x12774db690459bae 0xd3ec5ff687fa85fc 0x007fffffc007ff6d 0xc3f87ffc07fe07f8

def z228 : W := mkw 0xb88016504a0ab5fe 0x08fd757eb10c36b6 0xf1e07ff1fe3fffff 0xfdf9f1fe398e3fff

def z229 : W := mkw 0x00334d3480018028 0xc0a80fb4055a00d8 0x000001ffc001fd24 0xc0f80ffc007e00f8

def z230 : W := mkw 0x656aaa0026906228 0xa3aa8fa56f8168c3 0xfffffe003ff9f3ba 0xbfff8fffff81f8c7

def z231 : W := mkw 0x657bef34a691e228 0xe3028b916fdb68db 0xfffffffffff9febe 0xff078f83fffff8ff

def z232 : W := mkw 0x1000000000001186 0x0000404200000424 0x000001f000060d45 0x4000706000000738

def z233 : W := mkw 0xf2a18632464ffdae 0x18804d7bb54924ff 0xff8000000001fc30 0xfc000ffff80000ff

def z234 : W := mkw 0x520cb0cb3d6459c7 0x1057f0438025df25 0xfe0000003ffe00c3 0x3c07f003c001ff07

def z235 : W := mkw 0x657efbc93fb06269 0xa37fbb816fb7fbc3 0xfffffffffffff3ff 0xbfffff83ffffffc7

def z236 : W := mkw 0xb08012404a0a3586 0x0811604a30043626 0xf1e001f03e3fffff 0xfc01f06238003fff

def z237 : W := mkw 0x308016504a0ab42e 0x08000110210c36b6 0x00607ff1fe3fff2f 0xfd1801fc018e3fff

def z238 : W := mkw 0x5221802204455806 0x100008010441046d 0x000000000001fc00 0xfc000000000000ff

def z239 : W := mkw 0x0000000000000380 0x03ec56e680000000 0xfe000000000003e0 0x03fe7fffc0000000

def z240 : W := mkw 0x0021002000010180 0x00c45c6284400048 0xfe7f81fe0001ffec 0xc2e67e63c67000f8

def z241 : W := mkw 0x88000000000001d0 0x00fd76eed8000000 0xff80000000000170 0x00f87ffff8000000

def z242 : W := mkw 0xf5a29e504e9af5ae 0xa8116bdb7d0d36f7 0xffe07ff1fe3fffff 0xfd19fffff98e3fff

def z243 : W := mkw 0x0062080000000228 0x83000b80078000c0 0x007ffe000001f228 0x83000f80078000c0

def z244 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0x00607ff1fe3ffd4f 0xfc18707c018e3fff

def z245 : W := mkw 0x20734f348201a228 0xc3a80fb427da20da 0xf1fffffffe39ffbe 0xfff98ffe3ffe38ff

def z246 : W := mkw 0x5275c1a214455b86 0x13ec5c6386f3856d 0xfe7fffffffc7ffef 0xfffe7e63c7ffc7ff

def z247 : W := mkw 0x0050451000008228 0x03280110039a0090 0x007fffffc001ff2c 0xc3f801fc07fe00f8

def z248 : W := mkw 0x422580a214454800 0x10c41c2184618149 0x0e7f81fe01c1ff2c 0xc2e60e61c671c0f8

def z249 : W := mkw 0x120500a210451986 0x10c454628060852c 0xf06001fe3e07ffef 0xfce07062007007ff

def z250 : W := mkw 0x0000104008000000 0x0011200000041200 0x00007e01c0380000 0x01198000018e3800

def z251 : W := mkw 0x4024808014004000 0x0044180104218141 0xfe7f81fe3fc7f3ef 0xbee67e03c671c7c7

def z252 : W := mkw 0x0001002000010000 0x0080042000400008 0x000001fe00000d04 0x40e0006000700038

def z253 : W := mkw 0xa88016504a0aa678 0x0b3ba39c790c3292 0x01807e01c0380010 0x0119819c398e3800

def z254 : W := mkw 0x65628a0006906228 0xa3000b816f8120c3 0xfffffe000001f238 0xbf000f83ff8000c7

def z255 : W := mkw 0x2508220022902000 0x2002800068006802 0x0180000000380010 0x0001800038003800

def z256 : W := mkw 0x0011453480018000 0x40000010005a0018 0x000001ffc0000c04 0x40000000007e0038

def z257 : W := mkw 0x657bef34a691e228 0xe3a80fb527db68db 0x007ffffffff9ff2e 0xfff80ffc07fff8ff

def z258 : W := mkw 0x0073492480010228 0xc3a80fa407d200c8 0x007ffe0e0001f228 0x83e00f8007f000c0

def z259 : W := mkw 0x00524d1480008228 0xc3a807b4039a0090 0x00007e01c0000320 0x03f80ffc018e0000

def z260 : W := mkw 0x422580a214454800 0x10c41c2184618149 0x0e7f81fe3fc603cf 0x02e67e01c671c700

def z261 : W := mkw 0x656aaa0026906028 0xa0000901278168c3 0xfe7ffe003ff9f2aa 0xbe060e03c781f8c7

def z262 : W := mkw 0x0000000000000000 0x0000000000000000 0x007f81fe0000030c 0x02e0000006700000

def z263 : W := mkw 0x0000000000000200 0x0328028400000000 0x0000000000000000 0x0118019c00000000

def z264 : W := mkw 0x5a2580a214455bd6 0x13eedee7cc61856d 0xfe7f81fe3fc7ffef 0xfee67e63c671c7ff

def z265 : W := mkw 0x881451c9192001d1 0x00fd746e90369300 0x000001ffc0060145 0x00f8707c007e0700

def z266 : W := mkw 0x656aba402e906228 0xa313ab816f857ac3 0xfffffff1fffff3ff 0xbf1fff83ff8fffc7

def z267 : W := mkw 0x2000020002002028 0x0000010021002082 0x00607e003e39f00a 0xbc000000018038c7

def z268 : W := mkw 0x0000041000008228 0x03a807b401080090 0x00607ff1c001ff2c 0xc3f80ffc018e00f8

def z269 : W := mkw 0x007f7dfdb9218269 0xc3ffbfb407fedbd8 0x007fffffffffffef 0xc3fffffc07fffff8

def z270 : W := mkw 0x007f6dbdb1218269 0xc3ee9fb407fac9d8 0x007fffffc1c1ff2c 0xc3fe0ffc07ffc0f8

def z271 : W := mkw 0x88210020000103d0 0x03fffeeedc400048 0xffff81fe0001fffc 0xc3fffffffe7000f8

def z272 : W := mkw 0x6528a20026906000 0x200288016c016843 0xffff80003ff9f2ba 0xbe078e03fe01f8c7

def z273 : W := mkw 0x0062080000000200 0x83000a8006800040 0x001f800000000000 0x02000e0006000000

def z274 : W := mkw 0x8800000000000250 0x037fb28c58000000 0x01800000000003d0 0x03fff19c38000000

def z275 : W := mkw 0x887f7dfdb92183f9 0xc3fffffedffedbd8 0xffffffffffffffff 0xc3fffffffffffff8

def z276 : W := mkw 0x5204808214445986 0x10c4546380218525 0xfe0000003fc603e3 0x3ee67e63c001c707

def z277 : W := mkw 0xda2580a2144559d6 0x10d7fc6bdc61856d 0xffff81fe3fc7ffff 0xfee7fe63fe71c7ff

def z278 : W := mkw 0x5277cdb69445da2e 0xd3a80fb507fb85fd 0x007fffffffc7ff2f 0xfff80ffc07ffc7ff

def z279 : W := mkw 0xed08a200269061d0 0x2057f04bf8016803 0xff8000003ff800d2 0x3c07f003f801f807

def z280 : W := mkw 0x2048220022002228 0x0302810023806882 0xf1fffe003ff9f2ba 0xbf0781823f81f8c7

def z281 : W := mkw 0xa08016504a0aa428 0x08112118310c3292 0x01807e01c0380010 0x0119819c398e3800

def z282 : W := mkw 0xda77cdb69445dbfe 0xd3ffffffdffb85fd 0xffffffffffc7ffff 0xffffffffffffc7ff

def z283 : W := mkw 0x90915574c80b9586 0x48b9647e105e163c 0x000001ffc0060d45 0x40f8707c007e0738

def z284 : W := mkw 0x000410c018000000 0x0055300000249300 0x007ffffffffe03cf 0x03fff00007ffff00

def z285 : W := mkw 0x120500a210451986 0x10c454628060852c 0xfe0001fe00060fe5 0x42e67e63c0700738

def z286 : W := mkw 0x5200800204445986 0x1000404380010425 0xfe00000000000000 0x3c000003c0000007

def z287 : W := mkw 0xa0000200020021a8 0x0011614a31002082 0xf1e07e003e39f3fa 0xbd19f1fe398038c7

def z288 : W := mkw 0x656aaa0026906268 0xa37fbb816f8168c3 0xfffffe003ff9f3fa 0xbfffff83ff81f8c7

def z289 : W := mkw 0x770ca28236d47986 0x3046d043e821ed27 0xff8000003ffe00d3 0x3c07f003f801ff07

def z290 : W := mkw 0x005c71c939200001 0x0044100002b6db00 0x007ffffffffe03cf 0x02e6700007ffff00

def z291 : W := mkw 0xb0c836506a0ab7ae 0x0b13e15a338c7eb6 0xf1fffff1ffffffff 0xff1ff1fe3f8fffff

def z292 : W := mkw 0x657efbc93fb06229 0xa3028b816fb7fbc3 0xfffffffffffff2bf 0xbf078f83ffffffc7

def z293 : W := mkw 0x65228a0006906028 0xa0000b816d0120c3 0xffe07e003e39f2ba 0xbd018f83f98038c7

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0x006001f00001ff2c 0xc0000060000000f8

def z295 : W := mkw 0x5204808214445986 0x1044504380218525 0xfe6001f03fc7ffef 0xfc067063c001c7ff

def z296 : W := mkw 0x656aaa0026906200 0xa3028a816e816843 0xff9f80003ff80092 0x3e078e03fe01f807

def z297 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe000000000002a0 0x02060e03c0000000

def z298 : W := mkw 0x777ffbeb3ff57bef 0xb3ffffe3eff7ffef 0xffffffffffffffff 0xffffffe3ffffffff

def z299 : W := mkw 0x88000000000003d0 0x0357f2cad8000000 0xff800000000002f0 0x0307ff83f8000000

def z300 : W := mkw 0x257b6f34a291a228 0xe3aa8fb46fda68da 0x01ffffffc039ff3c 0xc3f98ffc3ffe38f8

def z301 : W := mkw 0x656aae102690e228 0xa3028b916f8968d3 0xfffffff1fff9ffbe 0xff1f8fffff8ff8ff

def z302 : W := mkw 0x001451c919200001 0x0000000000369300 0x000001ffc0060005 0x00000000007e0700

def z303 : W := mkw 0x2000020002002000 0x0000000020002002 0xf18000003e380092 0x3c01800238003807

def z304 : W := mkw 0x4508a00024904000 0x2002800148014801 0x0e00000001c00000 0x00060001c001c000

def z305 : W := mkw 0xda7df1eb3d655bd7 0x13fffeefdef7df6d 0xffffffffffffffff 0xffffffffffffffff

def z306 : W := mkw 0x88000000000001d0 0x0055704a90000000 0x0000000000000040 0x0000700000000000

def z307 : W := mkw 0x005451c919200241 0x037d300002b69300 0x007fffffc006034d 0x03f8700007fe0700

def z308 : W := mkw 0x308016504a0ab5ae 0x08004152210c36b6 0xf0607ff1fe3fffef 0xfc007062018e3fff

def z309 : W := mkw 0x6508a20026906000 0x2000000120016803 0x000000003ff80002 0x3c0000000001f807

def z310 : W := mkw 0x657eeb8937b06269 0xa36e9b816fb3e9c3 0xfffffe0e3ff9f2ba 0xbfe78f83fff1f8c7

def z311 : W := mkw 0x00734d3480018028 0xc0a80d3407da00d8 0x007fffffc001fd0c 0xc0f8007c07fe00f8

def z312 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0xf1807e01fe3e00d3 0x3d19f19e398e3f07

def z313 : W := mkw 0x0000041000008028 0x0000011001080090 0x000000000001fc20 0xc00001fc000000f8

def z314 : W := mkw 0x007b7d7da9218269 0xc3bbafb407de5ad8 0x007fffffc039ff2c 0xc3f98ffc07fe38f8

def z315 : W := mkw 0x0051453480018200 0x43a8043402da0018 0x007fffffc0000f0c 0x43f8007c07fe0038

def z316 : W := mkw 0x0004008010000180 0x00c4546280208100 0xfe7f81fe3fc603ef 0x02e67e63c671c700

def z317 : W := mkw 0x0011453480018200 0x43a806b4005a0018 0x000001ffc0000f24 0x43f80ffc007e0038

def z318 : W := mkw 0x457ee98935b04241 0xa36e9a814eb3c941 0x0e1f800e01c00000 0x02e60e01c671c000

def z319 : W := mkw 0x6508a20026906200 0x2302828168016803 0xff8000003ff802b2 0x3f078f83f801f807

def z320 : W := mkw 0x6508a20026906028 0x2002810169016883 0xffe07e003ff9f2ba 0xbd078183f981f8c7

def z321 : W := mkw 0x255e7bc93bb02269 0xa37fb3806bb6fb82 0x01fffffffffe03df 0x03fff1803fffff00

def z322 : W := mkw 0x007f7dfdb9218029 0xc000091007fedbd8 0x007ffffffffffc0f 0xc000000007fffff8

def z323 : W := mkw 0xb09457d95b2ab5ef 0x087d715a313eb7b6 0xf1e07ffffe3fffff 0xfdf9f1fe39fe3fff

def z324 : W := mkw 0x52238c368445d9ae 0xd0804ff7854904fd 0xfe0000000001fc20 0xfc000fffc00000ff

def z325 : W := mkw 0xed7bef34a691e3f8 0xe3ffffffffdb68db 0xfffffffffff9fffe 0xfffffffffffff8ff

def z326 : W := mkw 0x007f7dfdb9218269 0xc37fb91007fedbd8 0x007fffffffffffcf 0xc3fff00007fffff8

def z327 : W := mkw 0xa0d25f54ca0aa628 0xcb39239c339e3292 0x01807e01c0380010 0x0119819c398e3800

def z328 : W := mkw 0x0021043000018028 0x00800d30054800d8 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z329 : W := mkw 0x1201002200451986 0x108044628040042c 0x0000000000000c00 0x4000006000000038

def z330 : W := mkw 0x005d75fdb9218241 0x43ffb43402fedb18 0x007ffffffffe0fcf 0x43fff07c07ffff38

def z331 : W := mkw 0x1000000000001006 0x0000000000000424 0x006001f03e07fc0f 0xfc000000000007ff

def z332 : W := mkw 0x1000000000001186 0x0000404200000424 0xf00000003e0600c3 0x3c00700200000707

def z333 : W := mkw 0x4a2580a214454a50 0x13ee9ea5cc618149 0x0e1f800e01c00000 0x02e60e01c671c000

def z334 : W := mkw 0x88734d3480018278 0xc3bbafbc5fda00d8 0x01ffffffc001ff3c 0xc3f98ffc3ffe00f8

def z335 : W := mkw 0xa0800610420aa428 0x0800011831082092 0x0180000000000010 0x0000019c38000000

def z336 : W := mkw 0x656baa2026916228 0xa3828fa16fc168cb 0xfffffffe3ff9ffbe 0xffe78fe3fff1f8ff

def z337 : W := mkw 0x2000020002002228 0x0302838069002082 0xffe07e003e39f2ba 0xbf078f83f98038c7

def z338 : W := mkw 0x88040080100003d0 0x03fff6eed8208100 0xffff81fe3fc603ff 0x03fffffffe71c700

def z339 : W := mkw 0x0000041000008028 0x0000011001080090 0x00607ff1c001fc0c 0xc0000000018e00f8

def z340 : W := mkw 0xfdeabe506e9af7fe 0xabffffffff8d7ef7 0xfffffff1ffffffff 0xffffffffff8fffff

def z341 : W := mkw 0x652aaa0026906028 0xa0028b816d0168c3 0xff8000003ff9f0b2 0xbc078f83f801f8c7

def z342 : W := mkw 0x4020800004004180 0x00c45c6384010041 0xfe7f80003fc1f3ea 0xbee67e63c601c0c7

def z343 : W := mkw 0x776faaa236d57a2e 0xb3028b816fe1edef 0xfffffffe3ffffebf 0xff078f83fff1ffff

def z344 : W := mkw 0x422580a214454800 0x10c41c2184618149 0xfe7f800e3fc1f2aa 0xbee60e03c671c0c7

def z345 : W := mkw 0x200006100200a028 0x0000011021082092 0xf1e07ff1fe39ffbe 0xfd1981fe398e38ff

def z346 : W := mkw 0x0004008010000000 0x0044100000208100 0x001f800e01c00000 0x02e600000671c000

def z347 : W := mkw 0xb88016504a0ab5be 0x089167fef90c36b6 0xffe07ff1fe3fffff 0xfd19fffff98e3fff

def z348 : W := mkw 0x00734d34800183a8 0xc3ec5ff687da00d8 0xfe7fffffc001ffec 0xc3fe7fffc7fe00f8

def z349 : W := mkw 0x000c208931200041 0x004690000020c900 0x0000000001c00000 0x000600000001c000

def z350 : W := mkw 0x4068a00024004200 0x0302880106814841 0xfe7ffe003ff9f2aa 0xbf078e03c781f8c7

def z351 : W := mkw 0x001451c919200241 0x037fb00000369300 0x000001ffc00603c5 0x03fff000007e0700

def z352 : W := mkw 0x0052490480000200 0xc328028402920000 0x0000000000000000 0x0000000000000000

def z353 : W := mkw 0x00620c1000008228 0x83000b90078800d0 0x007ffff1c001ff2c 0xc3180ffc078e00f8

def z354 : W := mkw 0x005a7d5da9208269 0xc33ba394039e5a90 0x00007e01c0380000 0x0119819c018e3800

def z355 : W := mkw 0x65228a0006906028 0xa0000901250120c3 0x000000000001f000 0xbc000000000000c7

def z356 : W := mkw 0x007f7dfdb9218229 0xc3a80fb407fedbd8 0x007fffffffffff2f 0xc3f80ffc07fffff8

def z357 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000320 0x011801fc00000000

def z358 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0x001f81ffc1c60145 0x02fe7000067fc700

def z359 : W := mkw 0x88000000000003d0 0x03eed6eed8000000 0xff80000000000030 0x02e60ffff8000000

def z360 : W := mkw 0x75eabe506e9af42e 0xa8000911278d7ef7 0x007ffff1fffffc0f 0xfc000000078fffff

def z361 : W := mkw 0x65238e348691e028 0xe0800fb56d4920db 0xff8000000001fc30 0xfc000ffff80000ff

def z362 : W := mkw 0x308016504a0ab42e 0x08000110210c36b6 0xf1e07ff1fe3ffebf 0xfd018182398e3fff

def z363 : W := mkw 0x005c71c939200041 0x0057b00002b6db00 0x007ffffffffe00cf 0x0007f00007ffff00

def z364 : W := mkw 0x5277c9a694455b86 0xd3ec5ee786f3856d 0xfe7f81fe3fc7ffef 0xfee67e63c671c7ff

def z365 : W := mkw 0x10000410000091ae 0x00004152010804b4 0xf0607ff1fe07ffef 0xfd1871fe018e07ff

def z366 : W := mkw 0x88000000000001d0 0x0057f04ad8000000 0xff800000000003f0 0x011ff1fff8000000

def z367 : W := mkw 0x00734d3480018228 0xc3aa8fb44fda00d8 0xffffffffc001ffbc 0xc3ff8ffffffe00f8

def z368 : W := mkw 0xb08016504a0ab7ae 0x0bb967fe310c36b6 0xf1e07ff1fe3fffff 0xfff9fffe398e3fff

def z369 : W := mkw 0x88504100000003d0 0x03fff6eeda920000 0xffffffffc00003fc 0x03fffffffffe0000

def z370 : W := mkw 0x88000000000003d0 0x03fff46e90000000 0x00000000000003c0 0x03fff07c00000000

def z371 : W := mkw 0xb0f34f34c20bb7ae 0xcba84ffe37da24fe 0xf1ffffffc001ff3c 0xfff80ffe3ffe00ff

def z372 : W := mkw 0x4277c9a694454a00 0xd3ec1ea586f38149 0x0e1f800e01c00000 0x02e60e01c671c000

def z373 : W := mkw 0x001c71c939200041 0x007fb0000036db00 0x000001fffffe01c7 0x00fff000007fff00

def z374 : W := mkw 0x655cf3c93fb06241 0x237fb0016ab7fb03 0xfffffffffffe03df 0x3ffff003ffffff07

def z375 : W := mkw 0x88230c34800181b8 0xc0804ffedd4800d8 0xff8000000001fc30 0xc0000ffff80000f8

def z376 : W := mkw 0x8800000000000250 0x03ffb6acd8000000 0x0f80000000000010 0x03ff8f9df8000000

def z377 : W := mkw 0xf588b2406e9a7586 0x2813e04b78057e27 0xff8000003ffe00d3 0x3c07f003f801ff07

def z378 : W := mkw 0x30dc77d97b2ab66f 0x0b7fb11023beffb6 0x007fffffffffffcf 0xfffff00007ffffff

def z379 : W := mkw 0x0000000000000000 0x0000000000000000 0x00607ff1c000030c 0x01180000018e0000

def z380 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0x001f800e3ffe00c3 0x02e7f0000671ff00

def z381 : W := mkw 0x0000104008000240 0x037fb00000041200 0x00607ff1fe3e03cf 0x03fff000018e3f00

def z382 : W := mkw 0xf2a196724e4ffdae 0x18916d7bb54d36ff 0xffe07ff1fe3fffff 0xfd19fffff98e3fff

def z383 : W := mkw 0x0800000000000050 0x00469000c8000000 0x0e00000000000000 0x00060001c0000000

def z384 : W := mkw 0xb08012404a0a3586 0x0811604a30043626 0xf18000003e3e03f3 0x3d19f1fe38003f07

def z385 : W := mkw 0x0000000000000380 0x03c6d6e2c8000000 0xff800000000003f0 0x03e7ffe3f8000000

def z386 : W := mkw 0x88000000000003d0 0x037ff04ad8000000 0xff800000000003d0 0x03fff003f8000000

def z387 : W := mkw 0xf2fdf7fb7f6fffef 0x1bfffd7bb7ffffff 0xffffffffffffffff 0xffffffffffffffff

def z388 : W := mkw 0xf5eaae10669af7ae 0xab02cbdb7f896cf7 0xfffffe003ff9feba 0xff078fffff81f8ff

def z389 : W := mkw 0x0004008010000240 0x037fb00000208100 0x007f81fe3fc603cf 0x03fff0000671c700

def z390 : W := mkw 0x457ef9c93db04241 0xa37fba814eb7db41 0x0e7ffffffffe03cf 0x03fffe01c7ffff00

def z391 : W := mkw 0x0000000000000200 0x0328000000000000 0x0000000000000300 0x03f8000000000000

def z392 : W := mkw 0x007f69adb1210241 0xc3ee9ea406f2c948 0x001f800e01c00000 0x02e60e000671c000

def z393 : W := mkw 0xb88016504a0ab5fe 0x0857f15af90c36b6 0xffe07ff1fe3fffff 0xfd1ff1fff98e3fff

def z394 : W := mkw 0xb28516f25a4fbdae 0x18d5757ab16cb7be 0xf1e07ffffe3fffff 0xfdf9f1fe39fe3fff

def z395 : W := mkw 0x522580a214455986 0x10c45c638461856d 0x007f81fe3fc7fd4f 0xfce070600671c7ff

def z396 : W := mkw 0x0000000000000180 0x0080446280000000 0xfe00000000000020 0x00000e63c0000000

def z397 : W := mkw 0x98000000000013d6 0x03fff6eed8000424 0xffe001f03e07ffff 0xfffffffff80007ff

def z398 : W := mkw 0x88734d34800183f8 0xc3fd7ffe97da00d8 0x007fffffc001ff6c 0xc3f87ffc07fe00f8

def z399 : W := mkw 0x5204808214445806 0x1000000100218525 0x000000003fc60003 0x3c0000000001c707

def z400 : W := mkw 0x88000000000001d0 0x00fd746e90000000 0xf1800000000003f0 0x01f9f1fe38000000

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0x00607e003e38028a 0x0101800001803800

def z402 : W := mkw 0x0000041000008028 0x0000011001080090 0x00007e01c0000000 0x0118019c018e0000

def z403 : W := mkw 0x527ffdffbd65dbef 0xd3fffff787ffdffd 0xfe7fffffffffffef 0xffffffffc7ffffff

def z404 : W := mkw 0xb08c36d97b2ab5ef 0x0857f15a312cffb6 0xf1e07ff1ffffffff 0xfd1ff1fe398fffff

def z405 : W := mkw 0x0048200020000200 0x0302800002804800 0x00007e0000380000 0x0101800001803800

def z406 : W := mkw 0x00230c3480018028 0xc0800fb4054800d8 0x00607ff1c001ff2c 0xc1180ffc018e00f8

def z407 : W := mkw 0x120500a210451806 0x100000000060852c 0x000001fe00060c05 0x4000000000700738

def z408 : W := mkw 0x0048200020000000 0x0000000002804800 0x007ffe003ff8000a 0x000000000781f800

def z409 : W := mkw 0x0800000000000010 0x008006a4c8000000 0x0e00000000000000 0x00000e01c0000000

def z410 : W := mkw 0x0000000000000200 0x0302828048000000 0x0180000000000010 0x0101818038000000

def z411 : W := mkw 0x2000020002002028 0x0000010021002082 0x01807e0000380010 0x0101818039803800

def z412 : W := mkw 0xda2580a2144559d6 0x10fd7c6f9461856d 0xfe7f81fe3fc7ffef 0xfefe7e7fc671c7ff

def z413 : W := mkw 0x0800000000000250 0x03ffb6a4c8000000 0x0e000000000003c0 0x03fffe01c0000000

def z414 : W := mkw 0x9a0500a210451bd6 0x13fff6eed860852c 0xff8001fe00060ff5 0x43fffffff8700738

def z415 : W := mkw 0x054a280020900200 0xa30282804a804800 0x0000000000000000 0x0000000000000000

def z416 : W := mkw 0x0050514008000200 0x0339200002961200 0x007ffffffe3e03cf 0x03f9f00007fe3f00

def z417 : W := mkw 0x0001043480018000 0x4080043400480018 0x0000000000000c00 0x4000007c00000038

def z418 : W := mkw 0xed228a00069063f8 0xa3ffffeffd0120c3 0xff8000000001f3f0 0xbffffffff80000c7

def z419 : W := mkw 0x5221802204455986 0x10804c638441046d 0xfe7f81fe0001ff2c 0xfee00e63c67000ff

def z420 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x00007e01c001fc20 0xc1180ffc018e00f8

def z421 : W := mkw 0xb0800610420ab5ae 0x0800415a310824b6 0xf1e001f03e07ffff 0xfc0071fe380007ff

def z422 : W := mkw 0xf5feffd97fbaf7ef 0xab7ffbdb7fbffff7 0xffffffffffffffff 0xffffffffffffffff

def z423 : W := mkw 0x00230c3480018228 0xc3a80fb4054800d8 0x000000000001ff20 0xc3f80ffc000000f8

def z424 : W := mkw 0x657ffffdbfb1e269 0xe3ffbfb56ffffbdb 0xffffffffffffffff 0xffffffffffffffff

def z425 : W := mkw 0xf5fbff74ee9bf7ae 0xebbbefff7fdf7eff 0xffffffffffffffff 0xffffffffffffffff

def z426 : W := mkw 0xf2a596f25e4ffdae 0x1811695b356db7ff 0xf1ffffffffffffff 0xfd19f1fe3fffffff

def z427 : W := mkw 0x4277cdb69445ca28 0xd3ec1fb587fb81d9 0x0e7fffffc1c1ff2c 0xc3fe0ffdc7ffc0f8

def z428 : W := mkw 0x422580a214454980 0x10c45c6384618149 0xfe1f800e01c003e0 0x02e67e63c671c000

def z429 : W := mkw 0x6548a20026906200 0x230280016a816803 0xfffffe003ff8029a 0x3f078003ff81f807

def z430 : W := mkw 0xb08012404a0a3586 0x0811604a30043626 0xf1e07ff1fe3e03df 0x3d19f002398e3f07

def z431 : W := mkw 0x656aaa0026906028 0xa0000b816f8168c3 0xfffffe003ff9f03a 0xbc000f83ff81f8c7

def z432 : W := mkw 0x0800000000000250 0x03ee96a4c8000000 0x0e00000000000320 0x03fe0ffdc0000000

def z433 : W := mkw 0x77278aa216d579ae 0xb0c45fe3ed61a5ef 0xffff81fe3fc7ffff 0xfee67fe3fe71c7ff

def z434 : W := mkw 0xed6aaa00269063b8 0xa382cfefff8168c3 0xfffffe003ff9f2ba 0xbf078fffff81f8c7

def z435 : W := mkw 0x255a6f14a290a228 0xe32a83946b9a6892 0x01807e01c0380010 0x0119819c398e3800

def z436 : W := mkw 0xb08012404a0a35ae 0x0811614a310436a6 0xf1e07e003e3ff2fb 0xbd01f18239803fc7

def z437 : W := mkw 0x90801450480a9586 0x0811605a100c1634 0xf18001f1c0060ff5 0x4119f1fe380e0738

def z438 : W := mkw 0x002500a010010000 0x00c41c2004608148 0x007f81fe3fc7ffef 0xc2e67e600671c7f8

def z439 : W := mkw 0xb0d877596b2ab7ef 0x0b3be15a339e7eb6 0xf1e07ff1fe3fffff 0xfd19f1fe398e3fff

def z440 : W := mkw 0x88524d14800083f8 0xc3fff7fedb9a0090 0xff807e01c00003f0 0x03fffffff98e0000

def z441 : W := mkw 0x0000000000000000 0x0000000000000000 0xf06000003e01f2aa 0xbc000002000000c7

def z442 : W := mkw 0x0048304028000200 0x0313a00002845a00 0x007ffff1fffe03cf 0x031ff000078fff00

def z443 : W := mkw 0xca2580a214454bd0 0x13fffeefdc618149 0xff9f800e01c003f0 0x03fffffffe71c000

def z444 : W := mkw 0x4221802204454800 0x10800c2184410049 0x0e00000000000000 0x00000e01c0000000

def z445 : W := mkw 0x0000104008000000 0x0011200000041200 0x000001f1c0060145 0x00187000000e0700

def z446 : W := mkw 0x5235c5b69445d986 0x50ec5c77847b857d 0xfe7f81ffffc7ffef 0xfefe7e7fc67fc7ff

def z447 : W := mkw 0x005c71c939200241 0x03ffb6a402b6db00 0x007ffffffffe03ef 0x03fffffc07ffff00

def z448 : W := mkw 0x88000410000083f8 0x03fff7fed9080090 0xffe07ff1c001fffc 0xc3fffffff98e00f8

def z449 : W := mkw 0xc8208000040043d0 0x03fffeefdc010041 0xffff80003fc1f3fa 0xbffffffffe01c0c7

def z450 : W := mkw 0x72a596f25e4ffdae 0x18c45d73a56db7ff 0xfe7fffffffffffef 0xfee67e63c7ffffff

def z451 : W := mkw 0x650cb2c93fb06041 0x2057b0016825fb03 0xff8000003ffe00d3 0x3c07f003f801ff07

def z452 : W := mkw 0x526788a214455bae 0x93c45fe387e185ed 0xfe7ffffe3fc7ffef 0xffe67fe3c7f1c7ff

def z453 : W := mkw 0x656aaa0026906028 0xa00289016f8168c3 0xfffffe003ff9f09a 0xbc078003ff81f8c7

def z454 : W := mkw 0xb8800610420ab5be 0x088047fef90824b6 0xff8000000001fc30 0xfc000ffff80000ff

def z455 : W := mkw 0x520580a214455986 0x10c454638061852d 0xfe0001fe3fc60dc7 0x7ce67063c071c73f

def z456 : W := mkw 0xb08016504a0ab586 0x0811605a300c3636 0xf18001f1fe3e0dd7 0x7c19f07e380e3f3f

def z457 : W := mkw 0x88524d1480008278 0xc33ba39c5b9a0090 0x01807e01c0000010 0x0119819c398e0000

def z458 : W := mkw 0x522590e21c455986 0x10d57c638465976d 0xfe7fffffffffffef 0xfffffe63c7ffffff

def z459 : W := mkw 0x0000000000000000 0x00c4142080000000 0x0e00000000000000 0x02e60e01c0000000

def z460 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0x0f9ffe0001f80010 0x03078f81ff81f800

def z461 : W := mkw 0x8800000000000190 0x0080446e90000000 0x0000000000000000 0x0000007c00000000

def z462 : W := mkw 0x522580a214455b86 0x13c6dee3cc61856d 0xffff81fe3fc7ffff 0xffe7ffe3fe71c7ff

def z463 : W := mkw 0x90801450480a9586 0x0811605a100c1634 0x00607ff1fe3e0fcf 0x4119f07c018e3f38

def z464 : W := mkw 0x88114534800181d0 0x40fd747e905a0018 0x000001ffc0000d44 0x40f8707c007e0038

def z465 : W := mkw 0x0000104008000000 0x0011200000041200 0x000000003e3e00c3 0x0001f00000003f00

def z466 : W := mkw 0x00534d3480018228 0xc3a807b403da0098 0x00007fffc0000d04 0x41f801fc01fe0038

def z467 : W := mkw 0x1021002000011186 0x00804c620440046c 0xf07f81fe3e07ffef 0xfee07e62067007ff

def z468 : W := mkw 0x00774db490018228 0xc3ec1fb407fa81d8 0x007fffffffc7ffef 0xc3fe7ffc07ffc7f8

def z469 : W := mkw 0x30f35f74ca0bb42e 0xc800091027de36fe 0x007ffffffe3ffc0f 0xfc00000007fe3fff

def z470 : W := mkw 0x4020800004004000 0x0000080104010041 0x007f80003fc1f00a 0xbc0000000601c0c7

def z471 : W := mkw 0x006a280020000228 0x83028b80078048c0 0x007ffe003ff9f2aa 0x83078f800781f8c0

def z472 : W := mkw 0x085c71c939200251 0x03ffb6a4cab6db00 0x0e7ffffffffe03cf 0x03fffe01c7ffff00

def z473 : W := mkw 0x880c30c9392001d1 0x0057f04ad824db00 0xff8000003ffe00d3 0x0007f003f801ff00

def z474 : W := mkw 0x0058610020000200 0x032a800002924800 0x007ffffffff8038e 0x03ff800007fff800

def z475 : W := mkw 0x007f79edb9210241 0xc3ffbea406f6db48 0x007ffffffffe03cf 0x03fffe0007ffff00

def z476 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xff800000000000d0 0x02e7fe03f8000000

def z477 : W := mkw 0x005c618931200241 0x036e900002b2c900 0x007fffffc1c0030c 0x03fe000007ffc000

def z478 : W := mkw 0x88000000000003d0 0x033be2ce58000000 0xf1800000000003f0 0x0119f1fe38000000

def z479 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0x0e7ffe003ff9f00a 0xbe060e01c781f8c7

def z480 : W := mkw 0x656aaa0026906028 0xa0000901278168c3 0xf1fffe003ff9f2ba 0xbd0181823f81f8c7

def z481 : W := mkw 0xa0dc77d97b2aa669 0x0b7fb11833befb92 0x01fffffffffe03df 0x03fff19c3fffff00

def z482 : W := mkw 0x0000000000000180 0x0044504280000000 0xfe000000000000c0 0x00067003c0000000

def z483 : W := mkw 0x005c75d939208269 0x037fb11003bedb90 0x007fffffffffffef 0xc3fff1fc07fffff8

def z484 : W := mkw 0x522db0eb3d6559c7 0x10d7fc638465df6d 0xfe7f81fe3fffffef 0xfee7fe63c671ffff

def z485 : W := mkw 0x65228a0006906028 0xa0000b816d0120c3 0xffff80003fc1f2ba 0xbe060f83fe01c0c7

def z486 : W := mkw 0x00524d1480008228 0xc3280394039a0090 0x007fffffc000030c 0x03f8019c07fe0000

def z487 : W := mkw 0x1000000000001186 0x0000404200000424 0xf00000000001fc20 0xfc000062000000ff

def z488 : W := mkw 0x5277cdb69445d9ae 0xd0c45d7387fb85fd 0xfe7fffffffc7ffef 0xfee67e63c7ffc7ff

def z489 : W := mkw 0x0031453480018000 0x40a80c34045a0058 0x007f81ffc001ff2c 0xc2f80e7c067e00f8

def z490 : W := mkw 0x255a7b492bb02269 0xa33ba3806b967a82 0x01807e01c0380010 0x01198180398e3800

def z491 : W := mkw 0x0021002000010000 0x00800c2004400048 0x001f800e00000000 0x02e00e0006700000

def z492 : W := mkw 0xb0f35f74ca0bb5ae 0xc811695a37de36fe 0xf1fffffffe3fffff 0xfd19f1fe3ffe3fff

def z493 : W := mkw 0xed6aaa0026906278 0xa33bab8d7f8168c3 0xfffffe003ff9f2ba 0xbf1f8f9fff81f8c7

def z494 : W := mkw 0x254a2a0022902228 0xa30283806b806882 0x01fffe003ff8029a 0x030781803f81f800

def z495 : W := mkw 0x654aaa0026906228 0xa30283816b816883 0xff807e003ff80092 0x3d078183f981f807

def z496 : W := mkw 0x8800000000000390 0x0382c6eed8000000 0xff800000000002b0 0x03078ffff8000000

def z497 : W := mkw 0x00524d1480008028 0xc0000110039a0090 0x00007e01c0000000 0x00000000018e0000

def z498 : W := mkw 0x4020800004004000 0x0000080104010041 0x0e1f800001c00000 0x02060e01c601c000

def z499 : W := mkw 0xb88012404a0a37d6 0x0bfff6eef8043626 0xff8000003e3e03f3 0x3ffffffff8003f07

def z500 : W := mkw 0x005c618931200241 0x036e900002b2c900 0x007ffe0e3ff8028a 0x03e7800007f1f800

def z501 : W := mkw 0x0011412480010000 0x40a8042400520008 0x0000000e00000000 0x00e0000000700000

def z502 : W := mkw 0xf7efbef27edfffae 0xbbd7fffbffedffff 0xffffffffffffffff 0xffffffffffffffff

def z503 : W := mkw 0x0014418911200041 0x006c100000328100 0x0000000e00000000 0x00e0000000700000

def z504 : W := mkw 0x5235d1eb1d6559c7 0x10fd7c638477976d 0xfe7f81ffffc7ffef 0xfefe7e63c67fc7ff

def z505 : W := mkw 0x0000000000000000 0x0002800048000000 0xff80000000000090 0x00078003f8000000

def z506 : W := mkw 0x656aaa0026906228 0xa3000b81278168c3 0x007ffe003ff9f22a 0xbf000f800781f8c7

def z507 : W := mkw 0x0021002000010200 0x03a80ea404400048 0x007f81fe0001ff2c 0xc3f80ffc067000f8

def z508 : W := mkw 0xe56aaa00269063a8 0xa313ebcb7f8168c3 0xfffffe003ff9f3fa 0xbf1fffffff81f8c7

def z509 : W := mkw 0x30f35f74ca0bb62e 0xcba80fb427de36fe 0x007ffffffe3fff2f 0xfff80ffc07fe3fff

def z510 : W := mkw 0x00735d7488018228 0xc3b92fb407de12d8 0x007ffffffe3fffef 0xc3f9fffc07fe3ff8

def z511 : W := mkw 0x005e7dddb9208269 0xc37fb39403bedb90 0x007ffffffffe03cf 0x03fff19c07ffff00

def z512 : W := mkw 0x0000041000008000 0x0000001000080010 0x000001f1c0000d04 0x4018007c000e0038

def z513 : W := mkw 0x676faaa236d56a28 0xb3c69fa1efe1e9cb 0xfffffe0e3ff9f2ba 0xbfe78f83fff1f8c7

def z514 : W := mkw 0x0050410000000200 0x03a806a402920000 0x007fffffc000032c 0x03f80ffc07fe0000

def z515 : W := mkw 0x005c618931200241 0x036e900002b2c900 0x007f81fe3fc603cf 0x02e670000671c700

def z516 : W := mkw 0x928514f2584f9d86 0x18d5747a906c973c 0x000001ffc0060d45 0x40f8707c007e0738

def z517 : W := mkw 0x8800000000000010 0x0000028c58000000 0x0180000000000010 0x0000019c38000000

def z518 : W := mkw 0x4000800004004000 0x0000000100010001 0xfe0000003fc00082 0x3c060003c001c007

def z519 : W := mkw 0x656aaa00269063a8 0xa3c6dfe3ef8168c3 0xfffffe003ff9f3fa 0xbfe7ffe3ff81f8c7

def z520 : W := mkw 0x522580a214455806 0x10c41c218461856d 0x0e7f81fe3fc7fc0f 0xfee60e01c671c7ff

def z521 : W := mkw 0xb0e21e504a0ab7ae 0x8b116bda378c36f6 0xf1fffff1fe3fffff 0xff19fffe3f8e3fff

def z522 : W := mkw 0x522580a214455986 0x10c45c638461856d 0xfe1f800e3fc600c3 0x3ee67e03c671c707

def z523 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0x0180000000000150 0x01f9f1fc38000000

def z524 : W := mkw 0x9a0500a2104519d6 0x10fd746e9060852c 0x000001fe00060d45 0x40f8707c00700738

def z525 : W := mkw 0x756aaa00269073ae 0xa302cbc36f816ce7 0xfffffff03fffffff 0xff07ffe3ff81ffff

def z526 : W := mkw 0x722582a2164579ae 0x10c45d63a561a5ef 0xfffffffe3fffffff 0xffe7ffe3fff1ffff

def z527 : W := mkw 0x2000020002002028 0x0000010021002082 0xf18000000001f030 0xbc000182380000c7

def z528 : W := mkw 0x776eaa8236d47bae 0xb346dbc3efa1ede7 0xfffffe003ffff2fb 0xbf07ff83ff81ffc7

def z529 : W := mkw 0x522580a214455986 0x10804c638461856d 0xfe7f81fe3fc7fc2f 0xfc000e63c671c7ff

def z530 : W := mkw 0x656aaa0026906228 0xa3028901278168c3 0x007ffe003ff9f28a 0xbf0780000781f8c7

def z531 : W := mkw 0x909455d9592a95c7 0x087d705a103e9734 0x000001ffc0060d45 0x40f8707c007e0738

def z532 : W := mkw 0x001451c919200041 0x007d300000369300 0x007f81ffffc603cf 0x02fe7000067fc700

def z533 : W := mkw 0x00020c1480008028 0xc000039401080090 0x0000000000000000 0x0000019c00000000

def z534 : W := mkw 0x0020000000000000 0x0000080004000040 0x007f80000001f228 0x82000e00060000c0

def z535 : W := mkw 0x656bae34a691e228 0xe3828fb56fc968db 0xfffffe003ff9feba 0xff078fffff81f8ff

def z536 : W := mkw 0x000c30c939200041 0x0057b0000024db00 0x007f81fe3ffe03cf 0x02e7f0000671ff00

def z537 : W := mkw 0x005c71c9392003c1 0x03fff46282b6db00 0xfe7ffffffffe03ef 0x03fffe63c7ffff00

def z538 : W := mkw 0x4020800004004200 0x03028a814c010041 0xffff80003fc1f2ba 0xbf078f83fe01c0c7

def z539 : W := mkw 0x6500820006906000 0x2000000168012003 0xff80000000000010 0x3c000003f8000007

def z540 : W := mkw 0x522580a214455986 0x104458438461856d 0xfe7f81fe3fc7fccf 0xfc067003c671c7ff

def z541 : W := mkw 0x805c71c9392003c1 0x037ff04a12b6db00 0xf1fffffffffe03ff 0x03fff1fe3fffff00

def z542 : W := mkw 0x4d6aa80024904250 0xa3ee9ea5ce814841 0x0e1f800001c00000 0x02e60e01c601c000

def z543 : W := mkw 0x522580a214455806 0x10800c210461856d 0x007f81fe3fc7ff2f 0xfee00e600671c7ff

def z544 : W := mkw 0x00724d1480008228 0xc3280b94079a00d0 0x007ffe01c001f228 0x83180f9c078e00c0

def z545 : W := mkw 0xf28496d25e4efdae 0x1855715bb12db7b7 0xffe07ff1ffffffff 0xfd1ff1fff98fffff

def z546 : W := mkw 0xb5ca3e506a9ab7ae 0xab13e3da7b8c7eb6 0xf1e07ff1fe3fffff 0xfd19f1fe398e3fff

def z547 : W := mkw 0xb08016504a0ab7ae 0x0b13e3da790c36b6 0xffe07ff1fe3fffff 0xff1ffffff98e3fff

def z548 : W := mkw 0x0058714929200001 0x0000000002965a00 0x00007e01c0380000 0x00000000018e3800

def z549 : W := mkw 0xa08016504a0aa428 0x08112118310c3292 0xf1e07e01fe39f2ba 0xbd19819e398e38c7

def z550 : W := mkw 0x00734d3480018028 0xc0800d3007da00d8 0x007fffffc001ff2c 0xc2e00e6007fe00f8

def z551 : W := mkw 0xf28492c25e4e7d86 0x1855704bb025b727 0xff8000003ffe00d3 0x3c07f003f801ff07

def z552 : W := mkw 0x98801450480a97d6 0x0bfff6fed80c1634 0xff8001f1c0060ff5 0x43fffffff80e0738

def z553 : W := mkw 0xed7efbc93fb063f9 0xa3ffffefffb7fbc3 0xfffffffffffff3ff 0xbfffffffffffffc7

def z554 : W := mkw 0x777fefb6b6d5fbae 0xf3eedff7effbedff 0xffffffffffffffff 0xffffffffffffffff

def z555 : W := mkw 0x522580a214455b86 0x13ec5ee78461856d 0xfe7f81fe3fc7ffef 0xfffe7fffc671c7ff

def z556 : W := mkw 0x422580a214454800 0x1000080104618149 0x001f800e01c00000 0x000000000671c000

def z557 : W := mkw 0x005c618931200001 0x0000000002b2c900 0x001f800e01c00000 0x000000000671c000

def z558 : W := mkw 0x125d71eb39651bc7 0x13fff46282f6df2c 0x007ffffffffe0fcf 0x43fff06007ffff38

def z559 : W := mkw 0x0040000000000200 0x0300000002800000 0x007ffe0000000208 0x0300000007800000

def z560 : W := mkw 0x00775dfd99218269 0xc3fd3fb407fe93d8 0x007fffffc007ff6d 0xc3f87ffc07fe07f8

def z561 : W := mkw 0x254a2a0022902028 0xa000010023806882 0x00007e0000380000 0x0000000001803800

def z562 : W := mkw 0x1000104008001186 0x0011604200041624 0xf0607ff1fe3fffef 0xfd19f062018e3fff

def z563 : W := mkw 0x0000000000000240 0x036e900000000000 0x0000000000000000 0x02e6000000000000

def z564 : W := mkw 0x121545b690459986 0x50ec5476807a853c 0x000001ffc0060d45 0x40f8707c007e0738

def z565 : W := mkw 0x457be924a4914200 0xe3aa8ea54ed34849 0x0e1f800e01c00000 0x02e60e01c671c000

def z566 : W := mkw 0xf2a586b2564ffdae 0x18c45d7bb569a5ff 0xffff81fe3fc7ffff 0xfee67ffffe71c7ff

def z567 : W := mkw 0x656ebac93fb06269 0xa357bb816fa5fbc3 0xfffffe003ffff2fb 0xbf07ff83ff81ffc7

def z568 : W := mkw 0x0071412000010200 0x03a80c2006d20048 0x007fffffc001ff2c 0xc3f80e6007fe00f8

def z569 : W := mkw 0x005c71c939200201 0x0328000002b6db00 0x007ffffffffe030f 0x03f8000007ffff00

def z570 : W := mkw 0x456aa80024904200 0xa3028a814e814841 0x0e7ffe003ff8028a 0x03078e01c781f800

def z571 : W := mkw 0xb08016504a0ab42e 0x08112118310c36b6 0x01e07ff1fe3ffc1f 0xfd19819c398e3fff

def z572 : W := mkw 0xa8000200020023f8 0x03fff7eef9002082 0xffe07e003e39f3fa 0xbffffffff98038c7

def z573 : W := mkw 0x657afb492fb06269 0xa33bab816f977ac3 0xfffffe01fff9f2ba 0xbf1f8f83ff8ff8c7

def z574 : W := mkw 0x527df1eb3d655987 0x10c45c6386f7df6d 0xfe7fffffffffffef 0xfee67e63c7ffffff

def z575 : W := mkw 0x256a2a0022902228 0xa3028b806f8068c2 0x01fffe000039f238 0x83018f803f8038c0

def z576 : W := mkw 0xb0800610420ab5ae 0x0800415a310824b6 0xf1e07e003e39feba 0xfd0181fe398038ff

def z577 : W := mkw 0x657efbc93fb06269 0xa37fb90127b7fbc3 0x007ffffffffff3cf 0xbffff00007ffffc7

def z578 : W := mkw 0x5204808214445986 0x1044504380218525 0xfe7f81fe3fc603cf 0x3ee67003c671c707

def z579 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0xff807e000039f030 0xbd018f83f98038c7

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0x006001f03e0603cf 0x0000700000000700

def z581 : W := mkw 0x427de1ab35654a41 0x13ee9c2186f3c949 0x0e1f800e01c00000 0x02e60e01c671c000

def z582 : W := mkw 0xb0dc77d97b2ab5af 0x0811615a33beffb6 0xf1ffffffffffffff 0xfd19f1fe3fffffff

def z583 : W := mkw 0x30000200020031ae 0x00004142210024a6 0xf1e07ff03e3fffff 0xfd01f1e239803fff

def z584 : W := mkw 0x88000000000001d0 0x00fd746e90000000 0xfe000000000003e0 0x02fe7e7fc0000000

def z585 : W := mkw 0x0058714929200241 0x033ba00002965a00 0x00607ff1fe3e03cf 0x0119f000018e3f00

def z586 : W := mkw 0x00734d3480018268 0xc3ffbfb407da00d8 0x007fffffc001ffec 0xc3fffffc07fe00f8

def z587 : W := mkw 0xad4a2a00229023f8 0xa3fff7eefb806882 0xff807e00003803f0 0x03fffffff9803800

def z588 : W := mkw 0xf5a28e10469af5ae 0xa8004bdb7d0924f7 0xff8000000001fc30 0xfc000ffff80000ff

def z589 : W := mkw 0x0010410000000000 0x0028000000120000 0x000001ffc0000104 0x00f80000007e0000

def z590 : W := mkw 0x0000000000000200 0x03a806a400000000 0x0000000000000000 0x02e00e0000000000

def z591 : W := mkw 0x776faaa236d579ae 0xb0c45d63a7e1edef 0xfe7ffffe3fffffef 0xfee67e63c7f1ffff

def z592 : W := mkw 0x0073492480010200 0xc3a80ea406d20048 0x007fffffc000030c 0x03f80e0007fe0000

def z593 : W := mkw 0x657beb24a6916228 0xe3aa8fa56fd368cb 0xfffffe0e3ff9f2ba 0xbfe78f83fff1f8c7

def z594 : W := mkw 0x254a2a0022902228 0xa30283806b806882 0xf1e07e003e39f2ba 0xbd018182398038c7

def z595 : W := mkw 0x75eabe506e9af62e 0xab028b916f8d7ef7 0xfffffff1fffffebf 0xff078f83ff8fffff

def z596 : W := mkw 0x4020800004004000 0x0000080104010041 0xfe0000000001f020 0xbc000e03c00000c7

def z597 : W := mkw 0x200012400a002028 0x0011210021043282 0xf1e07ff1fe3ff3ff 0xbd19f182398e3fc7

def z598 : W := mkw 0x0058714929200241 0x037fb00002965a00 0x00007e01c03803c0 0x03fff000018e3800

def z599 : W := mkw 0xa08016504a0aa5a8 0x0811615a310c3292 0xf1807e01c03803f0 0x0119f1fe398e3800

def z600 : W := mkw 0x522580a214455986 0x10c45c638461856d 0x0e1f81fe01c60d45 0x42e67e61c671c738

def z601 : W := mkw 0xd2a594f25c4fdd86 0x18d57c7b946d977d 0xfe7f81ffffc7ffef 0xfefe7e7fc67fc7ff

def z602 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0xf18000003e3ffcf3 0xfc01f1fe38003fff

def z603 : W := mkw 0x0072490000000228 0x83280b80079200c0 0x007fffffc001f32c 0x83f80f8007fe00c0

def z604 : W := mkw 0x0000000000000200 0x0302800000000000 0x0000000000000280 0x0307800000000000

def z605 : W := mkw 0x476fa8a234d54a00 0xb3c69ea1cee1c949 0x0e1f800e01c00000 0x02e60e01c671c000

def z606 : W := mkw 0x005c618931200241 0x037fb00002b2c900 0x001f800e01c003c0 0x03fff0000671c000

def z607 : W := mkw 0x0000000000000240 0x03ffb6a400000000 0x00000000000003e0 0x03fffffc00000000

def z608 : W := mkw 0x0058714929200241 0x033ba00002965a00 0x007ffe01fff8028a 0x031f8000078ff800

def z609 : W := mkw 0x000c30c939200001 0x000000000024db00 0x000000003ffe0003 0x000000000001ff00

def z610 : W := mkw 0x0048200020000200 0x0302800002804800 0x001f800001c00000 0x020600000601c000

def z611 : W := mkw 0x0000145008008028 0x00112110010c1290 0x00607ff1fe3fffef 0xc119f1fc018e3ff8

def z612 : W := mkw 0xa0d877596b2aa669 0x0b3ba118339e7a92 0x01807e01c0380010 0x0119819c398e3800

def z613 : W := mkw 0x5221802204455986 0x10804c638441046d 0xfe6001f03e07ffef 0xfc007e63c00007ff

def z614 : W := mkw 0x527df1eb3d655a47 0x137fb80106f7df6d 0x007fffffffffffcf 0xfffff00007ffffff

def z615 : W := mkw 0x80000000000003c0 0x037ff04a10000000 0xf1800000000003f0 0x03fff1fe38000000

def z616 : W := mkw 0x0062080000000228 0x83028b804f8000c0 0xfffffe000001f2b8 0x83078f83ff8000c0

def z617 : W := mkw 0x0800000000000250 0x032a828448000000 0x0000000000000000 0x0000000000000000

def z618 : W := mkw 0x80734d34800183a8 0xc3b96ffe17da00d8 0xf1ffffffc001fffc 0xc3f9fffe3ffe00f8

def z619 : W := mkw 0x0062080000000228 0x83a80fa4078000c0 0x007ffe000001f328 0x83f80ffc078000c0

def z620 : W := mkw 0x20620a0002002228 0x83000b80278020c2 0xf1fffe003e39f2ba 0xbf018f823f8038c7

def z621 : W := mkw 0x77238a2206d579ae 0xb0804fe3ed4124ef 0xff8000000001fc30 0xfc000fe3f80000ff

def z622 : W := mkw 0xb08016504a0ab5ae 0x08d5757ab10c36b6 0xffe07ff1fe3fffff 0xfffffffff98e3fff

def z623 : W := mkw 0x00000000000003c0 0x03fff46280000000 0xfe000000000003e0 0x03fffe63c0000000

def z624 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0x01807ff1c03e0d55 0x4119f1fc398e3f38

def z625 : W := mkw 0x0054418010000200 0x036c100002b28100 0x007fffffffc603cf 0x03fe700007ffc700

def z626 : W := mkw 0x254a2a0022902228 0xa30283806b806882 0xff807e00003802b0 0x03078f83f9803800

def z627 : W := mkw 0x0022080000000028 0x80000b80050000c0 0x000000000001f020 0x80000f80000000c0

def z628 : W := mkw 0x0008200020000000 0x0002800000004800 0x000000003ff80082 0x000780000001f800

def z629 : W := mkw 0xf2a592e25e4f7d86 0x18d57c6bb465b76f 0xffff81fe3fffffff 0xfee7fe63fe71ffff

def z630 : W := mkw 0x0048200020000240 0x037fb00002804800 0x007ffe003ff803ca 0x03fff0000781f800

def z631 : W := mkw 0x10734d34800193ae 0xc3a84ff607da04fc 0xf07ffffffe07ffef 0xfff87ffe07fe07ff

def z632 : W := mkw 0x0000000000000040 0x007d300000000000 0x0000000000000140 0x00f8700000000000

def z633 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0xf1e07ff1fe3ffcdf 0xfc01f002398e3fff

def z634 : W := mkw 0x0000000000000240 0x033ba00000000000 0x0000000000000000 0x0119800000000000

def z635 : W := mkw 0xf5eabe506e9af5ae 0xa811695b378d7ef7 0xf1fffff1ffffffff 0xfd19f1fe3f8fffff

def z636 : W := mkw 0x90800410400a9586 0x0800405a10080434 0x0000000000000c00 0x4000007c00000038

def z637 : W := mkw 0x0873492480010250 0xc3ee9ea4ced20048 0x0e1f800e00000000 0x02e60e01c6700000

def z638 : W := mkw 0x98801450480a95d6 0x08fd747e900c1634 0x000001f1c0060d45 0x40f8707c000e0738

def z639 : W := mkw 0x656eaa8036906228 0xa3469b816fa1e9c3 0xfffffffe3ffff3ff 0xbfe7ff83fff1ffc7

def z640 : W := mkw 0x0042080000000228 0x8300038003800080 0x00007e0000000000 0x0100018001800000

def z641 : W := mkw 0x0800000000000050 0x00ec142480000000 0x0000000000000000 0x00e0000000000000

def z642 : W := mkw 0xcd6aa800249043d0 0xa3fffeefde814841 0xff9f800001c003f0 0x03fffffffe01c000

def z643 : W := mkw 0x0062080000000028 0x80000900078000c0 0x007ffe000001f008 0x80000000078000c0

def z644 : W := mkw 0x08000000000003d0 0x03eed6e6c8000000 0xfe000000000003e0 0x02e67e63c0000000

def z645 : W := mkw 0x427df1eb3d654a41 0x13ffbc2186f7db49 0x0e7ffffffffe03cf 0x03fffe01c7ffff00

def z646 : W := mkw 0xb0a31e74ca0bb5ae 0xc8916ffe354c36fe 0xf1e07ff1fe3fffff 0xfd19fffe398e3fff

def z647 : W := mkw 0x5273cd368445dbae 0xd3a84ff787db04fd 0xfe7fffffc001ff2c 0xfff80fffc7fe00ff

def z648 : W := mkw 0x0000000000000200 0x0302828048000000 0x0e00000000000000 0x02060e01c0000000

def z649 : W := mkw 0x6d6aaa0026906278 0xa3ee9fa5ef8168c3 0xfffffe003ff9f2ba 0xbfe78f83ff81f8c7

def z650 : W := mkw 0x0004008010000000 0x0044100000208100 0x000000003fc600c3 0x000670000001c700

def z651 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0x00007e01fffe00c3 0x011ff000018fff00

def z652 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x001ffe0fc0000000 0x03f80f9c07fe0000

def z653 : W := mkw 0xb0ff7ffdfb2bb7ef 0xcbfffffe37fefffe 0xf1ffffffffffffff 0xfffffffe3fffffff

def z654 : W := mkw 0xb08016504a0ab7ee 0x0b7ff15a310c36b6 0xf1e07ff1fe3fffff 0xfffff1fe398e3fff

def z655 : W := mkw 0xb0a116704a0bb5ae 0x08916d7a354c36fe 0xf1fffffffe3fffff 0xfff9fffe3ffe3fff

def z656 : W := mkw 0x522584b21445d9ae 0x10c45d73856985fd 0xfe7fffffffc7ffef 0xfffe7fffc7ffc7ff

def z657 : W := mkw 0x5020800004005186 0x0000484304010465 0xfe7f81f03fc7ffef 0xfe067e63c601c7ff

def z658 : W := mkw 0x522580a214455806 0x100008010461856d 0xfe7f81fe3fc7feaf 0xfe060e03c671c7ff

def z659 : W := mkw 0x522580a214455986 0x10c45c638461856d 0xfe1f800e01c1fc20 0xfee60e63c671c0ff

def z660 : W := mkw 0x0000000000000000 0x0011200000000000 0x00000000000003c0 0x0119f00000000000

def z661 : W := mkw 0x00524d1480008228 0xc3280394039a0090 0x00607ff1c001ff2c 0xc11801fc018e00f8

def z662 : W := mkw 0xe5eabe506e9ae628 0xab13ab997f8d7ad3 0xfffffe01fff9f2ba 0xbf1f8f9fff8ff8c7

def z663 : W := mkw 0x456aa80024904200 0xa3028a814e814841 0xfe7f80003fc1f2aa 0xbe060e03c601c0c7

def z664 : W := mkw 0xb08016504a0ab5ae 0x0800415a310c36b6 0xf1e07ff1fe3ffc3f 0xfc0001fe398e3fff

def z665 : W := mkw 0x0021002000010000 0x00800c2004400048 0x000000000001fc20 0xc0000e60000000f8

def z666 : W := mkw 0x0000000000000000 0x0080042000000000 0x0000000000000320 0x02e00e6000000000

def z667 : W := mkw 0x0000000000000000 0x0000000000000000 0xf1800000000002b0 0x0101818238000000

def z668 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x007fffffc001fc0c 0xc2e00e0007fe00f8

def z669 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0x01fffe003ff9f01a 0xbd0181803f81f8c7

def z670 : W := mkw 0x885c71c9392003d1 0x03fff46e92b6db00 0x007ffffffffe03cf 0x03fff07c07ffff00

def z671 : W := mkw 0x08734d3480018278 0xc3ee9fb4cfda00d8 0x0e7fffffc001ff2c 0xc3fe0ffdc7fe00f8

def z672 : W := mkw 0x8000000000000380 0x03b966ee10000000 0xf1800000000003f0 0x03f9fffe38000000

def z673 : W := mkw 0x522580a214455986 0x10c45c638461856d 0xfe0001fe0007fd65 0xfce07e63c07007ff

def z674 : W := mkw 0x8800000000000050 0x0039200c10000000 0x0000000000000000 0x0018001c00000000

def z675 : W := mkw 0x90801450480a9586 0x0811605a100c1634 0xf06001f1fe07ffef 0xfc18707e000e07ff

def z676 : W := mkw 0x0073492480010200 0xc3a80ea406d20048 0x001f800e00000320 0x03f80ffc06700000

def z677 : W := mkw 0x776faaa236d5782e 0xb000090127e1edef 0x007ffffe3ffffc0f 0xfc00000007f1ffff

def z678 : W := mkw 0x576fa8a234d55b86 0xb3c6dee3cee1cd6d 0xfe7f81fe3fc7ffef 0xfee67e63c671c7ff

def z679 : W := mkw 0xb8800610420ab7fe 0x0bfff7fef90824b6 0xff8000000001fff0 0xfffffffff80000ff

def z680 : W := mkw 0x105c71c9392013c7 0x037ff04202b6df24 0xf07fffffffffffef 0xfffff06207ffffff

def z681 : W := mkw 0xa88016504a0aa7f8 0x0bfff7fef90c3292 0xff807e01c03803f0 0x03fffffff98e3800

def z682 : W := mkw 0x0000000000000180 0x0000404200000000 0xf0000000000003e0 0x0000706200000000

def z683 : W := mkw 0x0073492480010200 0xc3a80ea406d20048 0x007f81fe0001ff2c 0xc2e00e60067000f8

def z684 : W := mkw 0x0800000000000250 0x03ee96a4c8000000 0xff800000000002b0 0x03e78f83f8000000

def z685 : W := mkw 0x0063082000010228 0x83800fa007c000c8 0x007ffffe0001ff2c 0xc3e00fe007f000f8

def z686 : W := mkw 0x020500a210450800 0x10c4142080608108 0x0000000e00000000 0x00e0000000700000

def z687 : W := mkw 0xda21802204455996 0x10804eefdc41046d 0xff8000000001fc30 0xfc000ffff80000ff

def z688 : W := mkw 0x8000000000000180 0x0011604a10000000 0x0000000000000140 0x0018707c00000000

def z689 : W := mkw 0x80000410000081a8 0x0011615a11080090 0xf1e07ff1c001fffc 0xc119f1fe398e00f8

def z690 : W := mkw 0x522580a214455986 0x100048430461856d 0xf07f81fe3fc7ffef 0xfc0070620671c7ff

def z691 : W := mkw 0x0023082480010000 0xc0800ea404400048 0x0000000000000000 0x00000e0000000000

def z692 : W := mkw 0x5277cdb69445d82e 0xd000091107fb85fd 0x007fffffffc7fc0f 0xfc00000007ffc7ff

def z693 : W := mkw 0x005c71c939200241 0x036e900002b6db00 0x007ffffffffe000f 0x02e6000007ffff00

def z694 : W := mkw 0x25020a0002902028 0xa000038069002082 0x0180000000000010 0x0000018038000000

def z695 : W := mkw 0x88734924800103d0 0xc3fffeeeded20048 0xff9f800e000003f0 0x03fffffffe700000

def z696 : W := mkw 0x88000000000003d0 0x037ff2ced8000000 0xff800000000000d0 0x011ff19ff8000000

def z697 : W := mkw 0x0073492480010000 0xc000080006d20048 0x001f800e00000000 0x0000000006700000

def z698 : W := mkw 0x0021002000010000 0x0000080004400048 0x007f81fe0001fc0c 0xc0000000067000f8

def z699 : W := mkw 0x0058714929200241 0x033ba00002965a00 0x007fffffc038030c 0x03f9800007fe3800

def z700 : W := mkw 0x525cf1cb3d645bc7 0x137ff04382b7df25 0xfe7ffffffffe03cf 0x3ffff003c7ffff07

def z701 : W := mkw 0xf5eaba406e9a77ae 0xab13ebcb7f857ee7 0xfffffe003ffff2fb 0xbf07ff83ff81ffc7

def z702 : W := mkw 0x0050410000000000 0x0000000002920000 0x007fffffc000000c 0x0000000007fe0000

def z703 : W := mkw 0x205c73c93b202269 0x037fb10023b6fb82 0xf1fffffffffff3ff 0xbffff1823fffffc7

def z704 : W := mkw 0x88000000000001d0 0x00d7f46ad8000000 0xff800000000003f0 0x02e7fe63f8000000

def z705 : W := mkw 0x456aa80024904000 0xa000080106814841 0x001f800001c00000 0x000000000601c000

def z706 : W := mkw 0xb88012404a0a35d6 0x0857f04af8043626 0xff8000003e3e00d3 0x3c07f003f8003f07

def z707 : W := mkw 0x0051453480018200 0x43a806b402da0018 0x007fffffc0000f2c 0x43f80ffc07fe0038

def z708 : W := mkw 0x00630c3000018228 0x83800fb007c800d8 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z709 : W := mkw 0x88734d34800181f8 0xc057f95adfda00d8 0xffffffffc001fcdc 0xc007f003fffe00f8

def z710 : W := mkw 0x0051453480018228 0x43a8053403da0098 0x007fffffc001ff2c 0xc3f801fc07fe00f8

def z711 : W := mkw 0xd5eabc506c9ad786 0xab13eadb5e8d5e75 0x0e1f81f1c1c60d45 0x421e7e7dc60fc738

def z712 : W := mkw 0x657bef34a691e228 0xe32a8b916fdb68db 0xfffffffffff9ffbe 0xffff8f83fffff8ff

def z713 : W := mkw 0x657bef34a691e228 0xe3aa8fb56fdb68db 0x0e7ffffffff9ff2e 0xfffe0ffdc7fff8ff

def z714 : W := mkw 0x985c71c9392013d7 0x03fff6eedab6df24 0xffffffffffffffff 0xffffffffffffffff

def z715 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0x007ffffffffe03ef 0x03fff1fc07ffff00

def z716 : W := mkw 0x4068a00024004200 0x03028a814e814841 0xfffffe003ff9f2ba 0xbf078f83ff81f8c7

def z717 : W := mkw 0x257b6f34a291a228 0xe3aa8fb46fda68da 0x01fffffffff9ffbe 0xc3ff8ffc3ffff8f8

def z718 : W := mkw 0xb0f35b64ca0b3786 0xcbb96eee36d6366e 0xf19f800e3e3e00d3 0x3ee1fe023e703f07

def z719 : W := mkw 0x881451c9192003d1 0x03fff6eed8369300 0xffff81ffffc603ff 0x03fffffffe7fc700

def z720 : W := mkw 0x255b6f34a291a228 0xe3aa87b46bda689a 0x01807fffc0380d14 0x41f981fc39fe3838

def z721 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xff800000000000f0 0x02e7fffff8000000

def z722 : W := mkw 0x88000000000001d0 0x00d576eed8000000 0xff80000000000070 0x00007ffff8000000

def z723 : W := mkw 0x657bef34a691e228 0xe32a891127db68db 0x007ffffffff9ff8e 0xffff800007fff8ff

def z724 : W := mkw 0x002f3cfdb9218069 0xc0d7bfb4056cdbd8 0x000000003ffffce3 0xc007fffc0001fff8

def z725 : W := mkw 0x8000000000000180 0x001162ca58000000 0xff800000000003f0 0x0119fffff8000000

def z726 : W := mkw 0x652aaa0026906228 0xa3028b816d0168c3 0xff8000003ff9f2b2 0xbf078f83f801f8c7

def z727 : W := mkw 0x8800000000000250 0x03ee96acd8000000 0x0f80000000000010 0x02e60f9df8000000

def z728 : W := mkw 0xa5da7f596bbaa669 0xab3ba3987b9e7a92 0x01807e01c0380010 0x0119819c398e3800

def z729 : W := mkw 0x8800000000000390 0x03ec56eed8000000 0xff800000000003f0 0x03fe7ffff8000000

def z730 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x001f81ffc001fd24 0xc2f80ffc067e00f8

def z731 : W := mkw 0x657ffffdbfb1e269 0xe37fb91127fffbdb 0x007fffffffffffcf 0xfffff00007ffffff

def z732 : W := mkw 0x656aaa0026906028 0xa00289016f8168c3 0xfffffe003ff9f2ba 0xbe078e03ff81f8c7

def z733 : W := mkw 0x881451c9192003d1 0x03fff6eed8369300 0xffe07ffffe3e03ff 0x03fffffff9fe3f00

def z734 : W := mkw 0x005c71c939200201 0x0339200002b6db00 0x007ffffffffe03cf 0x03f9f00007ffff00

def z735 : W := mkw 0x6073cf348601e228 0xc3a80fb527db20db 0xfffffffffff9ffbe 0xffff8ffffffff8ff

def z736 : W := mkw 0x88000000000001d0 0x00ec56eed8000000 0xff80000000000030 0x00e00ffff8000000

def z737 : W := mkw 0x72fdf7fb7f6ffc2f 0x1800091127ffffff 0x007ffffffffffc0f 0xfc00000007ffffff

def z738 : W := mkw 0x88000000000003d0 0x033be2ce58000000 0xff800000000003f0 0x031ffffff8000000

def z739 : W := mkw 0x9800000000001196 0x008046eed8000424 0xff8000000001fc30 0xfc000ffff80000ff

def z740 : W := mkw 0x88504100000003d0 0x03fff6eeda920000 0xff807e01c00003f0 0x03fffffff98e0000

def z741 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0xfffffff1fff9f3be 0xbf1f8f83ff8ff8c7

def z742 : W := mkw 0x0001043000018000 0x0080043000480018 0x000001ffc0000d04 0x40f8007c007e0038

def z743 : W := mkw 0x885c71c939200251 0x037fb28c5ab6db00 0xfffffffffffe03ff 0x03ffff9fffffff00

def z744 : W := mkw 0x0000000000000000 0x008006a448000000 0xff80000000000030 0x00000ffff8000000

def z745 : W := mkw 0x8800000000000190 0x008046eed8000000 0xff800000000002b0 0x01018ffff8000000

def z746 : W := mkw 0x457bed34a491c200 0xe3aa8eb54edb4859 0x0e1f81ffc1c00d04 0x42fe0e7dc67fc038

def z747 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x001fffffc0000d04 0x43f80ffc07fe0038

def z748 : W := mkw 0x005c71c939200041 0x007d300002b6db00 0x007ffffffffe03cf 0x02fe700007ffff00

def z749 : W := mkw 0x457fe9adb5b14241 0xe3ee9ea54ef3c949 0x0e1f800e01c00000 0x02e60e01c671c000

def z750 : W := mkw 0x4073cd348401c228 0xc3a80fb507db00d9 0xfe7fffffc001ff2c 0xfff80fffc7fe00ff

def z751 : W := mkw 0x00524d1480008228 0xc3280394039a0090 0x007fffffc001ff2c 0xc3f801fc07fe00f8

def z752 : W := mkw 0x880410c9192003d1 0x03fff6eed8249300 0xff800000000603f1 0x03fffffff8000700

def z753 : W := mkw 0x00734d3480018228 0xc3a80d3407da00d8 0x007fffffc001ff0c 0xc3f8007c07fe00f8

def z754 : W := mkw 0x007b6d34a0018228 0xc3aa8fb44fda48d8 0xfffffffffff9ffbe 0xc3ff8ffffffff8f8

def z755 : W := mkw 0x0031453480018028 0x40a80d34055a00d8 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z756 : W := mkw 0x00534d3480018200 0xc3a806b402da0018 0x000001ffc0000d04 0x40f8007c007e0038

def z757 : W := mkw 0x805c71c9392003c1 0x03fff46a92b6db00 0xfffffffffffe03ff 0x03ffffffffffff00

def z758 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0xf1fffffffffe03ff 0x03fff1823fffff00

def z759 : W := mkw 0xda0cb0cb3d6459d7 0x1057f04bd825df25 0xff8000003ffe00d3 0x3c07f003f801ff07

def z760 : W := mkw 0x8800000000000250 0x03ffb6acd8000000 0x0f800000000003d0 0x03ffff9df8000000

def z761 : W := mkw 0xb28412c25a4e3d86 0x1855704ab024b726 0xf18000003e3e00d3 0x3c01f00238003f07

def z762 : W := mkw 0x5256cd969444dbae 0xd36c53d783bb85b5 0xfe007e01ffc600c3 0x3d1e719fc18fc707

def z763 : W := mkw 0x656aae102690e028 0xa0000911278968d3 0x007ffff1fff9fc0e 0xfc000000078ff8ff

def z764 : W := mkw 0x9a01002200451bd6 0x13fff6eed840042c 0xff80000000000ff0 0x43fffffff8000038

def z765 : W := mkw 0x1004008010001186 0x00c4546280208524 0xfe7f81fe3fc7ffef 0xfee67e63c671c7ff

def z766 : W := mkw 0x4273cd368445ca28 0xd3a80fb587db00d9 0x0e7fffffc001ff2c 0xc3f80ffdc7fe00f8

def z767 : W := mkw 0x885c71c9392003d1 0x03fff6eedab6db00 0xff9ffe0fc1f803f0 0x03fffffffffff800

def z768 : W := mkw 0xf5a38e34c69bf5ae 0xe8804fff7d4924ff 0xff8000000001fc30 0xfc000ffff80000ff

def z769 : W := mkw 0xf2a492c25e4e7dae 0x1855794bb525b7e7 0xfffffe003ffff2fb 0xbf07ff83ff81ffc7

def z770 : W := mkw 0x885c71c939200251 0x037fb00c12b6db00 0x007ffffffffe03cf 0x03fff01c07ffff00

def z771 : W := mkw 0x20734f348201a228 0xc3aa8fb46fda20da 0xfffffffffe39ffbe 0xffff8ffffffe38ff

def z772 : W := mkw 0x8800000000000190 0x00a846eed8000000 0xff80000000000130 0x00f80ffff8000000

def z773 : W := mkw 0xd22580a214455986 0x1011684b1461856d 0xf1ff81fe3fc7ffff 0xfd19f1fe3e71c7ff

def z774 : W := mkw 0x0011453480018200 0x43a806b4005a0018 0x000001ffc0000d04 0x42f80e7c007e0038

def z775 : W := mkw 0x88000000000003d0 0x03bbe6eed8000000 0xff80000000000330 0x03f98ffff8000000

def z776 : W := mkw 0x8800000000000250 0x033ba28c58000000 0xff80000000000030 0x01198f9ff8000000

def z777 : W := mkw 0x522580a214455806 0x10c41c218461856d 0x0e7f81fe3fc7ffcf 0xfee67e01c671c7ff

def z778 : W := mkw 0x60628a0006006228 0x83000b81278120c3 0xfffffe003ff9f2ba 0xbf078f83ff81f8c7

def z779 : W := mkw 0x8000000000000380 0x03bbe6ee58000000 0xff800000000003f0 0x03fffffff8000000

def z780 : W := mkw 0x0011453480018028 0x40a80534015a0098 0x000001ffc001fd24 0xc0f801fc007e00f8

def z781 : W := mkw 0xed6aaa00269061f8 0xa0fd7d6fb78168c3 0x007ffe003ff9f14a 0xbcf8707c0781f8c7

def z782 : W := mkw 0x007b6d3da1218269 0xc3aa8fb407da48d8 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z783 : W := mkw 0x522580a214455986 0x10c45c638461856d 0xfe7ffffe3fffffef 0xffe7fe63c7f1ffff

def z784 : W := mkw 0x777fefb6b6d5f82e 0xf000091127fbedff 0x007ffffffffffc0f 0xfc00000007ffffff

def z785 : W := mkw 0x00734d3480018228 0xc328091007da00d8 0x007fffffc001ff2c 0xc3f801fc07fe00f8

def z786 : W := mkw 0x9a1551eb19651bd7 0x13fff6eed876972c 0xff8001ffc0060ff5 0x43fffffff87e0738

def z787 : W := mkw 0x88544180100003d0 0x03fff6eedab28100 0xffffffffffc603ff 0x03ffffffffffc700

def z788 : W := mkw 0x88000000000003d0 0x0357f2cad8000000 0xff800000000003f0 0x031ffffff8000000

def z789 : W := mkw 0x6573cf348691e028 0xe000091127db20db 0x007fffffc001fc0c 0xfc00000007fe00ff

def z790 : W := mkw 0x6573cf348691e228 0xe3a80fb527db20db 0x007fffffc001ff2c 0xfff80ffc07fe00ff

def z791 : W := mkw 0x75eaae10669af42e 0xa800091127896cf7 0x007ffe003ff9fc0a 0xfc0000000781f8ff

def z792 : W := mkw 0x9a8514f2584f9dd6 0x18fd747e906c973c 0x000001ffc0060d45 0x40f8707c007e0738

def z793 : W := mkw 0xda2580a214455a56 0x133baa8d5c61856d 0x01ff81fe3fc7fc1f 0xfd19819c3e71c7ff

def z794 : W := mkw 0xb0dc6799732ab7ef 0x0b6ed15a33baedb6 0xf19f800e01c1fc30 0xfee601fe3e71c0ff

def z795 : W := mkw 0x0000000000000200 0x0302828048000000 0xff800000000003b0 0x031f8ffff8000000

def z796 : W := mkw 0x6528a20026906000 0x200288016c016843 0xff9f80003ff80092 0x3e078e03fe01f807

def z797 : W := mkw 0x928410c2584e1d86 0x1855704a90249724 0x0000000000060041 0x0000700000000700

def z798 : W := mkw 0x00334d3480018028 0xc0a80d34055a00d8 0x000001ffc001fd04 0xc0f8007c007e00f8

def z799 : W := mkw 0x75fbff74ee9bf42e 0xe800091127df7eff 0x007ffffffffffc0f 0xfc00000007ffffff

def z800 : W := mkw 0x88000000000003d0 0x03bbe6eed8000000 0xff800000000002b0 0x031f8ffff8000000

def z801 : W := mkw 0x8800000000000190 0x009166eed8000000 0xff800000000000f0 0x0001fffff8000000

def z802 : W := mkw 0x6548a20026906200 0x230282816a816803 0xfffffe003ff802ba 0x3f078f83ff81f807

def z803 : W := mkw 0x9a0500a210451bd6 0x13fff6eed860852c 0xffff81fe3fc60fff 0x43fffffffe71c738

def z804 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0xfffffe003ff9f3ba 0xbf1f8fffff81f8c7

def z805 : W := mkw 0x0071412000010200 0x03a80ea406d20048 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z806 : W := mkw 0x72f7dff6de4ffc2e 0xd800091127ffb7ff 0x007ffffffffffc0f 0xfc00000007ffffff

def z807 : W := mkw 0x4073cd348401c228 0xc3a80fb507db00d9 0x007fffffffc1ff2e 0xfff80ffc07ffc0ff

def z808 : W := mkw 0x88400000000003d0 0x03fff6eeda800000 0xfffffe00000003f8 0x03ffffffff800000

def z809 : W := mkw 0x656aae14a690e228 0xe3028b956f8968d3 0xfffffe003ff9f2ba 0xbf078f9fff81f8c7

def z810 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x007ffffffe39ffae 0xc3f98ffc07fe38f8

def z811 : W := mkw 0x8800000000000190 0x008046eed8000000 0xff80000000000330 0x02e00ffff8000000

def z812 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xff80000000000030 0x03ff8ffff8000000

def z813 : W := mkw 0x656bae34a691e228 0xe3028b916fc968db 0xfffffe003ff9feba 0xff078f83ff81f8ff

def z814 : W := mkw 0x657bef34a691e228 0xe32a8b956fdb68db 0xfffffffffff9febe 0xff1f8f9ffffff8ff

def z815 : W := mkw 0x88104100000003d0 0x03fff6eed8120000 0xff8001ffc00003f4 0x03fffffff87e0000

def z816 : W := mkw 0x388016504a0ab67e 0x0bee97b4e90c36b6 0x0e607ff1fe3ffc0f 0xfee60e01c18e3fff

def z817 : W := mkw 0x6536dbc91fb06069 0xa07d3b816d37b3c3 0xff8001ffc007f175 0xbcf87f83f87e07c7

def z818 : W := mkw 0x6573cf348691e228 0xe3a80fb56fdb20db 0xfffffffffe39ffbe 0xfff98ffffffe38ff

def z819 : W := mkw 0x88587149292003d1 0x03fff6eeda965a00 0xffe07ff1fe3e03ff 0x03fffffff98e3f00

def z820 : W := mkw 0x0011453480018000 0x40a806b4005a0018 0x000001ffc0000d24 0x40f80ffc007e0038

def z821 : W := mkw 0x88000000000003d0 0x037ff2ced8000000 0xff800000000002f0 0x031fff9ff8000000

def z822 : W := mkw 0x00334d3480018028 0xc0a80fb4055a00d8 0x007f81ffc001ff2c 0xc2f80ffc067e00f8

def z823 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0xfffffe003ff9f09a 0xbe078e03ff81f8c7

def z824 : W := mkw 0x88001040080003d0 0x03fff6eed8041200 0xff8000003e3e03f3 0x03fffffff8003f00

def z825 : W := mkw 0x657aeb0026906228 0xa3028b816f9368c3 0xfffffffffff9f2be 0xbf078f83fffff8c7

def z826 : W := mkw 0x00334d3480018228 0xc3a80fb4055a00d8 0x000001ffc001ff24 0xc3f80ffc007e00f8

def z827 : W := mkw 0xda2580a214455996 0x10c45c6f9461856d 0xfe7f81fe3fc7ffef 0xfee67e7fc671c7ff

def z828 : W := mkw 0x88000000000003d0 0x03aac6eed8000000 0xff80000000000030 0x00000ffff8000000

def z829 : W := mkw 0x805c71c9392003c1 0x037ff2ca5ab6db00 0xfffffffffffe03ff 0x03ffffffffffff00

def z830 : W := mkw 0x885451c9192003d1 0x03fff6eedab69300 0xffffffffc00603fd 0x03fffffffffe0700

def z831 : W := mkw 0x005c71c939200241 0x036e900002b6db00 0x007ffffffffe03cf 0x02e6700007ffff00

def z832 : W := mkw 0x522580a214455986 0x10c45c638461856d 0xfe7fffffffc7ffef 0xfffe7e63c7ffc7ff

def z833 : W := mkw 0x00734d3480018228 0xc3a80fb44fda00d8 0xffffffffc001ff3c 0xc3f80ffffffe00f8

def z834 : W := mkw 0x652aaa0026906000 0xa0028a816c016843 0xff8000003ff80092 0x3c078e03f801f807

def z835 : W := mkw 0x8800000000000190 0x0082c6eed8000000 0xff800000000000b0 0x00078ffff8000000

def z836 : W := mkw 0xe2a596f25e4fec28 0x18d53d39b56db3db 0x0f9ffe0fc1f80010 0x03ff8f9dfffff800

def z837 : W := mkw 0x6573cf348691e228 0xe3aa8fb56fdb20db 0xffffffffc001ffbc 0xffff8ffffffe00ff

def z838 : W := mkw 0x000c30c939200041 0x0057b0000024db00 0x007ffffffffe03cf 0x03fff00007ffff00

def z839 : W := mkw 0x300006100200b1ae 0x00004152210824b6 0xf1e07ff1fe3fffff 0xfd19f1fe398e3fff

def z840 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xffff80003fc003fa 0x03fffffffe01c000

def z841 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0xfffffff03ff9ffbe 0xff078fe3ff81f8ff

def z842 : W := mkw 0x6519e734a691e000 0x60aa8435685b681b 0xff8001fffff80d96 0x7cff807ff87ff83f

def z843 : W := mkw 0x6508a20026906228 0x2302838169016883 0xffe07e003ff9f2ba 0xbf078f83f981f8c7

def z844 : W := mkw 0x374f2aa232d53bae 0xb3c6d7e2ebe0edae 0x01807ffe003e0d55 0x41e1f1e039f03f38

def z845 : W := mkw 0x0000000000000240 0x03ffb6a448000000 0xff800000000003f0 0x03fffffff8000000

def z846 : W := mkw 0x88000000000001d0 0x00d7f6eed8000000 0xff800000000003f0 0x02e7fffff8000000

def z847 : W := mkw 0x457bed34a491c228 0xe3aa8fb54fdb48d9 0x0e7ffffffff9ffae 0xc3ff8ffdc7fff8f8

def z848 : W := mkw 0x8800000000000190 0x00c456eed8000000 0xff80000000000030 0x02e60ffff8000000

def z849 : W := mkw 0x70a096504e0af42e 0x08000911250d36f7 0x007ffff1fffffc0f 0xfc000000078fffff

def z850 : W := mkw 0x88000000000003d0 0x03eed6eed8000000 0xff800000000003f0 0x02e67ffff8000000

def z851 : W := mkw 0x007b6d34a0018228 0xc3a80fb407da48d8 0x007ffffffff9ff2e 0xc3f80ffc07fff8f8

def z852 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xffe07e003e3803fa 0x03fffffff9803800

def z853 : W := mkw 0x75a29e504e9af42e 0xa8000911250d36f7 0x00607ff1fe3ffc0f 0xfc000000018e3fff

def z854 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0xfe7ffffffffe03ef 0x03fffe03c7ffff00

def z855 : W := mkw 0x657bef34a691e228 0xe3aa8fb56fdb68db 0xffffffffc039ff3c 0xfff98ffffffe38ff

def z856 : W := mkw 0x6528a20026906000 0x200288016c016843 0xff8000003ff9f0b2 0xbc078e03f801f8c7

def z857 : W := mkw 0x0011453480018028 0x40a80534015a0098 0x00007fffc0000d04 0x41f801fc01fe0038

def z858 : W := mkw 0x5279f16b2d655bc7 0x13bbec6386d75e6d 0xfe007e01c039fc20 0xfd198e63c18e38ff

def z859 : W := mkw 0x407bed34a401c228 0xc3aa8fb507db48d9 0xfe7ffffffff9ffae 0xffff8fffc7fff8ff

def z860 : W := mkw 0x00334d3480018028 0xc0a80fb4055a00d8 0x00607fffc001ff2c 0xc1f80ffc01fe00f8

def z861 : W := mkw 0x657aef102690e228 0xa32a8b916f9b68d3 0xfffffffffff9ffbe 0xffff8ffffffff8ff

def z862 : W := mkw 0x88000000000001d0 0x00b966eed8000000 0xff80000000000030 0x00180ffff8000000

def z863 : W := mkw 0xf78cb2c27ede7d86 0x3857f04bf825ff27 0xff8000003ffe00d3 0x3c07f003f801ff07

def z864 : W := mkw 0x77efbef27edffc2e 0xb800091127edffff 0x007ffffffffffc0f 0xfc00000007ffffff

def z865 : W := mkw 0x005c71c939200041 0x007d300002b6db00 0x007ffffffffe03cf 0x01f9f00007ffff00

def z866 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x007fffffffc1ffae 0xc3fe0ffc07ffc0f8

def z867 : W := mkw 0x0050451000008228 0x03a807b4039a0090 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z868 : W := mkw 0x5021802004015186 0x00804c630441046d 0xfe7f81fe3fc7ffef 0xfee67e63c671c7ff

def z869 : W := mkw 0x8800000000000190 0x00d576eed8000000 0xff800000000003f0 0x03fffffff8000000

def z870 : W := mkw 0x005c71c939200001 0x0055300002b6db00 0x007ffffffffe03cf 0x03fff00007ffff00

def z871 : W := mkw 0x657bef34a691e228 0xe3a80fb527db68db 0xf1fffffffff9ffbe 0xfff98ffe3ffff8ff

def z872 : W := mkw 0x6568a20026906200 0x230288016e816843 0xfffffe003ff9f2ba 0xbf078e03ff81f8c7

def z873 : W := mkw 0x005c71c939200241 0x037fb2804ab6db00 0x01fffffffffe03df 0x03fff1803fffff00

def z874 : W := mkw 0x00734d3480018228 0xc3aa8fb44fda00d8 0x0e7fffffc001ff2c 0xc3fe0ffdc7fe00f8

def z875 : W := mkw 0x522580a214455806 0x104418010461856d 0xfe7f81fe3fc7ffef 0xfee67e03c671c7ff

def z876 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xffff81fe000003fc 0x03fffffffe700000

def z877 : W := mkw 0x657ffffdbfb1e029 0xe000091127fffbdb 0x007ffffffffffc0f 0xfc00000007ffffff

def z878 : W := mkw 0xa8d877596b2aa679 0x0b3ba39c7b9e7a92 0x01807e01c0380010 0x0119819c398e3800

def z879 : W := mkw 0x885c71c939200191 0x008046eedab6db00 0xfffffffffffe003f 0x00000fffffffff00

def z880 : W := mkw 0x207b6f34a201a228 0xc3aa8fb427da68da 0xf1fffffffff9ffbe 0xffff8ffe3ffff8ff

def z881 : W := mkw 0x055e79c939b00241 0xa37fb2804ab6db00 0x007ffffffffe03cf 0x03fff00007ffff00

def z882 : W := mkw 0x0000041000008028 0x0000011001080090 0x007fffffc001ff2c 0xc3f801fc07fe00f8

def z883 : W := mkw 0x65238e348691e028 0xe0000911254920db 0x000000000001fc00 0xfc000000000000ff

def z884 : W := mkw 0x4a7de1ab35654a51 0x13ee9ea5cef3c949 0x0e1f800e01c00000 0x02e60e01c671c000

def z885 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xff800000000000d0 0x03ffff9ff8000000

def z886 : W := mkw 0x657aef14a690e228 0xe32a8b956f9b68d3 0xfffffffffff9f3be 0xbfff8f9ffffff8c7

def z887 : W := mkw 0xfa8492c25e4e7dd6 0x1857f04bf825b727 0xff8000003ffe00d3 0x3c07f003f801ff07

def z888 : W := mkw 0x88040080100003d0 0x03fff6eed8208100 0xff8001fe000603f5 0x03fffffff8700700

def z889 : W := mkw 0x255a7f5dabb0a269 0xe33ba3946b9e7a92 0x01807e01c0380010 0x0119819c398e3800

def z890 : W := mkw 0x0071453480018200 0x43a80c3406da0058 0x007fffffc001ff2c 0xc3f80e7c07fe00f8

def z891 : W := mkw 0x2048220022002228 0x030283806b806882 0xfffffe003ff9f2ba 0xbf078f83ff81f8c7

def z892 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0xff9ffe003ff80092 0x3f078f83ff81f807

def z893 : W := mkw 0x085c71c939200251 0x037fb2844ab6db00 0x007ffffffffe03cf 0x03fff00007ffff00

def z894 : W := mkw 0x657aef14a690e228 0xe3028b916f9b68d3 0xfffffe01fff9f2ba 0xbf078f83ff8ff8c7

def z895 : W := mkw 0x522580a214455986 0x10c45c638461856d 0xfe7f81fe3fc7ffef 0xfffe7fffc671c7ff

def z896 : W := mkw 0x657bef34a691e228 0xe3aa8fb56fdb68db 0x0fffffffc1f9ff3c 0xc3ff8ffdfffff8f8

def z897 : W := mkw 0x65eabe506e9ae428 0xa8000911278d7ad3 0x007ffe01fff9f00a 0xbc000000078ff8c7

def z898 : W := mkw 0x8800000000000250 0x03bba6ac58000000 0xff800000000003b0 0x03ff8ffff8000000

def z899 : W := mkw 0x88505140080003d0 0x03fff6eeda961200 0xfffffffffe3e03ff 0x03fffffffffe3f00

def z900 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0x007ffffffffe014f 0x02fe700007ffff00

def z901 : W := mkw 0x98001040080013d6 0x03fff6eed8041624 0xffe07ff1fe3fffff 0xfffffffff98e3fff

def z902 : W := mkw 0xb88c32c97b2a35d7 0x0857f04af824ff26 0xff8000003ffe00d3 0x3c07f003f801ff07

def z903 : W := mkw 0x880c30c9392003d1 0x03fff6eed824db00 0xffe07ff1fffe03ff 0x03fffffff98fff00

def z904 : W := mkw 0x8800000000000250 0x03bba6acd8000000 0x0f80000000000010 0x01198f9df8000000

def z905 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0x01e07ff1fe3ffd5f 0xfd19f1fc398e3fff

def z906 : W := mkw 0x8000000000000180 0x0011604a10000000 0xff800000000003f0 0x031ffffff8000000

def z907 : W := mkw 0x00734d3480018028 0xc0a80d3407da00d8 0x007fffffc001ff2c 0xc2f80e7c07fe00f8

def z908 : W := mkw 0x257b6f34a291a228 0xe3a80fb427da68da 0x007fffffc039ff2c 0xc3f80ffc07fe38f8

def z909 : W := mkw 0x6d6aaa0026906278 0xa32a8b856f8168c3 0xfffffe003ff9f2ba 0xbf078f83ff81f8c7

def z910 : W := mkw 0x00596534a0018200 0x43aa843402da4818 0x007ffffffff80f8e 0x43ff807c07fff838

def z911 : W := mkw 0x8000000000000380 0x03d7f6ead8000000 0xff800000000003f0 0x03fffffff8000000

def z912 : W := mkw 0x257b6f34a291a228 0xe3aa8fb46fda68da 0xf1fffffffe39ffbe 0xfff98ffe3ffe38ff

def z913 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0xf1fffffffe3fffff 0xfff9f1fe3ffe3fff

def z914 : W := mkw 0x402580a014014000 0x00c41c2104618149 0xfe7f81fe3fc7ffef 0xfee67e63c671c7ff

def z915 : W := mkw 0x004c30c038000200 0x0357b00002a4db00 0x007ffffffffe03cf 0x03fff00007ffff00

def z916 : W := mkw 0x88144189112003d1 0x03fff6eed8328100 0xff80000e000003f0 0x03fffffff8700000

def z917 : W := mkw 0x657bef34a691e028 0xe0a80d3527db68db 0x007ffffffff9fd0e 0xfcf8007c07fff8ff

def z918 : W := mkw 0x8800000000000190 0x008046eed8000000 0xff800000000003f0 0x00007ffff8000000

def z919 : W := mkw 0x989455d9592a95d7 0x08fd747e903e9734 0x000001ffc0060d45 0x40f8707c007e0738

def z920 : W := mkw 0x885c71c939200251 0x03ffb6acdab6db00 0x0ffffffffffe03df 0x03ffff9dffffff00

def z921 : W := mkw 0x00134d3480018028 0xc0a807b4015a0098 0x000001ffc0000d04 0x40f801fc007e0038

def z922 : W := mkw 0x72a196724e4ffc2e 0x18000911254d36ff 0x00607ff1fe3ffc0f 0xfc000000018e3fff

def z923 : W := mkw 0x007b6d34a0018228 0xc3aa8fb407da48d8 0x007fffffc039ff2c 0xc3f98ffc07fe38f8

def z924 : W := mkw 0x6508a20026906000 0x2002828168016803 0xff8000003ff800b2 0x3c078f83f801f807

def z925 : W := mkw 0x88483040280003d0 0x03fff6eeda845a00 0xfffffff1fffe03ff 0x03ffffffff8fff00

def z926 : W := mkw 0x656aaa0026906228 0xa32a8b816f8168c3 0xfffffe003ff9f3ba 0xbfff8f83ff81f8c7

def z927 : W := mkw 0x88000000000003d0 0x03eed6eed8000000 0xff80000000000330 0x03fe0ffff8000000

def z928 : W := mkw 0x00534d3480018028 0xc0a8053403da0098 0x00007fffc0000d04 0x40f8007c01fe0038

def z929 : W := mkw 0x00734d3480018228 0xc3aa8fb407da00d8 0x007fffffc001ffac 0xc3ff8ffc07fe00f8

def z930 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x007ffffffe07ffef 0xc3f87ffc07fe07f8

def z931 : W := mkw 0x88000000000001d0 0x00fd746e90000000 0xff800000000003f0 0x03fffffff8000000

def z932 : W := mkw 0x88504100000003d0 0x03fff6eeda920000 0xff9f800e000003f0 0x03fffffffe700000

def z933 : W := mkw 0x8800000000000010 0x008006acd8000000 0x0f80000000000010 0x00000f9df8000000

def z934 : W := mkw 0x885c71c939200251 0x037fb0085ab6db00 0x01fffffffffe03df 0x03fff0003fffff00

def z935 : W := mkw 0x477fe9a6b4d54a00 0xf3ee9ea5cef3c949 0x0e1f800e01c00000 0x02e60e01c671c000

def z936 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0xfffffff03ffff3ff 0xbf07ff83ff81ffc7

def z937 : W := mkw 0x88587149292003d1 0x03bbe6eeda965a00 0xff807e01c0380030 0x01198ffff98e3800

def z938 : W := mkw 0x88001040080003d0 0x03fff6eed8041200 0xff807e01c03803f0 0x03fffffff98e3800

def z939 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0xfe7fffffc001ffac 0xc3fe0fffc7fe00f8

def z940 : W := mkw 0x005c71c939200201 0x0346900002b6db00 0x007ffffffffe03cf 0x03e7f00007ffff00

def z941 : W := mkw 0x9a01002200451996 0x108046eed840042c 0xff80000000000c30 0x40000ffff8000038

def z942 : W := mkw 0x457bed34a491c228 0xe3aa8fb54fdb48d9 0xfe7fffffffc1ffae 0xfffe0fffc7ffc0ff

def z943 : W := mkw 0x72a18632464ffdae 0x18804d73a54924ff 0xfe0000000001fc20 0xfc000e63c00000ff

def z944 : W := mkw 0x0011453480018028 0x40a80534015a0098 0x00607fffc001fd0c 0xc0f8007c01fe00f8

def z945 : W := mkw 0x0001043000018028 0x0080053001480098 0x00607fffc001ff2c 0xc1f801fc01fe00f8

def z946 : W := mkw 0x0800000000000250 0x03ee96a4c8000000 0xff800000000003b0 0x03ff8ffff8000000

def z947 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0xffe07ff1fe3fffff 0xff1ffffff98e3fff

def z948 : W := mkw 0x72a596f25e4ffc2e 0x18553911256db7ff 0x007fffffffffffcf 0xfffff00007ffffff

def z949 : W := mkw 0x6528a20026906028 0x200289016d0168c3 0xfffffe003ff9f2ba 0xbf078f83ff81f8c7

def z950 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0xff807e003ff9f0b2 0xbd078f83f981f8c7

def z951 : W := mkw 0x98000000000013d6 0x03fff6eed8000424 0xff8000003e0603f3 0x3ffffffff8000707

def z952 : W := mkw 0x657beb24a6916228 0xe3028b816fd368cb 0xfffffe0e3ff9f2ba 0xbf078f83fff1f8c7

def z953 : W := mkw 0x657bef34a691e228 0xe3a80fb527db68db 0xfe7ffffffff9ffae 0xfffe0fffc7fff8ff

def z954 : W := mkw 0x005c71c939200241 0x03ffb6a44ab6db00 0xfffffffffffe03ff 0x03ffffffffffff00

def z955 : W := mkw 0x00534d3480018228 0xc3a807b403da0098 0x00607fffc001ff2c 0xc1f801fc01fe00f8

def z956 : W := mkw 0x00534d3480018228 0xc3a807b403da0098 0x00007fffc0000f24 0x43f80ffc01fe0038

def z957 : W := mkw 0x88587149292003d1 0x03fff6eeda965a00 0xfffffe01fff803fa 0x03ffffffff8ff800

def z958 : W := mkw 0x72a18632464ffc2e 0x18000911254924ff 0x000000000001fc00 0xfc000000000000ff

def z959 : W := mkw 0x0010451000008000 0x00280010001a0010 0x000001ffc0000d04 0x40f8007c007e0038

def z960 : W := mkw 0x885c71c9392003d1 0x03fff6eedab6db00 0xff807e01fffe03f3 0x03fffffff98fff00

def z961 : W := mkw 0x08734d3480018238 0xc3a80fb4cfda00d8 0x0e7fffffc001ff2c 0xc3f80ffdc7fe00f8

def z962 : W := mkw 0x005c71c939200241 0x037fb2804ab6db00 0x0e7ffffffffe03cf 0x03fffe01c7ffff00

def z963 : W := mkw 0x200016500a00a028 0x00112110210c3292 0xf1e07ff1fe3fffff 0xfd19f1fe398e3fff

def z964 : W := mkw 0x308016504a0ab5ae 0x08c45572a10c36b6 0xfe607ff1fe3fffef 0xfee67e63c18e3fff

def z965 : W := mkw 0x0011453480018228 0x43a807b4015a0098 0x00607fffc001ff2c 0xc3f80ffc01fe00f8

def z966 : W := mkw 0x80000000000003c0 0x03fff46a90000000 0xff800000000003f0 0x03fffffff8000000

def z967 : W := mkw 0x007b6d34a0018228 0xc3aa8fb407da48d8 0x007fffffc1c1ff2c 0xc3fe0ffc07ffc0f8

def z968 : W := mkw 0x8848200020000390 0x0382c6eeda804800 0xfffffe003ff802ba 0x03078fffff81f800

def z969 : W := mkw 0x0000000000000380 0x03eed6e6c8000000 0xff800000000003f0 0x03fffffff8000000

def z970 : W := mkw 0x001451c919200041 0x007d300000369300 0x007ffffffffe03cf 0x03fff00007ffff00

def z971 : W := mkw 0x00734d3480018000 0xc0a80c3406da0058 0x001f81ffc0000d04 0x40f8007c067e0038

def z972 : W := mkw 0x005c618030000200 0x036e900002b2c900 0x007ffffffffe03cf 0x03fff00007ffff00

def z973 : W := mkw 0x880410c0180003d0 0x03fff6eed8249300 0xfffffffffffe03ff 0x03ffffffffffff00

def z974 : W := mkw 0x656bae34a691e028 0xe000091127c968db 0x007ffe003ff9fc0a 0xfc0000000781f8ff

def z975 : W := mkw 0x6573cf348691e228 0xe3a80fb56fdb20db 0xffffffffffc1ffbe 0xfffe0fffffffc0ff

def z976 : W := mkw 0x88000000000001d0 0x0093e6eed8000000 0xff80000000000030 0x00018ffff8000000

def z977 : W := mkw 0x201147348201a028 0x40a80534215a209a 0xf1e07ffffe39ffbe 0xfdf981fe39fe38ff

def z978 : W := mkw 0x884c30c9392003d1 0x03fff6eedaa4db00 0xfffffe003ffe03fb 0x03ffffffff81ff00

def z979 : W := mkw 0x885c71c9392003d1 0x03fff6eedab6db00 0xff9f81ffc1c603f5 0x03fffffffe7fc700

def z980 : W := mkw 0x88586109212003d1 0x03fff6eeda924800 0xff800000000003f0 0x03fffffff8000000

def z981 : W := mkw 0x0011453480018000 0x40a80434005a0018 0x000001ffc0000f24 0x41f801fc007e0038

def z982 : W := mkw 0xb08412c05a0a3586 0x0855704a3024b726 0xf18000003ffe00d3 0x3c07f0023801ff07

def z983 : W := mkw 0x9000104008001186 0x0011604a10041624 0xf1e07ff1fe3fffff 0xfd19f1fe398e3fff

def z984 : W := mkw 0x457bed34a491c228 0xe3aa8fb54fdb48d9 0xffffffffc1c1ffbc 0xc3ff8fffffffc0f8

def z985 : W := mkw 0x00534d3480018228 0xc3a807b403da0098 0x007fffffc0000f0c 0x43f801fc07fe0038

def z986 : W := mkw 0x656aae102690e228 0xa3028b916f8968d3 0xfffffe01fff9f2ba 0xbf1f8f9fff8ff8c7

def z987 : W := mkw 0x0000000000000200 0x032a828448000000 0xff800000000002b0 0x031f8f9ff8000000

def z988 : W := mkw 0x20734f348201a228 0xc3a80fb427da20da 0x007ffffffe39ff2e 0xfff80ffc07fe38ff

def z989 : W := mkw 0x8800000000000390 0x03c6d6eed8000000 0xff800000000003f0 0x03e7fffff8000000

def z990 : W := mkw 0x72a586b2564ffc2e 0x180009112569a5ff 0x007f81fe3fc7fc0f 0xfc0000000671c7ff

def z991 : W := mkw 0x885c71c9392003d1 0x03fff6eedab6db00 0xff807fffc03e03f5 0x03fffffff9fe3f00

def z992 : W := mkw 0x8800000000000250 0x037fb28c58000000 0xff800000000003f0 0x03ffff9ff8000000

def z993 : W := mkw 0x9800000000001196 0x008046eed8000424 0xffe001f03e07ffff 0xfc007ffff80007ff

def z994 : W := mkw 0x77238e3686d5f9ae 0xf0804ff7ed4924ff 0xff8000000001fc30 0xfc000ffff80000ff

def z995 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0x007ffffffffe014f 0x01f9f00007ffff00

def z996 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x007fffffc001fd0c 0xc1f801fc07fe00f8

def z997 : W := mkw 0x657bef34a691e228 0xe3a80fb56fdb68db 0xfffffffffff9ff3e 0xfff80ffffffff8ff

def z998 : W := mkw 0x8000000000000180 0x00c4546a90000000 0xff800000000003f0 0x02e67ffff8000000

def z999 : W := mkw 0x656aaa0026906200 0xa3028a816e816843 0xffff80003ff9f2ba 0xbe078e03fe01f8c7

def z1000 : W := mkw 0x057b6d34a0918228 0xe3aa8fb44fda48d8 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z1001 : W := mkw 0x75feffd97fbaf66f 0xab7fb91127bffff7 0x007fffffffffffcf 0xfffff00007ffffff

def z1002 : W := mkw 0x522580a214455986 0x10c45c638461856d 0x0e7f81fe3fc7fd4f 0xfee67e61c671c7ff

def z1003 : W := mkw 0x00724d1000008228 0x83280b90079a00d0 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z1004 : W := mkw 0xa5da7f54ea9aa628 0xeb3ba39c7b9e7a92 0x01807e01c0380010 0x0119819c398e3800

def z1005 : W := mkw 0x657bef34a691e228 0xe3aa8fb56fdb68db 0x01fffffffff9ff3e 0xfff98ffc3ffff8ff

def z1006 : W := mkw 0x8800000000000190 0x009166eed8000000 0xff80000000000030 0x01198ffff8000000

def z1007 : W := mkw 0x929555f6d84f9d86 0x58fd747e907e973c 0x000001ffc0060d45 0x40f8707c007e0738

def z1008 : W := mkw 0x8800000000000390 0x038046eed8000000 0xff80000000000230 0x03000ffff8000000

def z1009 : W := mkw 0x88000000000003d0 0x03bbe6eed8000000 0xff800000000003f0 0x0119fffff8000000

def z1010 : W := mkw 0x656aaa0026906228 0xa32a8b856f8168c3 0xfffffe003ff9f2ba 0xbf1f8f9fff81f8c7

def z1011 : W := mkw 0x880c30c9392001d1 0x00d7f6eed824db00 0xff8000003ffe00f3 0x0007fffff801ff00

def z1012 : W := mkw 0x8800000000000390 0x03a846eed8000000 0xff80000000000030 0x01180ffff8000000

def z1013 : W := mkw 0x885c6189312003d1 0x03fff6eedab2c900 0xffffffffc1c003fc 0x03ffffffffffc000

def z1014 : W := mkw 0x205867102200a228 0x032a8110239a6892 0xf1fffffffff9ffbe 0xffff81fe3ffff8ff

def z1015 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0x0f80000000000150 0x03fffffdf8000000

def z1016 : W := mkw 0x00734d3480018028 0xc0800d3007da00d8 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z1017 : W := mkw 0x005c71c939200001 0x0044100002b6db00 0x007ffffffffe014f 0x00e0700007ffff00

def z1018 : W := mkw 0x000410c018000240 0x037fb00000249300 0x007ffffffffe03cf 0x03fff00007ffff00

def z1019 : W := mkw 0x88040080100003d0 0x03fff6eed8208100 0xff9f800e01c003f0 0x03fffffffe71c000

def z1020 : W := mkw 0x0031453480018000 0x40a80c34045a0058 0x000001ffc001fd24 0xc0f80e7c007e00f8

def z1021 : W := mkw 0xd22580a214455986 0x10c45c6b9461856d 0xffff81fe3fc7ffff 0xfee67ffffe71c7ff

def z1022 : W := mkw 0x88000000000003d0 0x03fd76eed8000000 0xff80000000000370 0x03f87ffff8000000

def z1023 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xff80000000000170 0x01f9fffff8000000

def z1024 : W := mkw 0x8048304028000380 0x0313e2ca5a845a00 0xfffffff1fffe03ff 0x031fffffff8fff00

def z1025 : W := mkw 0x75a28e10469af42e 0xa8000911250924f7 0x000000000001fc00 0xfc000000000000ff

def z1026 : W := mkw 0x657bef34a691e228 0xe3aa8fb56fdb68db 0xffffffffc1c1ff3c 0xfffe0fffffffc0ff

def z1027 : W := mkw 0x005c71c939200041 0x007fb00002b6db00 0x007ffffffffe01cf 0x00fff00007ffff00

def z1028 : W := mkw 0x0058714028000200 0x033ba00002965a00 0x007ffffffffe03cf 0x03fff00007ffff00

def z1029 : W := mkw 0x885c6189312003d1 0x03fff6eedab2c900 0xffff81fe3fc603ff 0x03fffffffe71c700

def z1030 : W := mkw 0x8000000000000200 0x0313a28858000000 0xff800000000002b0 0x031f8f9ff8000000

def z1031 : W := mkw 0x885c6189312003d1 0x03eed6eedab2c900 0xff9f800e01c00030 0x02e60ffffe71c000

def z1032 : W := mkw 0x0051453480018200 0x43a8043402da0018 0x001f81ffc0000d04 0x42f8007c067e0038

def z1033 : W := mkw 0x881c71c9392003d1 0x03fff6eed836db00 0xff8001fffffe03f7 0x03fffffff87fff00

def z1034 : W := mkw 0x656aae102690e228 0xa3028b916f8968d3 0xfffffff1fff9febe 0xff078f83ff8ff8ff

def z1035 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0xf1807ff1c03ffd75 0xfd19f1fe398e3fff

def z1036 : W := mkw 0x8804008010000190 0x00c456eed8208100 0xffff81fe3fc603ff 0x02e67ffffe71c700

def z1037 : W := mkw 0x88114124800103d0 0x43fff6eed8520008 0xff80000e000003f0 0x03fffffff8700000

def z1038 : W := mkw 0x000410c018000000 0x0044100000249300 0x007ffffffffe03cf 0x02e6700007ffff00

def z1039 : W := mkw 0x8800000000000390 0x03aac6eed8000000 0xff800000000003b0 0x03ff8ffff8000000

def z1040 : W := mkw 0x9a04008210441bd6 0x13fff6eed8208524 0xff800000000603f1 0x03fffffff8000700

def z1041 : W := mkw 0x0050451000008200 0x03280010029a0010 0x007fffffc0000f0c 0x43f8007c07fe0038

def z1042 : W := mkw 0x881451c9192001d1 0x00fd76eed8369300 0xff8001ffc0060175 0x00f87ffff87e0700

def z1043 : W := mkw 0x80000000000003c0 0x037ff2ca58000000 0xff800000000003f0 0x03fffffff8000000

def z1044 : W := mkw 0x657aeb04a6906228 0xe32a8b856f9368c3 0xfffffe003ff9f2ba 0xbf078f83ff81f8c7

def z1045 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0xf07ffffffe01ffae 0xfff80ffe07fe00ff

def z1046 : W := mkw 0x20734f348201a228 0xc3a80fb427da20da 0x01ffffffc039ff3c 0xc3f98ffc3ffe38f8

def z1047 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xff800000000000f0 0x011ffffff8000000

def z1048 : W := mkw 0x88524904800003d0 0xc3fff6eeda920000 0xff800000000003f0 0x03fffffff8000000

def z1049 : W := mkw 0x88083049292003d1 0x03fff6eed8045a00 0xff800000003803f0 0x03fffffff8003800

def z1050 : W := mkw 0x005451c018000200 0x037d300002b69300 0x007ffffffffe03cf 0x03fff00007ffff00

def z1051 : W := mkw 0xb08412c95b2a35c7 0x0855704a3024b726 0xf18000003e3e00d3 0x3c01f00238003f07

def z1052 : W := mkw 0x005c71c939200241 0x037fb28002b6db00 0x007ffffffffe03ef 0x03ffff8007ffff00

def z1053 : W := mkw 0x4031c5348401c000 0x40a80c35045b0059 0xfe7f81ffffc1ffae 0xfefe0e7fc67fc0ff

def z1054 : W := mkw 0x9a5d71eb39651bd7 0x13fff6eedaf6df2c 0xfffffffffffe0fff 0x43ffffffffffff38

def z1055 : W := mkw 0x98000000000013d6 0x03fff6eed8000424 0xff8001f000060ff5 0x43fffffff8000738

def z1056 : W := mkw 0x8800000000000250 0x03ffb6acd8000000 0xff800000000002b0 0x03ff8f9ff8000000

def z1057 : W := mkw 0x005c71c939200041 0x0057b00002b6db00 0x007ffffffffe03cf 0x02e7f00007ffff00

def z1058 : W := mkw 0x8800000000000190 0x00c456eed8000000 0xff80000000000170 0x00e07ffff8000000

def z1059 : W := mkw 0x00734d3480018200 0xc3a80eb406da0058 0x007f81ffc001ff2c 0xc2f80e7c067e00f8

def z1060 : W := mkw 0x656aaa0026906028 0xa0028b816f8168c3 0xfffffe003ff9f0ba 0xbc078f83ff81f8c7

def z1061 : W := mkw 0x0071453000018228 0x03a80d3007da00d8 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z1062 : W := mkw 0x0031453480018000 0x40a80c34045a0058 0x007f81ffc001fd0c 0xc0f8007c067e00f8

def z1063 : W := mkw 0x657aef14a690e228 0xe32a8b956f9b68d3 0xfffffff1fff9ffbe 0xff1f8fffff8ff8ff

def z1064 : W := mkw 0xf5eebac97fba77ef 0xab57fbcb7fa5ffe7 0xfffffe003ffff2fb 0xbf07ff83ff81ffc7

def z1065 : W := mkw 0x0031453480018000 0x40a80c34045a0058 0x001f81ffc0000d04 0x42f80e7c067e0038

def z1066 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xffe001f03e0603ff 0x03fffffff8000700

def z1067 : W := mkw 0x522580a214455986 0x10c45c638461856d 0xfe1f800e3fc7fce3 0xfee67e63c671c7ff

def z1068 : W := mkw 0x6068a20026006228 0x03028901278168c3 0xfffffe003ff9f2ba 0xbf078f83ff81f8c7

def z1069 : W := mkw 0x98000000000013d6 0x03fff6eed8000424 0xff8000000001fff0 0xfffffffff80000ff

def z1070 : W := mkw 0x88010020000103d0 0x03fff6eed8400008 0xff8001fe00000ff4 0x43fffffff8700038

def z1071 : W := mkw 0x72fdf7fb7f6ffe6f 0x1b7fb91127ffffff 0x007fffffffffffcf 0xfffff00007ffffff

def z1072 : W := mkw 0x880c2089312003d1 0x03fff6eed820c900 0xff80000001c003f0 0x03fffffff801c000

def z1073 : W := mkw 0xf2a38e36c64ffdae 0xd8804fffb54924ff 0xff8000000001fc30 0xfc000ffff80000ff

def z1074 : W := mkw 0x656aaa0026906200 0xa3028a816e816843 0xff9f80003ff802b2 0x3f078f83fe01f807

def z1075 : W := mkw 0x0011453480018000 0x40a80434005a0018 0x006001ffc001ff2c 0xc0f8007c007e00f8

def z1076 : W := mkw 0x005c71c939200241 0x037fb28402b6db00 0x007ffffffffe03cf 0x03fff19c07ffff00

def z1077 : W := mkw 0x0011453480018000 0x40a80434005a0018 0x000001ffc0000f24 0x42f80e7c007e0038

def z1078 : W := mkw 0x6533cf348691e028 0xe0a80fb56d5b20db 0xff8001ffc001fd34 0xfcf80ffff87e00ff

def z1079 : W := mkw 0x602186300601e028 0x00800d31254920db 0xfffffffffff9ffbe 0xffff8ffffffff8ff

def z1080 : W := mkw 0x522580a214455986 0x10c45c638461856d 0xffff81fe3fc7ffff 0xffe7ffe3fe71c7ff

def z1081 : W := mkw 0x00230c3480018028 0xc0800fb4054800d8 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z1082 : W := mkw 0x522580a214455986 0x10c45c638461856d 0xfe1f81fe01c7fd65 0xfee67e63c671c7ff

def z1083 : W := mkw 0x4073cd348401c228 0xc3a80fb507db00d9 0x0e7fffffc1c1ff2c 0xc3fe0ffdc7ffc0f8

def z1084 : W := mkw 0x0021043000018228 0x03a80fb4054800d8 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z1085 : W := mkw 0xf28cb2cb7f6e7dc7 0x1857f04bb025ff27 0xff8000003ffe00d3 0x3c07f003f801ff07

def z1086 : W := mkw 0x8800000000000190 0x00c456eed8000000 0xff800000000000f0 0x00067ffff8000000

def z1087 : W := mkw 0x4073cd348401c228 0xc3aa8fb54fdb00d9 0xffffffffffc1ffbe 0xffff8fffffffc0ff

def z1088 : W := mkw 0x656aae102690e228 0xa3028b916f8968d3 0xfffffe003ff9feba 0xff078fffff81f8ff

def z1089 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xffe000003e01f3fa 0xbffffffff80000c7

def z1090 : W := mkw 0x8000000000000180 0x0080446a90000000 0xff80000000000030 0x00000ffff8000000

def z1091 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0xf1807e01fe3ffcf3 0xfd19f1fe398e3fff

def z1092 : W := mkw 0x657bef34a691e228 0xe3aa8fb527db68db 0x007ffffffff9ffae 0xffff8ffc07fff8ff

def z1093 : W := mkw 0x6020820006006228 0x03028b816d0120c3 0xfffffe003ff9f2ba 0xbf078f83ff81f8c7

def z1094 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0xf1ffffffc001ffbc 0xc3f98ffe3ffe00f8

def z1095 : W := mkw 0x656baa2026916228 0xa3028b816fc168cb 0xfffffffe3ff9febe 0xff078f83fff1f8ff

def z1096 : W := mkw 0x880c30c9392003d1 0x03fff6eed824db00 0xffff81fe3ffe03ff 0x03fffffffe71ff00

def z1097 : W := mkw 0x0031453480018200 0x43a80eb4045a0058 0x007f81ffc001ff2c 0xc3f80ffc067e00f8

def z1098 : W := mkw 0x8800000000000390 0x03b966eed8000000 0xff800000000003f0 0x03f9fffff8000000

def z1099 : W := mkw 0x9a1551eb196519d7 0x10fd746e9076972c 0x000001ffc0060d45 0x40f8707c007e0738

def z1100 : W := mkw 0x8800000000000390 0x0382c6eed8000000 0xff80000000000030 0x02060ffff8000000

def z1101 : W := mkw 0x657aeb0026906228 0xa32a8b816f9368c3 0xfffffe01fff9f2ba 0xbf1f8f83ff8ff8c7

def z1102 : W := mkw 0x88482000200003d0 0x03fff6eeda804800 0xff9f800001c003f0 0x03fffffffe01c000

def z1103 : W := mkw 0x98801040480a17d6 0x0bfff6eed8041624 0xff800000000603f1 0x03fffffff8000700

def z1104 : W := mkw 0x8a0500a210450bd0 0x13fff6eed8608108 0xff80000e000003f0 0x03fffffff8700000

def z1105 : W := mkw 0xd28490c25c4e5d86 0x1855704b90259725 0xfe0000003fc600c3 0x3c067003c001c707

def z1106 : W := mkw 0x8d4a2800209003d0 0xa3fff6eeda804800 0xff800000000003f0 0x03fffffff8000000

def z1107 : W := mkw 0x908410c9592a15c7 0x0855704a10249724 0x0000000000060041 0x0000700000000700

def z1108 : W := mkw 0x005c71c939200241 0x037d300002b6db00 0x007ffffffffe034f 0x03f8700007ffff00

def z1109 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xff80000000000170 0x02fe7ffff8000000

def z1110 : W := mkw 0x6508a20026906000 0x2002800168016803 0xff8000003ff802b2 0x3e078e03f801f807

def z1111 : W := mkw 0x657bef34a691e228 0xe3028b916fdb68db 0xfffffffffff9ffbe 0xff1f8ffffffff8ff

def z1112 : W := mkw 0xf7a38e3246dffdae 0xb8804ffbfd4924ff 0xff8000000001fc30 0xfc000ffff80000ff

def z1113 : W := mkw 0x88482000200003d0 0x03fff6eeda804800 0xff807e00003803f0 0x03fffffff9803800

def z1114 : W := mkw 0x4573cd348491c228 0xe3a80fb54fdb00d9 0x0e7fffffc001ff2c 0xc3f80ffdc7fe00f8

def z1115 : W := mkw 0x98040080100013d6 0x03fff6eed8208524 0xffff81fe3fc7ffff 0xfffffffffe71c7ff

def z1116 : W := mkw 0x8800000000000390 0x0393e6eed8000000 0xff800000000003f0 0x031ffffff8000000

def z1117 : W := mkw 0xb08016504a0ab5ae 0x0811615a310c36b6 0xf1fffff1ffffffff 0xff1ff1fe3f8fffff

def z1118 : W := mkw 0x0011453480018000 0x40a80434005a0018 0x007f81ffc0000f0c 0x42f8007c067e0038

def z1119 : W := mkw 0x8800104008000190 0x009166eed8041200 0xffe07ff1fe3e03ff 0x0119fffff98e3f00

def z1120 : W := mkw 0x805c71c939200241 0x037fb00812b6db00 0x01fffffffffe03df 0x03fff19c3fffff00

def z1121 : W := mkw 0x0011453480018200 0x43a80434005a0018 0x000001ffc0000f04 0x43f8007c007e0038

def z1122 : W := mkw 0x652aaa0026906028 0xa0028b816d0168c3 0xffe07e003ff9f2ba 0xbd078f83f981f8c7

def z1123 : W := mkw 0x8800000000000210 0x0302828c58000000 0xff800000000002b0 0x03078f9ff8000000

def z1124 : W := mkw 0x00734d3480018200 0xc3a80eb406da0058 0x001f81ffc0000f24 0x43f80ffc067e0038

def z1125 : W := mkw 0x88587149292003d1 0x03fff6eeda965a00 0xffffffffc03803fc 0x03fffffffffe3800

def z1126 : W := mkw 0x88586100200003d0 0x03fff6eeda924800 0xfffffffffff803fe 0x03fffffffffff800

def z1127 : W := mkw 0x8800000000000190 0x008046eed8000000 0xff80000000000330 0x01180ffff8000000

def z1128 : W := mkw 0x25734f348291a228 0xe3a80fb46fda20da 0x01ffffffc001ff3c 0xc3f80ffc3ffe00f8

def z1129 : W := mkw 0x8850410000000390 0x03a846eeda920000 0xffffffffc000033c 0x03f80ffffffe0000

def z1130 : W := mkw 0x657aeb0026906228 0xa32a8b816f9368c3 0xfffffe0e3ff9f2ba 0xbfe78f83fff1f8c7

def z1131 : W := mkw 0x88000000000001d0 0x00fd76eed8000000 0xff800000000003f0 0x01f9fffff8000000

def z1132 : W := mkw 0x88000000000003d0 0x03d7f6eed8000000 0xff800000000002f0 0x0307fffff8000000

def z1133 : W := mkw 0x88000000000001d0 0x00c6d6eed8000000 0xff80000000000030 0x00060ffff8000000

def z1134 : W := mkw 0x88082000200003d0 0x03fff6eed8004800 0xff8000003ff803f2 0x03fffffff801f800

def z1135 : W := mkw 0x800410c018000180 0x00d5746a90249300 0xfffffffffffe03ff 0x03ffffffffffff00

def z1136 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0x001fffffc1fe0145 0x03fff00007ffff00

def z1137 : W := mkw 0x8800000000000250 0x033ba28c58000000 0x0f80000000000010 0x031f8f9df8000000

def z1138 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0x001ffe0ffffe00c3 0x03fff00007ffff00

def z1139 : W := mkw 0x005c71c939200201 0x036c100002b6db00 0x007ffffffffe03cf 0x03fe700007ffff00

def z1140 : W := mkw 0x656aaa0026906028 0xa0000901278168c3 0xfffffe003ff9f2ba 0xbf078f83ff81f8c7

def z1141 : W := mkw 0x8800000000000390 0x0382c6eed8000000 0xff80000000000030 0x01018ffff8000000

def z1142 : W := mkw 0xf7eebac27ede7fae 0xbb57fbcbffa5ffe7 0xfffffe003ffff2fb 0xbf07ff83ff81ffc7

def z1143 : W := mkw 0x0000000000000200 0x03a806a448000000 0xff80000000000330 0x03f80ffff8000000

def z1144 : W := mkw 0x20734f348201a228 0xc3a80fb427da20da 0xf1ffffffc001ff3c 0xfff80ffe3ffe00ff

def z1145 : W := mkw 0xfaa18632464ffdbe 0x18804ffffd4924ff 0xff8000000001fc30 0xfc000ffff80000ff

def z1146 : W := mkw 0x00734d3480018228 0xc3aa8fb44fda00d8 0x01ffffffc001ff3c 0xc3f98ffc3ffe00f8

def z1147 : W := mkw 0x00734d3480018028 0xc0a80fb407da00d8 0x007fffffc001fd2c 0xc0f80ffc07fe00f8

def z1148 : W := mkw 0x884c2080300003d0 0x03fff6eedaa0c900 0xfffffffe3ffe03ff 0x03fffffffff1ff00

def z1149 : W := mkw 0xf58cb2c97fba75c7 0x2857f04b7825ff27 0xff8000003ffe00d3 0x3c07f003f801ff07

def z1150 : W := mkw 0x0011453480018200 0x43aa86b4485a0018 0xff8001ffc0000fb4 0x43ff8ffff87e0038

def z1151 : W := mkw 0x0011453480018000 0x40a80434005a0018 0x00607fffc0000f0c 0x41f8007c01fe0038

def z1152 : W := mkw 0x88000000000001d0 0x00d7f46ad8000000 0xff800000000003f0 0x03fffffff8000000

def z1153 : W := mkw 0x885c71c9392003d1 0x03fff6eedab6db00 0xff9f800e3ffe03f3 0x03fffffffe71ff00

def z1154 : W := mkw 0x0021043000018000 0x00800c3004480058 0x007f81ffc001ff2c 0xc2f80e7c067e00f8

def z1155 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x00007fffc001fd24 0xc1f80ffc01fe00f8

def z1156 : W := mkw 0x9a0500a210451996 0x10c456eed860852c 0xff8001fe00060d75 0x40e07ffff8700738

def z1157 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0xfffffffe3ff9f3be 0xbfe78f83fff1f8c7

def z1158 : W := mkw 0x88000000000001d0 0x00d7f6eed8000000 0xff800000000003f0 0x011ffffff8000000

def z1159 : W := mkw 0x65228a0006906028 0xa0000b816d0120c3 0xfffffe003ff9f2ba 0xbf078f83ff81f8c7

def z1160 : W := mkw 0x88001040080003d0 0x03fff6eed8041200 0xff8001f1c00603f5 0x03fffffff80e0700

def z1161 : W := mkw 0x0010451000008028 0x00280110011a0090 0x00607fffc001ff2c 0xc1f801fc01fe00f8

def z1162 : W := mkw 0x8000000000000380 0x0302c2ca58000000 0xff800000000002b0 0x03078ffff8000000

def z1163 : W := mkw 0xb0cc32c97b2a37ef 0x0b57f14a33a4ffa6 0xf1fffe003ffff2fb 0xbf07f1823f81ffc7

def z1164 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0xff9ffe0001f9f030 0xbf078f83ff81f8c7

def z1165 : W := mkw 0x885c71c939200251 0x03ffb6acdab6db00 0x0f9ffe0fc1f80010 0x03ff8f9dfffff800

def z1166 : W := mkw 0x08734d3480018278 0xc3aa8fb44fda00d8 0x007fffffc001ff2c 0xc3f80ffc07fe00f8

def z1167 : W := mkw 0x00334d3480018000 0xc0a80eb4045a0058 0x000001ffc0000d04 0x40f80e7c007e0038

def z1168 : W := mkw 0x522580a214455986 0x10c45c638461856d 0xfe7f81fe3fc7fccf 0xfee67e03c671c7ff

def z1169 : W := mkw 0x8000000000000180 0x0091646a90000000 0xff800000000003f0 0x0119fffff8000000

def z1170 : W := mkw 0x8800000000000190 0x009166eed8000000 0xff80000000000170 0x00187ffff8000000

def z1171 : W := mkw 0x657aeb0927b06269 0xa32a8b816f9368c3 0xfffffe003ff9f2ba 0xbf078f83ff81f8c7

def z1172 : W := mkw 0x005c71c939200241 0x037fb0004ab6db00 0xfffffffffffe03df 0x03fff003ffffff00

def z1173 : W := mkw 0x0000000000000200 0x038286a448000000 0xff800000000002b0 0x03078ffff8000000

def z1174 : W := mkw 0x656aaa0026906228 0xa3028b816f8168c3 0xff9f80003ff9f0b2 0xbe078f83fe01f8c7

def z1175 : W := mkw 0x8800000000000010 0x0000028c58000000 0xff80000000000030 0x00000f9ff8000000

def z1176 : W := mkw 0x257b6f34a291a228 0xe3aa8fb46fda68da 0xffffffffc039ffbc 0xc3ff8ffffffe38f8

def z1177 : W := mkw 0x75feffd97fbaf42f 0xa800091127bffff7 0x007ffffffffffc0f 0xfc00000007ffffff

def z1178 : W := mkw 0x6020820006006000 0x0000080124012043 0xffff80003ff9f2ba 0xbe078e03fe01f8c7

def z1179 : W := mkw 0x885c6189312003d1 0x03fff6eedab2c900 0xfffffe0e3ff803fa 0x03fffffffff1f800

def z1180 : W := mkw 0x9a0500a210451bd6 0x13fff6eed860852c 0xffe001fe3e07ffff 0xfffffffff87007ff

def z1181 : W := mkw 0x6508a20026906200 0x2302828168016803 0xff8000003ff80092 0x3e078e03f801f807

def z1182 : W := mkw 0x656bae302691e228 0xa3828fb16fc968db 0xfffffffffff9ffbe 0xffff8ffffffff8ff

def z1183 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xffe07ff1c00003fc 0x03fffffff98e0000

def z1184 : W := mkw 0x88000000000003d0 0x03eed6eed8000000 0xff800000000002b0 0x03e78ffff8000000

def z1185 : W := mkw 0x88000000000003d0 0x03fff6eed8000000 0xffe001f00001fffc 0xc3fffffff80000f8

def z1186 : W := mkw 0x8000000000000380 0x03fd76ee90000000 0xff800000000003f0 0x03fffffff8000000

def z1187 : W := mkw 0x657aef14a690e028 0xe0000911279b68d3 0x007ffe01fff9f00a 0xbc000000078ff8c7

def z1188 : W := mkw 0x0011453480018200 0x43a806b4005a0018 0x000001ffc0000d04 0x41f801fc007e0038

def z1189 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0x007ffffffffe00cf 0x02e7f00007ffff00

def z1190 : W := mkw 0x88105149092003d1 0x03fff6eed8161200 0xff800001c00003f0 0x03fffffff80e0000

def z1191 : W := mkw 0x0051453480018000 0x40a8043402da0018 0x007fffffc0000d0c 0x40f8007c07fe0038

def z1192 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0x007fffffffffffef 0xc3fff06007fffff8

def z1193 : W := mkw 0x005c71c939200241 0x037fb00002b6db00 0xf07ffffffffff3ef 0xbffff00207ffffc7

def z1194 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x007fffffc001fd0c 0xc2f80e7c07fe00f8

def z1195 : W := mkw 0x8800000000000250 0x03ffb6acd8000000 0x0f80000000000330 0x03ff8ffdf8000000

def z1196 : W := mkw 0x0051453480018200 0x43a8043402da0018 0x00007fffc0000d04 0x41f8007c01fe0038

def z1197 : W := mkw 0x654aaa0026906228 0xa30283816b816883 0xff807e003ff802b2 0x3f078f83f981f807

def z1198 : W := mkw 0x8800000000000390 0x03a846eed8000000 0xff80000000000030 0x02e00ffff8000000

def z1199 : W := mkw 0x00734d3480018200 0xc3a80eb406da0058 0x007fffffc0000f0c 0x43f80e7c07fe0038

def z1200 : W := mkw 0x75eabe506e9af62e 0xab13a911278d7ef7 0x007ffff1ffffffcf 0xff1ff000078fffff

def z1201 : W := mkw 0x8800000000000190 0x008046eed8000000 0xff800000000002b0 0x02060ffff8000000

def z1202 : W := mkw 0x5024808014005186 0x0044584304218565 0xfe7f81fe3fc7ffef 0xfee67e63c671c7ff

def z1203 : W := mkw 0x8858714929200251 0x033ba28c5a965a00 0xfffffe01fff802ba 0x031f8f9fff8ff800

def z1204 : W := mkw 0x00734d3480018228 0xc3a80fb407da00d8 0x001ffe0fc001fc20 0xc3f80ffc07fe00f8

def z1205 : W := mkw 0x0058610020000200 0x03aa86a44a924800 0xfffffffffff803be 0x03ff8ffffffff800

def z1206 : W := mkw 0x085c71c939200251 0x037fb000cab6db00 0x0e7ffffffffe03cf 0x03fff001c7ffff00

def z1207 : W := mkw 0x6528a20026906200 0x23028a816c016843 0xffff80003ff9f2ba 0xbf078f83fe01f8c7

def z1208 : W := mkw 0x005e79cdb9200241 0xc37fb28402b6db00 0x007ffffffffe03cf 0x03fff00007ffff00

def z1209 : W := mkw 0x00734d3480018028 0xc0a80d3407da00d8 0x007fffffc001ff2c 0xc1f801fc07fe00f8

def z1210 : W := mkw 0x457bed34a491c228 0xe3a80fb507db48d9 0x007fffffc1c1ff2c 0xc3f80ffc07ffc0f8

def z1211 : W := mkw 0x652aaa0026906028 0xa0028b816d0168c3 0xffff80003ff9f2ba 0xbe078f83fe01f8c7

def z1212 : W := mkw 0x88000000000001d0 0x00fff6eed8000000 0xff800000000001f0 0x00fffffff8000000

def z1213 : W := mkw 0x88040080100003d0 0x03fff6eed8208100 0xff8000003fc603f3 0x03fffffff801c700

def z1214 : W := mkw 0x656aaa0026906200 0xa3028a816e816843 0xfffffe003ff8029a 0x3f078e03ff81f807

def z1215 : W := mkw 0x88000000000001d0 0x00fd76eed8000000 0xff800000000003f0 0x02fe7ffff8000000

def z1216 : W := mkw 0x8000000000000180 0x000042ca58000000 0xff80000000000030 0x00000ffff8000000

def z1217 : W := mkw 0x908c30c9792a15c7 0x0857f04a1024df24 0x000000003ffe00c3 0x0007f0000001ff00

def z1218 : W := mkw 0x929555fb596f9dc7 0x18fd747a907e973c 0x000001ffc0060d45 0x40f8707c007e0738

def z1219 : W := mkw 0x928510e2584f1d86 0x18d5746a9064972c 0x000001fe00060d45 0x40e0706000700738

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z9,z5,z6]),(0,[z1,z2,z10,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z11,z6]),(0,[z1,z2,z8,z4,z5,z6,z12]),(0,[z1,z2,z8,z13,z5,z6,z14])],[(0,[z15,z1,z2,z8,z4,z5,z6]),(0,[z16,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z17,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z19,z18,z6]),(0,[z1,z2,z8,z4,z18,z6,z20]),(0,[z1,z2,z21,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z22,z6]),(0,[z1,z2,z8,z23,z4,z5,z6]),(0,[z1,z24,z8,z4,z25,z5,z6]),(0,[z1,z8,z4,z5,z26,z6,z27])],[(0,[z28,z1,z2,z8,z4,z5,z6]),(0,[z29,z1,z2,z8,z4,z5,z6]),(0,[z30,z31,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z32])],[(0,[z33,z1,z2,z8,z4,z5,z6]),(0,[z1,z34,z35,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z36,z6,z14])],[(0,[z37,z38,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z39,z18,z6]),(0,[z31,z1,z40,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z41,z6]),(0,[z1,z2,z8,z4,z5,z6,z42])],[(1,[z1,z2,z8,z4,z43,z6]),(0,[z44,z1,z2,z8,z4,z18,z6]),(0,[z1,z2,z45,z8,z4,z46,z6]),(0,[z47,z1,z2,z8,z4,z48,z6]),(0,[z1,z8,z4,z25,z5,z6,z27]),(0,[z1,z2,z49,z8,z4,z5,z6]),(0,[z1,z2,z50,z40,z8,z4,z6]),(0,[z51,z1,z2,z8,z4,z39,z6]),(0,[z52,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z5,z53,z6,z54])],[(0,[z55,z1,z2,z8,z4,z5,z6]),(0,[z1,z56,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z57,z6])],[(0,[z58,z1,z2,z8,z4,z46,z6]),(0,[z37,z1,z8,z4,z5,z26,z6]),(1,[z1,z8,z4,z25,z46,z6]),(0,[z1,z59,z8,z4,z25,z5,z6]),(0,[z1,z2,z60,z8,z4,z5,z6])]],
   [[(0,[z61,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z62,z63,z5,z6]),(0,[z64,z1,z2,z8,z4,z46,z6]),(0,[z1,z2,z8,z65,z4,z5,z6]),(0,[z1,z66,z8,z4,z25,z5,z6]),(0,[z1,z2,z8,z4,z5,z53,z6]),(0,[z1,z2,z8,z4,z67,z5,z6]),(0,[z1,z2,z68,z50,z8,z4,z5])],[(0,[z1,z2,z68,z8,z4,z6,z69])],[(0,[z70,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z71,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z72,z6]),(0,[z31,z1,z2,z8,z4,z18,z6]),(0,[z31,z1,z8,z4,z73,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z74])],[(0,[z1,z2,z8,z4,z5,z75,z6]),(0,[z1,z2,z8,z76,z4,z18,z6]),(0,[z1,z2,z8,z4,z77,z18,z6]),(0,[z1,z2,z78,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z79,z5,z6]),(0,[z1,z2,z80,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z81]),(0,[z1,z2,z8,z4,z6,z82,z69])],[(0,[z83,z1,z2,z8,z4,z18,z6]),(0,[z1,z8,z63,z4,z25,z5,z6]),(0,[z1,z84,z2,z8,z4,z5,z6]),(0,[z85,z2,z8,z4,z5,z6,z86]),(1,[z1,z8,z25,z79,z5,z6]),(0,[z1,z2,z87,z34,z8,z5,z6])],[(0,[z1,z2,z88,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z89,z6]),(0,[z1,z2,z8,z4,z5,z90,z6])],[(0,[z1,z2,z8,z8,z4,z5,z6]),(0,[z91,z1,z2,z8,z4,z18,z6]),(1,[z1,z92,z8,z4,z5,z6]),(0,[z1,z2,z93,z8,z4,z5,z6]),(0,[z94,z1,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z95,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z96])],[(0,[z1,z2,z8,z4,z5,z97,z6]),(0,[z1,z2,z8,z4,z5,z98,z6]),(0,[z99,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z18,z6,z82]),(0,[z1,z2,z100,z8,z4,z5,z6]),(0,[z101,z1,z2,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z5,z102,z6]),(0,[z103,z1,z2,z8,z4,z5,z6]),(0,[z1,z104,z2,z8,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z4,z46,z6,z105]),(0,[z106,z1,z8,z4,z25,z5,z6]),(0,[z107,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z108,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z109]),(0,[z110,z1,z2,z8,z4,z5,z6])],[(0,[z111,z1,z2,z8,z4,z5,z6]),(0,[z112,z1,z2,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z5,z6,z113]),(0,[z114,z1,z8,z4,z25,z5,z6]),(0,[z115,z1,z2,z8,z4,z5,z6])],[(1,[z30,z2,z8,z4,z18,z6]),(0,[z116,z1,z2,z8,z4,z5,z6]),(0,[z1,z117,z8,z4,z25,z5,z6]),(0,[z31,z1,z118,z8,z4,z5,z6]),(0,[z101,z1,z2,z4,z5,z6,z69]),(0,[z1,z2,z4,z39,z5,z6,z69]),(0,[z1,z2,z40,z8,z4,z67,z6]),(0,[z1,z2,z8,z4,z119,z6,z14]),(0,[z120,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z121,z4,z5,z6])],[(0,[z58,z1,z2,z8,z122,z5,z6]),(1,[z0,z2,z8,z4,z18,z6]),(0,[z1,z2,z123,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z18,z124,z6]),(0,[z51,z1,z2,z8,z25,z5,z6]),(0,[z51,z1,z56,z2,z8,z4,z6]),(0,[z1,z2,z8,z4,z5,z6,z125]),(0,[z51,z126,z2,z8,z4,z5,z6]),(0,[z1,z127,z2,z8,z4,z5,z6])],[(0,[z128,z1,z2,z8,z4,z5,z6]),(0,[z129,z1,z2,z8,z4,z5,z6]),(1,[z1,z8,z4,z130,z5,z6]),(0,[z51,z1,z2,z8,z4,z46,z6]),(0,[z131,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z5,z6,z20]),(1,[z1,z2,z8,z4,z132,z6]),(0,[z1,z2,z8,z4,z133,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z134]),(0,[z135,z1,z2,z8,z4,z5,z6]),(0,[z101,z1,z2,z40,z4,z5,z6])],[(0,[z37,z1,z2,z8,z4,z136,z6]),(0,[z1,z2,z8,z137,z4,z5,z6]),(1,[z1,z2,z8,z4,z138,z6]),(0,[z83,z1,z2,z8,z4,z46,z6]),(1,[z31,z1,z8,z4,z18,z6]),(0,[z1,z2,z8,z139,z4,z5,z6]),(0,[z140,z1,z2,z8,z4,z5,z6]),(1,[z2,z8,z4,z5,z141,z6]),(0,[z1,z118,z142,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z143]),(0,[z1,z2,z8,z4,z5,z144,z6]),(0,[z145,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z117,z60,z8,z5,z6]),(0,[z1,z2,z8,z4,z79,z5,z6])]],
   [[(0,[z58,z1,z2,z8,z4,z146,z6]),(0,[z38,z1,z2,z8,z4,z18,z6]),(0,[z94,z1,z2,z8,z4,z46,z6]),(1,[z1,z2,z8,z4,z147,z6]),(0,[z1,z2,z148,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z149,z5,z6]),(0,[z1,z2,z150,z8,z4,z5,z6]),(0,[z151,z1,z2,z8,z4,z5,z6]),(0,[z152,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z153]),(0,[z1,z154,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z5,z6,z155,z86]),(0,[z31,z1,z2,z8,z62,z5,z6]),(0,[z1,z156,z2,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z5,z18,z6]),(0,[z31,z131,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z157,z6]),(0,[z1,z118,z8,z4,z25,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z158]),(0,[z1,z2,z159,z8,z4,z5,z6])],[(0,[z114,z58,z1,z8,z4,z5,z6]),(0,[z1,z2,z160,z8,z4,z46,z6]),(0,[z1,z8,z4,z25,z5,z6,z69]),(0,[z161,z1,z2,z8,z4,z5,z6])],[(0,[z162,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z163,z8,z4,z5,z6]),(0,[z164,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z165]),(1,[z1,z166,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z167,z5,z6])],[(0,[z1,z2,z60,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z5,z6,z168]),(0,[z1,z2,z8,z4,z5,z6,z169])],[(0,[z85,z1,z2,z8,z4,z170,z6]),(0,[z1,z171,z2,z8,z4,z5,z26])]],
   [[(1,[z31,z1,z8,z4,z46,z6]),(0,[z114,z1,z66,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z172,z6])],[(0,[z173,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z174,z6]),(0,[z1,z2,z8,z4,z18,z6,z175]),(0,[z1,z2,z8,z4,z5,z6,z176]),(0,[z1,z2,z8,z62,z4,z5,z6]),(0,[z177,z1,z2,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z5,z178,z6]),(0,[z31,z1,z8,z4,z5,z6,z179]),(0,[z1,z2,z180,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z20]),(0,[z1,z2,z181,z8,z4,z5,z6])],[(0,[z1,z2,z182,z8,z4,z46,z6])],[(0,[z1,z2,z8,z4,z5,z6,z183]),(1,[z1,z2,z8,z4,z184,z6]),(0,[z185,z1,z2,z8,z4,z186,z6]),(0,[z1,z2,z8,z4,z25,z46,z6]),(0,[z1,z2,z8,z4,z5,z187,z6]),(1,[z1,z34,z8,z25,z5,z6]),(0,[z1,z8,z4,z25,z5,z6,z82]),(0,[z188,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z189,z5,z6]),(0,[z185,z83,z2,z8,z4,z5,z6]),(0,[z85,z47,z2,z8,z4,z5,z6]),(0,[z1,z182,z8,z4,z25,z5,z6]),(0,[z1,z2,z8,z4,z5,z190,z6])],[(0,[z1,z2,z8,z4,z46,z53,z6]),(0,[z1,z2,z191,z8,z4,z5,z6]),(0,[z1,z8,z192,z4,z25,z5,z6]),(0,[z1,z2,z8,z4,z193,z5,z6]),(0,[z1,z2,z8,z4,z5,z194,z6]),(0,[z31,z1,z117,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z195]),(0,[z51,z120,z2,z8,z4,z5,z6]),(0,[z1,z2,z68,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z196,z6]),(0,[z1,z2,z8,z4,z197,z5,z6]),(1,[z1,z8,z4,z132,z25,z6]),(0,[z1,z2,z8,z25,z5,z6,z54]),(0,[z31,z1,z198,z8,z4,z5,z6]),(0,[z1,z2,z60,z8,z5,z6,z54])],[(0,[z37,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z199,z46,z6]),(0,[z47,z1,z2,z8,z4,z5,z200])]],
   [[(0,[z91,z1,z2,z76,z4,z5,z6]),(0,[z201,z1,z2,z8,z4,z18,z6]),(0,[z1,z202,z2,z8,z4,z46,z6])],[(0,[z30,z16,z2,z8,z4,z5,z6]),(0,[z1,z2,z203,z8,z4,z5,z6]),(0,[z1,z2,z34,z8,z4,z5,z6])],[(0,[z1,z2,z92,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z204,z6]),(1,[z1,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z205,z5,z6]),(0,[z114,z31,z1,z8,z4,z5,z6]),(1,[z152,z1,z8,z4,z5,z6])],[(0,[z1,z2,z206,z8,z4,z5,z6]),(0,[z131,z1,z8,z4,z25,z5,z6]),(0,[z1,z2,z207,z8,z4,z5,z6]),(0,[z208,z1,z2,z8,z209,z4,z6])],[(0,[z0,z1,z8,z4,z25,z5,z6]),(0,[z1,z2,z50,z8,z4,z18,z6]),(0,[z210,z31,z1,z8,z4,z5,z6]),(0,[z1,z2,z87,z8,z4,z5,z6]),(0,[z211,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z212,z5,z6]),(0,[z1,z2,z8,z4,z5,z213,z6])],[(0,[z30,z1,z2,z8,z4,z46,z6]),(0,[z1,z2,z214,z8,z4,z5,z6]),(0,[z215,z31,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z216,z5,z6]),(0,[z1,z2,z8,z4,z5,z217,z6]),(0,[z114,z1,z171,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z218,z5,z6])],[(1,[z0,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z219,z4,z5,z6]),(0,[z185,z1,z8,z4,z25,z5,z6]),(0,[z1,z2,z8,z63,z4,z18,z6]),(0,[z1,z220,z2,z8,z4,z5,z6]),(0,[z1,z171,z2,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z221,z5,z6]),(0,[z1,z2,z222,z8,z4,z5,z6])],[(0,[z223,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z224,z5,z6]),(0,[z1,z2,z8,z4,z5,z170,z6]),(0,[z1,z2,z8,z4,z5,z225,z6]),(0,[z226,z1,z8,z4,z25,z5,z6]),(0,[z31,z1,z8,z209,z4,z5,z6]),(0,[z1,z2,z227,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z228]),(0,[z1,z2,z8,z4,z5,z6,z82])]],
   [[(1,[z229,z1,z8,z4,z5,z6]),(0,[z1,z50,z8,z4,z25,z5,z6]),(0,[z1,z2,z8,z4,z230,z5,z6]),(1,[z1,z2,z8,z231,z5,z6]),(0,[z1,z2,z232,z8,z4,z5,z6]),(1,[z2,z8,z4,z5,z6,z233])],[(0,[z1,z2,z234,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z235,z46,z6]),(0,[z1,z2,z8,z4,z5,z236,z6])],[(0,[z1,z2,z66,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z46,z6,z54]),(0,[z1,z2,z8,z192,z4,z5,z6]),(0,[z31,z1,z8,z4,z19,z5,z6]),(0,[z1,z2,z237,z8,z4,z5,z6])],[(0,[z1,z2,z238,z8,z4,z5,z6]),(0,[z47,z1,z2,z8,z4,z18,z6]),(0,[z162,z1,z8,z4,z25,z5,z6]),(0,[z239,z1,z2,z8,z4,z5,z6]),(0,[z208,z1,z8,z4,z25,z5,z6]),(0,[z240,z1,z2,z8,z4,z5,z6])],[(0,[z31,z38,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z18,z6,z27]),(0,[z85,z1,z2,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z124,z6])],[(0,[z1,z2,z8,z4,z241,z5,z6]),(0,[z2,z8,z63,z4,z235,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z242]),(0,[z1,z243,z2,z8,z4,z18,z6]),(0,[z31,z1,z8,z4,z39,z5,z6]),(0,[z1,z2,z8,z4,z5,z244,z6]),(0,[z1,z60,z245,z8,z4,z5,z6])],[(0,[z1,z2,z8,z246,z4,z5,z6]),(0,[z247,z1,z8,z4,z5,z6,z86]),(0,[z1,z2,z248,z8,z4,z5,z6]),(0,[z1,z2,z249,z8,z4,z5,z6])],[(0,[z250,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z251,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z46,z18,z6]),(0,[z252,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z117,z8,z73,z5,z6]),(1,[z101,z1,z2,z4,z6,z69]),(0,[z1,z2,z8,z4,z5,z253,z6])]],
   [[(0,[z1,z2,z8,z254,z4,z5,z6]),(0,[z1,z2,z8,z63,z4,z46,z6]),(0,[z1,z2,z255,z8,z4,z5,z6]),(0,[z256,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z209,z4,z257,z5,z6]),(0,[z1,z258,z2,z8,z4,z5,z6])],[(0,[z0,z2,z8,z4,z5,z200,z6]),(0,[z131,z1,z2,z192,z4,z5,z6]),(1,[z1,z2,z34,z73,z5,z6]),(0,[z259,z1,z2,z8,z4,z5,z6])],[(0,[z83,z2,z8,z4,z235,z5,z6]),(0,[z1,z2,z260,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z73,z5,z6]),(0,[z1,z60,z8,z4,z25,z5,z6])],[(0,[z208,z1,z2,z8,z4,z19,z6]),(0,[z1,z2,z8,z261,z4,z5,z6])],[(0,[z262,z1,z2,z8,z4,z5,z6]),(0,[z31,z1,z8,z76,z4,z5,z6]),(0,[z263,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z160,z182,z4,z5,z6]),(0,[z1,z2,z8,z264,z4,z5,z6])],[(0,[z37,z1,z8,z4,z25,z5,z6]),(0,[z1,z2,z8,z4,z265,z18,z6]),(0,[z1,z2,z8,z4,z266,z5,z6]),(0,[z106,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z267,z8,z4,z5,z6]),(0,[z1,z2,z8,z209,z4,z67,z6]),(0,[z268,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z269,z8,z4,z46,z6]),(0,[z16,z2,z3,z8,z4,z5,z6]),(0,[z247,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z270,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z271,z6]),(0,[z1,z2,z8,z272,z4,z5,z6]),(0,[z1,z273,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z274,z5,z6]),(0,[z1,z2,z8,z4,z18,z275,z6]),(0,[z1,z2,z34,z8,z25,z5,z6])]],
   [[(0,[z58,z1,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z46,z187,z6]),(0,[z1,z2,z276,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z277]),(0,[z1,z2,z40,z8,z4,z5,z6]),(0,[z1,z2,z8,z278,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z279])],[(0,[z1,z2,z8,z4,z5,z6,z175]),(0,[z1,z2,z280,z8,z4,z5,z6]),(0,[z162,z1,z2,z192,z4,z5,z6]),(0,[z1,z2,z182,z4,z5,z281,z6])],[(0,[z1,z2,z8,z4,z5,z6,z282]),(0,[z1,z2,z8,z4,z132,z25,z6]),(0,[z1,z2,z8,z4,z5,z283,z6]),(1,[z284,z2,z8,z4,z5,z6]),(0,[z1,z2,z285,z8,z4,z5,z6])],[(0,[z1,z2,z286,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z287,z6])],[(0,[z83,z1,z2,z8,z4,z98,z6]),(0,[z1,z2,z8,z4,z288,z5,z6]),(0,[z1,z2,z8,z4,z5,z5,z6])],[(1,[z1,z2,z8,z4,z146,z6]),(0,[z2,z8,z4,z5,z200,z6,z86]),(0,[z1,z243,z2,z8,z62,z5,z6]),(0,[z1,z2,z8,z4,z289,z5,z6]),(0,[z290,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z291]),(0,[z1,z2,z8,z4,z292,z5,z6]),(0,[z1,z2,z8,z293,z4,z5,z6]),(0,[z294,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z295,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z73,z5,z6])],[(1,[z16,z2,z8,z4,z46,z6]),(0,[z31,z47,z1,z8,z4,z5,z6]),(0,[z1,z2,z117,z8,z62,z5,z6]),(0,[z1,z8,z4,z19,z5,z124,z6]),(1,[z1,z2,z8,z296,z5,z6]),(0,[z297,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z68,z50,z8,z4,z6])]],
   [[(0,[z1,z2,z8,z4,z298,z5,z6]),(0,[z101,z1,z2,z8,z4,z18,z6]),(0,[z47,z1,z2,z8,z4,z225,z6]),(1,[z1,z118,z8,z25,z5,z6]),(0,[z31,z1,z8,z4,z299,z5,z6]),(0,[z1,z87,z300,z8,z4,z5,z6]),(0,[z1,z2,z8,z209,z4,z6,z20])],[(0,[z114,z1,z2,z8,z301,z5,z6])],[(0,[z58,z1,z8,z4,z5,z26,z6]),(0,[z302,z1,z2,z8,z4,z5,z6]),(0,[z85,z1,z8,z4,z25,z5,z6]),(0,[z1,z2,z303,z8,z4,z5,z6]),(0,[z1,z2,z304,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z18,z6,z305]),(0,[z1,z2,z8,z4,z18,z6,z69]),(0,[z1,z8,z4,z25,z306,z5,z6]),(0,[z31,z1,z8,z4,z5,z281,z6]),(0,[z307,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z308,z8,z4,z5,z6])],[(1,[z1,z2,z8,z193,z5,z6]),(0,[z1,z2,z8,z309,z4,z5,z6]),(0,[z1,z2,z8,z4,z231,z5,z6])],[(0,[z1,z2,z8,z4,z310,z5,z6]),(0,[z1,z2,z160,z4,z5,z6,z14]),(1,[z1,z311,z8,z4,z5,z6])],[(0,[z51,z1,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z46,z6,z86]),(0,[z1,z2,z8,z4,z5,z312,z6]),(0,[z1,z2,z118,z8,z4,z5,z6])],[(0,[z313,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z314,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z186,z6]),(0,[z315,z1,z8,z63,z4,z5,z6]),(0,[z316,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z209,z4,z25,z5,z6]),(0,[z317,z1,z8,z209,z4,z5,z6])]],
   [[(0,[z1,z2,z318,z8,z4,z5,z6]),(0,[z208,z1,z56,z8,z4,z5,z6]),(0,[z208,z1,z2,z8,z4,z124,z6]),(1,[z1,z2,z8,z319,z5,z6]),(0,[z1,z2,z8,z320,z4,z5,z6]),(0,[z1,z2,z321,z8,z4,z5,z6])],[(0,[z1,z2,z322,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z323]),(0,[z16,z1,z2,z8,z4,z18,z6]),(0,[z1,z2,z324,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z5,z6,z325]),(0,[z1,z2,z8,z319,z4,z5,z6]),(0,[z1,z2,z160,z8,z4,z5,z281])],[(1,[z208,z1,z8,z4,z124,z6]),(0,[z1,z2,z326,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z327,z6]),(1,[z328,z1,z8,z4,z5,z6]),(0,[z1,z2,z60,z118,z8,z5,z6])],[(0,[z38,z2,z269,z8,z4,z5,z6]),(0,[z1,z2,z329,z8,z4,z5,z6]),(0,[z31,z1,z330,z8,z4,z5,z6]),(1,[z1,z300,z8,z4,z5,z6]),(0,[z1,z2,z331,z8,z4,z5,z6])],[(0,[z1,z2,z332,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z27])],[(0,[z1,z2,z160,z8,z4,z18,z6]),(0,[z114,z1,z2,z8,z4,z46,z6]),(0,[z1,z2,z333,z8,z4,z5,z6]),(0,[z284,z2,z8,z4,z5,z6,z14])],[(0,[z37,z31,z1,z8,z4,z5,z6]),(0,[z1,z56,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z46,z200,z6]),(0,[z1,z2,z8,z4,z5,z334,z6])],[(0,[z1,z2,z8,z4,z5,z335,z6]),(0,[z1,z2,z60,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z336,z5,z6]),(0,[z31,z1,z8,z4,z5,z26,z6]),(0,[z2,z8,z4,z5,z6,z233,z14]),(0,[z1,z2,z182,z8,z4,z5,z281]),(0,[z1,z2,z337,z8,z4,z5,z6])]],
   [[(0,[z37,z1,z269,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z338,z6]),(0,[z31,z1,z8,z4,z5,z18,z6]),(0,[z339,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z147,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z340])],[(0,[z1,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z341,z4,z5,z6]),(0,[z0,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z132,z25,z5,z6]),(0,[z114,z1,z8,z4,z5,z6,z27]),(0,[z1,z2,z342,z8,z4,z5,z6])],[(0,[z31,z1,z3,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z343,z5,z6]),(0,[z1,z2,z344,z8,z4,z5,z6])],[(0,[z185,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z182,z8,z4,z18,z6]),(0,[z16,z1,z2,z8,z4,z46,z6]),(0,[z1,z2,z345,z8,z4,z5,z6])],[(0,[z226,z1,z2,z8,z4,z5,z6]),(0,[z346,z1,z2,z8,z4,z5,z6]),(1,[z185,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z25,z18,z6]),(0,[z1,z2,z8,z4,z46,z6,z347]),(0,[z1,z2,z348,z8,z4,z5,z6])],[(0,[z349,z1,z2,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z5,z6,z14]),(0,[z31,z1,z50,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z179])],[(0,[z51,z1,z2,z8,z62,z5,z6])],[(0,[z1,z2,z8,z4,z5,z275,z6]),(0,[z1,z2,z350,z8,z4,z5,z6]),(0,[z31,z1,z8,z63,z4,z5,z6]),(1,[z1,z2,z8,z4,z36,z6]),(0,[z351,z1,z2,z8,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z4,z136,z5,z6]),(0,[z83,z1,z2,z8,z63,z5,z6]),(0,[z1,z56,z2,z8,z4,z46,z6]),(0,[z352,z1,z2,z8,z4,z5,z6]),(0,[z208,z1,z2,z8,z4,z5,z6]),(0,[z1,z353,z2,z8,z4,z5,z6])],[(0,[z354,z1,z2,z8,z4,z5,z6]),(0,[z85,z0,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z355,z4,z18,z6]),(0,[z1,z2,z356,z8,z4,z5,z6]),(0,[z357,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z34,z4,z73,z5,z6]),(0,[z358,z1,z2,z8,z4,z5,z6])],[(1,[z1,z2,z8,z4,z98,z6]),(0,[z1,z2,z8,z4,z67,z46,z6]),(0,[z1,z2,z8,z4,z359,z5,z6]),(0,[z1,z8,z4,z25,z19,z5,z6]),(0,[z1,z2,z198,z8,z4,z5,z6]),(1,[z1,z56,z8,z4,z19,z6]),(1,[z1,z2,z8,z4,z360,z6])],[(0,[z31,z83,z1,z8,z4,z5,z6]),(0,[z85,z31,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z361,z4,z5,z6]),(0,[z1,z2,z362,z8,z4,z5,z6])],[(0,[z363,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z364,z4,z5,z6]),(0,[z1,z2,z87,z4,z73,z5,z6]),(0,[z1,z2,z50,z8,z209,z4,z6])],[(0,[z91,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z365,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z39,z5,z6]),(1,[z1,z245,z8,z4,z5,z6])],[(0,[z30,z1,z2,z8,z4,z18,z6]),(1,[z1,z2,z8,z272,z5,z6]),(0,[z252,z31,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z366,z5,z6])],[(1,[z2,z3,z8,z4,z18,z6]),(0,[z315,z1,z2,z8,z4,z5,z6]),(0,[z1,z171,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z18,z281,z6]),(0,[z256,z31,z1,z8,z4,z5,z6]),(0,[z31,z1,z56,z8,z4,z5,z6]),(0,[z1,z2,z40,z8,z4,z6,z69]),(1,[z1,z367,z8,z4,z5,z6])]],
   [[(0,[z37,z58,z2,z8,z4,z5,z6]),(0,[z31,z91,z1,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z46,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z368])],[(0,[z1,z2,z8,z4,z5,z369,z6]),(0,[z1,z2,z8,z4,z370,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z371]),(0,[z1,z2,z372,z8,z4,z5,z6]),(0,[z373,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z4,z25,z5,z6]),(0,[z1,z2,z8,z374,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z375,z6]),(0,[z1,z2,z8,z4,z376,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z377]),(0,[z1,z2,z378,z8,z4,z5,z6])],[(0,[z379,z1,z2,z8,z4,z5,z6]),(0,[z0,z91,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z235,z18,z6]),(0,[z380,z1,z2,z8,z4,z5,z6]),(0,[z381,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z305]),(0,[z1,z2,z8,z4,z5,z6,z382]),(0,[z1,z2,z66,z8,z4,z18,z6]),(0,[z1,z2,z8,z25,z79,z5,z6]),(0,[z1,z2,z383,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z69]),(0,[z1,z2,z8,z209,z4,z5,z6])],[(0,[z0,z16,z2,z8,z4,z5,z6]),(0,[z85,z1,z2,z8,z4,z359,z6]),(0,[z1,z2,z8,z4,z5,z384,z6]),(0,[z385,z1,z2,z8,z4,z5,z6]),(1,[z51,z1,z2,z8,z6,z20]),(0,[z51,z1,z2,z8,z5,z6,z20]),(0,[z1,z2,z60,z8,z4,z5,z53])],[(0,[z1,z2,z8,z4,z386,z5,z6]),(0,[z0,z1,z2,z8,z4,z338,z6]),(0,[z1,z2,z8,z4,z5,z6,z387]),(0,[z1,z2,z8,z4,z5,z6,z388]),(0,[z389,z1,z2,z8,z4,z5,z6])],[(0,[z185,z16,z2,z8,z4,z5,z6]),(0,[z1,z2,z17,z8,z4,z5,z6]),(0,[z31,z162,z1,z8,z4,z5,z6]),(0,[z1,z2,z390,z8,z4,z5,z6])],[(0,[z131,z1,z2,z8,z4,z46,z6]),(1,[z162,z1,z192,z4,z5,z6]),(0,[z1,z2,z68,z8,z4,z39,z6]),(0,[z1,z126,z2,z8,z4,z5,z6]),(0,[z1,z2,z50,z8,z4,z67,z5])]],
   [[(0,[z391,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z392,z8,z4,z5,z6]),(0,[z229,z83,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z393]),(0,[z1,z2,z117,z34,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z394]),(0,[z1,z2,z395,z8,z4,z5,z6])],[(0,[z396,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z46,z6,z27]),(0,[z1,z66,z8,z192,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z397,z6]),(0,[z51,z1,z311,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z398,z6]),(0,[z152,z1,z118,z8,z4,z5,z6])],[(0,[z1,z2,z399,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z400,z5,z6])],[(0,[z401,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z18,z26,z6]),(0,[z402,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z403,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z404]),(0,[z405,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z130,z5,z6]),(0,[z1,z8,z63,z4,z130,z5,z6]),(0,[z406,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z407,z8,z4,z5,z6])],[(0,[z408,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z68,z8,z4,z18,z6]),(0,[z1,z2,z409,z8,z4,z5,z6]),(0,[z410,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z411,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z412])],[(0,[z1,z2,z413,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z414,z6]),(0,[z1,z2,z415,z8,z4,z5,z6]),(1,[z1,z2,z60,z8,z5,z54])],[(0,[z1,z2,z269,z8,z4,z18,z6]),(0,[z162,z1,z2,z8,z4,z46,z6]),(0,[z31,z1,z2,z8,z4,z5,z6]),(0,[z416,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z118,z8,z4,z5,z54])]],
   [[(0,[z417,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z418])],[(0,[z1,z2,z419,z8,z4,z5,z6]),(0,[z1,z420,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z421,z6]),(0,[z1,z2,z34,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z18,z6,z14]),(0,[z1,z2,z8,z4,z5,z265,z6]),(0,[z85,z1,z2,z8,z4,z5,z86])],[(0,[z1,z2,z8,z4,z5,z6,z422]),(0,[z423,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z424,z5,z6]),(0,[z1,z8,z4,z25,z5,z6,z425]),(0,[z1,z2,z8,z4,z5,z6,z426]),(0,[z1,z2,z427,z8,z4,z5,z6]),(0,[z1,z2,z428,z8,z4,z5,z6])],[(0,[z58,z2,z269,z8,z4,z5,z6]),(0,[z1,z2,z8,z429,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z430,z6]),(0,[z91,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z431,z4,z5,z6]),(0,[z1,z2,z8,z62,z4,z46,z6]),(0,[z1,z8,z4,z25,z5,z281,z6]),(0,[z31,z145,z1,z8,z4,z5,z6]),(0,[z1,z2,z432,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z433,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z434]),(0,[z1,z2,z435,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z5,z436,z6]),(0,[z1,z2,z8,z4,z5,z437,z6])],[(0,[z438,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z439]),(0,[z2,z3,z8,z4,z5,z200,z6]),(0,[z1,z2,z8,z4,z5,z440,z6]),(0,[z441,z1,z2,z8,z4,z5,z6]),(0,[z442,z1,z2,z8,z4,z5,z6])],[(0,[z1,z56,z8,z4,z19,z5,z6]),(0,[z1,z2,z34,z8,z5,z53,z6]),(0,[z1,z2,z8,z4,z5,z6,z443])],[(0,[z1,z2,z444,z8,z4,z5,z6]),(0,[z185,z1,z2,z8,z235,z5,z6]),(0,[z16,z2,z8,z4,z235,z5,z6]),(0,[z445,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z46,z19,z6]),(0,[z1,z2,z68,z8,z4,z46,z6]),(0,[z1,z171,z2,z8,z4,z5,z27])]],
   [[(0,[z58,z1,z8,z4,z25,z5,z6]),(0,[z1,z8,z76,z4,z25,z5,z6]),(0,[z1,z2,z8,z4,z197,z46,z6]),(0,[z47,z2,z8,z4,z5,z200,z6])],[(0,[z37,z1,z2,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z46,z6,z20]),(0,[z31,z1,z8,z446,z4,z5,z6]),(0,[z1,z447,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z448,z6]),(0,[z1,z2,z8,z4,z5,z6,z449]),(0,[z1,z2,z8,z4,z450,z5,z6])],[(1,[z1,z2,z8,z4,z170,z6]),(1,[z1,z2,z8,z4,z225,z6])],[(0,[z1,z2,z8,z451,z4,z5,z6]),(0,[z1,z2,z238,z8,z4,z18,z6]),(0,[z1,z2,z34,z8,z4,z46,z6]),(0,[z1,z2,z8,z452,z4,z5,z6]),(0,[z1,z2,z8,z62,z5,z6,z54]),(0,[z1,z2,z8,z453,z4,z5,z6]),(0,[z1,z2,z4,z5,z281,z6,z14]),(0,[z1,z2,z8,z4,z5,z6,z454])],[(0,[z1,z2,z455,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z456,z6]),(0,[z1,z2,z8,z4,z5,z457,z6]),(0,[z1,z2,z8,z296,z4,z5,z6]),(0,[z1,z2,z50,z8,z4,z6,z82])],[(0,[z1,z2,z8,z458,z4,z5,z6]),(0,[z459,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z460,z4,z5,z6])],[(1,[z1,z2,z8,z4,z136,z6]),(0,[z1,z2,z8,z4,z461,z5,z6]),(0,[z1,z2,z87,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z48,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z425]),(0,[z31,z1,z160,z8,z4,z5,z6]),(0,[z1,z2,z8,z462,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z463,z6]),(0,[z1,z2,z214,z8,z4,z46,z6]),(0,[z131,z1,z2,z8,z193,z5,z6]),(0,[z1,z8,z4,z25,z5,z26,z6]),(0,[z1,z2,z8,z4,z5,z464,z6]),(0,[z101,z1,z2,z8,z4,z67,z6]),(0,[z1,z2,z8,z4,z5,z281,z6])]],
   [[(0,[z1,z2,z8,z4,z146,z5,z6]),(0,[z465,z1,z2,z8,z4,z5,z6]),(0,[z0,z31,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z62,z235,z5,z6]),(0,[z1,z8,z4,z25,z5,z18,z6]),(0,[z31,z1,z60,z8,z4,z5,z6])],[(0,[z31,z185,z1,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z5,z53,z6]),(0,[z114,z1,z2,z8,z4,z5,z26]),(1,[z466,z1,z8,z4,z5,z6])],[(0,[z1,z2,z467,z8,z4,z5,z6]),(0,[z1,z2,z40,z8,z4,z39,z6])],[(0,[z1,z2,z468,z8,z4,z5,z6]),(0,[z1,z2,z469,z8,z4,z5,z6]),(0,[z1,z2,z470,z8,z4,z5,z6]),(0,[z51,z1,z367,z8,z4,z5,z6])],[(0,[z1,z471,z2,z8,z4,z5,z6]),(0,[z91,z1,z2,z8,z4,z224,z6]),(0,[z1,z2,z8,z192,z4,z46,z6]),(0,[z31,z1,z182,z8,z4,z5,z6]),(0,[z1,z2,z472,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z473,z6]),(0,[z1,z8,z4,z25,z5,z6,z14]),(0,[z31,z1,z8,z4,z25,z5,z6]),(0,[z51,z1,z2,z8,z4,z67,z6])],[(0,[z114,z1,z2,z8,z4,z18,z6]),(0,[z85,z1,z2,z8,z4,z46,z6]),(0,[z474,z1,z8,z4,z25,z5,z6]),(0,[z1,z330,z2,z8,z4,z5,z6]),(0,[z1,z2,z475,z8,z4,z5,z6]),(0,[z466,z1,z2,z8,z4,z5,z6]),(0,[z51,z1,z2,z8,z209,z5,z6]),(0,[z1,z2,z8,z4,z67,z5,z82])],[(0,[z83,z1,z8,z4,z25,z5,z6]),(0,[z16,z2,z8,z4,z46,z5,z6]),(0,[z1,z2,z8,z4,z46,z6,z82]),(0,[z208,z31,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z476,z5,z6]),(0,[z477,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z478,z5,z6]),(0,[z1,z2,z8,z479,z4,z5,z6]),(0,[z1,z2,z8,z480,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z4,z5,z481,z6])],[(0,[z91,z1,z8,z4,z25,z5,z6]),(0,[z482,z1,z2,z8,z4,z5,z6]),(0,[z94,z1,z8,z4,z25,z5,z6]),(0,[z1,z483,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z360,z5,z6])],[(0,[z1,z2,z8,z209,z4,z6,z69]),(0,[z1,z166,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z484,z4,z5,z6]),(0,[z1,z2,z8,z485,z4,z5,z6]),(0,[z486,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z487,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z26,z6]),(0,[z1,z2,z117,z8,z4,z414,z6])],[(0,[z30,z2,z8,z4,z5,z18,z6]),(0,[z1,z2,z8,z4,z46,z124,z6]),(0,[z1,z2,z8,z488,z4,z5,z6]),(1,[z489,z1,z8,z4,z5,z6])],[(0,[z37,z1,z2,z8,z4,z43,z6]),(0,[z1,z2,z490,z8,z4,z5,z6]),(0,[z491,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z492]),(0,[z1,z2,z8,z4,z5,z141,z6]),(0,[z1,z2,z8,z4,z5,z6,z493]),(0,[z1,z2,z8,z209,z4,z79,z6])],[(0,[z1,z2,z3,z8,z4,z5,z6]),(0,[z1,z2,z494,z8,z4,z5,z6]),(0,[z1,z2,z8,z495,z4,z5,z6]),(0,[z131,z1,z2,z66,z4,z5,z6]),(0,[z31,z1,z8,z4,z5,z6,z54]),(1,[z1,z8,z4,z257,z5,z6])],[(1,[z1,z2,z8,z4,z5,z6]),(0,[z185,z1,z2,z8,z4,z496,z6]),(0,[z497,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z498,z8,z4,z5,z6])]],
   [[(0,[z31,z58,z1,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z46,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z499]),(0,[z1,z2,z8,z79,z5,z6,z20]),(0,[z500,z1,z2,z8,z4,z5,z6])],[(0,[z501,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z502]),(0,[z1,z2,z8,z4,z5,z6,z14]),(0,[z1,z2,z50,z8,z4,z5,z6])],[(0,[z503,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z40,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z306,z5,z6])],[(0,[z38,z1,z8,z4,z25,z5,z6]),(0,[z31,z1,z8,z4,z235,z5,z6]),(0,[z1,z2,z8,z504,z4,z5,z6]),(0,[z1,z2,z8,z4,z67,z18,z6]),(0,[z505,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z506,z4,z5,z6]),(0,[z507,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z508]),(0,[z1,z2,z509,z8,z4,z5,z6])],[(0,[z1,z2,z510,z8,z4,z5,z6]),(0,[z162,z1,z8,z192,z4,z5,z6]),(0,[z1,z511,z2,z8,z4,z5,z6]),(0,[z31,z1,z66,z8,z4,z5,z6]),(0,[z512,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z513,z5,z6])],[(0,[z514,z1,z2,z8,z4,z5,z6]),(0,[z515,z1,z2,z8,z4,z5,z6])],[(0,[z162,z1,z2,z66,z4,z5,z6]),(1,[z1,z117,z8,z25,z5,z6]),(0,[z208,z1,z8,z4,z5,z124,z6]),(0,[z1,z56,z2,z8,z4,z19,z6]),(1,[z1,z2,z8,z5,z516,z6])],[(0,[z1,z2,z8,z4,z517,z5,z6]),(0,[z316,z1,z2,z8,z4,z18,z6]),(0,[z1,z2,z518,z8,z4,z5,z6]),(0,[z1,z56,z2,z8,z231,z5,z6]),(0,[z1,z2,z8,z4,z519,z5,z6]),(1,[z290,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z39,z6,z82]),(0,[z1,z2,z520,z8,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z4,z73,z46,z6]),(0,[z47,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z521]),(0,[z1,z40,z8,z4,z25,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z325]),(0,[z1,z2,z8,z4,z5,z178,z6]),(0,[z1,z2,z522,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z523,z5,z6]),(0,[z489,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z524,z6]),(0,[z290,z2,z8,z4,z39,z5,z6]),(0,[z1,z2,z8,z4,z525,z5,z6]),(0,[z1,z2,z8,z4,z526,z5,z6])],[(0,[z1,z2,z527,z8,z4,z5,z6])],[(0,[z0,z1,z2,z8,z4,z184,z6]),(1,[z1,z2,z8,z4,z186,z6]),(0,[z1,z2,z100,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z528,z5,z6]),(0,[z1,z243,z2,z8,z4,z5,z6]),(0,[z1,z87,z8,z4,z25,z5,z6]),(1,[z1,z2,z8,z4,z376,z6])],[(0,[z1,z2,z529,z8,z4,z5,z6]),(0,[z1,z2,z8,z530,z4,z5,z6]),(1,[z1,z8,z4,z5,z6,z155]),(0,[z1,z2,z8,z4,z5,z531,z6]),(0,[z106,z1,z2,z8,z4,z25,z6]),(0,[z532,z1,z2,z8,z4,z5,z6]),(0,[z1,z166,z60,z8,z4,z5,z6]),(0,[z1,z2,z118,z8,z5,z53,z6])],[(0,[z533,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z46,z5,z6]),(0,[z534,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z117,z8,z4,z5,z6]),(0,[z1,z2,z60,z34,z8,z5,z6])],[(0,[z1,z2,z8,z4,z535,z5,z6]),(0,[z1,z2,z8,z4,z18,z53,z6]),(0,[z536,z1,z2,z8,z4,z5,z6]),(0,[z1,z537,z2,z8,z4,z5,z6]),(0,[z1,z2,z538,z8,z4,z5,z6])],[(0,[z38,z58,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z539,z4,z5,z6]),(0,[z31,z31,z1,z8,z4,z5,z6]),(0,[z31,z1,z68,z8,z4,z5,z6]),(0,[z1,z2,z540,z8,z4,z5,z6]),(0,[z114,z1,z2,z8,z4,z5,z27]),(0,[z1,z2,z8,z4,z541,z5,z6])],[(0,[z1,z2,z118,z8,z25,z5,z6]),(0,[z417,z31,z1,z8,z4,z5,z6]),(0,[z1,z2,z542,z8,z4,z5,z6])]],
   [[(0,[z31,z1,z269,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z224,z6]),(1,[z2,z8,z4,z235,z18,z6]),(0,[z131,z1,z2,z8,z4,z18,z6]),(0,[z1,z2,z118,z8,z4,z46,z6]),(0,[z1,z435,z8,z4,z25,z5,z6]),(0,[z1,z2,z543,z8,z4,z5,z6]),(0,[z1,z544,z2,z8,z4,z5,z6]),(1,[z1,z142,z8,z4,z5,z6])],[(0,[z1,z1,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z5,z6,z6]),(0,[z1,z2,z8,z4,z5,z6,z545]),(0,[z31,z1,z171,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z546]),(0,[z1,z2,z8,z4,z5,z6,z547])],[(0,[z548,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z79,z18,z6]),(0,[z94,z31,z1,z8,z4,z5,z6]),(0,[z31,z1,z34,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z549,z6]),(0,[z1,z550,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z5,z6,z551,z14]),(0,[z1,z2,z8,z4,z5,z552,z6])],[(1,[z1,z2,z8,z4,z338,z6]),(0,[z185,z1,z2,z8,z4,z18,z6]),(0,[z1,z2,z45,z8,z4,z5,z6]),(0,[z114,z1,z2,z8,z296,z5,z6]),(0,[z1,z2,z8,z4,z167,z6,z54]),(0,[z1,z2,z68,z8,z4,z5,z82])],[(0,[z1,z2,z8,z4,z18,z6,z553]),(0,[z1,z8,z4,z25,z554,z5,z6]),(1,[z106,z1,z2,z8,z4,z6]),(0,[z1,z2,z8,z555,z4,z5,z6]),(0,[z1,z2,z556,z8,z4,z5,z6])],[(0,[z58,z1,z2,z8,z4,z5,z6]),(0,[z557,z1,z2,z8,z4,z5,z6]),(0,[z31,z16,z1,z8,z4,z5,z6]),(1,[z1,z8,z4,z25,z5,z6]),(0,[z1,z2,z558,z8,z4,z5,z6])],[(0,[z559,z1,z2,z8,z4,z5,z6]),(0,[z64,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z36,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z233])]],
   [[(0,[z1,z2,z560,z8,z4,z5,z6]),(0,[z162,z1,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z5,z6,z105]),(0,[z1,z2,z561,z8,z4,z5,z6])],[(0,[z1,z2,z562,z8,z4,z5,z6]),(0,[z563,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z564,z8,z4,z5,z6]),(0,[z1,z565,z8,z4,z25,z5,z6]),(0,[z1,z2,z8,z4,z19,z5,z6])],[(0,[z1,z2,z8,z4,z5,z43,z6]),(0,[z1,z2,z8,z4,z18,z6,z54]),(0,[z31,z1,z8,z4,z5,z6,z86]),(0,[z1,z2,z8,z4,z5,z6,z566]),(0,[z1,z2,z300,z8,z4,z5,z6]),(0,[z2,z8,z4,z39,z5,z141,z6]),(0,[z1,z2,z160,z8,z4,z5,z14]),(0,[z1,z2,z8,z4,z257,z5,z6])],[(0,[z1,z2,z8,z4,z567,z5,z6]),(0,[z0,z1,z2,z8,z4,z46,z6]),(0,[z1,z568,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z4,z5,z6]),(0,[z1,z1,z2,z8,z4,z46,z6]),(0,[z1,z56,z2,z8,z4,z124,z6]),(0,[z569,z1,z2,z8,z4,z5,z6])],[(0,[z85,z2,z3,z8,z4,z5,z6]),(0,[z1,z2,z8,z62,z4,z18,z6]),(0,[z1,z2,z570,z8,z4,z5,z6]),(0,[z1,z171,z8,z4,z5,z26,z6]),(0,[z1,z2,z8,z4,z39,z5,z6]),(0,[z1,z2,z8,z4,z5,z571,z6]),(0,[z1,z2,z8,z4,z5,z572,z6]),(0,[z1,z2,z68,z8,z4,z67,z6])],[(0,[z1,z2,z8,z4,z573,z5,z6]),(0,[z185,z1,z2,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z473,z18,z6]),(0,[z44,z1,z2,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z5,z124,z6]),(0,[z101,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z209,z4,z39,z6]),(0,[z1,z2,z8,z5,z516,z6,z14])],[(0,[z1,z2,z8,z574,z4,z5,z6]),(0,[z47,z1,z8,z4,z25,z5,z6]),(0,[z1,z2,z575,z8,z4,z5,z6])],[(0,[z112,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z18,z18,z6])]],
   [[(0,[z1,z2,z8,z4,z5,z576,z6]),(1,[z2,z8,z4,z46,z18,z6]),(0,[z1,z243,z8,z4,z25,z5,z6]),(0,[z328,z1,z8,z4,z5,z6,z14]),(0,[z1,z2,z182,z8,z4,z5,z14])],[(0,[z1,z2,z8,z4,z184,z5,z6]),(0,[z1,z8,z4,z25,z5,z53,z6]),(0,[z1,z2,z8,z4,z577,z5,z6])],[(0,[z37,z1,z2,z8,z4,z18,z6]),(0,[z208,z1,z2,z8,z4,z46,z6]),(0,[z31,z1,z8,z4,z5,z200,z6]),(1,[z51,z1,z8,z25,z5,z6]),(0,[z1,z2,z117,z8,z25,z5,z6]),(1,[z1,z35,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z516,z6])],[(0,[z1,z2,z578,z8,z4,z5,z6]),(0,[z1,z2,z8,z579,z4,z5,z6]),(0,[z580,z1,z2,z8,z4,z5,z6]),(0,[z0,z2,z8,z76,z4,z5,z6]),(0,[z1,z2,z581,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z77,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z582]),(0,[z85,z1,z2,z8,z4,z5,z200]),(0,[z474,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z583,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z584,z5,z6]),(0,[z585,z1,z2,z8,z4,z5,z6])],[(1,[z1,z2,z8,z4,z369,z6]),(0,[z83,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z586,z8,z4,z5,z6]),(0,[z1,z2,z34,z8,z73,z5,z6]),(0,[z1,z2,z8,z4,z5,z587,z6]),(0,[z1,z2,z8,z4,z5,z6,z588])],[(0,[z589,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z25,z5,z6]),(0,[z1,z68,z8,z4,z25,z5,z6]),(0,[z1,z2,z8,z446,z4,z5,z6]),(0,[z590,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z119,z5,z6]),(0,[z1,z2,z8,z4,z591,z5,z6])],[(0,[z94,z1,z2,z8,z4,z5,z6]),(0,[z1,z592,z2,z8,z4,z5,z6]),(0,[z31,z1,z243,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z301,z5,z6]),(0,[z1,z2,z8,z4,z593,z5,z6]),(0,[z1,z2,z594,z8,z4,z5,z6]),(1,[z120,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z595,z5,z6])],[(0,[z1,z2,z596,z8,z4,z5,z6]),(0,[z1,z2,z597,z8,z4,z5,z6]),(0,[z1,z2,z87,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z5,z6,z155]),(0,[z1,z56,z2,z8,z319,z5,z6]),(0,[z598,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z599,z6]),(0,[z1,z2,z600,z8,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z4,z5,z6,z601])],[(0,[z1,z2,z8,z4,z5,z602,z6]),(0,[z1,z603,z2,z8,z4,z5,z6]),(0,[z162,z131,z1,z8,z4,z5,z6]),(0,[z466,z1,z34,z8,z4,z5,z6])],[(0,[z604,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z605,z8,z4,z5,z6]),(0,[z1,z2,z160,z8,z4,z5,z6]),(0,[z606,z1,z2,z8,z4,z5,z6])],[(0,[z607,z1,z2,z8,z4,z5,z6]),(0,[z0,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z138,z6]),(0,[z2,z8,z4,z235,z5,z18,z6]),(0,[z608,z1,z2,z8,z4,z5,z6])],[(0,[z609,z1,z2,z8,z4,z5,z6]),(0,[z610,z1,z2,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z397,z6]),(0,[z1,z2,z245,z8,z4,z5,z6]),(0,[z1,z2,z142,z8,z4,z5,z6])],[(0,[z611,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z192,z4,z18,z6]),(0,[z1,z2,z8,z209,z4,z46,z6]),(0,[z1,z2,z8,z4,z5,z612,z6]),(0,[z1,z2,z613,z8,z4,z5,z6]),(0,[z1,z8,z361,z4,z25,z5,z6]),(0,[z1,z2,z117,z87,z8,z5,z6]),(0,[z1,z2,z8,z614,z4,z5,z6])],[(1,[z58,z269,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z615,z5,z6]),(1,[z31,z1,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z5,z6,z54]),(0,[z1,z616,z2,z8,z4,z5,z6]),(0,[z1,z2,z617,z8,z4,z5,z6]),(0,[z1,z2,z367,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z618,z5,z6])],[(0,[z229,z1,z2,z8,z4,z5,z6]),(1,[z83,z2,z8,z235,z5,z6]),(0,[z85,z1,z2,z8,z4,z18,z6]),(1,[z1,z8,z25,z5,z6,z54]),(0,[z1,z2,z8,z4,z299,z5,z6]),(1,[z1,z2,z160,z4,z5,z14]),(0,[z1,z619,z2,z8,z4,z5,z6])]],
   [[(0,[z38,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z5,z144,z6]),(0,[z501,z31,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z62,z79,z5,z6]),(0,[z1,z2,z620,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z621,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z622]),(0,[z1,z2,z182,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z424,z5,z6]),(0,[z623,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z25,z5,z6]),(0,[z1,z2,z8,z4,z5,z624,z6]),(1,[z1,z2,z8,z4,z414,z6])],[(0,[z625,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z626,z8,z4,z5,z6])],[(0,[z1,z269,z8,z4,z25,z5,z6]),(0,[z627,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z235,z5,z6]),(0,[z396,z1,z2,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z46,z6,z69]),(0,[z101,z1,z8,z4,z25,z5,z6]),(0,[z512,z31,z1,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z167,z6])],[(0,[z628,z1,z2,z8,z4,z5,z6]),(1,[z1,z8,z25,z235,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z553]),(0,[z31,z1,z8,z4,z67,z5,z6]),(0,[z1,z2,z34,z8,z62,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z629])],[(0,[z1,z2,z8,z4,z199,z5,z6]),(0,[z1,z2,z160,z8,z4,z376,z6]),(0,[z630,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z355,z4,z5,z6]),(0,[z1,z2,z8,z4,z18,z6,z86]),(0,[z1,z202,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z46,z79,z6]),(0,[z1,z2,z631,z8,z4,z5,z6])],[(0,[z632,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z409,z8,z4,z46,z6]),(1,[z1,z2,z8,z4,z359,z6]),(0,[z1,z2,z8,z209,z79,z5,z6])]],
   [[(0,[z31,z1,z2,z8,z25,z5,z6]),(0,[z1,z2,z8,z4,z5,z633,z6])],[(0,[z31,z1,z2,z8,z4,z46,z6]),(0,[z51,z1,z8,z4,z25,z5,z6]),(0,[z1,z56,z2,z8,z209,z4,z6])],[(0,[z58,z1,z2,z8,z4,z369,z6]),(0,[z1,z2,z8,z76,z4,z46,z6]),(0,[z634,z1,z2,z8,z4,z5,z6]),(0,[z1,z66,z8,z4,z5,z26,z6]),(0,[z284,z1,z2,z8,z4,z5,z6]),(0,[z328,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z635]),(0,[z1,z2,z8,z4,z5,z6,z54])],[(1,[z1,z2,z8,z341,z5,z6]),(1,[z1,z2,z8,z4,z496,z6]),(0,[z30,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z40,z8,z4,z18,z6])],[(0,[z1,z2,z8,z4,z5,z636,z6]),(0,[z16,z1,z8,z4,z25,z5,z6]),(0,[z1,z2,z637,z8,z4,z5,z6]),(0,[z1,z171,z2,z8,z4,z5,z6]),(1,[z317,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z638,z6])],[(0,[z1,z2,z8,z4,z639,z5,z6]),(0,[z91,z1,z2,z8,z4,z46,z6]),(0,[z640,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z24,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z5,z6,z27]),(0,[z1,z2,z641,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z18,z200,z6]),(0,[z1,z2,z35,z8,z4,z5,z6]),(0,[z489,z1,z87,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z642])],[(0,[z1,z2,z8,z4,z122,z5,z6]),(0,[z0,z2,z8,z4,z5,z18,z6]),(0,[z1,z2,z8,z4,z235,z5,z6]),(0,[z1,z2,z8,z4,z5,z18,z6]),(0,[z1,z643,z2,z8,z4,z5,z6]),(0,[z101,z1,z2,z50,z8,z4,z6]),(0,[z1,z2,z8,z13,z4,z5,z6]),(0,[z1,z2,z644,z8,z4,z5,z6])]],
   [[(0,[z114,z37,z1,z8,z4,z5,z6]),(0,[z201,z1,z2,z8,z4,z5,z6]),(1,[z1,z8,z63,z25,z5,z6]),(0,[z1,z2,z66,z8,z4,z5,z6]),(1,[z1,z8,z4,z5,z6,z551])],[(0,[z185,z2,z8,z4,z5,z18,z6]),(0,[z1,z2,z8,z4,z73,z18,z6]),(0,[z1,z56,z8,z4,z25,z5,z6]),(0,[z1,z2,z645,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z646]),(0,[z1,z2,z8,z647,z4,z5,z6]),(0,[z83,z1,z2,z8,z4,z241,z6]),(0,[z648,z1,z2,z8,z4,z5,z6]),(0,[z317,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z649,z5,z6])],[(0,[z650,z1,z2,z8,z4,z5,z6]),(0,[z651,z1,z2,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z79,z5,z6]),(0,[z1,z652,z2,z8,z4,z5,z6]),(0,[z51,z1,z2,z8,z4,z6,z20])],[(0,[z1,z2,z8,z4,z5,z6,z653]),(0,[z1,z2,z8,z4,z5,z6,z654]),(0,[z1,z2,z8,z4,z46,z6,z434]),(0,[z1,z2,z8,z4,z5,z6,z655]),(1,[z31,z1,z8,z25,z5,z6]),(0,[z1,z2,z8,z4,z132,z5,z6]),(0,[z1,z2,z8,z656,z4,z5,z6]),(0,[z101,z1,z2,z8,z4,z6,z69]),(0,[z1,z2,z8,z4,z360,z6,z54])],[(0,[z51,z1,z2,z50,z8,z4,z6]),(0,[z1,z2,z657,z8,z4,z5,z6])],[(0,[z58,z1,z269,z8,z4,z5,z6]),(0,[z1,z2,z8,z63,z4,z5,z6]),(0,[z1,z2,z658,z8,z4,z5,z6])],[(0,[z38,z1,z2,z8,z4,z46,z6]),(0,[z1,z2,z659,z8,z4,z5,z6])]],
   [[(0,[z83,z1,z2,z8,z235,z5,z6]),(0,[z185,z2,z8,z63,z4,z5,z6]),(0,[z660,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z461,z46,z6]),(0,[z661,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z662]),(0,[z1,z2,z663,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z664,z6]),(0,[z1,z2,z118,z8,z4,z18,z6])],[(0,[z665,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z5,z6,z86]),(0,[z666,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z117,z8,z4,z147,z6]),(0,[z51,z1,z2,z8,z4,z6,z69]),(0,[z667,z1,z2,z8,z4,z5,z6]),(0,[z1,z668,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z669,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z670,z6])],[(0,[z1,z2,z269,z8,z4,z5,z6]),(0,[z37,z38,z1,z8,z4,z5,z6]),(0,[z131,z1,z2,z8,z272,z5,z6]),(0,[z1,z160,z8,z4,z25,z5,z6]),(0,[z101,z31,z1,z8,z4,z5,z6])],[(0,[z2,z8,z4,z46,z5,z18,z6]),(0,[z47,z1,z2,z8,z4,z5,z86]),(0,[z1,z8,z4,z25,z5,z124,z6]),(0,[z31,z1,z8,z4,z5,z6,z20]),(0,[z31,z1,z8,z62,z4,z5,z6]),(1,[z1,z2,z8,z301,z5,z6]),(0,[z51,z1,z2,z8,z4,z79,z6]),(0,[z1,z2,z671,z8,z4,z5,z6])],[(0,[z1,z2,z3,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z672,z5,z6]),(0,[z1,z2,z40,z4,z39,z5,z6])],[(0,[z1,z2,z673,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z46,z281,z6]),(1,[z85,z2,z8,z4,z5,z86]),(1,[z1,z2,z8,z4,z119,z6])]],
   [[(0,[z1,z2,z8,z25,z235,z5,z6]),(0,[z1,z2,z8,z4,z674,z5,z6]),(0,[z1,z2,z8,z4,z5,z675,z6]),(0,[z1,z311,z2,z8,z4,z5,z6]),(0,[z1,z676,z2,z8,z4,z5,z6])],[(0,[z58,z1,z2,z8,z341,z5,z6]),(0,[z30,z1,z8,z4,z25,z5,z6])],[(0,[z1,z8,z4,z25,z5,z200,z6]),(0,[z1,z171,z8,z4,z25,z5,z6]),(0,[z51,z31,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z677,z5,z6]),(0,[z1,z2,z8,z678,z4,z5,z6])],[(0,[z1,z8,z62,z4,z25,z5,z6])],[(0,[z0,z1,z2,z8,z4,z18,z6]),(1,[z106,z1,z8,z4,z25,z6]),(0,[z589,z31,z1,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z5,z6,z69])],[(1,[z315,z1,z8,z4,z5,z6]),(0,[z514,z1,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z5,z6,z679]),(0,[z1,z2,z680,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z681,z6]),(0,[z1,z2,z60,z8,z4,z5,z54])],[(0,[z1,z2,z8,z4,z46,z39,z6]),(0,[z1,z2,z8,z4,z5,z6,z86]),(0,[z682,z1,z2,z8,z4,z5,z6])],[(0,[z51,z208,z1,z2,z8,z4,z6]),(0,[z1,z2,z160,z8,z4,z397,z6]),(0,[z1,z683,z2,z8,z4,z5,z6]),(0,[z1,z2,z684,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z67,z82])]],
   [[(0,[z1,z2,z3,z8,z4,z46,z6]),(0,[z83,z1,z92,z8,z4,z5,z6]),(1,[z247,z1,z8,z4,z5,z6]),(0,[z31,z1,z87,z8,z4,z5,z6]),(0,[z1,z685,z2,z8,z4,z5,z6]),(0,[z1,z2,z686,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z687]),(1,[z126,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z688,z5,z6])],[(1,[z1,z2,z8,z4,z46,z6]),(0,[z1,z2,z118,z8,z62,z5,z6]),(0,[z1,z2,z8,z4,z689,z5,z6]),(1,[z1,z2,z8,z13,z5,z6])],[(0,[z1,z3,z8,z4,z25,z5,z6]),(0,[z114,z162,z1,z8,z4,z5,z6]),(0,[z1,z2,z690,z8,z4,z5,z6])],[(0,[z208,z1,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z46,z26,z6]),(0,[z1,z2,z50,z8,z4,z46,z6]),(0,[z31,z1,z8,z4,z5,z6,z82]),(0,[z1,z2,z8,z4,z67,z6,z82])],[(0,[z691,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z63,z25,z5,z6]),(0,[z1,z2,z117,z8,z4,z18,z6]),(0,[z1,z2,z8,z692,z4,z5,z6]),(1,[z1,z243,z8,z25,z5,z6]),(0,[z1,z2,z117,z87,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z551]),(0,[z693,z1,z2,z8,z4,z5,z6])],[],[(0,[z1,z2,z2,z8,z4,z5,z6]),(0,[z1,z2,z694,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z496,z5,z6]),(0,[z1,z2,z8,z4,z5,z200,z6]),(0,[z31,z1,z8,z192,z4,z5,z6]),(0,[z1,z34,z8,z4,z25,z5,z6]),(0,[z1,z2,z565,z8,z4,z5,z6]),(0,[z1,z2,z118,z8,z4,z5,z53])],[(0,[z131,z1,z66,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z695,z6])]],
   [[(1,[z1,z2,z8,z4,z241,z6]),(0,[z1,z2,z8,z4,z696,z5,z6]),(0,[z1,z2,z59,z8,z4,z5,z6]),(0,[z1,z345,z8,z4,z25,z5,z6]),(0,[z1,z697,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z517,z46,z6]),(0,[z1,z2,z8,z4,z46,z6,z14]),(0,[z698,z1,z2,z8,z4,z5,z6]),(0,[z699,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z117,z8,z5,z53,z6])],[(0,[z91,z1,z2,z8,z4,z138,z6]),(0,[z47,z1,z2,z8,z4,z46,z6]),(0,[z1,z2,z8,z700,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z701])],[(0,[z702,z1,z2,z8,z4,z5,z6]),(0,[z91,z2,z3,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z554,z5,z6]),(0,[z1,z243,z2,z8,z25,z5,z6]),(0,[z1,z2,z8,z4,z5,z436,z6]),(0,[z114,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z703,z8,z4,z5,z6])],[(0,[z1,z243,z2,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z5,z6,z347]),(1,[z1,z2,z8,z4,z48,z6]),(0,[z1,z8,z4,z25,z67,z5,z6]),(1,[z114,z1,z8,z4,z5,z27])],[(1,[z1,z8,z4,z25,z18,z6]),(0,[z1,z2,z8,z530,z4,z46,z6]),(0,[z162,z1,z8,z4,z5,z26,z6]),(0,[z1,z2,z8,z4,z704,z5,z6]),(0,[z210,z1,z2,z8,z4,z5,z6])],[(1,[z1,z2,z8,z122,z5,z6]),(0,[z1,z2,z8,z4,z89,z18,z6]),(0,[z1,z2,z8,z209,z4,z18,z6]),(0,[z1,z2,z8,z4,z46,z46,z6]),(0,[z1,z2,z117,z8,z4,z46,z6]),(0,[z215,z1,z2,z8,z4,z5,z6]),(0,[z51,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z705,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z706])],[(0,[z2,z3,z8,z76,z4,z5,z6]),(0,[z185,z1,z2,z8,z63,z5,z6]),(0,[z101,z1,z2,z8,z4,z39,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z707,z1,z8,z4,z5,z6]),(0,[z466,z1,z8,z4,z18,z6]),(0,[z1,z345,z8,z4,z5,z425]),(0,[z1,z708,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z11,z82])],[(0,[z1,z663,z8,z25,z5,z6]),(0,[z1,z8,z4,z19,z709,z6])],[(0,[z710,z1,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z67,z82]),(0,[z1,z2,z60,z8,z5,z711])],[(0,[z1,z2,z8,z712,z5,z6]),(0,[z85,z2,z8,z4,z359,z86]),(0,[z31,z1,z8,z25,z5,z6]),(0,[z1,z8,z4,z713,z5,z6])],[(0,[z31,z1,z8,z4,z46,z6]),(0,[z2,z8,z4,z18,z6,z434]),(0,[z1,z2,z8,z4,z714,z6]),(0,[z52,z2,z8,z4,z46,z6]),(0,[z31,z1,z8,z13,z5,z6]),(0,[z715,z2,z8,z4,z5,z6])],[(0,[z1,z2,z716,z8,z5,z6]),(0,[z1,z717,z8,z4,z5,z6]),(0,[z83,z2,z8,z235,z46,z6]),(0,[z2,z321,z8,z4,z18,z6]),(0,[z1,z8,z4,z5,z718,z27]),(0,[z1,z2,z8,z4,z719,z6]),(0,[z1,z2,z160,z13,z5,z14])],[(0,[z16,z8,z25,z235,z5,z6]),(0,[z1,z720,z8,z25,z5,z6]),(0,[z1,z8,z4,z709,z124,z6])],[(0,[z1,z2,z8,z122,z369,z6]),(0,[z1,z2,z8,z4,z721,z6]),(0,[z1,z2,z8,z4,z184,z6]),(0,[z2,z8,z4,z235,z98,z6]),(0,[z1,z202,z8,z4,z19,z6]),(0,[z1,z34,z8,z25,z5,z6]),(0,[z1,z2,z8,z4,z722,z6]),(0,[z208,z1,z8,z4,z132,z6])]],
   [[(0,[z112,z1,z8,z25,z5,z6]),(0,[z1,z8,z288,z25,z5,z6]),(0,[z1,z8,z4,z723,z25,z6]),(0,[z8,z4,z25,z5,z6,z233]),(0,[z1,z2,z8,z25,z167,z6])],[(0,[z724,z58,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z725,z6]),(0,[z1,z207,z8,z25,z5,z6])],[(0,[z1,z2,z8,z726,z5,z6]),(0,[z1,z2,z8,z4,z727,z6]),(0,[z1,z8,z25,z235,z46,z6]),(0,[z1,z2,z4,z5,z728,z6]),(0,[z1,z8,z4,z132,z25,z6]),(0,[z51,z1,z2,z8,z231,z6])],[(0,[z1,z2,z8,z4,z729,z6]),(0,[z31,z1,z8,z4,z241,z6]),(0,[z1,z730,z8,z4,z5,z6]),(0,[z31,z8,z4,z46,z18,z6]),(0,[z489,z1,z8,z4,z18,z6]),(0,[z1,z8,z4,z25,z731,z6])],[(0,[z99,z2,z8,z4,z18,z6]),(0,[z30,z8,z4,z25,z18,z6]),(0,[z2,z8,z4,z46,z41,z6]),(0,[z1,z2,z8,z732,z5,z6]),(0,[z1,z2,z8,z4,z733,z6])],[(0,[z315,z1,z8,z341,z5,z6]),(0,[z16,z2,z8,z4,z496,z6]),(0,[z2,z8,z4,z375,z18,z6]),(0,[z1,z8,z4,z257,z18,z6]),(0,[z734,z2,z8,z4,z5,z6]),(0,[z1,z8,z735,z4,z5,z6]),(0,[z51,z1,z2,z8,z6,z508]),(0,[z1,z2,z8,z4,z736,z6])],[(0,[z1,z2,z8,z4,z18,z6]),(0,[z0,z8,z4,z25,z18,z6]),(0,[z1,z2,z8,z4,z737,z6]),(0,[z85,z2,z8,z4,z5,z86]),(0,[z152,z1,z8,z4,z5,z6]),(0,[z1,z60,z8,z25,z5,z54]),(0,[z1,z2,z8,z4,z738,z6]),(0,[z1,z2,z8,z4,z119,z6]),(0,[z1,z2,z8,z4,z739,z6])],[(0,[z1,z2,z8,z4,z740,z6]),(0,[z1,z2,z8,z741,z5,z6]),(0,[z290,z2,z8,z4,z184,z6]),(0,[z31,z1,z8,z4,z48,z6]),(0,[z1,z8,z132,z25,z6,z54]),(0,[z742,z1,z8,z4,z5,z6]),(0,[z466,z1,z34,z73,z5,z6]),(0,[z2,z8,z4,z5,z743,z6])]],
   [[(0,[z1,z8,z4,z25,z138,z6]),(0,[z1,z92,z8,z4,z241,z6])],[(0,[z58,z269,z8,z122,z5,z6]),(0,[z31,z1,z8,z122,z5,z6]),(0,[z1,z2,z8,z341,z46,z6]),(0,[z2,z150,z8,z4,z18,z6]),(0,[z744,z1,z2,z8,z4,z6]),(0,[z208,z1,z8,z4,z709,z6]),(0,[z1,z2,z8,z4,z745,z6])],[(0,[z0,z2,z76,z4,z5,z6]),(0,[z317,z1,z8,z4,z46,z6]),(0,[z1,z746,z8,z4,z5,z6]),(0,[z1,z2,z8,z25,z147,z6]),(0,[z1,z747,z8,z4,z5,z6]),(0,[z748,z2,z8,z4,z5,z6])],[(0,[z1,z269,z8,z122,z5,z6]),(0,[z1,z2,z749,z8,z4,z5]),(0,[z1,z750,z8,z4,z5,z6]),(0,[z751,z1,z8,z4,z5,z6])],[(0,[z229,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z752,z6]),(0,[z1,z753,z8,z4,z5,z6]),(0,[z598,z2,z8,z4,z18,z6]),(0,[z1,z754,z8,z4,z5,z6]),(0,[z1,z249,z8,z25,z5,z6]),(0,[z31,z290,z8,z4,z5,z6]),(0,[z210,z1,z8,z231,z5,z6]),(0,[z755,z1,z8,z4,z5,z6]),(0,[z756,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z757,z6]),(0,[z758,z2,z8,z4,z5,z6])],[(0,[z1,z8,z4,z5,z6,z759]),(0,[z1,z2,z8,z4,z760,z6]),(0,[z1,z117,z8,z25,z18,z6]),(0,[z112,z1,z2,z8,z6,z434]),(0,[z1,z8,z4,z5,z6,z761])],[(0,[z1,z8,z254,z25,z5,z6]),(0,[z1,z92,z8,z235,z5,z6]),(0,[z1,z8,z63,z25,z46,z6]),(0,[z201,z1,z8,z4,z473,z6]),(0,[z290,z2,z8,z4,z18,z6]),(0,[z1,z8,z4,z25,z36,z6]),(0,[z1,z8,z25,z5,z6,z701]),(0,[z742,z1,z8,z5,z516,z6])],[(0,[z2,z8,z4,z141,z18,z6]),(0,[z162,z1,z762,z4,z5,z6]),(0,[z51,z1,z8,z132,z25,z6]),(0,[z1,z2,z8,z763,z301,z6]),(0,[z1,z2,z8,z4,z763,z6]),(0,[z1,z300,z34,z8,z5,z6])]],
   [[(0,[z1,z2,z8,z4,z46,z6]),(0,[z31,z1,z8,z4,z43,z6]),(0,[z1,z2,z8,z4,z764,z6]),(0,[z1,z2,z765,z4,z5,z6])],[(0,[z627,z1,z8,z25,z5,z6]),(0,[z1,z766,z8,z4,z5,z6]),(0,[z351,z2,z8,z4,z18,z6]),(0,[z1,z8,z261,z25,z5,z6]),(0,[z1,z8,z4,z25,z360,z6]),(0,[z1,z34,z35,z73,z5,z6])],[(0,[z1,z2,z8,z4,z767,z6])],[(0,[z128,z1,z8,z25,z5,z6]),(0,[z358,z2,z8,z4,z18,z6]),(0,[z1,z243,z8,z25,z5,z6]),(0,[z106,z1,z118,z8,z25,z6]),(0,[z2,z8,z4,z5,z6,z768]),(0,[z1,z8,z4,z5,z6,z769]),(0,[z1,z8,z301,z5,z6,z27]),(0,[z2,z8,z4,z5,z770,z6]),(0,[z101,z1,z2,z4,z6,z69]),(0,[z1,z8,z257,z79,z5,z6]),(0,[z1,z771,z8,z4,z5,z6])],[(0,[z2,z8,z4,z189,z18,z6]),(0,[z1,z8,z4,z46,z6,z551]),(0,[z1,z8,z272,z25,z5,z6]),(0,[z31,z1,z8,z4,z772,z6]),(0,[z1,z2,z8,z4,z6,z773]),(0,[z774,z1,z8,z4,z5,z6])],[(0,[z1,z8,z122,z25,z5,z6]),(0,[z1,z2,z8,z4,z775,z6]),(0,[z1,z8,z4,z25,z184,z6]),(0,[z632,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z776,z6]),(0,[z1,z2,z777,z4,z5,z6]),(0,[z1,z2,z8,z778,z5,z6]),(0,[z1,z8,z4,z25,z779,z6]),(0,[z1,z2,z285,z4,z6,z69])],[(0,[z1,z8,z573,z25,z5,z6]),(0,[z780,z1,z8,z4,z5,z6]),(0,[z126,z2,z8,z4,z39,z6])],[(0,[z0,z2,z458,z4,z5,z6]),(0,[z1,z142,z8,z4,z18,z6]),(0,[z112,z1,z8,z25,z46,z6]),(0,[z1,z2,z8,z5,z6,z781])]],
   [[(0,[z1,z782,z8,z4,z5,z6]),(0,[z1,z2,z783,z4,z5,z6]),(0,[z290,z2,z8,z4,z46,z6]),(0,[z1,z2,z762,z4,z5,z6])],[(0,[z120,z2,z8,z4,z496,z6]),(0,[z162,z1,z446,z4,z5,z6]),(0,[z1,z2,z8,z4,z784,z6])],[(0,[z83,z92,z8,z235,z5,z6]),(0,[z514,z1,z8,z4,z275,z6]),(0,[z1,z785,z8,z4,z46,z6]),(0,[z208,z1,z8,z231,z5,z6])],[(0,[z1,z2,z8,z4,z786,z6]),(0,[z1,z2,z8,z301,z46,z6]),(0,[z135,z2,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z787,z6]),(0,[z1,z2,z8,z4,z788,z6]),(0,[z114,z1,z8,z4,z5,z27]),(0,[z2,z8,z4,z147,z743,z6]),(0,[z1,z8,z13,z5,z6,z551])],[(0,[z1,z2,z8,z4,z789,z6]),(0,[z1,z8,z4,z790,z5,z6]),(0,[z1,z8,z4,z25,z18,z6]),(0,[z1,z2,z8,z4,z791,z6]),(0,[z1,z2,z8,z4,z743,z6]),(0,[z1,z2,z8,z5,z792,z6]),(0,[z284,z8,z4,z5,z6,z551])],[(0,[z1,z2,z8,z46,z516,z6]),(0,[z208,z1,z8,z4,z187,z6]),(0,[z1,z2,z4,z6,z793,z69]),(0,[z8,z4,z5,z6,z551,z233]),(0,[z1,z2,z8,z13,z119,z6])],[(0,[z0,z2,z76,z4,z338,z6]),(0,[z284,z2,z8,z4,z5,z6]),(0,[z44,z1,z8,z25,z18,z6]),(0,[z2,z8,z4,z5,z794,z86]),(0,[z1,z8,z25,z310,z5,z6]),(0,[z795,z1,z2,z8,z4,z6]),(0,[z1,z8,z4,z36,z6,z551]),(0,[z1,z2,z8,z796,z5,z6])],[(0,[z417,z1,z8,z25,z5,z6]),(0,[z0,z2,z8,z4,z138,z6]),(0,[z162,z1,z8,z193,z5,z6]),(0,[z1,z8,z4,z5,z797,z6]),(1,[z2,z8,z4,z743,z6])]],
   [[(0,[z798,z1,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z132,z6]),(0,[z648,z1,z8,z25,z5,z6]),(0,[z1,z544,z8,z25,z5,z6]),(0,[z1,z2,z8,z4,z799,z6])],[(0,[z1,z2,z8,z4,z146,z6]),(0,[z1,z2,z8,z4,z800,z6]),(0,[z31,z1,z8,z4,z138,z6]),(1,[z1,z8,z4,z709,z6]),(0,[z1,z2,z8,z4,z801,z6]),(0,[z1,z245,z34,z8,z5,z6])],[(0,[z315,z1,z8,z25,z5,z6])],[(0,[z1,z2,z8,z802,z5,z6]),(0,[z315,z1,z8,z4,z46,z6]),(0,[z16,z2,z8,z4,z46,z6]),(0,[z1,z2,z8,z296,z5,z6]),(0,[z31,z1,z8,z4,z147,z6]),(0,[z756,z1,z8,z13,z5,z6]),(0,[z1,z8,z5,z797,z516,z6])],[(0,[z1,z2,z8,z4,z43,z6]),(0,[z1,z2,z8,z4,z803,z6]),(0,[z114,z1,z8,z4,z5,z179]),(0,[z1,z2,z8,z804,z5,z6]),(0,[z208,z1,z8,z4,z257,z6])],[(0,[z1,z805,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z806,z6]),(0,[z1,z311,z8,z319,z5,z6]),(0,[z1,z807,z8,z4,z5,z6]),(0,[z284,z2,z8,z5,z516,z6])],[(0,[z1,z2,z8,z4,z808,z6]),(0,[z1,z2,z8,z809,z5,z6]),(0,[z1,z810,z8,z4,z5,z6]),(0,[z1,z318,z8,z25,z5,z6]),(0,[z247,z1,z8,z4,z46,z6]),(0,[z126,z2,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z811,z6]),(0,[z114,z1,z8,z301,z5,z27])],[(0,[z1,z2,z8,z4,z812,z6]),(0,[z2,z251,z8,z4,z18,z6]),(0,[z1,z2,z8,z813,z18,z6]),(0,[z1,z2,z8,z13,z46,z6]),(0,[z1,z2,z34,z133,z5,z6]),(0,[z1,z2,z8,z814,z5,z6]),(0,[z1,z2,z8,z36,z516,z6])]],
   [[(0,[z1,z2,z8,z4,z815,z6]),(0,[z1,z2,z8,z193,z5,z6]),(0,[z2,z8,z5,z516,z6,z233]),(0,[z1,z2,z816,z8,z4,z6])],[(0,[z2,z8,z817,z4,z5,z6]),(0,[z1,z35,z8,z4,z18,z6]),(0,[z51,z1,z8,z25,z18,z6]),(0,[z107,z2,z8,z4,z18,z6]),(0,[z1,z8,z4,z818,z5,z6]),(0,[z1,z8,z25,z147,z5,z6]),(0,[z1,z2,z8,z4,z819,z6])],[(0,[z229,z1,z8,z4,z241,z6])],[(0,[z83,z2,z8,z235,z98,z6]),(0,[z44,z1,z2,z8,z6,z553]),(0,[z389,z2,z8,z4,z18,z6]),(0,[z820,z1,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z821,z6]),(0,[z1,z8,z25,z343,z5,z6]),(0,[z1,z8,z25,z79,z5,z6])],[(0,[z822,z1,z8,z4,z5,z6]),(0,[z1,z8,z266,z25,z5,z6]),(0,[z1,z2,z8,z823,z5,z6]),(0,[z1,z2,z816,z8,z4,z5])],[(0,[z417,z1,z8,z122,z5,z6]),(0,[z114,z1,z8,z4,z5,z183]),(0,[z58,z483,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z824,z6]),(0,[z1,z123,z8,z25,z5,z6]),(0,[z1,z8,z63,z132,z25,z6]),(0,[z2,z8,z4,z18,z6,z687]),(0,[z120,z2,z8,z4,z18,z6]),(0,[z1,z160,z4,z25,z5,z14]),(0,[z1,z337,z8,z25,z5,z6]),(0,[z1,z2,z4,z5,z6,z793]),(0,[z1,z8,z4,z119,z6,z551])],[(0,[z1,z2,z8,z825,z5,z6]),(0,[z31,z1,z8,z4,z184,z6]),(0,[z826,z1,z8,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z827]),(0,[z474,z8,z4,z424,z5,z6]),(0,[z1,z56,z8,z4,z709,z6]),(0,[z284,z2,z8,z4,z828,z6])],[(0,[z1,z8,z341,z25,z5,z6]),(0,[z2,z8,z4,z274,z18,z6]),(0,[z2,z8,z4,z18,z6,z233]),(0,[z1,z2,z8,z4,z829,z6])]],
   [[(1,[z1,z8,z25,z147,z6])],[(0,[z1,z148,z8,z25,z5,z6]),(0,[z1,z2,z8,z4,z830,z6]),(0,[z2,z40,z8,z4,z141,z6]),(0,[z831,z2,z8,z4,z5,z6])],[(0,[z1,z2,z832,z4,z5,z6]),(0,[z724,z1,z8,z4,z5,z6]),(0,[z85,z2,z8,z4,z5,z153]),(0,[z1,z833,z8,z4,z46,z6]),(0,[z1,z2,z8,z834,z5,z6]),(0,[z1,z34,z25,z73,z5,z6]),(0,[z1,z2,z8,z4,z835,z6]),(0,[z501,z1,z8,z301,z5,z6]),(0,[z1,z2,z160,z4,z5,z836]),(0,[z126,z2,z8,z4,z461,z6])],[(0,[z0,z2,z8,z4,z18,z6]),(0,[z1,z8,z4,z837,z5,z6]),(0,[z838,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z132,z231,z6])],[(0,[z1,z2,z8,z122,z46,z6]),(0,[z1,z8,z4,z130,z5,z6]),(0,[z466,z1,z8,z272,z5,z6]),(0,[z1,z839,z8,z4,z25,z5]),(0,[z284,z8,z4,z25,z5,z6])],[(0,[z58,z269,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z840,z6]),(0,[z1,z350,z8,z25,z5,z6]),(0,[z2,z8,z4,z5,z141,z6]),(0,[z2,z8,z62,z235,z18,z6]),(0,[z31,z1,z8,z4,z18,z6]),(0,[z1,z2,z8,z841,z5,z6]),(0,[z1,z8,z842,z4,z5,z6]),(0,[z1,z2,z8,z843,z5,z6]),(0,[z1,z2,z844,z34,z5,z6])],[(0,[z83,z2,z8,z235,z18,z6]),(0,[z31,z8,z4,z235,z18,z6]),(0,[z1,z2,z160,z4,z18,z14]),(0,[z845,z1,z8,z4,z25,z6]),(0,[z1,z8,z4,z25,z799,z6]),(0,[z1,z2,z160,z4,z119,z14]),(0,[z1,z2,z8,z119,z516,z6])],[(0,[z1,z2,z8,z4,z846,z6]),(0,[z120,z2,z8,z4,z46,z6]),(0,[z1,z847,z8,z4,z5,z6])]],
   [[(0,[z185,z2,z8,z4,z18,z6]),(0,[z447,z2,z8,z4,z46,z6]),(0,[z162,z1,z656,z4,z5,z6]),(0,[z1,z8,z193,z25,z5,z6]),(0,[z1,z2,z8,z4,z848,z6])],[(0,[z16,z8,z4,z25,z46,z6]),(0,[z1,z2,z8,z4,z849,z6])],[(0,[z1,z2,z8,z4,z850,z6]),(0,[z1,z8,z25,z370,z5,z6]),(0,[z1,z56,z8,z319,z19,z6])],[(0,[z1,z8,z25,z235,z18,z6]),(0,[z31,z1,z8,z231,z5,z6]),(0,[z1,z2,z8,z4,z36,z6])],[(0,[z1,z851,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z852,z6]),(0,[z1,z2,z8,z4,z853,z6]),(0,[z1,z166,z8,z4,z5,z6])],[(0,[z501,z1,z8,z25,z5,z6]),(0,[z854,z2,z8,z4,z5,z6]),(0,[z51,z120,z2,z8,z6,z20])],[(0,[z1,z8,z4,z855,z5,z6]),(0,[z1,z2,z8,z856,z5,z6]),(0,[z1,z2,z8,z4,z98,z6]),(1,[z8,z25,z235,z18,z6]),(0,[z1,z8,z25,z5,z6,z388]),(0,[z1,z2,z8,z4,z709,z6]),(0,[z857,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z360,z6])],[(0,[z58,z269,z8,z4,z46,z6]),(0,[z2,z858,z76,z4,z5,z6]),(0,[z1,z859,z8,z4,z5,z6]),(0,[z860,z1,z8,z4,z5,z6]),(0,[z1,z8,z861,z5,z6,z86]),(0,[z1,z24,z4,z554,z5,z6]),(0,[z1,z8,z4,z132,z257,z6]),(0,[z1,z2,z8,z4,z862,z6]),(0,[z1,z8,z4,z5,z6,z863])]],
   [[(0,[z724,z269,z8,z4,z5,z6]),(0,[z1,z8,z132,z25,z235,z6]),(0,[z1,z2,z160,z4,z46,z14]),(0,[z1,z2,z8,z4,z864,z6]),(0,[z865,z2,z8,z4,z5,z6])],[(0,[z1,z866,z8,z4,z5,z6]),(0,[z2,z324,z8,z4,z18,z6]),(0,[z867,z1,z8,z4,z18,z6]),(0,[z1,z8,z25,z5,z6,z394])],[(0,[z1,z2,z8,z341,z18,z6]),(0,[z2,z326,z8,z4,z18,z6]),(0,[z1,z8,z25,z221,z5,z6]),(0,[z1,z868,z4,z25,z5,z6]),(0,[z1,z2,z8,z4,z779,z6])],[(0,[z1,z2,z8,z4,z869,z6]),(0,[z2,z329,z8,z4,z18,z6]),(0,[z317,z1,z8,z4,z18,z6]),(0,[z2,z472,z8,z4,z46,z6]),(0,[z1,z8,z25,z5,z6,z228]),(0,[z1,z8,z25,z400,z5,z6]),(0,[z101,z2,z8,z4,z141,z6]),(0,[z870,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z871,z5,z6])],[(0,[z1,z92,z8,z4,z46,z6]),(0,[z1,z390,z8,z25,z5,z6]),(0,[z31,z1,z34,z73,z5,z6]),(0,[z1,z2,z8,z4,z5,z711])],[(0,[z1,z2,z8,z872,z5,z6]),(0,[z873,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z67,z547]),(0,[z1,z874,z8,z4,z5,z6])],[(0,[z1,z2,z875,z4,z5,z6]),(0,[z1,z8,z25,z46,z6,z54]),(0,[z31,z1,z8,z336,z5,z6])],[(0,[z1,z2,z8,z4,z876,z6]),(0,[z1,z471,z8,z25,z5,z6]),(0,[z1,z2,z8,z4,z877,z6]),(0,[z83,z2,z8,z817,z5,z6]),(0,[z1,z8,z63,z25,z18,z6]),(0,[z1,z2,z4,z18,z878,z6])]],
   [[(0,[z0,z2,z574,z4,z5,z6]),(0,[z30,z2,z8,z4,z879,z6]),(0,[z707,z1,z8,z4,z18,z6]),(0,[z363,z2,z8,z4,z46,z6]),(0,[z247,z1,z8,z834,z5,z6]),(0,[z1,z880,z8,z4,z5,z6]),(0,[z51,z120,z8,z25,z5,z6]),(0,[z2,z881,z8,z4,z5,z6])],[(0,[z882,z1,z8,z4,z5,z6]),(0,[z1,z8,z25,z5,z6,z242]),(0,[z511,z2,z8,z4,z18,z6]),(0,[z1,z8,z883,z4,z25,z6]),(0,[z1,z2,z884,z8,z4,z18]),(0,[z744,z1,z8,z4,z25,z6]),(0,[z1,z2,z8,z4,z885,z6]),(0,[z106,z1,z8,z25,z6,z54]),(0,[z1,z127,z8,z25,z5,z6]),(0,[z1,z56,z8,z4,z257,z6])],[(0,[z1,z2,z8,z886,z5,z6]),(0,[z1,z8,z25,z5,z265,z6]),(0,[z31,z1,z8,z4,z788,z6]),(0,[z1,z2,z8,z62,z167,z6]),(0,[z1,z8,z4,z5,z6,z887]),(0,[z328,z8,z4,z5,z6,z233])],[(0,[z1,z2,z8,z4,z888,z6]),(0,[z31,z1,z8,z25,z18,z6]),(0,[z2,z8,z4,z18,z6,z96]),(0,[z1,z8,z842,z25,z5,z6]),(0,[z252,z1,z446,z4,z5,z6]),(0,[z1,z117,z245,z8,z5,z6])],[(0,[z44,z2,z8,z235,z18,z6])],[(0,[z2,z8,z817,z235,z5,z6]),(0,[z1,z2,z716,z8,z18,z6]),(0,[z1,z66,z8,z193,z5,z6]),(0,[z51,z31,z1,z8,z6,z20])],[(0,[z1,z2,z889,z4,z5,z6]),(0,[z185,z8,z4,z25,z18,z6]),(0,[z85,z247,z8,z4,z5,z86]),(0,[z284,z2,z160,z4,z5,z14])],[(0,[z1,z890,z8,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z233]),(0,[z31,z83,z8,z235,z5,z6]),(0,[z1,z2,z891,z8,z5,z6]),(0,[z1,z2,z8,z892,z5,z6]),(0,[z1,z2,z8,z231,z5,z6]),(0,[z2,z893,z8,z4,z5,z6]),(0,[z1,z8,z13,z735,z5,z6])]],
   [[(0,[z31,z1,z8,z4,z146,z6]),(0,[z58,z269,z8,z4,z146,z6]),(0,[z1,z251,z8,z25,z5,z6]),(0,[z316,z1,z2,z4,z6,z69]),(0,[z1,z2,z8,z894,z5,z6])],[(0,[z1,z8,z431,z25,z5,z6]),(0,[z1,z8,z25,z265,z18,z6]),(0,[z252,z1,z8,z193,z5,z6]),(0,[z1,z2,z895,z4,z5,z6]),(0,[z1,z8,z4,z896,z5,z6]),(0,[z1,z2,z8,z4,z897,z6])],[(0,[z724,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z898,z6]),(0,[z106,z1,z8,z4,z124,z6]),(0,[z1,z2,z8,z4,z899,z6]),(0,[z1,z2,z8,z13,z36,z6]),(0,[z1,z2,z60,z8,z5,z54])],[(0,[z1,z166,z8,z4,z46,z6]),(0,[z900,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z901,z6]),(0,[z1,z8,z4,z25,z98,z6]),(0,[z1,z2,z8,z301,z18,z6]),(0,[z31,z120,z8,z4,z5,z6])],[(0,[z16,z2,z8,z4,z184,z6]),(0,[z0,z76,z4,z25,z5,z6]),(0,[z1,z2,z8,z883,z4,z6]),(0,[z1,z8,z4,z18,z6,z902]),(0,[z31,z1,z8,z25,z46,z6]),(0,[z64,z1,z8,z4,z187,z6]),(0,[z1,z2,z8,z712,z46,z6]),(0,[z1,z2,z8,z4,z903,z6])],[(0,[z85,z2,z8,z4,z18,z86]),(0,[z1,z2,z8,z4,z904,z6]),(0,[z1,z8,z25,z5,z283,z6]),(0,[z1,z2,z8,z4,z5,z905]),(0,[z1,z2,z8,z4,z906,z6]),(0,[z1,z907,z8,z4,z5,z6]),(0,[z1,z908,z8,z4,z5,z6]),(0,[z1,z2,z8,z909,z5,z6])],[(0,[z910,z1,z8,z63,z5,z6]),(0,[z85,z8,z4,z5,z155,z86]),(0,[z31,z1,z8,z193,z5,z6]),(0,[z31,z1,z8,z4,z815,z6]),(0,[z1,z2,z8,z4,z911,z6]),(0,[z51,z126,z2,z8,z6,z20])]],
   [[(0,[z1,z2,z34,z73,z5,z6]),(0,[z1,z912,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z913]),(0,[z2,z8,z374,z4,z18,z6]),(0,[z2,z378,z8,z4,z18,z6]),(0,[z1,z34,z8,z25,z46,z6])],[(0,[z1,z8,z25,z292,z5,z6]),(0,[z1,z914,z4,z25,z5,z6]),(0,[z1,z345,z8,z25,z5,z54]),(0,[z1,z8,z296,z25,z5,z6]),(0,[z31,z1,z8,z4,z821,z6]),(0,[z915,z2,z8,z4,z5,z6])],[(0,[z297,z1,z8,z25,z5,z6]),(0,[z1,z8,z460,z25,z5,z6]),(0,[z51,z1,z311,z8,z6,z20])],[(0,[z185,z2,z8,z235,z18,z6]),(0,[z1,z2,z8,z4,z916,z6]),(0,[z315,z1,z8,z4,z18,z6]),(0,[z1,z8,z4,z917,z5,z6]),(0,[z2,z8,z209,z4,z141,z6]),(0,[z1,z2,z8,z4,z918,z6])],[(0,[z1,z2,z8,z341,z146,z6]),(0,[z1,z2,z8,z18,z919,z6]),(0,[z2,z8,z4,z541,z46,z6]),(0,[z1,z8,z4,z25,z877,z6]),(0,[z1,z2,z8,z4,z920,z6])],[(0,[z921,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z922,z6]),(0,[z2,z390,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z170,z6]),(0,[z1,z2,z8,z4,z225,z6])],[(0,[z1,z923,z8,z4,z5,z6]),(0,[z126,z2,z8,z4,z18,z6]),(0,[z247,z1,z8,z4,z18,z6]),(0,[z1,z8,z4,z18,z6,z155]),(0,[z307,z2,z8,z4,z18,z6]),(0,[z380,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z924,z5,z6]),(0,[z1,z8,z293,z25,z5,z6]),(0,[z152,z1,z8,z25,z5,z6]),(0,[z1,z8,z4,z5,z6,z718])]],
   [[(0,[z1,z2,z8,z4,z879,z6]),(0,[z1,z2,z8,z13,z18,z6]),(0,[z1,z2,z765,z4,z18,z6]),(0,[z85,z2,z8,z4,z46,z86]),(0,[z152,z1,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z925,z6])],[],[(0,[z1,z2,z8,z926,z5,z6]),(0,[z1,z2,z8,z4,z927,z6]),(0,[z51,z126,z8,z25,z5,z6]),(0,[z1,z8,z132,z231,z25,z6]),(0,[z31,z1,z8,z230,z5,z6])],[(0,[z1,z243,z8,z25,z18,z6]),(0,[z928,z1,z8,z4,z5,z6])],[(0,[z0,z2,z76,z4,z46,z6]),(0,[z1,z929,z8,z4,z5,z6]),(0,[z1,z889,z4,z25,z5,z6]),(0,[z1,z2,z8,z4,z67,z622])],[(0,[z1,z930,z8,z4,z5,z6]),(0,[z466,z1,z8,z4,z5,z6]),(0,[z1,z8,z479,z25,z5,z6]),(0,[z1,z2,z8,z4,z931,z6])],[(0,[z229,z1,z8,z4,z46,z6]),(0,[z1,z753,z8,z4,z46,z6]),(0,[z1,z8,z25,z5,z6,z493]),(0,[z1,z8,z231,z19,z5,z6]),(0,[z114,z1,z8,z4,z5,z718])],[(0,[z1,z2,z8,z4,z932,z6]),(0,[z1,z2,z8,z4,z933,z6]),(0,[z2,z8,z4,z5,z934,z6]),(0,[z1,z935,z8,z4,z25,z5]),(0,[z1,z118,z8,z25,z5,z6]),(0,[z1,z353,z8,z25,z5,z6]),(0,[z2,z117,z8,z4,z743,z6]),(0,[z2,z8,z4,z141,z6,z82])]],
   [[(0,[z1,z2,z8,z936,z5,z6]),(0,[z0,z2,z8,z4,z937,z6]),(0,[z51,z1,z8,z25,z67,z6])],[(0,[z316,z2,z3,z4,z18,z6]),(0,[z51,z1,z8,z917,z5,z6]),(0,[z589,z330,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z938,z6]),(0,[z1,z8,z319,z25,z5,z6]),(0,[z31,z1,z8,z4,z36,z6]),(0,[z1,z939,z8,z4,z5,z6]),(0,[z940,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z941,z6]),(0,[z1,z942,z8,z4,z5,z6]),(0,[z2,z8,z4,z943,z5,z6]),(0,[z944,z1,z8,z4,z5,z6])],[(0,[z945,z1,z8,z4,z5,z6]),(0,[z1,z2,z160,z4,z36,z14])],[(0,[z1,z329,z8,z25,z5,z6]),(0,[z106,z1,z8,z63,z25,z6]),(0,[z1,z311,z8,z4,z5,z6])],[(0,[z1,z2,z8,z122,z18,z6]),(0,[z31,z1,z8,z4,z98,z6]),(0,[z416,z2,z8,z4,z18,z6]),(0,[z1,z243,z8,z25,z46,z6]),(0,[z1,z498,z8,z25,z5,z6]),(0,[z1,z2,z946,z8,z4,z6]),(0,[z31,z1,z8,z4,z360,z6]),(0,[z1,z2,z8,z4,z5,z947])],[(0,[z110,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z948,z6]),(0,[z1,z2,z8,z949,z5,z6]),(0,[z31,z126,z8,z4,z5,z6]),(0,[z284,z2,z8,z4,z119,z6])],[(0,[z1,z2,z8,z950,z5,z6]),(0,[z1,z2,z777,z4,z46,z6]),(0,[z1,z2,z8,z4,z951,z6]),(0,[z1,z2,z8,z319,z5,z6]),(0,[z1,z2,z8,z842,z5,z6]),(0,[z126,z2,z8,z62,z5,z6]),(0,[z1,z2,z8,z952,z5,z6]),(0,[z1,z2,z34,z526,z5,z6]),(0,[z1,z8,z4,z953,z5,z6])]],
   [[(0,[z185,z2,z8,z4,z98,z6]),(0,[z30,z31,z8,z4,z18,z6]),(0,[z489,z1,z8,z4,z5,z6]),(0,[z1,z954,z2,z8,z4,z6]),(0,[z955,z1,z8,z4,z5,z6]),(0,[z101,z1,z2,z4,z6,z793])],[(0,[z328,z1,z8,z4,z5,z6]),(0,[z1,z8,z25,z5,z6,z521]),(0,[z1,z8,z25,z5,z524,z6]),(0,[z1,z8,z25,z525,z5,z6]),(0,[z1,z8,z25,z5,z6,z179]),(0,[z208,z1,z8,z4,z124,z6]),(0,[z956,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z957,z6])],[(0,[z2,z3,z8,z4,z138,z6]),(0,[z1,z92,z8,z4,z98,z6]),(0,[z1,z8,z4,z789,z130,z6]),(0,[z1,z300,z8,z4,z5,z6]),(0,[z1,z8,z4,z257,z5,z6])],[(0,[z1,z2,z8,z4,z958,z6]),(0,[z1,z8,z762,z4,z5,z6]),(0,[z208,z126,z2,z8,z4,z6]),(0,[z2,z8,z13,z5,z6,z233])],[(0,[z2,z8,z4,z879,z18,z6]),(0,[z1,z8,z4,z25,z170,z6]),(0,[z959,z1,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z225,z6]),(0,[z31,z1,z8,z132,z25,z6])],[(0,[z1,z8,z4,z5,z6,z902]),(0,[z114,z1,z8,z4,z46,z27]),(0,[z1,z2,z8,z4,z960,z6]),(0,[z534,z1,z8,z25,z5,z6])],[(0,[z2,z8,z4,z461,z18,z6]),(0,[z1,z961,z8,z4,z5,z6]),(0,[z962,z2,z8,z4,z5,z6])],[(0,[z211,z1,z8,z25,z5,z6]),(0,[z1,z8,z4,z132,z19,z6])]],
   [[(0,[z1,z8,z4,z25,z136,z6]),(0,[z8,z4,z25,z235,z18,z6]),(0,[z284,z2,z8,z4,z46,z6]),(0,[z1,z963,z8,z4,z25,z5]),(0,[z1,z34,z8,z132,z25,z6]),(0,[z1,z126,z8,z25,z5,z6]),(0,[z1,z2,z964,z8,z4,z6]),(0,[z284,z2,z8,z13,z5,z6]),(0,[z328,z1,z8,z5,z516,z6]),(0,[z965,z1,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z966,z6]),(0,[z1,z117,z435,z25,z5,z6])],[(0,[z1,z967,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z968,z6]),(0,[z1,z117,z8,z25,z5,z6]),(0,[z969,z1,z8,z4,z25,z6]),(0,[z1,z8,z25,z5,z6,z547]),(0,[z970,z2,z8,z4,z5,z6])],[(0,[z8,z25,z235,z5,z18,z6]),(0,[z1,z8,z25,z79,z18,z6]),(0,[z606,z2,z8,z4,z18,z6]),(0,[z1,z538,z8,z25,z5,z6]),(0,[z1,z198,z8,z25,z5,z6]),(1,[z126,z8,z25,z5,z6]),(0,[z1,z971,z8,z4,z5,z6])],[(0,[z532,z2,z8,z4,z18,z6]),(0,[z972,z8,z4,z25,z5,z6]),(0,[z1,z8,z25,z167,z6,z54])],[(0,[z1,z92,z8,z4,z18,z6]),(0,[z47,z2,z8,z4,z18,z200]),(0,[z1,z2,z8,z5,z919,z6]),(0,[z1,z2,z8,z296,z46,z6]),(0,[z969,z1,z2,z8,z4,z6]),(0,[z284,z328,z8,z4,z5,z6]),(0,[z1,z2,z8,z5,z6,z711])],[(0,[z1,z2,z8,z4,z937,z6]),(0,[z1,z2,z8,z4,z186,z6]),(0,[z1,z2,z8,z817,z5,z6]),(0,[z1,z2,z8,z4,z376,z6]),(0,[z1,z2,z8,z4,z973,z6]),(0,[z51,z1,z2,z8,z6,z781])],[(0,[z1,z8,z4,z5,z6,z155]),(0,[z1,z2,z8,z4,z974,z6]),(0,[z1,z8,z4,z975,z5,z6]),(0,[z1,z2,z8,z4,z898,z6]),(0,[z106,z1,z56,z8,z4,z6]),(0,[z51,z1,z8,z257,z5,z6])]],
   [[(0,[z536,z2,z8,z4,z18,z6]),(0,[z44,z1,z2,z8,z6,z20]),(0,[z1,z2,z8,z4,z976,z6]),(0,[z1,z977,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z978,z6]),(0,[z1,z2,z8,z4,z979,z6])],[(0,[z1,z2,z8,z4,z980,z6]),(0,[z483,z2,z8,z4,z18,z6]),(0,[z31,z1,z60,z8,z5,z54]),(0,[z1,z56,z8,z4,z19,z6]),(0,[z981,z1,z8,z4,z5,z6])],[(0,[z1,z8,z4,z5,z6,z982]),(0,[z106,z1,z8,z25,z235,z6]),(0,[z1,z2,z8,z4,z18,z983]),(0,[z1,z2,z8,z193,z46,z6]),(0,[z1,z2,z8,z4,z5,z794]),(0,[z1,z311,z8,z25,z5,z6]),(0,[z1,z2,z181,z4,z6,z69]),(0,[z126,z311,z8,z4,z5,z6]),(0,[z1,z984,z8,z4,z5,z6])],[(0,[z1,z558,z8,z25,z5,z6]),(0,[z1,z345,z8,z4,z5,z27]),(0,[z1,z2,z8,z4,z828,z6])],[(0,[z8,z361,z25,z235,z5,z6]),(0,[z1,z8,z4,z130,z18,z6]),(0,[z1,z245,z8,z4,z5,z6]),(0,[z1,z142,z8,z4,z5,z6])],[(0,[z985,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z272,z5,z6]),(0,[z1,z2,z8,z986,z5,z6]),(0,[z1,z720,z34,z8,z5,z6])],[(0,[z2,z3,z8,z4,z18,z6]),(0,[z987,z1,z2,z8,z193,z6]),(0,[z1,z367,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z6,z781]),(0,[z1,z988,z8,z4,z5,z6]),(0,[z1,z2,z60,z8,z167,z54])],[(0,[z1,z2,z8,z4,z989,z6]),(0,[z1,z2,z8,z4,z990,z6]),(0,[z106,z1,z117,z8,z25,z6]),(0,[z51,z1,z2,z8,z6,z165]),(0,[z1,z2,z8,z4,z991,z6])]],
   [[(0,[z1,z2,z8,z122,z146,z6]),(0,[z8,z63,z25,z235,z5,z6]),(0,[z2,z8,z235,z265,z18,z6]),(0,[z8,z4,z25,z46,z18,z6]),(0,[z515,z2,z8,z4,z18,z6]),(0,[z85,z31,z8,z4,z5,z86]),(0,[z114,z1,z8,z296,z5,z27]),(0,[z328,z1,z8,z13,z5,z6])],[(0,[z1,z8,z4,z25,z5,z6]),(0,[z1,z2,z8,z4,z992,z6]),(0,[z1,z2,z8,z4,z993,z6]),(0,[z1,z117,z34,z25,z5,z6]),(0,[z8,z4,z25,z994,z5,z6]),(0,[z1,z395,z8,z25,z5,z6]),(0,[z995,z2,z8,z4,z5,z6]),(0,[z1,z996,z8,z4,z5,z6])],[(0,[z1,z8,z4,z997,z5,z6]),(0,[z1,z570,z8,z25,z5,z6]),(0,[z1,z2,z8,z4,z998,z6]),(0,[z1,z2,z8,z999,z5,z6]),(0,[z1,z1000,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1001,z6])],[(0,[z0,z2,z8,z4,z170,z6]),(0,[z693,z2,z8,z4,z46,z6]),(0,[z1,z8,z25,z5,z516,z6]),(0,[z51,z1,z2,z8,z6,z20]),(0,[z1,z2,z1002,z4,z5,z6])],[(0,[z474,z269,z8,z4,z5,z6]),(0,[z0,z31,z76,z4,z5,z6]),(0,[z1,z1003,z8,z4,z5,z6]),(0,[z1,z166,z8,z4,z18,z6]),(0,[z1,z243,z8,z132,z25,z6]),(0,[z1,z4,z25,z5,z1004,z6]),(0,[z210,z1,z8,z4,z178,z6]),(0,[z31,z1,z8,z453,z5,z6]),(0,[z1,z8,z4,z1005,z5,z6]),(0,[z1,z2,z8,z4,z1006,z6])],[(0,[z31,z1,z8,z4,z170,z6]),(0,[z85,z2,z8,z4,z5,z794]),(0,[z31,z1,z8,z4,z225,z6]),(0,[z1,z2,z8,z5,z1007,z6]),(0,[z1,z2,z8,z4,z1008,z6]),(0,[z106,z31,z1,z8,z4,z6]),(0,[z1,z2,z4,z5,z6,z836]),(0,[z1,z8,z5,z516,z6,z551])],[(0,[z1,z2,z8,z4,z1009,z6]),(0,[z1,z92,z8,z63,z5,z6]),(0,[z1,z8,z25,z5,z6,z422]),(0,[z1,z8,z4,z130,z46,z6]),(0,[z2,z8,z4,z5,z879,z6]),(0,[z1,z2,z4,z46,z6,z827]),(0,[z162,z1,z192,z4,z5,z6]),(0,[z1,z2,z8,z1010,z5,z6])],[(0,[z1,z2,z8,z4,z1011,z6]),(0,[z1,z2,z8,z4,z1012,z6]),(0,[z1,z8,z25,z595,z5,z6]),(0,[z1,z2,z8,z4,z1013,z6])]],
   [[(0,[z58,z330,z8,z4,z5,z6]),(0,[z396,z2,z8,z4,z18,z6]),(0,[z474,z8,z25,z235,z5,z6]),(0,[z1,z1014,z8,z4,z5,z6]),(0,[z1,z118,z8,z25,z5,z54]),(0,[z1,z2,z8,z4,z1015,z6]),(0,[z1,z1016,z8,z4,z5,z6]),(0,[z1,z160,z4,z5,z551,z14])],[(0,[z31,z1,z8,z4,z136,z6]),(0,[z290,z8,z4,z25,z5,z6]),(0,[z1017,z2,z8,z4,z5,z6]),(0,[z1018,z2,z8,z4,z5,z6]),(0,[z396,z2,z8,z4,z141,z6])],[(0,[z1,z34,z8,z25,z18,z6])],[(0,[z1,z2,z8,z4,z1019,z6]),(0,[z1020,z1,z8,z4,z5,z6]),(0,[z2,z529,z8,z4,z18,z6]),(0,[z316,z1,z2,z4,z6,z305]),(0,[z1,z2,z4,z5,z6,z1021]),(0,[z120,z311,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1022,z6]),(0,[z31,z1,z8,z535,z5,z6]),(0,[z1,z2,z8,z813,z5,z6]),(0,[z1,z2,z8,z4,z1023,z6]),(0,[z1,z8,z4,z25,z186,z6]),(0,[z2,z8,z4,z46,z18,z6]),(0,[z1,z8,z4,z18,z6,z551]),(0,[z1,z2,z8,z4,z1024,z6]),(0,[z1,z2,z8,z4,z1025,z6]),(0,[z1,z8,z4,z1026,z5,z6]),(0,[z1,z8,z4,z861,z5,z6]),(0,[z1027,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z25,z376,z6]),(0,[z1028,z8,z4,z25,z5,z6]),(0,[z1,z2,z345,z8,z5,z54]),(0,[z1,z2,z8,z4,z978,z6]),(0,[z1,z56,z8,z4,z299,z6])],[(0,[z1,z596,z8,z25,z5,z6]),(0,[z31,z185,z8,z4,z18,z6]),(0,[z2,z8,z4,z46,z141,z6]),(0,[z2,z8,z4,z994,z5,z6]),(0,[z1,z8,z917,z25,z5,z6]),(0,[z1,z2,z60,z8,z5,z134]),(0,[z1,z2,z8,z4,z1029,z6]),(0,[z1,z2,z8,z4,z1030,z6])],[(0,[z0,z2,z76,z4,z184,z6]),(0,[z1,z2,z8,z4,z1031,z6]),(0,[z1032,z1,z8,z4,z5,z6]),(0,[z1,z35,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1033,z6]),(0,[z1,z977,z8,z25,z5,z6]),(0,[z1,z2,z8,z1034,z5,z6])],[(0,[z38,z1,z8,z122,z5,z6]),(0,[z1,z2,z8,z62,z147,z6])]],
   [[(0,[z1,z2,z8,z4,z5,z1035]),(0,[z1,z2,z8,z4,z1036,z6]),(0,[z1,z2,z8,z4,z67,z347]),(0,[z1,z8,z25,z299,z5,z6]),(0,[z1,z2,z4,z5,z1004,z6]),(0,[z1,z2,z8,z4,z1037,z6])],[(0,[z152,z1,z8,z4,z18,z6]),(0,[z1,z273,z8,z25,z5,z6]),(0,[z1038,z2,z8,z4,z5,z6])],[(0,[z1,z8,z4,z25,z224,z6]),(0,[z1,z8,z25,z461,z5,z6]),(0,[z1,z8,z4,z25,z1039,z6]),(0,[z208,z1,z8,z4,z178,z6]),(0,[z1,z2,z8,z209,z231,z6])],[(0,[z2,z45,z8,z4,z18,z6]),(0,[z101,z1,z2,z4,z6,z105]),(0,[z1,z2,z8,z4,z1040,z6]),(0,[z1,z8,z25,z5,z464,z6]),(0,[z1041,z1,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1042,z6]),(0,[z1,z2,z8,z4,z1043,z6]),(0,[z1,z2,z8,z1044,z5,z6]),(0,[z1,z1045,z8,z4,z5,z6]),(0,[z126,z367,z8,z4,z5,z6])],[(0,[z1,z8,z4,z25,z338,z6]),(0,[z0,z2,z76,z4,z18,z6]),(0,[z1,z2,z8,z18,z516,z6]),(0,[z1,z455,z8,z25,z5,z6])],[(0,[z37,z1,z8,z301,z5,z6]),(0,[z2,z8,z4,z18,z6,z169]),(0,[z1,z1046,z8,z4,z5,z6]),(0,[z126,z2,z8,z4,z67,z6])],[(0,[z3,z8,z4,z25,z18,z6]),(0,[z229,z1,z8,z4,z18,z6]),(0,[z1,z754,z8,z4,z18,z6]),(0,[z1,z2,z891,z8,z18,z6]),(0,[z1,z2,z8,z231,z18,z6]),(0,[z537,z2,z8,z4,z46,z6]),(0,[z126,z8,z4,z25,z5,z6]),(0,[z1,z946,z8,z4,z25,z6])]],
   [[(0,[z1,z2,z8,z4,z1047,z6]),(0,[z2,z8,z4,z46,z670,z6]),(0,[z1,z2,z875,z4,z46,z6]),(0,[z1,z2,z8,z4,z1048,z6]),(0,[z106,z1,z367,z8,z4,z6]),(0,[z284,z31,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z397,z6])],[(0,[z1,z2,z8,z4,z1049,z6]),(0,[z1050,z2,z8,z4,z5,z6]),(0,[z328,z1,z160,z4,z5,z14])],[(0,[z31,z1,z8,z4,z5,z6]),(0,[z1,z8,z4,z5,z6,z1051]),(0,[z1052,z2,z8,z4,z5,z6]),(0,[z1,z1053,z8,z4,z5,z6])],[(0,[z2,z8,z4,z937,z18,z6]),(0,[z83,z2,z8,z235,z5,z6]),(0,[z2,z8,z4,z496,z18,z6]),(0,[z1,z2,z8,z4,z1054,z6]),(0,[z114,z1,z8,z4,z5,z655]),(0,[z1,z8,z132,z25,z79,z6]),(0,[z1,z2,z8,z4,z1055,z6]),(0,[z284,z2,z8,z4,z36,z6]),(0,[z51,z1,z367,z8,z6,z20]),(0,[z1,z245,z8,z5,z6,z54])],[(0,[z1,z749,z8,z4,z25,z5]),(0,[z31,z8,z4,z5,z141,z6]),(0,[z1,z2,z8,z4,z1056,z6])],[(0,[z1,z2,z8,z4,z136,z6]),(0,[z1057,z2,z8,z4,z5,z6]),(0,[z1,z720,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z414,z6]),(0,[z1,z2,z8,z4,z1058,z6]),(0,[z1,z1059,z8,z4,z5,z6]),(0,[z1,z2,z8,z5,z711,z54])],[(0,[z1,z2,z8,z1060,z5,z6]),(0,[z1,z1061,z8,z4,z5,z6]),(1,[z2,z8,z4,z879,z6]),(0,[z396,z1,z2,z4,z6,z105]),(0,[z1,z2,z816,z8,z4,z67])],[(0,[z1,z8,z4,z25,z241,z6]),(0,[z1062,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z1063,z5,z6]),(0,[z1,z2,z8,z4,z167,z6])]],
   [[(0,[z1,z2,z34,z73,z18,z6]),(0,[z2,z703,z8,z4,z18,z6]),(0,[z188,z2,z8,z4,z46,z6]),(0,[z1,z8,z4,z5,z6,z1064]),(0,[z106,z1,z34,z8,z25,z6]),(0,[z1,z330,z8,z25,z5,z6]),(0,[z1065,z1,z8,z4,z5,z6])],[(0,[z2,z8,z4,z184,z18,z6]),(0,[z2,z8,z4,z577,z18,z6]),(0,[z1,z2,z8,z231,z46,z6]),(0,[z972,z2,z8,z4,z5,z6]),(0,[z31,z1,z8,z5,z516,z6]),(0,[z126,z2,z8,z4,z6,z20])],[(0,[z1,z2,z8,z4,z1066,z6]),(0,[z99,z1,z8,z25,z5,z6]),(0,[z1,z8,z4,z18,z6,z759]),(0,[z1,z2,z4,z5,z878,z6])],[(0,[z1,z2,z1067,z4,z5,z6]),(0,[z1,z2,z8,z1068,z5,z6]),(0,[z1,z2,z8,z4,z359,z6]),(0,[z1,z202,z8,z4,z199,z6]),(0,[z1,z641,z8,z25,z5,z6])],[(0,[z1,z8,z485,z25,z5,z6]),(0,[z1,z2,z8,z4,z1069,z6]),(0,[z185,z2,z8,z4,z968,z6]),(0,[z514,z1,z8,z4,z124,z6]),(0,[z1,z56,z8,z4,z473,z6]),(0,[z1,z2,z60,z8,z46,z54]),(0,[z1,z117,z8,z25,z414,z6]),(0,[z31,z1,z8,z4,z1070,z6]),(0,[z1,z2,z8,z4,z5,z718]),(0,[z101,z1,z2,z4,z6,z42]),(0,[z1,z2,z8,z4,z1071,z6])],[(0,[z1,z2,z914,z4,z5,z6]),(0,[z1,z2,z8,z4,z1072,z6]),(0,[z31,z1,z8,z4,z186,z6]),(0,[z2,z8,z4,z5,z6,z1073]),(0,[z210,z106,z1,z8,z25,z6]),(0,[z31,z1,z8,z593,z5,z6]),(0,[z31,z1,z8,z4,z376,z6]),(0,[z1,z2,z8,z1074,z5,z6]),(0,[z1075,z1,z8,z4,z5,z6]),(0,[z120,z367,z8,z4,z5,z6])],[(0,[z1,z8,z4,z25,z369,z6]),(0,[z114,z1,z8,z4,z18,z27]),(0,[z85,z2,z8,z4,z170,z86]),(0,[z1076,z2,z8,z4,z5,z6]),(0,[z1,z8,z209,z25,z79,z6]),(0,[z256,z1,z8,z4,z299,z6]),(0,[z1077,z1,z8,z4,z5,z6]),(0,[z1,z2,z160,z4,z376,z14]),(0,[z1,z2,z816,z8,z4,z82])],[(0,[z1,z8,z1078,z4,z5,z6]),(0,[z1,z8,z4,z790,z18,z6]),(0,[z2,z8,z4,z46,z6,z233]),(0,[z1,z8,z1079,z4,z5,z6]),(0,[z1,z8,z25,z5,z6,z508]),(0,[z1,z2,z1080,z4,z5,z6])]],
   [[(0,[z1081,z1,z8,z4,z5,z6]),(0,[z1,z2,z1082,z4,z5,z6]),(0,[z317,z1,z8,z4,z5,z6]),(0,[z120,z8,z4,z25,z5,z6]),(0,[z1,z954,z8,z4,z25,z6]),(0,[z1,z2,z868,z4,z5,z6]),(0,[z1,z1083,z8,z4,z5,z6]),(0,[z126,z2,z8,z4,z6,z69]),(0,[z1084,z1,z8,z4,z5,z6])],[(0,[z1,z8,z4,z5,z6,z1085]),(0,[z284,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z1086,z6]),(0,[z1,z8,z4,z25,z1040,z6])],[(0,[z1,z2,z884,z8,z4,z5]),(0,[z1,z2,z34,z73,z46,z6]),(0,[z1,z1087,z8,z4,z5,z6])],[(0,[z1,z2,z8,z1088,z5,z6]),(0,[z31,z1,z8,z4,z224,z6]),(0,[z910,z1,z8,z4,z5,z6]),(0,[z798,z1,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z1089,z6]),(0,[z1,z117,z300,z8,z5,z6]),(0,[z2,z8,z4,z1090,z6,z233])],[(0,[z1,z2,z8,z4,z5,z1091]),(0,[z1,z8,z63,z25,z5,z6]),(0,[z83,z8,z25,z235,z5,z6]),(0,[z1,z8,z4,z1092,z5,z6]),(0,[z1,z8,z4,z5,z6,z551]),(0,[z1,z8,z25,z523,z5,z6]),(0,[z101,z1,z4,z25,z6,z69]),(0,[z1,z8,z25,z5,z670,z6]),(0,[z1,z8,z4,z132,z306,z6]),(0,[z1,z8,z506,z25,z5,z6]),(0,[z1,z2,z8,z1093,z5,z6]),(0,[z1,z1094,z8,z4,z5,z6])],[(0,[z0,z31,z8,z4,z18,z6]),(0,[z2,z8,z614,z4,z18,z6]),(0,[z1,z2,z8,z1095,z5,z6]),(0,[z1,z2,z8,z4,z1096,z6]),(0,[z177,z1,z8,z25,z5,z6]),(0,[z1097,z1,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1098,z6]),(0,[z31,z1,z8,z4,z338,z6]),(0,[z1,z2,z8,z802,z18,z6]),(0,[z1,z2,z8,z296,z18,z6]),(0,[z1,z2,z8,z18,z1099,z6]),(0,[z1,z2,z8,z4,z77,z82]),(0,[z16,z2,z8,z4,z879,z6]),(0,[z1,z8,z25,z528,z5,z6]),(0,[z1,z243,z8,z842,z5,z6]),(0,[z1,z8,z4,z25,z397,z6]),(0,[z51,z1,z8,z25,z6,z20]),(0,[z152,z1,z8,z296,z5,z6]),(0,[z1,z2,z8,z4,z1100,z6])],[(0,[z1,z118,z8,z25,z18,z6])]],
   [[(0,[z1,z2,z8,z1101,z5,z6]),(0,[z1,z2,z8,z4,z1102,z6]),(0,[z2,z8,z4,z621,z18,z6]),(0,[z31,z16,z8,z4,z46,z6]),(0,[z162,z1,z8,z301,z5,z6]),(0,[z1,z117,z8,z25,z147,z6]),(0,[z106,z31,z1,z8,z25,z6]),(0,[z1,z8,z4,z25,z1103,z6]),(0,[z51,z1,z2,z8,z230,z6]),(0,[z1,z2,z8,z4,z1104,z6])],[(0,[z229,z83,z8,z235,z5,z6]),(0,[z44,z2,z8,z235,z5,z6]),(0,[z625,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z924,z46,z6]),(0,[z1,z24,z192,z4,z5,z6]),(0,[z2,z8,z4,z36,z6,z233])],[(1,[z1,z8,z861,z5,z6]),(0,[z51,z106,z1,z8,z25,z6]),(0,[z1,z8,z4,z5,z6,z1105])],[(0,[z1,z2,z8,z193,z18,z6]),(0,[z1,z8,z4,z25,z414,z6]),(0,[z1,z2,z8,z4,z1106,z6])],[(0,[z1,z311,z8,z4,z18,z6]),(0,[z381,z2,z8,z4,z18,z6]),(0,[z1,z8,z4,z5,z1107,z6]),(0,[z1108,z2,z8,z4,z5,z6]),(0,[z51,z1,z2,z8,z6,z493])],[(0,[z1,z2,z8,z4,z1109,z6]),(0,[z103,z2,z8,z4,z18,z6]),(0,[z1,z762,z192,z4,z5,z6]),(0,[z51,z1,z8,z25,z6,z69]),(0,[z1,z8,z4,z25,z167,z6]),(0,[z1,z2,z8,z5,z516,z6]),(0,[z1,z2,z8,z1110,z5,z6]),(0,[z1,z2,z8,z1111,z5,z6])],[(0,[z290,z2,z8,z4,z5,z6]),(0,[z91,z2,z3,z4,z18,z6]),(0,[z106,z1,z8,z4,z6,z325]),(0,[z466,z1,z8,z25,z5,z6]),(0,[z31,z8,z4,z5,z6,z233]),(0,[z2,z8,z4,z5,z6,z1112])],[(0,[z2,z8,z858,z4,z5,z6]),(0,[z1,z2,z8,z4,z1113,z6]),(0,[z1,z2,z8,z319,z18,z6]),(0,[z466,z1,z8,z4,z46,z6]),(0,[z208,z1,z367,z8,z4,z6]),(0,[z2,z160,z4,z5,z233,z14])]],
   [[(0,[z1,z1114,z8,z4,z5,z6]),(0,[z2,z8,z4,z18,z6,z454]),(0,[z1,z785,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1115,z6]),(0,[z1,z2,z8,z4,z1070,z6]),(0,[z51,z1,z8,z25,z79,z6]),(0,[z512,z1,z8,z4,z5,z179])],[(0,[z83,z2,z8,z235,z241,z6]),(0,[z1,z2,z8,z4,z1116,z6]),(0,[z328,z1,z8,z4,z18,z6]),(0,[z1,z118,z8,z25,z46,z6]),(0,[z1,z8,z4,z25,z359,z6]),(0,[z1,z8,z231,z25,z5,z6]),(0,[z1,z2,z8,z301,z5,z6]),(0,[z1028,z2,z8,z4,z5,z6]),(0,[z328,z1,z8,z4,z119,z6])],[(0,[z1,z2,z8,z4,z5,z1117]),(0,[z1118,z1,z8,z4,z5,z6]),(0,[z474,z2,z8,z235,z5,z6]),(0,[z115,z2,z8,z4,z18,z6]),(0,[z1,z300,z8,z4,z18,z6])],[(0,[z1,z2,z8,z4,z1119,z6]),(0,[z2,z8,z4,z1120,z5,z6])],[(0,[z1121,z1,z8,z4,z5,z6]),(0,[z8,z4,z25,z5,z6,z768])],[(0,[z1,z2,z8,z1122,z5,z6]),(0,[z2,z8,z4,z639,z18,z6]),(0,[z1,z2,z8,z4,z1123,z6]),(0,[z1,z8,z4,z25,z496,z6]),(0,[z1,z1124,z8,z4,z5,z6])],[(0,[z1,z8,z25,z18,z6,z54]),(0,[z1,z311,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z1125,z6]),(0,[z1,z8,z4,z25,z1126,z6]),(0,[z1,z686,z8,z25,z5,z6])],[(0,[z31,z1,z8,z4,z369,z6]),(0,[z58,z269,z8,z4,z369,z6]),(0,[z1,z2,z8,z4,z1039,z6]),(0,[z1,z2,z8,z4,z224,z6]),(0,[z1,z2,z858,z4,z5,z6]),(0,[z2,z8,z4,z235,z18,z6]),(0,[z1,z8,z4,z25,z147,z6]),(0,[z31,z1,z8,z4,z1037,z6]),(0,[z1,z2,z8,z4,z1127,z6])]],
   [[(0,[z1,z2,z8,z4,z77,z175]),(0,[z106,z1,z8,z4,z25,z6]),(0,[z51,z1,z56,z8,z25,z6]),(0,[z1,z2,z844,z8,z5,z6]),(0,[z2,z8,z4,z119,z6,z233])],[(0,[z315,z1,z8,z4,z5,z6]),(0,[z1,z1128,z8,z4,z5,z6]),(0,[z910,z1,z8,z25,z5,z6]),(0,[z1,z2,z8,z319,z46,z6])],[(0,[z1,z2,z8,z4,z1129,z6]),(0,[z1,z2,z8,z4,z338,z6]),(0,[z489,z1,z8,z4,z46,z6]),(0,[z1,z564,z8,z25,z5,z6])],[(0,[z161,z2,z8,z4,z18,z6]),(0,[z328,z1,z8,z4,z46,z6]),(0,[z1,z8,z4,z1092,z46,z6]),(0,[z1,z8,z301,z25,z5,z6]),(0,[z1,z977,z118,z8,z5,z6]),(0,[z106,z1,z2,z8,z4,z6]),(0,[z1,z2,z8,z4,z67,z82])],[(0,[z247,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z1130,z5,z6]),(0,[z126,z2,z8,z4,z5,z6]),(0,[z1,z300,z8,z4,z46,z6]),(0,[z1,z8,z4,z257,z46,z6]),(0,[z210,z1,z8,z25,z5,z6]),(0,[z1,z311,z8,z62,z5,z6]),(0,[z795,z1,z2,z8,z301,z6])],[(0,[z1,z2,z963,z8,z4,z5]),(0,[z1,z2,z8,z4,z1131,z6]),(0,[z2,z8,z4,z18,z481,z6]),(0,[z51,z1,z50,z8,z25,z6]),(0,[z31,z1,z8,z4,z1132,z6]),(0,[z1,z2,z8,z4,z1133,z6]),(0,[z1,z2,z8,z13,z5,z6]),(0,[z1,z2,z844,z73,z5,z6])],[(0,[z1,z2,z8,z4,z1134,z6]),(0,[z1,z2,z8,z4,z1135,z6]),(0,[z44,z1,z8,z25,z5,z6]),(0,[z1136,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1137,z6])],[(0,[z1138,z2,z8,z4,z5,z6]),(0,[z1139,z2,z8,z4,z5,z6]),(0,[z1,z575,z8,z25,z5,z6]),(0,[z31,z1,z8,z4,z397,z6]),(0,[z1,z8,z4,z5,z709,z6]),(0,[z1017,z2,z8,z4,z147,z6]),(0,[z1,z2,z8,z1140,z5,z6]),(0,[z1,z245,z118,z8,z5,z6])]],
   [[(0,[z1,z603,z8,z25,z5,z6]),(0,[z1,z2,z8,z4,z197,z347]),(0,[z1,z961,z8,z4,z46,z6]),(0,[z1,z8,z25,z5,z6,z588]),(0,[z1,z2,z8,z4,z1141,z6]),(0,[z1,z2,z160,z4,z397,z14]),(0,[z2,z8,z4,z958,z6,z233]),(0,[z1,z8,z4,z5,z6,z1142])],[(0,[z1143,z1,z2,z8,z4,z6]),(0,[z1,z1144,z8,z4,z5,z6]),(0,[z820,z1,z8,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z1145])],[(0,[z2,z8,z4,z5,z6,z794]),(0,[z1,z2,z935,z8,z4,z5]),(0,[z1,z8,z4,z25,z722,z6]),(0,[z31,z1,z160,z4,z5,z14]),(0,[z1,z1146,z8,z4,z5,z6])],[(0,[z1,z1147,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1090,z6]),(0,[z1,z2,z8,z4,z1148,z6]),(0,[z2,z68,z8,z4,z141,z6])],[(0,[z1,z2,z8,z341,z369,z6]),(0,[z1,z8,z579,z25,z5,z6]),(0,[z1,z2,z8,z4,z241,z6]),(0,[z1,z8,z4,z5,z6,z1149]),(0,[z1,z245,z8,z4,z18,z6]),(0,[z1,z117,z8,z25,z46,z6]),(0,[z1150,z1,z8,z4,z5,z6]),(0,[z31,z1,z8,z4,z414,z6])],[(0,[z1,z805,z8,z4,z5,z6]),(0,[z1,z2,z8,z272,z18,z6]),(0,[z1151,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1152,z6]),(0,[z101,z31,z1,z4,z6,z69]),(0,[z1,z2,z8,z4,z1153,z6]),(0,[z1154,z1,z8,z4,z5,z6])],[(0,[z1,z2,z8,z5,z1099,z6]),(0,[z1,z367,z8,z4,z18,z6]),(0,[z31,z1,z8,z4,z167,z6])],[(0,[z114,z1,z8,z122,z5,z6]),(0,[z1,z1155,z8,z4,z5,z6]),(0,[z229,z1,z8,z4,z98,z6]),(0,[z1143,z1,z8,z4,z130,z6]),(0,[z1,z2,z8,z4,z1156,z6]),(0,[z1,z2,z8,z861,z5,z6]),(0,[z1,z56,z8,z231,z19,z6]),(0,[z1,z60,z245,z8,z5,z54])]],
   [[(0,[z1,z2,z8,z1157,z5,z6]),(0,[z1,z2,z8,z4,z1158,z6]),(0,[z1,z2,z8,z1159,z5,z6]),(0,[z2,z8,z25,z235,z18,z6]),(0,[z1,z2,z8,z4,z1160,z6]),(0,[z1161,z1,z8,z4,z5,z6]),(0,[z1,z833,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z48,z6]),(0,[z2,z207,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z1162,z6]),(0,[z1,z166,z60,z8,z5,z54])],[(0,[z85,z8,z4,z25,z5,z86]),(0,[z1,z8,z4,z5,z6,z1163]),(0,[z1,z8,z4,z25,z119,z6]),(0,[z51,z1,z8,z25,z5,z6])],[(0,[z1,z2,z8,z122,z5,z6]),(0,[z0,z2,z3,z4,z18,z6]),(0,[z1,z2,z8,z1164,z5,z6]),(0,[z1,z2,z8,z4,z1165,z6]),(0,[z31,z1,z8,z4,z359,z6]),(0,[z1,z1166,z8,z4,z5,z6]),(0,[z1,z2,z8,z6,z781,z20]),(0,[z1,z2,z60,z8,z360,z54])],[(0,[z1,z2,z8,z4,z369,z6]),(0,[z1167,z1,z8,z4,z5,z6]),(0,[z1,z2,z1168,z4,z5,z6])],[],[(0,[z120,z2,z8,z4,z5,z6])],[(0,[z58,z269,z8,z341,z5,z6]),(0,[z2,z3,z8,z4,z170,z6]),(0,[z1,z2,z8,z4,z1169,z6]),(0,[z31,z1,z8,z4,z496,z6]),(0,[z162,z1,z192,z4,z18,z6]),(0,[z1,z245,z8,z4,z46,z6]),(0,[z1,z142,z8,z4,z46,z6]),(0,[z1,z8,z65,z25,z5,z6])],[(0,[z1,z8,z122,z5,z26,z6]),(0,[z373,z2,z8,z4,z18,z6]),(0,[z1,z8,z4,z46,z6,z155]),(0,[z1,z2,z8,z272,z46,z6]),(0,[z1,z8,z4,z25,z752,z6]),(0,[z1,z2,z8,z4,z1170,z6])]],
   [[(0,[z1,z2,z8,z1171,z5,z6]),(0,[z1,z367,z8,z4,z46,z6]),(0,[z51,z1,z8,z25,z39,z6]),(0,[z1,z118,z8,z132,z25,z6]),(0,[z106,z1,z8,z4,z132,z6]),(0,[z1172,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1132,z6]),(0,[z1,z8,z4,z25,z67,z82]),(0,[z1,z620,z8,z25,z5,z6]),(0,[z1,z80,z8,z25,z5,z6])],[(0,[z58,z1,z8,z301,z5,z6]),(0,[z1173,z1,z2,z8,z4,z6]),(0,[z1,z8,z25,z46,z79,z6]),(0,[z126,z2,z8,z25,z5,z6]),(0,[z126,z56,z2,z8,z4,z6])],[(0,[z1,z2,z8,z1174,z5,z6]),(0,[z1,z88,z8,z25,z5,z6]),(0,[z2,z3,z4,z89,z18,z6]),(0,[z1,z8,z4,z25,z46,z6]),(0,[z630,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z1175,z6]),(0,[z1,z626,z8,z25,z5,z6]),(1,[z1,z8,z25,z167,z6]),(0,[z1,z616,z8,z25,z5,z6]),(0,[z1,z1176,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1177,z6]),(0,[z1,z93,z8,z25,z5,z6]),(0,[z1,z56,z367,z8,z4,z6]),(0,[z1,z2,z8,z1178,z5,z6]),(0,[z1,z2,z8,z4,z1179,z6])],[(0,[z58,z269,z8,z4,z5,z6]),(0,[z1,z2,z60,z8,z18,z54]),(0,[z106,z1,z243,z8,z25,z6]),(0,[z106,z1,z8,z25,z79,z6]),(0,[z1,z8,z25,z5,z6,z125]),(0,[z1,z2,z8,z4,z1103,z6]),(0,[z1,z2,z8,z4,z772,z6]),(0,[z1,z2,z8,z4,z1180,z6]),(0,[z1,z2,z8,z1181,z5,z6])],[(0,[z51,z1,z2,z8,z6,z434]),(0,[z1,z66,z8,z301,z5,z6]),(0,[z1,z8,z25,z5,z6,z134]),(0,[z8,z4,z25,z5,z141,z6]),(0,[z1,z8,z25,z5,z6,z54]),(0,[z1,z2,z160,z4,z5,z14]),(0,[z284,z2,z8,z4,z973,z6]),(0,[z1,z8,z4,z1182,z5,z6])],[(0,[z1,z2,z8,z4,z1183,z6]),(0,[z1,z2,z8,z4,z1184,z6]),(0,[z1,z2,z8,z4,z1185,z6]),(0,[z1,z2,z8,z4,z1186,z6]),(0,[z1,z2,z8,z4,z1187,z6]),(0,[z1188,z1,z8,z4,z5,z6])]],
   [[(0,[z162,z1,z192,z4,z46,z6]),(0,[z1,z8,z25,z5,z638,z6]),(0,[z1189,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1190,z6]),(0,[z51,z1,z2,z8,z132,z6])],[(0,[z1,z92,z8,z4,z5,z6]),(0,[z1,z8,z639,z25,z5,z6]),(0,[z1191,z1,z8,z4,z5,z6]),(0,[z1192,z2,z8,z4,z5,z6]),(0,[z51,z208,z1,z8,z25,z6]),(0,[z1193,z2,z8,z4,z5,z6]),(0,[z1,z1194,z8,z4,z5,z6])],[(0,[z1,z8,z567,z25,z5,z6]),(0,[z1,z8,z25,z235,z5,z6]),(0,[z1,z2,z8,z4,z723,z6]),(0,[z569,z2,z8,z4,z46,z6]),(0,[z1,z2,z8,z4,z1195,z6]),(0,[z1,z117,z24,z25,z5,z6])],[(0,[z1196,z1,z8,z4,z5,z6]),(0,[z1,z8,z139,z25,z5,z6]),(0,[z1,z8,z4,z25,z784,z6]),(0,[z1,z2,z4,z5,z836,z14])],[(0,[z247,z1,z8,z861,z5,z6]),(0,[z1,z2,z8,z4,z731,z6]),(0,[z1,z2,z160,z5,z516,z14])],[(0,[z30,z2,z8,z4,z18,z6]),(0,[z2,z8,z4,z46,z879,z6]),(0,[z1,z8,z4,z25,z48,z6]),(0,[z1,z2,z8,z1197,z5,z6]),(0,[z1,z8,z25,z167,z5,z6]),(0,[z1,z2,z8,z4,z1198,z6]),(0,[z126,z2,z50,z8,z4,z6])],[(0,[z111,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z5,z983]),(0,[z1,z1199,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1200,z6]),(0,[z1,z150,z8,z25,z5,z6]),(0,[z1,z2,z8,z4,z1201,z6])]],
   [[(0,[z1,z2,z1202,z4,z5,z6]),(0,[z2,z7,z8,z4,z18,z6]),(0,[z2,z8,z4,z968,z18,z6]),(0,[z1,z35,z8,z4,z46,z6]),(0,[z51,z1,z8,z25,z46,z6]),(0,[z1,z2,z839,z8,z4,z5]),(0,[z987,z1,z2,z8,z4,z6]),(0,[z1,z8,z13,z25,z5,z6]),(0,[z1,z8,z25,z360,z6,z54]),(0,[z31,z1,z8,z301,z5,z6])],[(0,[z2,z8,z4,z288,z18,z6]),(0,[z867,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z132,z6]),(0,[z51,z2,z8,z4,z141,z6])],[(0,[z1,z2,z8,z341,z5,z6]),(0,[z1,z2,z8,z4,z138,z6]),(0,[z1,z2,z8,z4,z496,z6]),(0,[z1,z2,z8,z4,z1203,z6]),(0,[z31,z1,z8,z4,z119,z6]),(0,[z1,z2,z8,z4,z5,z836])],[(0,[z1,z1204,z8,z4,z5,z6]),(0,[z1205,z1,z8,z4,z25,z6]),(0,[z1,z2,z4,z46,z6,z1021]),(0,[z1,z163,z8,z25,z5,z6]),(0,[z1,z117,z8,z132,z25,z6]),(0,[z1,z2,z8,z4,z1126,z6]),(0,[z2,z1206,z8,z4,z5,z6]),(0,[z1,z171,z8,z301,z5,z6])],[(0,[z1,z8,z4,z25,z146,z6]),(0,[z0,z2,z858,z4,z5,z6]),(0,[z1,z8,z25,z461,z46,z6]),(0,[z1,z2,z8,z1187,z193,z6]),(0,[z1,z2,z8,z1207,z5,z6]),(0,[z1,z8,z25,z5,z6,z662]),(0,[z1,z2,z8,z4,z147,z6])],[(0,[z31,z3,z8,z4,z18,z6]),(0,[z252,z1,z8,z25,z5,z6]),(0,[z1208,z2,z8,z4,z5,z6]),(0,[z1,z565,z8,z25,z5,z54]),(0,[z1,z1209,z8,z4,z5,z6]),(0,[z1,z1210,z8,z4,z5,z6])],[(0,[z1,z2,z8,z1211,z5,z6]),(0,[z1,z2,z8,z4,z1212,z6]),(0,[z845,z1,z2,z8,z4,z6]),(0,[z1,z2,z8,z4,z1213,z6]),(0,[z1,z2,z8,z1214,z5,z6]),(0,[z28,z2,z8,z4,z18,z6]),(0,[z1,z2,z8,z4,z1215,z6]),(0,[z1205,z1,z2,z8,z4,z6]),(0,[z1,z2,z8,z4,z1216,z6]),(0,[z1,z657,z8,z25,z5,z6]),(0,[z328,z1,z8,z4,z36,z6]),(0,[z126,z2,z8,z4,z79,z6]),(0,[z1,z8,z4,z5,z1217,z6])],[(0,[z1,z8,z4,z25,z43,z6]),(0,[z1,z2,z8,z5,z1218,z6]),(0,[z1,z658,z8,z25,z5,z6]),(0,[z1,z2,z8,z5,z1219,z6]),(0,[z1,z2,z844,z4,z5,z6]),(0,[z1,z2,z8,z4,z6,z793])]]]

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
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 920).take 435) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1355)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [460, 460, 435] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 91).take 90).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 181).take 75).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [91, 90, 75] = true :=
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

end PEqualNP.Outside.L_meta_45770

theorem PEqualNP.Outside.L_meta_45770 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241888 * 2 ^ 32 + 4008216704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241888 * 2 ^ 32 + 4008216704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45770.solve