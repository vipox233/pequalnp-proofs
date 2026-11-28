import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38771

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4238919816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0010224258836159#64 ++ 0x4001022425883615#64 ++ 0x5031e7c7d88fe3ff#64 ++ 0xa5031e7c7d88fe3f#64 : BitVec 256),
   (0x00c6891920388ea2#64 ++ 0x800c6891920388ea#64 ++ 0xe1ce993920f8ffff#64 ++ 0x7e1ce993920f8fff#64 : BitVec 256),
   (0x160b162e2b0d34c3#64 ++ 0x0160b162e2b0d34c#64 ++ 0x7e0f1e3e3f0f3cce#64 ++ 0xf7e0f1e3e3f0f3cc#64 : BitVec 256),
   (0x2b701fc01dd03b0c#64 ++ 0x02b701fc01dd03b0#64 ++ 0xbff01fc03ff03f0d#64 ++ 0xfbff01fc03ff03f0#64 : BitVec 256),
   (0x8dbfe00036eec000#64 ++ 0x08dbfe00036eec00#64 ++ 0xbfffe0003fffc00b#64 ++ 0xebfffe0003fffc00#64 : BitVec 256),
   (0x4fedddb580000000#64 ++ 0x04fedddb58000000#64 ++ 0xcfffffffc0000007#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [10, 5]⟩, ⟨.and, [8, 7]⟩, ⟨.and, [13, 11]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0010224258836159 0x4001022425883615 0x5031e7c7d88fe3ff 0xa5031e7c7d88fe3f

def z1 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1ce993920f8ffff 0x7e1ce993920f8fff

def z2 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0f1e3e3f0f3cce 0xf7e0f1e3e3f0f3cc

def z3 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff01fc03ff03f0d 0xfbff01fc03ff03f0

def z4 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfffffffc0000007 0xfcfffffffc000000

def z5 : W := mkw 0x8dafc000266c8000 0x08dafc000266c800 0xbfcf00003f7f000a 0xebfcf00003f7f000

def z6 : W := mkw 0x0010224258836159 0x4001022425883615 0x4030e7c7c080e3f5 0x04030e7c7c080e3f

def z7 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfffe0003fffc00b 0xebfffe0003fffc00

def z8 : W := mkw 0x4ffdfdb590824000 0x04ffdfdb59082400 0xdfffffffd88fc00f 0xfdfffffffd88fc00

def z9 : W := mkw 0x040b0008220c0482 0x0040b0008220c048 0x7e0f18383f0f3cce 0xf7e0f18383f0f3cc

def z10 : W := mkw 0x201002401dd03b0c 0x0201002401dd03b0 0x300000003ff03f08 0x0300000003ff03f0

def z11 : W := mkw 0x8012200036eec000 0x08012200036eec00 0x300000003fffc008 0x0300000003fffc00

def z12 : W := mkw 0x16dfbf7f7bbffffb 0xc16dfbf7f7bbffff 0xffffffffffffffff 0xffffffffffffffff

def z13 : W := mkw 0x00d6a95970bacfba 0xc00d6a95970bacfb 0xe1fef9f9e0f8ffff 0x7e1fef9f9e0f8fff

def z14 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xfff1ffc7ffffffff 0xffff1ffc7fffffff

def z15 : W := mkw 0x0000024248012159 0x4000002424801215 0x400007c7c00023f4 0x0400007c7c00023f

def z16 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xafc0180027701c00 0x5afc0180027701c0

def z17 : W := mkw 0x6fedddb585501a04 0x06fedddb585501a0 0xefffffffe7701c07 0xfefffffffe7701c0

def z18 : W := mkw 0x0010200010824000 0x0001020001082400 0x1031e000188fc00b 0xa1031e000188fc00

def z19 : W := mkw 0x8dafc000266c8000 0x08dafc000266c800 0xafce000027700000 0x4afce00002770000

def z20 : W := mkw 0x00868019202884a2 0x800868019202884a 0x400e80390008c0f2 0x0400e80390008c0f

def z21 : W := mkw 0x848fe000222ec000 0x0848fe000222ec00 0x000fe000000fc002 0x0000fe000000fc00

def z22 : W := mkw 0x0200160009003000 0x0020016000900300 0x3e001e003f003c0c 0xf3e001e003f003c0

def z23 : W := mkw 0x6f3956e49dc0310c 0x06f3956e49dc0310 0x1e3166c6df000000 0x81e3166c6df00000

def z24 : W := mkw 0x8defc919267c8ea2 0x88defc919267c8ea 0xefce993927f8ffff 0x7efce993927f8fff

def z25 : W := mkw 0x0000020009003000 0x0000002000900300 0x300000003f003c08 0x0300000003f003c0

def z26 : W := mkw 0x8ffffd8036eec000 0x08ffffd8036eec00 0xbfffffc03fffc00f 0xfbfffffc03fffc00

def z27 : W := mkw 0x49f4ebd3d8836159 0x449f4ebd3d883615 0xd1f1e7c7d88fe3ff 0xad1f1e7c7d88fe3f

def z28 : W := mkw 0x46491db580000000 0x046491db58000000 0x4e0f1fffc0000006 0xf4e0f1fffc000000

def z29 : W := mkw 0x060b142c20080482 0x0060b142c2008048 0x6e0f1e3e20083cce 0xf6e0f1e3e20083cc

def z30 : W := mkw 0x0010224258836159 0x4001022425883615 0x1031e6c6d88fc00b 0xa1031e6c6d88fc00

def z31 : W := mkw 0x4040099180000000 0x0404009918000000 0x000001c1c0000000 0x0000001c1c000000

def z32 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xa1ce183820701c00 0x5a1ce183820701c0

def z33 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1ffffffe0f8ffff 0xfe1ffffffe0f8fff

def z34 : W := mkw 0x161b362e3b8f74c3 0x0161b362e3b8f74c 0x7e3ffe3e3f8ffccf 0xf7e3ffe3e3f8ffcc

def z35 : W := mkw 0x448fc03da02884a2 0x8448fc03da02884a 0x400fe03fc008c0f2 0x0400fe03fc008c0f

def z36 : W := mkw 0x0609142400000000 0x0060914240000000 0x4e0f1e3e00000006 0xf4e0f1e3e0000000

def z37 : W := mkw 0x5fefdfbfab0d34c3 0x05fefdfbfab0d34c 0xffffffffff0f3ccf 0xfffffffffff0f3cc

def z38 : W := mkw 0x448dc03580000000 0x0448dc0358000000 0x400fe03fc0000002 0x0400fe03fc000000

def z39 : W := mkw 0x364b1fee2b1d3fcf 0x0364b1fee2b1d3fc 0x7e0f1ffe3f0f3fce 0xf7e0f1ffe3f0f3fc

def z40 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xffffe1013fffe3ff 0xeffffe1013fffe3f

def z41 : W := mkw 0x0000000000000000 0x0000000000000000 0x400081010088e3ff 0x2400081010088e3f

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0x0030e1c1c0000001 0x00030e1c1c000000

def z43 : W := mkw 0x0010204050824118 0x4001020405082411 0x0030e1c1c080c331 0x00030e1c1c080c33

def z44 : W := mkw 0x160b142c230c1482 0x0160b142c230c148 0x2e0e183827001c00 0x52e0e183827001c0

def z45 : W := mkw 0x0040090000100a00 0x00040090000100a0 0xa1c0190020f03f0d 0x7a1c0190020f03f0

def z46 : W := mkw 0x2bf69fd93df8bfae 0x82bf69fd93df8bfa 0xfffe9ff93ff8ffff 0xffffe9ff93ff8fff

def z47 : W := mkw 0x00c4891100000000 0x000c489110000000 0xc1ce993900000007 0x7c1ce99390000000

def z48 : W := mkw 0x4f2954a480000000 0x04f2954a48000000 0x0e3166c6c0000000 0x80e3166c6c000000

def z49 : W := mkw 0x1200162e090134c3 0x01200162e090134c 0x40001e3e00003cc4 0x140001e3e00003cc

def z50 : W := mkw 0x89b4e00014e2c000 0x089b4e00014e2c00 0x81f0e00000f0c001 0x081f0e00000f0c00

def z51 : W := mkw 0x0000020208012041 0x0000002020801204 0x40000606000020c4 0x040000606000020c

def z52 : W := mkw 0x16cf9f3f2b3dbee3 0x816cf9f3f2b3dbee 0xffcf9f3f3fffffff 0xfffcf9f3f3ffffff

def z53 : W := mkw 0x3f6b1fae2f5d3ec7 0x03f6b1fae2f5d3ec 0xffcf1e3e3f7f3cce 0xfffcf1e3e3f7f3cc

def z54 : W := mkw 0x4fedddb580100a00 0x04fedddb580100a0 0xefffffffe0f03f0f 0xfefffffffe0f03f0

def z55 : W := mkw 0x8d39600016c64000 0x08d39600016c6400 0x1e3160001f070000 0x81e3160001f07000

def z56 : W := mkw 0x9fbff62e3feff4c3 0x09fbff62e3feff4c 0xfffffe3e3ffffccf 0xffffffe3e3ffffcc

def z57 : W := mkw 0x4dedc9b580000000 0x04dedc9b58000000 0xc1ffe1ffc0000003 0x0c1ffe1ffc000000

def z58 : W := mkw 0x1002020a2b0d34c3 0x01002020a2b0d34c 0x300000003f0f3cc8 0x0300000003f0f3cc

def z59 : W := mkw 0x1210366e598375db 0x41210366e598375d 0x5031ffffd88fffff 0xb5031ffffd88ffff

def z60 : W := mkw 0x0b601d8000000000 0x00b601d800000000 0x8ff01fc000000005 0xf8ff01fc00000000

def z61 : W := mkw 0xafffffc03ffefb0c 0x0afffffc03ffefb0 0xbfffffc03fffff0f 0xfbfffffc03fffff0

def z62 : W := mkw 0x22c69fd92938bfae 0x822c69fd92938bfa 0xe1ce9ff920f8ffff 0x7e1ce9ff920f8fff

def z63 : W := mkw 0x00868019202884a2 0x800868019202884a 0xe1ce803920f8c0fb 0x6e1ce803920f8c0f

def z64 : W := mkw 0x0000020208012041 0x0000002020801204 0x50010606180f20ce 0xa50010606180f20c

def z65 : W := mkw 0x22401d8001101a04 0x022401d8001101a0 0x0000180000001c00 0x10000180000001c0

def z66 : W := mkw 0x8dbfe01936eec4a2 0x88dbfe01936eec4a 0xffffe0393fffc0fb 0xeffffe0393fffc0f

def z67 : W := mkw 0x2b3016c01dc0310c 0x02b3016c01dc0310 0x1e3006c01f000000 0x81e3006c01f00000

def z68 : W := mkw 0xafefdd80277c9a04 0x0afefdd80277c9a0 0xafce180027701c00 0x5afce180027701c0

def z69 : W := mkw 0x4f2954a480000000 0x04f2954a48000000 0x0e00000000000000 0x00e0000000000000

def z70 : W := mkw 0x041b2000328e4000 0x0041b2000328e400 0x3e3fe0003f8fc00b 0xe3e3fe0003f8fc00

def z71 : W := mkw 0x160b166e6b0d35db 0x4160b166e6b0d35d 0x7e0f1fffff0f3ffe 0xf7e0f1fffff0f3ff

def z72 : W := mkw 0x048f8000222c8000 0x0048f8000222c800 0xbfcf80003fffc00b 0xebfcf80003fffc00

def z73 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xbff000003ff00009 0xebff000003ff0000

def z74 : W := mkw 0x0930000014c00000 0x00930000014c0000 0x1e3000001f000000 0x81e3000001f00000

def z75 : W := mkw 0x42401db580000000 0x042401db58000000 0x40001fffc0000004 0x140001fffc000000

def z76 : W := mkw 0x161b366e7b8f75db 0x4161b366e7b8f75d 0x7e3fffffff8fffff 0xf7e3fffffff8ffff

def z77 : W := mkw 0x0010024018802108 0x0001002401880210 0x103007c01880230d 0xa103007c01880230

def z78 : W := mkw 0x0920000004400000 0x0092000000440000 0xafc0000027700000 0x4afc000002770000

def z79 : W := mkw 0x0086800020288000 0x0008680002028800 0xa1ce800020f8c00b 0x6a1ce800020f8c00

def z80 : W := mkw 0x00c4891100308a20 0x800c4891100308a2 0xa1c0990120f0ff3d 0x7a1c0990120f0ff3

def z81 : W := mkw 0x0619366658836159 0x4061936665883615 0x5e3fffffd88fe3ff 0xf5e3fffffd88fe3f

def z82 : W := mkw 0x0010224258836159 0x4001022425883615 0x10000000188fe3f8 0x010000000188fe3f

def z83 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0x8fce183800000000 0x58fce18380000000

def z84 : W := mkw 0x1002020a2b0d34c3 0x01002020a2b0d34c 0x700106063f0f3cce 0xa700106063f0f3cc

def z85 : W := mkw 0x49e4c99180000000 0x049e4c9918000000 0x81f0e1c1c0000001 0x081f0e1c1c000000

def z86 : W := mkw 0x2b601fc00d503b0c 0x02b601fc00d503b0 0xafc01fc027703f04 0x5afc01fc027703f0

def z87 : W := mkw 0x5fefdfbfab3dbee3 0x85fefdfbfab3dbee 0xffffffffffffffff 0xffffffffffffffff

def z88 : W := mkw 0x0b703fc258836159 0x40b703fc25883615 0xdff1ffc7d88fe3ff 0xfdff1ffc7d88fe3f

def z89 : W := mkw 0x00c6890020388a00 0x000c6890020388a0 0xa1ce990020f8ff0f 0x7a1ce990020f8ff0

def z90 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff01ec03f701c00 0xdbff01ec03f701c0

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0x4031e7c7c0000007 0xa4031e7c7c000000

def z92 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbfc018003ff03f08 0x5bfc018003ff03f0

def z93 : W := mkw 0x0040091100100a20 0x80040091100100a2 0x0000010100000330 0x0000001010000033

def z94 : W := mkw 0x8dffe91936fecea2 0x88dffe91936fecea 0xfffff9393fffffff 0xffffff9393ffffff

def z95 : W := mkw 0x0dbdc00014c00000 0x00dbdc00014c0000 0xbfffe0003ff0000b 0xebfffe0003ff0000

def z96 : W := mkw 0x0000200240034051 0x4000020024003405 0x4001e007c00fc0f2 0x04001e007c00fc0f

def z97 : W := mkw 0x0002000820388ea2 0x80002000820388ea 0x2000000020f8fff8 0x02000000020f8fff

def z98 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xaff01fc027701c05 0xfaff01fc027701c0

def z99 : W := mkw 0x2b701fc25dd13b5d 0x42b701fc25dd13b5 0xfff01fc7fff03ffd 0xffff01fc7fff03ff

def z100 : W := mkw 0x2b721fc83dd83f8e 0x02b721fc83dd83f8 0xfffe1ff83ff83fcf 0xffffe1ff83ff83fc

def z101 : W := mkw 0x22401fc009103b0c 0x022401fc009103b0 0xa1c01fc020f03f0d 0x7a1c01fc020f03f0

def z102 : W := mkw 0x2b703fc05dd27b1c 0x42b703fc05dd27b1 0xbff0ffc1fff0ff3d 0xfbff0ffc1fff0ff3

def z103 : W := mkw 0x2b601f800d503a04 0x02b601f800d503a0 0xbfc01e003f703c0c 0xfbfc01e003f703c0

def z104 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0x8ff1e7c7c0000001 0x88ff1e7c7c000000

def z105 : W := mkw 0x148f803f222d84e3 0x8148f803f222d84e 0x400f803f000fc0f2 0x0400f803f000fc0f

def z106 : W := mkw 0x0202160829083482 0x0020216082908348 0x7e0e1e383f083cce 0xf7e0e1e383f083cc

def z107 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xfff1ffc7fff03f0f 0xffff1ffc7fff03f0

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0x0031e00000000003 0xa0031e0000000000

def z109 : W := mkw 0xabf4ffc01df2fb0c 0x0abf4ffc01df2fb0 0xbff0ffc03ff0ff0d 0xfbff0ffc03ff0ff0

def z110 : W := mkw 0x22401fc249113b5d 0x422401fc249113b5 0x40001fc7c0003ff4 0x140001fc7c0003ff

def z111 : W := mkw 0x0b20148000000000 0x00b2014800000000 0x0e3006c000000000 0x80e3006c00000000

def z112 : W := mkw 0x0040091900100ea2 0x80040091900100ea 0x4000193900003ff4 0x14000193900003ff

def z113 : W := mkw 0x0002000820388ea2 0x80002000820388ea 0x600e183820f8fffe 0x7600e183820f8fff

def z114 : W := mkw 0x0010024018802108 0x0001002401880210 0x5031e7c7d880230f 0xa5031e7c7d880230

def z115 : W := mkw 0x6ffddff59dd03b0c 0x06ffddff59dd03b0 0xfffffffffff03f0f 0xffffffffffff03f0

def z116 : W := mkw 0x961b362e3feff4c3 0x0961b362e3feff4c 0x7e0f1e3e3ffffcce 0xf7e0f1e3e3ffffcc

def z117 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xbff17fc6fff73f0d 0xfbff17fc6fff73f0

def z118 : W := mkw 0x0b3016001dc03000 0x00b3016001dc0300 0xbff01e003ff03c0d 0xfbff01e003ff03c0

def z119 : W := mkw 0x1f3b162e3fcd34c3 0x01f3b162e3fcd34c 0xffff1e3e3fff3ccf 0xfffff1e3e3fff3cc

def z120 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xa1ce993920f0df31 0x5a1ce993920f0df3

def z121 : W := mkw 0x0086800020288000 0x0008680002028800 0xe1ce810120f8e3ff 0x6e1ce810120f8e3f

def z122 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0x9ff007c01ff00301 0x89ff007c01ff0030

def z123 : W := mkw 0x040b0000220c0000 0x0040b0000220c000 0x3e0f00003f0f000a 0xe3e0f00003f0f000

def z124 : W := mkw 0x140b002e220d04c3 0x0140b002e220d04c 0x400f003e000f00c2 0x0400f003e000f00c

def z125 : W := mkw 0x297009c014d00b0c 0x0297009c014d00b0 0x81f001c000f00301 0x081f001c000f0030

def z126 : W := mkw 0x160916260b053041 0x0160916260b05304 0x1e0106061f070000 0x81e0106061f07000

def z127 : W := mkw 0x29700bc01cd02b0c 0x029700bc01cd02b0 0x91f007c018f0230d 0xa91f007c018f0230

def z128 : W := mkw 0x2bf6bfdb7dfbffff 0xc2bf6bfdb7dfbfff 0xffffffffffffffff 0xffffffffffffffff

def z129 : W := mkw 0x8dbfe2427eefe159 0x48dbfe2427eefe15 0xffffe7c7ffffe3ff 0xeffffe7c7ffffe3f

def z130 : W := mkw 0x0b701fc018802108 0x00b701fc01880210 0x9ff01fc01880230d 0xf9ff01fc01880230

def z131 : W := mkw 0x00c6891920080482 0x000c689192008048 0xe1ce993920083ccf 0x7e1ce993920083cc

def z132 : W := mkw 0x9f3976261fc77041 0x09f3976261fc7704 0x1e3166061f070000 0x81e3166061f07000

def z133 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0f9f3f3f8fffff 0xf7e0f9f3f3f8ffff

def z134 : W := mkw 0x2000000005501a04 0x02000000005501a0 0x2000000027701c00 0x02000000027701c0

def z135 : W := mkw 0x1200162e090134c3 0x01200162e090134c 0x50011e3e180f3cce 0xb50011e3e180f3cc

def z136 : W := mkw 0x42401db580000000 0x042401db58000000 0x4031ffffc0000007 0xb4031ffffc000000

def z137 : W := mkw 0x4f2954a480000000 0x04f2954a48000000 0x4e3f7efec0000006 0xf4e3f7efec000000

def z138 : W := mkw 0x00c4891100308a20 0x800c4891100308a2 0x81c0810100f0c331 0x081c0810100f0c33

def z139 : W := mkw 0x20d68b593df8bfae 0x820d68b593df8bfa 0xf1ce99393ff8ffff 0x7f1ce99393ff8fff

def z140 : W := mkw 0x22401fc009103b0c 0x022401fc009103b0 0x00001fc000003f04 0x100001fc000003f0

def z141 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1ce183820783cce 0x7e1ce183820783cc

def z142 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z143 : W := mkw 0xcfefddb5a66c8000 0x0cfefddb5a66c800 0xefffffffe7700007 0xfefffffffe770000

def z144 : W := mkw 0x164b1f3f2b1d3ee3 0x8164b1f3f2b1d3ee 0x7e0f1f3f3f0f3ffe 0xf7e0f1f3f3f0f3ff

def z145 : W := mkw 0x0000200240034051 0x4000020024003405 0x4031e7c7c00fc0f7 0xa4031e7c7c00fc0f

def z146 : W := mkw 0x6b701ff59dd03b0c 0x06b701ff59dd03b0 0xfff01ffffff03f0d 0xffff01ffffff03f0

def z147 : W := mkw 0x00020008202884a2 0x800020008202884a 0x000000000008c0f0 0x0000000000008c0f

def z148 : W := mkw 0x4fedddbd80100ea2 0x84fedddbd80100ea 0xcfffffffc0003ff7 0xfcfffffffc0003ff

def z149 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xa1c0810120f8fff9 0x0a1c0810120f8fff

def z150 : W := mkw 0x42503ff7d8836159 0x442503ff7d883615 0x5031ffffd88fe3ff 0xb5031ffffd88fe3f

def z151 : W := mkw 0x0609162608012041 0x0060916260801204 0x5e0f1e3e180f20ce 0xf5e0f1e3e180f20c

def z152 : W := mkw 0x1000020a090134c3 0x01000020a090134c 0x0000000000003cc0 0x00000000000003cc

def z153 : W := mkw 0xcffffdb5b6eec000 0x0cffffdb5b6eec00 0xffffffffffffc00f 0xfffffffffffffc00

def z154 : W := mkw 0x1002000a220d04c3 0x01002000a220d04c 0x00000000000f00c0 0x000000000000f00c

def z155 : W := mkw 0x4fefddbda0388ea2 0x84fefddbda0388ea 0xefffffffe0f8ffff 0xfefffffffe0f8fff

def z156 : W := mkw 0x160916260b053041 0x0160916260b05304 0x5e0106061f0f20ce 0xa5e0106061f0f20c

def z157 : W := mkw 0x0010204050824118 0x4001020405082411 0x000000000080c330 0x0000000000080c33

def z158 : W := mkw 0x0086801920388ea2 0x80086801920388ea 0x600e803920f8fffa 0x0600e803920f8fff

def z159 : W := mkw 0x0086800820388ea2 0x80086800820388ea 0xa1ce800020f8fffb 0x6a1ce800020f8fff

def z160 : W := mkw 0x0002000820080482 0x0000200082008048 0x600e99392088ffff 0x7600e99392088fff

def z161 : W := mkw 0xaffffd8037feda04 0x0affffd8037feda0 0xbffff8003fffdc0b 0xfbffff8003fffdc0

def z162 : W := mkw 0x16cf9f3f2b3dbee3 0x816cf9f3f2b3dbee 0xffcf1e3e3f7f3cce 0xfffcf1e3e3f7f3cc

def z163 : W := mkw 0x12401f3f09113ee3 0x812401f3f09113ee 0x40001f3f00003ff4 0x140001f3f00003ff

def z164 : W := mkw 0x0010224258836159 0x4001022425883615 0x1030e1c1d88fe3f9 0x01030e1c1d88fe3f

def z165 : W := mkw 0x0040090000100a00 0x00040090000100a0 0xa1c0180020701c00 0x5a1c0180020701c0

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0x4001e007c0000002 0x04001e007c000000

def z167 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0x1e3fe0001f0fc002 0x81e3fe0001f0fc00

def z168 : W := mkw 0x8010200016c64000 0x08010200016c6400 0x100000001f070000 0x0100000001f07000

def z169 : W := mkw 0x0042090820180e82 0x00042090820180e8 0xe1ce193820f83fcf 0x7e1ce193820f83fc

def z170 : W := mkw 0x0096a00030aac000 0x00096a00030aac00 0xb1ffe00038ffc00b 0xeb1ffe00038ffc00

def z171 : W := mkw 0xafffffc27ffffb5d 0x4afffffc27ffffb5 0xffffffc7ffffffff 0xfffffffc7fffffff

def z172 : W := mkw 0x160b162e2b3dbee3 0x8160b162e2b3dbee 0x7e0f1e3e3ffffffe 0xf7e0f1e3e3ffffff

def z173 : W := mkw 0x801222427eefe159 0x4801222427eefe15 0x7031e7c7ffffe3ff 0xa7031e7c7ffffe3f

def z174 : W := mkw 0x00c4891100000000 0x000c489110000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z175 : W := mkw 0x1f6b1fae2b0d34c3 0x01f6b1fae2b0d34c 0xffff1ffe3f0f3ccf 0xfffff1ffe3f0f3cc

def z176 : W := mkw 0xafffffd93ffeffae 0x8afffffd93ffeffa 0xfffffff93fffffff 0xffffffff93ffffff

def z177 : W := mkw 0x0010224258836159 0x4001022425883615 0x503167c7d80723f4 0x8503167c7d80723f

def z178 : W := mkw 0x0002000820080482 0x0000200082008048 0x600e183820083cce 0x7600e183820083cc

def z179 : W := mkw 0x8d39600016c64000 0x08d39600016c6400 0xbff160003ff70009 0xebff160003ff7000

def z180 : W := mkw 0x849fe00036eec000 0x0849fe00036eec00 0x300fe0003fffc00a 0x0300fe0003fffc00

def z181 : W := mkw 0x0010224258836159 0x4001022425883615 0x103166c6d8070000 0x8103166c6d807000

def z182 : W := mkw 0x0000020208012041 0x0000002020801204 0x10000000180f20c8 0x010000000180f20c

def z183 : W := mkw 0x4fedddb580308a20 0x84fedddb580308a2 0xcfffffffc0f0c337 0xfcfffffffc0f0c33

def z184 : W := mkw 0x8d3b600036ce4000 0x08d3b600036ce400 0x3e3f60003f0f000a 0xe3e3f60003f0f000

def z185 : W := mkw 0x0010000010800000 0x0001000001080000 0x1030000018800009 0xa103000001880000

def z186 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1ce993920701c07 0x7e1ce993920701c0

def z187 : W := mkw 0x161b366e7b8f75db 0x4161b366e7b8f75d 0x7e0f1e3e3f8ffffe 0xf7e0f1e3e3f8ffff

def z188 : W := mkw 0x2b3016c01dd03b0c 0x02b3016c01dd03b0 0x3e3006c03ff03f08 0x83e3006c03ff03f0

def z189 : W := mkw 0x9012220a3feff4c3 0x09012220a3feff4c 0x300000003ffffcc8 0x0300000003ffffcc

def z190 : W := mkw 0x1012224a7b8f75db 0x41012224a7b8f75d 0x300000003f8ffff8 0x0300000003f8ffff

def z191 : W := mkw 0x3f7b1fec3fdc3f8e 0x03f7b1fec3fdc3f8 0xbffe1ff83ff03f0d 0xfbffe1ff83ff03f0

def z192 : W := mkw 0x297029c054d24b1c 0x4297029c054d24b1 0x81f0e1c1c0f0c331 0x081f0e1c1c0f0c33

def z193 : W := mkw 0x0b601d8000000000 0x00b601d800000000 0x8fc0180000000000 0x58fc018000000000

def z194 : W := mkw 0x0dadc00000000000 0x00dadc0000000000 0x8fffe00000000003 0xe8fffe0000000000

def z195 : W := mkw 0x0010224258836159 0x4001022425883615 0x1031e000188fe3fb 0xa1031e000188fe3f

def z196 : W := mkw 0x3f7b3fee7fdf7fdf 0x43f7b3fee7fdf7fd 0xffffffffffffffff 0xffffffffffffffff

def z197 : W := mkw 0x2bf69fc03df8bb0c 0x02bf69fc03df8bb0 0xbffe9fc03ff8ff0f 0xfbffe9fc03ff8ff0

def z198 : W := mkw 0x9fbff66e7feff5db 0x49fbff66e7feff5d 0xffffffffffffffff 0xffffffffffffffff

def z199 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e3fffffff0f3ccf 0xf7e3fffffff0f3cc

def z200 : W := mkw 0x4fadd4b580000000 0x04fadd4b58000000 0x4e3fe6ffc0000002 0x84e3fe6ffc000000

def z201 : W := mkw 0x0010224258836159 0x4001022425883615 0x50008101188fe3ff 0x250008101188fe3f

def z202 : W := mkw 0x4ffddff598802108 0x04ffddff59880210 0xdfffffffd880230f 0xfdfffffffd880230

def z203 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1ce193920703ff4 0x5e1ce193920703ff

def z204 : W := mkw 0x09f6891934f88ea2 0x809f6891934f88ea 0xfffe99393ff8ffff 0xffffe99393ff8fff

def z205 : W := mkw 0x8dbfe00276efc051 0x48dbfe00276efc05 0xffffe007ffffc0fb 0xeffffe007ffffc0f

def z206 : W := mkw 0x8dbfc00036ec8000 0x08dbfc00036ec800 0xbffe00003ff00009 0xebffe00003ff0000

def z207 : W := mkw 0x8d3962425ec76159 0x48d3962425ec7615 0x1e3166c6df070000 0x81e3166c6df07000

def z208 : W := mkw 0x0002000020288000 0x0000200002028800 0x2000000020f8c008 0x02000000020f8c00

def z209 : W := mkw 0x0010200010824000 0x0001020001082400 0x5031e7c7d88fc00f 0xa5031e7c7d88fc00

def z210 : W := mkw 0x2b701fc21dd13b4d 0x02b701fc21dd13b4 0xfff11fc63fff3fcf 0xffff11fc63fff3fc

def z211 : W := mkw 0x16cf9d3d233c9ea2 0x816cf9d3d233c9ea 0xefce993927f8ffff 0x7efce993927f8fff

def z212 : W := mkw 0x0dadc00000000000 0x00dadc0000000000 0x8fce000000000000 0x48fce00000000000

def z213 : W := mkw 0x2b3036c25dc3715d 0x42b3036c25dc3715 0x5e31e7c7df8fe3ff 0xa5e31e7c7df8fe3f

def z214 : W := mkw 0x1609162e0b0534c3 0x01609162e0b0534c 0x5e011e3e1f073cc4 0x95e011e3e1f073cc

def z215 : W := mkw 0x848fe002622fc051 0x4848fe002622fc05 0x400fe007c00fc0f2 0x0400fe007c00fc0f

def z216 : W := mkw 0x161936665b877159 0x4161936665b87715 0x5e31e7c7df8fe3ff 0xa5e31e7c7df8fe3f

def z217 : W := mkw 0x0409000002040000 0x0040900000204000 0x1e0100001f070000 0x81e0100001f07000

def z218 : W := mkw 0x22503fc259937b5d 0x422503fc259937b5 0x5031ffc7d88fffff 0xb5031ffc7d88ffff

def z219 : W := mkw 0x00d4a95150b2cb38 0xc00d4a95150b2cb3 0x81f0e1c1c0f0c331 0x081f0e1c1c0f0c33

def z220 : W := mkw 0x00500b4018902b08 0x000500b4018902b0 0xb1f01fc038f03f0d 0xfb1f01fc038f03f0

def z221 : W := mkw 0x448dc03580000000 0x0448dc0358000000 0x403fe7ffc0000007 0xa403fe7ffc000000

def z222 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xa1ce183820f8fff8 0x5a1ce183820f8fff

def z223 : W := mkw 0x160916260b053041 0x0160916260b05304 0x3e011e063f073c0c 0xf3e011e063f073c0

def z224 : W := mkw 0x49e6c999a0388ea2 0x849e6c999a0388ea 0xe1fef9f9e0f8ffff 0x7e1fef9f9e0f8fff

def z225 : W := mkw 0x00868019202884a2 0x800868019202884a 0x000e003800000000 0x0000e00380000000

def z226 : W := mkw 0x0be69d9920388ea2 0x80be69d9920388ea 0xeffe9ff920f8ffff 0xfeffe9ff920f8fff

def z227 : W := mkw 0x42c69dbda0388ea2 0x842c69dbda0388ea 0xe1ce9fffe0f8ffff 0x7e1ce9fffe0f8fff

def z228 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xafc0190027f03f0d 0x7afc0190027f03f0

def z229 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xffffe7c7ffffc00f 0xeffffe7c7ffffc00

def z230 : W := mkw 0x448de037c0034051 0x4448de037c003405 0x400fe03fc00fc0f2 0x0400fe03fc00fc0f

def z231 : W := mkw 0x141b226e7a8f65db 0x4141b226e7a8f65d 0x503fe7ffd88fe3ff 0xa503fe7ffd88fe3f

def z232 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x400f1e3e000f3cc6 0x1400f1e3e000f3cc

def z233 : W := mkw 0xc48fe035a22ec000 0x0c48fe035a22ec00 0x400fe03fc00fc002 0x0400fe03fc00fc00

def z234 : W := mkw 0x8dffeb5b7effeffb 0xc8dffeb5b7effeff 0xffffffffffffffff 0xffffffffffffffff

def z235 : W := mkw 0x0970090014d00a00 0x00970090014d00a0 0xbff019003ff03f0d 0xfbff019003ff03f0

def z236 : W := mkw 0x040b0000220c0000 0x0040b0000220c000 0x000f0000000f0002 0x0000f0000000f000

def z237 : W := mkw 0x0dafc000220c0000 0x00dafc000220c000 0xbfffe0003f0f000b 0xebfffe0003f0f000

def z238 : W := mkw 0x00020000220c0000 0x000020000220c000 0x300000003f0f0008 0x0300000003f0f000

def z239 : W := mkw 0x361b166e3fdd3fcf 0x0361b166e3fdd3fc 0x7e0f1e3e3fff3fce 0xf7e0f1e3e3fff3fc

def z240 : W := mkw 0x00d6a91930bacea2 0x800d6a91930bacea 0xf1fff93938ffffff 0xff1fff93938fffff

def z241 : W := mkw 0x948fe02e222fc4c3 0x0948fe02e222fc4c 0x400fe03e000fc0c2 0x0400fe03e000fc0c

def z242 : W := mkw 0x0010224258836159 0x4001022425883615 0x5001e007d88fe3fa 0x05001e007d88fe3f

def z243 : W := mkw 0x0010200010824000 0x0001020001082400 0x1031600018070000 0x8103160001807000

def z244 : W := mkw 0x6ffdfff7ddd37b5d 0x46ffdfff7ddd37b5 0xffffffffffffffff 0xffffffffffffffff

def z245 : W := mkw 0x3f7b1fee3fdd3fcf 0x03f7b1fee3fdd3fc 0xffff1ffe3fff3fcf 0xfffff1ffe3fff3fc

def z246 : W := mkw 0x89f6e91934facea2 0x889f6e91934facea 0xe1fef93920f8ffff 0x7e1fef93920f8fff

def z247 : W := mkw 0x1609162e090134c3 0x01609162e090134c 0x4e0f1e3e00003cc6 0xf4e0f1e3e00003cc

def z248 : W := mkw 0x00c4891100000000 0x000c489110000000 0x81c0810100000001 0x081c081010000000

def z249 : W := mkw 0x0409000000000000 0x0040900000000000 0x0e0f000000000002 0xe0e0f00000000000

def z250 : W := mkw 0x8fbff42436eec000 0x08fbff42436eec00 0xfffffe3e3fffc00f 0xffffffe3e3fffc00

def z251 : W := mkw 0x160b142e220d04c3 0x0160b142e220d04c 0x4e0f1e3e000f00c6 0xf4e0f1e3e000f00c

def z252 : W := mkw 0x0000220248036051 0x4000022024803605 0x5001e607d80fe0fe 0xa5001e607d80fe0f

def z253 : W := mkw 0x293002401dd03b0c 0x0293002401dd03b0 0xbff000003ff03f09 0xebff000003ff03f0

def z254 : W := mkw 0x0000000000308a20 0x80000000000308a2 0x0000000000f0c330 0x00000000000f0c33

def z255 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfffffffc088e3ff 0xfcfffffffc088e3f

def z256 : W := mkw 0x00868019202884a2 0x800868019202884a 0x400e81390088e3ff 0x2400e81390088e3f

def z257 : W := mkw 0x0002000820080482 0x0000200082008048 0x400e0038000800c2 0x0400e0038000800c

def z258 : W := mkw 0x02401f0009103a00 0x002401f0009103a0 0xbfc01f003ff03f0d 0xfbfc01f003ff03f0

def z259 : W := mkw 0x293000c014c0010c 0x0293000c014c0010 0x003000c000000000 0x0003000c00000000

def z260 : W := mkw 0x2bf49fd11dd03b0c 0x02bf49fd11dd03b0 0xfffe9ff93ff03f0f 0xffffe9ff93ff03f0

def z261 : W := mkw 0x5f2b56aeab0d34c3 0x05f2b56aeab0d34c 0x7e3f7efeff0f3cce 0xf7e3f7efeff0f3cc

def z262 : W := mkw 0x0084801100000000 0x0008480110000000 0x400e803900000002 0x0400e80390000000

def z263 : W := mkw 0x0084800000000000 0x0008480000000000 0x81ce800000000003 0x681ce80000000000

def z264 : W := mkw 0x8012200836fecea2 0x88012200836fecea 0x300000003ffffff8 0x0300000003ffffff

def z265 : W := mkw 0x0200160009003000 0x0020016000900300 0x1e0006001f000000 0x81e0006001f00000

def z266 : W := mkw 0x84cfe919223ecea2 0x884cfe919223ecea 0xe1cff93920ffffff 0x7e1cff93920fffff

def z267 : W := mkw 0x00d6ab5b78bbeffb 0xc00d6ab5b78bbeff 0xf1fffffff8ffffff 0xff1fffffff8fffff

def z268 : W := mkw 0x201022425dd37b5d 0x4201022425dd37b5 0x300000003ffffff8 0x0300000003ffffff

def z269 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xa1ce983820f8dc0b 0x7a1ce983820f8dc0

def z270 : W := mkw 0x00d4ab5358836159 0x400d4ab535883615 0xd1ffffffd88fe3ff 0xfd1ffffffd88fe3f

def z271 : W := mkw 0x8932200036eec000 0x08932200036eec00 0xbff000003fffc009 0xebff000003fffc00

def z272 : W := mkw 0x0012224a78bbeffb 0xc0012224a78bbeff 0x3000000038fffff8 0x03000000038fffff

def z273 : W := mkw 0x0002000820080482 0x0000200082008048 0x200e183820001c00 0x5200e183820001c0

def z274 : W := mkw 0x0dafc00020288000 0x00dafc0002028800 0xafffe00020f8c00b 0xeafffe00020f8c00

def z275 : W := mkw 0xcffffdbdb6fecea2 0x8cffffdbdb6fecea 0xffffffffffffffff 0xffffffffffffffff

def z276 : W := mkw 0x5fefddbfa20d04c3 0x05fefddbfa20d04c 0xcfffffffc00f00c7 0xfcfffffffc00f00c

def z277 : W := mkw 0x0040090000100a00 0x00040090000100a0 0x81c0010000f00301 0x081c0010000f0030

def z278 : W := mkw 0x468dd43580000000 0x0468dd4358000000 0x4e0ffe3fc0000006 0xf4e0ffe3fc000000

def z279 : W := mkw 0x140b022e2a0d24c3 0x0140b022e2a0d24c 0x500f063e180f20ce 0xa500f063e180f20c

def z280 : W := mkw 0x3f3b16ee3fcd35cf 0x03f3b16ee3fcd35c 0x7e3f1efe3f0f3cce 0xf7e3f1efe3f0f3cc

def z281 : W := mkw 0x4084c01180000000 0x04084c0118000000 0x0000e001c0000000 0x00000e001c000000

def z282 : W := mkw 0x0000000000000000 0x0000000000000000 0x003166c6c0000000 0x8003166c6c000000

def z283 : W := mkw 0x2960098004500a04 0x02960098004500a0 0x81c0000000700000 0x081c000000070000

def z284 : W := mkw 0x168f963f2b2db4e3 0x8168f963f2b2db4e 0x7e0f9e3f3f0ffcfe 0xf7e0f9e3f3f0ffcf

def z285 : W := mkw 0x00c68919202884a2 0x800c68919202884a 0xc1ce99390008c0f7 0x7c1ce99390008c0f

def z286 : W := mkw 0x0000000000000000 0x0000000000000000 0x000081010080c331 0x0000081010080c33

def z287 : W := mkw 0x2b20148005401004 0x02b2014800540100 0x0e00000007000000 0x00e0000000700000

def z288 : W := mkw 0x3fff9fff3ffdbfef 0x83fff9fff3ffdbfe 0xffff9fff3fffffff 0xfffff9fff3ffffff

def z289 : W := mkw 0x548fc03fa20d04c3 0x0548fc03fa20d04c 0x400fe03fc00f00c2 0x0400fe03fc00f00c

def z290 : W := mkw 0x06cd9d3500000000 0x006cd9d350000000 0xcfcf9f3f00000007 0xfcfcf9f3f0000000

def z291 : W := mkw 0x0000224248036159 0x4000022424803615 0x4001e7c7c00fe3f6 0x04001e7c7c00fe3f

def z292 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xaffee00027f0c001 0x4affee00027f0c00

def z293 : W := mkw 0x4feddfb589003000 0x04feddfb58900300 0xffffffffff003c0f 0xfffffffffff003c0

def z294 : W := mkw 0x841b200036eec000 0x0841b200036eec00 0x3e0f00003fffc00a 0xe3e0f00003fffc00

def z295 : W := mkw 0xafffdfc03ffcbb0c 0x0afffdfc03ffcbb0 0xbffe1fc03ff03f0d 0xfbffe1fc03ff03f0

def z296 : W := mkw 0x8d3b600036eec000 0x08d3b600036eec00 0x3e3160003fffc008 0x83e3160003fffc00

def z297 : W := mkw 0x4fefddbda0388ea2 0x84fefddbda0388ea 0xafce183820701c00 0x5afce183820701c0

def z298 : W := mkw 0x093022425cc36159 0x4093022425cc3615 0xfff1e7c7ffffe3ff 0xefff1e7c7ffffe3f

def z299 : W := mkw 0x0002000820080482 0x0000200082008048 0x2000000020083cc8 0x02000000020083cc

def z300 : W := mkw 0x140b002e220d04c3 0x0140b002e220d04c 0x600f183e200f3cce 0x7600f183e200f3cc

def z301 : W := mkw 0x0040091900100ea2 0x80040091900100ea 0x400099390088ffff 0x3400099390088fff

def z302 : W := mkw 0x0b701d8014c00000 0x00b701d8014c0000 0xbff01fc03ff0000d 0xfbff01fc03ff0000

def z303 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0x8fff7efec0000000 0xd8fff7efec000000

def z304 : W := mkw 0x0000004040000118 0x4000000404000011 0x000001c1c0000330 0x0000001c1c000033

def z305 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xbff01fc03ffffffd 0xfbff01fc03ffffff

def z306 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0x1e301fc01f003f04 0x91e301fc01f003f0

def z307 : W := mkw 0x2f7b1fc03fdc3b0c 0x02f7b1fc03fdc3b0 0xbfff1fc03fff3f0f 0xfbfff1fc03fff3f0

def z308 : W := mkw 0x2b703fc01dd27b0c 0x02b703fc01dd27b0 0xbff1ffc03fffff0f 0xfbff1ffc03fffff0

def z309 : W := mkw 0x8096a00036eec000 0x08096a00036eec00 0xb1ce80003fffc00b 0x6b1ce80003fffc00

def z310 : W := mkw 0x89b6e00036eec000 0x089b6e00036eec00 0xb1f0e0003fffc009 0x0b1f0e0003fffc00

def z311 : W := mkw 0x0010224258836159 0x4001022425883615 0x1000000018070000 0x0100000001807000

def z312 : W := mkw 0xeffffff5bffefb0c 0x0effffff5bffefb0 0xffffffffffffff0f 0xfffffffffffffff0

def z313 : W := mkw 0x1202162e2b0d34c3 0x01202162e2b0d34c 0x70001e3e3f0f3ccc 0x170001e3e3f0f3cc

def z314 : W := mkw 0x0010224018826108 0x0001022401882610 0x1031e7c0188fe30f 0xa1031e7c0188fe30

def z315 : W := mkw 0x4ffdfff7d8836159 0x44ffdfff7d883615 0xdfffffffd88fe3ff 0xfdfffffffd88fe3f

def z316 : W := mkw 0xbfffffee3fffffcf 0x0bfffffee3fffffc 0xfffffffe3fffffcf 0xffffffffe3fffffc

def z317 : W := mkw 0x0fadd42400000000 0x00fadd4240000000 0xcffffe3e00000007 0xfcffffe3e0000000

def z318 : W := mkw 0x0010024258812159 0x4001002425881215 0x503007c7d88023fd 0xa503007c7d88023f

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000810100000007 0x2400081010000000

def z320 : W := mkw 0x0010200010824000 0x0001020001082400 0x5031e101188fe3ff 0xa5031e101188fe3f

def z321 : W := mkw 0x04cf8919223c8ea2 0x804cf8919223c8ea 0xffcf99393fffffff 0xfffcf99393ffffff

def z322 : W := mkw 0x1200162e090134c3 0x01200162e090134c 0x7e001e3e3f003ccc 0xf7e001e3e3f003cc

def z323 : W := mkw 0x2bf69fd93df8bfae 0x82bf69fd93df8bfa 0xbffe1ff83ff03f0d 0xfbffe1ff83ff03f0

def z324 : W := mkw 0x848fc000222c8000 0x0848fc000222c800 0x000e000000000000 0x0000e00000000000

def z325 : W := mkw 0x0930200014c24000 0x00930200014c2400 0xbff1e0003fffc00b 0xebff1e0003fffc00

def z326 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0x8ffe1ff800000005 0xf8ffe1ff80000000

def z327 : W := mkw 0x62401ff589103b0c 0x062401ff589103b0 0x40001fffc0003f04 0x140001fffc0003f0

def z328 : W := mkw 0x29f489d114f08b2c 0x829f489d114f08b2 0x81f081c100f0c331 0x081f081c100f0c33

def z329 : W := mkw 0xafbff6c03feef10c 0x0afbff6c03feef10 0xbfffe6c03fffc00b 0xebfffe6c03fffc00

def z330 : W := mkw 0x1002020a2b0d34c3 0x01002020a2b0d34c 0x700e18383f0f3cce 0x7700e18383f0f3cc

def z331 : W := mkw 0x4f695db580000000 0x04f695db58000000 0x4e317fffc0000004 0x94e317fffc000000

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0x000001000080230d 0x2000001000080230

def z333 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfff60003f770000 0xcbfff60003f77000

def z334 : W := mkw 0x00d6ab5b78bbeffb 0xc00d6ab5b78bbeff 0xf1ce993938ffffff 0x7f1ce993938fffff

def z335 : W := mkw 0x0040090000000000 0x0004009000000000 0x81c0190000000005 0x781c019000000000

def z336 : W := mkw 0x8dffe90036feca00 0x08dffe90036feca0 0xbffff9003fffff0f 0xfbffff9003fffff0

def z337 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x3e0106063f0f3cc8 0x83e0106063f0f3cc

def z338 : W := mkw 0x3b721fca3fdd3fcf 0x03b721fca3fdd3fc 0xbff01fc03fff3fcd 0xfbff01fc03fff3fc

def z339 : W := mkw 0x0000000800100ea2 0x80000000800100ea 0x0000000000003ff0 0x00000000000003ff

def z340 : W := mkw 0x0d3b000036cc0000 0x00d3b000036cc000 0xbfff00003fff000b 0xebfff00003fff000

def z341 : W := mkw 0x0609142400000000 0x0060914240000000 0x4e3fffffc0000007 0xf4e3fffffc000000

def z342 : W := mkw 0x0010224258836159 0x4001022425883615 0x5031e6c7d80fc0f2 0x85031e6c7d80fc0f

def z343 : W := mkw 0x46cdddb580000000 0x046cdddb58000000 0x400fffffc0000006 0x1400fffffc000000

def z344 : W := mkw 0x00c68b1b2839aee3 0x800c68b1b2839aee 0xf1cf9f3f38ffffff 0xff1cf9f3f38fffff

def z345 : W := mkw 0x0096a24278abe159 0x40096a24278abe15 0xf1ffe7c7f8ffe3ff 0xef1ffe7c7f8ffe3f

def z346 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0x400e99390008fff6 0x1400e99390008fff

def z347 : W := mkw 0x4b601db580000000 0x04b601db58000000 0xcff01fffc0000005 0xfcff01fffc000000

def z348 : W := mkw 0x201022425dd37b5d 0x4201022425dd37b5 0x7031e7c7ffffffff 0xa7031e7c7fffffff

def z349 : W := mkw 0x0000024248012159 0x4000002424801215 0x000006c6c0000000 0x0000006c6c000000

def z350 : W := mkw 0x0010224258836159 0x4001022425883615 0x103166c6d88fe3f8 0x8103166c6d88fe3f

def z351 : W := mkw 0x140b020a2b0d34c3 0x0140b020a2b0d34c 0x3e0f00003f0f3cca 0xe3e0f00003f0f3cc

def z352 : W := mkw 0x0000200000024000 0x0000020000002400 0x0001e000000fc002 0x00001e000000fc00

def z353 : W := mkw 0x4fefddbda0080482 0x04fefddbda008048 0xefffffffe0083ccf 0xfefffffffe0083cc

def z354 : W := mkw 0x8dffe91136eec000 0x08dffe91136eec00 0xfffff9393fffc00f 0xffffff9393fffc00

def z355 : W := mkw 0x49e4c99180000000 0x049e4c9918000000 0x81c0000000000000 0x081c000000000000

def z356 : W := mkw 0x0000000240010051 0x4000000024001005 0x40000007c00000f0 0x040000007c00000f

def z357 : W := mkw 0x4f2954a480000000 0x04f2954a48000000 0x4e31e7c7c0000007 0xa4e31e7c7c000000

def z358 : W := mkw 0x9fafd62e2f6db4c3 0x09fafd62e2f6db4c 0xffcf1e3e3f7f3cce 0xfffcf1e3e3f7f3cc

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0x4031e7c7c088e3ff 0xa4031e7c7c088e3f

def z360 : W := mkw 0x968ff62e2b2ff4c3 0x0968ff62e2b2ff4c 0x7e0ffe3e3f0ffcce 0xf7e0ffe3e3f0ffcc

def z361 : W := mkw 0xcffdfdb596c64000 0x0cffdfdb596c6400 0xdfffffffdf070007 0xfdfffffffdf07000

def z362 : W := mkw 0x02c69f192938bea2 0x802c69f192938bea 0xffce9f393ff8ffff 0xfffce9f393ff8fff

def z363 : W := mkw 0x5f2956a68b053041 0x05f2956a68b05304 0x1e3166c6df070000 0x81e3166c6df07000

def z364 : W := mkw 0x4f3976e6d8836159 0x44f3976e6d883615 0x5e31e7c7d88fe3ff 0xa5e31e7c7d88fe3f

def z365 : W := mkw 0x848fe019222ec4a2 0x8848fe019222ec4a 0x400fe039000fc0f2 0x0400fe039000fc0f

def z366 : W := mkw 0x564b1fbfab0d34c3 0x0564b1fbfab0d34c 0x7e0f1fffff0f3cce 0xf7e0f1fffff0f3cc

def z367 : W := mkw 0x8dffe91136feca20 0x88dffe91136feca2 0xbfffe1013fffc33b 0xebfffe1013fffc33

def z368 : W := mkw 0x44cdc93580000000 0x044cdc9358000000 0xc1cff93fc0000007 0x7c1cff93fc000000

def z369 : W := mkw 0x0010220218836041 0x0001022021883604 0x5031e606188fe0cf 0xa5031e606188fe0c

def z370 : W := mkw 0x568fd63fab0d34c3 0x0568fd63fab0d34c 0x7e0ffe3fff0f3cce 0xf7e0ffe3fff0f3cc

def z371 : W := mkw 0x00c4891100000000 0x000c489110000000 0x81ce183800000000 0x581ce18380000000

def z372 : W := mkw 0x2b3016c01dc0310c 0x02b3016c01dc0310 0xbff006c03ff00009 0xebff006c03ff0000

def z373 : W := mkw 0x0086800020288000 0x0008680002028800 0xa1ce000020700000 0x4a1ce00002070000

def z374 : W := mkw 0x6ffddff59dd03b0c 0x06ffddff59dd03b0 0xbffe1ff83ff03f0d 0xfbffe1ff83ff03f0

def z375 : W := mkw 0x00d68b5938b8afaa 0x800d68b5938b8afa 0xf1fe9ff938f8ffff 0xff1fe9ff938f8fff

def z376 : W := mkw 0x0010224258836159 0x4001022425883615 0x503166c6d80f20ce 0xa503166c6d80f20c

def z377 : W := mkw 0x0930000014c00000 0x00930000014c0000 0x81f0000000f00001 0x081f0000000f0000

def z378 : W := mkw 0x8dbfe2427eefe159 0x48dbfe2427eefe15 0xbfffe6c6ffffc00b 0xebfffe6c6ffffc00

def z379 : W := mkw 0x0d29400000000000 0x00d2940000000000 0x0e31600000000000 0x80e3160000000000

def z380 : W := mkw 0x221016401dd03b0c 0x0221016401dd03b0 0x3e001e003ff03f0c 0xf3e001e003ff03f0

def z381 : W := mkw 0xcdbfe035b6eec000 0x0cdbfe035b6eec00 0xffffe03fffffc00b 0xeffffe03fffffc00

def z382 : W := mkw 0x4fefddbda02884a2 0x84fefddbda02884a 0xcfffffffc008c0f7 0xfcfffffffc008c0f

def z383 : W := mkw 0x00000019000004a2 0x800000019000004a 0x40000039000000f0 0x040000039000000f

def z384 : W := mkw 0x2b701dc015d01b0c 0x02b701dc015d01b0 0xaff019c027f01f01 0x5aff019c027f01f0

def z385 : W := mkw 0x0200142400000000 0x0020014240000000 0x40001e3e00000004 0x140001e3e0000000

def z386 : W := mkw 0x2000024009103b0c 0x02000024009103b0 0x0000000000003f00 0x00000000000003f0

def z387 : W := mkw 0x0000000000100a00 0x00000000000100a0 0x2000000020f03f08 0x02000000020f03f0

def z388 : W := mkw 0x0002000820388ea2 0x80002000820388ea 0x6000810120f8ffff 0x26000810120f8fff

def z389 : W := mkw 0x2f791fe41dd03b0c 0x02f791fe41dd03b0 0xffff1ffe3ff03f0f 0xfffff1ffe3ff03f0

def z390 : W := mkw 0x0609162409003000 0x0060916240900300 0x7e0f1e3e3f003c0e 0xf7e0f1e3e3f003c0

def z391 : W := mkw 0x0dbde24258836159 0x40dbde2425883615 0xdfffe7c7d88fe3ff 0xedfffe7c7d88fe3f

def z392 : W := mkw 0x4ffdfff7d8836159 0x44ffdfff7d883615 0xdfffffffd8070007 0xfdfffffffd807000

def z393 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x3e0e18383f0f3cc8 0x53e0e18383f0f3cc

def z394 : W := mkw 0x2b701d8015d01a04 0x02b701d8015d01a0 0xbff018003ff01c09 0xfbff018003ff01c0

def z395 : W := mkw 0x22501fc019903b0c 0x022501fc019903b0 0x10301fc018803f0d 0xb10301fc018803f0

def z396 : W := mkw 0x00868019202884a2 0x800868019202884a 0x600e98392008fcfe 0x7600e98392008fcf

def z397 : W := mkw 0x060b1424220c0000 0x0060b1424220c000 0x7e0f1e3e3f0f000e 0xf7e0f1e3e3f0f000

def z398 : W := mkw 0x16cf9d3d233c9ea2 0x816cf9d3d233c9ea 0xafce183827701c00 0x5afce183827701c0

def z399 : W := mkw 0x161936665b877159 0x4161936665b87715 0x1e3166c6df070000 0x81e3166c6df07000

def z400 : W := mkw 0xcffffff7feefe159 0x4cffffff7feefe15 0xffffffffffffe3ff 0xfffffffffffffe3f

def z401 : W := mkw 0x6fedddb585501a04 0x06fedddb585501a0 0xafce183827701c00 0x5afce183827701c0

def z402 : W := mkw 0x0609142400000000 0x0060914240000000 0x0e01060600000000 0x80e0106060000000

def z403 : W := mkw 0x0b601f8009003000 0x00b601f800900300 0xbff01fc03f003c0d 0xfbff01fc03f003c0

def z404 : W := mkw 0x0010004010800108 0x0001000401080010 0x003001c000800301 0x0003001c00080030

def z405 : W := mkw 0x89a4c00004608000 0x089a4c0000460800 0x81c0000000700000 0x081c000000070000

def z406 : W := mkw 0xcfbff4a4b6eec000 0x0cfbff4a4b6eec00 0xbfffe6c6ffffc00b 0xebfffe6c6ffffc00

def z407 : W := mkw 0x0042090820388ea2 0x80042090820388ea 0xa1c0190020f8fffd 0x7a1c0190020f8fff

def z408 : W := mkw 0xaf3976c01fc6710c 0x0af3976c01fc6710 0x1e3166c01f070000 0x81e3166c01f07000

def z409 : W := mkw 0x0042091920388ea2 0x80042091920388ea 0x6000193920f8fffc 0x16000193920f8fff

def z410 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xfff09fc13ff8ffff 0xffff09fc13ff8fff

def z411 : W := mkw 0x0b601d8000000000 0x00b601d800000000 0xcff1ffc7c0000007 0xfcff1ffc7c000000

def z412 : W := mkw 0x4409402480000000 0x0440940248000000 0x00016006c0000000 0x000016006c000000

def z413 : W := mkw 0x220016c00900310c 0x0220016c00900310 0x000006c000000000 0x0000006c00000000

def z414 : W := mkw 0x0b601d8000100a00 0x00b601d8000100a0 0xaff01fc020f03f0d 0xfaff01fc020f03f0

def z415 : W := mkw 0x0000024248012159 0x4000002424801215 0x400087c7c088e3ff 0x2400087c7c088e3f

def z416 : W := mkw 0x22401fc009103b0c 0x022401fc009103b0 0x3e001fc03f003f0c 0xf3e001fc03f003f0

def z417 : W := mkw 0x0000000000000000 0x0000000000000000 0x003007c000000005 0xa003007c00000000

def z418 : W := mkw 0x7fffdfffbfdd3fcf 0x07fffdfffbfdd3fc 0xffffffffffff3fcf 0xfffffffffffff3fc

def z419 : W := mkw 0x0dbde00010824000 0x00dbde0001082400 0x9fffe000188fc00b 0xe9fffe000188fc00

def z420 : W := mkw 0x3b701fee1dd13fcf 0x03b701fee1dd13fc 0xfff01ffe3ff03fcd 0xffff01ffe3ff03fc

def z421 : W := mkw 0x2ffddfc01dd03b0c 0x02ffddfc01dd03b0 0xbfffffc03ff03f0f 0xfbfffffc03ff03f0

def z422 : W := mkw 0x32401fee09113fcf 0x032401fee09113fc 0x40001ffe00003fc4 0x140001ffe00003fc

def z423 : W := mkw 0x5fefddbda30c1482 0x05fefddbda30c148 0xafce183827001c00 0x5afce183827001c0

def z424 : W := mkw 0x00c4891100308a20 0x800c4891100308a2 0x81c0000000700000 0x081c000000070000

def z425 : W := mkw 0x8dafe000222ec000 0x08dafe000222ec00 0x8fffe000000fc003 0xe8fffe000000fc00

def z426 : W := mkw 0x1fafd62e2b0d34c3 0x01fafd62e2b0d34c 0xfffffe3e3f0f3ccf 0xffffffe3e3f0f3cc

def z427 : W := mkw 0x0dedc91100000000 0x00dedc9110000000 0xcffff93900000007 0xfcffff9390000000

def z428 : W := mkw 0x0012224a788b65db 0x40012224a788b65d 0x703ffffff88fffff 0xf703ffffff88ffff

def z429 : W := mkw 0xaf797fc01fd67b0c 0x0af797fc01fd67b0 0xbff17fc03ff73f0d 0xfbff17fc03ff73f0

def z430 : W := mkw 0xa01222403ffefb0c 0x0a01222403ffefb0 0x300000003fffff08 0x0300000003fffff0

def z431 : W := mkw 0x0040090000100a00 0x00040090000100a0 0xe1c0990120f8ffff 0x7e1c0990120f8fff

def z432 : W := mkw 0x00d4ab5358b3eb79 0xc00d4ab5358b3eb7 0xd1f1e7c7d8ffe3ff 0xad1f1e7c7d8ffe3f

def z433 : W := mkw 0x4fedfdb7c0034051 0x44fedfdb7c003405 0xcfffffffc00fc0f7 0xfcfffffffc00fc0f

def z434 : W := mkw 0x49f4e9d1d0824118 0x449f4e9d1d082411 0x81f0e1c1c080c331 0x081f0e1c1c080c33

def z435 : W := mkw 0x0000024248012159 0x4000002424801215 0x00000000000023f0 0x000000000000023f

def z436 : W := mkw 0x4feddfb788012041 0x04feddfb78801204 0xdfffffffd80f20cf 0xfdfffffffd80f20c

def z437 : W := mkw 0x848fe000222ec000 0x0848fe000222ec00 0xa1cfe00020ffc00b 0x6a1cfe00020ffc00

def z438 : W := mkw 0x0200140001001000 0x0020014000100100 0x2e00180027001c00 0x52e00180027001c0

def z439 : W := mkw 0x100002020b053041 0x0100002020b05304 0x100000001f070000 0x0100000001f07000

def z440 : W := mkw 0x3f6b1dac275c1e86 0x03f6b1dac275c1e8 0xafce183827701c00 0x5afce183827701c0

def z441 : W := mkw 0x8dbfe00836eec482 0x08dbfe00836eec48 0xfffff8383ffffccf 0xffffff8383ffffcc

def z442 : W := mkw 0x8d29400006440000 0x08d2940000644000 0x0e00000007000000 0x00e0000000700000

def z443 : W := mkw 0x0000000000000000 0x0000000000000000 0x400007c7c0000004 0x0400007c7c000000

def z444 : W := mkw 0x297009c014d00b0c 0x0297009c014d00b0 0xa1f019c020f03f0d 0x7a1f019c020f03f0

def z445 : W := mkw 0x0000000000000000 0x0000000000000000 0xa1c0000020f00009 0x6a1c0000020f0000

def z446 : W := mkw 0x201002401dc0310c 0x0201002401dc0310 0x100000001f000000 0x0100000001f00000

def z447 : W := mkw 0x8084e0000022c000 0x08084e0000022c00 0x0000e0000000c000 0x00000e0000000c00

def z448 : W := mkw 0x160b142c230c1482 0x0160b142c230c148 0x3e0f18383f0f1c0a 0xf3e0f18383f0f1c0

def z449 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x5e0f063e1f0f00c2 0x85e0f063e1f0f00c

def z450 : W := mkw 0x0000000800000482 0x0000000080000048 0x4000183800003cc4 0x14000183800003cc

def z451 : W := mkw 0x0010204050824118 0x4001020405082411 0x4031e7c7c080c337 0xa4031e7c7c080c33

def z452 : W := mkw 0x2b701fc01dc0310c 0x02b701fc01dc0310 0x9ff01fc01f000005 0xf9ff01fc01f00000

def z453 : W := mkw 0x048dc00000000000 0x0048dc0000000000 0x000fe00000000002 0x0000fe0000000000

def z454 : W := mkw 0x0defc91920388ea2 0x80defc91920388ea 0xeffff93920f8ffff 0xfeffff93920f8fff

def z455 : W := mkw 0x4fefddbda0388ea2 0x84fefddbda0388ea 0xefffffffe0701c07 0xfefffffffe0701c0

def z456 : W := mkw 0x449de277d8836159 0x4449de277d883615 0x503fe7ffd88fe3ff 0xa503fe7ffd88fe3f

def z457 : W := mkw 0x0000000000000000 0x0000000000000000 0x000080000088c00b 0x2000080000088c00

def z458 : W := mkw 0x8930600014c24000 0x08930600014c2400 0x0030600000000000 0x0003060000000000

def z459 : W := mkw 0x4ffffffff8bbeffb 0xc4ffffffff8bbeff 0xfffffffff8ffffff 0xffffffffff8fffff

def z460 : W := mkw 0x2b721fc83df8bfae 0x82b721fc83df8bfa 0xbff01fc03ff8fffd 0xfbff01fc03ff8fff

def z461 : W := mkw 0x00c4891900308ea2 0x800c4891900308ea 0xc1c0993900f0fff5 0x1c1c0993900f0fff

def z462 : W := mkw 0x8dbfe2403eeee108 0x08dbfe2403eeee10 0xbfffe7c03fffe30f 0xebfffe7c03fffe30

def z463 : W := mkw 0x0010224258836159 0x4001022425883615 0x103007c0188fe3fd 0xa103007c0188fe3f

def z464 : W := mkw 0x160b142c230c1482 0x0160b142c230c148 0x6e0e183827083cce 0x76e0e183827083cc

def z465 : W := mkw 0x0000000000000000 0x0000000000000000 0x4001060600000006 0xa400106060000000

def z466 : W := mkw 0x00502b5b58936ffb 0xc00502b5b58936ff 0x5031ffffd88fffff 0xb5031ffffd88ffff

def z467 : W := mkw 0x8dbde00014e2c000 0x08dbde00014e2c00 0x8fffe00000f0c003 0xe8fffe00000f0c00

def z468 : W := mkw 0x093002401cc02108 0x0093002401cc0210 0xbff007c03ff0230d 0xebff007c03ff0230

def z469 : W := mkw 0x1002020a2b3dbee3 0x81002020a2b3dbee 0x300000003ffffff8 0x0300000003ffffff

def z470 : W := mkw 0x8409600002064000 0x0840960000206400 0x0001600000070000 0x0000160000007000

def z471 : W := mkw 0x9dbfe02e36efc4c3 0x09dbfe02e36efc4c 0xffffe03e3fffc0cb 0xeffffe03e3fffc0c

def z472 : W := mkw 0x0000020208012041 0x0000002020801204 0x5031e7c7d80f20cf 0xa5031e7c7d80f20c

def z473 : W := mkw 0x9dbfe20a3feff4c3 0x09dbfe20a3feff4c 0xbfffe0003ffffccb 0xebfffe0003ffffcc

def z474 : W := mkw 0x0002000820388ea2 0x80002000820388ea 0x2000000020701c00 0x02000000020701c0

def z475 : W := mkw 0x0200160209013041 0x0020016020901304 0x7e011e063f0f3cce 0xf7e011e063f0f3cc

def z476 : W := mkw 0x0084801100208020 0x8008480110020802 0x000080010000c030 0x0000080010000c03

def z477 : W := mkw 0x0010224058826118 0x4001022405882611 0x1030e7c1d880e33d 0xa1030e7c1d880e33

def z478 : W := mkw 0x5fefdfbfab0d34c3 0x05fefdfbfab0d34c 0xffcf1e3e3f0f3cce 0xfffcf1e3e3f0f3cc

def z479 : W := mkw 0x0012224a78bbeffb 0xc0012224a78bbeff 0x7031e7c7f8ffffff 0xa7031e7c7f8fffff

def z480 : W := mkw 0x06cf9d3d20388ea2 0x806cf9d3d20388ea 0xefcf9f3f20f8ffff 0xfefcf9f3f20f8fff

def z481 : W := mkw 0xcf3974a496c64000 0x0cf3974a496c6400 0x1e3166c6df070000 0x81e3166c6df07000

def z482 : W := mkw 0x42401ff7c8012159 0x442401ff7c801215 0x40001fffc00023f4 0x140001fffc00023f

def z483 : W := mkw 0x0040091100000000 0x0004009110000000 0x4000193900000004 0x1400019390000000

def z484 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x3e0f1e3e3f071c00 0xd3e0f1e3e3f071c0

def z485 : W := mkw 0x89b4e00014e2c000 0x089b4e00014e2c00 0x91f1e00018ffc00b 0xa91f1e00018ffc00

def z486 : W := mkw 0x0010024018802108 0x0001002401880210 0x1000000018802308 0x0100000001880230

def z487 : W := mkw 0x1202162e290934c3 0x01202162e290934c 0x600e1e3e20083cce 0x7600e1e3e20083cc

def z488 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfce00003fffc008 0x4bfce00003fffc00

def z489 : W := mkw 0xcdffe991b6eec000 0x0cdffe991b6eec00 0xbfffe1c1ffffc00b 0xebfffe1c1ffffc00

def z490 : W := mkw 0x0000024248012159 0x4000002424801215 0x500107c7d80f23fe 0xa500107c7d80f23f

def z491 : W := mkw 0x140b022e2b0d34c3 0x0140b022e2b0d34c 0x700f003e3f0f3cca 0x0700f003e3f0f3cc

def z492 : W := mkw 0x1000002e000104c3 0x01000002e000104c 0x4000003e000000c0 0x04000003e000000c

def z493 : W := mkw 0x8dbfe04076eec118 0x48dbfe04076eec11 0xbfffe1c1ffffc33b 0xebfffe1c1ffffc33

def z494 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfce1fffc0000004 0x5cfce1fffc000000

def z495 : W := mkw 0x49e4c99180000000 0x049e4c9918000000 0xc1fef9f9c0000007 0x7c1fef9f9c000000

def z496 : W := mkw 0x8dbfe00836fecea2 0x88dbfe00836fecea 0xbfffe0003ffffffb 0xebfffe0003ffffff

def z497 : W := mkw 0x89f4e91114f2ca20 0x889f4e91114f2ca2 0x81f0e10100f0c331 0x081f0e10100f0c33

def z498 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfcf1e3e00000006 0xfcfcf1e3e0000000

def z499 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xa1ce193820f03f0d 0x7a1ce193820f03f0

def z500 : W := mkw 0x0000200240034051 0x4000020024003405 0x00000000000fc0f0 0x000000000000fc0f

def z501 : W := mkw 0x42c49db580000000 0x042c49db58000000 0xc1ce9fffc0000007 0x7c1ce9fffc000000

def z502 : W := mkw 0x22501fc01dd03b0c 0x022501fc01dd03b0 0x30001fc03ff03f0c 0x130001fc03ff03f0

def z503 : W := mkw 0x2b3016c01dc0310c 0x02b3016c01dc0310 0x3e301ec03f003c0c 0xf3e301ec03f003c0

def z504 : W := mkw 0x140b002e220d04c3 0x0140b002e220d04c 0x7e0f003e3f0f00ca 0xe7e0f003e3f0f00c

def z505 : W := mkw 0x0010224258836159 0x4001022425883615 0x500007c7d88fe3fc 0x0500007c7d88fe3f

def z506 : W := mkw 0x0040091900100ea2 0x80040091900100ea 0x0000183800001c00 0x10000183800001c0

def z507 : W := mkw 0x89b4e04054e2c118 0x489b4e04054e2c11 0x81f0e1c1c0f0c331 0x081f0e1c1c0f0c33

def z508 : W := mkw 0x164b1f2e2b1d3ec3 0x0164b1f2e2b1d3ec 0xffcf1f3e3fff3fcf 0xfffcf1f3e3fff3fc

def z509 : W := mkw 0x6fffdffdbdf8bfae 0x86fffdffdbdf8bfa 0xfffffffffff8ffff 0xffffffffffff8fff

def z510 : W := mkw 0x00c6891120388a20 0x800c6891120388a2 0xa1ce810120f8c33b 0x6a1ce810120f8c33

def z511 : W := mkw 0x0000200040024010 0x4000020004002401 0x0000e001c000c030 0x00000e001c000c03

def z512 : W := mkw 0x160b162c2b0c3482 0x0160b162c2b0c348 0x3e0e1e383f003c0c 0xf3e0e1e383f003c0

def z513 : W := mkw 0x2b701fd91dd03fae 0x82b701fd91dd03fa 0xfff01ff93ff03ffd 0xffff01ff93ff03ff

def z514 : W := mkw 0x160916260b053041 0x0160916260b05304 0x5e0f1e3e1f070006 0xf5e0f1e3e1f07000

def z515 : W := mkw 0x4be4dd9180000000 0x04be4dd918000000 0x8ff0ffc1c0000005 0xf8ff0ffc1c000000

def z516 : W := mkw 0x4f3976e6d8836159 0x44f3976e6d883615 0x1e3166c6d8070000 0x81e3166c6d807000

def z517 : W := mkw 0x0086800820288482 0x0008680082028848 0xe1ce983820f8fccf 0x7e1ce983820f8fcc

def z518 : W := mkw 0x00c6a91b603bcef3 0xc00c6a91b603bcef 0xe1cff93fe0ffffff 0x7e1cff93fe0fffff

def z519 : W := mkw 0x10c68b1b2b3dbee3 0x810c68b1b2b3dbee 0xf1ce99393fffffff 0x7f1ce99393ffffff

def z520 : W := mkw 0x00c4891100100a00 0x000c4891100100a0 0xe1ce993920f03f0f 0x7e1ce993920f03f0

def z521 : W := mkw 0x448dc03580000000 0x0448dc0358000000 0x000e003800000000 0x0000e00380000000

def z522 : W := mkw 0x0010204050824118 0x4001020405082411 0x1031e1c1d88fc33b 0xa1031e1c1d88fc33

def z523 : W := mkw 0x8d39600016c64000 0x08d39600016c6400 0x1e31e0001f8fc00b 0xa1e31e0001f8fc00

def z524 : W := mkw 0x0000000000000000 0x0000000000000000 0x400e183800000006 0x7400e18380000000

def z525 : W := mkw 0x0000200240034051 0x4000020024003405 0x4001e107c08fe3ff 0x24001e107c08fe3f

def z526 : W := mkw 0x4fadd4a480000000 0x04fadd4a48000000 0x8fffe6c6c0000003 0xe8fffe6c6c000000

def z527 : W := mkw 0x0010224258836159 0x4001022425883615 0x50010606188fe3fe 0xa50010606188fe3f

def z528 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0x8ffef9f9c0000001 0x58ffef9f9c000000

def z529 : W := mkw 0x0002000020080000 0x0000200002008000 0x200e00002008000a 0x6200e00002008000

def z530 : W := mkw 0xadbfe2403ffefb0c 0x0adbfe2403ffefb0 0xbfffe0003fffff0b 0xebfffe0003fffff0

def z531 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000101000023f4 0x040000101000023f

def z532 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0x8ffff83800000003 0xf8ffff8380000000

def z533 : W := mkw 0x5feddfbf890134c3 0x05feddfbf890134c 0xcfffffffc0003cc7 0xfcfffffffc0003cc

def z534 : W := mkw 0x2be69d9925789ea6 0x82be69d9925789ea 0xefce993927f8ffff 0x7efce993927f8fff

def z535 : W := mkw 0x4feddff7c8012159 0x44feddff7c801215 0xcfffffffc00023f7 0xfcfffffffc00023f

def z536 : W := mkw 0x0040090000100a00 0x00040090000100a0 0x0000190000003f04 0x10000190000003f0

def z537 : W := mkw 0x0000000000000000 0x0000000000000000 0x3e0000003f000008 0xe3e0000003f00000

def z538 : W := mkw 0xcffdfdb594e2c000 0x0cffdfdb594e2c00 0xcfffffffc0f0c007 0xfcfffffffc0f0c00

def z539 : W := mkw 0x2b3016c01dc0310c 0x02b3016c01dc0310 0x1e3007c01f80230d 0xa1e3007c01f80230

def z540 : W := mkw 0x0feddd8000000000 0x00feddd800000000 0x8fffffc000000007 0xf8fffffc00000000

def z541 : W := mkw 0x0000000000000000 0x0000000000000000 0x10010000180f000a 0xa10010000180f000

def z542 : W := mkw 0x10020008230c1482 0x010020008230c148 0x2000000027001c00 0x02000000027001c0

def z543 : W := mkw 0x4be4ddb580000000 0x04be4ddb58000000 0xc1f0ffffc0000005 0x1c1f0ffffc000000

def z544 : W := mkw 0x1200166e490135db 0x41200166e490135d 0x40001fffc0003ff4 0x140001fffc0003ff

def z545 : W := mkw 0x2b3036c25dc3715d 0x42b3036c25dc3715 0x1e3166c6df070000 0x81e3166c6df07000

def z546 : W := mkw 0x4920408080000000 0x0492040808000000 0x003060c0c0000000 0x0003060c0c000000

def z547 : W := mkw 0x4fefddb5a0288000 0x04fefddb5a028800 0xefffffffe0f8c00f 0xfefffffffe0f8c00

def z548 : W := mkw 0x2b601fc009103b0c 0x02b601fc009103b0 0x8ff01fc000003f05 0xf8ff01fc000003f0

def z549 : W := mkw 0x8dafc000266c8000 0x08dafc000266c800 0xafffe00027700003 0xeafffe0002770000

def z550 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x6e0e1e3e27003cc4 0x56e0e1e3e27003cc

def z551 : W := mkw 0x0010224258836159 0x4001022425883615 0x1031e7c7d887c331 0x81031e7c7d887c33

def z552 : W := mkw 0x420014a480000000 0x0420014a48000000 0x000006c6c0000000 0x0000006c6c000000

def z553 : W := mkw 0x040b0000220c0000 0x0040b0000220c000 0x2e0e000027000000 0x42e0e00002700000

def z554 : W := mkw 0xadffe9c036fecb0c 0x0adffe9c036fecb0 0xbfffe1c03fffc30b 0xebfffe1c03fffc30

def z555 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfcff83fc0000002 0x5cfcff83fc000000

def z556 : W := mkw 0x42401db580000000 0x042401db58000000 0x0000183800000000 0x1000018380000000

def z557 : W := mkw 0x49e4c99180308a20 0x849e4c99180308a2 0x81f0e1c1c0f0c331 0x081f0e1c1c0f0c33

def z558 : W := mkw 0x0010200010824000 0x0001020001082400 0x10000000188fc008 0x010000000188fc00

def z559 : W := mkw 0x8dafc000266c8000 0x08dafc000266c800 0xafce800027f8c00b 0x6afce800027f8c00

def z560 : W := mkw 0x49e4c99180000000 0x049e4c9918000000 0xc1f1e7c7c0000007 0xac1f1e7c7c000000

def z561 : W := mkw 0x9fffff3f3ffffee3 0x89fffff3f3ffffee 0xffffff3f3fffffff 0xfffffff3f3ffffff

def z562 : W := mkw 0x22401fd909103fae 0x822401fd909103fa 0x40001ff900003ff4 0x140001ff900003ff

def z563 : W := mkw 0x8dbde00016c64000 0x08dbde00016c6400 0x9fffe0001f070003 0xe9fffe0001f07000

def z564 : W := mkw 0x00c4891900100ea2 0x800c4891900100ea 0xc1ce993900003ff7 0x7c1ce993900003ff

def z565 : W := mkw 0x849fe00032aec000 0x0849fe00032aec00 0x103fe000188fc00b 0xa103fe000188fc00

def z566 : W := mkw 0x0409002400000000 0x0040900240000000 0x400f003e00000002 0x0400f003e0000000

def z567 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000180020003c0c 0x72000180020003c0

def z568 : W := mkw 0x297009c014d00b0c 0x0297009c014d00b0 0xbff001c03ff00309 0xebff001c03ff0030

def z569 : W := mkw 0x3f791fe61fd53b4d 0x03f791fe61fd53b4 0xbff11fc63ff73f0d 0xfbff11fc63ff73f0

def z570 : W := mkw 0x0000020208012041 0x0000002020801204 0x1001060618070000 0x8100106061807000

def z571 : W := mkw 0x0010024018802108 0x0001002401880210 0x103006c018000000 0x8103006c01800000

def z572 : W := mkw 0x1409002602050041 0x0140900260205004 0x0001000600070000 0x0000100060007000

def z573 : W := mkw 0x89b4e2425ce3e159 0x489b4e2425ce3e15 0xd1f1e7c7d8ffe3ff 0xad1f1e7c7d8ffe3f

def z574 : W := mkw 0x69f4c9d194d00b0c 0x069f4c9d194d00b0 0x81f0e1c1c0f00301 0x081f0e1c1c0f0030

def z575 : W := mkw 0x0010200250834051 0x4001020025083405 0x5031e007d88fc0fb 0xa5031e007d88fc0f

def z576 : W := mkw 0x1200142c01001482 0x01200142c0100148 0x0000183800001c00 0x10000183800001c0

def z577 : W := mkw 0x0960098000000000 0x0096009800000000 0x81f001c000000001 0x081f001c00000000

def z578 : W := mkw 0x2010004014d00b0c 0x02010004014d00b0 0x0000000000f00300 0x00000000000f0030

def z579 : W := mkw 0x89b6e00034eac000 0x089b6e00034eac00 0xa1fee00020f8c00b 0x6a1fee00020f8c00

def z580 : W := mkw 0x5fefddbda30c1482 0x05fefddbda30c148 0xefffffffe7001c07 0xfefffffffe7001c0

def z581 : W := mkw 0x2bf49fd11df0bb2c 0x82bf49fd11df0bb2 0xbff09fc13ff0ff3d 0xfbff09fc13ff0ff3

def z582 : W := mkw 0x0010224258836159 0x4001022425883615 0x5031e7c7d8070007 0xa5031e7c7d807000

def z583 : W := mkw 0x0609142400000000 0x0060914240000000 0x0e0e183800000000 0x50e0e18380000000

def z584 : W := mkw 0x80d6a91936fecea2 0x880d6a91936fecea 0xf1ce99393fffffff 0x7f1ce99393ffffff

def z585 : W := mkw 0x5ffffffffb8f75db 0x45ffffffffb8f75d 0xffffffffff8fffff 0xfffffffffff8ffff

def z586 : W := mkw 0x2b701dc014d00b0c 0x02b701dc014d00b0 0x8ff01fc000f00305 0xf8ff01fc000f0030

def z587 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0x81ffe00000ffc003 0x081ffe00000ffc00

def z588 : W := mkw 0x29f689d934f88fae 0x829f689d934f88fa 0xe1fe99f920f8ffff 0x7e1fe99f920f8fff

def z589 : W := mkw 0x1609142403041000 0x0160914240304100 0x0e00000007000000 0x00e0000000700000

def z590 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1ce98392078dcf2 0x5e1ce98392078dcf

def z591 : W := mkw 0x0010224258836159 0x4001022425883615 0x103167c6d887230d 0xa103167c6d887230

def z592 : W := mkw 0x040b02022a0d2041 0x0040b02022a0d204 0x7e0f06063f0f20ce 0xe7e0f06063f0f20c

def z593 : W := mkw 0x6ffddff59dc0310c 0x06ffddff59dc0310 0xdfffffffdf000007 0xfdfffffffdf00000

def z594 : W := mkw 0x0010024218812149 0x0001002421881214 0x503107c6188f23cf 0xa503107c6188f23c

def z595 : W := mkw 0xc9f4e99194e2c000 0x0c9f4e99194e2c00 0x81f0e1c1c0f0c001 0x081f0e1c1c0f0c00

def z596 : W := mkw 0x9f3b762e3fcf74c3 0x09f3b762e3fcf74c 0x7e3f7e3e3f0f3cce 0xf7e3f7e3e3f0f3cc

def z597 : W := mkw 0x00c4891100000000 0x000c489110000000 0xc1ce99390088e3ff 0x7c1ce99390088e3f

def z598 : W := mkw 0x16cf9f3f2b0d34c3 0x016cf9f3f2b0d34c 0xffcf9f3f3f0f3ccf 0xfffcf9f3f3f0f3cc

def z599 : W := mkw 0x0210364259837159 0x4021036425983715 0x7e31ffc7ff8fffff 0xf7e31ffc7ff8ffff

def z600 : W := mkw 0x3f3916e61fc5314d 0x03f3916e61fc5314 0x1e3106c61f070000 0x81e3106c61f07000

def z601 : W := mkw 0x00502b4258936b59 0x400502b4258936b5 0xf1f1ffc7f8ffffff 0xff1f1ffc7f8fffff

def z602 : W := mkw 0x0086a01b602bc4f3 0xc0086a01b602bc4f 0x400fe03fc00fc0f2 0x0400fe03fc00fc0f

def z603 : W := mkw 0x9fafd42c276c9482 0x09fafd42c276c948 0xafce183827701c00 0x5afce183827701c0

def z604 : W := mkw 0x1202160a2b0d34c3 0x01202160a2b0d34c 0x3e001e003f0f3ccc 0xf3e001e003f0f3cc

def z605 : W := mkw 0x0010204250834159 0x4001020425083415 0x4031e1c7c08fc3f3 0x04031e1c7c08fc3f

def z606 : W := mkw 0x1200162609013041 0x0120016260901304 0x0000060600000000 0x0000006060000000

def z607 : W := mkw 0x52401fbf890134c3 0x052401fbf890134c 0x40001fffc0003cc4 0x140001fffc0003cc

def z608 : W := mkw 0x0010200010824000 0x0001020001082400 0x0030e0000080c001 0x00030e0000080c00

def z609 : W := mkw 0x29702bc25cd36b5d 0x429702bc25cd36b5 0xd1f1e7c7d8ffe3ff 0xad1f1e7c7d8ffe3f

def z610 : W := mkw 0x204009c000100b0c 0x0204009c000100b0 0x000001c000000300 0x0000001c00000030

def z611 : W := mkw 0x02401d8000000000 0x002401d800000000 0x00001fc000000004 0x100001fc00000000

def z612 : W := mkw 0x0084800000208000 0x0008480000020800 0x81c0800000f0c001 0x081c0800000f0c00

def z613 : W := mkw 0x8dbde00016e6c000 0x08dbde00016e6c00 0x9ff1e0001ff7c001 0x89ff1e0001ff7c00

def z614 : W := mkw 0x8d3962425ec76159 0x48d3962425ec7615 0x5e31e7c7df8fe3ff 0xa5e31e7c7df8fe3f

def z615 : W := mkw 0x160b362e6b0f74d3 0x4160b362e6b0f74d 0x7e0ffe3fff0ffcfe 0xf7e0ffe3fff0ffcf

def z616 : W := mkw 0x160b16262b0d3041 0x0160b16262b0d304 0x3e0f06063f0f000a 0xe3e0f06063f0f000

def z617 : W := mkw 0x8dbfe2427eefe159 0x48dbfe2427eefe15 0xbfffe0003fffe3fb 0xebfffe0003fffe3f

def z618 : W := mkw 0x168f962e2b2db4c3 0x0168f962e2b2db4c 0xffcf9e3e3ffffccf 0xfffcf9e3e3ffffcc

def z619 : W := mkw 0x0000200240034051 0x4000020024003405 0x00016006c0070000 0x000016006c007000

def z620 : W := mkw 0x0210164019803108 0x0021016401980310 0x3e301fc03f803f0d 0xf3e301fc03f803f0

def z621 : W := mkw 0x0002020a280924c3 0x00002020a280924c 0x700f1e3e380f3cce 0xf700f1e3e380f3cc

def z622 : W := mkw 0x0010204050824118 0x4001020405082411 0x003060c0c0000000 0x0003060c0c000000

def z623 : W := mkw 0x0000000200010041 0x0000000020001004 0x40010006000f00c2 0x040010006000f00c

def z624 : W := mkw 0x160b142e230d14c3 0x0160b142e230d14c 0x6e0f183e270f1cc2 0x56e0f183e270f1cc

def z625 : W := mkw 0x80020000266c8000 0x080020000266c800 0x2000000027700000 0x0200000002770000

def z626 : W := mkw 0x160b142c230c1482 0x0160b142c230c148 0x6e0f1e3e27001c06 0xf6e0f1e3e27001c0

def z627 : W := mkw 0x29700bc01dd03b0c 0x029700bc01dd03b0 0xb1f001c03ff03f09 0x0b1f001c03ff03f0

def z628 : W := mkw 0xcfefddb5a66c8000 0x0cfefddb5a66c800 0xafce183827700000 0x5afce18382770000

def z629 : W := mkw 0x801222427eefe159 0x4801222427eefe15 0x300000003fffe3f8 0x0300000003fffe3f

def z630 : W := mkw 0x20500b401dd03b0c 0x020500b401dd03b0 0xb1c019003ff03f0d 0x7b1c019003ff03f0

def z631 : W := mkw 0x0040091900100ea2 0x80040091900100ea 0xe1c0193920f03ffd 0x7e1c0193920f03ff

def z632 : W := mkw 0xcfeffdb5a22ec000 0x0cfeffdb5a22ec00 0xcfffffffc00fc007 0xfcfffffffc00fc00

def z633 : W := mkw 0x6f795fe49dd03b0c 0x06f795fe49dd03b0 0xbff17fc6fff03f0d 0xfbff17fc6fff03f0

def z634 : W := mkw 0x8defc919267c8ea2 0x88defc919267c8ea 0xafce183827701c00 0x5afce183827701c0

def z635 : W := mkw 0x0000020208012041 0x0000002020801204 0x50018707188fe3ff 0xa50018707188fe3f

def z636 : W := mkw 0x4fefddb5a20c0000 0x04fefddb5a20c000 0xffffffffff0f000f 0xfffffffffff0f000

def z637 : W := mkw 0x0010024018802108 0x0001002401880210 0x503087c11888e3ff 0xa503087c11888e3f

def z638 : W := mkw 0x89b4e00014e2c000 0x089b4e00014e2c00 0xbff0e0003ff0c009 0xebff0e0003ff0c00

def z639 : W := mkw 0x848fe000222ec000 0x0848fe000222ec00 0x3e0fe0003f0fc00a 0xe3e0fe0003f0fc00

def z640 : W := mkw 0x0920000000000000 0x0092000000000000 0x8ff0000000000001 0xe8ff000000000000

def z641 : W := mkw 0x09b6800034e88000 0x009b6800034e8800 0xbffe80003ff8c00b 0xebffe80003ff8c00

def z642 : W := mkw 0x0086800020288000 0x0008680002028800 0x000e80000008c002 0x0000e80000008c00

def z643 : W := mkw 0x6bf4dfd19dd03b0c 0x06bf4dfd19dd03b0 0xbff0ffc1fff03f0d 0xfbff0ffc1fff03f0

def z644 : W := mkw 0x161b166e3b8d35cb 0x0161b166e3b8d35c 0x7e3f1ffe3f8f3fcf 0xf7e3f1ffe3f8f3fc

def z645 : W := mkw 0x4f695da480000000 0x04f695da48000000 0x8ff17fc6c0000005 0xf8ff17fc6c000000

def z646 : W := mkw 0x00c4891100308a20 0x800c4891100308a2 0xc1ce993900f0c337 0x7c1ce993900f0c33

def z647 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0x81f01fc000f03f05 0x181f01fc000f03f0

def z648 : W := mkw 0x6ffdddf594d00b0c 0x06ffdddf594d00b0 0xcfffffffc0f00307 0xfcfffffffc0f0030

def z649 : W := mkw 0x00c68b5b6839affb 0xc00c68b5b6839aff 0xe1ce9fffe0f8ffff 0x7e1ce9fffe0f8fff

def z650 : W := mkw 0x849fe2427aafe159 0x4849fe2427aafe15 0x503fe7c7d88fe3ff 0xa503fe7c7d88fe3f

def z651 : W := mkw 0x00400b5b48112ffb 0xc00400b5b48112ff 0x40001fffc0003ff4 0x140001fffc0003ff

def z652 : W := mkw 0x0dadc00000000000 0x00dadc0000000000 0xcfffe7c7c0000007 0xecfffe7c7c000000

def z653 : W := mkw 0x0be49d9100000000 0x00be49d910000000 0xcffe9ff900000007 0xfcffe9ff90000000

def z654 : W := mkw 0x80022000222ec000 0x080022000222ec00 0x00000000000fc000 0x000000000000fc00

def z655 : W := mkw 0x201002401dd03b0c 0x0201002401dd03b0 0x303007c03ff03f0d 0xa303007c03ff03f0

def z656 : W := mkw 0x201202483df8bfae 0x8201202483df8bfa 0x300000003ff8fff8 0x0300000003ff8fff

def z657 : W := mkw 0x0096a25b78abe5fb 0xc0096a25b78abe5f 0x503fe7ffd88fe3ff 0xa503fe7ffd88fe3f

def z658 : W := mkw 0x42401dbd80100ea2 0x842401dbd80100ea 0x40001fffc0003ff4 0x140001fffc0003ff

def z659 : W := mkw 0x0f691da400000000 0x00f691da40000000 0xcfff1ffe00000007 0xfcfff1ffe0000000

def z660 : W := mkw 0xab723fc03ffefb0c 0x0ab723fc03ffefb0 0xbff01fc03fffff0d 0xfbff01fc03fffff0

def z661 : W := mkw 0x0000020008002000 0x0000002000800200 0x100006001800200c 0xa100006001800200

def z662 : W := mkw 0x00c4891100308a20 0x800c4891100308a2 0xc1c0810100f8e3ff 0x2c1c0810100f8e3f

def z663 : W := mkw 0x9fbff42c37eed482 0x09fbff42c37eed48 0xbffff8383fffdc0b 0xfbffff8383fffdc0

def z664 : W := mkw 0xa9f4e9c014f2cb0c 0x0a9f4e9c014f2cb0 0x81f0e1c000f0c301 0x081f0e1c000f0c30

def z665 : W := mkw 0x161b366e7b8f75db 0x4161b366e7b8f75d 0x7e3f7efeff0f3cce 0xf7e3f7efeff0f3cc

def z666 : W := mkw 0x14cf893f223d8ee3 0x814cf893f223d8ee 0xe1cf993f20ffffff 0x7e1cf993f20fffff

def z667 : W := mkw 0x0042091920180ea2 0x80042091920180ea 0x600e193920083ffe 0x7600e193920083ff

def z668 : W := mkw 0x4ffdfdf5d0824118 0x44ffdfdf5d082411 0xcfffffffc080c337 0xfcfffffffc080c33

def z669 : W := mkw 0x8dafe000266ec000 0x08dafe000266ec00 0xafcfe000277fc002 0x4afcfe000277fc00

def z670 : W := mkw 0x0200160009003000 0x0020016000900300 0x00001e0000003c04 0x100001e0000003c0

def z671 : W := mkw 0x140b202e620f44d3 0x4140b202e620f44d 0x400fe03fc00fc0f2 0x0400fe03fc00fc0f

def z672 : W := mkw 0x5feddfb78b053041 0x05feddfb78b05304 0xdfffffffdf070007 0xfdfffffffdf07000

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x400080010008c0f2 0x0400080010008c0f

def z674 : W := mkw 0x0010000014c00000 0x00010000014c0000 0x300000003ff00008 0x0300000003ff0000

def z675 : W := mkw 0x060b16002b0c3000 0x0060b16002b0c300 0x3e0f1e003f0f3c0e 0xf3e0f1e003f0f3c0

def z676 : W := mkw 0x0200140000000000 0x0020014000000000 0x0e001e0000000004 0xf0e001e000000000

def z677 : W := mkw 0xcffffdb5b6eec000 0x0cffffdb5b6eec00 0xbffff8383fffc00b 0xfbffff8383fffc00

def z678 : W := mkw 0x8dbfe2023eefe041 0x08dbfe2023eefe04 0xffffe6063fffe0cf 0xeffffe6063fffe0c

def z679 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xc1ce813900f8c3f3 0x0c1ce813900f8c3f

def z680 : W := mkw 0x4dadc03580000000 0x04dadc0358000000 0xcfffe03fc0000003 0xecfffe03fc000000

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000088e3f8 0x0000000000088e3f

def z682 : W := mkw 0x09a4c00000000000 0x009a4c0000000000 0x81f0e00000000001 0x081f0e0000000000

def z683 : W := mkw 0x8dffe91936fecea2 0x88dffe91936fecea 0xbffff8383fffdc0b 0xfbffff8383fffdc0

def z684 : W := mkw 0x4fefddbda0388ea2 0x84fefddbda0388ea 0xefce993920f8ffff 0x7efce993920f8fff

def z685 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfce993900000007 0x7cfce99390000000

def z686 : W := mkw 0x140b002c220c0482 0x0140b002c220c048 0x000e003800000000 0x0000e00380000000

def z687 : W := mkw 0x0000024008002108 0x0000002400800210 0x000007c000002304 0x0000007c00000230

def z688 : W := mkw 0x9fbff6263feff041 0x09fbff6263feff04 0xbfffe6063fffc00b 0xebfffe6063fffc00

def z689 : W := mkw 0x0010204050824118 0x4001020405082411 0x4030e1c1c088e3ff 0x24030e1c1c088e3f

def z690 : W := mkw 0x4ffdddb594c00000 0x04ffdddb594c0000 0xfffffffffff0000f 0xffffffffffff0000

def z691 : W := mkw 0x3012024a3fdd3fcf 0x03012024a3fdd3fc 0x300000003fff3fc8 0x0300000003fff3fc

def z692 : W := mkw 0x12c69f3f2939bee3 0x812c69f3f2939bee 0xe1ce9f3f20f8ffff 0x7e1ce9f3f20f8fff

def z693 : W := mkw 0x6feddff589103b0c 0x06feddff589103b0 0xcfffffffc0003f07 0xfcfffffffc0003f0

def z694 : W := mkw 0x00c6891120288000 0x000c689112028800 0xe1ce993920f8c00f 0x7e1ce993920f8c00

def z695 : W := mkw 0xdfffffbfbfeff4c3 0x0dfffffbfbfeff4c 0xfffffffffffffccf 0xffffffffffffffcc

def z696 : W := mkw 0x44cfc93da0388ea2 0x844cfc93da0388ea 0xe1cff93fe0f8ffff 0x7e1cff93fe0f8fff

def z697 : W := mkw 0x8fbff6003feef000 0x08fbff6003feef00 0xbffffe003ffffc0f 0xfbffffe003ffffc0

def z698 : W := mkw 0x4000003580000000 0x0400000358000000 0x4000003fc0000000 0x04000003fc000000

def z699 : W := mkw 0x0000024248012159 0x4000002424801215 0x4031e7c7c00023f7 0xa4031e7c7c00023f

def z700 : W := mkw 0x8010200014e2c000 0x08010200014e2c00 0x0000000000f0c000 0x00000000000f0c00

def z701 : W := mkw 0x1012224a7b8f75db 0x41012224a7b8f75d 0x7031e7c7ff8fffff 0xa7031e7c7ff8ffff

def z702 : W := mkw 0x4dedc99180000000 0x04dedc9918000000 0x8fffe1c1c0000003 0xe8fffe1c1c000000

def z703 : W := mkw 0x2be69d9925789ea6 0x82be69d9925789ea 0xafce183827701c00 0x5afce183827701c0

def z704 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000000820ce 0x240000000000820c

def z705 : W := mkw 0x8012200036eec000 0x08012200036eec00 0x3031e0003fffc00b 0xa3031e0003fffc00

def z706 : W := mkw 0x041b22427a8f6159 0x4041b22427a8f615 0x7e3fe7c7ff8fe3ff 0xe7e3fe7c7ff8fe3f

def z707 : W := mkw 0x09700b401cd02b08 0x009700b401cd02b0 0xbff01fc03ff03f0d 0xfbff01fc03ff03f0

def z708 : W := mkw 0x161b346c738e559a 0x4161b346c738e559 0x2e3ef9f9e780df31 0x52e3ef9f9e780df3

def z709 : W := mkw 0x0be49d9100000000 0x00be49d910000000 0xcfffffffc0000007 0xfcfffffffc000000

def z710 : W := mkw 0x0000200240034051 0x4000020024003405 0x4031e7c7c08fe3ff 0xa4031e7c7c08fe3f

def z711 : W := mkw 0x2b701fc25dd13b5d 0x42b701fc25dd13b5 0xfff11fc7ffff3fff 0xffff11fc7ffff3ff

def z712 : W := mkw 0x0b701d8014d00a00 0x00b701d8014d00a0 0xbff01fc03ff03f0d 0xfbff01fc03ff03f0

def z713 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfffffffc00820cf 0xfcfffffffc00820c

def z714 : W := mkw 0x22401fdb49113fff 0xc22401fdb49113ff 0x40001fffc0003ff4 0x140001fffc0003ff

def z715 : W := mkw 0xab707fc01dd27b0c 0x0ab707fc01dd27b0 0xbff07fc03ff03f0d 0xfbff07fc03ff03f0

def z716 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xfff17fc6ffff3fcf 0xffff17fc6ffff3fc

def z717 : W := mkw 0x4fedddb580100a20 0x84fedddb580100a2 0xcfffffffc0000337 0xfcfffffffc000033

def z718 : W := mkw 0x8dafc000266c8000 0x08dafc000266c800 0xbfcf00003f770000 0xcbfcf00003f77000

def z719 : W := mkw 0xe9f4e9d194f2cb0c 0x0e9f4e9d194f2cb0 0x81f0e1c1c0f0c301 0x081f0e1c1c0f0c30

def z720 : W := mkw 0x00d6ab5b78bbeffb 0xc00d6ab5b78bbeff 0xb1ff7efef8771c00 0xdb1ff7efef8771c0

def z721 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1ce183820f8fffe 0x7e1ce183820f8fff

def z722 : W := mkw 0x2b603d8245535a55 0x42b603d8245535a5 0xefc1f807e77fdcf2 0x5efc1f807e77fdcf

def z723 : W := mkw 0x8dbde00016e6c000 0x08dbde00016e6c00 0x9fffe0001ff7c003 0xe9fffe0001ff7c00

def z724 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0f1fffff0f3cce 0xf7e0f1fffff0f3cc

def z725 : W := mkw 0x4f695db580000000 0x04f695db58000000 0x4e3f7fffc0000006 0xf4e3f7fffc000000

def z726 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff01fc03f701c05 0xfbff01fc03f701c0

def z727 : W := mkw 0x0b701f001dd03a00 0x00b701f001dd03a0 0xbff01f003ff03f0d 0xfbff01f003ff03f0

def z728 : W := mkw 0x32401fe609113b4d 0x032401fe609113b4 0x00001fc600003f04 0x100001fc600003f0

def z729 : W := mkw 0x59e6cb9bab0d34c3 0x059e6cb9bab0d34c 0xb1f0e1c1ff0f3cc9 0x0b1f0e1c1ff0f3cc

def z730 : W := mkw 0x160b142c230c1482 0x0160b142c230c148 0x7e0f18383f0f3cce 0xf7e0f18383f0f3cc

def z731 : W := mkw 0x8dbfe00836eec482 0x08dbfe00836eec48 0xbffff8383fffdc0b 0xfbffff8383fffdc0

def z732 : W := mkw 0x3012224a7fdf7fdf 0x43012224a7fdf7fd 0x300000003ffffff8 0x0300000003ffffff

def z733 : W := mkw 0x4ffdfff7d8836159 0x44ffdfff7d883615 0x9fce1838188fe3f8 0x59fce1838188fe3f

def z734 : W := mkw 0x948fe03f222fc4e3 0x8948fe03f222fc4e 0x400fe03f000fc0f2 0x0400fe03f000fc0f

def z735 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfce00003f770000 0x4bfce00003f77000

def z736 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0f1e3e3f071c06 0xf7e0f1e3e3f071c0

def z737 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0f1f3f3f0f3ffe 0xf7e0f1f3f3f0f3ff

def z738 : W := mkw 0x0d2b0000264c0000 0x00d2b0000264c000 0xbfcf00003f7f000a 0xebfcf00003f7f000

def z739 : W := mkw 0x4fadd4b580000000 0x04fadd4b58000000 0xcfffe6ffc0000003 0xecfffe6ffc000000

def z740 : W := mkw 0x2bb696d93de8b5ae 0x82bb696d93de8b5a 0x5e3e86f91f08c0f2 0x85e3e86f91f08c0f

def z741 : W := mkw 0x848fe008222ec4a2 0x8848fe008222ec4a 0x000fe000000fc0f2 0x0000fe000000fc0f

def z742 : W := mkw 0x0b20140005401000 0x00b2014000540100 0xafc0180027701c00 0x5afc0180027701c0

def z743 : W := mkw 0x4be4ddb580000000 0x04be4ddb58000000 0xc1feffffc0000007 0x7c1feffffc000000

def z744 : W := mkw 0x2b701d8015d01a04 0x02b701d8015d01a0 0xaff0180027f01c01 0x5aff0180027f01c0

def z745 : W := mkw 0x048f8019222c84a2 0x8048f8019222c84a 0x400f8039000fc0f2 0x0400f8039000fc0f

def z746 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0f1e3e3f8ffffe 0xf7e0f1e3e3f8ffff

def z747 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff019c03ff03f09 0x5bff019c03ff03f0

def z748 : W := mkw 0x4f2b54aca0388ea2 0x84f2b54aca0388ea 0x2e3166c6e0f8fff8 0x82e3166c6e0f8fff

def z749 : W := mkw 0x32401fee49113fdf 0x432401fee49113fd 0x40001fffc0003ff4 0x140001fffc0003ff

def z750 : W := mkw 0x89b4e00014e2c000 0x089b4e00014e2c00 0xbff1e0003fffc00b 0xebff1e0003fffc00

def z751 : W := mkw 0x2b701fc21dd13b4d 0x02b701fc21dd13b4 0xfff19fc73fffffff 0xffff19fc73ffffff

def z752 : W := mkw 0x0000020208012041 0x0000002020801204 0x5031e7c7d88fe3ff 0xa5031e7c7d88fe3f

def z753 : W := mkw 0x2b601fc00d503b0c 0x02b601fc00d503b0 0xafc0180027703f00 0x5afc0180027703f0

def z754 : W := mkw 0xc2523db5b6eec000 0x0c2523db5b6eec00 0x70001fffffffc00c 0x170001fffffffc00

def z755 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xa1ce993920f8fff9 0x5a1ce993920f8fff

def z756 : W := mkw 0x8dbfe01136eec000 0x08dbfe01136eec00 0xffffe0393fffc00b 0xeffffe0393fffc00

def z757 : W := mkw 0x140b002e220d04c3 0x0140b002e220d04c 0x7e0f183e3f0f3cce 0xf7e0f183e3f0f3cc

def z758 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xaff0180027701c01 0xfaff0180027701c0

def z759 : W := mkw 0x2012224a7dfbffff 0xc2012224a7dfbfff 0x300000003ffffff8 0x0300000003ffffff

def z760 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xefc0990127f8ffff 0x7efc0990127f8fff

def z761 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xafc0190027f01f01 0x5afc0190027f01f0

def z762 : W := mkw 0x40c6c919a0388ea2 0x840c6c919a0388ea 0xe1cef939e0f8ffff 0x7e1cef939e0f8fff

def z763 : W := mkw 0x22401fc249113b5d 0x422401fc249113b5 0x00001fc000003ff4 0x100001fc000003ff

def z764 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfff7fffc0000004 0xdcfff7fffc000000

def z765 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfcfe0003fffc00a 0x4bfcfe0003fffc00

def z766 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xa1ce193820f8fffd 0x7a1ce193820f8fff

def z767 : W := mkw 0x32401fae09113ec7 0x032401fae09113ec 0x40001e3e00003cc4 0x140001e3e00003cc

def z768 : W := mkw 0x0010224258836159 0x4001022425883615 0x7e31e7c7ff8fe3ff 0xe7e31e7c7ff8fe3f

def z769 : W := mkw 0x40c68999a0388ea2 0x840c68999a0388ea 0xe1ce99f9e0f8ffff 0x7e1ce99f9e0f8fff

def z770 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xfff09fc13ff03f0f 0xffff09fc13ff03f0

def z771 : W := mkw 0x0202160a290934c3 0x00202160a290934c 0x7e0f1e3e3f0f3cce 0xf7e0f1e3e3f0f3cc

def z772 : W := mkw 0x8932200036eec000 0x08932200036eec00 0xbff1e0003fffc00b 0xebff1e0003fffc00

def z773 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0xffcf1e3e3fff3ccf 0xfffcf1e3e3fff3cc

def z774 : W := mkw 0x649dc2759dd03b0c 0x0649dc2759dd03b0 0x700fe03ffff03f0a 0x0700fe03ffff03f0

def z775 : W := mkw 0x040b0000220c0000 0x0040b0000220c000 0xbfcf00003fff000b 0xebfcf00003fff000

def z776 : W := mkw 0x2b701fc21dd13b4d 0x02b701fc21dd13b4 0xfff1ffc7ffff3fcf 0xffff1ffc7ffff3fc

def z777 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xafc0190027703f04 0x5afc0190027703f0

def z778 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfff7efec0000006 0xfcfff7efec000000

def z779 : W := mkw 0x0930200014c24000 0x00930200014c2400 0xbff160003ff70009 0xebff160003ff7000

def z780 : W := mkw 0x8d79691916d64ea2 0x88d79691916d64ea 0x5e3179391f073ff4 0x95e3179391f073ff

def z781 : W := mkw 0x2b701d8015d01a04 0x02b701d8015d01a0 0xbff018003f701c00 0xdbff018003f701c0

def z782 : W := mkw 0x16cd9f370b35ba61 0x816cd9f370b35ba6 0x9fc187071ff7c331 0x89fc187071ff7c33

def z783 : W := mkw 0x2b701fd11dd03b0c 0x02b701fd11dd03b0 0xfff01ff93ff03f0d 0xffff01ff93ff03f0

def z784 : W := mkw 0x0930200014c24000 0x00930200014c2400 0xbff000003fffc009 0xebff000003fffc00

def z785 : W := mkw 0x8930200016c64000 0x08930200016c6400 0xbff000003ff70009 0xebff000003ff7000

def z786 : W := mkw 0x1286962e2929b4c3 0x01286962e2929b4c 0xe1ce9e3e20f8fccf 0x7e1ce9e3e20f8fcc

def z787 : W := mkw 0x02501f4019903b08 0x002501f4019903b0 0xbff01fc03ff03f0d 0xfbff01fc03ff03f0

def z788 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xaff01ec027701c00 0xdaff01ec027701c0

def z789 : W := mkw 0x0609142400000000 0x0060914240000000 0x4e3f7efec0000006 0xf4e3f7efec000000

def z790 : W := mkw 0x1609162e0b0534c3 0x01609162e0b0534c 0x5e0f1e3e1f073cc6 0xf5e0f1e3e1f073cc

def z791 : W := mkw 0x29700bc01dd03b0c 0x029700bc01dd03b0 0xbff001c03ff03f09 0xebff001c03ff03f0

def z792 : W := mkw 0x00d4ab5358836159 0x400d4ab535883615 0xd1ce9939188fe3ff 0x7d1ce9939188fe3f

def z793 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xffffe0013fffc0fb 0xeffffe0013fffc0f

def z794 : W := mkw 0x6b701ff59dd03b0c 0x06b701ff59dd03b0 0xfff1fffffff03f0f 0xffff1fffffff03f0

def z795 : W := mkw 0x2b3016401dd03b0c 0x02b3016401dd03b0 0xbff01e003ff03f0d 0xfbff01e003ff03f0

def z796 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xffffe0003fffe0cf 0xeffffe0003fffe0c

def z797 : W := mkw 0x89f4e95154f2cb38 0xc89f4e95154f2cb3 0x81f0e1c1c0f0c331 0x081f0e1c1c0f0c33

def z798 : W := mkw 0x09b6a00034eac000 0x009b6a00034eac00 0xbfffe0003fffc00b 0xebfffe0003fffc00

def z799 : W := mkw 0x848fc019222c84a2 0x8848fc019222c84a 0x000e003800000000 0x0000e00380000000

def z800 : W := mkw 0x2b701fd11dd03b2c 0x82b701fd11dd03b2 0xbff01fc13ff03f3d 0xfbff01fc13ff03f3

def z801 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1cff93fe0f8ffff 0x7e1cff93fe0f8fff

def z802 : W := mkw 0xa6cfffc02b3efb0c 0x0a6cfffc02b3efb0 0x000fffc0000fff06 0x1000fffc0000fff0

def z803 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xaff01fc027f03f05 0x5aff01fc027f03f0

def z804 : W := mkw 0x0b30140015c01000 0x00b30140015c0100 0xbff018003ff01c09 0xfbff018003ff01c0

def z805 : W := mkw 0x3d7b09ee36dd0fcf 0x03d7b09ee36dd0fc 0xc1ff01fe00ff03c3 0x0c1ff01fe00ff03c

def z806 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbffe00003fffc009 0xebffe00003fffc00

def z807 : W := mkw 0x4dedc9b580000000 0x04dedc9b58000000 0xc1ffe7ffc0000007 0xac1ffe7ffc000000

def z808 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e3ffe3e3f0f3ccf 0xf7e3ffe3e3f0f3cc

def z809 : W := mkw 0x060b16082b0c3482 0x0060b16082b0c348 0x7e0f1e383f0f3cce 0xf7e0f1e383f0f3cc

def z810 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0f9e3f3f0ffcfe 0xf7e0f9e3f3f0ffcf

def z811 : W := mkw 0x2b601f800d503a04 0x02b601f800d503a0 0xbfc01e003f701c00 0xdbfc01e003f701c0

def z812 : W := mkw 0x6b701fd19dd03b0c 0x06b701fd19dd03b0 0xbff01fc1fff03f0d 0xfbff01fc1fff03f0

def z813 : W := mkw 0x8dbfe00836eec4a2 0x88dbfe00836eec4a 0xbfffe0003fffc0fb 0xebfffe0003fffc0f

def z814 : W := mkw 0x2b701dc015d01b0c 0x02b701dc015d01b0 0xbff019c03ff01f09 0xfbff019c03ff01f0

def z815 : W := mkw 0x22401fc209113b4d 0x022401fc209113b4 0x40001fc600003fc4 0x140001fc600003fc

def z816 : W := mkw 0x2b601fc00d503b0c 0x02b601fc00d503b0 0xaff01fc027703f05 0xfaff01fc027703f0

def z817 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff007c03ff03f09 0x8bff007c03ff03f0

def z818 : W := mkw 0x0dbf800036ec8000 0x00dbf800036ec800 0xbfff80003fffc00b 0xebfff80003fffc00

def z819 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xffffe1013fffc00f 0xeffffe1013fffc00

def z820 : W := mkw 0x040b020a2a0d24c3 0x0040b020a2a0d24c 0x7e0f1e3e3f0f3cce 0xf7e0f1e3e3f0f3cc

def z821 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfffe1c1ffffc00b 0xebfffe1c1ffffc00

def z822 : W := mkw 0x8dafc000266c8000 0x08dafc000266c800 0xbfffe0003f7f000b 0xebfffe0003f7f000

def z823 : W := mkw 0x2b703fc01dd27b0c 0x02b703fc01dd27b0 0xbff0ffc03ff0ff0d 0xfbff0ffc03ff0ff0

def z824 : W := mkw 0x0b3036021dc37041 0x00b3036021dc3704 0xfff1fe063ffffccf 0xffff1fe063ffffcc

def z825 : W := mkw 0x0dbde00014c24000 0x00dbde00014c2400 0xbfffe0003fffc00b 0xebfffe0003fffc00

def z826 : W := mkw 0x8932200036eec000 0x08932200036eec00 0xbfc000003fffc008 0x4bfc000003fffc00

def z827 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xafc0190027701c05 0x7afc0190027701c0

def z828 : W := mkw 0x140b020a2b0d34c3 0x0140b020a2b0d34c 0x7e0f18383f0f3cce 0xf7e0f18383f0f3cc

def z829 : W := mkw 0x62401ff7c9113b5d 0x462401ff7c9113b5 0x40001fffc0003ff4 0x140001fffc0003ff

def z830 : W := mkw 0x8dbfe01936eec4a2 0x88dbfe01936eec4a 0xffffe1393fffe3ff 0xeffffe1393fffe3f

def z831 : W := mkw 0x6f3976e6ddc3715d 0x46f3976e6ddc3715 0x1e3166c6df070000 0x81e3166c6df07000

def z832 : W := mkw 0x0960090004500a00 0x00960090004500a0 0xafc0180027701c00 0x5afc0180027701c0

def z833 : W := mkw 0x2b601fc00d503b0c 0x02b601fc00d503b0 0xafc01ec027701c00 0x5afc01ec027701c0

def z834 : W := mkw 0x9bb4f62e1de3f4c3 0x09bb4f62e1de3f4c 0xc1f0fe3e00f0fcc5 0x1c1f0fe3e00f0fcc

def z835 : W := mkw 0x0960090004500a00 0x00960090004500a0 0xafc0190027f03f0d 0x7afc0190027f03f0

def z836 : W := mkw 0x360b16ee2b0d35cf 0x0360b16ee2b0d35c 0x7e0f1efe3f0f3cce 0xf7e0f1efe3f0f3cc

def z837 : W := mkw 0x6fedddb585401004 0x06fedddb58540100 0xcfffffffc7000007 0xfcfffffffc700000

def z838 : W := mkw 0x4fedddb580308a20 0x84fedddb580308a2 0xcfffffffc0700007 0xfcfffffffc070000

def z839 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1ce9fffe0f8ffff 0x7e1ce9fffe0f8fff

def z840 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xfff11fc63ff03f0f 0xffff11fc63ff03f0

def z841 : W := mkw 0x0d3b200036ce4000 0x00d3b200036ce400 0xbfffe0003fffc00b 0xebfffe0003fffc00

def z842 : W := mkw 0x22401fc009103b0c 0x022401fc009103b0 0xbfc01fc03ff03f0d 0xfbfc01fc03ff03f0

def z843 : W := mkw 0x8012224a7effeffb 0xc8012224a7effeff 0x300000003ffffff8 0x0300000003ffffff

def z844 : W := mkw 0x4fadd4b580000000 0x04fadd4b58000000 0x4e3fe7ffc0000007 0xa4e3fe7ffc000000

def z845 : W := mkw 0x8dbfe04076eec118 0x48dbfe04076eec11 0xbfffe0003fffc33b 0xebfffe0003fffc33

def z846 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfffffffc00023f7 0xfcfffffffc00023f

def z847 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff11fc03fff3f0f 0xfbff11fc03fff3f0

def z848 : W := mkw 0x8d3b600036ce4000 0x08d3b600036ce400 0xbfff60003fff000b 0xebfff60003fff000

def z849 : W := mkw 0x6b701ff59dd03b0c 0x06b701ff59dd03b0 0xbff01ff83ff03f0d 0xfbff01ff83ff03f0

def z850 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xbff1ffc7fff7ff3d 0xfbff1ffc7fff7ff3

def z851 : W := mkw 0x0084801100000000 0x0008480110000000 0x403fe7ffc0000007 0xa403fe7ffc000000

def z852 : W := mkw 0x0086800820388ea2 0x80086800820388ea 0xe1ce983820f8ffff 0x7e1ce983820f8fff

def z853 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xbff0ffc1fffffffd 0xfbff0ffc1fffffff

def z854 : W := mkw 0x2b703dc055d25b1c 0x42b703dc055d25b1 0xaff0f9c1e7f0df31 0x5aff0f9c1e7f0df3

def z855 : W := mkw 0x948fe02c222ec482 0x0948fe02c222ec48 0x000fe038000fc002 0x0000fe038000fc00

def z856 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xafc01fc027701c04 0x5afc01fc027701c0

def z857 : W := mkw 0x8d3b200036eec000 0x08d3b200036eec00 0xbfff00003fffc00b 0xebfff00003fffc00

def z858 : W := mkw 0x3f3936e65fc7715d 0x43f3936e65fc7715 0x1e3166c6df070000 0x81e3166c6df07000

def z859 : W := mkw 0x44cdc93580000000 0x044cdc9358000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z860 : W := mkw 0x0042090820180e82 0x00042090820180e8 0xe1ce993920f8ffff 0x7e1ce993920f8fff

def z861 : W := mkw 0x8dafc2426e6da159 0x48dafc2426e6da15 0xefce07c7e77023f4 0x4efce07c7e77023f

def z862 : W := mkw 0xcdbfe035b6eec000 0x0cdbfe035b6eec00 0xffffe7ffffffc00f 0xeffffe7ffffffc00

def z863 : W := mkw 0x0f691da400000000 0x00f691da40000000 0xcfffffffc0000007 0xfcfffffffc000000

def z864 : W := mkw 0x8dbfe04076eec118 0x48dbfe04076eec11 0xffffe7c7ffffc33f 0xeffffe7c7ffffc33

def z865 : W := mkw 0x2b701dc015d01b0c 0x02b701dc015d01b0 0xaff01fc027f01f05 0xfaff01fc027f01f0

def z866 : W := mkw 0x4fedddb580100a00 0x04fedddb580100a0 0xefffffffe0f8ffff 0xfefffffffe0f8fff

def z867 : W := mkw 0x149fa27f7aafe5fb 0xc149fa27f7aafe5f 0x503fe7ffd88fe3ff 0xa503fe7ffd88fe3f

def z868 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbfc01e003ff03f0c 0xfbfc01e003ff03f0

def z869 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x3e0e1e383f0f3ccc 0xf3e0e1e383f0f3cc

def z870 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0x8fff7ffec0000005 0xf8fff7ffec000000

def z871 : W := mkw 0x8d39600016c64000 0x08d39600016c6400 0xbff1e0003fffc00b 0xebff1e0003fffc00

def z872 : W := mkw 0x9dbfe02c36eec482 0x09dbfe02c36eec48 0xbfffe0383fffc00b 0xebfffe0383fffc00

def z873 : W := mkw 0x0609162609013041 0x0060916260901304 0x7e0f1e3e3f0f3cce 0xf7e0f1e3e3f0f3cc

def z874 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xefffffffe0003c0f 0xfefffffffe0003c0

def z875 : W := mkw 0x22501f401dd03b0c 0x022501f401dd03b0 0xbfc01f003ff03f0d 0xfbfc01f003ff03f0

def z876 : W := mkw 0x049fa00032aec000 0x0049fa00032aec00 0xbfffe0003fffc00b 0xebfffe0003fffc00

def z877 : W := mkw 0x448dc03580000000 0x0448dc0358000000 0x403fe6ffc0000002 0x8403fe6ffc000000

def z878 : W := mkw 0x8dbfc00036ec8000 0x08dbfc00036ec800 0xbfff00003fff000b 0xebfff00003fff000

def z879 : W := mkw 0x8d3b600036eec000 0x08d3b600036eec00 0xbff160003fffc009 0xebff160003fffc00

def z880 : W := mkw 0x22401fc249113b5d 0x422401fc249113b5 0x00001fc6c0003f04 0x100001fc6c0003f0

def z881 : W := mkw 0x0970090014d00a00 0x00970090014d00a0 0xbff018003ff01c09 0xfbff018003ff01c0

def z882 : W := mkw 0xcdbfe035b6eec000 0x0cdbfe035b6eec00 0xbfffe0383fffc00b 0xebfffe0383fffc00

def z883 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xfff17fc7fff73ffd 0xffff17fc7fff73ff

def z884 : W := mkw 0x1012224a7bbffffb 0xc1012224a7bbffff 0x300000003ffffff8 0x0300000003ffffff

def z885 : W := mkw 0x468dd43580000000 0x0468dd4358000000 0x4e3fffffc0000007 0xf4e3fffffc000000

def z886 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xffffe6063fffc00f 0xeffffe6063fffc00

def z887 : W := mkw 0x0010224258836159 0x4001022425883615 0x503fffffd88fe3ff 0xf503fffffd88fe3f

def z888 : W := mkw 0x848fe008222ec482 0x0848fe008222ec48 0x400fe038000fc0c2 0x0400fe038000fc0c

def z889 : W := mkw 0x0010224258836159 0x4001022425883615 0x5031e7c7d80fe3f6 0x85031e7c7d80fe3f

def z890 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xefffffffe0f0000f 0xfefffffffe0f0000

def z891 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfffe6c6ffffc00b 0xebfffe6c6ffffc00

def z892 : W := mkw 0x160b162e2b2db4e3 0x8160b162e2b2db4e 0x7e0f1e3e3f0ffcfe 0xf7e0f1e3e3f0ffcf

def z893 : W := mkw 0x8dbde00016c64000 0x08dbde00016c6400 0xbfffe0003ff7000b 0xebfffe0003ff7000

def z894 : W := mkw 0x8dafe000266ec000 0x08dafe000266ec00 0xbfcfe0003f7fc00a 0xebfcfe0003f7fc00

def z895 : W := mkw 0x160b162e6b0d34d3 0x4160b162e6b0d34d 0x7e0f1e3fff0f3cfe 0xf7e0f1e3fff0f3cf

def z896 : W := mkw 0x0010200010824000 0x0001020001082400 0x5031e7c7d88fe3ff 0xa5031e7c7d88fe3f

def z897 : W := mkw 0x12401f3f09113ee3 0x812401f3f09113ee 0x40001e3e00003cc4 0x140001e3e00003cc

def z898 : W := mkw 0x0fadd42400000000 0x00fadd4240000000 0xcfffffffc0000007 0xfcfffffffc000000

def z899 : W := mkw 0x02401d0001101a00 0x002401d0001101a0 0xafc0180027701c00 0x5afc0180027701c0

def z900 : W := mkw 0x0000000000000000 0x0000000000000000 0x403fffffc0000007 0xf403fffffc000000

def z901 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfff60003ff70009 0xebfff60003ff7000

def z902 : W := mkw 0x02401d0001101a00 0x002401d0001101a0 0xafc0190027f03f0d 0x7afc0190027f03f0

def z903 : W := mkw 0x4fedddb581001000 0x04fedddb58100100 0xefffffffe7001c07 0xfefffffffe7001c0

def z904 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e3fffffff8fffff 0xf7e3fffffff8ffff

def z905 : W := mkw 0x2920000005501a04 0x02920000005501a0 0xafc0000027701c00 0x4afc0000027701c0

def z906 : W := mkw 0x4fedddb580208020 0x84fedddb58020802 0xcfffffffc000c037 0xfcfffffffc000c03

def z907 : W := mkw 0x160b166e6b0d35db 0x4160b166e6b0d35d 0x7e0f9fffff8fffff 0xf7e0f9fffff8ffff

def z908 : W := mkw 0x4fedddb584400000 0x04fedddb58440000 0xefffffffe7700007 0xfefffffffe770000

def z909 : W := mkw 0x2b703fc05dd27b1c 0x42b703fc05dd27b1 0xbff01fc03ff0ff3d 0xfbff01fc03ff0ff3

def z910 : W := mkw 0x4f2954a480000000 0x04f2954a48000000 0x0e3f7efec0000000 0xd0e3f7efec000000

def z911 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0x9fffe0001fffc003 0x89fffe0001fffc00

def z912 : W := mkw 0x0b601f8009103a00 0x00b601f8009103a0 0xbff01fc03ff03f0d 0xfbff01fc03ff03f0

def z913 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xbff17fc6fffffffd 0xfbff17fc6fffffff

def z914 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfffffffc088c00f 0xfcfffffffc088c00

def z915 : W := mkw 0x8dbfe01936eec4a2 0x88dbfe01936eec4a 0xbfffe0383fffc00b 0xebfffe0383fffc00

def z916 : W := mkw 0xcdbfe024b6eec000 0x0cdbfe024b6eec00 0xbfffe006ffffc00b 0xebfffe006ffffc00

def z917 : W := mkw 0x4dadc03580000000 0x04dadc0358000000 0xcfffe7ffc0000007 0xecfffe7ffc000000

def z918 : W := mkw 0x8dbfe04076eec118 0x48dbfe04076eec11 0xffffe1c1ffffe3ff 0xeffffe1c1ffffe3f

def z919 : W := mkw 0x0010224258836159 0x4001022425883615 0xf1f1e7c7f8ffe3ff 0xef1f1e7c7f8ffe3f

def z920 : W := mkw 0x0930000014d00a00 0x00930000014d00a0 0xbff000003ff03f09 0xebff000003ff03f0

def z921 : W := mkw 0xc48fe03da22ec4a2 0x8c48fe03da22ec4a 0x400fe03fc00fc0f2 0x0400fe03fc00fc0f

def z922 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xbfc018003ffffff8 0x5bfc018003ffffff

def z923 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xdfffffffd80f000f 0xfdfffffffd80f000

def z924 : W := mkw 0x6fedddb581101a04 0x06fedddb581101a0 0xcfffffffc0001c07 0xfcfffffffc0001c0

def z925 : W := mkw 0x6b705fc09dd03b0c 0x06b705fc09dd03b0 0xbff07fc0fff03f0d 0xfbff07fc0fff03f0

def z926 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xc1ce993900f8fff7 0x1c1ce993900f8fff

def z927 : W := mkw 0x2b703fc05dd27b1c 0x42b703fc05dd27b1 0xbff07fc0fff03f0d 0xfbff07fc0fff03f0

def z928 : W := mkw 0x6b701ff7ddd13b5d 0x46b701ff7ddd13b5 0xfff01ffffff03ffd 0xffff01ffffff03ff

def z929 : W := mkw 0x8dbde00016e6c000 0x08dbde00016e6c00 0xbff1e0003ff7c009 0xebff1e0003ff7c00

def z930 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xbff018003ff03c0d 0xfbff018003ff03c0

def z931 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xbff01fc03ff73f0d 0xfbff01fc03ff73f0

def z932 : W := mkw 0x6fedddb584500a04 0x06fedddb584500a0 0xcfffffffc0700007 0xfcfffffffc070000

def z933 : W := mkw 0x32401fff09113fef 0x832401fff09113fe 0x40001fff00003ff4 0x140001fff00003ff

def z934 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x5e0f1e3e1f0f3cc6 0x95e0f1e3e1f0f3cc

def z935 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x3e0f1e3e3f0f1c0a 0xf3e0f1e3e3f0f1c0

def z936 : W := mkw 0x2b701dc015d01b0c 0x02b701dc015d01b0 0xaff019c027f03f0d 0x7aff019c027f03f0

def z937 : W := mkw 0x8dbfe00836eec482 0x08dbfe00836eec48 0xffffe0383fffc0cb 0xeffffe0383fffc0c

def z938 : W := mkw 0x0040090000100a00 0x00040090000100a0 0xbfc019003ff03f0d 0xfbfc019003ff03f0

def z939 : W := mkw 0x5fedddb583041000 0x05fedddb58304100 0xcfffffffc7000007 0xfcfffffffc700000

def z940 : W := mkw 0x2b601f800d503a04 0x02b601f800d503a0 0xbff01fc03f703c0d 0xfbff01fc03f703c0

def z941 : W := mkw 0xcdbfe03db6eec4a2 0x8cdbfe03db6eec4a 0xffffe03fffffc0fb 0xeffffe03fffffc0f

def z942 : W := mkw 0xcdbfe011b6eec000 0x0cdbfe011b6eec00 0xbfffe001ffffc00b 0xebfffe001ffffc00

def z943 : W := mkw 0x4fedddb580100a00 0x04fedddb580100a0 0xcfffffffc0003f07 0xfcfffffffc0003f0

def z944 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfffe7ffc0000003 0x8cfffe7ffc000000

def z945 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xc1ffffffc0000007 0x1c1ffffffc000000

def z946 : W := mkw 0x2b701dc015d01b0c 0x02b701dc015d01b0 0xafc0180027f01f00 0x5afc0180027f01f0

def z947 : W := mkw 0x160916260b053041 0x0160916260b05304 0x7e0f1e3e3f073c0e 0xf7e0f1e3e3f073c0

def z948 : W := mkw 0xadbfe0c036eec10c 0x0adbfe0c036eec10 0xbfffe0c03fffc00b 0xebfffe0c03fffc00

def z949 : W := mkw 0x849fe25b7aafe5fb 0xc849fe25b7aafe5f 0x503fe7ffd88fe3ff 0xa503fe7ffd88fe3f

def z950 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfffe0003f7fc002 0xcbfffe0003f7fc00

def z951 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff09fc13ff0ff3d 0xfbff09fc13ff0ff3

def z952 : W := mkw 0x0930000014c00000 0x00930000014c0000 0xbff100003fff000b 0xebff100003fff000

def z953 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e3f1ffe3f0f3ccf 0xf7e3f1ffe3f0f3cc

def z954 : W := mkw 0x0dafc000222c8000 0x00dafc000222c800 0xbfffe0003fffc00b 0xebfffe0003fffc00

def z955 : W := mkw 0x4fedddb580100a00 0x04fedddb580100a0 0xcfffffffc0f00307 0xfcfffffffc0f0030

def z956 : W := mkw 0x00c4891900308ea2 0x800c4891900308ea 0xc1ce993900f0fff7 0x7c1ce993900f0fff

def z957 : W := mkw 0x49e4c99180000000 0x049e4c9918000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z958 : W := mkw 0x040b0008220c0482 0x0040b0008220c048 0x3e0f18383f0f1c0a 0xf3e0f18383f0f1c0

def z959 : W := mkw 0x2b703fc01dd27b0c 0x02b703fc01dd27b0 0xbff01fc03fffff0d 0xfbff01fc03fffff0

def z960 : W := mkw 0xa9f4e9d114f2cb2c 0x8a9f4e9d114f2cb2 0x81f0e1c100f0c331 0x081f0e1c100f0c33

def z961 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff01ec03ff01c09 0xfbff01ec03ff01c0

def z962 : W := mkw 0x2b701fc25dd13b5d 0x42b701fc25dd13b5 0xbff01fc6fff03f0d 0xfbff01fc6fff03f0

def z963 : W := mkw 0x148f803d222c84a2 0x8148f803d222c84a 0x400e80390008c0f2 0x0400e80390008c0f

def z964 : W := mkw 0x4fadd4b580000000 0x04fadd4b58000000 0x4e3ffeffc0000006 0xf4e3ffeffc000000

def z965 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xffce99393ff8ffff 0xfffce99393ff8fff

def z966 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xeff1ffc7e7701c07 0xfeff1ffc7e7701c0

def z967 : W := mkw 0x8dbde00016e6c000 0x08dbde00016e6c00 0x9ff160001f770000 0x89ff160001f77000

def z968 : W := mkw 0x948fc02c222c8482 0x0948fc02c222c848 0x000e003800000000 0x0000e00380000000

def z969 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xfffff8383fffc00f 0xffffff8383fffc00

def z970 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfffe0003fffe3fb 0xebfffe0003fffe3f

def z971 : W := mkw 0x148fa03f622fc4f3 0xc148fa03f622fc4f 0x400fe03fc00fc0f2 0x0400fe03fc00fc0f

def z972 : W := mkw 0x46cdddb580000000 0x046cdddb58000000 0x403fffffc0000007 0xb403fffffc000000

def z973 : W := mkw 0x2b3016c01dc0310c 0x02b3016c01dc0310 0xbff01ec03ff03c0d 0xfbff01ec03ff03c0

def z974 : W := mkw 0x160b162e2b2db4c3 0x0160b162e2b2db4c 0x7e0f1e3e3ffffcce 0xf7e0f1e3e3ffffcc

def z975 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff0ffc1fff03f0d 0xfbff0ffc1fff03f0

def z976 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xa1ce983820f8fffb 0x7a1ce983820f8fff

def z977 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xfff01fc7fffffffd 0xffff01fc7fffffff

def z978 : W := mkw 0x00c68919223c8ea2 0x800c68919223c8ea 0xf1ce99393fffffff 0x7f1ce99393ffffff

def z979 : W := mkw 0x2b701fc25dd13b5d 0x42b701fc25dd13b5 0xbff01fc03ff03ffd 0xfbff01fc03ff03ff

def z980 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfffe1013fffc33b 0xebfffe1013fffc33

def z981 : W := mkw 0x8dbfe00836eec482 0x08dbfe00836eec48 0xfffff9393fffffff 0xffffff9393ffffff

def z982 : W := mkw 0x948fc02e222d84c3 0x0948fc02e222d84c 0x400f003e000f00c2 0x0400f003e000f00c

def z983 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xfff01fc13ff03ffd 0xffff01fc13ff03ff

def z984 : W := mkw 0x2b601fc00d503b0c 0x02b601fc00d503b0 0xbfc01fc03f703f0c 0xfbfc01fc03f703f0

def z985 : W := mkw 0x02401f0209113a41 0x002401f0209113a4 0xffc19f073fffffff 0xfffc19f073ffffff

def z986 : W := mkw 0x4fedddb580100a00 0x04fedddb580100a0 0xefffffffe0701c07 0xfefffffffe0701c0

def z987 : W := mkw 0x8d39600016c64000 0x08d39600016c6400 0x9ff160001ff70001 0x89ff160001ff7000

def z988 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfff60003fffc008 0xcbfff60003fffc00

def z989 : W := mkw 0x4f695da480000000 0x04f695da48000000 0xcfff7ffec0000007 0xfcfff7ffec000000

def z990 : W := mkw 0x0b2016000d403000 0x00b2016000d40300 0xbfc01e003f703c0c 0xfbfc01e003f703c0

def z991 : W := mkw 0x160b142c230c1482 0x0160b142c230c148 0x3e0e18383f0f1c08 0x53e0e18383f0f1c0

def z992 : W := mkw 0x2b703fc01dd27b0c 0x02b703fc01dd27b0 0xbff17fc03ff73f0d 0xfbff17fc03ff73f0

def z993 : W := mkw 0x9012224a7feff5db 0x49012224a7feff5d 0x300000003ffffff8 0x0300000003ffffff

def z994 : W := mkw 0x00c4891100100a00 0x000c4891100100a0 0xe1ce993920f8ffff 0x7e1ce993920f8fff

def z995 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0e1e3e3f0f3ccc 0x57e0e1e3e3f0f3cc

def z996 : W := mkw 0x89f4e91114f2ca20 0x889f4e91114f2ca2 0x81f0e00000f0c001 0x081f0e00000f0c00

def z997 : W := mkw 0x160b166e2b0d35cb 0x0160b166e2b0d35c 0x7e0f1ffe3f0f3fce 0xf7e0f1ffe3f0f3fc

def z998 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e3f7efeff0f3cce 0xf7e3f7efeff0f3cc

def z999 : W := mkw 0x148f802e222d84c3 0x0148f802e222d84c 0x400f803e000fc0c2 0x0400f803e000fc0c

def z1000 : W := mkw 0x6b601db585501a04 0x06b601db585501a0 0xafc0183827701c00 0x5afc0183827701c0

def z1001 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0f1e3e3f0f1cc2 0xd7e0f1e3e3f0f1cc

def z1002 : W := mkw 0x0b701f801dc03000 0x00b701f801dc0300 0xbff01fc03ff03c0d 0xfbff01fc03ff03c0

def z1003 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0f1f3e3f8f3fcf 0xf7e0f1f3e3f8f3fc

def z1004 : W := mkw 0x160b166e6b0d35db 0x4160b166e6b0d35d 0x7e0f1efeff0f3cce 0xf7e0f1efeff0f3cc

def z1005 : W := mkw 0x948fe02e622fc4d3 0x4948fe02e622fc4d 0x400fe03fc00fc0f2 0x0400fe03fc00fc0f

def z1006 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x3e0f18383f0f3cca 0xf3e0f18383f0f3cc

def z1007 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xaff019c027701c01 0x5aff019c027701c0

def z1008 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff01fc03ff8fffd 0xfbff01fc03ff8fff

def z1009 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbffee0003fffc009 0x4bffee0003fffc00

def z1010 : W := mkw 0x0409002400000000 0x0040900240000000 0x403fe7ffc0000007 0xa403fe7ffc000000

def z1011 : W := mkw 0x2b601f800d503a04 0x02b601f800d503a0 0xbfc018003f703c08 0x5bfc018003f703c0

def z1012 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xf1cf993938ffffff 0xff1cf993938fffff

def z1013 : W := mkw 0x160b166e6b0d35db 0x4160b166e6b0d35d 0x7e0f1e3e3f0f3ffe 0xf7e0f1e3e3f0f3ff

def z1014 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfffffffc080c337 0xfcfffffffc080c33

def z1015 : W := mkw 0x9f3976665fc77159 0x49f3976665fc7715 0x1e3166c6df070000 0x81e3166c6df07000

def z1016 : W := mkw 0x6b701fe49dd03b0c 0x06b701fe49dd03b0 0xbff01fc6fff03f0d 0xfbff01fc6fff03f0

def z1017 : W := mkw 0x160b166e6b0d35db 0x4160b166e6b0d35d 0x7e3fffffff0f3fff 0xf7e3fffffff0f3ff

def z1018 : W := mkw 0x29700b401dd03b0c 0x029700b401dd03b0 0xbff019003ff03f0d 0xfbff019003ff03f0

def z1019 : W := mkw 0x848fe019222ec4a2 0x8848fe019222ec4a 0x000fe038000fc002 0x0000fe038000fc00

def z1020 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff018003ff03f09 0xfbff018003ff03f0

def z1021 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0x8ffffefec0000003 0xf8ffffefec000000

def z1022 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1fff93920f8ffff 0xfe1fff93920f8fff

def z1023 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfffe0003ff7c001 0xcbfffe0003ff7c00

def z1024 : W := mkw 0x2b701fc21dd13b4d 0x02b701fc21dd13b4 0xfff01fc63ff03fcd 0xffff01fc63ff03fc

def z1025 : W := mkw 0x2b601f820d513a45 0x02b601f820d513a4 0xffc11e063f7f3cce 0xfffc11e063f7f3cc

def z1026 : W := mkw 0x2b703fc05dd27b1c 0x42b703fc05dd27b1 0xfff1ffc7fff0ff3f 0xffff1ffc7fff0ff3

def z1027 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfffffffc080230f 0xfcfffffffc080230

def z1028 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff17fc6fff03f0d 0xfbff17fc6fff03f0

def z1029 : W := mkw 0xcfefddbda67c8ea2 0x8cfefddbda67c8ea 0xafce183827701c00 0x5afce183827701c0

def z1030 : W := mkw 0x2b703fc05dd27b1c 0x42b703fc05dd27b1 0xfff0ffc1fff8ffff 0xffff0ffc1fff8fff

def z1031 : W := mkw 0x0d39000016c40000 0x00d39000016c4000 0xbff100003ff70009 0xebff100003ff7000

def z1032 : W := mkw 0x0b3036425dc37159 0x40b3036425dc3715 0xfff1ffc7ffffffff 0xffff1ffc7fffffff

def z1033 : W := mkw 0x8d39600016c64000 0x08d39600016c6400 0xbff160003f770000 0xcbff160003f77000

def z1034 : W := mkw 0x0002000820388ea2 0x80002000820388ea 0x6031e7c7e0f8ffff 0xa6031e7c7e0f8fff

def z1035 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xfff09fc13fffffff 0xffff09fc13ffffff

def z1036 : W := mkw 0xcfedddb586440000 0x0cfedddb58644000 0xcfffffffc7000007 0xfcfffffffc700000

def z1037 : W := mkw 0x2b701fc21dd13b4d 0x02b701fc21dd13b4 0xbff01fc03fff3fcd 0xfbff01fc03fff3fc

def z1038 : W := mkw 0x8dbfe00076eec010 0x48dbfe00076eec01 0xbfffe001ffffc03b 0xebfffe001ffffc03

def z1039 : W := mkw 0x4fedddb580308a20 0x84fedddb580308a2 0xcfffffffc0f8e3ff 0xfcfffffffc0f8e3f

def z1040 : W := mkw 0x160b162c2b0c3482 0x0160b162c2b0c348 0x3e0f1e383f0f3c0e 0xf3e0f1e383f0f3c0

def z1041 : W := mkw 0x949fe22e3aafe4c3 0x0949fe22e3aafe4c 0x503fe63e188fe0cf 0xa503fe63e188fe0c

def z1042 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xafc0180027f01c09 0x7afc0180027f01c0

def z1043 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1ce193920f8fffc 0x5e1ce193920f8fff

def z1044 : W := mkw 0x548fc03fa22d84e3 0x8548fc03fa22d84e 0x400fe03fc00fc0f2 0x0400fe03fc00fc0f

def z1045 : W := mkw 0xd48fe03fa22fc4c3 0x0d48fe03fa22fc4c 0x400fe03fc00fc0c2 0x0400fe03fc00fc0c

def z1046 : W := mkw 0x2b701d8015d01a04 0x02b701d8015d01a0 0xbff019003ff03f0d 0xfbff019003ff03f0

def z1047 : W := mkw 0x29f4a9d154f2cb3c 0xc29f4a9d154f2cb3 0x81f0e1c1c0f0c331 0x081f0e1c1c0f0c33

def z1048 : W := mkw 0x69f4e9d1d4d24b1c 0x469f4e9d1d4d24b1 0x81f0e1c1c0f0c331 0x081f0e1c1c0f0c33

def z1049 : W := mkw 0x0012224a788b65db 0x40012224a788b65d 0x30000000388ffff8 0x030000000388ffff

def z1050 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff01ec03ff03f08 0xdbff01ec03ff03f0

def z1051 : W := mkw 0x2b701fc05dd03b1c 0x42b701fc05dd03b1 0xbff01fc1fff03f3d 0xfbff01fc1fff03f3

def z1052 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1fe9ff920f8ffff 0xfe1fe9ff920f8fff

def z1053 : W := mkw 0x560b562eab0d34c3 0x0560b562eab0d34c 0x7e0f7e3eff0f3cce 0xf7e0f7e3eff0f3cc

def z1054 : W := mkw 0x093002001dc03000 0x0093002001dc0300 0xbff000003ff03c09 0xebff000003ff03c0

def z1055 : W := mkw 0x948fe00a222fc4c3 0x0948fe00a222fc4c 0x000fe000000fc0c2 0x0000fe000000fc0c

def z1056 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfffe7c03fffc00f 0xebfffe7c03fffc00

def z1057 : W := mkw 0x1012224a7a8f65db 0x41012224a7a8f65d 0x10000000188fe3f8 0x010000000188fe3f

def z1058 : W := mkw 0x2b701d8015d01a04 0x02b701d8015d01a0 0xbfc018003ff01c08 0x5bfc018003ff01c0

def z1059 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcffffeffc0000002 0xdcffffeffc000000

def z1060 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0f9f3f3f0f3ccf 0xf7e0f9f3f3f0f3cc

def z1061 : W := mkw 0x06cd9d3500000000 0x006cd9d350000000 0xcfffffffc0000007 0xfcfffffffc000000

def z1062 : W := mkw 0x0010224258836159 0x4001022425883615 0x4031e7c7c08fe3f7 0x04031e7c7c08fe3f

def z1063 : W := mkw 0x2b601f800d503a04 0x02b601f800d503a0 0xafc01e0027703c04 0x5afc01e0027703c0

def z1064 : W := mkw 0x0000224248036159 0x4000022424803615 0x4031e7c7c00fe3f7 0xa4031e7c7c00fe3f

def z1065 : W := mkw 0x297009c014d00b0c 0x0297009c014d00b0 0xbff019c03ff03f0d 0xfbff019c03ff03f0

def z1066 : W := mkw 0x0010224258836159 0x4001022425883615 0x7031ffc7f88fffff 0xf7031ffc7f88ffff

def z1067 : W := mkw 0x2b701fc25dd13b5d 0x42b701fc25dd13b5 0xfff09fc7fff8ffff 0xffff09fc7fff8fff

def z1068 : W := mkw 0x32401fca09113fcf 0x032401fca09113fc 0x00001fc000003fc4 0x100001fc000003fc

def z1069 : W := mkw 0x849fe01932aec4a2 0x8849fe01932aec4a 0x503fe139188fe3ff 0xa503fe139188fe3f

def z1070 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xbfc018003f701c08 0xfbfc018003f701c0

def z1071 : W := mkw 0x0010224259837159 0x4001022425983715 0x7031e7c7ff8fffff 0xa7031e7c7ff8ffff

def z1072 : W := mkw 0x4fadd4a480000000 0x04fadd4a48000000 0xcffffefec0000007 0xfcffffefec000000

def z1073 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xbff1ffc6ffffff0f 0xfbff1ffc6ffffff0

def z1074 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbfc019003ff03f0d 0x7bfc019003ff03f0

def z1075 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfcf00003fffc00a 0xebfcf00003fffc00

def z1076 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x3e0f1e3e3f073c0c 0xf3e0f1e3e3f073c0

def z1077 : W := mkw 0x2b3016c01dd03b0c 0x02b3016c01dd03b0 0xbff006c03ff03f09 0xebff006c03ff03f0

def z1078 : W := mkw 0x4fadd4b580000000 0x04fadd4b58000000 0x0e3f66fec0000000 0x80e3f66fec000000

def z1079 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xfffe1ff83ff03f0f 0xffffe1ff83ff03f0

def z1080 : W := mkw 0x8dafc000266c8000 0x08dafc000266c800 0xbfcf80003fffc00b 0xebfcf80003fffc00

def z1081 : W := mkw 0x5fefddbda33c9ea2 0x85fefddbda33c9ea 0xafce183827701c00 0x5afce183827701c0

def z1082 : W := mkw 0xcdbfe080b6eec000 0x0cdbfe080b6eec00 0xbfffe0c0ffffc00b 0xebfffe0c0ffffc00

def z1083 : W := mkw 0x2b601fc00d503b0c 0x02b601fc00d503b0 0xafc01fc027f03f0d 0x7afc01fc027f03f0

def z1084 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbff1e0003fffc009 0x8bff1e0003fffc00

def z1085 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xfff11fc63fffffff 0xffff11fc63ffffff

def z1086 : W := mkw 0x044b0919221c0ea2 0x8044b0919221c0ea 0x7e0f19393f0f3ffe 0xf7e0f19393f0f3ff

def z1087 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xbff1ffc03fffffff 0xfbff1ffc03ffffff

def z1088 : W := mkw 0x1012224a7b8f75db 0x41012224a7b8f75d 0x300000003f0f3cc8 0x0300000003f0f3cc

def z1089 : W := mkw 0x46491db580000000 0x046491db58000000 0x4e3fffffc0000007 0xf4e3fffffc000000

def z1090 : W := mkw 0x148f803d222c84a2 0x8148f803d222c84a 0x000e003800000000 0x0000e00380000000

def z1091 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xfff01fc7fff03f0d 0xffff01fc7fff03f0

def z1092 : W := mkw 0x8dbfe00836eec482 0x08dbfe00836eec48 0xbfffe0003ffffccb 0xebfffe0003ffffcc

def z1093 : W := mkw 0x060b16242b0c3000 0x0060b16242b0c300 0x7e0f1e3e3f0f3c0e 0xf7e0f1e3e3f0f3c0

def z1094 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfce80003fffc00b 0x6bfce80003fffc00

def z1095 : W := mkw 0x12401f7f49113ffb 0xc12401f7f49113ff 0x40001fffc0003ff4 0x140001fffc0003ff

def z1096 : W := mkw 0x848fe01b622fc4f3 0xc848fe01b622fc4f 0x400fe03fc00fc0f2 0x0400fe03fc00fc0f

def z1097 : W := mkw 0x2b703fc01dd27b0c 0x02b703fc01dd27b0 0xfff1ffc13fffffff 0xffff1ffc13ffffff

def z1098 : W := mkw 0x0dedc91100000000 0x00dedc9110000000 0xcfffffffc0000007 0xfcfffffffc000000

def z1099 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1ce993920f0fff5 0x5e1ce993920f0fff

def z1100 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1ce983920f8fffa 0x5e1ce983920f8fff

def z1101 : W := mkw 0x2b701fc25dd13b5d 0x42b701fc25dd13b5 0xfff1ffc7fff03fff 0xffff1ffc7fff03ff

def z1102 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff01ec03f703c0c 0xfbff01ec03f703c0

def z1103 : W := mkw 0x09702b425cd36b59 0x409702b425cd36b5 0xfff1ffc7ffffffff 0xffff1ffc7fffffff

def z1104 : W := mkw 0x89b6e00036eec000 0x089b6e00036eec00 0xbff0e0003fffc009 0xebff0e0003fffc00

def z1105 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xbff17ec6ff771c00 0xdbff17ec6ff771c0

def z1106 : W := mkw 0x6fedddb585501a04 0x06fedddb585501a0 0xefffffffe7f03f0f 0xfefffffffe7f03f0

def z1107 : W := mkw 0x0042090820388ea2 0x80042090820388ea 0xe1ce193820f8ffff 0x7e1ce193820f8fff

def z1108 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbfc01fc03ff03f0c 0x5bfc01fc03ff03f0

def z1109 : W := mkw 0x4fedddb580208000 0x04fedddb58020800 0xcfffffffc0f0c007 0xfcfffffffc0f0c00

def z1110 : W := mkw 0x8dbfe02436eec000 0x08dbfe02436eec00 0xffffe03e3fffc00b 0xeffffe03e3fffc00

def z1111 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0ffe3fff0f3cce 0xf7e0ffe3fff0f3cc

def z1112 : W := mkw 0x2b701d8015d01a04 0x02b701d8015d01a0 0xbff01fc03ff01c0d 0xfbff01fc03ff01c0

def z1113 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfffe1003fffe30f 0xebfffe1003fffe30

def z1114 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xafc01e0027701c04 0xfafc01e0027701c0

def z1115 : W := mkw 0x42c49db580000000 0x042c49db58000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z1116 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xffffe7c7ffffe3ff 0xeffffe7c7ffffe3f

def z1117 : W := mkw 0x060b142c220c0482 0x0060b142c220c048 0x7e0f1e3e3f0f3cce 0xf7e0f1e3e3f0f3cc

def z1118 : W := mkw 0xcfedddb584608000 0x0cfedddb58460800 0xcfffffffc0700007 0xfcfffffffc070000

def z1119 : W := mkw 0x001022425cc36159 0x4001022425cc3615 0x7031e7c7ffffe3ff 0xa7031e7c7ffffe3f

def z1120 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbffff8003ffffc0f 0xfbffff8003ffffc0

def z1121 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xafc0180027f03f08 0x5afc0180027f03f0

def z1122 : W := mkw 0x8dbfe04036eec108 0x08dbfe04036eec10 0xbfffe1c03fffc30b 0xebfffe1c03fffc30

def z1123 : W := mkw 0x560b16aeab0d34c3 0x0560b16aeab0d34c 0x7e0f1efeff0f3cce 0xf7e0f1efeff0f3cc

def z1124 : W := mkw 0x02401f0009103a00 0x002401f0009103a0 0xbfc01e003f703c0c 0xfbfc01e003f703c0

def z1125 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcffeffffc0000005 0x5cffeffffc000000

def z1126 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xfff1ffc7fff8ffff 0xffff1ffc7fff8fff

def z1127 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0f183e3f0f3cca 0x57e0f183e3f0f3cc

def z1128 : W := mkw 0x1202160a2b0d34c3 0x01202160a2b0d34c 0x7e0e1e383f0f3cce 0xf7e0e1e383f0f3cc

def z1129 : W := mkw 0x0932000036cc0000 0x00932000036cc000 0xbff000003fff0009 0xebff000003fff000

def z1130 : W := mkw 0x293022425dd37b5d 0x4293022425dd37b5 0xbff1e0003ffffffb 0xebff1e0003ffffff

def z1131 : W := mkw 0x2b703fc21dd37b4d 0x02b703fc21dd37b4 0xfff1ffc63fffffcf 0xffff1ffc63fffffc

def z1132 : W := mkw 0x848fe000222ec000 0x0848fe000222ec00 0xbfcfe0003fffc00b 0xebfcfe0003fffc00

def z1133 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0x8fffffffc0000001 0xd8fffffffc000000

def z1134 : W := mkw 0x048f8000222c8000 0x0048f8000222c800 0xbfcf00003f7f000a 0xebfcf00003f7f000

def z1135 : W := mkw 0x6b703ff7ddd37b5d 0x46b703ff7ddd37b5 0xfff1ffffffffffff 0xffff1fffffffffff

def z1136 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0x4e3fffffc0000006 0x94e3fffffc000000

def z1137 : W := mkw 0x949fe26e7aafe5db 0x4949fe26e7aafe5d 0x503fe7ffd88fe3ff 0xa503fe7ffd88fe3f

def z1138 : W := mkw 0x6b601db585501a04 0x06b601db585501a0 0xefc01fffe7701c04 0x5efc01fffe7701c0

def z1139 : W := mkw 0x12401f2e09113ec3 0x012401f2e09113ec 0x40001f3e00003fc4 0x140001f3e00003fc

def z1140 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1fef9f9e0f8ffff 0x7e1fef9f9e0f8fff

def z1141 : W := mkw 0x160b142e230d14c3 0x0160b142e230d14c 0x7e0f183e3f0f1cca 0xf7e0f183e3f0f1cc

def z1142 : W := mkw 0x8dbfe01136eec020 0x88dbfe01136eec02 0xbfffe0013fffc03b 0xebfffe0013fffc03

def z1143 : W := mkw 0x849fa00036eec000 0x0849fa00036eec00 0xbfcf80003fffc00b 0xebfcf80003fffc00

def z1144 : W := mkw 0x160b142c230c1482 0x0160b142c230c148 0x3e0f18383f071c00 0xd3e0f18383f071c0

def z1145 : W := mkw 0x8dbfe01936eec4a2 0x88dbfe01936eec4a 0xfffff8393ffffcff 0xffffff8393ffffcf

def z1146 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0f1e3e3f073cc4 0xd7e0f1e3e3f073cc

def z1147 : W := mkw 0x2b703d8015d25a04 0x02b703d8015d25a0 0xbff1f8003fffdc0b 0xfbff1f8003fffdc0

def z1148 : W := mkw 0x293002401dd03b0c 0x0293002401dd03b0 0xbfc000003ff03f08 0x4bfc000003ff03f0

def z1149 : W := mkw 0x2930000015d01a04 0x02930000015d01a0 0xbff000003ff01c09 0xebff000003ff01c0

def z1150 : W := mkw 0x2b701fc21dd13b4d 0x02b701fc21dd13b4 0xbff11fc63ff73f0d 0xfbff11fc63ff73f0

def z1151 : W := mkw 0x0b3016401dc03108 0x00b3016401dc0310 0xbff01fc03ff03f0d 0xfbff01fc03ff03f0

def z1152 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xffffe007ffffc00b 0xeffffe007ffffc00

def z1153 : W := mkw 0x848fc019222c84a2 0x8848fc019222c84a 0x400e80390008c0f2 0x0400e80390008c0f

def z1154 : W := mkw 0x4f2954a480000000 0x04f2954a48000000 0x4e3fffffc0000007 0xf4e3fffffc000000

def z1155 : W := mkw 0x201022425dc3715d 0x4201022425dc3715 0x5031e7c7df8fe3ff 0xa5031e7c7df8fe3f

def z1156 : W := mkw 0x2b703fc05dd27b1c 0x42b703fc05dd27b1 0xbff1ffc1ffffff3f 0xfbff1ffc1ffffff3

def z1157 : W := mkw 0x02503f4259937b59 0x402503f4259937b5 0xfff1ffc7ffffffff 0xffff1ffc7fffffff

def z1158 : W := mkw 0x0dbfc00036cc0000 0x00dbfc00036cc000 0xbfffe0003fff000b 0xebfffe0003fff000

def z1159 : W := mkw 0x4fedddb580308a20 0x84fedddb580308a2 0xefffffffe0f0ff3f 0xfefffffffe0f0ff3

def z1160 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff09fc03ff8ff0f 0xfbff09fc03ff8ff0

def z1161 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0e18383f0f3cce 0x77e0e18383f0f3cc

def z1162 : W := mkw 0x8dbde00016e6c000 0x08dbde00016e6c00 0x9ff1e0001fffc00b 0xa9ff1e0001fffc00

def z1163 : W := mkw 0x2b701dc015d01b0c 0x02b701dc015d01b0 0xaff018c027701c00 0x5aff018c027701c0

def z1164 : W := mkw 0x0010204250834159 0x4001020425083415 0x4031e7c7c08fc3f7 0xa4031e7c7c08fc3f

def z1165 : W := mkw 0x160b142c230c1482 0x0160b142c230c148 0x7e0f1e3e3f0f1c0e 0xf7e0f1e3e3f0f1c0

def z1166 : W := mkw 0x0200160009003000 0x0020016000900300 0xbfc01e003ff03c0d 0xfbfc01e003ff03c0

def z1167 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xafc0180027703c0c 0x7afc0180027703c0

def z1168 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xfff1ffc7fff73f0f 0xffff1ffc7fff73f0

def z1169 : W := mkw 0x8dbfe04076eec118 0x48dbfe04076eec11 0xbfffe0c0ffffc00b 0xebfffe0c0ffffc00

def z1170 : W := mkw 0x4fedddb582040000 0x04fedddb58204000 0xdfffffffdf070007 0xfdfffffffdf07000

def z1171 : W := mkw 0x2b601d8005501a04 0x02b601d8005501a0 0xaff01fc027f03f0d 0xfaff01fc027f03f0

def z1172 : W := mkw 0x2b701f801dd03a04 0x02b701f801dd03a0 0xbff01e003ff03c0d 0xfbff01e003ff03c0

def z1173 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfff60003f7f000a 0xebfff60003f7f000

def z1174 : W := mkw 0x148f803f222d84e3 0x8148f803f222d84e 0x400f003e000f00c2 0x0400f003e000f00c

def z1175 : W := mkw 0x148f823f2a2da4e3 0x8148f823f2a2da4e 0x500f873f188fe3ff 0xa500f873f188fe3f

def z1176 : W := mkw 0x2b601dc005501b0c 0x02b601dc005501b0 0xafc019c027701f00 0x5afc019c027701f0

def z1177 : W := mkw 0x0010224258836159 0x4001022425883615 0x5031e7c7d88fc3f3 0x85031e7c7d88fc3f

def z1178 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbfc018003f701c00 0x5bfc018003f701c0

def z1179 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x7e0f9e3e3f8ffccf 0xf7e0f9e3e3f8ffcc

def z1180 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff01fc03ff01f01 0xdbff01fc03ff01f0

def z1181 : W := mkw 0x0012224a78abe5fb 0xc0012224a78abe5f 0x10000000188fe3f8 0x010000000188fe3f

def z1182 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x3e0f1e3e3f0f3cc8 0xd3e0f1e3e3f0f3cc

def z1183 : W := mkw 0x2b601f800d503a04 0x02b601f800d503a0 0xbfc01f003ff03f0d 0xfbfc01f003ff03f0

def z1184 : W := mkw 0x160b162e2b0d34c3 0x0160b162e2b0d34c 0x3e0e18383f071c00 0x53e0e18383f071c0

def z1185 : W := mkw 0x4f2954a480000000 0x04f2954a48000000 0x4e3f66fec0000002 0x84e3f66fec000000

def z1186 : W := mkw 0x52401fbf89113ee3 0x852401fbf89113ee 0x40001fffc0003ff4 0x140001fffc0003ff

def z1187 : W := mkw 0x00c6891920388ea2 0x800c6891920388ea 0xe1cf9f3f20f8ffff 0xfe1cf9f3f20f8fff

def z1188 : W := mkw 0x2b703fc01dd27b0c 0x02b703fc01dd27b0 0xfff1ffc7ffffff0f 0xffff1ffc7ffffff0

def z1189 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xfff01fc03ff83fcf 0xffff01fc03ff83fc

def z1190 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff01fc03f703f04 0xdbff01fc03f703f0

def z1191 : W := mkw 0x293002401dd03b0c 0x0293002401dd03b0 0xbff007c03ff03f0d 0xebff007c03ff03f0

def z1192 : W := mkw 0x89b6a00036eec000 0x089b6a00036eec00 0xbffe80003fffc00b 0xebffe80003fffc00

def z1193 : W := mkw 0x2b701fc01dd03b0c 0x02b701fc01dd03b0 0xbff1ffc03ff03f0f 0xfbff1ffc03ff03f0

def z1194 : W := mkw 0x2b703fc25dd37b5d 0x42b703fc25dd37b5 0xfff0ffc7fff0fffd 0xffff0ffc7fff0fff

def z1195 : W := mkw 0x293022425dd37b5d 0x4293022425dd37b5 0xfff1e7c7ffffffff 0xefff1e7c7fffffff

def z1196 : W := mkw 0x0086800820288482 0x0008680082028848 0xe1ce993920f8ffff 0x7e1ce993920f8fff

def z1197 : W := mkw 0x8dbfe00036eec000 0x08dbfe00036eec00 0xbfffe0003f770003 0xebfffe0003f77000

def z1198 : W := mkw 0x0970290014d24a00 0x00970290014d24a0 0xfff1f9013fffffff 0xffff1f9013ffffff

def z1199 : W := mkw 0x72401fff89113fcf 0x072401fff89113fc 0x40001fffc0003fc4 0x140001fffc0003fc

def z1200 : W := mkw 0x3b701fe61dd13b4d 0x03b701fe61dd13b4 0xbff01fc63ff03f0d 0xfbff01fc63ff03f0

def z1201 : W := mkw 0x2b601fc24d513b5d 0x42b601fc24d513b5 0xefc01fc7e7703ff4 0x5efc01fc7e7703ff

def z1202 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xffffffffff00000f 0xfffffffffff00000

def z1203 : W := mkw 0x8dafc000266c8000 0x08dafc000266c800 0xbfce00003f7f0008 0x4bfce00003f7f000

def z1204 : W := mkw 0x4fedddb580000000 0x04fedddb58000000 0xcfffffffc008c0f7 0xfcfffffffc008c0f

def z1205 : W := mkw 0xc9f4e99194f2ca20 0x8c9f4e99194f2ca2 0x81f0e1c1c0f0c331 0x081f0e1c1c0f0c33

def z1206 : W := mkw 0x0010224258836159 0x4001022425883615 0x1031e7c7d88fe3f9 0x81031e7c7d88fe3f

def z1207 : W := mkw 0x2b701fe41dd03b0c 0x02b701fe41dd03b0 0xfff01ffe3ff03f0d 0xffff01ffe3ff03f0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z6,z0,z1,z2,z3,z4,z7])],[(0,[z0,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z8,z7]),(0,[z0,z1,z9,z2,z3,z4,z7]),(0,[z0,z1,z2,z10,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z11,z7])],[(0,[z0,z1,z2,z12,z3,z4,z7]),(0,[z0,z1,z13,z2,z3,z4,z7]),(0,[z0,z0,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z10,z14,z4,z7]),(0,[z15,z0,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z3,z4,z17,z7]),(0,[z18,z0,z1,z2,z3,z4,z19]),(0,[z0,z20,z1,z2,z4,z21,z7]),(0,[z0,z1,z22,z2,z4,z21,z7]),(0,[z0,z1,z2,z3,z4,z23,z7])],[(0,[z0,z1,z2,z3,z4,z7,z24]),(0,[z25,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z26])],[(0,[z0,z1,z2,z3,z27,z4,z7]),(0,[z0,z1,z2,z3,z28,z4,z7])],[(0,[z0,z1,z29,z2,z3,z4,z7]),(0,[z30,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z31,z4,z7])],[(0,[z0,z32,z1,z2,z3,z4,z7]),(0,[z0,z1,z33,z2,z3,z4,z7]),(0,[z0,z1,z2,z34,z3,z4,z7]),(0,[z0,z1,z2,z3,z35,z4,z7]),(1,[z0,z1,z36,z3,z37,z7]),(0,[z0,z1,z2,z10,z3,z38,z7]),(0,[z0,z1,z2,z3,z39,z4,z7])],[(1,[z0,z1,z2,z3,z4,z40]),(0,[z41,z0,z1,z2,z3,z4,z40]),(0,[z0,z32,z1,z2,z14,z4,z7]),(0,[z42,z0,z1,z2,z3,z4,z7]),(0,[z43,z0,z1,z44,z3,z4,z7]),(0,[z0,z45,z1,z2,z46,z4,z7]),(0,[z0,z47,z1,z2,z3,z48,z7]),(0,[z0,z1,z49,z3,z4,z50,z7]),(0,[z0,z1,z2,z10,z4,z21,z7])]],
   [[(0,[z51,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z52,z16,z4,z7]),(0,[z0,z1,z2,z3,z53,z4,z7]),(0,[z0,z45,z1,z2,z3,z54,z7]),(0,[z0,z1,z2,z3,z4,z55,z56]),(0,[z0,z1,z2,z3,z57,z4,z7]),(0,[z0,z1,z58,z2,z3,z37,z7]),(0,[z0,z1,z59,z2,z3,z4,z7]),(0,[z0,z1,z60,z2,z10,z4,z7]),(0,[z0,z1,z2,z4,z21,z7,z61]),(0,[z0,z1,z2,z62,z3,z4,z7]),(0,[z0,z63,z1,z2,z3,z4,z7])],[(0,[z64,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z65,z16,z4,z7]),(1,[z15,z1,z2,z3,z4,z19]),(0,[z0,z20,z1,z2,z3,z4,z66]),(0,[z0,z20,z1,z2,z67,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z68])],[(0,[z0,z1,z2,z3,z69,z4,z7]),(0,[z0,z1,z70,z2,z3,z4,z7]),(0,[z15,z0,z1,z71,z3,z4,z7]),(0,[z0,z1,z72,z2,z3,z4,z7]),(0,[z0,z20,z1,z73,z2,z4,z7]),(0,[z0,z1,z74,z2,z3,z4,z7]),(0,[z0,z1,z22,z73,z2,z4,z7]),(0,[z0,z1,z2,z3,z75,z11,z7])],[(0,[z0,z1,z58,z76,z3,z4,z7]),(0,[z77,z0,z1,z2,z16,z4,z7]),(1,[z1,z2,z16,z14,z4,z7]),(0,[z0,z1,z78,z2,z3,z4,z7]),(0,[z0,z79,z1,z49,z2,z3,z4]),(0,[z0,z80,z1,z2,z3,z4,z7]),(0,[z0,z1,z81,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z50,z7]),(0,[z0,z1,z2,z3,z4,z21,z7])],[(0,[z0,z1,z36,z2,z16,z4,z7]),(0,[z82,z1,z2,z3,z83,z4,z7]),(0,[z0,z1,z84,z2,z3,z4,z7]),(0,[z0,z1,z3,z85,z4,z37,z7])],[(1,[z0,z1,z2,z86,z4,z7]),(0,[z0,z1,z2,z3,z4,z87,z7]),(0,[z0,z1,z88,z2,z3,z4,z7]),(0,[z0,z89,z1,z2,z3,z4,z7])],[(1,[z0,z1,z2,z90,z4,z7]),(0,[z41,z0,z1,z2,z90,z4,z7]),(0,[z91,z0,z1,z2,z92,z4,z7]),(0,[z0,z93,z1,z2,z3,z4,z7]),(1,[z0,z79,z2,z3,z4,z94]),(0,[z0,z1,z95,z2,z3,z4,z7])],[(0,[z96,z0,z1,z2,z3,z4,z7]),(0,[z91,z97,z0,z1,z2,z3,z7]),(1,[z0,z1,z2,z98,z4,z7]),(0,[z0,z1,z2,z3,z99,z4,z7]),(0,[z0,z1,z2,z3,z100,z4,z7]),(0,[z0,z1,z2,z101,z3,z4,z7])]],
   [[(0,[z43,z0,z1,z2,z102,z4,z7]),(1,[z0,z1,z2,z103,z4,z7]),(0,[z0,z1,z2,z3,z4,z5,z7]),(0,[z0,z1,z2,z3,z104,z4,z7]),(0,[z0,z1,z105,z2,z52,z4,z7]),(0,[z0,z1,z106,z2,z3,z4,z7])],[(0,[z43,z0,z1,z2,z16,z4,z7]),(0,[z0,z1,z60,z2,z16,z4,z7])],[(1,[z0,z1,z2,z107,z4,z7]),(0,[z108,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z109])],[(0,[z0,z1,z2,z110,z14,z4,z7]),(0,[z0,z1,z111,z2,z3,z4,z7]),(0,[z0,z112,z1,z2,z3,z4,z7]),(0,[z113,z0,z1,z2,z3,z4,z7]),(0,[z114,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z115,z7]),(0,[z0,z1,z2,z3,z4,z7,z116])],[(0,[z0,z1,z2,z3,z117,z4,z7]),(0,[z0,z112,z1,z2,z14,z4,z7]),(0,[z0,z1,z118,z2,z4,z7,z56]),(0,[z0,z1,z2,z119,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z40]),(0,[z0,z120,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z75,z4,z7]),(0,[z0,z121,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z122,z3,z4,z7]),(0,[z0,z112,z1,z123,z2,z3,z4]),(1,[z0,z1,z124,z125,z4,z7])],[(0,[z0,z1,z126,z44,z3,z4,z7]),(0,[z97,z82,z0,z1,z2,z3,z7]),(0,[z0,z112,z2,z3,z4,z55,z7])],[(0,[z0,z1,z2,z127,z3,z4,z7]),(0,[z0,z1,z2,z14,z128,z4,z7]),(0,[z0,z1,z2,z16,z4,z7,z129]),(0,[z0,z1,z130,z2,z3,z4,z7]),(0,[z0,z131,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z132]),(1,[z0,z1,z73,z2,z4,z61]),(0,[z0,z1,z2,z3,z4,z7,z61])]],
   [[(1,[z0,z1,z133,z3,z4,z7]),(0,[z41,z0,z1,z133,z3,z4,z7]),(0,[z0,z1,z2,z67,z16,z4,z7]),(0,[z0,z1,z2,z134,z3,z4,z7]),(0,[z18,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z135,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z136,z4,z7]),(1,[z0,z1,z2,z3,z137,z7]),(0,[z0,z138,z1,z2,z3,z137,z7]),(0,[z0,z1,z2,z139,z3,z4,z7]),(0,[z0,z1,z2,z140,z3,z4,z7])],[(0,[z0,z141,z1,z2,z3,z4,z7]),(0,[z18,z0,z1,z2,z14,z4,z7]),(0,[z142,z0,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z143]),(0,[z0,z1,z2,z144,z3,z4,z7]),(0,[z145,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z75,z4,z146,z7])],[(0,[z97,z0,z1,z2,z14,z4,z7]),(1,[z0,z1,z2,z16,z17,z7]),(0,[z147,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z148,z7]),(0,[z0,z149,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z150,z4,z7])],[(0,[z0,z1,z151,z2,z3,z4,z7]),(0,[z15,z1,z2,z3,z4,z19,z7]),(1,[z0,z1,z2,z3,z54,z7]),(0,[z0,z1,z152,z2,z3,z4,z7]),(0,[z0,z1,z73,z2,z10,z4,z7])],[(0,[z0,z1,z2,z98,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z19,z153]),(0,[z0,z1,z154,z2,z3,z4,z7])],[(0,[z0,z47,z2,z3,z4,z155,z7])],[(0,[z0,z1,z156,z2,z3,z4,z7]),(0,[z157,z0,z1,z2,z3,z4,z7]),(0,[z0,z158,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z140,z4,z21,z7]),(0,[z0,z159,z1,z2,z3,z4,z7])],[(0,[z160,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z161]),(0,[z0,z1,z73,z2,z3,z4,z21])]],
   [[(0,[z0,z1,z2,z162,z3,z4,z7]),(0,[z0,z1,z126,z2,z16,z4,z7]),(0,[z0,z1,z163,z2,z3,z4,z7]),(0,[z164,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z49,z2,z140,z3,z4])],[(0,[z0,z165,z1,z2,z3,z4,z7]),(0,[z166,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z48,z4,z7]),(0,[z91,z0,z1,z2,z3,z115,z7]),(0,[z0,z1,z2,z3,z4,z167,z7]),(0,[z0,z1,z2,z3,z4,z168,z7]),(0,[z0,z2,z3,z4,z55,z7,z94]),(0,[z0,z169,z1,z2,z3,z4,z7]),(0,[z0,z1,z73,z2,z3,z4,z153])],[(0,[z0,z170,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z14,z4,z7,z171]),(0,[z0,z45,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z172,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z173,z7])],[(0,[z0,z174,z1,z2,z3,z4,z7]),(0,[z0,z1,z118,z2,z3,z4,z7]),(0,[z0,z1,z2,z175,z3,z4,z7])],[(0,[z0,z1,z73,z2,z16,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z176]),(0,[z177,z0,z1,z2,z3,z4,z7])],[(0,[z178,z0,z1,z123,z3,z4,z7]),(0,[z0,z20,z1,z124,z2,z4,z7]),(0,[z0,z1,z2,z140,z3,z4,z94]),(0,[z0,z1,z123,z2,z140,z3,z4])],[(0,[z0,z1,z2,z14,z4,z7,z94]),(1,[z0,z1,z118,z2,z4,z7])],[(0,[z0,z20,z1,z2,z3,z4,z179]),(0,[z0,z1,z2,z3,z4,z180,z7])]],
   [[(0,[z181,z0,z1,z2,z3,z4,z7]),(0,[z182,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z4,z7,z56]),(1,[z0,z1,z2,z3,z183,z7]),(0,[z0,z138,z1,z2,z3,z183,z7]),(0,[z0,z1,z2,z3,z48,z115,z7])],[(0,[z181,z0,z1,z2,z14,z4,z7]),(0,[z0,z126,z2,z52,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z184,z7]),(0,[z0,z1,z58,z2,z3,z4,z7])],[(1,[z43,z1,z44,z3,z4,z7]),(0,[z185,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z58,z2,z14,z4,z7]),(0,[z0,z186,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z187,z3,z4,z7]),(0,[z0,z138,z1,z123,z3,z4,z7]),(0,[z0,z1,z2,z188,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z189])],[(1,[z0,z1,z190,z2,z3,z7]),(0,[z0,z1,z2,z3,z191,z4,z7]),(0,[z0,z1,z2,z14,z4,z55,z7]),(0,[z0,z1,z2,z192,z3,z4,z7]),(0,[z0,z1,z193,z2,z16,z4,z7]),(0,[z0,z1,z194,z2,z3,z4,z7]),(0,[z195,z0,z1,z2,z3,z4,z7])],[(0,[z41,z181,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z196,z4,z7]),(0,[z0,z1,z190,z2,z76,z3,z7]),(0,[z91,z0,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z192,z14,z4,z7]),(0,[z0,z1,z194,z2,z14,z4,z7]),(0,[z0,z1,z2,z16,z4,z155,z7]),(1,[z0,z33,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z197,z4,z7])],[(0,[z181,z0,z32,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z198]),(0,[z91,z0,z1,z199,z3,z4,z7]),(0,[z0,z45,z1,z2,z3,z200,z7]),(0,[z201,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z50,z55])],[(0,[z64,z0,z1,z76,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z202,z7]),(0,[z0,z203,z1,z2,z3,z4,z7]),(0,[z0,z1,z204,z2,z3,z4,z7])],[(0,[z0,z1,z2,z16,z4,z7,z153]),(0,[z91,z82,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z7,z205]),(0,[z0,z1,z2,z3,z4,z206,z7]),(0,[z178,z0,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z3,z4,z207,z7]),(0,[z0,z1,z49,z2,z3,z4,z19])],[(1,[z181,z32,z2,z3,z4,z7]),(0,[z208,z0,z1,z2,z3,z4,z7]),(0,[z0,z112,z1,z49,z2,z3,z4]),(1,[z0,z1,z2,z10,z38,z7]),(1,[z0,z1,z2,z140,z4,z21]),(0,[z209,z0,z1,z2,z3,z4,z7])],[(1,[z0,z1,z2,z210,z4,z7]),(0,[z0,z1,z2,z211,z3,z4,z7]),(1,[z0,z1,z2,z110,z3,z4]),(0,[z82,z0,z1,z2,z16,z4,z7]),(0,[z0,z1,z212,z2,z3,z4,z7]),(0,[z0,z1,z2,z213,z3,z4,z7]),(0,[z0,z1,z214,z2,z3,z4,z7]),(0,[z0,z1,z123,z73,z2,z3,z4]),(1,[z0,z1,z60,z2,z115,z7])],[(0,[z0,z1,z2,z14,z4,z37,z7]),(0,[z0,z1,z2,z3,z4,z215,z7]),(0,[z0,z1,z2,z216,z3,z4,z7]),(0,[z0,z1,z217,z2,z3,z4,z7]),(1,[z0,z20,z2,z67,z4,z7]),(0,[z0,z1,z2,z218,z3,z4,z7])],[(0,[z0,z1,z219,z2,z3,z4,z7]),(1,[z0,z1,z2,z102,z4,z7])],[(0,[z41,z0,z1,z2,z16,z4,z7]),(1,[z0,z1,z2,z16,z4,z7]),(0,[z0,z138,z1,z2,z16,z4,z7]),(0,[z0,z1,z123,z2,z3,z4,z19]),(0,[z0,z112,z1,z2,z3,z4,z55])],[(0,[z0,z220,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z221,z7]),(1,[z0,z222,z2,z3,z4,z7]),(0,[z0,z1,z223,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z224,z4,z7]),(1,[z0,z1,z2,z4,z146,z7])],[(0,[z0,z225,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z3,z4,z7]),(0,[z0,z1,z226,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z227,z4,z7])]],
   [[(0,[z0,z1,z2,z228,z3,z4,z7]),(0,[z0,z1,z2,z14,z4,z19,z7]),(0,[z0,z225,z1,z2,z14,z4,z7]),(0,[z91,z0,z1,z2,z3,z4,z229]),(0,[z0,z1,z2,z3,z230,z4,z7]),(0,[z15,z0,z1,z2,z140,z3,z4]),(0,[z0,z1,z231,z2,z3,z4,z7]),(0,[z0,z1,z60,z2,z4,z115,z7]),(0,[z0,z1,z232,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z233])],[(0,[z0,z1,z2,z3,z4,z7,z234]),(0,[z0,z1,z124,z2,z16,z4,z7]),(1,[z0,z1,z235,z2,z4,z7]),(0,[z0,z1,z236,z2,z3,z4,z7]),(0,[z0,z1,z237,z2,z3,z4,z7]),(0,[z238,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z239,z4,z7])],[(0,[z0,z1,z2,z16,z53,z4,z7]),(0,[z0,z1,z240,z2,z3,z4,z7]),(0,[z0,z1,z2,z140,z3,z4,z55]),(0,[z0,z1,z2,z3,z4,z7,z241]),(0,[z242,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z10,z3,z115,z7])],[(0,[z243,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z44,z2,z14,z4,z7]),(1,[z77,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z14,z4,z244,z7]),(0,[z0,z1,z22,z3,z245,z4,z7]),(0,[z0,z1,z73,z2,z3,z4,z61])],[(0,[z0,z2,z67,z3,z46,z4,z7]),(0,[z0,z1,z2,z3,z4,z246,z7]),(0,[z0,z1,z247,z2,z3,z4,z7])],[(0,[z0,z1,z2,z16,z4,z50,z7]),(0,[z0,z1,z2,z16,z4,z21,z7]),(0,[z91,z0,z1,z36,z2,z3,z7]),(0,[z0,z248,z1,z2,z3,z4,z7]),(0,[z0,z1,z249,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z250]),(0,[z0,z1,z251,z2,z3,z4,z7])],[(0,[z0,z1,z76,z3,z4,z50,z7]),(0,[z252,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z253,z75,z4,z7])],[(0,[z254,z0,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z255,z7]),(0,[z0,z256,z1,z2,z16,z4,z7]),(0,[z257,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z258,z2,z52,z4,z7]),(0,[z0,z1,z2,z259,z3,z4,z7]),(1,[z0,z1,z2,z3,z200,z7]),(0,[z0,z1,z2,z3,z260,z4,z7]),(0,[z0,z1,z2,z3,z4,z261,z7]),(0,[z0,z1,z2,z3,z4,z7,z153])],[(0,[z0,z262,z1,z2,z3,z4,z7]),(0,[z0,z263,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z264,z7])],[(0,[z0,z1,z265,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z266,z7])],[(0,[z41,z1,z267,z2,z3,z4,z7]),(0,[z0,z1,z2,z268,z3,z4,z7]),(0,[z0,z269,z1,z2,z3,z4,z7]),(0,[z0,z1,z123,z49,z3,z4,z7])],[(0,[z0,z267,z2,z3,z4,z155,z7]),(0,[z0,z1,z2,z268,z14,z4,z7]),(0,[z0,z1,z270,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z38,z4,z271])],[(0,[z96,z1,z2,z16,z3,z4,z7]),(0,[z0,z1,z2,z16,z4,z115,z7]),(0,[z0,z1,z2,z3,z4,z19,z94])],[(1,[z0,z272,z1,z2,z3,z7]),(0,[z273,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z14,z245,z4,z7]),(0,[z0,z1,z274,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z275]),(0,[z0,z1,z2,z3,z4,z276,z7]),(0,[z0,z1,z49,z2,z3,z4,z7])],[(0,[z0,z1,z2,z90,z3,z4,z7]),(0,[z0,z1,z49,z2,z14,z4,z7]),(0,[z0,z222,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z11,z129]),(0,[z0,z277,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z278,z4,z7]),(0,[z0,z1,z36,z2,z3,z37,z7])]],
   [[(0,[z0,z1,z2,z3,z3,z4,z7]),(0,[z0,z1,z279,z2,z3,z4,z7]),(0,[z82,z0,z1,z2,z3,z83,z7]),(0,[z0,z20,z2,z67,z3,z4,z7]),(0,[z0,z1,z2,z3,z280,z4,z7]),(0,[z0,z1,z2,z3,z281,z4,z7])],[(0,[z282,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z283,z3,z4,z7]),(0,[z0,z1,z190,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z14,z4,z7]),(0,[z0,z1,z2,z16,z4,z7,z61]),(0,[z0,z1,z163,z2,z52,z3,z4]),(0,[z0,z45,z1,z22,z2,z4,z7]),(0,[z0,z1,z2,z284,z3,z4,z7]),(0,[z0,z1,z58,z2,z3,z155,z7]),(0,[z0,z285,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z2,z3,z4,z7]),(0,[z0,z1,z73,z2,z3,z4,z94])],[(0,[z286,z0,z1,z2,z3,z4,z7]),(0,[z64,z43,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z14,z46,z4,z7]),(0,[z0,z1,z2,z287,z16,z4,z7]),(0,[z0,z1,z2,z3,z288,z4,z7]),(0,[z0,z1,z2,z3,z4,z289,z7]),(0,[z0,z1,z123,z2,z3,z4,z7])],[(0,[z0,z1,z290,z2,z3,z4,z7]),(0,[z291,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z292,z7]),(0,[z64,z0,z1,z2,z14,z4,z7]),(0,[z178,z0,z1,z3,z4,z50,z7]),(0,[z0,z1,z2,z3,z4,z293,z7]),(0,[z0,z1,z58,z2,z3,z85,z7]),(0,[z0,z1,z2,z3,z4,z294,z7])],[(0,[z0,z79,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z295]),(0,[z0,z1,z2,z3,z4,z296,z7]),(0,[z0,z1,z2,z3,z4,z297,z7]),(0,[z0,z1,z298,z2,z3,z4,z7]),(0,[z0,z1,z194,z2,z3,z7,z153])],[(0,[z181,z0,z1,z2,z228,z4,z7]),(0,[z82,z0,z1,z2,z98,z4,z7]),(0,[z299,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z300,z2,z3,z4,z7]),(0,[z97,z0,z1,z2,z3,z48,z7])]],
   [[(0,[z0,z301,z1,z2,z3,z4,z7]),(1,[z0,z1,z22,z245,z4,z7]),(0,[z0,z1,z302,z2,z3,z4,z7])],[(1,[z0,z1,z2,z3,z303,z7]),(0,[z41,z0,z1,z2,z3,z303,z7]),(0,[z304,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z4,z7,z161]),(0,[z82,z0,z1,z2,z305,z4,z7]),(0,[z0,z1,z2,z306,z3,z4,z7]),(0,[z0,z1,z2,z3,z307,z4,z7])],[(0,[z18,z0,z1,z2,z308,z4,z7]),(0,[z0,z138,z1,z3,z4,z50,z7]),(0,[z0,z1,z2,z3,z4,z309,z7]),(0,[z0,z1,z22,z124,z3,z4,z7]),(0,[z0,z1,z73,z2,z3,z4,z11])],[(0,[z96,z0,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z3,z4,z310,z7])],[(0,[z311,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z44,z52,z3,z4,z7]),(1,[z0,z1,z2,z305,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z312]),(0,[z0,z1,z313,z2,z3,z4,z7])],[(0,[z0,z1,z2,z14,z85,z4,z7]),(0,[z314,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z14,z4,z315,z7]),(0,[z0,z45,z20,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z316]),(0,[z0,z1,z317,z2,z3,z4,z7]),(0,[z318,z0,z1,z2,z3,z4,z7])],[(0,[z319,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z267,z2,z16,z4,z7]),(1,[z97,z0,z2,z3,z48,z7]),(0,[z320,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z321,z2,z3,z4,z7])]],
   [[(1,[z0,z1,z2,z99,z4,z7]),(0,[z0,z1,z2,z3,z4,z55,z19]),(0,[z0,z1,z322,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z323,z4,z7]),(0,[z0,z1,z2,z14,z4,z324,z7]),(0,[z1,z2,z16,z3,z14,z4,z7]),(0,[z0,z1,z325,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z326,z4,z7]),(0,[z82,z0,z47,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z327,z7])],[(0,[z0,z1,z2,z3,z128,z4,z7]),(0,[z0,z1,z325,z2,z14,z4,z7]),(1,[z91,z1,z2,z3,z315,z7]),(0,[z0,z1,z2,z328,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z329]),(0,[z0,z1,z330,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z331,z4,z7])],[(0,[z332,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z333,z7]),(0,[z0,z1,z334,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z11,z7,z153])],[(0,[z0,z1,z2,z140,z14,z4,z7]),(0,[z0,z335,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z336]),(0,[z0,z1,z337,z2,z3,z4,z7]),(0,[z0,z1,z124,z2,z245,z4,z7]),(0,[z0,z1,z2,z3,z338,z4,z7])],[(1,[z0,z1,z2,z117,z4,z7]),(0,[z339,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z340,z2,z3,z4])],[(0,[z0,z1,z341,z2,z76,z3,z7]),(0,[z18,z0,z1,z2,z3,z4,z129]),(0,[z342,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z343,z4,z7])],[(0,[z0,z1,z344,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z3,z17,z7]),(0,[z178,z0,z1,z126,z3,z4,z7]),(0,[z0,z345,z1,z2,z3,z4,z7]),(0,[z0,z346,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z347,z4,z7])]],
   [[(0,[z0,z1,z2,z348,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z271]),(0,[z0,z1,z2,z253,z3,z4,z7])],[(0,[z97,z0,z267,z2,z3,z4,z7]),(1,[z0,z45,z2,z46,z4,z7])],[(0,[z349,z0,z1,z2,z3,z4,z7]),(0,[z350,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z351,z2,z3,z4,z7])],[(0,[z352,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z92,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z353,z7]),(0,[z0,z1,z2,z3,z4,z7,z354]),(0,[z0,z1,z36,z58,z3,z4,z7])],[(0,[z0,z1,z2,z3,z303,z4,z7]),(0,[z0,z1,z2,z3,z355,z4,z7]),(0,[z356,z0,z1,z2,z3,z4,z7]),(0,[z15,z18,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z129,z153]),(0,[z0,z138,z1,z126,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z54,z7])],[(0,[z0,z1,z2,z3,z357,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z358]),(0,[z359,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z360])],[(0,[z0,z1,z44,z3,z4,z37,z7]),(0,[z0,z1,z2,z3,z4,z7,z361]),(0,[z0,z1,z362,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z363,z7])],[(0,[z0,z32,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z3,z364,z4,z7]),(0,[z0,z1,z2,z3,z4,z365,z7]),(0,[z0,z1,z2,z3,z4,z366,z7])]],
   [[(0,[z15,z0,z1,z2,z99,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z367]),(0,[z0,z1,z2,z3,z368,z4,z7]),(0,[z0,z1,z36,z2,z3,z4,z7]),(0,[z369,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z370,z7])],[(0,[z91,z0,z1,z2,z107,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z94])],[(0,[z0,z371,z1,z2,z3,z4,z7])],[(0,[z0,z1,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z372,z3,z4,z7])],[],[(0,[z0,z373,z1,z2,z3,z4,z7]),(0,[z43,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z155,z315,z7]),(0,[z0,z1,z2,z3,z4,z374,z7]),(0,[z0,z1,z60,z2,z3,z4,z7])],[(0,[z0,z1,z375,z2,z3,z4,z7]),(0,[z0,z1,z60,z2,z14,z4,z7]),(0,[z376,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z55,z7]),(0,[z0,z1,z377,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z378]),(0,[z0,z1,z2,z76,z3,z4,z7]),(0,[z0,z1,z379,z2,z3,z4,z7]),(0,[z0,z1,z2,z380,z3,z4,z7]),(0,[z0,z1,z2,z3,z38,z4,z381])]],
   [[(0,[z181,z0,z267,z2,z3,z4,z7]),(0,[z0,z1,z2,z76,z14,z4,z7]),(0,[z0,z1,z123,z76,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z382,z7]),(0,[z383,z0,z1,z2,z3,z4,z7])],[(0,[z64,z0,z1,z2,z384,z4,z7]),(0,[z0,z1,z2,z3,z4,z183,z7]),(0,[z0,z1,z49,z2,z3,z4,z50]),(0,[z0,z1,z2,z10,z38,z4,z7])],[(0,[z0,z1,z385,z2,z3,z4,z7]),(0,[z0,z1,z60,z2,z3,z38,z7])],[(0,[z0,z1,z2,z386,z3,z4,z7])],[(0,[z0,z1,z2,z14,z4,z155,z7]),(0,[z0,z112,z1,z2,z16,z4,z7]),(1,[z0,z1,z2,z92,z4,z7]),(0,[z387,z0,z1,z2,z3,z4,z7]),(0,[z0,z79,z1,z2,z3,z4,z94]),(0,[z0,z1,z2,z4,z7,z241,z56])],[(0,[z96,z77,z1,z2,z3,z4,z7]),(0,[z388,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z235,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z389,z4,z7]),(0,[z0,z1,z2,z3,z38,z4,z7]),(0,[z0,z1,z390,z2,z3,z4,z7]),(0,[z0,z1,z391,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z392,z7]),(1,[z0,z1,z393,z3,z4,z7]),(1,[z0,z1,z2,z394,z4,z7]),(0,[z0,z1,z2,z395,z3,z4,z7]),(1,[z0,z1,z105,z2,z4,z7]),(0,[z0,z1,z72,z2,z52,z3,z4]),(0,[z0,z396,z1,z2,z3,z4,z7]),(0,[z0,z1,z123,z2,z3,z4,z50]),(0,[z0,z1,z397,z2,z3,z4,z7])],[(0,[z64,z1,z2,z76,z3,z4,z7]),(0,[z0,z1,z2,z398,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z399,z3,z4,z7])],[(0,[z18,z0,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z134,z16,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z400]),(0,[z0,z1,z2,z3,z4,z401,z7]),(0,[z0,z1,z2,z3,z4,z271,z7])],[(0,[z97,z0,z1,z2,z16,z4,z7]),(0,[z0,z1,z402,z2,z3,z4,z7]),(0,[z0,z1,z403,z2,z3,z4,z7])],[(0,[z0,z1,z341,z2,z3,z4,z7]),(0,[z404,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z14,z4,z7]),(0,[z0,z1,z2,z14,z4,z11,z7]),(0,[z0,z1,z2,z3,z4,z19,z7])],[(0,[z0,z1,z2,z3,z4,z405,z7]),(0,[z0,z1,z2,z3,z4,z7,z406]),(0,[z0,z407,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z408]),(0,[z0,z409,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z410,z4,z7]),(0,[z0,z1,z411,z2,z3,z4,z7]),(0,[z0,z1,z105,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z412,z4,z7])],[(0,[z0,z1,z411,z2,z14,z4,z7]),(1,[z0,z1,z325,z2,z3,z4]),(0,[z0,z1,z2,z413,z3,z4,z7]),(0,[z0,z1,z414,z2,z3,z4,z7]),(0,[z415,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z416,z3,z4,z7])],[(0,[z417,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z83,z4,z7]),(0,[z0,z1,z2,z3,z4,z418,z7])]],
   [[(0,[z0,z1,z419,z2,z3,z4,z7]),(0,[z0,z1,z22,z2,z245,z4,z7]),(0,[z0,z1,z2,z3,z420,z4,z7]),(0,[z0,z1,z73,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z421,z4,z7])],[(0,[z0,z1,z2,z16,z221,z4,z7]),(0,[z0,z1,z2,z3,z422,z4,z7]),(0,[z0,z1,z2,z3,z4,z423,z7]),(1,[z0,z1,z123,z3,z4,z56]),(0,[z0,z1,z73,z2,z140,z4,z7])],[(0,[z0,z424,z1,z2,z3,z4,z7]),(1,[z64,z1,z76,z3,z4,z7]),(0,[z0,z165,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z3,z308,z4,z7])],[(0,[z91,z0,z33,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z425,z7]),(0,[z0,z1,z2,z426,z3,z4,z7])],[(0,[z0,z1,z427,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z75,z4,z153])],[(0,[z0,z428,z1,z2,z3,z4,z7]),(0,[z0,z20,z1,z2,z46,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z429]),(0,[z0,z1,z2,z3,z4,z7,z430])],[(1,[z0,z1,z2,z110,z14,z4]),(0,[z0,z431,z1,z2,z3,z4,z7]),(0,[z0,z1,z325,z2,z3,z14,z4]),(0,[z0,z1,z2,z3,z107,z4,z7]),(0,[z15,z0,z1,z2,z394,z4,z7])],[(0,[z0,z431,z1,z2,z14,z4,z7]),(0,[z0,z1,z193,z2,z3,z4,z7]),(0,[z0,z1,z432,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z433,z7]),(0,[z0,z1,z2,z3,z434,z4,z7]),(0,[z435,z0,z1,z2,z3,z4,z7]),(0,[z15,z0,z1,z73,z2,z3,z4]),(0,[z0,z1,z36,z2,z3,z155,z7])],[(0,[z181,z0,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z3,z4,z436,z7]),(0,[z0,z1,z2,z3,z4,z437,z7])],[],[(0,[z82,z0,z1,z58,z2,z3,z7]),(0,[z15,z0,z1,z2,z3,z4,z19]),(0,[z0,z45,z1,z2,z67,z4,z7]),(1,[z0,z1,z2,z3,z4,z381])],[(0,[z0,z1,z2,z384,z3,z4,z7]),(0,[z0,z1,z438,z2,z3,z4,z7]),(0,[z91,z0,z1,z2,z16,z4,z7]),(0,[z0,z1,z194,z2,z16,z4,z7]),(0,[z178,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z439,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z440,z4,z7]),(0,[z0,z1,z36,z2,z3,z85,z7])],[(0,[z178,z0,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z3,z4,z129,z94]),(0,[z178,z0,z1,z2,z3,z4,z441]),(0,[z0,z1,z2,z4,z115,z21,z7]),(0,[z0,z1,z194,z2,z3,z75,z7])],[(0,[z0,z272,z1,z267,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z442,z7]),(0,[z82,z0,z1,z2,z3,z4,z7]),(0,[z443,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z444,z3,z4,z7]),(0,[z445,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z46,z4,z7]),(0,[z0,z1,z2,z446,z3,z4,z7]),(0,[z0,z47,z1,z2,z3,z4,z7]),(0,[z0,z1,z73,z2,z4,z115,z7])],[(1,[z41,z267,z2,z3,z4,z7]),(0,[z0,z47,z1,z2,z14,z4,z7]),(0,[z0,z1,z123,z2,z14,z4,z7]),(0,[z0,z1,z2,z199,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z447,z7])]],
   [[(0,[z82,z0,z1,z2,z3,z315,z7]),(1,[z0,z1,z448,z3,z4,z7]),(0,[z0,z1,z449,z2,z3,z4,z7])],[(0,[z41,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z7]),(0,[z0,z138,z1,z2,z3,z4,z7]),(0,[z450,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z125,z3,z245,z4,z7]),(0,[z451,z0,z1,z2,z3,z4,z7])],[(0,[z43,z0,z1,z76,z3,z4,z7]),(1,[z0,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z3,z221,z4,z7]),(1,[z82,z1,z2,z3,z83,z7]),(1,[z0,z1,z2,z3,z4,z441]),(0,[z0,z1,z2,z452,z3,z4,z7]),(0,[z0,z1,z453,z2,z3,z4,z7]),(0,[z0,z1,z73,z2,z4,z7,z61])],[(1,[z0,z1,z199,z3,z4,z7]),(0,[z82,z0,z1,z2,z3,z38,z7]),(0,[z0,z1,z454,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z455,z7]),(0,[z1,z44,z2,z76,z3,z4,z7]),(0,[z18,z0,z1,z2,z86,z4,z7]),(0,[z0,z1,z2,z3,z456,z4,z7])],[(0,[z457,z0,z1,z2,z3,z4,z7]),(0,[z0,z32,z2,z3,z4,z155,z7]),(0,[z0,z1,z2,z394,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z458,z7]),(0,[z0,z1,z2,z3,z38,z155,z7]),(0,[z0,z1,z124,z2,z3,z4,z7])],[(0,[z41,z0,z32,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z459,z7]),(1,[z0,z138,z126,z3,z4,z7]),(0,[z0,z1,z2,z3,z460,z4,z7]),(0,[z0,z1,z235,z2,z4,z7,z94]),(0,[z0,z461,z1,z2,z3,z4,z7])],[(0,[z0,z1,z76,z52,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z462])]],
   [[(0,[z463,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z464,z2,z3,z4,z7]),(0,[z465,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z315,z7]),(0,[z0,z1,z2,z3,z4,z7,z381])],[(0,[z0,z466,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z467,z7])],[(0,[z0,z1,z44,z2,z16,z4,z7]),(0,[z0,z1,z2,z16,z4,z7,z94]),(0,[z0,z1,z468,z2,z3,z4,z7]),(0,[z0,z1,z469,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z470,z7]),(0,[z0,z1,z2,z3,z4,z7,z471]),(0,[z0,z1,z124,z2,z4,z21,z7]),(0,[z472,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z473])],[(0,[z474,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z475,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z324,z7]),(0,[z0,z256,z1,z2,z3,z4,z7]),(0,[z0,z476,z1,z2,z3,z4,z7]),(1,[z0,z1,z9,z3,z4,z7]),(0,[z477,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z478,z7]),(0,[z0,z479,z1,z2,z3,z4,z7]),(0,[z97,z0,z2,z3,z48,z4,z7]),(0,[z0,z1,z49,z2,z3,z4,z56])],[(1,[z0,z1,z2,z3,z4,z66]),(0,[z0,z1,z2,z125,z3,z4,z7]),(0,[z0,z1,z480,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z481])],[(0,[z0,z1,z2,z125,z14,z4,z7]),(0,[z0,z1,z2,z3,z482,z4,z7]),(0,[z0,z1,z2,z3,z83,z155,z7]),(0,[z0,z1,z2,z3,z4,z7,z7]),(0,[z0,z483,z1,z2,z3,z4,z7])]],
   [[(1,[z0,z1,z484,z3,z4,z7]),(0,[z41,z0,z1,z484,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z485,z7]),(0,[z486,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z14,z75,z4,z7]),(0,[z0,z1,z2,z16,z4,z55,z7]),(0,[z0,z20,z1,z2,z16,z4,z7]),(0,[z0,z1,z22,z2,z16,z4,z7]),(0,[z15,z0,z1,z448,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z441])],[(0,[z0,z1,z126,z76,z3,z4,z7]),(0,[z15,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z487,z2,z3,z4,z7])],[(0,[z0,z1,z2,z14,z4,z7,z129]),(0,[z15,z0,z1,z2,z14,z4,z7]),(0,[z91,z0,z1,z2,z3,z83,z7]),(1,[z0,z1,z2,z3,z4,z488]),(0,[z0,z1,z2,z3,z4,z488,z7]),(0,[z91,z0,z1,z58,z2,z3,z7]),(1,[z0,z47,z2,z3,z155,z7]),(0,[z0,z1,z58,z2,z3,z48,z7]),(0,[z0,z1,z73,z2,z3,z4,z55]),(0,[z0,z1,z2,z3,z4,z7,z489]),(0,[z490,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z491,z2,z3,z4,z7])],[(0,[z64,z0,z1,z44,z3,z4,z7]),(0,[z0,z1,z492,z2,z3,z4,z7])],[(0,[z32,z1,z267,z2,z3,z4,z7]),(0,[z43,z0,z1,z2,z3,z4,z493]),(0,[z0,z1,z2,z3,z155,z115,z7])],[(0,[z0,z0,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z10,z16,z4,z7]),(0,[z0,z1,z2,z3,z494,z4,z7]),(0,[z0,z1,z2,z3,z495,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z496]),(0,[z0,z1,z2,z3,z4,z497,z7])],[(0,[z0,z1,z2,z3,z210,z4,z7]),(0,[z0,z1,z2,z3,z498,z4,z7]),(0,[z43,z1,z44,z2,z3,z4,z7]),(0,[z0,z499,z1,z2,z3,z4,z7]),(0,[z500,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z501,z4,z7]),(0,[z0,z1,z60,z2,z3,z115,z7]),(0,[z0,z1,z2,z502,z3,z4,z7])],[(0,[z0,z1,z2,z287,z3,z4,z7]),(0,[z0,z1,z2,z16,z38,z4,z7]),(0,[z0,z1,z2,z52,z3,z4,z7]),(0,[z0,z1,z2,z503,z3,z4,z7]),(0,[z0,z45,z1,z124,z2,z4,z7]),(0,[z0,z1,z504,z2,z3,z4,z7]),(0,[z505,z0,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z506,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z102,z4,z7]),(0,[z0,z1,z2,z52,z14,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z171]),(0,[z0,z1,z2,z16,z4,z37,z7]),(0,[z0,z1,z2,z65,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z507,z7]),(0,[z0,z1,z2,z508,z3,z4,z7]),(0,[z0,z79,z2,z3,z4,z7,z94]),(1,[z0,z1,z2,z253,z4,z7])],[(0,[z0,z1,z76,z3,z4,z37,z7]),(0,[z0,z1,z279,z2,z16,z4,z7]),(0,[z0,z1,z2,z3,z48,z83,z7]),(0,[z0,z1,z2,z3,z4,z509,z7]),(0,[z0,z1,z73,z124,z2,z4,z7]),(0,[z0,z510,z1,z2,z3,z4,z7])],[(0,[z64,z0,z1,z2,z210,z4,z7]),(0,[z511,z0,z1,z2,z3,z4,z7]),(0,[z77,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z512,z2,z3,z4,z7]),(0,[z0,z1,z2,z283,z16,z4,z7]),(0,[z0,z1,z393,z2,z3,z4,z7]),(0,[z0,z79,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z513,z4,z7])],[(0,[z77,z0,z1,z2,z14,z4,z7])],[(0,[z0,z1,z2,z14,z48,z4,z7]),(0,[z0,z1,z36,z2,z14,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z66]),(0,[z0,z79,z1,z123,z2,z3,z4])],[(0,[z64,z0,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z16,z4,z19,z7]),(0,[z0,z1,z258,z2,z3,z4,z7]),(0,[z0,z1,z514,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z515,z4,z7])],[(0,[z0,z47,z1,z2,z3,z155,z7])],[(0,[z77,z1,z2,z3,z14,z4,z7]),(0,[z0,z1,z78,z2,z16,z4,z7]),(0,[z0,z1,z2,z3,z516,z4,z7]),(0,[z18,z0,z1,z2,z140,z3,z4]),(0,[z0,z1,z2,z3,z4,z94,z56]),(0,[z0,z517,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z103,z3,z4,z7]),(0,[z0,z1,z518,z2,z3,z4,z7]),(1,[z0,z1,z2,z4,z365,z7]),(0,[z0,z1,z519,z2,z3,z4,z7]),(1,[z0,z1,z58,z3,z85,z7]),(0,[z0,z520,z1,z2,z3,z4,z7])],[(0,[z43,z0,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z14,z521,z4,z7]),(0,[z0,z1,z2,z16,z83,z4,z7]),(0,[z522,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z523,z7]),(0,[z524,z0,z1,z2,z3,z4,z7]),(0,[z525,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z526,z4,z7]),(0,[z527,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z267,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z528,z4,z7]),(0,[z0,z1,z2,z14,z4,z7,z56]),(0,[z96,z0,z1,z2,z16,z4,z7]),(0,[z91,z0,z47,z1,z2,z3,z7]),(0,[z0,z1,z2,z71,z3,z4,z7]),(0,[z529,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z530])],[(0,[z531,z0,z1,z2,z3,z4,z7]),(1,[z0,z174,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z532,z4,z7]),(0,[z0,z1,z2,z3,z4,z533,z7]),(1,[z0,z1,z49,z3,z4,z50])],[(0,[z0,z1,z2,z3,z534,z4,z7]),(0,[z0,z1,z2,z3,z4,z535,z7]),(0,[z0,z536,z1,z2,z3,z4,z7]),(0,[z0,z1,z340,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z422,z4]),(0,[z0,z1,z2,z3,z422,z245,z4]),(0,[z0,z1,z2,z3,z75,z4,z11])],[(1,[z0,z1,z2,z384,z4,z7]),(0,[z537,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z538])],[(0,[z0,z1,z2,z67,z3,z4,z7]),(0,[z0,z1,z2,z140,z3,z4,z21])]],
   [[(0,[z142,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z228,z4,z7]),(0,[z0,z1,z2,z539,z3,z4,z7]),(0,[z0,z1,z2,z67,z14,z4,z7]),(0,[z0,z1,z540,z2,z3,z4,z7])],[(0,[z541,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z542,z2,z3,z4,z7]),(0,[z142,z0,z1,z2,z14,z4,z7]),(1,[z0,z1,z2,z3,z17,z7]),(0,[z0,z1,z2,z3,z137,z4,z7]),(0,[z0,z1,z2,z3,z4,z37,z7]),(0,[z0,z1,z2,z3,z543,z4,z7]),(0,[z0,z1,z2,z140,z3,z4,z153])],[(0,[z0,z1,z544,z2,z3,z4,z7]),(0,[z0,z1,z2,z14,z4,z7,z153]),(0,[z0,z1,z2,z545,z3,z4,z7]),(1,[z0,z1,z258,z2,z4,z7]),(0,[z0,z1,z2,z3,z546,z4,z7]),(0,[z0,z1,z2,z3,z4,z547,z7]),(0,[z0,z1,z58,z3,z85,z4,z7]),(0,[z0,z1,z2,z548,z3,z4,z7])],[(0,[z0,z1,z2,z545,z14,z4,z7]),(0,[z0,z1,z2,z16,z245,z4,z7]),(0,[z0,z1,z2,z3,z4,z549,z7]),(0,[z0,z1,z550,z2,z3,z4,z7]),(0,[z551,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z552,z4,z7])],[(0,[z0,z1,z553,z2,z3,z4,z7]),(0,[z0,z1,z2,z140,z16,z4,z7]),(1,[z0,z1,z2,z3,z4,z179]),(0,[z0,z1,z2,z4,z365,z7,z94]),(0,[z0,z1,z2,z3,z4,z7,z554])],[(0,[z0,z1,z2,z3,z555,z4,z7]),(0,[z0,z1,z2,z3,z556,z4,z7]),(0,[z0,z1,z2,z3,z557,z4,z7])],[(0,[z558,z0,z1,z2,z3,z4,z7]),(0,[z178,z0,z138,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z559,z7]),(0,[z0,z1,z2,z3,z560,z4,z7]),(0,[z0,z1,z126,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z561]),(0,[z0,z1,z2,z562,z3,z4,z7]),(0,[z0,z2,z3,z48,z4,z155,z7]),(0,[z0,z1,z2,z3,z4,z563,z7]),(0,[z0,z564,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z126,z2,z14,z4,z7]),(0,[z0,z1,z2,z16,z46,z4,z7]),(0,[z0,z1,z2,z3,z4,z565,z7]),(0,[z0,z1,z566,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z244,z7]),(0,[z567,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z163,z2,z3,z4]),(0,[z0,z45,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z568,z3,z4,z7])],[(0,[z0,z45,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z3,z569,z4,z7])],[(0,[z570,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z58,z44,z3,z4,z7]),(0,[z0,z1,z2,z14,z14,z4,z7]),(0,[z91,z1,z2,z3,z4,z315,z7]),(0,[z0,z1,z124,z2,z125,z4,z7])],[(0,[z571,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z73,z2,z14,z4,z7]),(0,[z0,z1,z572,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z573,z7]),(0,[z0,z1,z2,z3,z4,z574,z7]),(0,[z575,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z576,z2,z3,z4,z7]),(0,[z0,z1,z577,z2,z3,z4,z7]),(0,[z0,z1,z2,z578,z3,z4,z7]),(1,[z0,z1,z2,z3,z75,z11])],[(1,[z0,z1,z2,z410,z4,z7]),(0,[z41,z0,z1,z2,z410,z4,z7]),(0,[z0,z1,z2,z3,z4,z579,z7]),(0,[z0,z112,z79,z2,z3,z4,z7]),(1,[z0,z1,z2,z4,z7,z241])],[(0,[z0,z1,z2,z3,z4,z580,z7]),(0,[z82,z0,z1,z2,z3,z115,z7]),(0,[z0,z1,z2,z3,z581,z4,z7]),(0,[z0,z45,z1,z2,z4,z21,z7]),(0,[z0,z20,z1,z22,z2,z4,z7]),(0,[z97,z0,z47,z2,z3,z4,z7]),(0,[z582,z0,z1,z2,z3,z4,z7])]],
   [[(1,[z0,z1,z2,z3,z4,z493]),(0,[z0,z1,z583,z2,z3,z4,z7]),(0,[z0,z1,z2,z14,z4,z50,z7]),(0,[z0,z1,z2,z14,z4,z21,z7]),(0,[z0,z1,z2,z3,z305,z4,z7]),(0,[z178,z0,z2,z52,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z584,z7])],[(0,[z0,z1,z2,z3,z4,z585,z7]),(0,[z0,z1,z448,z2,z3,z4,z7]),(0,[z0,z1,z2,z586,z3,z4,z7])],[(0,[z0,z1,z2,z16,z85,z4,z7]),(0,[z0,z1,z2,z3,z4,z587,z7]),(0,[z0,z1,z2,z588,z3,z4,z7])],[(0,[z0,z1,z589,z2,z3,z4,z7]),(0,[z0,z590,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z4,z315,z7]),(1,[z0,z1,z2,z308,z4,z7]),(0,[z591,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z592,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z593,z7]),(0,[z0,z79,z1,z2,z3,z4,z55]),(0,[z594,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z245,z4,z7]),(0,[z0,z1,z194,z2,z3,z4,z153])],[(0,[z0,z174,z1,z267,z2,z3,z7]),(0,[z0,z1,z58,z2,z16,z4,z7]),(0,[z91,z0,z1,z393,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z595])],[(0,[z0,z1,z2,z3,z4,z7,z596])],[(0,[z0,z1,z2,z110,z3,z4,z7]),(0,[z0,z597,z1,z2,z3,z4,z7]),(0,[z0,z1,z49,z2,z3,z4,z129]),(0,[z0,z45,z1,z73,z2,z4,z7]),(0,[z0,z1,z2,z598,z3,z4,z7]),(0,[z0,z1,z599,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z600,z4,z7])]],
   [[(0,[z0,z1,z2,z76,z16,z4,z7]),(0,[z0,z1,z2,z14,z4,z115,z7]),(0,[z91,z0,z222,z2,z3,z4,z7]),(0,[z0,z601,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z133,z3,z4,z7]),(0,[z0,z602,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z603]),(0,[z0,z1,z604,z2,z3,z4,z7])],[(0,[z82,z0,z1,z2,z14,z4,z7]),(1,[z0,z1,z325,z2,z14,z4]),(0,[z605,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z606,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z607,z7]),(0,[z0,z1,z2,z140,z3,z4,z61])],[(0,[z608,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z14,z4,z7,z61]),(0,[z0,z1,z123,z2,z3,z4,z129]),(0,[z0,z1,z2,z609,z3,z4,z7]),(0,[z0,z1,z2,z610,z3,z4,z7]),(0,[z0,z1,z611,z2,z3,z4,z7])],[(0,[z41,z0,z1,z2,z14,z4,z7]),(0,[z0,z138,z1,z2,z14,z4,z7]),(0,[z0,z612,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z50,z94])],[(0,[z0,z1,z2,z3,z4,z7,z493]),(0,[z178,z0,z1,z2,z3,z4,z613]),(0,[z97,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z614,z7])],[(0,[z0,z1,z2,z615,z3,z4,z7]),(0,[z0,z1,z616,z2,z3,z4,z7]),(0,[z0,z1,z36,z3,z4,z37,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z7,z617]),(0,[z0,z1,z2,z618,z3,z4,z7])],[(0,[z41,z0,z267,z2,z3,z4,z7]),(0,[z619,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z620,z2,z3,z4,z7]),(0,[z0,z1,z124,z2,z14,z4,z7])],[(0,[z621,z0,z1,z2,z3,z4,z7]),(0,[z622,z0,z1,z2,z3,z4,z7]),(0,[z623,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z624,z2,z3,z4,z7]),(1,[z0,z1,z2,z16,z221,z7]),(0,[z0,z1,z2,z3,z4,z4,z7]),(0,[z0,z1,z2,z3,z4,z625,z7]),(0,[z0,z1,z626,z2,z3,z4,z7]),(0,[z0,z1,z2,z627,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z628])],[(0,[z97,z0,z32,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z16,z4,z7]),(1,[z0,z1,z2,z3,z4,z613]),(0,[z0,z1,z2,z3,z85,z4,z7]),(0,[z0,z1,z3,z4,z50,z7,z56])],[(0,[z43,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z16,z3,z221,z7]),(0,[z0,z1,z2,z3,z4,z629,z7]),(0,[z0,z1,z2,z630,z3,z4,z7]),(1,[z0,z112,z2,z3,z4,z55]),(0,[z0,z631,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z632])],[(1,[z96,z1,z2,z16,z4,z7]),(1,[z18,z1,z2,z3,z4,z129]),(0,[z0,z1,z2,z3,z4,z633,z7]),(0,[z0,z1,z2,z3,z4,z7,z634]),(0,[z0,z112,z1,z2,z3,z4,z94]),(0,[z0,z1,z9,z3,z4,z7,z94])],[(1,[z0,z1,z72,z2,z3,z4])],[(0,[z635,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z636,z7])]],
   [[(0,[z0,z1,z475,z2,z14,z4,z7]),(0,[z637,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z638,z7]),(0,[z0,z1,z2,z3,z4,z639,z7]),(0,[z0,z1,z640,z2,z3,z4,z7])],[(1,[z0,z1,z2,z3,z4,z333]),(0,[z41,z0,z1,z2,z3,z4,z333]),(1,[z0,z1,z2,z3,z4,z229]),(0,[z0,z1,z641,z2,z3,z4,z7]),(0,[z0,z642,z1,z2,z3,z4,z7]),(0,[z0,z1,z36,z2,z3,z48,z7]),(0,[z0,z1,z2,z3,z4,z643,z7]),(0,[z0,z1,z73,z49,z2,z3,z4])],[(0,[z0,z1,z2,z644,z3,z4,z7]),(0,[z0,z1,z2,z3,z645,z4,z7]),(0,[z0,z646,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z647,z3,z4,z7])],[(0,[z82,z0,z1,z36,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z648,z7]),(0,[z0,z1,z2,z3,z75,z4,z7])],[(0,[z0,z272,z1,z2,z3,z4,z7]),(0,[z0,z1,z649,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z613,z7]),(0,[z0,z45,z2,z3,z46,z4,z7]),(0,[z0,z1,z2,z3,z4,z650,z7])],[(0,[z0,z651,z1,z2,z3,z4,z7]),(0,[z0,z1,z123,z44,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z129]),(0,[z0,z1,z652,z2,z3,z4,z7]),(0,[z0,z138,z126,z2,z3,z4,z7]),(0,[z0,z1,z653,z2,z3,z4,z7]),(0,[z0,z1,z123,z2,z3,z4,z56]),(0,[z0,z1,z2,z3,z4,z654,z7])],[(0,[z0,z1,z2,z655,z3,z4,z7]),(0,[z0,z1,z2,z656,z3,z4,z7]),(0,[z0,z657,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z658,z4,z7]),(0,[z0,z1,z659,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z660])],[(0,[z661,z0,z1,z2,z3,z4,z7]),(0,[z0,z662,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z663]),(0,[z0,z1,z2,z16,z534,z4,z7]),(0,[z15,z0,z1,z2,z3,z4,z129]),(0,[z0,z1,z2,z3,z200,z4,z7]),(0,[z0,z1,z22,z2,z125,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z664])]],
   [[(0,[z0,z1,z2,z665,z3,z4,z7]),(1,[z0,z1,z341,z2,z3,z7]),(0,[z91,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z666,z2,z3,z4,z7]),(0,[z0,z667,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z14,z196,z4,z7]),(0,[z178,z0,z1,z52,z3,z4,z7]),(0,[z0,z1,z340,z2,z3,z245,z4]),(0,[z0,z1,z124,z125,z3,z4,z7])],[(0,[z181,z32,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z668,z7]),(0,[z0,z1,z2,z3,z4,z669,z7]),(0,[z0,z1,z49,z2,z16,z4,z7]),(0,[z91,z0,z1,z2,z3,z315,z7]),(0,[z0,z1,z2,z86,z3,z4,z7]),(0,[z0,z1,z670,z2,z3,z4,z7]),(0,[z0,z1,z2,z140,z3,z4,z11])],[(0,[z0,z1,z484,z2,z3,z4,z7]),(0,[z0,z1,z671,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z11,z19])],[(0,[z43,z0,z1,z2,z103,z4,z7]),(0,[z0,z1,z2,z3,z4,z179,z7]),(1,[z0,z1,z3,z4,z497,z7])],[(0,[z0,z1,z438,z2,z16,z4,z7]),(0,[z91,z0,z1,z2,z3,z38,z7]),(0,[z0,z1,z2,z3,z4,z672,z7]),(0,[z0,z1,z2,z38,z4,z115,z7]),(0,[z0,z1,z2,z3,z4,z146,z7])],[(0,[z673,z0,z1,z2,z3,z4,z7]),(0,[z0,z79,z1,z2,z14,z4,z7]),(0,[z0,z138,z1,z52,z3,z4,z7]),(0,[z0,z1,z2,z3,z38,z48,z7]),(0,[z674,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z675,z2,z3,z4,z7])],[(0,[z0,z1,z2,z14,z38,z4,z7]),(0,[z0,z47,z1,z2,z16,z4,z7]),(0,[z0,z1,z123,z2,z16,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z229]),(0,[z0,z1,z2,z3,z48,z4,z7]),(0,[z0,z1,z676,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z16,z4,z11,z7]),(0,[z0,z1,z2,z3,z4,z7,z677])],[(0,[z0,z1,z2,z3,z4,z7,z678]),(0,[z0,z1,z2,z16,z4,z17,z7]),(0,[z0,z1,z2,z3,z48,z315,z7]),(0,[z0,z679,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z680,z4,z7]),(1,[z0,z1,z194,z2,z3,z153])],[(0,[z681,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z4,z565,z7]),(0,[z0,z1,z682,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z683])],[(0,[z181,z0,z1,z2,z117,z4,z7]),(0,[z0,z1,z2,z3,z521,z4,z7]),(0,[z0,z1,z2,z3,z4,z684,z7])],[(0,[z0,z1,z2,z3,z685,z4,z7]),(0,[z0,z1,z686,z2,z3,z4,z7]),(0,[z687,z0,z1,z2,z3,z4,z7]),(1,[z178,z0,z52,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z688])],[(0,[z0,z1,z686,z2,z14,z4,z7]),(0,[z689,z0,z1,z2,z3,z4,z7]),(0,[z97,z0,z1,z2,z3,z155,z7]),(0,[z0,z1,z2,z3,z4,z7,z56]),(0,[z0,z1,z2,z3,z4,z690,z7])],[(1,[z0,z1,z2,z3,z255,z7]),(0,[z41,z0,z1,z2,z3,z255,z7]),(0,[z0,z1,z267,z2,z14,z4,z7]),(0,[z0,z1,z44,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z55,z129]),(0,[z0,z1,z2,z3,z691,z4,z7]),(0,[z0,z1,z123,z3,z4,z7,z56]),(0,[z0,z1,z692,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z693,z7]),(0,[z0,z694,z1,z2,z3,z4,z7])]],
   [[],[(0,[z0,z1,z2,z14,z83,z4,z7]),(0,[z91,z0,z1,z2,z3,z4,z488]),(0,[z0,z1,z2,z3,z4,z7,z695]),(0,[z0,z1,z2,z3,z696,z4,z7])],[(0,[z1,z2,z3,z83,z4,z315,z7]),(0,[z1,z2,z3,z4,z19,z7,z129]),(1,[z0,z1,z71,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z155,z7]),(0,[z0,z1,z2,z3,z4,z7,z697]),(0,[z0,z1,z2,z3,z698,z4,z7])],[(0,[z0,z1,z44,z3,z4,z50,z7]),(0,[z0,z1,z3,z4,z497,z7,z94]),(0,[z699,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z110,z3,z14,z4]),(0,[z18,z1,z2,z3,z4,z7,z129]),(0,[z0,z20,z1,z2,z3,z4,z7]),(0,[z0,z1,z22,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z700,z7]),(0,[z0,z1,z701,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z702,z4,z7])],[(0,[z0,z20,z1,z2,z14,z4,z7]),(0,[z0,z1,z22,z2,z14,z4,z7]),(0,[z0,z1,z2,z3,z703,z4,z7]),(0,[z0,z1,z194,z2,z3,z4,z11])],[(0,[z704,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z705,z7])],[(0,[z0,z1,z2,z125,z16,z4,z7]),(0,[z18,z0,z1,z73,z2,z3,z4]),(0,[z0,z1,z706,z2,z3,z4,z7])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z707,z2,z4,z7]),(0,[z64,z1,z708,z3,z4,z7]),(0,[z0,z1,z709,z2,z14,z7]),(0,[z0,z1,z2,z14,z54,z7]),(0,[z710,z1,z2,z3,z4,z7]),(0,[z0,z149,z2,z3,z48,z7]),(0,[z0,z1,z2,z711,z4,z7])],[(0,[z0,z1,z484,z90,z4,z7]),(0,[z0,z1,z544,z3,z4,z50]),(0,[z0,z1,z58,z3,z560,z7]),(0,[z0,z222,z2,z16,z4,z7]),(0,[z0,z1,z712,z2,z4,z7])],[(0,[z0,z1,z16,z4,z497,z7]),(0,[z0,z1,z2,z3,z4,z613])],[(0,[z0,z1,z2,z3,z713,z7]),(0,[z0,z1,z2,z14,z4,z613]),(0,[z0,z1,z2,z714,z14,z4]),(0,[z0,z1,z2,z4,z7,z715]),(0,[z0,z1,z2,z716,z4,z7])],[(0,[z96,z1,z2,z16,z4,z7]),(0,[z359,z1,z2,z14,z4,z7]),(0,[z0,z112,z2,z14,z4,z55]),(0,[z0,z1,z2,z3,z717,z7]),(0,[z0,z1,z2,z3,z4,z718]),(0,[z0,z1,z3,z4,z7,z719])],[(0,[z0,z720,z2,z3,z4,z7]),(0,[z0,z721,z2,z3,z4,z7]),(0,[z96,z1,z2,z722,z4,z7]),(0,[z0,z1,z60,z2,z17,z7]),(0,[z0,z1,z2,z3,z4,z723]),(0,[z0,z1,z72,z2,z3,z4])],[(0,[z41,z267,z2,z3,z4,z333]),(0,[z0,z1,z71,z394,z4,z7]),(0,[z0,z1,z22,z119,z4,z7])],[(0,[z0,z1,z2,z107,z4,z488]),(0,[z0,z1,z724,z3,z4,z7]),(0,[z97,z0,z334,z2,z3,z7]),(0,[z0,z1,z2,z3,z725,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z333]),(0,[z0,z1,z2,z726,z4,z7]),(0,[z0,z1,z727,z2,z4,z7]),(0,[z0,z1,z2,z3,z728,z4]),(0,[z0,z1,z2,z630,z38,z7]),(0,[z0,z1,z3,z4,z729,z7]),(0,[z0,z1,z2,z347,z115,z7])],[(0,[z0,z1,z2,z14,z4,z333]),(0,[z0,z1,z76,z3,z4,z5]),(0,[z0,z1,z2,z14,z4,z229]),(0,[z0,z1,z123,z16,z4,z56]),(0,[z0,z1,z9,z3,z4,z129]),(0,[z6,z1,z2,z3,z4,z19])],[(0,[z0,z1,z730,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z731]),(0,[z64,z1,z76,z16,z4,z7]),(0,[z0,z1,z2,z3,z732,z7]),(0,[z1,z2,z3,z4,z733,z7]),(0,[z0,z1,z2,z4,z7,z734]),(0,[z0,z1,z2,z3,z4,z735]),(0,[z0,z1,z118,z2,z4,z7])],[(0,[z0,z1,z736,z3,z4,z7]),(0,[z0,z1,z737,z3,z4,z7]),(0,[z0,z1,z738,z2,z16,z4]),(0,[z0,z1,z2,z3,z739,z7]),(0,[z0,z1,z2,z740,z4,z7]),(0,[z0,z1,z2,z4,z741,z7]),(1,[z0,z1,z3,z729,z7])],[(0,[z720,z267,z2,z3,z4,z7]),(0,[z0,z1,z742,z2,z4,z7]),(0,[z0,z1,z2,z3,z183,z7]),(0,[z0,z1,z2,z3,z743,z7]),(0,[z0,z1,z2,z744,z4,z7])],[(0,[z0,z1,z73,z2,z54,z7]),(0,[z0,z1,z745,z2,z4,z7]),(0,[z0,z1,z73,z2,z4,z660])],[(0,[z0,z1,z746,z3,z4,z7]),(0,[z0,z1,z2,z747,z4,z7]),(0,[z0,z1,z2,z3,z748,z7]),(0,[z0,z1,z36,z3,z729,z7])],[(0,[z0,z1,z341,z2,z3,z7]),(0,[z0,z1,z2,z3,z749,z4]),(0,[z0,z1,z2,z3,z4,z750]),(0,[z0,z1,z2,z751,z4,z7]),(0,[z752,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z753,z4,z7]),(0,[z0,z1,z2,z3,z11,z754])]],
   [[(0,[z0,z33,z2,z3,z4,z7]),(0,[z0,z755,z2,z3,z4,z7]),(0,[z0,z1,z2,z14,z749,z4]),(0,[z0,z1,z2,z14,z4,z750]),(0,[z0,z1,z325,z2,z4,z244]),(0,[z0,z1,z2,z3,z4,z756]),(0,[z0,z1,z757,z3,z4,z7]),(0,[z0,z1,z123,z618,z3,z4])],[(0,[z0,z33,z2,z14,z4,z7]),(0,[z451,z1,z2,z14,z4,z7]),(0,[z0,z1,z325,z2,z140,z4]),(0,[z0,z1,z72,z2,z16,z4]),(0,[z0,z138,z126,z3,z183,z7]),(0,[z0,z1,z2,z758,z4,z7])],[(0,[z0,z1,z2,z759,z14,z7]),(0,[z0,z33,z199,z3,z4,z7]),(0,[z0,z1,z2,z3,z343,z11])],[(0,[z77,z1,z2,z110,z14,z4]),(0,[z0,z1,z2,z110,z4,z324]),(0,[z0,z1,z2,z16,z4,z381])],[(0,[z0,z1,z2,z760,z4,z7]),(0,[z1,z2,z110,z16,z14,z4]),(0,[z0,z1,z2,z761,z4,z7]),(0,[z0,z2,z3,z762,z4,z7])],[(0,[z181,z32,z2,z3,z4,z7]),(0,[z0,z1,z325,z2,z268,z4]),(0,[z1,z2,z14,z4,z650,z7]),(0,[z0,z33,z2,z3,z38,z7]),(0,[z0,z1,z2,z763,z3,z4]),(0,[z15,z1,z2,z394,z4,z19]),(0,[z0,z1,z2,z140,z4,z21])],[(0,[z0,z1,z2,z3,z764,z7]),(0,[z0,z1,z2,z210,z4,z7]),(0,[z0,z1,z2,z3,z4,z765]),(0,[z0,z1,z2,z110,z3,z4]),(0,[z0,z766,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z767,z4]),(0,[z0,z1,z60,z2,z115,z7])],[(0,[z41,z267,z2,z16,z4,z7]),(0,[z0,z1,z123,z3,z4,z358]),(0,[z0,z20,z2,z67,z4,z7]),(0,[z0,z112,z692,z2,z3,z4]),(0,[z768,z1,z2,z3,z4,z7]),(0,[z0,z2,z3,z769,z4,z7])]],
   [[(0,[z0,z1,z2,z770,z4,z7]),(0,[z0,z1,z2,z102,z4,z7]),(0,[z0,z431,z1,z325,z2,z4]),(0,[z0,z1,z771,z14,z4,z7]),(0,[z0,z1,z2,z14,z4,z772]),(0,[z0,z1,z448,z16,z4,z7]),(0,[z0,z1,z773,z3,z4,z7]),(0,[z0,z1,z194,z2,z3,z153])],[(0,[z0,z1,z2,z16,z4,z7]),(1,[z0,z1,z2,z774,z7])],[(0,[z0,z1,z2,z722,z4,z7]),(0,[z82,z1,z2,z16,z83,z7]),(0,[z0,z1,z2,z16,z4,z441]),(0,[z0,z1,z775,z2,z3,z4]),(0,[z0,z1,z9,z3,z4,z56]),(0,[z0,z1,z2,z776,z4,z7])],[(0,[z0,z1,z341,z2,z16,z7]),(0,[z0,z1,z199,z16,z4,z7]),(0,[z0,z1,z2,z98,z17,z7]),(0,[z0,z1,z2,z777,z4,z7]),(0,[z0,z667,z2,z3,z4,z55]),(0,[z0,z1,z73,z2,z307,z4]),(0,[z0,z1,z60,z2,z774,z7])],[(0,[z0,z1,z2,z3,z778,z7]),(0,[z41,z267,z2,z3,z255,z7]),(0,[z0,z1,z779,z2,z117,z4]),(0,[z0,z662,z126,z3,z4,z7]),(0,[z77,z1,z325,z2,z14,z4]),(0,[z178,z0,z52,z3,z4,z7]),(1,[z0,z2,z3,z4,z780]),(0,[z0,z1,z2,z781,z4,z7])],[(0,[z178,z0,z52,z14,z4,z7]),(0,[z178,z0,z52,z3,z4,z441]),(1,[z0,z782,z3,z4,z7]),(0,[z0,z1,z2,z783,z4,z7])],[(0,[z0,z138,z126,z16,z4,z7]),(0,[z0,z1,z784,z2,z3,z4])],[(0,[z0,z1,z2,z14,z255,z7]),(0,[z77,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z110,z4,z21]),(0,[z0,z1,z58,z187,z3,z7]),(0,[z0,z1,z2,z3,z4,z785]),(0,[z0,z1,z786,z2,z3,z4])]],
   [[(0,[z0,z1,z787,z2,z4,z7]),(0,[z6,z1,z2,z14,z4,z7]),(0,[z0,z1,z193,z2,z17,z7]),(0,[z0,z1,z2,z788,z4,z7])],[(0,[z0,z174,z2,z3,z155,z7]),(0,[z0,z1,z789,z2,z3,z7]),(0,[z0,z1,z71,z3,z4,z7]),(0,[z0,z33,z2,z3,z4,z488]),(0,[z0,z45,z362,z2,z4,z7]),(0,[z0,z1,z790,z3,z4,z7]),(0,[z0,z346,z2,z3,z4,z55]),(0,[z0,z1,z73,z2,z4,z697]),(0,[z0,z1,z2,z791,z4,z7])],[(0,[z0,z1,z71,z14,z4,z7]),(0,[z114,z1,z2,z14,z4,z7]),(0,[z0,z165,z2,z534,z4,z7]),(0,[z0,z1,z792,z2,z3,z7]),(0,[z0,z1,z2,z140,z4,z365]),(0,[z0,z1,z2,z10,z4,z271])],[(0,[z0,z1,z2,z3,z4,z793]),(0,[z0,z1,z2,z4,z794,z7]),(0,[z0,z1,z4,z365,z497,z7]),(0,[z0,z1,z2,z795,z4,z7]),(0,[z0,z1,z2,z38,z774,z7])],[(0,[z0,z1,z2,z3,z4,z796]),(0,[z0,z1,z3,z4,z797,z7]),(0,[z0,z1,z798,z2,z14,z4]),(0,[z0,z1,z2,z4,z799,z7]),(0,[z0,z1,z9,z16,z4,z7]),(0,[z0,z1,z194,z2,z16,z153]),(0,[z82,z479,z1,z2,z3,z7]),(0,[z0,z1,z2,z800,z4,z7]),(0,[z0,z1,z2,z3,z200,z7]),(0,[z0,z20,z2,z67,z4,z66])],[(0,[z1,z88,z2,z16,z4,z7]),(0,[z0,z1,z49,z3,z39,z4])],[(0,[z0,z801,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z4,z66]),(0,[z91,z222,z2,z3,z315,z7]),(0,[z91,z1,z2,z3,z456,z7]),(0,[z0,z1,z2,z4,z7,z802])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z803,z4,z7]),(0,[z0,z1,z804,z2,z4,z7]),(0,[z178,z0,z321,z3,z4,z7]),(0,[z0,z1,z2,z805,z4,z7]),(0,[z0,z1,z2,z10,z38,z271])]],
   [[(0,[z0,z1,z484,z16,z4,z7]),(0,[z0,z1,z2,z14,z4,z5]),(0,[z0,z1,z2,z3,z4,z806]),(0,[z0,z1,z2,z16,z807,z7]),(0,[z0,z1,z808,z3,z4,z7]),(0,[z0,z1,z809,z3,z4,z7])],[(0,[z0,z1,z810,z3,z4,z7]),(0,[z0,z1,z72,z76,z3,z4]),(0,[z0,z1,z2,z811,z4,z7]),(0,[z0,z1,z2,z4,z812,z7])],[(0,[z0,z272,z1,z2,z3,z7]),(0,[z1,z44,z708,z3,z4,z7]),(0,[z0,z1,z2,z16,z4,z488]),(0,[z0,z47,z2,z16,z155,z7]),(0,[z415,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z3,z4,z813])],[(0,[z0,z1,z2,z814,z4,z7]),(0,[z0,z1,z2,z103,z4,z493]),(0,[z0,z1,z78,z2,z4,z161]),(0,[z0,z1,z58,z3,z557,z7]),(0,[z0,z1,z124,z4,z7,z360])],[(0,[z41,z267,z2,z3,z4,z40]),(0,[z0,z1,z2,z815,z3,z4]),(0,[z0,z1,z2,z816,z4,z7]),(0,[z0,z1,z2,z817,z4,z7]),(0,[z0,z1,z818,z2,z3,z4]),(0,[z0,z1,z118,z2,z4,z55])],[(0,[z0,z1,z2,z3,z4,z819]),(0,[z0,z1,z235,z4,z497,z7])],[(0,[z0,z1,z2,z3,z4,z40]),(0,[z0,z1,z820,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z821]),(0,[z0,z1,z2,z3,z4,z822]),(0,[z0,z1,z2,z823,z4,z7]),(0,[z1,z2,z14,z703,z4,z7]),(0,[z0,z1,z824,z2,z4,z7]),(0,[z0,z1,z825,z2,z3,z4]),(0,[z0,z1,z2,z16,z221,z826]),(0,[z0,z1,z2,z140,z420,z4])],[(0,[z0,z1,z2,z14,z4,z40]),(0,[z0,z174,z1,z2,z14,z7]),(0,[z15,z1,z448,z3,z4,z19]),(0,[z0,z1,z2,z827,z4,z7]),(0,[z0,z1,z828,z3,z4,z7])]],
   [[(0,[z15,z1,z2,z3,z4,z19])],[(0,[z15,z1,z2,z14,z4,z19]),(0,[z0,z1,z2,z3,z4,z829]),(0,[z0,z1,z2,z16,z4,z830]),(0,[z0,z1,z2,z3,z733,z7]),(0,[z0,z2,z3,z4,z780,z7])],[(0,[z0,z2,z14,z4,z831,z7]),(0,[z0,z1,z2,z14,z4,z829]),(0,[z0,z1,z2,z268,z521,z7]),(0,[z0,z1,z832,z2,z4,z7]),(0,[z0,z1,z2,z833,z4,z7]),(0,[z0,z1,z49,z3,z4,z834])],[(0,[z41,z267,z2,z90,z4,z7]),(0,[z41,z267,z2,z3,z303,z7]),(0,[z43,z1,z708,z3,z4,z7]),(0,[z0,z1,z325,z686,z2,z4]),(0,[z0,z1,z835,z2,z4,z7]),(0,[z0,z1,z3,z836,z4,z7])],[(0,[z0,z1,z2,z3,z837,z7]),(0,[z0,z1,z2,z3,z838,z7]),(0,[z0,z1,z2,z86,z4,z7]),(0,[z0,z839,z2,z3,z4,z7]),(0,[z0,z1,z2,z140,z99,z4]),(0,[z0,z1,z22,z245,z4,z7])],[(0,[z0,z1,z2,z3,z303,z7]),(0,[z0,z1,z2,z840,z4,z7]),(0,[z0,z1,z841,z2,z3,z4]),(0,[z0,z1,z73,z448,z3,z4]),(0,[z0,z1,z2,z842,z4,z7]),(0,[z0,z79,z2,z3,z4,z94])],[(0,[z0,z1,z2,z14,z303,z7]),(0,[z0,z1,z2,z3,z843,z7]),(0,[z0,z1,z2,z3,z844,z7]),(0,[z0,z1,z2,z3,z4,z845]),(0,[z0,z1,z2,z98,z4,z7]),(0,[z0,z79,z2,z14,z4,z94])],[(0,[z0,z1,z123,z118,z4,z56])]],
   [[(0,[z0,z1,z2,z305,z4,z7]),(0,[z0,z1,z58,z16,z85,z7]),(0,[z0,z1,z73,z2,z4,z312]),(0,[z0,z1,z2,z75,z146,z11])],[(0,[z0,z1,z2,z3,z846,z7]),(0,[z582,z32,z2,z3,z4,z7]),(0,[z0,z1,z2,z847,z4,z7]),(0,[z82,z1,z2,z305,z83,z7]),(0,[z0,z1,z2,z3,z4,z848])],[(0,[z1,z2,z708,z3,z4,z7]),(0,[z1,z2,z14,z4,z7,z68]),(0,[z0,z1,z2,z4,z849,z7]),(0,[z0,z1,z2,z850,z4,z7]),(0,[z0,z851,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z834]),(1,[z0,z1,z2,z3,z754])],[(0,[z0,z1,z779,z2,z3,z4]),(0,[z0,z1,z2,z221,z115,z7]),(0,[z575,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z98,z38,z7]),(0,[z0,z852,z2,z3,z4,z7])],[(0,[z181,z32,z2,z228,z4,z7]),(0,[z0,z1,z163,z2,z14,z4]),(0,[z0,z1,z49,z16,z4,z50]),(0,[z0,z1,z2,z853,z4,z7]),(0,[z0,z1,z3,z729,z37,z7])],[(0,[z41,z267,z133,z3,z4,z7]),(0,[z0,z1,z2,z410,z4,z333]),(0,[z0,z1,z2,z854,z4,z7]),(0,[z428,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z16,z422,z4]),(0,[z18,z1,z2,z86,z4,z129]),(0,[z0,z1,z123,z119,z3,z4])],[(0,[z0,z1,z2,z4,z7,z855]),(0,[z0,z1,z2,z110,z99,z4]),(0,[z0,z1,z73,z2,z4,z61]),(0,[z0,z1,z2,z856,z4,z7])],[(0,[z0,z1,z133,z3,z4,z7]),(0,[z0,z1,z411,z2,z244,z7]),(0,[z0,z301,z2,z3,z4,z55]),(0,[z0,z1,z2,z3,z137,z7]),(0,[z0,z1,z2,z3,z4,z857])]],
   [[(0,[z0,z1,z133,z14,z4,z7]),(0,[z0,z1,z2,z14,z137,z7]),(0,[z0,z2,z14,z858,z4,z7]),(0,[z0,z1,z22,z325,z2,z4]),(0,[z0,z1,z2,z16,z859,z7]),(0,[z0,z1,z2,z92,z221,z7]),(0,[z0,z222,z2,z92,z4,z7]),(0,[z0,z79,z9,z3,z4,z94]),(0,[z0,z1,z123,z3,z4,z603]),(0,[z0,z1,z123,z118,z2,z4])],[(0,[z0,z860,z2,z3,z4,z7]),(0,[z0,z1,z2,z16,z17,z7]),(0,[z0,z1,z36,z199,z3,z7]),(1,[z1,z2,z3,z4,z861]),(0,[z0,z1,z340,z2,z3,z4])],[(0,[z0,z1,z2,z90,z4,z333]),(0,[z64,z1,z341,z76,z3,z7]),(0,[z0,z860,z2,z14,z4,z7]),(0,[z0,z1,z2,z3,z221,z862]),(0,[z0,z222,z393,z3,z4,z7]),(0,[z0,z1,z3,z4,z50,z367])],[(0,[z0,z1,z341,z199,z3,z7]),(0,[z0,z1,z863,z2,z14,z7]),(0,[z0,z2,z740,z46,z4,z7]),(0,[z0,z1,z2,z3,z4,z864])],[(0,[z0,z1,z484,z3,z303,z7]),(0,[z0,z1,z2,z865,z4,z7]),(0,[z0,z1,z2,z3,z866,z7]),(0,[z0,z1,z325,z2,z4,z61]),(0,[z0,z1,z2,z16,z4,z179]),(0,[z91,z1,z81,z2,z3,z7]),(0,[z0,z1,z867,z2,z4,z7]),(0,[z0,z138,z126,z3,z137,z7])],[(0,[z0,z1,z2,z868,z4,z7]),(0,[z0,z1,z2,z14,z866,z7]),(0,[z0,z45,z2,z46,z4,z7])],[(0,[z0,z1,z869,z3,z4,z7]),(0,[z0,z1,z73,z2,z4,z161]),(0,[z0,z1,z2,z107,z4,z229])],[(0,[z0,z1,z2,z3,z870,z7]),(0,[z0,z225,z1,z325,z2,z4]),(0,[z0,z1,z2,z65,z4,z565]),(0,[z0,z20,z2,z4,z266,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z871]),(0,[z0,z1,z2,z3,z4,z872]),(0,[z0,z1,z873,z3,z4,z7]),(0,[z0,z1,z2,z3,z874,z7])],[(0,[z0,z1,z2,z14,z4,z871]),(0,[z0,z1,z2,z14,z4,z872]),(0,[z0,z1,z873,z14,z4,z7]),(0,[z0,z33,z2,z3,z115,z7]),(0,[z0,z1,z2,z875,z4,z7])],[(0,[z0,z1,z876,z2,z3,z4]),(0,[z64,z1,z76,z210,z4,z7]),(1,[z1,z708,z3,z4,z7]),(0,[z1,z2,z213,z16,z4,z7]),(0,[z0,z1,z2,z3,z75,z754])],[(0,[z359,z267,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z877,z7]),(0,[z0,z1,z2,z3,z4,z878]),(0,[z1,z2,z218,z16,z4,z7]),(0,[z0,z1,z2,z3,z4,z879])],[(0,[z472,z1,z76,z3,z4,z7])],[(0,[z0,z1,z2,z880,z3,z4]),(0,[z0,z1,z881,z2,z4,z7]),(0,[z0,z1,z2,z3,z4,z882]),(0,[z0,z1,z2,z16,z75,z11]),(0,[z0,z1,z2,z883,z4,z7]),(0,[z0,z79,z3,z4,z497,z94])],[(0,[z0,z1,z884,z2,z3,z7]),(0,[z0,z1,z2,z3,z885,z7]),(0,[z0,z1,z2,z14,z732,z7]),(0,[z0,z1,z448,z140,z3,z4]),(0,[z0,z517,z1,z123,z3,z4]),(0,[z0,z1,z2,z10,z774,z7])],[(0,[z0,z1,z2,z3,z4,z886]),(0,[z0,z1,z2,z102,z4,z493]),(0,[z887,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z4,z888,z7]),(0,[z889,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z890,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z891]),(0,[z0,z1,z2,z16,z4,z493]),(0,[z0,z1,z2,z14,z183,z7]),(0,[z0,z1,z2,z4,z888,z441]),(0,[z0,z1,z892,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z893])],[(0,[z43,z1,z44,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z894]),(0,[z0,z1,z895,z3,z4,z7]),(0,[z896,z1,z2,z3,z4,z7])],[(0,[z0,z1,z897,z2,z3,z4]),(0,[z0,z1,z190,z2,z3,z7]),(0,[z0,z1,z898,z2,z3,z7]),(0,[z43,z1,z44,z14,z4,z7]),(0,[z0,z1,z899,z2,z4,z7]),(0,[z0,z1,z2,z17,z565,z7]),(0,[z900,z0,z1,z2,z3,z7]),(0,[z0,z1,z123,z3,z4,z441]),(0,[z178,z0,z72,z52,z3,z4]),(0,[z0,z45,z2,z740,z4,z7]),(0,[z0,z1,z22,z340,z2,z4]),(0,[z0,z1,z2,z4,z115,z271]),(0,[z0,z1,z2,z10,z38,z381]),(0,[z0,z1,z2,z140,z4,z233])],[(0,[z0,z1,z2,z410,z255,z7]),(0,[z0,z1,z2,z3,z4,z901]),(0,[z0,z1,z902,z2,z4,z7]),(0,[z1,z2,z14,z4,z173,z7]),(0,[z0,z1,z2,z16,z903,z7]),(0,[z0,z1,z904,z3,z4,z7])],[(0,[z0,z79,z2,z4,z365,z94])],[(0,[z0,z1,z2,z905,z4,z7]),(0,[z0,z1,z2,z3,z906,z7]),(0,[z0,z1,z907,z3,z4,z7]),(0,[z0,z1,z805,z245,z4,z7])],[(0,[z0,z1,z123,z3,z4,z663]),(0,[z0,z1,z2,z3,z908,z7]),(0,[z1,z2,z3,z4,z861,z7]),(0,[z15,z1,z71,z3,z4,z19])],[(0,[z0,z1,z2,z909,z4,z7]),(0,[z0,z2,z67,z740,z4,z7]),(0,[z0,z79,z2,z3,z4,z780])]],
   [[(0,[z0,z1,z2,z90,z255,z7]),(0,[z0,z1,z2,z3,z910,z7]),(0,[z0,z1,z2,z3,z4,z911]),(0,[z0,z1,z2,z10,z38,z7])],[(0,[z181,z32,z2,z14,z4,z7]),(0,[z0,z1,z72,z2,z14,z4]),(0,[z0,z1,z912,z2,z4,z7]),(0,[z0,z1,z2,z913,z4,z7])],[(0,[z0,z1,z2,z3,z914,z7]),(0,[z0,z1,z2,z3,z4,z915]),(0,[z0,z1,z393,z3,z4,z7]),(0,[z314,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z3,z4,z916]),(0,[z0,z1,z9,z140,z3,z4])],[(0,[z0,z1,z2,z14,z4,z915]),(0,[z0,z1,z2,z3,z917,z7]),(0,[z0,z1,z2,z3,z4,z918]),(0,[z919,z1,z2,z3,z4,z7])],[(0,[z0,z1,z920,z2,z4,z7])],[(0,[z0,z222,z2,z3,z4,z7]),(0,[z181,z720,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z221,z7]),(0,[z0,z1,z2,z4,z7,z921]),(0,[z0,z1,z2,z4,z146,z7])],[(1,[z720,z2,z3,z4,z7]),(0,[z0,z1,z190,z2,z16,z7]),(0,[z0,z1,z2,z14,z221,z7]),(0,[z0,z222,z2,z14,z4,z7]),(0,[z0,z1,z2,z922,z4,z7])],[(0,[z0,z222,z199,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z923,z7]),(0,[z594,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z16,z924,z7]),(0,[z0,z33,z2,z3,z4,z229]),(0,[z0,z1,z2,z4,z925,z7]),(0,[z0,z1,z235,z2,z4,z7]),(0,[z0,z1,z124,z284,z4,z7]),(0,[z0,z1,z22,z422,z245,z4])],[(0,[z41,z174,z267,z2,z3,z7]),(0,[z0,z926,z2,z3,z4,z7])],[(0,[z0,z1,z133,z3,z255,z7]),(0,[z0,z1,z2,z927,z4,z7]),(0,[z0,z1,z325,z2,z3,z4]),(0,[z0,z1,z2,z140,z4,z565]),(0,[z0,z1,z2,z4,z928,z7]),(0,[z1,z2,z3,z4,z19,z861]),(0,[z15,z1,z2,z218,z3,z4]),(0,[z0,z1,z2,z3,z4,z929]),(0,[z0,z1,z930,z2,z4,z7]),(0,[z0,z1,z22,z805,z4,z7])],[(0,[z0,z1,z2,z410,z4,z40]),(0,[z0,z1,z2,z931,z4,z7]),(0,[z0,z1,z341,z2,z14,z7]),(0,[z0,z1,z2,z3,z932,z7]),(0,[z0,z1,z2,z103,z4,z5]),(0,[z551,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z16,z4,z613]),(0,[z242,z1,z2,z16,z4,z7]),(0,[z0,z1,z930,z2,z4,z441])],[(0,[z689,z1,z44,z3,z4,z7]),(0,[z0,z1,z475,z245,z4,z7]),(0,[z0,z112,z2,z16,z4,z55]),(0,[z91,z1,z2,z92,z315,z7]),(0,[z0,z1,z2,z3,z933,z4]),(0,[z0,z1,z934,z3,z4,z7])],[(0,[z0,z1,z935,z3,z4,z7]),(0,[z0,z1,z2,z936,z4,z7]),(0,[z0,z1,z2,z110,z16,z4]),(0,[z18,z1,z2,z16,z4,z129]),(0,[z0,z33,z36,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z937]),(0,[z0,z938,z1,z2,z4,z7])],[(0,[z0,z267,z2,z3,z255,z7]),(0,[z1,z298,z2,z16,z4,z7]),(0,[z91,z1,z393,z3,z315,z7]),(0,[z178,z0,z52,z3,z4,z613])],[(0,[z0,z1,z2,z3,z939,z7]),(0,[z0,z1,z2,z940,z4,z7]),(0,[z451,z1,z44,z3,z4,z7]),(0,[z0,z45,z1,z325,z2,z4]),(0,[z0,z1,z325,z2,z10,z4]),(0,[z0,z1,z2,z3,z4,z941]),(0,[z0,z1,z2,z3,z4,z942])]],
   [[(0,[z1,z2,z722,z3,z4,z7]),(0,[z0,z1,z2,z14,z200,z7]),(0,[z0,z1,z2,z3,z943,z7]),(0,[z0,z1,z2,z4,z327,z21])],[(0,[z0,z1,z2,z16,z4,z333]),(0,[z0,z1,z2,z16,z4,z229]),(0,[z0,z597,z2,z3,z155,z7]),(0,[z0,z1,z2,z3,z944,z7]),(0,[z0,z1,z73,z2,z4,z429]),(0,[z0,z1,z22,z340,z245,z4]),(0,[z0,z1,z73,z2,z4,z430])],[(0,[z0,z1,z2,z410,z303,z7]),(0,[z0,z1,z9,z3,z4,z19]),(0,[z0,z1,z2,z3,z945,z7]),(0,[z0,z1,z2,z946,z4,z7])],[(0,[z0,z1,z393,z3,z4,z488]),(0,[z0,z1,z947,z3,z4,z7])],[(0,[z0,z1,z686,z192,z4,z7]),(0,[z0,z1,z194,z2,z14,z153]),(0,[z0,z45,z2,z534,z4,z7]),(0,[z1,z2,z3,z83,z733,z7]),(0,[z0,z1,z2,z3,z4,z948]),(0,[z0,z1,z2,z4,z949,z7])],[(0,[z0,z1,z2,z3,z4,z950])],[(0,[z0,z1,z2,z951,z4,z7]),(0,[z0,z1,z2,z3,z255,z333]),(0,[z0,z371,z2,z3,z155,z7]),(0,[z0,z1,z952,z2,z3,z4]),(0,[z160,z0,z52,z3,z4,z7]),(0,[z0,z1,z953,z3,z4,z7]),(0,[z0,z222,z2,z3,z4,z488])],[(0,[z1,z720,z2,z3,z4,z7]),(0,[z0,z1,z2,z98,z115,z7]),(0,[z0,z1,z954,z2,z3,z4]),(0,[z0,z1,z2,z3,z955,z7]),(0,[z0,z956,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z957,z7]),(0,[z0,z1,z958,z3,z4,z7]),(0,[z0,z1,z475,z325,z2,z4]),(0,[z0,z1,z2,z253,z4,z153])],[(0,[z0,z1,z36,z3,z261,z7])],[(0,[z0,z1,z2,z228,z877,z7]),(0,[z0,z1,z2,z3,z767,z4]),(0,[z0,z1,z279,z125,z4,z7]),(0,[z0,z1,z2,z959,z4,z7]),(0,[z0,z1,z3,z4,z7,z960]),(0,[z0,z1,z73,z2,z4,z365])],[(0,[z0,z1,z2,z961,z4,z7]),(0,[z0,z1,z2,z962,z4,z7]),(0,[z0,z1,z963,z2,z4,z7]),(0,[z0,z1,z2,z3,z964,z7]),(0,[z0,z965,z2,z3,z4,z7]),(0,[z0,z1,z58,z3,z729,z7])],[(0,[z0,z1,z133,z410,z4,z7]),(0,[z0,z1,z2,z966,z4,z7])],[(0,[z0,z1,z2,z3,z4,z967]),(0,[z0,z225,z2,z545,z4,z7]),(0,[z0,z1,z2,z4,z7,z968]),(0,[z0,z1,z2,z3,z4,z969])],[(0,[z0,z1,z2,z3,z4,z970]),(0,[z0,z1,z971,z2,z4,z7]),(0,[z6,z1,z44,z3,z4,z7]),(0,[z0,z1,z2,z134,z221,z7]),(0,[z82,z1,z2,z3,z83,z7]),(0,[z15,z1,z2,z3,z4,z861]),(0,[z0,z407,z2,z3,z48,z7])],[(0,[z82,z1,z2,z14,z83,z7]),(0,[z0,z1,z2,z3,z972,z7]),(0,[z0,z1,z2,z973,z4,z7]),(0,[z0,z1,z974,z3,z4,z7])]],
   [[(0,[z477,z1,z2,z14,z4,z7]),(0,[z1,z2,z348,z16,z4,z7]),(0,[z82,z1,z2,z3,z733,z7]),(0,[z0,z1,z2,z3,z729,z7])],[(0,[z0,z1,z133,z90,z4,z7]),(0,[z0,z272,z1,z2,z16,z7]),(0,[z0,z1,z2,z975,z4,z7]),(0,[z342,z1,z2,z16,z4,z7])],[(0,[z0,z976,z2,z3,z4,z7]),(0,[z0,z1,z3,z4,z50,z441])],[(0,[z0,z1,z125,z805,z4,z7])],[(0,[z177,z1,z2,z14,z4,z7]),(0,[z0,z782,z52,z3,z4,z7]),(0,[z0,z1,z2,z977,z4,z7])],[(0,[z178,z0,z52,z16,z4,z7]),(0,[z0,z1,z124,z805,z4,z7]),(0,[z0,z978,z2,z3,z4,z7])],[(0,[z0,z1,z44,z3,z4,z5]),(0,[z318,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z979,z4,z7]),(0,[z0,z1,z448,z99,z4,z7]),(0,[z97,z0,z2,z3,z48,z7])],[(0,[z0,z1,z2,z3,z4,z980]),(0,[z0,z1,z2,z16,z255,z7]),(0,[z1,z2,z14,z4,z297,z7]),(0,[z97,z0,z2,z14,z48,z7]),(0,[z0,z1,z2,z99,z4,z7]),(0,[z0,z1,z2,z774,z115,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z981]),(0,[z0,z1,z393,z92,z4,z7]),(0,[z0,z1,z2,z4,z7,z982]),(0,[z0,z1,z9,z3,z4,z7]),(0,[z0,z20,z666,z2,z4,z7])],[(0,[z0,z1,z2,z983,z4,z7]),(0,[z252,z1,z2,z16,z4,z7]),(0,[z91,z1,z2,z3,z315,z7]),(0,[z0,z1,z9,z3,z4,z441])],[(0,[z41,z267,z484,z3,z4,z7]),(0,[z0,z1,z2,z984,z4,z7]),(0,[z91,z1,z2,z14,z315,z7]),(0,[z0,z1,z985,z2,z4,z7]),(0,[z0,z1,z825,z2,z14,z4]),(0,[z0,z1,z71,z16,z4,z7]),(0,[z0,z1,z2,z16,z986,z7]),(0,[z0,z1,z9,z235,z4,z7])],[(0,[z0,z174,z33,z2,z3,z7]),(0,[z91,z1,z199,z3,z315,z7]),(0,[z0,z1,z258,z72,z2,z4]),(0,[z0,z1,z73,z2,z4,z336]),(1,[z0,z2,z740,z4,z7]),(0,[z0,z1,z49,z144,z3,z4]),(0,[z0,z1,z2,z3,z4,z987])],[(0,[z0,z1,z484,z3,z4,z7]),(0,[z0,z1,z2,z117,z4,z7]),(0,[z0,z1,z2,z3,z4,z988]),(0,[z0,z1,z2,z3,z807,z7]),(0,[z0,z1,z73,z2,z99,z4]),(0,[z0,z2,z782,z3,z4,z7]),(0,[z0,z1,z2,z3,z989,z7])],[(0,[z0,z1,z484,z14,z4,z7]),(0,[z0,z1,z2,z3,z303,z333]),(0,[z64,z1,z190,z76,z3,z7]),(0,[z0,z1,z990,z2,z4,z7]),(0,[z0,z20,z2,z67,z4,z179]),(0,[z0,z1,z991,z3,z4,z7])],[(0,[z0,z1,z2,z992,z4,z7]),(0,[z0,z1,z2,z3,z7,z993]),(0,[z0,z994,z2,z3,z4,z7]),(0,[z0,z1,z995,z3,z4,z7]),(0,[z0,z47,z2,z3,z155,z7])],[(0,[z0,z1,z3,z4,z996,z7]),(0,[z0,z1,z2,z102,z4,z5]),(0,[z0,z994,z2,z14,z4,z7]),(0,[z97,z0,z33,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z271])]],
   [[(0,[z43,z1,z44,z3,z4,z493]),(0,[z0,z1,z2,z16,z4,z5]),(0,[z0,z1,z997,z3,z4,z7]),(0,[z0,z1,z2,z14,z4,z271]),(0,[z0,z1,z2,z4,z774,z7])],[(0,[z0,z1,z998,z3,z4,z7]),(0,[z0,z1,z72,z44,z3,z4]),(0,[z0,z1,z2,z16,z4,z826]),(0,[z0,z1,z784,z2,z305,z4]),(0,[z0,z1,z414,z2,z115,z7]),(0,[z0,z1,z999,z2,z4,z7]),(0,[z0,z1,z2,z4,z1000,z7])],[(0,[z0,z1,z1001,z3,z4,z7]),(0,[z0,z1,z2,z3,z221,z826]),(1,[z1,z2,z3,z733,z7]),(0,[z0,z112,z2,z3,z4,z780]),(0,[z0,z1,z1002,z2,z4,z7])],[(0,[z0,z1,z1003,z3,z4,z7]),(0,[z0,z1,z1004,z3,z4,z7])],[(0,[z0,z1,z2,z4,z7,z1005]),(0,[z0,z1,z1006,z3,z4,z7]),(0,[z0,z1,z2,z1007,z4,z7])],[(0,[z0,z1,z2,z1008,z4,z7]),(0,[z0,z1,z2,z3,z4,z1009]),(0,[z43,z1,z44,z103,z4,z7]),(0,[z0,z1,z14,z4,z497,z7]),(0,[z0,z63,z2,z3,z4,z94]),(0,[z0,z1,z1010,z2,z3,z7]),(0,[z0,z1,z2,z1011,z4,z7]),(0,[z0,z1,z123,z4,z241,z56])],[(0,[z0,z1012,z2,z3,z4,z7]),(0,[z0,z1,z36,z16,z37,z7]),(0,[z91,z1,z2,z3,z315,z229])],[(0,[z0,z1,z133,z3,z4,z333]),(0,[z0,z1,z2,z16,z4,z40]),(0,[z0,z1,z1013,z3,z4,z7]),(0,[z18,z1,z298,z2,z3,z4]),(0,[z0,z1,z3,z4,z7,z834])]],
   [[(0,[z0,z1,z2,z3,z1014,z7]),(0,[z0,z1,z78,z2,z17,z7]),(0,[z0,z1,z340,z2,z16,z4])],[(0,[z0,z2,z3,z4,z7,z1015]),(0,[z0,z1,z2,z14,z4,z882]),(0,[z0,z1,z411,z2,z115,z7]),(0,[z0,z33,z2,z107,z4,z7]),(0,[z0,z1,z2,z4,z1016,z7]),(0,[z0,z1,z1017,z3,z4,z7])],[(0,[z0,z1,z325,z2,z4,z171]),(0,[z91,z1,z2,z3,z315,z488]),(0,[z0,z2,z3,z48,z748,z7]),(0,[z0,z1,z2,z1018,z4,z7]),(0,[z0,z1,z9,z73,z3,z4])],[(0,[z0,z1,z2,z4,z1019,z7]),(0,[z1,z2,z16,z722,z4,z7]),(0,[z0,z1,z2,z1020,z4,z7]),(0,[z0,z1,z652,z2,z3,z153]),(0,[z0,z1,z2,z3,z680,z153])],[(0,[z0,z1,z2,z3,z255,z40]),(0,[z0,z1,z2,z3,z1021,z7]),(0,[z1,z2,z16,z14,z221,z7]),(0,[z0,z1022,z2,z3,z4,z7]),(0,[z0,z1,z58,z3,z85,z7])],[(0,[z0,z1,z2,z3,z4,z1023]),(0,[z0,z1,z2,z1024,z4,z7]),(0,[z0,z1,z2,z1025,z4,z7]),(0,[z0,z1,z2,z1026,z4,z7])],[(0,[z0,z1,z2,z3,z1027,z7]),(0,[z0,z1,z2,z1028,z4,z7]),(0,[z0,z79,z2,z16,z4,z94]),(0,[z1,z2,z3,z4,z7,z1029]),(0,[z0,z1,z487,z3,z4,z50])],[(0,[z0,z1,z2,z1030,z4,z7]),(0,[z0,z1,z1031,z2,z3,z4]),(0,[z0,z520,z2,z3,z155,z7]),(0,[z0,z1,z1032,z2,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z1033]),(0,[z1034,z0,z1,z2,z3,z7]),(0,[z0,z1,z2,z1035,z4,z7]),(0,[z0,z1,z49,z3,z4,z50])],[(0,[z0,z1,z2,z3,z7,z1036]),(0,[z0,z1,z2,z815,z210,z4]),(0,[z0,z1,z2,z1037,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1038]),(0,[z0,z1,z2,z3,z1039,z7]),(0,[z0,z1,z1040,z3,z4,z7]),(0,[z0,z1,z2,z4,z7,z1041]),(0,[z201,z1,z2,z3,z83,z7]),(0,[z0,z1,z2,z1042,z4,z7])],[(0,[z0,z1,z2,z92,z4,z7]),(0,[z0,z1043,z2,z3,z4,z7]),(0,[z0,z1,z2,z4,z1044,z7]),(0,[z0,z93,z1,z123,z3,z4])],[(0,[z0,z1,z2,z3,z859,z7]),(0,[z0,z1,z124,z192,z4,z7]),(0,[z605,z1,z2,z16,z4,z7]),(0,[z1,z2,z3,z4,z861,z129]),(0,[z0,z1,z448,z394,z4,z7]),(0,[z0,z79,z1,z9,z3,z4]),(0,[z0,z1,z2,z4,z7,z1045])],[(0,[z0,z1,z2,z3,z17,z7]),(0,[z0,z1,z2,z394,z4,z7]),(0,[z0,z1,z2,z17,z21,z7]),(0,[z0,z1,z2,z3,z4,z862]),(0,[z0,z1,z199,z92,z4,z7]),(0,[z0,z1,z105,z2,z4,z7])],[(0,[z1,z325,z2,z16,z14,z4]),(0,[z0,z1,z2,z14,z17,z7]),(0,[z0,z1,z393,z14,z4,z7]),(0,[z657,z1,z2,z14,z4,z7]),(0,[z82,z1,z2,z3,z401,z7]),(0,[z0,z1,z258,z2,z4,z7]),(0,[z97,z0,z2,z3,z748,z7])],[(0,[z0,z1,z2,z1046,z4,z7]),(0,[z0,z1,z9,z4,z365,z7])]],
   [[(0,[z0,z1,z133,z16,z4,z7]),(0,[z0,z1,z2,z16,z137,z7]),(0,[z0,z1,z2,z92,z38,z7]),(0,[z0,z45,z204,z2,z4,z7]),(0,[z0,z20,z2,z740,z4,z7])],[(0,[z0,z1,z1047,z3,z4,z7]),(0,[z0,z1,z14,z4,z1048,z7]),(0,[z0,z1,z448,z3,z4,z19]),(0,[z0,z1049,z1,z2,z3,z7]),(0,[z0,z1,z2,z253,z4,z11])],[(0,[z0,z1,z2,z1050,z4,z7]),(0,[z0,z1,z2,z1051,z4,z7]),(0,[z0,z1052,z2,z3,z4,z7]),(0,[z0,z1,z1047,z14,z4,z7]),(0,[z388,z0,z2,z3,z48,z7]),(0,[z0,z1,z3,z4,z1053,z7]),(0,[z0,z1,z1054,z2,z4,z7]),(0,[z0,z1,z2,z4,z7,z1055]),(0,[z0,z1,z118,z49,z2,z4])],[(0,[z0,z1,z2,z3,z4,z1056]),(0,[z0,z1,z2,z16,z221,z862]),(0,[z0,z1,z2,z16,z54,z7]),(0,[z0,z1,z1057,z2,z3,z7])],[(0,[z0,z256,z2,z67,z4,z7]),(0,[z525,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z3,z4,z780]),(0,[z0,z1,z2,z3,z754,z153])],[(0,[z0,z1,z782,z3,z4,z7]),(0,[z0,z1,z163,z2,z3,z4]),(0,[z0,z2,z3,z740,z4,z7]),(0,[z0,z1,z2,z1058,z4,z7])],[(0,[z0,z1,z2,z3,z1059,z7]),(0,[z0,z1,z1060,z3,z4,z7]),(0,[z0,z1,z1061,z2,z3,z7]),(0,[z0,z1,z190,z2,z14,z7]),(0,[z0,z1,z58,z199,z3,z7]),(0,[z0,z1,z2,z3,z136,z11]),(0,[z1062,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z1063,z4,z7]),(0,[z1064,z1,z2,z3,z4,z7])],[(0,[z178,z0,z105,z52,z4,z7]),(0,[z0,z1,z2,z1065,z4,z7]),(0,[z0,z2,z3,z4,z55,z780])]],
   [[(0,[z1066,z1,z2,z3,z4,z7]),(0,[z0,z517,z2,z3,z4,z94]),(0,[z0,z1,z2,z1067,z4,z7]),(0,[z0,z1,z2,z3,z1068,z4]),(0,[z0,z1,z123,z3,z4,z56])],[(0,[z64,z1,z76,z3,z4,z7]),(0,[z0,z1,z123,z14,z4,z56]),(0,[z96,z1,z2,z16,z221,z7]),(0,[z0,z1,z2,z3,z75,z11])],[(0,[z64,z1,z76,z14,z4,z7]),(0,[z1,z2,z14,z4,z401,z7]),(0,[z0,z1,z2,z4,z1069,z7]),(0,[z0,z1,z393,z3,z4,z229]),(0,[z0,z1,z2,z4,z7,z241]),(0,[z0,z1,z2,z1070,z4,z7])],[(0,[z0,z1,z2,z90,z4,z40]),(0,[z0,z1,z2,z3,z303,z40]),(0,[z0,z1,z325,z2,z4,z115]),(0,[z0,z1,z73,z2,z17,z7]),(0,[z18,z1,z2,z3,z4,z861]),(0,[z0,z1,z9,z3,z4,z50])],[(0,[z0,z1,z709,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z493]),(0,[z1,z2,z722,z14,z4,z7]),(0,[z0,z1,z2,z92,z4,z488]),(0,[z1071,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z110,z14,z4]),(0,[z0,z222,z2,z3,z4,z229]),(0,[z0,z1,z2,z3,z1072,z7]),(0,[z0,z1,z2,z1073,z4,z7]),(0,[z0,z1,z2,z3,z7,z754])],[(0,[z0,z1,z22,z2,z4,z179])],[(0,[z0,z1,z2,z714,z3,z4])]],
   [[(0,[z0,z1,z2,z16,z183,z7]),(0,[z0,z138,z1,z72,z3,z4])],[(0,[z0,z1,z2,z1074,z4,z7]),(0,[z43,z1,z44,z102,z4,z7]),(0,[z0,z1,z2,z3,z4,z1075]),(0,[z0,z1,z325,z2,z16,z4]),(0,[z0,z121,z2,z3,z4,z94]),(0,[z0,z270,z2,z3,z155,z7])],[(0,[z0,z1,z1076,z3,z4,z7]),(0,[z0,z1,z2,z90,z303,z7]),(0,[z43,z1,z44,z16,z4,z7]),(0,[z0,z1,z2,z1077,z4,z7]),(0,[z0,z1,z2,z3,z4,z381])],[(0,[z0,z1,z2,z3,z1078,z7]),(0,[z0,z1,z2,z14,z4,z381]),(0,[z0,z1,z22,z53,z4,z7]),(0,[z0,z1,z2,z1079,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1080]),(0,[z1,z701,z2,z14,z4,z7]),(0,[z0,z33,z2,z16,z4,z7]),(0,[z1,z2,z3,z4,z1081,z7]),(0,[z0,z1,z2,z3,z4,z1082])],[(0,[z0,z1,z133,z3,z4,z40]),(0,[z0,z1,z2,z1083,z4,z7]),(0,[z0,z20,z1,z325,z2,z4]),(0,[z0,z1,z2,z10,z221,z7]),(0,[z0,z1,z2,z3,z4,z1084]),(0,[z0,z1,z2,z1085,z4,z7])],[(0,[z41,z267,z2,z3,z4,z7]),(1,[z1,z2,z722,z4,z7]),(0,[z0,z1,z325,z2,z14,z4]),(0,[z463,z1,z2,z14,z4,z7]),(0,[z82,z1,z701,z2,z3,z7]),(0,[z0,z126,z782,z3,z4,z7])],[(0,[z41,z267,z2,z14,z4,z7]),(0,[z0,z1,z448,z3,z4,z7]),(0,[z1,z706,z2,z14,z4,z7]),(0,[z0,z1,z2,z16,z908,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z7]),(0,[z635,z1,z76,z3,z4,z7]),(0,[z0,z1,z448,z14,z4,z7]),(0,[z0,z2,z3,z4,z831,z7]),(0,[z0,z1,z1086,z2,z3,z4]),(0,[z0,z1,z2,z1087,z4,z7])],[(0,[z0,z1,z2,z14,z4,z7]),(0,[z0,z1,z484,z410,z4,z7]),(0,[z0,z1,z1088,z2,z3,z7]),(0,[z181,z32,z2,z16,z4,z7]),(0,[z0,z1,z2,z3,z1089,z7]),(0,[z0,z1,z1090,z2,z4,z7]),(0,[z0,z1,z2,z1091,z4,z7]),(0,[z0,z1,z2,z3,z4,z441]),(0,[z0,z1,z2,z3,z4,z1092]),(0,[z0,z1,z1093,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1094]),(0,[z0,z1,z199,z3,z4,z7]),(0,[z0,z1,z2,z14,z4,z441]),(0,[z145,z1,z2,z16,z4,z7]),(1,[z0,z1,z805,z4,z7]),(0,[z0,z1,z2,z4,z21,z471])],[(0,[z41,z720,z2,z3,z4,z7]),(0,[z0,z1,z1095,z2,z3,z4]),(0,[z0,z1,z2,z4,z1096,z7]),(0,[z0,z1,z199,z14,z4,z7]),(0,[z0,z1,z2,z1097,z4,z7])],[(0,[z0,z1,z133,z3,z303,z7]),(0,[z0,z1,z1098,z2,z3,z7]),(0,[z0,z1099,z2,z3,z4,z7]),(0,[z0,z1100,z2,z3,z4,z7]),(0,[z0,z1,z738,z2,z3,z4]),(0,[z0,z1,z2,z1101,z4,z7])],[(0,[z0,z1,z2,z1102,z4,z7]),(0,[z1,z2,z14,z440,z4,z7]),(0,[z0,z138,z126,z3,z4,z7]),(0,[z0,z1,z1103,z2,z4,z7]),(0,[z0,z1,z2,z3,z4,z1104])],[(0,[z0,z1,z2,z1105,z4,z7]),(0,[z0,z1,z2,z759,z3,z7]),(0,[z0,z1,z2,z3,z1106,z7]),(0,[z97,z0,z2,z3,z357,z7]),(0,[z0,z1,z2,z16,z221,z7]),(0,[z0,z138,z126,z14,z4,z7]),(0,[z0,z1,z2,z140,z308,z4]),(0,[z0,z1,z2,z54,z21,z7]),(0,[z0,z1107,z2,z3,z4,z7])],[(0,[z91,z1,z2,z107,z315,z7])]],
   [[(0,[z43,z1,z44,z3,z4,z5]),(0,[z0,z1,z2,z1108,z4,z7]),(0,[z0,z1,z2,z3,z1109,z7]),(0,[z0,z112,z2,z3,z4,z55]),(0,[z0,z1,z2,z3,z4,z1110]),(0,[z0,z1,z2,z253,z75,z11])],[(0,[z0,z272,z1,z2,z14,z7]),(0,[z490,z1,z76,z3,z4,z7]),(0,[z0,z1,z1111,z3,z4,z7]),(0,[z18,z1,z2,z3,z4,z129])],[(0,[z18,z1,z2,z14,z4,z129]),(0,[z0,z431,z2,z128,z4,z7]),(0,[z359,z1,z2,z3,z315,z7]),(0,[z0,z1,z2,z1112,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1113]),(0,[z1,z708,z76,z3,z4,z7]),(0,[z77,z1,z2,z722,z4,z7]),(0,[z0,z1,z2,z763,z305,z4]),(0,[z0,z1,z2,z1114,z4,z7])],[(0,[z0,z1,z9,z14,z4,z7]),(0,[z0,z1,z475,z196,z4,z7]),(0,[z0,z1,z2,z16,z932,z7]),(0,[z0,z1,z22,z508,z4,z7])],[(0,[z1,z2,z14,z456,z4,z7]),(0,[z0,z1,z2,z3,z4,z229]),(0,[z699,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z3,z4,z66]),(0,[z0,z1,z73,z492,z2,z4])],[(0,[z0,z1,z2,z3,z1115,z7]),(0,[z0,z2,z3,z858,z4,z7]),(0,[z0,z1,z2,z14,z4,z66]),(0,[z0,z1,z2,z3,z4,z1116]),(0,[z0,z1,z1117,z3,z4,z7]),(0,[z0,z1,z3,z85,z729,z7])],[(0,[z32,z720,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z7,z1118]),(0,[z0,z1,z199,z3,z4,z229])]],
   [[(0,[z0,z1,z2,z16,z200,z7]),(0,[z178,z0,z1,z72,z3,z4]),(0,[z1119,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z488]),(0,[z0,z1,z2,z3,z4,z1120]),(0,[z0,z1,z124,z2,z4,z179]),(1,[z0,z2,z3,z748,z7]),(0,[z0,z1,z2,z1121,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1122]),(0,[z0,z1,z2,z14,z4,z488]),(0,[z0,z47,z2,z14,z155,z7]),(0,[z0,z1,z2,z38,z17,z7]),(0,[z0,z33,z2,z3,z83,z7]),(0,[z0,z33,z58,z2,z3,z7]),(0,[z0,z1,z3,z4,z1123,z7])],[(0,[z0,z1,z1124,z2,z4,z7]),(0,[z0,z1,z2,z3,z1125,z7]),(0,[z0,z256,z2,z287,z4,z7]),(0,[z0,z1,z199,z3,z4,z488]),(0,[z0,z1,z73,z2,z308,z4]),(0,[z0,z1,z2,z4,z21,z66]),(0,[z0,z1,z2,z1126,z4,z7])],[(0,[z0,z1,z1127,z3,z4,z7]),(0,[z0,z1,z841,z2,z14,z4])],[(0,[z0,z1,z341,z58,z3,z7]),(0,[z0,z2,z3,z748,z4,z7]),(1,[z0,z1,z3,z4,z834])],[(0,[z64,z1,z76,z384,z4,z7]),(0,[z0,z1,z1128,z3,z4,z7]),(0,[z0,z1,z1129,z2,z3,z4])],[(0,[z0,z1,z2,z1130,z4,z7]),(0,[z0,z33,z2,z3,z315,z7]),(0,[z0,z1,z49,z3,z4,z507]),(0,[z0,z45,z2,z46,z54,z7]),(0,[z0,z112,z1,z9,z3,z4]),(0,[z0,z1,z2,z1131,z4,z7]),(0,[z0,z1,z2,z253,z4,z7]),(0,[z0,z1,z2,z3,z4,z802])]],
   [[(0,[z0,z1,z798,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z830]),(0,[z0,z1,z2,z3,z4,z1132]),(0,[z0,z1,z3,z4,z497,z7]),(0,[z0,z1,z2,z140,z4,z802])],[(0,[z0,z1,z2,z3,z1133,z7]),(0,[z0,z1,z1134,z2,z3,z4]),(0,[z0,z1,z2,z4,z1135,z7]),(0,[z0,z1,z325,z2,z308,z4]),(0,[z0,z1,z2,z3,z1136,z7]),(0,[z0,z1,z2,z4,z7,z1137])],[(0,[z0,z1,z2,z4,z1138,z7])],[(0,[z0,z1,z73,z2,z4,z66]),(0,[z0,z1,z123,z3,z4,z834])],[(0,[z0,z1,z484,z3,z4,z333]),(0,[z0,z1,z771,z3,z4,z7]),(0,[z1,z2,z16,z14,z17,z7]),(0,[z345,z1,z2,z14,z4,z7]),(0,[z0,z1,z325,z124,z2,z4]),(0,[z0,z1,z2,z3,z4,z772]),(0,[z0,z1,z2,z92,z115,z7]),(0,[z91,z1,z270,z2,z3,z7]),(0,[z0,z1,z1139,z2,z3,z4]),(0,[z0,z1,z118,z2,z4,z94])],[(0,[z0,z1140,z2,z3,z4,z7]),(0,[z0,z1,z1141,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1142]),(0,[z0,z1,z2,z4,z21,z802])],[(0,[z0,z1,z2,z3,z4,z1143]),(0,[z0,z1,z1144,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1145]),(0,[z0,z1,z2,z4,z802,z61])],[(0,[z0,z1,z1146,z3,z4,z7]),(0,[z0,z1,z2,z1147,z4,z7]),(0,[z0,z1,z2,z1148,z4,z7]),(0,[z0,z138,z782,z3,z4,z7]),(0,[z0,z1,z2,z4,z365,z7])]],
   [[(0,[z0,z1,z58,z14,z85,z7]),(0,[z0,z1,z340,z2,z14,z4]),(0,[z0,z1,z2,z268,z38,z7]),(0,[z0,z1,z2,z16,z837,z7]),(0,[z0,z1,z2,z16,z972,z7])],[(0,[z0,z1,z2,z16,z303,z7]),(0,[z91,z33,z2,z3,z315,z7]),(0,[z0,z1,z2,z1149,z4,z7]),(0,[z522,z1,z2,z3,z4,z129]),(0,[z0,z1,z163,z105,z2,z4])],[(0,[z0,z1,z2,z1150,z4,z7]),(0,[z0,z1,z1151,z2,z4,z7]),(0,[z0,z1,z2,z3,z4,z1152]),(0,[z0,z1,z2,z16,z844,z7]),(0,[z0,z1,z2,z4,z1153,z7]),(0,[z0,z1,z73,z2,z4,z530])],[(0,[z0,z1,z2,z3,z255,z7]),(0,[z0,z174,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z1154,z7]),(0,[z0,z1,z952,z2,z210,z4]),(0,[z0,z1,z393,z107,z4,z7]),(0,[z0,z1,z2,z10,z343,z7])],[(0,[z0,z1,z49,z14,z4,z50]),(0,[z699,z1,z2,z14,z4,z7]),(0,[z0,z138,z3,z4,z246,z7]),(0,[z1,z2,z1155,z3,z4,z7]),(0,[z0,z1,z2,z3,z422,z4]),(0,[z0,z1,z2,z1156,z4,z7])],[(0,[z0,z1,z2,z384,z4,z7]),(0,[z0,z1,z2,z14,z422,z4]),(0,[z0,z1,z1157,z2,z4,z7]),(0,[z0,z79,z235,z2,z4,z94]),(0,[z0,z1,z73,z2,z4,z802])],[(0,[z0,z1,z2,z3,z986,z7]),(0,[z0,z222,z2,z107,z4,z7]),(0,[z0,z1,z1158,z2,z3,z4])],[(0,[z0,z1,z2,z228,z4,z7]),(0,[z0,z1,z123,z3,z4,z198]),(0,[z97,z0,z2,z16,z48,z7]),(0,[z0,z1,z2,z3,z1159,z7])]],
   [[(0,[z0,z32,z2,z3,z255,z7])],[(0,[z0,z1,z2,z1160,z4,z7]),(0,[z181,z32,z2,z117,z4,z7]),(0,[z0,z1,z1161,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1162]),(0,[z91,z1,z2,z16,z315,z7]),(0,[z291,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z1163,z4,z7]),(0,[z1164,z1,z2,z3,z4,z7]),(0,[z0,z1,z3,z805,z4,z7])],[(0,[z0,z20,z2,z545,z4,z7]),(0,[z0,z1,z1165,z3,z4,z7]),(0,[z0,z1,z258,z163,z2,z4]),(0,[z0,z1,z2,z3,z4,z179]),(0,[z0,z1,z1166,z2,z4,z7])],[(0,[z637,z1,z2,z14,z4,z7]),(0,[z0,z1,z2,z14,z4,z179]),(0,[z0,z1,z3,z4,z1048,z7]),(0,[z0,z1,z2,z1167,z4,z7]),(0,[z0,z1,z2,z4,z365,z66]),(0,[z0,z1,z2,z1168,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1169]),(0,[z0,z1,z2,z228,z1106,z7]),(0,[z0,z1,z2,z3,z4,z826]),(0,[z209,z1,z2,z3,z4,z129]),(0,[z0,z1,z2,z3,z1170,z7])],[(0,[z0,z1,z2,z1171,z4,z7])],[(0,[z0,z174,z1,z2,z16,z7]),(0,[z0,z1,z2,z1172,z4,z7]),(0,[z1,z599,z2,z16,z4,z7]),(0,[z0,z1,z2,z221,z17,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z1173]),(0,[z601,z1,z2,z16,z4,z7]),(0,[z0,z1,z2,z16,z4,z271]),(0,[z0,z47,z33,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z861]),(0,[z0,z1,z71,z99,z4,z7]),(0,[z0,z1,z2,z3,z4,z754])],[(0,[z0,z1,z1174,z2,z4,z7]),(0,[z96,z1,z2,z16,z17,z7]),(0,[z0,z1,z1175,z2,z4,z7]),(0,[z320,z1,z2,z3,z4,z129])],[(0,[z0,z1,z484,z3,z255,z7]),(0,[z0,z1,z36,z3,z37,z7]),(0,[z0,z1,z2,z1176,z4,z7]),(0,[z0,z1,z194,z2,z3,z754])],[(0,[z41,z267,z2,z410,z4,z7]),(0,[z0,z1,z2,z880,z117,z4]),(0,[z0,z1,z36,z14,z37,z7]),(0,[z0,z1,z2,z92,z4,z229]),(0,[z1177,z1,z2,z3,z4,z7]),(0,[z178,z0,z258,z52,z4,z7]),(0,[z0,z1,z2,z1178,z4,z7]),(0,[z0,z1,z675,z73,z2,z4])],[(0,[z0,z1,z1179,z3,z4,z7]),(0,[z97,z0,z174,z2,z3,z7]),(0,[z0,z1,z341,z3,z37,z7]),(0,[z1,z2,z609,z16,z4,z7])],[(0,[z0,z1,z2,z410,z4,z7]),(0,[z0,z1,z2,z1180,z4,z7]),(0,[z0,z1,z2,z14,z75,z11]),(0,[z0,z1181,z1,z2,z3,z7]),(0,[z0,z2,z3,z748,z155,z7])],[(0,[z0,z1,z1182,z3,z4,z7])],[(0,[z0,z1,z2,z1183,z4,z7]),(0,[z0,z1,z863,z2,z3,z7]),(0,[z1,z2,z16,z14,z4,z7]),(0,[z178,z0,z782,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z14,z4,z493]),(0,[z1,z231,z2,z14,z4,z7]),(0,[z0,z1,z73,z2,z110,z4]),(0,[z0,z1,z1184,z3,z4,z7]),(0,[z0,z1,z2,z3,z1185,z7])],[(0,[z0,z1,z708,z3,z4,z7]),(0,[z0,z1,z279,z283,z4,z7])],[(0,[z0,z1,z2,z90,z4,z7]),(0,[z0,z1,z2,z3,z903,z7]),(0,[z0,z1,z2,z308,z4,z7]),(0,[z0,z1,z2,z16,z885,z7]),(0,[z178,z0,z163,z52,z3,z4]),(0,[z0,z1,z2,z3,z4,z1186]),(1,[z0,z1,z2,z4,z802])],[(0,[z41,z272,z267,z2,z3,z7]),(0,[z0,z1187,z2,z3,z4,z7]),(0,[z0,z33,z2,z92,z4,z7]),(0,[z0,z1,z2,z1188,z4,z7])],[(0,[z0,z1,z2,z1189,z4,z7]),(0,[z0,z1,z2,z1190,z4,z7]),(0,[z0,z1,z2,z103,z4,z7]),(0,[z591,z1,z2,z14,z4,z7]),(0,[z0,z1,z163,z2,z16,z4]),(0,[z82,z1,z2,z98,z83,z7]),(0,[z0,z1,z2,z1191,z4,z7]),(0,[z0,z45,z2,z46,z200,z7]),(0,[z0,z1,z2,z3,z4,z1192])],[(0,[z0,z33,z393,z3,z4,z7]),(0,[z0,z1,z2,z1193,z4,z7]),(0,[z0,z1,z2,z1194,z4,z7]),(0,[z0,z1,z2,z1195,z4,z7])],[(0,[z0,z1,z325,z2,z110,z4]),(0,[z0,z431,z2,z46,z4,z7]),(0,[z0,z1,z2,z107,z4,z7]),(0,[z0,z1,z72,z105,z2,z4]),(0,[z0,z1,z340,z124,z2,z4]),(0,[z0,z1,z2,z3,z774,z7])],[(0,[z0,z1196,z2,z3,z4,z7]),(0,[z0,z1,z2,z14,z1078,z7]),(0,[z0,z1,z438,z53,z4,z7]),(0,[z1,z2,z3,z733,z315,z7]),(0,[z15,z1,z2,z99,z4,z19]),(0,[z0,z1,z3,z4,z834,z56])]],
   [[(0,[z0,z1,z199,z107,z4,z7]),(0,[z91,z1,z2,z3,z733,z7]),(0,[z0,z646,z2,z3,z155,z7])],[(0,[z0,z1,z2,z3,z4,z1197]),(0,[z0,z1,z1198,z2,z4,z7]),(0,[z0,z1,z2,z16,z4,z1033]),(0,[z0,z79,z321,z2,z3,z4]),(0,[z0,z1,z124,z125,z4,z7]),(0,[z0,z1,z2,z3,z4,z1199])],[(0,[z0,z1,z484,z3,z4,z40]),(0,[z0,z1,z2,z1200,z4,z7])],[(0,[z0,z1,z2,z1201,z4,z7]),(0,[z18,z1,z2,z308,z4,z129]),(0,[z0,z2,z3,z4,z780,z94]),(0,[z0,z1,z3,z4,z50,z834])],[(0,[z0,z1,z2,z3,z1202,z7]),(0,[z0,z1,z2,z3,z4,z1203])],[(0,[z0,z1,z2,z3,z1204,z7]),(0,[z0,z1,z448,z3,z4,z129]),(0,[z0,z1,z3,z4,z7,z1205])],[(0,[z0,z1,z393,z16,z4,z7]),(0,[z0,z1,z2,z16,z4,z862]),(0,[z1206,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z16,z917,z7]),(0,[z0,z1,z2,z3,z924,z7]),(0,[z0,z1,z2,z3,z54,z7]),(0,[z0,z47,z2,z3,z748,z7]),(0,[z0,z1,z2,z1207,z4,z7])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 526) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 526).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1053).take 187) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1240)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [526, 527, 187] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 104).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 104).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 221).take 35).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [104, 117, 35] = true :=
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

end PEqualNP.Outside.L_meta_38771

theorem PEqualNP.Outside.L_meta_38771 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4238919816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4238919816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38771.solve