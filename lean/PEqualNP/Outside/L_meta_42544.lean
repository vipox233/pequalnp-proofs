import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42544

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
  Nat.testBit (4276812992 * 2 ^ 32 + 4241029248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0635e631910cc6ea#64 ++ 0x2418d798c644331b#64 ++ 0x0e7fe631911ccffd#64 ++ 0x2439ff98c644733f#64 : BitVec 256),
   (0x108c02d606770b4c#64 ++ 0x0842300b5819dc2d#64 ++ 0x318c07fe1fff0ffb#64 ++ 0x7cc6301ff87ffc3f#64 : BitVec 256),
   (0x4170282aa1a151b0#64 ++ 0x0105c0a0aa868546#64 ++ 0xc1f0783fe1e3f1f7#64 ++ 0xbf07c1e0ff878fc7#64 : BitVec 256),
   (0xae0055415a02ac00#64 ++ 0x02b8015505680ab0#64 ++ 0xfe007fc1fe03fe2f#64 ++ 0xfff801ff07f80ff8#64 : BitVec 256),
   (0xfbda8001fdd80000#64 ++ 0x43ef6a0007f76000#64 ++ 0xffff8001fffc003f#64 ++ 0xcbfffe0007fff000#64 : BitVec 256),
   (0xfdef7fbc00000000#64 ++ 0x33f7bdfef0000000#64 ++ 0xfffffffe0000001f#64 ++ 0xf3fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [6, 12]⟩, ⟨.and, [13, 9]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7fe631911ccffd 0x2439ff98c644733f

def z1 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318c07fe1fff0ffb 0x7cc6301ff87ffc3f

def z2 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc1f0783fe1e3f1f7 0xbf07c1e0ff878fc7

def z3 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xfe007fc1fe03fe2f 0xfff801ff07f80ff8

def z4 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffff8001fffc003f 0xcbfffe0007fff000

def z5 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z6 : W := mkw 0xfdef7fbc00040248 0x33f7bdfef0001009 0xfffffffe111c0fff 0xf7fffffff844703f

def z7 : W := mkw 0xfbda880bfdf91110 0x43ef6a202ff7e444 0xffff980fffff303f 0xdbfffe603ffffcc0

def z8 : W := mkw 0xfdca5d8c00000000 0x13f7297630000000 0xff807fce0000000f 0xf3fe01ff38000000

def z9 : W := mkw 0xf9ce1bde06770b4c 0x1be7386f7819dc2d 0xf18c1ffe1fff0ffb 0xffc6307ff87ffc3f

def z10 : W := mkw 0xae0055015800a400 0x02b8015405600290 0xfe007801fe00f02f 0xcbf801e007f803c0

def z11 : W := mkw 0xaa00000158000000 0x02a8000005600000 0xfe000001fe00002f 0xcbf8000007f80000

def z12 : W := mkw 0xffdad541ffdaac00 0x43ff6b5507ff6ab0 0xffffffc1fffffe3f 0xffffffff07fffff8

def z13 : W := mkw 0x4170286aa3a359b0 0x0105c0a1aa8e8d66 0xf1f07fffffe3ffff 0xffc7c1ffffff8fff

def z14 : W := mkw 0x0635e631fddcc6ea 0x6418d798c7f7731b 0x0e7fe631fffccffd 0x2c39ff98c7fff33f

def z15 : W := mkw 0x042566300004c6ea 0x24109598c000131b 0x000066300000cfc0 0x24000198c000033f

def z16 : W := mkw 0xfdef7fbc0004c6ea 0x37f7bdfef000131b 0xfffffffe0000cfdf 0xf7fffffff800033f

def z17 : W := mkw 0x51fc2abea5f553fc 0x0947f0aafa97d54f 0x01fc003e01fc01d0 0x0007f000f807f007

def z18 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xfe0007c1fe000e2f 0xcbf8001f07f80038

def z19 : W := mkw 0x0004021000040248 0x0000100840001009 0x000c0630111c0ff9 0x24003018c044703f

def z20 : W := mkw 0xfbda8001f9880000 0x43ef6a0007e62000 0xffff8001e000001f 0xc3fffe0007800000

def z21 : W := mkw 0x108c02960475034c 0x0842300a5811d40d 0x318c003e1ffc01fb 0x48c63000f87ff007

def z22 : W := mkw 0x0631e4219108c4a2 0x2418c79086442312 0x0e73e0018000c004 0x0039cf8006000300

def z23 : W := mkw 0x108800c606730904 0x084220031819cc24 0x318001ce0ee30002 0x58c60007383b8c00

def z24 : W := mkw 0x0000004002020800 0x0000000100080820 0x300007c01e030e2b 0x7cc0001f00780c38

def z25 : W := mkw 0xbe8c57d75e77af4c 0x0afa315f5d79debd 0xff8c7fffffffffff 0xfffe31ffffffffff

def z26 : W := mkw 0x41500000a1800000 0x0105400002860000 0xc1f00001e1e00037 0x8b07c00007878000

def z27 : W := mkw 0xfbfaa82bfdf951b0 0x43efeaa0aff7e546 0xfffff83ffffff1ff 0xffffffe0ffffffc7

def z28 : W := mkw 0xfbca80017cd80000 0x43ef2a0005f36000 0xff8f80007efc000a 0xcbfe3e0001fbf000

def z29 : W := mkw 0x51ffa230a5dc42ea 0x6547fe88c297710b 0x01ff803001fc01d0 0x0007fe00c007f007

def z30 : W := mkw 0x108c02d406560a4c 0x0842300b50195829 0x300c07c01e1f0e2b 0x7cc0301f00787c38

def z31 : W := mkw 0x0000000200210100 0x0000000008008404 0x0180003e01e301f3 0x3c060000f8078c07

def z32 : W := mkw 0x51fc2afea7f75bfc 0x0947f0abfa9fdd6f 0xf1fc7fffffffffff 0xffc7f1ffffffffff

def z33 : W := mkw 0x4140000020800000 0x0105000000820000 0xc180000060e00002 0x8b06000001838000

def z34 : W := mkw 0xfbda9141ffda2800 0x43ef6a4507ff68a0 0xffff99c1ffff303f 0xdbfffe6707fffcc0

def z35 : W := mkw 0xf9ca198c00000000 0x13e7286630000000 0xf18019ce00000002 0xd3c6006738000000

def z36 : W := mkw 0xffffffbd910cc6ea 0x37fffffef644331b 0xffffffff911ccfff 0xf7fffffffe44733f

def z37 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0x3e0007c01e000e08 0x40f8001f00780038

def z38 : W := mkw 0xef707d6bfba3fdb0 0x03bdc1f5afee8ff6 0xfff07fffffe3ffff 0xffffc1ffffff8fff

def z39 : W := mkw 0xbc8f579400000000 0x32f23d5e50000000 0x3e0f87c000000008 0x40f83e1f00000000

def z40 : W := mkw 0xffef7ffd5a02ac00 0x33ffbdfff5680ab0 0xfffffffffe03fe3f 0xfffffffffff80ff8

def z41 : W := mkw 0x108c02960475034c 0x0842300a5811d40d 0x018c003e01fc01d0 0x00063000f807f007

def z42 : W := mkw 0xfdeb7dac00000000 0x33f7adf6b0000000 0xfff3f9ce00000006 0xd3ffcfe738000000

def z43 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180003e00000013 0x30060000f8000000

def z44 : W := mkw 0x0004029400000000 0x0000100a50000000 0x000007fe00000000 0x3000001ff8000000

def z45 : W := mkw 0xffffffbffdf951b0 0x73fffffefff7e546 0xfffffffffffff1ff 0xffffffffffffffc7

def z46 : W := mkw 0xac0055400202ac00 0x02b0015500080ab0 0xfe007fc00003fe0f 0xf7f801ff00000ff8

def z47 : W := mkw 0xffffffbfb1add7fa 0x37fffffefec6b75f 0xfffffffff1ffffff 0xffffffffffc7ffff

def z48 : W := mkw 0xae00440158008400 0x02b8011005600210 0xfe006601fe00ce2f 0xeff8019807f80338

def z49 : W := mkw 0x0405579400000000 0x3010155e50000000 0x000007c000000000 0x0000001f00000000

def z50 : W := mkw 0xffffe631fddcc6ea 0x67ffff98c7f7731b 0xffffe631fffccfff 0xefffff98c7fff33f

def z51 : W := mkw 0xbe8c57d55e56ae4c 0x0afa315f55795ab9 0x3e0c07c01e1c0e08 0x40f8301f00787038

def z52 : W := mkw 0x51ff2abea1a151b0 0x3147fcaafa868546 0xc1fff83fe1e3f1f7 0xbf07ffe0ff878fc7

def z53 : W := mkw 0x00100000a18050b0 0x0000400002860142 0x00000001e000f000 0x00000000078003c0

def z54 : W := mkw 0xba8a80015c580000 0x42ea2a0005716000 0x3f8f80001ffc003b 0x48fe3e00007ff000

def z55 : W := mkw 0xffff7ffffba3fdb0 0x33fffdffffee8ff6 0xffffffffffe3ffff 0xffffffffffff8fff

def z56 : W := mkw 0x00100002a1a151b0 0x000040000a868546 0x00000001e1e3f1e0 0x0c00000007878fc7

def z57 : W := mkw 0x0000004206770b4c 0x080000010819dc2d 0x000000001fff0fe0 0x0c000000007ffc3f

def z58 : W := mkw 0x02108001fdd80000 0x4008420007f76000 0x00000001fffc0020 0x0800000007fff000

def z59 : W := mkw 0xef607d695a02ac00 0x03bd81f5a5680ab0 0xfff07ffffe03fe3f 0xffffc1fffff80ff8

def z60 : W := mkw 0x108c029600210100 0x0042300a58008404 0x318c07fe01e301fb 0x7cc6301ff8078c07

def z61 : W := mkw 0x16bde6f7977fcfee 0x2c5af79bde5dff3f 0x3fffe7ff9fffcfff 0x7cffff9ffe7fff3f

def z62 : W := mkw 0x02108043977fcfee 0x0c0842010e5dff3f 0x000000019fffcfe0 0x0c000000067fff3f

def z63 : W := mkw 0x4140080a20a11110 0x0105002028828444 0xc180180e60e33002 0x9b06006039838cc0

def z64 : W := mkw 0x000402d602270b4c 0x0800100b58089c2d 0x000c07fe111f0ff9 0x3400301ff8447c3f

def z65 : W := mkw 0xf9ca00006cd00000 0x43e7280001b34000 0xffff80006ee0001f 0xcbfffe0001bb8000

def z66 : W := mkw 0xffded7d7ffffaf4c 0x4bff7b5f5ffffebd 0xffffffffffffffff 0xffffffffffffffff

def z67 : W := mkw 0x4160282800000000 0x010580a0a0000000 0xc1f0783e00000017 0xb307c1e0f8000000

def z68 : W := mkw 0xfdff7fbea1a151b0 0x33f7fdfefa868546 0xffffffffe1e3f1ff 0xffffffffff878fc7

def z69 : W := mkw 0xac25773000000000 0x22b095dcc0000000 0xfe7ffff00000001f 0xf3f9ffffc0000000

def z70 : W := mkw 0x0000004202270b4c 0x0800000108089c2d 0x0000000000030fc0 0x0400000000000c3f

def z71 : W := mkw 0xef505541fb82ac00 0x03bd415507ee0ab0 0xfff07fc1ffe3fe3f 0xffffc1ff07ff8ff8

def z72 : W := mkw 0x0635ffbd910cc6ea 0x3418d7fef644331b 0x0e7fffff911ccffd 0x3439fffffe44733f

def z73 : W := mkw 0x00302020810040a0 0x0000c08082040102 0x007060318100c1f5 0x2401c180c6040307

def z74 : W := mkw 0x4775ee3bb1add7fa 0x251dd7b8eec6b75f 0xcffffe3ff1ffffff 0xbf3ffff8ffc7ffff

def z75 : W := mkw 0x129c82d7977fcfee 0x0c4a720b5e5dff3f 0x318c07ff9fffcffb 0x7cc6301ffe7fff3f

def z76 : W := mkw 0xfdef7fbc04500000 0x33f7bdfef0114000 0xfffffffe1ffc003f 0xfbfffffff87ff000

def z77 : W := mkw 0x14ad66b400000000 0x2052b59ad0000000 0x3fffe7fe0000001f 0x70ffff9ff8000000

def z78 : W := mkw 0x02008001100c864a 0x0408020004403219 0x00000000101c0e00 0x0000000000407038

def z79 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xcffff83e00000014 0x833fffe0f8000000

def z80 : W := mkw 0x02108043ffff0b4c 0x480842010ffffc2d 0x00000001ffff0fe0 0x0c00000007fffc3f

def z81 : W := mkw 0xf9ca00006cd00000 0x43e7280001b34000 0xf18000006ee00002 0xcbc6000001bb8000

def z82 : W := mkw 0x04256e3a0025d7fa 0x241095b8e800975f 0x00007e3e0003ffc0 0x340001f8f8000fff

def z83 : W := mkw 0xfdef7fbc6cd00000 0x73f7bdfef1b34000 0xfffffffe6ee0001f 0xfbfffffff9bb8000

def z84 : W := mkw 0x1088000004500000 0x0042200000114000 0x318c00001ffc003b 0x48c63000007ff000

def z85 : W := mkw 0xfbde82d7ffff0b4c 0x4bef7a0b5ffffc2d 0xffff87ffffff0fff 0xfffffe1ffffffc3f

def z86 : W := mkw 0x51ef2abc00000000 0x3147bcaaf0000000 0x01ff803e00000010 0x0007fe00f8000000

def z87 : W := mkw 0xf9ca198c6cd00000 0x53e7286631b34000 0xf18019ce6ee00002 0xdbc6006739bb8000

def z88 : W := mkw 0xfdef663000000000 0x23f7bd98c0000000 0xffffe6300000001f 0xe3ffff98c0000000

def z89 : W := mkw 0x000402d602270b4c 0x0800100b58089c2d 0x000007fe00030fc0 0x3400001ff8000c3f

def z90 : W := mkw 0x04257fbc00000000 0x301095fef0000000 0x00007ffe00000000 0x300001fff8000000

def z91 : W := mkw 0x12988001fdd80000 0x404a620007f76000 0x318c0001fffc003b 0x48c6300007fff000

def z92 : W := mkw 0x0020282a002151b0 0x000080a0a8008546 0x0000003e000001c0 0x00000000f8000007

def z93 : W := mkw 0xf9ea39ac00000000 0x13e7a8e6b0000000 0xf1f079fe00000017 0xf3c7c1e7f8000000

def z94 : W := mkw 0xfffffffddb0eeeea 0x37fffffff76c3bbb 0xffffffffff1fffff 0xfffffffffffc7fff

def z95 : W := mkw 0x108800c606730904 0x084220031819cc24 0x318007ce1ee30e2b 0x7cc6001f387b8c38

def z96 : W := mkw 0xae0055435e77af4c 0x0ab801550d79debd 0xfe007fc1ffffffef 0xfff801ff07ffffff

def z97 : W := mkw 0x0000004206770b4c 0x080000010819dc2d 0x0180003e1fff0ff3 0x3c060000f87ffc3f

def z98 : W := mkw 0x51ca088c00000000 0x1147282230000000 0x0180000e00000000 0x0006000038000000

def z99 : W := mkw 0xaa0011415a022800 0x02a80045056808a0 0xfe0019c1fe03302f 0xdbf8006707f80cc0

def z100 : W := mkw 0x000402d606770b4c 0x0800100b5819dc2d 0x000007fe1fff0fe0 0x3c00001ff87ffc3f

def z101 : W := mkw 0x02148211910c0248 0x0008520846443009 0x0e7f8631911c0ffd 0x2439fe18c644703f

def z102 : W := mkw 0x0035a230810c42ea 0x2400d688c204310b 0x007f8030011c01d0 0x0001fe00c0047007

def z103 : W := mkw 0x0600440110008400 0x0018011004400210 0x0e0066019000ce2d 0x2438019806400338

def z104 : W := mkw 0x020000015800a400 0x0008000005600290 0x00000001e000f000 0x00000000078003c0

def z105 : W := mkw 0xb88a000000000000 0x02e2280000000000 0x3e0f800000000008 0x40f83e0000000000

def z106 : W := mkw 0x00100042a7f75bfc 0x080040010a9fdd6f 0x00000001ffffffe0 0x0c00000007ffffff

def z107 : W := mkw 0x41500000a1800000 0x0105400002860000 0x01f0000001e00010 0x0007c00000078000

def z108 : W := mkw 0xf9ce1b9c00000000 0x13e7386e70000000 0xf18c1ffe0000001b 0xf3c6307ff8000000

def z109 : W := mkw 0x000402960025034c 0x0800100a5800940d 0x0000003e000001c0 0x00000000f8000007

def z110 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0xce7ffe31f11fffff 0xbf39fff8c7c47fff

def z111 : W := mkw 0x108800c606730904 0x084220031819cc24 0x318c01ce1fff003b 0x58c63007387ffc00

def z112 : W := mkw 0xba8c02d75e770b4c 0x0aea300b5d79dc2d 0xff8c07ffffff0fff 0xfffe301ffffffc3f

def z113 : W := mkw 0xfbde8211fddc0248 0x43ef7a0847f77009 0xffff8631fffc0fff 0xeffffe18c7fff03f

def z114 : W := mkw 0x0210800191080000 0x0008420006442000 0x0e7f8001911c003d 0x0039fe0006447000

def z115 : W := mkw 0x41702828a18050b0 0x0105c0a0a2860142 0xc0707801e003f027 0xbf01c1e007800fc0

def z116 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0x3e007fc01e03fe08 0x74f801ff00780ff8

def z117 : W := mkw 0x51faa82aa5f951b0 0x4147eaa0aa97e546 0xc1fff83fe1fff1f7 0xbf07ffe0ff87ffc7

def z118 : W := mkw 0x020000415a02ac00 0x0008000105680ab0 0x00000001fe03fe20 0x0c00000007f80ff8

def z119 : W := mkw 0xac00550000000000 0x02b0015400000000 0xfe007fc00000000f 0xf3f801ff00000000

def z120 : W := mkw 0xffffffbd9108c4a2 0x37fffffef6442312 0xffffffff8000c01f 0xf3fffffffe000300

def z121 : W := mkw 0x108c029400000000 0x0042300a50000000 0x318c07fe0000001b 0x70c6301ff8000000

def z122 : W := mkw 0xf9ca000000000000 0x03e7280000000000 0xffff80000000001f 0xc3fffe0000000000

def z123 : W := mkw 0xfdef7ffe06770b4c 0x3bf7bdfff819dc2d 0xfffffffe1fff0fff 0xfffffffff87ffc3f

def z124 : W := mkw 0x51fc2afea7f75bfc 0x0947f0abfa9fdd6f 0x31fc07fe1fff0ffb 0x7cc7f01ff87ffc3f

def z125 : W := mkw 0x042577700206eeea 0x241095ddc0081bbb 0x00007ff00003ffc0 0x340001ffc0000fff

def z126 : W := mkw 0x51ca000024d00000 0x4147280000934000 0x0180000000e00000 0x0006000000038000

def z127 : W := mkw 0xba8e82d55e5e0a4c 0x4aea3a0b55797829 0x3e0f87c01e1c0e08 0x40f83e1f00787038

def z128 : W := mkw 0xffdfd795fdd80000 0x73ff7f5e57f76000 0xffff87c1fffc003f 0xcbfffe1f07fff000

def z129 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318c07ce1eff0e0a 0x58c6301f387bfc38

def z130 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0007801e003f027 0xbf0001e007800fc0

def z131 : W := mkw 0x108c02d406560a4c 0x0842300b50195829 0x300c07c01e1c0e08 0x40c0301f00787038

def z132 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000001e003f020 0x0c00000007800fc0

def z133 : W := mkw 0x108c029404500000 0x0042300a50114000 0x318c07fe1ffc003b 0x78c6301ff87ff000

def z134 : W := mkw 0xae2577715a06eeea 0x26b895ddc5681bbb 0xfe007ff1fe03ffef 0xfff801ffc7f80fff

def z135 : W := mkw 0x0635e671db0eeeea 0x2418d799c76c3bbb 0x0e7fe631ff1ffffd 0x2c39ff98c7fc7fff

def z136 : W := mkw 0xae0055015800a400 0x02b8015405600290 0xce007e01f000fe2d 0xa73801f807c003f8

def z137 : W := mkw 0xf9da8000edd80000 0x43e76a0003b76000 0xf1ff80006ffc0012 0xcbc7fe0001bff000

def z138 : W := mkw 0xf9ca198c00000000 0x13e7286630000000 0xffff99ce0000001f 0xd3fffe6738000000

def z139 : W := mkw 0xae05d7515a0eae4a 0x26b8175d45683ab9 0x3e0f87c01e1c0e08 0x40f83e1f00787038

def z140 : W := mkw 0x53da8001b5d80000 0x414f6a0006d76000 0x0fff800191fc003d 0x003ffe000647f000

def z141 : W := mkw 0x16bde6b7957dc7ee 0x2c5af79ade55f71f 0x0fffe63f91fccffd 0x243fff98fe47f33f

def z142 : W := mkw 0xffdad501fdd8a400 0x43ff6b5407f76290 0xfffff801fffcf03f 0xcbffffe007fff3c0

def z143 : W := mkw 0x040055400202ac00 0x0010015500080ab0 0x00007fc00003fe00 0x340001ff00000ff8

def z144 : W := mkw 0xffffffff977fcfee 0x3ffffffffe5dff3f 0xffffffff9fffcfff 0xfffffffffe7fff3f

def z145 : W := mkw 0xffdac401fdd88400 0x43ff6b1007f76210 0xffffe601fffcce3f 0xefffff9807fff338

def z146 : W := mkw 0xe942000000000000 0x03a5080000000000 0xce73800000000004 0x8339ce0000000000

def z147 : W := mkw 0xed637d2800000000 0x33b58df4a0000000 0xce73f80000000004 0x8339cfe000000000

def z148 : W := mkw 0x51ef2abe0475034c 0x3947bcaaf811d40d 0x01ff803e01fc01d0 0x0007fe00f807f007

def z149 : W := mkw 0xbe8f57d55a02ac00 0x32fa3d5f55680ab0 0xfe0fffc1fe03fe2f 0xfff83fff07f80ff8

def z150 : W := mkw 0x02108001910cc6ea 0x040842000644331b 0x0e7f8001911ccffd 0x0439fe000644733f

def z151 : W := mkw 0x0605c611100c864a 0x2418171844403219 0x0e0f8600101c0e08 0x00383e1800407038

def z152 : W := mkw 0x000000006cd00000 0x4000000001b34000 0x000000006ee00000 0x0800000001bb8000

def z153 : W := mkw 0x4160282800000000 0x010580a0a0000000 0x01f0003e00000010 0x0007c000f8000000

def z154 : W := mkw 0x0615c611910c864a 0x2418571846443219 0x0e7f8601911c0e3d 0x0039fe1806447038

def z155 : W := mkw 0x51ff2abea1a151b0 0x3147fcaafa868546 0x01ff803e01e001d0 0x0007fe00f8078007

def z156 : W := mkw 0xaa108001d9080000 0x02a8420007642000 0xfe7f8001ff1c003f 0xcbf9fe0007fc7000

def z157 : W := mkw 0xb88c13d64e772b4c 0x0ae2304f5939dcad 0xf18c1ffe7fff3ffb 0xffc6307ff9fffcff

def z158 : W := mkw 0xf9da8000a5d80000 0x43e76a0002976000 0xffff800001fc001f 0xc3fffe000007f000

def z159 : W := mkw 0x4771ec2bb1a9d5b2 0x251dc7b0aec6a756 0xcff3f83fe1e3f1f7 0xbf3fcfe0ff878fc7

def z160 : W := mkw 0x0600440110008400 0x0018011004400210 0x0e00060010000e08 0x0038001800400038

def z161 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0xf18c7fffffffffff 0xffc631ffffffffff

def z162 : W := mkw 0x57ffe631b5dcc6ea 0x655fff98c6d7731b 0x0fffe63191fccffd 0x243fff98c647f33f

def z163 : W := mkw 0x41500000a1800000 0x0105400002860000 0xc0700001e0000004 0x8301c00007800000

def z164 : W := mkw 0xffffe631910cc6ea 0x27ffff98c644331b 0xffffe631911ccfff 0xe7ffff98c644733f

def z165 : W := mkw 0x10bda2f6877f4bee 0x2c42f68bda1dfd2f 0x31ff87fe1fff0ffb 0x7cc7fe1ff87ffc3f

def z166 : W := mkw 0x0000000200210100 0x0000000008008404 0x0180003e01e001d0 0x00060000f8078007

def z167 : W := mkw 0xfdef7ffc02020800 0x33f7bdfff0080820 0xfffffffe1e030e3f 0xfffffffff8780c38

def z168 : W := mkw 0x0600440110008400 0x0018011004400210 0x0e0060018000c004 0x0038018006000300

def z169 : W := mkw 0x000000404a022800 0x00000001012808a0 0x000000006e033000 0x0800000001b80cc0

def z170 : W := mkw 0xba8800015c500000 0x02ea200005714000 0xff8c0001fffc003f 0xcbfe300007fff000

def z171 : W := mkw 0xf9ca00c66ef30904 0x4be7280319bbcc24 0xf18001ce6ee30002 0xdbc6000739bb8c00

def z172 : W := mkw 0x128c02d75e77af4c 0x084a300b5d79debd 0x318c07fffffffffb 0x7cc6301fffffffff

def z173 : W := mkw 0x1088000204710100 0x004220000811c404 0x318c003e1fff01fb 0x7cc63000f87ffc07

def z174 : W := mkw 0x0435e630810cc6ea 0x2410d798c204331b 0x007fe630011ccfd0 0x2401ff98c004733f

def z175 : W := mkw 0x0000080a00211110 0x0000002028008444 0x0000180e00033000 0x1000006038000cc0

def z176 : W := mkw 0xffffffbd91080000 0x33fffffef6442000 0xffffffff911c003f 0xf3fffffffe447000

def z177 : W := mkw 0xed737d28a18050b0 0x33b5cdf4a2860142 0xce73f801e000f004 0x8339cfe0078003c0

def z178 : W := mkw 0x0031a020810840a2 0x2400c68082042102 0x0073800000000000 0x0001ce0000000000

def z179 : W := mkw 0xfdffffbc810c42ea 0x37f7fffef204310b 0xfffffffe011c01df 0xf3fffffff8047007

def z180 : W := mkw 0x41702020a18040a0 0x0105c08082860102 0xc1f06031e1e0c1f7 0xaf07c180c7878307

def z181 : W := mkw 0xf9ca19ce06730904 0x1be728673819cc24 0xf18019ce0ee30002 0xdbc60067383b8c00

def z182 : W := mkw 0x02148211910cc6ea 0x040852084644331b 0x000c0631911ccff9 0x24003018c644733f

def z183 : W := mkw 0x000402d602270b4c 0x0800100b58089c2d 0x018007fe01e30ff3 0x3c06001ff8078c3f

def z184 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc1f0183e61e331d2 0x9b07c060f9878cc7

def z185 : W := mkw 0xeb72a829f98850b0 0x43adcaa0a7e62142 0xce73f801e000f004 0x8339cfe0078003c0

def z186 : W := mkw 0xef52d501f988a400 0x43bd4b5407e62290 0xce73f801e000f004 0x8339cfe0078003c0

def z187 : W := mkw 0x45656e3800000000 0x211595b8e0000000 0xcffffe3e0000001f 0xb33ffff8f8000000

def z188 : W := mkw 0x04257fbc00000000 0x301095fef0000000 0x0e7ffffe0000001d 0x3039fffff8000000

def z189 : W := mkw 0xfdef7fbe00210100 0x33f7bdfef8008404 0xfffffffe01e301ff 0xfffffffff8078c07

def z190 : W := mkw 0x51c808ce26f31914 0x09472023389bcc64 0xf18019ce6ee33002 0xdbc6006739bb8cc0

def z191 : W := mkw 0xbebdf7f7df7fefee 0x2efaf7dfdf7dffbf 0xffffffffffffffff 0xffffffffffffffff

def z192 : W := mkw 0x0425663000000000 0x20109598c0000000 0x0e7fe6300000001d 0x2039ff98c0000000

def z193 : W := mkw 0xffffffbdfdd80000 0x73fffffef7f76000 0xfffffffffffc003f 0xfbfffffffffff000

def z194 : W := mkw 0xeb528001f9880000 0x43ad4a0007e62000 0xce738001e0000004 0x8339ce0007800000

def z195 : W := mkw 0x51fc2abea1a151b0 0x0147f0aafa868546 0xf1fc7fffe1e3f1ff 0xffc7f1ffff878fc7

def z196 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318c07fe1ffc0fd8 0x40c6301ff87ff03f

def z197 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xfffff801fffff03f 0xffffffe007ffffc0

def z198 : W := mkw 0xbe8ad5415e5aac00 0x42fa2b5505796ab0 0xfe0fffc1fe1ffe2f 0xfff83fff07f87ff8

def z199 : W := mkw 0x0635e633b1add7fa 0x2418d798cec6b75f 0x0e7fe631f1fffffd 0x2c39ff98c7c7ffff

def z200 : W := mkw 0xed677f3800000000 0x33b59dfce0000000 0xce7ffe300000001d 0xa339fff8c0000000

def z201 : W := mkw 0x4771ec29b188d4b2 0x251dc7b0a6c62352 0xce73f801e000f004 0x8339cfe0078003c0

def z202 : W := mkw 0x129c82d7977f0b4c 0x084a720b5e5dfc2d 0x3fff87ff9fff0fff 0x7cfffe1ffe7ffc3f

def z203 : W := mkw 0xfdcf579400000000 0x33f73d5e50000000 0xffff87c00000001f 0xc3fffe1f00000000

def z204 : W := mkw 0x1298800195580000 0x004a620006556000 0x3fff80019ffc003f 0x48fffe00067ff000

def z205 : W := mkw 0x0631e4219108c4a2 0x2418c79086442312 0x0e73e0318100c1f5 0x2439cf80c6040307

def z206 : W := mkw 0xae35f771db0eeeea 0x26b8d7ddc76c3bbb 0xfe7ffff1ff1fffff 0xfff9ffffc7fc7fff

def z207 : W := mkw 0x45756e3aa1a5d7fa 0x2515d5b8ea86975f 0xc1f07e3fe1e3fff7 0xbf07c1f8ff878fff

def z208 : W := mkw 0xf9ce02d66ef70b4c 0x4be7380b59bbdc2d 0xf18c07fe7fff0ffb 0xffc6301ff9fffc3f

def z209 : W := mkw 0xf9da0000a1800000 0x03e7680002860000 0xffff8001e1e0003f 0xcbfffe0007878000

def z210 : W := mkw 0x000000000004c6ea 0x040000000000131b 0x000000000000cfc0 0x040000000000033f

def z211 : W := mkw 0xed677fbc00000000 0x33b59dfef0000000 0xce73fffe00000004 0xb339cffff8000000

def z212 : W := mkw 0x0000000000000000 0x0000000000000000 0x000078000003f000 0x340001e000000fc0

def z213 : W := mkw 0x0000004006560a4c 0x0800000100195829 0x000000001e1c0e00 0x0000000000787038

def z214 : W := mkw 0x0000000200210100 0x0000000008008404 0xc180783fe1e3f1f7 0xbf0601e0ff878fc7

def z215 : W := mkw 0x02108001fddcc6ea 0x4408420007f7731b 0x00000001fffccfe0 0x0c00000007fff33f

def z216 : W := mkw 0xf9fa282aedf151b0 0x43e7e8a0abb7c546 0xf1f0783fefe3f1f7 0xffc7c1e0ffbf8fc7

def z217 : W := mkw 0xae0055015800a400 0x02b8015405600290 0xce007801e003f027 0xbf3801e007800fc0

def z218 : W := mkw 0x1088000004500000 0x0042200000114000 0x018c000001fc0010 0x000630000007f000

def z219 : W := mkw 0x57fdeeffb7ffdffe 0x2d5ff7bbfedfff7f 0xffffffffffffffff 0xffffffffffffffff

def z220 : W := mkw 0x0000114002022800 0x00000045000808a0 0x000019c000033000 0x1000006700000cc0

def z221 : W := mkw 0xae2577715a02ac00 0x22b895ddc5680ab0 0xfe7ffff1fe03fe3f 0xfff9ffffc7f80ff8

def z222 : W := mkw 0x51faa82aa5f951b0 0x4147eaa0aa97e546 0x01ff803e01fc01d0 0x0007fe00f807f007

def z223 : W := mkw 0xae35f731910cc6ea 0x26b8d7dcc644331b 0xfe7ffff1911ccfff 0xf7f9ffffc644733f

def z224 : W := mkw 0x41702828a1800000 0x0105c0a0a2860000 0xc1f0783fe1e00037 0xbb07c1e0ff878000

def z225 : W := mkw 0x10ac2afe06775bfc 0x0842b0abf819dd6f 0x318c7ffe1ffffffb 0x7cc631fff87fffff

def z226 : W := mkw 0x51ffaabc810c42ea 0x3547feaaf204310b 0x01ff803e011c01d0 0x0007fe00f8047007

def z227 : W := mkw 0x41702828a18050b0 0x0105c0a0a2860142 0xc1f07801e1e0f037 0x8b07c1e0078783c0

def z228 : W := mkw 0x0000000000040248 0x0000000000001009 0x00000000111c0fe0 0x040000000044703f

def z229 : W := mkw 0x1088000000000000 0x0042200000000000 0x318c00000000001b 0x40c6300000000000

def z230 : W := mkw 0x02108041db0eeeea 0x04084201076c3bbb 0x00000001ff1fffe0 0x0c00000007fc7fff

def z231 : W := mkw 0x043566308104c6ea 0x2410d598c204131b 0x007066318100cff5 0x2401c198c604033f

def z232 : W := mkw 0x0615c611910cc6ea 0x241857184644331b 0x0e0f8601911ccfe8 0x04383e180644733f

def z233 : W := mkw 0x00100002a1a151b0 0x000040000a868546 0xc0007801e1e3f1e7 0xbf0001e007878fc7

def z234 : W := mkw 0x0000004002020800 0x0000000100080820 0x300001c00e030002 0x58c0000700380c00

def z235 : W := mkw 0x0400440000008400 0x0010011000000210 0x000066000000ce00 0x2400019800000338

def z236 : W := mkw 0x41702828a18050b0 0x0105c0a0a2860142 0xc0707801e000f004 0x8301c1e0078003c0

def z237 : W := mkw 0x0000004002020800 0x0000000100080820 0xf0007fc1fe03fe2f 0xffc001ff07f80ff8

def z238 : W := mkw 0xeb500001f9800000 0x03ad400007e60000 0xfff00001ffe0003f 0xcbffc00007ff8000

def z239 : W := mkw 0x0230a021910840a0 0x0008c28086442102 0x0e7fe031911cc1fd 0x2439ff80c6447307

def z240 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0x01f0003fe1e3f1f0 0x0c07c000ff878fc7

def z241 : W := mkw 0xf9fa39aea1a151b0 0x13e7e8e6ba868546 0xf1f079ffe1e3f1f7 0xffc7c1e7ff878fc7

def z242 : W := mkw 0xf9ca00006cd00000 0x43e7280001b34000 0xf18c00007ffc003b 0xcbc6300001fff000

def z243 : W := mkw 0x000000020475034c 0x080000000811d40d 0x0000000001fc01c0 0x000000000007f007

def z244 : W := mkw 0x16bde6b5910cc6ea 0x245af79ad644331b 0x3fffe7ff911ccfff 0x74ffff9ffe44733f

def z245 : W := mkw 0x0425663000040248 0x20109598c0001009 0x0e7fe630111c0ffd 0x2439ff98c044703f

def z246 : W := mkw 0xf9ef3bbc00000000 0x33e7bceef0000000 0xf1ff99fe00000012 0xd3c7fe67f8000000

def z247 : W := mkw 0xba9a8001fdd80000 0x42ea6a0007f76000 0x3e0f8001fffc0028 0x48f83e0007fff000

def z248 : W := mkw 0xfbca80015c580000 0x43ef2a0005716000 0xffff80001e1c001f 0xc3fffe0000787000

def z249 : W := mkw 0xffffe631fdd80000 0x63ffff98c7f76000 0xffffe631fffc003f 0xebffff98c7fff000

def z250 : W := mkw 0x51de8296a5fd034c 0x49477a0a5a97f40d 0x01ff803e01fc01d0 0x0007fe00f807f007

def z251 : W := mkw 0x108800c406520804 0x0842200310194820 0x300001c00e000000 0x40c0000700380000

def z252 : W := mkw 0x4140080a20a11110 0x0105002028828444 0x0180000e00e00000 0x0006000038038000

def z253 : W := mkw 0x0010800081080000 0x0000420002042000 0x007f8000011c0010 0x0001fe0000047000

def z254 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xfe007fc1fe00fe0c 0xc3f801ff07f803f8

def z255 : W := mkw 0xef52d541fb8aac00 0x43bd4b5507ee2ab0 0xfe73ffc1fe03fe2f 0xfff9cfff07f80ff8

def z256 : W := mkw 0x042566f60227cfee 0x2c10959bd8089f3f 0x000067fe0003cfc0 0x3400019ff8000f3f

def z257 : W := mkw 0x4370a82bb1add7fa 0x050dc2a0aec6b75f 0xc1f0783ff1fffff7 0xbf07c1e0ffc7ffff

def z258 : W := mkw 0x060044415a02ac00 0x0018011105680ab0 0x0e006601fe03fe2d 0x2c38019807f80ff8

def z259 : W := mkw 0x0625e631100c864a 0x24189798c4403219 0x0e7fe630101c0e1d 0x2039ff98c0407038

def z260 : W := mkw 0x43508001b1880000 0x010d420006c62000 0xcfff8001f1fc003f 0x8b3ffe0007c7f000

def z261 : W := mkw 0x0030282aa1a151b0 0x0000c0a0aa868546 0x0000783fe1e3f1e0 0x3c0001e0ff878fc7

def z262 : W := mkw 0x02108001910cc6ea 0x040842000644331b 0x00000001911ccfe0 0x040000000644733f

def z263 : W := mkw 0x00342230810442e8 0x0000d088c204110b 0x007c6631911ccffd 0x2401f198c644733f

def z264 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0x01f0003e01e001d0 0x0007c000f8078007

def z265 : W := mkw 0x0631e4219108c4a2 0x2418c79086442312 0x0e73e6019000ce2d 0x2439cf9806400338

def z266 : W := mkw 0x020000415a02ac00 0x0008000105680ab0 0x300007c1fe03fe2b 0x7cc0001f07f80ff8

def z267 : W := mkw 0x108c02960475034c 0x0842300a5811d40d 0x018c003e01ff01f3 0x3c063000f807fc07

def z268 : W := mkw 0x4170286aa7f75bfc 0x0905c0a1aa9fdd6f 0xc1f0783ffffffff7 0xbf07c1e0ffffffff

def z269 : W := mkw 0xfbda8043ffff0b4c 0x4bef6a010ffffc2d 0xffff8001ffff0fff 0xcffffe0007fffc3f

def z270 : W := mkw 0x000402d602270b4c 0x0800100b58089c2d 0x300007fe1e030feb 0x7cc0001ff8780c3f

def z271 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc070783fe003f1c4 0xb701c1e0ff800fc7

def z272 : W := mkw 0x0631e4219108c4a2 0x2418c79086442312 0x0e7fe001911cc03d 0x0039ff8006447300

def z273 : W := mkw 0xeb528001fdd80000 0x43ad4a0007f76000 0xce738001fffc0024 0x8b39ce0007fff000

def z274 : W := mkw 0x4775e631b18cc6ea 0x251dd798c6c6331b 0xcfffe631f1fccfff 0xaf3fff98c7c7f33f

def z275 : W := mkw 0x040055400202ac00 0x0010015500080ab0 0xc0007fc1e003fe27 0xbf0001ff07800ff8

def z276 : W := mkw 0x0000198c00000000 0x1000006630000000 0x000019ce00000000 0x1000006738000000

def z277 : W := mkw 0xef77ff39910cc6ea 0x37bddffce644331b 0xce7ffe31911ccffd 0xa739fff8c644733f

def z278 : W := mkw 0x00252230000442ea 0x24009488c000110b 0x00000030000001c0 0x00000000c0000007

def z279 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e73e6318000cfc4 0x2439cf98c600033f

def z280 : W := mkw 0x129c82d7ffff0b4c 0x484a720b5ffffc2d 0x318c07ffffff0ffb 0x7cc6301ffffffc3f

def z281 : W := mkw 0x00058210000c024a 0x2400160840003009 0x000f8000001c0000 0x00003e0000007000

def z282 : W := mkw 0x4175aa3aa1ad53fa 0x2505d6a8ea86b54f 0xc1fff83fe1fff1f7 0xbf07ffe0ff87ffc7

def z283 : W := mkw 0xae0055015800a400 0x02b8015405600290 0x0e00000000000000 0x0038000000000000

def z284 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7f8630111c0fd8 0x0039fe18c044703f

def z285 : W := mkw 0x0020282a002151b0 0x000080a0a8008546 0x0000783e0003f1c0 0x340001e0f8000fc7

def z286 : W := mkw 0x108c02d406560a4c 0x0842300b50195829 0x300c07f01f1c0ff9 0x64c0301fc07c703f

def z287 : W := mkw 0xa800110000000000 0x02a0004400000000 0xf00019c000000002 0xd3c0006700000000

def z288 : W := mkw 0x02100043fba3fdb0 0x000840010fee8ff6 0x00000001ffe3ffe0 0x0c00000007ff8fff

def z289 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z290 : W := mkw 0x060055411202ac00 0x0018015504480ab0 0x0e007fc19003fe2d 0x343801ff06400ff8

def z291 : W := mkw 0x0605c611100c864a 0x2418171844403219 0x0e0f8630111c0ff9 0x24383e18c044703f

def z292 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0007801e000f004 0x830001e0078003c0

def z293 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7fe031811cc1d4 0x0039ff80c6047307

def z294 : W := mkw 0xbe8c57d55a02ac00 0x02fa315f55680ab0 0xff8c7ffffe03fe3f 0xfffe31fffff80ff8

def z295 : W := mkw 0xba8a80015c580000 0x42ea2a0005716000 0x3e0f80001e1c0008 0x40f83e0000787000

def z296 : W := mkw 0x0010000081000000 0x0000400002040000 0x0070000181000035 0x0001c00006040000

def z297 : W := mkw 0xfffffffdffdaac00 0x73fffffff7ff6ab0 0xfffffffffffffe3f 0xfffffffffffffff8

def z298 : W := mkw 0x00108000810c42ea 0x040042000204310b 0x00000000011c01c0 0x0000000000047007

def z299 : W := mkw 0xffca55417ed2ac00 0x43ff295505fb4ab0 0xff807fc1fee3fe2f 0xfffe01ff07fb8ff8

def z300 : W := mkw 0xfbfaa82bfdf951b0 0x43efeaa0aff7e546 0xffff803ffffc01ff 0xcbfffe00fffff007

def z301 : W := mkw 0x04257fbe002151b0 0x301095fef8008546 0x00007ffe0003f1c0 0x340001fff8000fc7

def z302 : W := mkw 0x51da8000a5d80000 0x41476a0002976000 0x31ff80001ffc003b 0x48c7fe00007ff000

def z303 : W := mkw 0xbe8f57d55a02ac00 0x32fa3d5f55680ab0 0x3e0f87c01e000e08 0x40f83e1f00780038

def z304 : W := mkw 0x45757fbea1a151b0 0x3115d5fefa868546 0xc1f07fffe1e3f1f7 0xbf07c1ffff878fc7

def z305 : W := mkw 0x0004021000000000 0x0000100840000000 0x000c063000000019 0x20003018c0000000

def z306 : W := mkw 0x0635e633912dc7ea 0x2418d798ce44b71f 0x0fffe63f91ffcfff 0x3c3fff98fe47ff3f

def z307 : W := mkw 0xbe8fd7955c580000 0x72fa3f5e55716000 0x3e0f87c01e1c0008 0x40f83e1f00787000

def z308 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xfe0079c1ee03f006 0xdbf801e707b80fc0

def z309 : W := mkw 0xbc8f57d406560a4c 0x3af23d5f50195829 0x3e0f87c01e1c0e08 0x40f83e1f00787038

def z310 : W := mkw 0x0000004202230900 0x0000000108088c24 0x318007fe1fe30ffb 0x7cc6001ff87f8c3f

def z311 : W := mkw 0x0600444112028c00 0x0018011104480a30 0x3e0067c19e03ce2f 0x7cf8019f06780f38

def z312 : W := mkw 0x0425663000000000 0x20109598c0000000 0x0000663000000000 0x20000198c0000000

def z313 : W := mkw 0x00302022a1a151b0 0x0000c0808a868546 0x00706031e1e3f1f5 0x2c01c180c7878fc7

def z314 : W := mkw 0xfbda8003fdf90100 0x43ef6a000ff7e404 0xffff803fffff01ff 0xfffffe00fffffc07

def z315 : W := mkw 0xa80011404a022800 0x02a00045012808a0 0xf00019c06e033002 0xdbc0006701b80cc0

def z316 : W := mkw 0xac0055404a022800 0x02b00155012808a0 0xfe007fc06e03300f 0xfbf801ff01b80cc0

def z317 : W := mkw 0x108a800004580000 0x40422a0000116000 0x000f8000001c0000 0x00003e0000007000

def z318 : W := mkw 0xaa00000158000000 0x02a8000005600000 0xfe007801fe03f02f 0xfff801e007f80fc0

def z319 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc1f0003fe1e001f7 0x8b07c000ff878007

def z320 : W := mkw 0xfbfeaaffffff5bfc 0x4beffaabfffffd6f 0xffffffffffffffff 0xffffffffffffffff

def z321 : W := mkw 0x108c029400000000 0x0042300a50000000 0x300c07c000000008 0x40c0301f00000000

def z322 : W := mkw 0x0020282a002151b0 0x000080a0a8008546 0x0180783e01e3f1f3 0x3c0601e0f8078fc7

def z323 : W := mkw 0xbe8c57d75e77af4c 0x0afa315f5d79debd 0x3f8c07fe1fff0ffb 0x7cfe301ff87ffc3f

def z324 : W := mkw 0x57ffeebd910cc6ea 0x355fffbaf644331b 0x0fffe63f911ccffd 0x243fff98fe44733f

def z325 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xfe001fc07e033e0a 0xdbf8007f01f80cf8

def z326 : W := mkw 0xaa0000415a020800 0x02a8000105680820 0xfe0007c1fe030e2f 0xfff8001f07f80c38

def z327 : W := mkw 0xfdeb7d2800000000 0x33f7adf4a0000000 0xfffff8000000001f 0xc3ffffe000000000

def z328 : W := mkw 0x000000c602230904 0x0800000318088c24 0x000001ce00030000 0x1000000738000c00

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000030023 0x3c00000000000c00

def z330 : W := mkw 0xba8a80015c580000 0x42ea2a0005716000 0xfe0f8001fe1c002f 0xcbf83e0007f87000

def z331 : W := mkw 0x0400440000000000 0x0010011000000000 0x0e0066000000000d 0x2038019800000000

def z332 : W := mkw 0x108c029400000000 0x0042300a50000000 0x018c003e00000010 0x00063000f8000000

def z333 : W := mkw 0xfdff7fbea1a151b0 0x33f7fdfefa868546 0xfffffffe01e001df 0xf3fffffff8078007

def z334 : W := mkw 0x108c02d406560a4c 0x0842300b50195829 0x318c07c01ffc0e3b 0x48c6301f007ff038

def z335 : W := mkw 0xfbffaabdfdd80000 0x73effeaaf7f76000 0xffff803ffffc003f 0xcbfffe00fffff000

def z336 : W := mkw 0x51ef2abc00000000 0x3147bcaaf0000000 0xc1fff83e00000017 0xb307ffe0f8000000

def z337 : W := mkw 0x1088000004500000 0x0042200000114000 0x318000000ee00002 0x48c60000003b8000

def z338 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0x3fff80001ffc0018 0x40fffe00007ff000

def z339 : W := mkw 0xbcaf77b400000000 0x32f2bdded0000000 0x3e7fe7f00000001d 0x60f9ff9fc0000000

def z340 : W := mkw 0x0200000110008400 0x0008000004400210 0x000000019000ce20 0x0400000006400338

def z341 : W := mkw 0x0000000000000000 0x0000000000000000 0x300007c00000000b 0x70c0001f00000000

def z342 : W := mkw 0x04217d2800000000 0x301085f4a0000000 0x0000780000000000 0x000001e000000000

def z343 : W := mkw 0xa800000000000000 0x02a0000000000000 0xfe0000000000000f 0xc3f8000000000000

def z344 : W := mkw 0x4160282a20a11110 0x010580a0a8828444 0xc1f0783e60e33017 0xbb07c1e0f9838cc0

def z345 : W := mkw 0x020000435e77af4c 0x080800010d79debd 0x00000001ffffffe0 0x0c00000007ffffff

def z346 : W := mkw 0xffffffbdf9880000 0x73fffffef7e62000 0xffffffffe000001f 0xf3ffffffff800000

def z347 : W := mkw 0xac00554002020800 0x02b0015500080820 0xfe007fc01e030e2f 0xfff801ff00780c38

def z348 : W := mkw 0x4160282800000000 0x010580a0a0000000 0xc1f0783fe003f037 0xbf07c1e0ff800fc0

def z349 : W := mkw 0xbe8ad5415e5aac00 0x42fa2b5505796ab0 0x3e0f87c01e1c0e08 0x40f83e1f00787038

def z350 : W := mkw 0xf9ce02d606770b4c 0x0be7380b5819dc2d 0xffff87fe1fff0fff 0xfffffe1ff87ffc3f

def z351 : W := mkw 0x4160282a20a151b0 0x010580a0a8828546 0xc180783e60e3f1c2 0xbf0601e0f9838fc7

def z352 : W := mkw 0x0405461000000000 0x2010151840000000 0x0e0f860000000008 0x00383e1800000000

def z353 : W := mkw 0x0004025206770b4c 0x080010094819dc2d 0x000c06301fff0ff9 0x2c003018c07ffc3f

def z354 : W := mkw 0x51ffaabca5d80000 0x7147feaaf2976000 0x01ff803e01fc0010 0x0007fe00f807f000

def z355 : W := mkw 0xfbda800191080000 0x03ef6a0006442000 0xffff8001911c003f 0xc3fffe0006447000

def z356 : W := mkw 0xfbde82d5ffde0a4c 0x4bef7a0b57ff7829 0xffff87c1fffc0e3f 0xcbfffe1f07fff038

def z357 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc1f0783fe1e0f1d4 0x8307c1e0ff8783c7

def z358 : W := mkw 0x042566300004c6ea 0x24109598c000131b 0x0e7fe6300000cfdd 0x2439ff98c000033f

def z359 : W := mkw 0x0210800191080000 0x0008420006442000 0x0e73800180000004 0x0039ce0006000000

def z360 : W := mkw 0xa80011404a022800 0x02a00045012808a0 0xf00079c1ee03f027 0xffc001e707b80fc0

def z361 : W := mkw 0xffffffffffff0b4c 0x7bfffffffffffc2d 0xffffffffffff0fff 0xfffffffffffffc3f

def z362 : W := mkw 0x4160282a00210100 0x010580a0a8008404 0xc1f0783e01e301f7 0xbf07c1e0f8078c07

def z363 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7fe601901cce0c 0x0039ff9806407338

def z364 : W := mkw 0xed637d2800000000 0x33b58df4a0000000 0xfe73ffc00000000f 0xf3f9cfff00000000

def z365 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0x3fff87fe00000018 0x40fffe1ff8000000

def z366 : W := mkw 0xfffafd6bfffbfdb0 0x43ffebf5afffeff6 0xffffffffffffffff 0xffffffffffffffff

def z367 : W := mkw 0xf9fa282aa1a151b0 0x03e7e8a0aa868546 0xfffff83fe1e3f1ff 0xffffffe0ff878fc7

def z368 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0x01f0603f81e0c1f5 0x2407c180fe078307

def z369 : W := mkw 0xaa0011415a02ac00 0x02a8004505680ab0 0xf00019c1fe03fe22 0xdfc0006707f80ff8

def z370 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x00006631911ccfe0 0x24000198c644733f

def z371 : W := mkw 0xbe8855c75e73ad04 0x0afa21571d79ceb4 0xff807fcffee3fe2f 0xfffe01ff3ffb8ff8

def z372 : W := mkw 0x4175aa3aa1ad53fa 0x2505d6a8ea86b54f 0x01ff803e01fc01d0 0x0007fe00f807f007

def z373 : W := mkw 0xae0055015800a400 0x02b8015405600290 0xce007801e000f004 0x833801e0078003c0

def z374 : W := mkw 0xef707d2bf9a1f5b0 0x03bdc1f4afe687d6 0xcff0783fe1e3f1f7 0xbf3fc1e0ff878fc7

def z375 : W := mkw 0xfdffffbca5d80000 0x73f7fffef2976000 0xfffffffe01fc001f 0xf3fffffff807f000

def z376 : W := mkw 0x1088004206770b4c 0x084220010819dc2d 0x318c00001fff0ffb 0x4cc63000007ffc3f

def z377 : W := mkw 0x168dc6d7167f8f4e 0x2c5a371b5c59fe3d 0x3f8f87fe1fff0ffb 0x7cfe3e1ff87ffc3f

def z378 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0x01f0003e01e301f3 0x3c07c000f8078c07

def z379 : W := mkw 0x0605c611100c864a 0x2418171844403219 0x0e0fe601901cce2d 0x24383f9806407338

def z380 : W := mkw 0x00100002a1a151b0 0x000040000a868546 0x0000000001e001c0 0x0000000000078007

def z381 : W := mkw 0xa80011404a022800 0x02a00045012808a0 0xf0001fc07e033e2b 0xffc0007f01f80cf8

def z382 : W := mkw 0xae0457d75a27af4c 0x0ab8115f5d689ebd 0xfe007ffffe03ffef 0xfff801fffff80fff

def z383 : W := mkw 0x51da8000a5d80000 0x41476a0002976000 0x01ff800001fc0010 0x0007fe000007f000

def z384 : W := mkw 0xe970396aeba379b0 0x03a5c0e5abae8de6 0xf1f079ffefe3f1f7 0xffc7c1e7ffbf8fc7

def z385 : W := mkw 0x51ef2abc00000000 0x3147bcaaf0000000 0x31ff87fe0000001b 0x70c7fe1ff8000000

def z386 : W := mkw 0x02108001fdd80000 0x4008420007f76000 0x0e7f8001fffc003d 0x0839fe0007fff000

def z387 : W := mkw 0x0610c401910cc6ea 0x041843100644331b 0x0e006601911ccfed 0x243801980644733f

def z388 : W := mkw 0x0000004206770b4c 0x080000010819dc2d 0x300007c01fff0feb 0x7cc0001f007ffc3f

def z389 : W := mkw 0xffdad501fdd80000 0x43ff6b5407f76000 0xffffffc1fffc003f 0xfbffffff07fff000

def z390 : W := mkw 0xef75ff7bfbaffffa 0x27bdd7fdefeebfff 0xffffffffffffffff 0xffffffffffffffff

def z391 : W := mkw 0xac0055404a02ac00 0x02b0015501280ab0 0xf0007fc06e03fe02 0xffc001ff01b80ff8

def z392 : W := mkw 0x4163282800000000 0x31058ca0a0000000 0x0073800000000000 0x0001ce0000000000

def z393 : W := mkw 0x0000004002020800 0x0000000100080820 0x000000001e030e20 0x0c00000000780c38

def z394 : W := mkw 0xeb528001f9880000 0x43ad4a0007e62000 0xfe738001fe00002f 0xcbf9ce0007f80000

def z395 : W := mkw 0xfdca550000000000 0x03f7295400000000 0xffffffc00000001f 0xf3ffffff00000000

def z396 : W := mkw 0xae00550110008400 0x02b8015404400210 0xfe007fc19000ce2f 0xf7f801ff06400338

def z397 : W := mkw 0xae35f731d90ce6ea 0x26b8d7dcc764339b 0xce7ffe31f11cfffd 0xa739fff8c7c473ff

def z398 : W := mkw 0xbebfe631dd5cc6ea 0x66faff98c775731b 0x3e7fe6319f1ccffd 0x64f9ff98c67c733f

def z399 : W := mkw 0xf9ca000000000000 0x03e7280000000000 0xf180000000000002 0xc3c6000000000000

def z400 : W := mkw 0xae10d541db0eeeea 0x06b84355076c3bbb 0xfe007fc1ff1fffef 0xfff801ff07fc7fff

def z401 : W := mkw 0xeb70282bf9a151b0 0x03adc0a0afe68546 0xfff0783fffe3f1ff 0xffffc1e0ffff8fc7

def z402 : W := mkw 0xfbfaa829fdd850b0 0x43efeaa0a7f76142 0xfffff801fffcf03f 0xcbffffe007fff3c0

def z403 : W := mkw 0xfbde8295fdd80000 0x43ef7a0a57f76000 0xffff87fffffc003f 0xfbfffe1ffffff000

def z404 : W := mkw 0xaa00000158000000 0x02a8000005600000 0x3e0000001e000008 0x40f8000000780000

def z405 : W := mkw 0x0000004002020800 0x0000000100080820 0x300007c01e000e08 0x40c0001f00780038

def z406 : W := mkw 0x040055000000a400 0x0010015400000290 0x000078000000f000 0x000001e0000003c0

def z407 : W := mkw 0x0635ee3b912dd7fa 0x2418d7b8ee44b75f 0x0e7ffe3f911ffffd 0x3439fff8fe447fff

def z408 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x018c07fe01ff0fd0 0x3406301ff807fc3f

def z409 : W := mkw 0xf9ca11406ed22800 0x43e7284501bb48a0 0xf18019c06ee33002 0xdbc6006701bb8cc0

def z410 : W := mkw 0x51da8000a5d80000 0x41476a0002976000 0xc1ff8001e1fc0037 0x8b07fe000787f000

def z411 : W := mkw 0xae207d6b5a23fdb0 0x02b881f5ad688ff6 0xfe007ffffe03ffef 0xfff801fffff80fff

def z412 : W := mkw 0x51fc2abea5f553fc 0x0947f0aafa97d54f 0xc1fc783fe1fff1f7 0xbf07f1e0ff87ffc7

def z413 : W := mkw 0x4775ee39910cc6ea 0x251dd7b8e644331b 0xcffffe3f911ccfff 0xb73ffff8fe44733f

def z414 : W := mkw 0x020000415a02ac00 0x0008000105680ab0 0xc0007801fe03fe27 0xbf0001e007f80ff8

def z415 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0x01f0783e01e3f1d0 0x3407c1e0f8078fc7

def z416 : W := mkw 0x00302022812141a0 0x0000c0808a048506 0x01f0603f81e3c1f7 0x3c07c180fe078f07

def z417 : W := mkw 0x1088000004500000 0x0042200000114000 0x300c00001e1c0008 0x40c0300000787000

def z418 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xce007fc1e003fe04 0xb73801ff07800ff8

def z419 : W := mkw 0x0025223000000000 0x20009488c0000000 0x007f803000000010 0x0001fe00c0000000

def z420 : W := mkw 0x00202828000050b0 0x000080a0a0000142 0x000078000000f000 0x000001e0000003c0

def z421 : W := mkw 0x41742afea3a75bfc 0x0905d0abfa8e9d6f 0xc1f07fffe1e3fff7 0xbf07c1ffff878fff

def z422 : W := mkw 0xf9ea282800000000 0x03e7a8a0a0000000 0xfffff83e0000001f 0xf3ffffe0f8000000

def z423 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xfe007fc01e000e0f 0xf3f801ff00780038

def z424 : W := mkw 0x108c02d602270b4c 0x0842300b58089c2d 0x318c07fe00030fdb 0x74c6301ff8000c3f

def z425 : W := mkw 0xfbda8041ffdaac00 0x43ef6a0107ff6ab0 0xffff8001fffffe3f 0xcffffe0007fffff8

def z426 : W := mkw 0xaa0000415a02ac00 0x02a8000105680ab0 0xfe000001fe03fe2f 0xcff8000007f80ff8

def z427 : W := mkw 0xfffbfd29fdd80000 0x73ffeff4a7f76000 0xfffff801fffc003f 0xcbffffe007fff000

def z428 : W := mkw 0x021080019108c4a2 0x0408420006442312 0x000000018000c000 0x0000000006000300

def z429 : W := mkw 0x040055400202ac00 0x0010015500080ab0 0x000007c000000e00 0x0000001f00000038

def z430 : W := mkw 0xae257ffd5a02ac00 0x32b895fff5680ab0 0xfe007ffffe03fe2f 0xfff801fffff80ff8

def z431 : W := mkw 0x41528000a1880000 0x41054a0002862000 0x0073800000000000 0x0001ce0000000000

def z432 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000001e0000027 0x8b00000007800000

def z433 : W := mkw 0x00302020810040a0 0x0000c08082040102 0x00700030010001d0 0x0001c000c0040007

def z434 : W := mkw 0x51cc0ade26f71b5c 0x0947302b789bdc6d 0xf18c1ffe7fff3ffb 0xffc6307ff9fffcff

def z435 : W := mkw 0xffffffbdfddcc6ea 0x77fffffef7f7731b 0xfffffffffffccfff 0xfffffffffffff33f

def z436 : W := mkw 0xf9ce029400000000 0x03e7380a50000000 0xffff87fe0000001f 0xf3fffe1ff8000000

def z437 : W := mkw 0xffdad541ffdaac00 0x43ff6b5507ff6ab0 0xffff87c1fffc0e3f 0xcbfffe1f07fff038

def z438 : W := mkw 0xbebff7b5910cc6ea 0x36faffded644331b 0x3e7fe7f1911ccffd 0x64f9ff9fc644733f

def z439 : W := mkw 0x0000000200210100 0x0000000008008404 0x0000000001e301e0 0x0c00000000078c07

def z440 : W := mkw 0xeb528001f9880000 0x43ad4a0007e62000 0xcff38001e1e00037 0x8b3fce0007878000

def z441 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e7f80000000001d 0x0039fe0000000000

def z442 : W := mkw 0xef77e631f98cc6ea 0x67bddf98c7e6331b 0xce7fe631f11ccffd 0xa739ff98c7c4733f

def z443 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000030010001f1 0x24000000c0040007

def z444 : W := mkw 0xfdff7fbc810040a0 0x33f7fdfef2040102 0xffffffff8100c1ff 0xf7fffffffe040307

def z445 : W := mkw 0x45756e3aa1a151b0 0x2115d5b8ea868546 0xcffffe3fe1e3f1ff 0xbf3ffff8ff878fc7

def z446 : W := mkw 0x4775ee39b18cd6fa 0x251dd7b8e6c6335b 0xce7ffe31f11cfffd 0xa739fff8c7c473ff

def z447 : W := mkw 0x51f828eea7f359b4 0x0947e0a3ba9fcd66 0xf1f079ffefe3f1f7 0xffc7c1e7ffbf8fc7

def z448 : W := mkw 0x042566300004c6ea 0x24109598c000131b 0x000c6630111ccff9 0x24003198c044733f

def z449 : W := mkw 0xaa108001fdd80000 0x42a8420007f76000 0xfe000001fffc002f 0xcbf8000007fff000

def z450 : W := mkw 0xa80011404a022800 0x02a00045012808a0 0x300001c00e000000 0x40c0000700380000

def z451 : W := mkw 0x0210800191080000 0x0008420006442000 0x00000001911c0020 0x0000000006447000

def z452 : W := mkw 0x4140080a20a11110 0x0105002028828444 0xc180183e61e331f3 0xbf060060f9878cc7

def z453 : W := mkw 0xbe8c57d55e56ae4c 0x0afa315f55795ab9 0xfe0c7fc1fe1ffe2f 0xfff831ff07f87ff8

def z454 : W := mkw 0x51ec2abc00000000 0x0147b0aaf0000000 0xf1fc7ffe0000001f 0xf3c7f1fff8000000

def z455 : W := mkw 0xb88811c64e732904 0x0ae220471939cca4 0xf18019ce6ee33002 0xdbc6006739bb8cc0

def z456 : W := mkw 0x0230a021910cc6ea 0x0408c2808644331b 0x00706031911ccff5 0x2401c180c644733f

def z457 : W := mkw 0xef637d695a02ac00 0x33bd8df5a5680ab0 0xfe73ffc1fe03fe2f 0xfff9cfff07f80ff8

def z458 : W := mkw 0x109c02d6a7f75bfc 0x0842700b5a9fdd6f 0x318c07fffffffffb 0x7cc6301fffffffff

def z459 : W := mkw 0x168dc6d5165e8e4e 0x2c5a371b54597a39 0x3e0f87c01e1c0e08 0x40f83e1f00787038

def z460 : W := mkw 0x000402d402060a4c 0x0800100b50081829 0x000007c000000e00 0x0000001f00000038

def z461 : W := mkw 0x41702828a18050b0 0x0105c0a0a2860142 0x0070000000000000 0x0001c00000000000

def z462 : W := mkw 0x16bde631955cc6ea 0x245af798c655731b 0x3fffe6319ffccfff 0x6cffff98c67ff33f

def z463 : W := mkw 0xfdef7ffc4a022800 0x33f7bdfff12808a0 0xfffffffe6e03301f 0xfbfffffff9b80cc0

def z464 : W := mkw 0x1088004006520800 0x0042200100194820 0x318c07c01fff0e3b 0x7cc6301f007ffc38

def z465 : W := mkw 0x4150080aa1a151b0 0x010540202a868546 0xc180180fe1e3f1e2 0x9f0600603f878fc7

def z466 : W := mkw 0xed707d2aa1a151b0 0x03b5c1f4aa868546 0xfff07fffe1e3f1ff 0xffffc1ffff878fc7

def z467 : W := mkw 0x0435e630810c42ea 0x2410d798c204310b 0x0e7fe630011c01dd 0x2039ff98c0047007

def z468 : W := mkw 0x00302020810040a0 0x0000c08082040102 0xc0707831e103f1f7 0xbf01c1e0c7840fc7

def z469 : W := mkw 0xfbca000158000000 0x03ef280005600000 0xffff8001fe00003f 0xcbfffe0007f80000

def z470 : W := mkw 0x4370286bfba3fdb0 0x010dc0a1afee8ff6 0xc1f0783fffe3fff7 0xbf07c1e0ffff8fff

def z471 : W := mkw 0xffef7fbd5800a400 0x33ffbdfef5600290 0xffffffffe000f01f 0xf3ffffffff8003c0

def z472 : W := mkw 0x0235a231910cc6ea 0x2408d688c644331b 0x007f8031911ccff0 0x0401fe00c644733f

def z473 : W := mkw 0x53da8001fdd80000 0x414f6a0007f76000 0x01ff8001fffc0030 0x0807fe0007fff000

def z474 : W := mkw 0xeb528001f9880000 0x43ad4a0007e62000 0xce7f8001f11c003d 0x8339fe0007c47000

def z475 : W := mkw 0xae10d541db0aac00 0x02b84355076c2ab0 0xfe7fffc1ff1ffe3f 0xfff9ffff07fc7ff8

def z476 : W := mkw 0x108c02d406560a4c 0x0842300b50195829 0x318c07fe1e1c0e1b 0x70c6301ff8787038

def z477 : W := mkw 0x4775ee3bb1add7fa 0x251dd7b8eec6b75f 0x0fffe63f91fccffd 0x243fff98fe47f33f

def z478 : W := mkw 0x43508001fdd80000 0x410d420007f76000 0xc1f00001fffc0037 0x8b07c00007fff000

def z479 : W := mkw 0xf9ca080a6cf11110 0x43e7282029b3c444 0xf180180e6ee33002 0xdbc6006039bb8cc0

def z480 : W := mkw 0x41702828a18050b0 0x0105c0a0a2860142 0xc1f0783fe000f017 0xb307c1e0ff8003c0

def z481 : W := mkw 0xbcaf7fbc00000000 0x32f2bdfef0000000 0x3e0ffffe00000008 0x70f83ffff8000000

def z482 : W := mkw 0x00000002002151b0 0x0000000008008546 0x000000000003f1c0 0x0400000000000fc7

def z483 : W := mkw 0xffef7fff5e77af4c 0x3bffbdfffd79debd 0xffffffffffffffff 0xffffffffffffffff

def z484 : W := mkw 0xac00550000000000 0x02b0015400000000 0xfe007fc1e003f02f 0xfff801ff07800fc0

def z485 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x018c003e1fff0ff0 0x0c063000f87ffc3f

def z486 : W := mkw 0xffffe6f7ffffcfee 0x6fffff9bdfffff3f 0xffffe7ffffffcfff 0xffffff9fffffff3f

def z487 : W := mkw 0x02108003fdf951b0 0x400842000ff7e546 0x00000001fffff1e0 0x0c00000007ffffc7

def z488 : W := mkw 0x51ef2afe06770b4c 0x3947bcabf819dc2d 0x31ff87fe1fff0ffb 0x7cc7fe1ff87ffc3f

def z489 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000780000000007 0xb30001e000000000

def z490 : W := mkw 0xaa02800158080000 0x42a80a0005602000 0x0e03800000000000 0x00380e0000000000

def z491 : W := mkw 0x0631e421910cc6ea 0x2418c7908644331b 0x0e73e001911ccfe4 0x0439cf800644733f

def z492 : W := mkw 0x4370a82bb1a951b0 0x010dc2a0aec6a546 0xcffff83ff1fff1ff 0xbf3fffe0ffc7ffc7

def z493 : W := mkw 0x41500000a1800000 0x0105400002860000 0xc1f07801e1e3f037 0xbf07c1e007878fc0

def z494 : W := mkw 0x148c57d60677af4c 0x0852315f5819debd 0x318c7ffe1ffffffb 0x7cc631fff87fffff

def z495 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc1f0783e01e001d7 0xb307c1e0f8078007

def z496 : W := mkw 0x51d80000a5d00000 0x0147600002974000 0xf1fc0001fffc003f 0xcbc7f00007fff000

def z497 : W := mkw 0x00100002a1a151b0 0x000040000a868546 0x0180003fe1e3f1f3 0x3c060000ff878fc7

def z498 : W := mkw 0x0625663110008400 0x20189598c4400210 0x0e7fe6319000ce3d 0x2439ff98c6400338

def z499 : W := mkw 0xaa00000158000000 0x02a8000005600000 0xce000001e0000004 0x8338000007800000

def z500 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xffffffffe003f03f 0xffffffffff800fc0

def z501 : W := mkw 0x0625e631100cc6ea 0x24189798c440331b 0x0e0fe630101ccfc8 0x24383f98c040733f

def z502 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000060010000e29 0x2400001800400038

def z503 : W := mkw 0x00302020810040a0 0x0000c08082040102 0x007060018000c004 0x0001c18006000300

def z504 : W := mkw 0x108c02940454024c 0x0842300a50115009 0x000c0000001c0000 0x0000300000007000

def z505 : W := mkw 0xed607d2800000000 0x03b581f4a0000000 0xfff07ffe0000001f 0xf3ffc1fff8000000

def z506 : W := mkw 0xf9ca198e20a11110 0x13e7286638828444 0xf18019ce60e33002 0xdbc6006739838cc0

def z507 : W := mkw 0x000000400202ac00 0x0000000100080ab0 0x000000000003fe00 0x0400000000000ff8

def z508 : W := mkw 0xe942000068800000 0x43a5080001a20000 0xc000000060000000 0x8300000001800000

def z509 : W := mkw 0x0000000000000000 0x0000000000000000 0x000060018000c025 0x2400018006000300

def z510 : W := mkw 0x0004021200250348 0x000010084800940d 0x018c063e11ff0ffb 0x3c063018f847fc3f

def z511 : W := mkw 0xfbda998dfdd80000 0x53ef6a6637f76000 0xffff99cffffc003f 0xdbfffe673ffff000

def z512 : W := mkw 0x063064219100c4a0 0x0018c19086440312 0x0e7066319100cffd 0x2439c198c644033f

def z513 : W := mkw 0x04257ffc0202ac00 0x301095fff0080ab0 0x00007ffe0003fe00 0x340001fff8000ff8

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c0000111c0039 0x0000300000447000

def z515 : W := mkw 0x0610c40191088400 0x0018431006442210 0x0e7fe601911cce3d 0x2439ff9806447338

def z516 : W := mkw 0x02108041ffdaac00 0x4008420107ff6ab0 0x00000001fffffe20 0x0c00000007fffff8

def z517 : W := mkw 0xfdef7fbe002151b0 0x33f7bdfef8008546 0xfffffffe0003f1df 0xf7fffffff8000fc7

def z518 : W := mkw 0xfdff7fbca1800000 0x33f7fdfef2860000 0xffffffffe1e0003f 0xfbffffffff878000

def z519 : W := mkw 0x0020282800000000 0x000080a0a0000000 0x0000783e00000000 0x300001e0f8000000

def z520 : W := mkw 0x1088008400000000 0x0042200210000000 0x318001ce00000002 0x50c6000738000000

def z521 : W := mkw 0x4140000000000000 0x0105000000000000 0xc1f0000000000017 0x8307c00000000000

def z522 : W := mkw 0x0004021000040248 0x0000100840001009 0x0000063000000fc0 0x24000018c000003f

def z523 : W := mkw 0x4140080820801010 0x0105002020820040 0xc000180060003000 0x83000060018000c0

def z524 : W := mkw 0xfffff771ffdeeeea 0x67ffffddc7ff7bbb 0xfffffff1ffffffff 0xffffffffc7ffffff

def z525 : W := mkw 0x0030282a812151b0 0x0000c0a0aa048546 0x0070783f8103f1f5 0x3401c1e0fe040fc7

def z526 : W := mkw 0x02108003b1add7fa 0x040842000ec6b75f 0x00000001f1ffffe0 0x0c00000007c7ffff

def z527 : W := mkw 0xac257fbc00000000 0x32b095fef0000000 0xfe007ffe0000000f 0xf3f801fff8000000

def z528 : W := mkw 0xfbfaa829fdd80000 0x43efeaa0a7f76000 0xfffff83ffffc003f 0xfbffffe0fffff000

def z529 : W := mkw 0x0004021000040248 0x0000100840001009 0x000c0030011c01d0 0x00003000c0047007

def z530 : W := mkw 0xfdef7ffc06560a4c 0x3bf7bdfff0195829 0xfffffffe1e1c0e1f 0xf3fffffff8787038

def z531 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc1f0780fe0e3f006 0x9b07c1e03f838fc0

def z532 : W := mkw 0xe942190800000000 0x13a5086420000000 0xc000180000000000 0x8300006000000000

def z533 : W := mkw 0x0601c40110088402 0x2418071004402210 0x0e03800000000000 0x00380e0000000000

def z534 : W := mkw 0xfbda80c7fffb0904 0x4bef6a031fffec24 0xffff81cfffff003f 0xdbfffe073ffffc00

def z535 : W := mkw 0xef73e421f988c4a2 0x67bdcf9087e62312 0xce73e001e000c004 0x8339cf8007800300

def z536 : W := mkw 0x0000000004500000 0x0000000000114000 0x000000001ffc0020 0x08000000007ff000

def z537 : W := mkw 0xfffbe421fdd8c4a2 0x67ffef9087f76312 0xffffe001fffcc03f 0xcbffff8007fff300

def z538 : W := mkw 0x00100000810040a0 0x0000400002040102 0x000000018100c1e0 0x0400000006040307

def z539 : W := mkw 0x14ad66f60677cfee 0x2c52b59bd819df3f 0x318c67fe1fffcffb 0x7cc6319ff87fff3f

def z540 : W := mkw 0x10bc22f687774bec 0x0842f08bda1ddd2f 0x31fc67ff9fffcfff 0x7cc7f19ffe7fff3f

def z541 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0x3e0067c19e00ce2d 0x64f8019f06780338

def z542 : W := mkw 0x040055400202ac00 0x0010015500080ab0 0x30007fc01e03fe2b 0x7cc001ff00780ff8

def z543 : W := mkw 0x060055415a02ac00 0x0018015505680ab0 0x00007fc1fe03fe20 0x3c0001ff07f80ff8

def z544 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xfff38001eee00006 0xcbffce0007bb8000

def z545 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318c01fe0fff01d2 0x58c63007f83ffc07

def z546 : W := mkw 0xfbffa231fddc42ea 0x67effe88c7f7710b 0xffff8031fffc01ff 0xcbfffe00c7fff007

def z547 : W := mkw 0xba8e82d75e7f0b4c 0x4aea3a0b5d79fc2d 0x3f8f87fe1fff0ffb 0x7cfe3e1ff87ffc3f

def z548 : W := mkw 0x062566311004c6ea 0x24189598c440131b 0x0e0066319000cfed 0x24380198c640033f

def z549 : W := mkw 0x51ca000000000000 0x0147280000000000 0x01ff800000000010 0x0007fe0000000000

def z550 : W := mkw 0xfdef7fbe0475034c 0x3bf7bdfef811d40d 0xfffffffe01fc01df 0xf3fffffff807f007

def z551 : W := mkw 0xae0055015800a400 0x02b8015405600290 0xfe007fc1e000f00f 0xf3f801ff078003c0

def z552 : W := mkw 0x51ec2afe06770b4c 0x0947b0abf819dc2d 0xf1fc7ffe1fff0fff 0xffc7f1fff87ffc3f

def z553 : W := mkw 0xfdcf5f9c00000000 0x33f73d7e70000000 0xff8f9fce0000000a 0xd3fe3e7f38000000

def z554 : W := mkw 0x020000415a02ac00 0x0008000105680ab0 0x000000001e000e00 0x0000000000780038

def z555 : W := mkw 0x1088008604710104 0x084220021811c404 0x0180000e00e00000 0x0006000038038000

def z556 : W := mkw 0x55ef7fbc00000000 0x3157bdfef0000000 0x01fffffe00000010 0x3007fffff8000000

def z557 : W := mkw 0x4140080800000000 0x0105002020000000 0xc180180e00000002 0x9306006038000000

def z558 : W := mkw 0x108c021004540248 0x0042300840115009 0x318c06301ffc0ffb 0x6cc63018c07ff03f

def z559 : W := mkw 0xef637d295800a400 0x33bd8df4a5600290 0xce73f801e000f004 0x8339cfe0078003c0

def z560 : W := mkw 0x108c029400040248 0x0042300a50001009 0x318c07fe111c0ffb 0x74c6301ff844703f

def z561 : W := mkw 0x04257ffe02270b4c 0x381095fff8089c2d 0x00007ffe00030fc0 0x340001fff8000c3f

def z562 : W := mkw 0xac00550000000000 0x02b0015400000000 0x3e0007c000000008 0x40f8001f00000000

def z563 : W := mkw 0xfdef7ffc0202ac00 0x33f7bdfff0080ab0 0xfffffffe0003fe1f 0xf7fffffff8000ff8

def z564 : W := mkw 0x040546100004864a 0x2410151840001219 0x0000060000000e00 0x0000001800000038

def z565 : W := mkw 0xef73fd299108c4a2 0x37bdcff4a6442312 0xce73f8018000c004 0x8339cfe006000300

def z566 : W := mkw 0x02108001f9880000 0x4008420007e62000 0x00000001e0000000 0x0000000007800000

def z567 : W := mkw 0xf9ca000004500000 0x03e7280000114000 0xffff80001ffc003f 0xcbfffe00007ff000

def z568 : W := mkw 0x020080015c580000 0x4008020005716000 0x000000001e1c0000 0x0000000000787000

def z569 : W := mkw 0x45657fbc00000000 0x311595fef0000000 0xc1f07ffe00000017 0xb307c1fff8000000

def z570 : W := mkw 0x168c46d716778f4c 0x085a311b5c59de3d 0x3f8c67ff9fffcfff 0x7cfe319ffe7fff3f

def z571 : W := mkw 0x16bde6f5975eceee 0x2c5af79bd65d7b3b 0x3e7fe7f19f1ccffd 0x64f9ff9fc67c733f

def z572 : W := mkw 0xae35f771db0eeeea 0x26b8d7ddc76c3bbb 0x3e7fe7f19f1ccffd 0x64f9ff9fc67c733f

def z573 : W := mkw 0x0235a231910c42ea 0x2408d688c644310b 0x0e7f8031911c01fd 0x0039fe00c6447007

def z574 : W := mkw 0xae31f561db0aeca2 0x26b8c7d5876c2bb2 0xfe73ffc1fe03fe2f 0xfff9cfff07f80ff8

def z575 : W := mkw 0xef405d4b7aa3bd10 0x03bd01752dea8ef4 0xff807fcffee3fe2f 0xfffe01ff3ffb8ff8

def z576 : W := mkw 0x14ad7ffe06770b4c 0x3852b5fff819dc2d 0x318c7ffe1fff0ffb 0x7cc631fff87ffc3f

def z577 : W := mkw 0x0000000200210100 0x0000000008008404 0x0180000e00e30002 0x1806000038038c00

def z578 : W := mkw 0xbc8f579400000000 0x32f23d5e50000000 0xfe0fffc00000000f 0xf3f83fff00000000

def z579 : W := mkw 0xae35e631d90cc6ea 0x26b8d798c764331b 0xfe7fe631ff1ccfff 0xeff9ff98c7fc733f

def z580 : W := mkw 0x0020202000000000 0x0000808080000000 0x0070603000000015 0x2001c180c0000000

def z581 : W := mkw 0x0200800110080000 0x0008020004402000 0x0e0f8000101c0008 0x00383e0000407000

def z582 : W := mkw 0xffca5dcd5a02ac00 0x13ff297735680ab0 0xff807fcffe03fe2f 0xfffe01ff3ff80ff8

def z583 : W := mkw 0x0635e6319108c4a2 0x2418d798c6442312 0x0e7fe6318000c01d 0x2039ff98c6000300

def z584 : W := mkw 0x108c02d402020800 0x0042300b50080820 0x318c07fe1e030e3b 0x7cc6301ff8780c38

def z585 : W := mkw 0xffef7fbd58000000 0x33ffbdfef5600000 0xfffffffffe00003f 0xfbfffffffff80000

def z586 : W := mkw 0x51de82d6a7ff0b4c 0x49477a0b5a9ffc2d 0x31ff87fe1fff0ffb 0x7cc7fe1ff87ffc3f

def z587 : W := mkw 0xffca55415a02ac00 0x03ff295505680ab0 0xffffffc1fe03fe3f 0xffffffff07f80ff8

def z588 : W := mkw 0x47706c2bb1a1d5b0 0x011dc1b0aec68756 0xcff07e3ff1e3ffff 0xbf3fc1f8ffc78fff

def z589 : W := mkw 0x0000000200210100 0x0000000008008404 0x0000003e000301c0 0x34000000f8000c07

def z590 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xfe7f8001fe1c000c 0xc3f9fe0007f87000

def z591 : W := mkw 0xed737d2aa1a151b0 0x33b5cdf4aa868546 0xcff3f83fe1e3f1f7 0xbf3fcfe0ff878fc7

def z592 : W := mkw 0x51dc02d6a7f70b4c 0x0947700b5a9fdc2d 0xf1fc07ffffff0fff 0xffc7f01ffffffc3f

def z593 : W := mkw 0x00108000a5d80000 0x4000420002976000 0x0000000001fc0000 0x000000000007f000

def z594 : W := mkw 0x0000004206730904 0x080000010819cc24 0x000000000ee30000 0x08000000003b8c00

def z595 : W := mkw 0x41500002a1a10100 0x010540000a868404 0xc1f0003fe1e301f7 0xbf07c000ff878c07

def z596 : W := mkw 0xeb72a82bf9a951b0 0x43adcaa0afe6a546 0xcff3f83fe1e3f1f7 0xbf3fcfe0ff878fc7

def z597 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xce007801fe03fe24 0x8f3801e007f80ff8

def z598 : W := mkw 0x108f029400000000 0x30423c0a50000000 0x000f800000000000 0x00003e0000000000

def z599 : W := mkw 0xae105543fba3fdb0 0x02b841550fee8ff6 0xfe007fc1ffe3ffef 0xfff801ff07ff8fff

def z600 : W := mkw 0x108c02960475034c 0x0842300a5811d40d 0x018c063e11fc0ff9 0x24063018f847f03f

def z601 : W := mkw 0x0635e63191080000 0x2018d798c6442000 0x0e7fe631911c003d 0x2039ff98c6447000

def z602 : W := mkw 0xfdef7fbe20a11110 0x33f7bdfef8828444 0xfffffffe60e3301f 0xfbfffffff9838cc0

def z603 : W := mkw 0x41500002a1a151b0 0x010540000a868546 0xc1f00001e1e3f1f7 0x8f07c00007878fc7

def z604 : W := mkw 0x0004021000040248 0x0000100840001009 0x000c0600101c0e08 0x0000301800407038

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180000001e00033 0x0806000000078000

def z606 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x300c07fe1e1f0fc8 0x74c0301ff8787c3f

def z607 : W := mkw 0x55ef6ebc00000000 0x3157bdbaf0000000 0x0fffe63e0000001d 0x203fff98f8000000

def z608 : W := mkw 0xba9a8001dd580000 0x42ea6a0007756000 0x3e7f80019f1c003d 0x40f9fe00067c7000

def z609 : W := mkw 0xffefffbd5c580000 0x73ffbffef5716000 0xfffffffe1e1c001f 0xf3fffffff8787000

def z610 : W := mkw 0xf9ca19cc4a022800 0x13e72867312808a0 0xf18019ce6e033002 0xdbc6006739b80cc0

def z611 : W := mkw 0xffefffbd100c864a 0x37ffbffef4403219 0xfffffffe101c0e1f 0xf3fffffff8407038

def z612 : W := mkw 0x0421642000000000 0x2010859080000000 0x0e73e00000000004 0x0039cf8000000000

def z613 : W := mkw 0xae307561db02eca0 0x02b8c1d5876c0bb2 0xfe707ff1ff03ffff 0xfff9c1ffc7fc0fff

def z614 : W := mkw 0x4140080a20a11110 0x0105002028828444 0xc180780fe0e3f027 0xbf0601e03f838fc0

def z615 : W := mkw 0x0604461110048648 0x0018111844401219 0x0e0c6631911ccffd 0x24383198c644733f

def z616 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0x3e0007c01e030e2b 0x7cf8001f00780c38

def z617 : W := mkw 0x4160282800000000 0x010580a0a0000000 0xc070780000000004 0x8301c1e000000000

def z618 : W := mkw 0xffef7ffd5a02ac00 0x33ffbdfff5680ab0 0xfffffffe1e000e1f 0xf3fffffff8780038

def z619 : W := mkw 0xf9ef2abc00000000 0x33e7bcaaf0000000 0xffff803e0000001f 0xc3fffe00f8000000

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000180060033002 0x9b00006001800cc0

def z621 : W := mkw 0x0200000110000000 0x0008000004400000 0x0e0000019000002d 0x0038000006400000

def z622 : W := mkw 0xbc8f579400000000 0x32f23d5e50000000 0x3f8f87fe0000001b 0x70fe3e1ff8000000

def z623 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xcfff8001e1fc0014 0x833ffe000787f000

def z624 : W := mkw 0xfdef7ffe02270b4c 0x3bf7bdfff8089c2d 0xfffffffe00030fdf 0xf7fffffff8000c3f

def z625 : W := mkw 0x45707d6aa3a3fdb0 0x0115c1f5aa8e8ff6 0xc1f07fffe1e3fff7 0xbf07c1ffff878fff

def z626 : W := mkw 0x0400550000000000 0x0010015400000000 0x00007fc000000000 0x300001ff00000000

def z627 : W := mkw 0x0035a230810c42ea 0x2400d688c204310b 0x007f8630111c0ff9 0x2401fe18c044703f

def z628 : W := mkw 0x4160282a002151b0 0x010580a0a8008546 0xc1f0783e0003f1d7 0xb707c1e0f8000fc7

def z629 : W := mkw 0x4150080aa1a11110 0x010540202a868444 0xc1f0180fe1e33037 0x9b07c0603f878cc0

def z630 : W := mkw 0xac03550000000000 0x32b00d5400000000 0x0e03800000000000 0x00380e0000000000

def z631 : W := mkw 0x14ad7fbc00000000 0x3052b5fef0000000 0x318c7ffe0000001b 0x70c631fff8000000

def z632 : W := mkw 0x0035a230810c42ea 0x2400d688c204310b 0x007fe031811cc1f5 0x2401ff80c6047307

def z633 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0x3e0007c1fe03fe28 0x4cf8001f07f80ff8

def z634 : W := mkw 0xbc8c57d606770b4c 0x0af2315f5819dc2d 0xff8c7ffe1fff0fff 0xfffe31fff87ffc3f

def z635 : W := mkw 0x41702828a18050b0 0x0105c0a0a2860142 0xc0707831e100f1f5 0xa701c1e0c78403c7

def z636 : W := mkw 0x00202020000040a0 0x0000808080000102 0x000060300000c1c0 0x24000180c0000307

def z637 : W := mkw 0xffffee3bfdfdd7fa 0x67ffffb8eff7f75f 0xfffffe3fffffffff 0xfffffff8ffffffff

def z638 : W := mkw 0x14ad66f606770b4c 0x2852b59bd819dc2d 0x3fffe7fe1fff0fff 0x7cffff9ff87ffc3f

def z639 : W := mkw 0xed637d2800000000 0x33b58df4a0000000 0xcff3f83e00000017 0xb33fcfe0f8000000

def z640 : W := mkw 0xef73fd29f9880000 0x73bdcff4a7e62000 0xce73f801e0000004 0x8339cfe007800000

def z641 : W := mkw 0xae00550158000000 0x02b8015405600000 0xfe007fc1fe00002f 0xfbf801ff07f80000

def z642 : W := mkw 0xfbca00017cd00000 0x43ef280005f34000 0xff800001fee0002f 0xcbfe000007fb8000

def z643 : W := mkw 0xef707d29f980f4b0 0x03bdc1f4a7e603d2 0xce707801e000f004 0x8339c1e0078003c0

def z644 : W := mkw 0xe940194a6aa33910 0x03a5006529aa8ce4 0xf18019ce6ee33002 0xdbc6006739bb8cc0

def z645 : W := mkw 0x04207d6a0223fdb0 0x001081f5a8088ff6 0x00007ffe0003ffc0 0x340001fff8000fff

def z646 : W := mkw 0xfbde8297fdfd034c 0x4bef7a0a5ff7f40d 0xffff803ffffc01ff 0xcbfffe00fffff007

def z647 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x300c07c01fff0fe8 0x4cc0301f007ffc3f

def z648 : W := mkw 0x0020282a002151b0 0x000080a0a8008546 0xc000783fe003f1e7 0xbf0001e0ff800fc7

def z649 : W := mkw 0xae10d541ffdaac00 0x42b8435507ff6ab0 0xfe007fc1fffffe2f 0xfff801ff07fffff8

def z650 : W := mkw 0xb88a00004c500000 0x42e2280001314000 0x300000000e000000 0x40c0000000380000

def z651 : W := mkw 0xae0055435a23ad00 0x02b801550d688eb4 0xff807fffffe3ffff 0xfffe01ffffff8fff

def z652 : W := mkw 0x0000000220a11110 0x0000000008828444 0x0000000060e33000 0x0800000001838cc0

def z653 : W := mkw 0xa800000048000000 0x02a0000001200000 0xf00000006e000002 0xcbc0000001b80000

def z654 : W := mkw 0x00252abc00000000 0x300094aaf0000000 0x0000003e00000000 0x00000000f8000000

def z655 : W := mkw 0xbe8fc6115c5c864a 0x66fa3f1845717219 0x3e0f86001e1c0e08 0x40f83e1800787038

def z656 : W := mkw 0xfffc7ffffff7fffc 0x0bfff1ffffffdfff 0xfffc7fffffffffff 0xfffff1ffffffffff

def z657 : W := mkw 0x108c02960475034c 0x0842300a5811d40d 0x318c07fe01fc01db 0x70c6301ff807f007

def z658 : W := mkw 0x10bda2b6857d43ee 0x2c42f68ada15f50f 0x01ff803e01fc01d0 0x0007fe00f807f007

def z659 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xf1807ffe00000002 0xf3c601fff8000000

def z660 : W := mkw 0x040457d60227af4c 0x0810115f58089ebd 0x00007ffe0003ffc0 0x340001fff8000fff

def z661 : W := mkw 0xfbfaa021fdd840a0 0x43efea8087f76102 0xffffe031fffcc1ff 0xefffff80c7fff307

def z662 : W := mkw 0x108800c606770b4c 0x084220031819dc2d 0x318001ce1fff0fe2 0x5cc60007387ffc3f

def z663 : W := mkw 0xfdff7fbca18050b0 0x33f7fdfef2860142 0xffffffffe000f01f 0xf3ffffffff8003c0

def z664 : W := mkw 0xfdef7ffe06730904 0x3bf7bdfff819cc24 0xfffffffe0ee3001f 0xfbfffffff83b8c00

def z665 : W := mkw 0x41702828810040a0 0x0105c0a0a2040102 0xc1f0783f8100c1f7 0xb707c1e0fe040307

def z666 : W := mkw 0x0004025002060a48 0x0000100940081829 0x300c07f01f1f0ffb 0x7cc0301fc07c7c3f

def z667 : W := mkw 0x00242afe02275bfc 0x080090abf8089d6f 0x00007ffe0003ffc0 0x340001fff8000fff

def z668 : W := mkw 0x042164200000c4a2 0x2410859080000312 0x000060000000c000 0x0000018000000300

def z669 : W := mkw 0xae05d7515a0eae4a 0x26b8175d45683ab9 0xfe0fffc1fe1ffe2f 0xfff83fff07f87ff8

def z670 : W := mkw 0xae31f521d908e4a2 0x26b8c7d487642392 0xce73f801e000f004 0x8339cfe0078003c0

def z671 : W := mkw 0x108c02d606730904 0x0842300b5819cc24 0x318c07fe0ee3001b 0x78c6301ff83b8c00

def z672 : W := mkw 0xfbda8001fddcc6ea 0x47ef6a0007f7731b 0xffff8001fffccfff 0xcffffe0007fff33f

def z673 : W := mkw 0xb88a118400000000 0x12e2284610000000 0x300001c000000000 0x40c0000700000000

def z674 : W := mkw 0xfdff7ffea7f75bfc 0x3bf7fdfffa9fdd6f 0xffffffffffffffff 0xffffffffffffffff

def z675 : W := mkw 0xffef7fbd10008400 0x33ffbdfef4400210 0xffffffff9000ce3f 0xf7fffffffe400338

def z676 : W := mkw 0x0635e671930eceea 0x2418d799c64c3b3b 0x3e7fe7f19f1fcfff 0x7cf9ff9fc67c7f3f

def z677 : W := mkw 0xfbda8003fdf951b0 0x43ef6a000ff7e546 0xffff8001fffff1ff 0xcffffe0007ffffc7

def z678 : W := mkw 0x0635f771930eeeea 0x2418d7ddc64c3bbb 0x0e7ffff1911ffffd 0x3439ffffc6447fff

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0x300000001e00002b 0x48c0000000780000

def z680 : W := mkw 0x0200000158000000 0x0008000005600000 0x00000001fe000020 0x0800000007f80000

def z681 : W := mkw 0xbe8fd795100c864a 0x36fa3f5e54403219 0x3e0f87c0101c0e08 0x40f83e1f00407038

def z682 : W := mkw 0xac00550000000000 0x02b0015400000000 0xce00780000000004 0x833801e000000000

def z683 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc0707801e1e3f1e4 0x8f01c1e007878fc7

def z684 : W := mkw 0x04356630810040a0 0x2010d598c2040102 0x0e7fe6318100c1fd 0x2439ff98c6040307

def z685 : W := mkw 0x108800c606730904 0x084220031819cc24 0x318001fe0fe301f3 0x7cc60007f83f8c07

def z686 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xf1800001fffc0022 0xcbc6000007fff000

def z687 : W := mkw 0xffdfc611fddc864a 0x67ff7f1847f77219 0xffff8601fffc0e3f 0xcbfffe1807fff038

def z688 : W := mkw 0x41742a3aa1a553f8 0x0105d0a8ea86954f 0xc1fc7e3ff1ffffff 0xbf07f1f8ffc7ffff

def z689 : W := mkw 0x0600440110008400 0x0018011004400210 0xce007e01f003fe2f 0xbf3801f807c00ff8

def z690 : W := mkw 0xfbda8041ffda0800 0x43ef6a0107ff6820 0xffff87c1ffff0e3f 0xfffffe1f07fffc38

def z691 : W := mkw 0x4370a82bfdf951b0 0x410dc2a0aff7e546 0xc1f0783ffffff1f7 0xbf07c1e0ffffffc7

def z692 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318007fe0ee30fc2 0x7cc6001ff83b8c3f

def z693 : W := mkw 0x04257fbc0004c6ea 0x341095fef000131b 0x00007ffe0000cfc0 0x340001fff800033f

def z694 : W := mkw 0xef707d69fb82fcb0 0x03bdc1f5a7ee0bf2 0xfe707fc1fe03fe2f 0xfff9c1ff07f80ff8

def z695 : W := mkw 0xbc8c579400000000 0x02f2315e50000000 0xff8c7ffe0000001f 0xf3fe31fff8000000

def z696 : W := mkw 0xbe8855415e52ac00 0x02fa215505794ab0 0xff8c7fc1fffffe3f 0xfffe31ff07fffff8

def z697 : W := mkw 0x00100000a1800000 0x0000400002860000 0x00000001e1e00020 0x0800000007878000

def z698 : W := mkw 0xbc8f57d606770b4c 0x3af23d5f5819dc2d 0x3f8f87fe1fff0ffb 0x7cfe3e1ff87ffc3f

def z699 : W := mkw 0x0635e673977fcfee 0x2c18d799ce5dff3f 0x0e7fe6319fffcffd 0x2c39ff98c67fff3f

def z700 : W := mkw 0xae0457515a06ae48 0x02b8115d45681ab9 0xfe0c7ff1ff1fffff 0xfff831ffc7fc7fff

def z701 : W := mkw 0xa800110048002000 0x02a0004401200080 0xc000180060003000 0x83000060018000c0

def z702 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfe7fffc00000000c 0xc3f9ffff00000000

def z703 : W := mkw 0x0000004002020800 0x0000000100080820 0x000007c000030e00 0x3400001f00000c38

def z704 : W := mkw 0x0635e6f7932fcfee 0x2c18d79bde4cbf3f 0x0e7fe7ff911fcffd 0x3439ff9ffe447f3f

def z705 : W := mkw 0xf9da0000edd00000 0x43e7680003b74000 0xf1f00001efe00037 0xcbc7c00007bf8000

def z706 : W := mkw 0x51f8282aa5f151b0 0x0147e0a0aa97c546 0xf1fc783ffffff1ff 0xffc7f1e0ffffffc7

def z707 : W := mkw 0xfdef7fbc6cd00000 0x73f7bdfef1b34000 0xfffffffe7ffc003f 0xfbfffffff9fff000

def z708 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7fe601911ccfec 0x0439ff980644733f

def z709 : W := mkw 0x02108043ffffaf4c 0x480842010ffffebd 0x00000001ffffffe0 0x0c00000007ffffff

def z710 : W := mkw 0x4170a82aa1a951b0 0x0105c2a0aa86a546 0xc1fff83fe1fff1f7 0xbf07ffe0ff87ffc7

def z711 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7fe631911fcfff 0x3c39ff98c6447f3f

def z712 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xff807ffffe03fe3f 0xfffe01fffff80ff8

def z713 : W := mkw 0x02108043df7fefee 0x0c0842010f7dffbf 0x00000001ffffffe0 0x0c00000007ffffff

def z714 : W := mkw 0x51fc2afca7d65afc 0x0947f0abf29f596b 0xf07c7fc1fe1cfe0c 0xc3c1f1ff07f873f8

def z715 : W := mkw 0xfbda8001fdd8a400 0x43ef6a0007f76290 0xffff8001fffcf03f 0xcbfffe0007fff3c0

def z716 : W := mkw 0xfdef7fbc20801010 0x33f7bdfef0820040 0xfffffffe6000301f 0xf3fffffff98000c0

def z717 : W := mkw 0x43508001fdd80000 0x410d420007f76000 0xcfff8001fffc003f 0x8b3ffe0007fff000

def z718 : W := mkw 0xfdef66306cd4c6ea 0x67f7bd98c1b3531b 0xf18066306ee0cfc2 0xefc60198c1bb833f

def z719 : W := mkw 0xbe8ed7d55e5eae4c 0x4afa3b5f55797ab9 0x3e0f87c01e1c0e08 0x40f83e1f00787038

def z720 : W := mkw 0x0635f7b5910cc6ea 0x3418d7ded644331b 0x0e7fe7f1911ccffd 0x2439ff9fc644733f

def z721 : W := mkw 0xbcaf77b400000000 0x32f2bdded0000000 0x3fffe7fe0000001f 0x70ffff9ff8000000

def z722 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfffffffe0000001c 0xc3fffffff8000000

def z723 : W := mkw 0x53ef2afd5a02ac00 0x314fbcabf5680ab0 0x01ff803ffe03fe30 0x0c07fe00fff80ff8

def z724 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc1f0783fe0e3f1c6 0xbf07c1e0ff838fc7

def z725 : W := mkw 0x0234a231910c42e8 0x0008d288c644310b 0x0e7fe631911ccffd 0x2439ff98c644733f

def z726 : W := mkw 0x4160282a00210100 0x010580a0a8008404 0xc1f0783fe1e3f1f7 0xbf07c1e0ff878fc7

def z727 : W := mkw 0xbc9f5796a1a151b0 0x32f27d5e5a868546 0x3e0f87c1e1e3f1e8 0x4cf83e1f07878fc7

def z728 : W := mkw 0xfbda998d910cc6ea 0x17ef6a663644331b 0xf18019cf911ccfe2 0xd7c600673e44733f

def z729 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xfe007ff1ff03ffff 0xfff801ffc7fc0fff

def z730 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xfe007fc1fe03fe0e 0xdbf801ff07f80ff8

def z731 : W := mkw 0xa80011404a022800 0x02a00045012808a0 0xf0007fc1fe03fe2f 0xffc001ff07f80ff8

def z732 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318c67ff9fffcfff 0x7cc6319ffe7fff3f

def z733 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0x3fff80019ffc003d 0x40fffe00067ff000

def z734 : W := mkw 0xfdef7fbc48000000 0x33f7bdfef1200000 0xfffffffe6e00001f 0xfbfffffff9b80000

def z735 : W := mkw 0xed637d6a06770b4c 0x3bb58df5a819dc2d 0xce73f8001fff0fe4 0x8f39cfe0007ffc3f

def z736 : W := mkw 0x16b9e4e7977bcda6 0x2c5ae7939e5def36 0x3ff3e1cf8ee3c006 0x58ffcf873e3b8f00

def z737 : W := mkw 0xf9ca00006cd00000 0x43e7280001b34000 0xffff80007ffc003f 0xcbfffe0001fff000

def z738 : W := mkw 0x0425667206770b4c 0x28109599c819dc2d 0x0e7fe6301fff0ffd 0x2c39ff98c07ffc3f

def z739 : W := mkw 0xfdef7fbc000050b0 0x33f7bdfef0000142 0xfffffffe0000f01f 0xf3fffffff80003c0

def z740 : W := mkw 0x0635f731910cc6ea 0x2418d7dcc644331b 0x0e7ffff1911ccffd 0x3439ffffc644733f

def z741 : W := mkw 0xfdef7fbc04500000 0x33f7bdfef0114000 0xfffffffe1e1c001f 0xf3fffffff8787000

def z742 : W := mkw 0x1088004206730900 0x004220010819cc24 0x318c07fe1fff0ffb 0x7cc6301ff87ffc3f

def z743 : W := mkw 0x108c029400000000 0x0042300a50000000 0x3fff87fe0000001f 0x70fffe1ff8000000

def z744 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xffffffffe000003f 0xfbffffffff800000

def z745 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xffff9ffe0000001a 0xd3fffe7ff8000000

def z746 : W := mkw 0x45657fbc00000000 0x311595fef0000000 0xcffffffe0000001f 0xb33ffffff8000000

def z747 : W := mkw 0xfdce579400000000 0x03f7395e50000000 0xfffffffe0000001f 0xf3fffffff8000000

def z748 : W := mkw 0xfdea7d2800000000 0x03f7a9f4a0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z749 : W := mkw 0xef707d6bfba3fdb0 0x03bdc1f5afee8ff6 0x3ff007fe1fe00fd8 0x40ffc01ff87f803f

def z750 : W := mkw 0x04257fbc00000000 0x301095fef0000000 0x0e73fffe00000004 0x3039cffff8000000

def z751 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffffe001fffcc03f 0xefffff8007fff300

def z752 : W := mkw 0x55dad540a7daac00 0x41576b55029f6ab0 0x01ffffc001fffe10 0x3407ffff0007fff8

def z753 : W := mkw 0x0625663110048648 0x20189598c4401219 0x0e7fe631911ccffd 0x2439ff98c644733f

def z754 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7fe631f11ffffd 0x2c39ff98c7c47fff

def z755 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffff8001fefc000e 0xcbfffe0007fbf000

def z756 : W := mkw 0xbe8c57975c75a74c 0x0afa315e5d71d69d 0xcf8c783fe1fcf1d4 0x833e31e0ff87f3c7

def z757 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffff8031fffc01ff 0xeffffe00c7fff007

def z758 : W := mkw 0x53da8001b5d80000 0x414f6a0006d76000 0x3fff80019ffc003f 0x48fffe00067ff000

def z759 : W := mkw 0x55ef6ebc00000000 0x3157bdbaf0000000 0x3fffe7fe0000001f 0x70ffff9ff8000000

def z760 : W := mkw 0x4745ce1b30ad975a 0x251d17386cc2b65d 0xcf8f9e0e70ff3e0a 0x9b3e3e7839c3fcf8

def z761 : W := mkw 0xfdef7fbc24d00000 0x73f7bdfef0934000 0xfffffffe00e0001f 0xf3fffffff8038000

def z762 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x3fff87fe1fff0fff 0x7cfffe1ff87ffc3f

def z763 : W := mkw 0xf9da8000a5d80000 0x43e76a0002976000 0xffff80001ffc003f 0xcbfffe00007ff000

def z764 : W := mkw 0x0625e631100c864a 0x24189798c4403219 0x0e7fe630111c0ffd 0x2439ff98c044703f

def z765 : W := mkw 0x108f02d606770b4c 0x38423c0b5819dc2d 0x318f87fe1fff0ffb 0x7cc63e1ff87ffc3f

def z766 : W := mkw 0xbaaaa82b5c7951b0 0x42eaaaa0ad71e546 0x3e0ff83e1e1ff1c8 0x74f83fe0f8787fc7

def z767 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xfe0c7fc1ff1ffe3f 0xfff831ff07fc7ff8

def z768 : W := mkw 0xfdef66b400000000 0x23f7bd9ad0000000 0xffffe7fe0000001f 0xf3ffff9ff8000000

def z769 : W := mkw 0x0630e4219108c4a0 0x0018c39086442312 0x0e7fe631911ccffd 0x2439ff98c644733f

def z770 : W := mkw 0x04257ffe02275bfc 0x381095fff8089d6f 0x00007ffe0003ffc0 0x340001fff8000fff

def z771 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7fe630111c0fdd 0x2039ff98c044703f

def z772 : W := mkw 0xba9a8001dd580000 0x42ea6a0007756000 0x3fff80019ffc003f 0x48fffe00067ff000

def z773 : W := mkw 0xf9ef3bbc00000000 0x33e7bceef0000000 0xffff99fe0000001f 0xd3fffe67f8000000

def z774 : W := mkw 0x108c029404540248 0x0042300a50115009 0x318c07fe1ffc0ffb 0x7cc6301ff87ff03f

def z775 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0x3ffffffe00000018 0x70fffffff8000000

def z776 : W := mkw 0x53d88001b5d80000 0x014f620006d76000 0xffff8001fffc003f 0xcbfffe0007fff000

def z777 : W := mkw 0xba988001dd580000 0x02ea620007756000 0xffff8001fffc003f 0xcbfffe0007fff000

def z778 : W := mkw 0x0004025202270b48 0x0000100948089c2d 0x318c07fe1fff0ffb 0x7cc6301ff87ffc3f

def z779 : W := mkw 0xeb5682d7fbaf0b4c 0x4bad5a0b5feebc2d 0xce7387ffe0030fc4 0xb739ce1fff800c3f

def z780 : W := mkw 0x0635e631f98cc6ea 0x6418d798c7e6331b 0x0e7fe631f11ccffd 0x2439ff98c7c4733f

def z781 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfffff9fe00000016 0xd3ffffe7f8000000

def z782 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffff80007ffc001a 0xcbfffe0001fff000

def z783 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xfffff801fffc003f 0xfbffffe007fff000

def z784 : W := mkw 0x0635ffbdfdd80000 0x7018d7fef7f76000 0x00007ffffffc0020 0x380001fffffff000

def z785 : W := mkw 0x02108043932fcfee 0x0c0842010e4cbf3f 0x00000001911fcfe0 0x0400000006447f3f

def z786 : W := mkw 0x042566f602270b4c 0x2810959bd8089c2d 0x000067fe00030fc0 0x3400019ff8000c3f

def z787 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xf1f07fffe1e3f1ff 0xffc7c1ffff878fc7

def z788 : W := mkw 0xfbda9101fdd80000 0x43ef6a4407f76000 0xffff99c1fffc003f 0xdbfffe6707fff000

def z789 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318007fe1fff0fe2 0x7cc6001ff87ffc3f

def z790 : W := mkw 0x0635ee39910cc6ea 0x2418d7b8e644331b 0x0e7ffe3f911ccffd 0x3439fff8fe44733f

def z791 : W := mkw 0x55ef7fbc00000000 0x3157bdfef0000000 0x0ffffffe0000001d 0x303ffffff8000000

def z792 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0xce7ffe31911ccfff 0xb739fff8c644733f

def z793 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffff8601fffc0e3f 0xeffffe1807fff038

def z794 : W := mkw 0xfdef7fbc68800000 0x73f7bdfef1a20000 0xfffffffe6000001f 0xf3fffffff9800000

def z795 : W := mkw 0xbe8f57d55e56ae4c 0x3afa3d5f55795ab9 0x3e0f87c01e1c0e08 0x40f83e1f00787038

def z796 : W := mkw 0x0631e421910cc6ea 0x2418c7908644331b 0x0e7fe001911ccffd 0x0439ff800644733f

def z797 : W := mkw 0xfdef7fbc04500000 0x33f7bdfef0114000 0xfffffffe01fc001f 0xf3fffffff807f000

def z798 : W := mkw 0xf9ea39ac00000000 0x13e7a8e6b0000000 0xfffff9fe0000001f 0xf3ffffe7f8000000

def z799 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7fe631911ccfdc 0x0039ff98c644733f

def z800 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0xf18c7ffe1fff0fff 0xffc631fff87ffc3f

def z801 : W := mkw 0xfdeb7dac00000000 0x33f7adf6b0000000 0xfff3ffce0000000f 0xf3ffcfff38000000

def z802 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0x3fff8001fffc0038 0x48fffe0007fff000

def z803 : W := mkw 0xfdef7fbc00040248 0x33f7bdfef0001009 0xfffffffe00000fdf 0xf7fffffff800003f

def z804 : W := mkw 0x04257ffe0227cfee 0x3c1095fff8089f3f 0x00007ffe0003cfc0 0x340001fff8000f3f

def z805 : W := mkw 0xfdef7fbc48002000 0x33f7bdfef1200080 0xfffffffe6000301f 0xf3fffffff98000c0

def z806 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffff8001fffc001c 0xc3fffe0007fff000

def z807 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfff3fffe00000006 0xf3ffcffff8000000

def z808 : W := mkw 0x020000415a02ac00 0x0008000105680ab0 0xf0007fc1fe03fe2f 0xffc001ff07f80ff8

def z809 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc1f0783fe1e3f1f4 0x8f07c1e0ff878fc7

def z810 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc1f0783fe1e3f1d6 0x9b07c1e0ff878fc7

def z811 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc1f0783fe1e3f1d4 0xb707c1e0ff878fc7

def z812 : W := mkw 0xfbca00015c500000 0x03ef280005714000 0xffff8001fffc003f 0xcbfffe0007fff000

def z813 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffff803ffffc003f 0xfbfffe00fffff000

def z814 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0xce7ffe31f11cfffd 0xa739fff8c7c473ff

def z815 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc1fc783ff1fff1ff 0xbf07f1e0ffc7ffc7

def z816 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0xf18c07ffffff0fff 0xffc6301ffffffc3f

def z817 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xffffffce0000000e 0xd3ffffff38000000

def z818 : W := mkw 0xfbda8001fdd8c4a2 0x47ef6a0007f76312 0xffff8001fffcc03f 0xcbfffe0007fff300

def z819 : W := mkw 0xfdef7fbc4c500000 0x73f7bdfef1314000 0xfffffffe0e00001f 0xf3fffffff8380000

def z820 : W := mkw 0xaa108001fdd80000 0x42a8420007f76000 0xfe7f8001fffc003f 0xcbf9fe0007fff000

def z821 : W := mkw 0xae02d5415a0aac00 0x42b80b5505682ab0 0xfe03ffc1fe03fe2f 0xfff80fff07f80ff8

def z822 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x3e7fe6319f1ccfff 0x6cf9ff98c67c733f

def z823 : W := mkw 0x0615c611910cc6ea 0x241857184644331b 0x0e7f8601911ccffd 0x0439fe180644733f

def z824 : W := mkw 0xfdef7fbc0004864a 0x37f7bdfef0001219 0xfffffffe00000e1f 0xf3fffffff8000038

def z825 : W := mkw 0x129c8295910cc6ea 0x044a720a5644331b 0x318c07ff911ccffb 0x74c6301ffe44733f

def z826 : W := mkw 0xf9ca11c66ef32904 0x4be7284719bbcca4 0xf18019ce6ee33002 0xdbc6006739bb8cc0

def z827 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xffff87fe0000001f 0xc3fffe1ff8000000

def z828 : W := mkw 0x04256efe0227dffe 0x2c1095bbf8089f7f 0x00007ffe0003ffc0 0x340001fff8000fff

def z829 : W := mkw 0xfdef7fbc00008400 0x33f7bdfef0000210 0xfffffffe0000ce1f 0xf7fffffff8000338

def z830 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318c07fe1fff0ff8 0x4cc6301ff87ffc3f

def z831 : W := mkw 0x0635ee39910cd6fa 0x2418d7b8e644335b 0x0e7ffe31911cfffd 0x2439fff8c64473ff

def z832 : W := mkw 0xf9ca19ce4e732904 0x1be728673939cca4 0xf18019ce6ee33002 0xdbc6006739bb8cc0

def z833 : W := mkw 0x042577f60227efee 0x2c1095dfd8089fbf 0x00007ffe0003ffc0 0x340001fff8000fff

def z834 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0fffe63f911ccfff 0x343fff98fe44733f

def z835 : W := mkw 0xfbda9909fdd80000 0x53ef6a6427f76000 0xffff9801fffc003f 0xcbfffe6007fff000

def z836 : W := mkw 0xfbda8809fdd80000 0x43ef6a2027f76000 0xffff980ffffc003f 0xdbfffe603ffff000

def z837 : W := mkw 0xa835b370cb0e6aea 0x26a0d6cdc32c39ab 0xf07f99f06f1f31d2 0xdbc1fe67c1bc7cc7

def z838 : W := mkw 0x02108043977f0b4c 0x080842010e5dfc2d 0x000000019fff0fe0 0x0c000000067ffc3f

def z839 : W := mkw 0xfdcf5f9c00000000 0x33f73d7e70000000 0xffff9fce0000001f 0xd3fffe7f38000000

def z840 : W := mkw 0xed677fbc00000000 0x33b59dfef0000000 0xcff3fffe00000017 0xb33fcffff8000000

def z841 : W := mkw 0x02108043fffb0904 0x480842010fffec24 0x00000001ffff0020 0x0800000007fffc00

def z842 : W := mkw 0x04257ffe0227af4c 0x381095fff8089ebd 0x00007ffe0003ffc0 0x340001fff8000fff

def z843 : W := mkw 0x4173282aa1a151b0 0x3105cca0aa868546 0xc1f3f83fe1e3f1f7 0xbf07cfe0ff878fc7

def z844 : W := mkw 0x042566300004c6ea 0x24109598c000131b 0x0e7fe630111ccffd 0x2439ff98c044733f

def z845 : W := mkw 0xed677fbc00000000 0x33b59dfef0000000 0xce7ffffe0000001d 0xb339fffff8000000

def z846 : W := mkw 0x51feaabea5fd53fc 0x4947faaafa97f54f 0x01ff803e01fc01d0 0x0007fe00f807f007

def z847 : W := mkw 0xfbda8001fdd850b0 0x43ef6a0007f76142 0xffff8001fffcf03f 0xcbfffe0007fff3c0

def z848 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfffffffe1e00003f 0xfbfffffff8780000

def z849 : W := mkw 0x0600444112028c00 0x0018011104480a30 0xfe007fc1fe03fe2f 0xfff801ff07f80ff8

def z850 : W := mkw 0xbcaf7fbc00000000 0x32f2bdfef0000000 0x3e7ffffe0000001d 0x70f9fffff8000000

def z851 : W := mkw 0x02108043fbaffffa 0x040842010feebfff 0x00000001ffffffe0 0x0c00000007ffffff

def z852 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0x3fffe7fe0000001d 0x60ffff9ff8000000

def z853 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xfe7fffc1fe03fe3f 0xfff9ffff07f80ff8

def z854 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffff9801ffff303f 0xdbfffe6007fffcc0

def z855 : W := mkw 0xfbca80015c580000 0x43ef2a0005716000 0xffff80001ffc003f 0xcbfffe00007ff000

def z856 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318c07fe1fff0fd8 0x74c6301ff87ffc3f

def z857 : W := mkw 0x4160282a20a151b0 0x010580a0a8828546 0xc180783fe0e3f1e7 0xbf0601e0ff838fc7

def z858 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc180783fe1e3f1e2 0xbf0601e0ff878fc7

def z859 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0x3fff80001ffc003b 0x48fffe00007ff000

def z860 : W := mkw 0x0235a231910c42ea 0x2408d688c644310b 0x0e7f8631911c0ffd 0x2439fe18c644703f

def z861 : W := mkw 0x129c8295fdd80000 0x404a720a57f76000 0x318c07fffffc003b 0x78c6301ffffff000

def z862 : W := mkw 0x0635e631d90cc6ea 0x2418d798c764331b 0x0e7fe631ff1ccffd 0x2c39ff98c7fc733f

def z863 : W := mkw 0x042566720227cfee 0x2c109599c8089f3f 0x000066300003cfc0 0x24000198c0000f3f

def z864 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffff80001ffc001f 0xc3fffe00007ff000

def z865 : W := mkw 0xac00554002020800 0x02b0015500080820 0xfe007fc1fe03fe2f 0xfff801ff07f80ff8

def z866 : W := mkw 0xf9da8000edd80000 0x43e76a0003b76000 0xffff80006ffc001f 0xcbfffe0001bff000

def z867 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfffffffe0003003f 0xfffffffff8000c00

def z868 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0x3fff87fe0000001b 0x70fffe1ff8000000

def z869 : W := mkw 0x55ed6ebc00000000 0x2157b5baf0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z870 : W := mkw 0x4140080a20a11110 0x0105002028828444 0xc180783fe1e3f1f7 0xbf0601e0ff878fc7

def z871 : W := mkw 0xef71fd29f988f4b2 0x27bdc7f4a7e623d2 0xce73f801e000f004 0x8339cfe0078003c0

def z872 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xfe007fc1fe03fe0c 0xf7f801ff07f80ff8

def z873 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318c07fe1fff0fda 0x58c6301ff87ffc3f

def z874 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318c07fe1ffc0fdb 0x70c6301ff87ff03f

def z875 : W := mkw 0x1088000004500000 0x0042200000114000 0x3fff80001ffc003f 0x48fffe00007ff000

def z876 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7fe630111ccfd8 0x2439ff98c044733f

def z877 : W := mkw 0x0615c611910c864a 0x2418571846443219 0x0e7f8631911c0ffd 0x2439fe18c644703f

def z878 : W := mkw 0x4172a82aa1a951b0 0x4105caa0aa86a546 0xc1f3f83fe1e3f1f7 0xbf07cfe0ff878fc7

def z879 : W := mkw 0x0435e630810c42ea 0x2410d798c204310b 0x0e7fe630111c0ffd 0x2439ff98c044703f

def z880 : W := mkw 0x0625e631100cc6ea 0x24189798c440331b 0x0e7fe630101ccfdd 0x2439ff98c040733f

def z881 : W := mkw 0xf9ce1b9c00000000 0x13e7386e70000000 0xffff9ffe0000001f 0xf3fffe7ff8000000

def z882 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7f8631911c0ffd 0x0039fe18c644703f

def z883 : W := mkw 0xed637dac00000000 0x33b58df6b0000000 0xce73f9ce00000004 0x9339cfe738000000

def z884 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7fe031911ccff4 0x0439ff80c644733f

def z885 : W := mkw 0x0004021000040248 0x0000100840001009 0x0e7f8630111c0ffd 0x2439fe18c044703f

def z886 : W := mkw 0xfdef7fbc04540248 0x33f7bdfef0115009 0xfffffffe1ffc0fff 0xfffffffff87ff03f

def z887 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xc1f07e3ff1e3ffff 0xbf07c1f8ffc78fff

def z888 : W := mkw 0xfdef7fbc0454024c 0x3bf7bdfef0115009 0xfffffffe001c001f 0xf3fffffff8007000

def z889 : W := mkw 0xfdef7fbc0000a400 0x33f7bdfef0000290 0xfffffffe0000f01f 0xf3fffffff80003c0

def z890 : W := mkw 0x00302022812141a0 0x0000c0808a048506 0xc1f0783fe1e3f1f7 0xbf07c1e0ff878fc7

def z891 : W := mkw 0xeb508001f9880000 0x03ad420007e62000 0xffff8001fffc003f 0xcbfffe0007fff000

def z892 : W := mkw 0x0635ffbd910cc6ea 0x3418d7fef644331b 0x00007fff911ccfe0 0x340001fffe44733f

def z893 : W := mkw 0xf9ca08ce6ef31914 0x4be7282339bbcc64 0xf18019ce6ee33002 0xdbc6006739bb8cc0

def z894 : W := mkw 0x0635e631b18cd6fa 0x2418d798c6c6335b 0x0e7fe631f11cfffd 0x2439ff98c7c473ff

def z895 : W := mkw 0x00100002a1a151b0 0x000040000a868546 0xc180783fe1e3f1f7 0xbf0601e0ff878fc7

def z896 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfffffffe6003301f 0xfbfffffff9800cc0

def z897 : W := mkw 0xfdef7fbc000442ea 0x37f7bdfef000110b 0xfffffffe000001df 0xf3fffffff8000007

def z898 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0fffe63191fccfff 0x2c3fff98c647f33f

def z899 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7fe631901ccfcc 0x2439ff98c640733f

def z900 : W := mkw 0x0614c611910c8648 0x0018531846443219 0x0e7fe631911ccffd 0x2439ff98c644733f

def z901 : W := mkw 0xbe8dd7d55e5eae4e 0x2efa375f55797ab9 0x3e0f87c01e1c0e08 0x40f83e1f00787038

def z902 : W := mkw 0xfdef7fbc000040a0 0x33f7bdfef0000102 0xfffffffe0000c1df 0xf7fffffff8000307

def z903 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xfe007fc1fe03fe2c 0xcff801ff07f80ff8

def z904 : W := mkw 0xae0355415a02ac00 0x32b80d5505680ab0 0xfe03ffc1fe03fe2f 0xfff80fff07f80ff8

def z905 : W := mkw 0xfdef7fbc00040248 0x33f7bdfef0001009 0xfffffffe011c01df 0xf3fffffff8047007

def z906 : W := mkw 0xef73fd29f988c4a2 0x77bdcff4a7e62312 0xce73f801e000c004 0x8339cfe007800300

def z907 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0xce7fe631f11ccfff 0xaf39ff98c7c4733f

def z908 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xcfff8001fffc0034 0x8b3ffe0007fff000

def z909 : W := mkw 0xfdeb7dac00000000 0x33f7adf6b0000000 0xfff3f9fe00000017 0xf3ffcfe7f8000000

def z910 : W := mkw 0xed657f3800000000 0x23b595fce0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z911 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318c7ffe1ffffffb 0x7cc631fff87fffff

def z912 : W := mkw 0x0635e631b18cc6ea 0x2418d798c6c6331b 0x0e7fe631f1fccffd 0x2c39ff98c7c7f33f

def z913 : W := mkw 0xfbca80017cd80000 0x43ef2a0005f36000 0xffff80007efc001f 0xcbfffe0001fbf000

def z914 : W := mkw 0xeb528001fdd80000 0x43ad4a0007f76000 0xce7f8001fffc003d 0x8b39fe0007fff000

def z915 : W := mkw 0xae00d5415a0aac00 0x02b8035505682ab0 0xfe0fffc1fe1ffe2f 0xfff83fff07f87ff8

def z916 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfffffffe01e0003f 0xfbfffffff8078000

def z917 : W := mkw 0xf9ca00c606730904 0x0be728031819cc24 0xf18001ce0ee30002 0xdbc60007383b8c00

def z918 : W := mkw 0xba9a8001fdd80000 0x42ea6a0007f76000 0x3e7f8001fffc003d 0x48f9fe0007fff000

def z919 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xcffff83fe1e3f1ff 0xbf3fffe0ff878fc7

def z920 : W := mkw 0xf9ca194a6ef33910 0x43e7286529bbcce4 0xf18019ce6ee33002 0xdbc6006739bb8cc0

def z921 : W := mkw 0xfdeb7dac00000000 0x33f7adf6b0000000 0xfffff9ce0000001f 0xd3ffffe738000000

def z922 : W := mkw 0xfdef7fbc0000c4a2 0x37f7bdfef0000312 0xfffffffe0000c01f 0xf3fffffff8000300

def z923 : W := mkw 0xf9ca00426ef30904 0x4be7280109bbcc24 0xf18000006ee30002 0xcbc6000001bb8c00

def z924 : W := mkw 0x0610c401910cc6ea 0x041843100644331b 0x0e7fe601911ccffd 0x2439ff980644733f

def z925 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xfe007fc1ee03fe06 0xfff801ff07b80ff8

def z926 : W := mkw 0x51ff2abea5f553fc 0x3947fcaafa97d54f 0x01ff803e01fc01d0 0x0007fe00f807f007

def z927 : W := mkw 0xac0055404a02ac00 0x02b0015501280ab0 0xf0007fc1ee03fe27 0xffc001ff07b80ff8

def z928 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xfffff801fffcf03f 0xcbffffe007fff3c0

def z929 : W := mkw 0xf9ca198c00000000 0x13e7286630000000 0xfff399ce00000006 0xd3ffce6738000000

def z930 : W := mkw 0x0635eebd910cc6ea 0x3418d7baf644331b 0x0e7fe63f911ccffd 0x2439ff98fe44733f

def z931 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318c07fffffffffb 0x7cc6301fffffffff

def z932 : W := mkw 0x41500002a1a10100 0x010540000a868404 0xc1f0783fe1e3f1f7 0xbf07c1e0ff878fc7

def z933 : W := mkw 0x0635e631910c0248 0x2018d798c6443009 0x0e7fe631911c0ffd 0x2439ff98c644703f

def z934 : W := mkw 0x53da8001fdd80000 0x414f6a0007f76000 0x0fff8001fffc003d 0x083ffe0007fff000

def z935 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfe7ffffe0000000c 0xf3f9fffff8000000

def z936 : W := mkw 0xed677fbc00000000 0x33b59dfef0000000 0xfe73fffe0000000f 0xf3f9cffff8000000

def z937 : W := mkw 0xf9ee2abc00000000 0x03e7b8aaf0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z938 : W := mkw 0x0435e630810cc6ea 0x2410d798c204331b 0x0e7fe630011ccfdd 0x2439ff98c004733f

def z939 : W := mkw 0xfdef7fbc00040248 0x33f7bdfef0001009 0xfffffffe101c0e1f 0xf3fffffff8407038

def z940 : W := mkw 0xfdcf579400000000 0x33f73d5e50000000 0xffff87fe0000001f 0xf3fffe1ff8000000

def z941 : W := mkw 0xf9ca19ce6ef30904 0x5be7286739bbcc24 0xf18019ce6ee30002 0xdbc6006739bb8c00

def z942 : W := mkw 0xaa0000415a020800 0x02a8000105680820 0xfe007fc1fe03fe2f 0xfff801ff07f80ff8

def z943 : W := mkw 0x02108043ffff5bfc 0x480842010ffffd6f 0x00000001ffffffe0 0x0c00000007ffffff

def z944 : W := mkw 0x02108043b7ffdffe 0x0c0842010edfff7f 0x00000001ffffffe0 0x0c00000007ffffff

def z945 : W := mkw 0xbcad77b400000000 0x22f2b5ded0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z946 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7ffe31911ffffd 0x3439fff8c6447fff

def z947 : W := mkw 0xfbda8085fdd80000 0x43ef6a0217f76000 0xffff81cffffc003f 0xdbfffe073ffff000

def z948 : W := mkw 0xfbda9185fdd80000 0x53ef6a4617f76000 0xffff81c1fffc003f 0xcbfffe0707fff000

def z949 : W := mkw 0xfdef7fbc0004c6ea 0x37f7bdfef000131b 0xfffffffe111ccfff 0xf7fffffff844733f

def z950 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7fe631811ccfd4 0x2439ff98c604733f

def z951 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xcffffffe00000014 0xb33ffffff8000000

def z952 : W := mkw 0x02108043fffbfdb0 0x400842010fffeff6 0x00000001ffffffe0 0x0c00000007ffffff

def z953 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfffffffe111c003f 0xf3fffffff8447000

def z954 : W := mkw 0xfbda8001fdd88400 0x43ef6a0007f76210 0xffff8001fffcce3f 0xcffffe0007fff338

def z955 : W := mkw 0xf9ca19ce26f31914 0x1be72867389bcc64 0xf18019ce6ee33002 0xdbc6006739bb8cc0

def z956 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7f8630111c0ff9 0x2439fe18c044703f

def z957 : W := mkw 0x0635ff39910cc6ea 0x3418d7fce644331b 0x0e7ffe31911ccffd 0x2439fff8c644733f

def z958 : W := mkw 0x0230a021910cc6ea 0x0408c2808644331b 0x0e7fe031911ccffd 0x2439ff80c644733f

def z959 : W := mkw 0xfdca5d8c00000000 0x13f7297630000000 0xffffffce0000001f 0xf3ffffff38000000

def z960 : W := mkw 0xfbda8001fdd840a0 0x43ef6a0007f76102 0xffff8001fffcc1ff 0xcffffe0007fff307

def z961 : W := mkw 0x4170282aa1a151b0 0x0105c0a0aa868546 0xf1f0783fffe3f1ff 0xffc7c1e0ffff8fc7

def z962 : W := mkw 0x04257f7a0227fffa 0x241095fde8089fff 0x00007ffe0003ffc0 0x340001fff8000fff

def z963 : W := mkw 0xf9ef2abc00000000 0x33e7bcaaf0000000 0xffff87fe0000001f 0xf3fffe1ff8000000

def z964 : W := mkw 0xf9ca004206770b4c 0x0be728010819dc2d 0xffff80001fff0fff 0xcffffe00007ffc3f

def z965 : W := mkw 0x0210800195580000 0x0008420006556000 0x0e7f80019ffc003d 0x0839fe00067ff000

def z966 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfffffffe010001ff 0xf7fffffff8040007

def z967 : W := mkw 0xfbda8809fdd81010 0x43ef6a2027f76040 0xffff9801fffc303f 0xcbfffe6007fff0c0

def z968 : W := mkw 0x4171a82aa1a951b2 0x2505c6a0aa86a546 0xc1f3f83fe1e3f1f7 0xbf07cfe0ff878fc7

def z969 : W := mkw 0xf9ca008400000000 0x03e7280210000000 0xffff81ce0000001f 0xd3fffe0738000000

def z970 : W := mkw 0x12988001fdd80000 0x404a620007f76000 0x3fff8001fffc003f 0x48fffe0007fff000

def z971 : W := mkw 0xfdef7fbc20800000 0x33f7bdfef0820000 0xfffffffe60e0001f 0xfbfffffff9838000

def z972 : W := mkw 0x040055400202ac00 0x0010015500080ab0 0xf0007fc1fe03fe2f 0xffc001ff07f80ff8

def z973 : W := mkw 0x0635e631d90ce6ea 0x2418d798c764339b 0x0e7fe631f11cfffd 0x2439ff98c7c473ff

def z974 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffff8001fffff03f 0xcffffe0007ffffc0

def z975 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfffffffe0003f01f 0xf7fffffff8000fc0

def z976 : W := mkw 0xfbda9101fdd82000 0x43ef6a4407f76080 0xffff9801fffc303f 0xcbfffe6007fff0c0

def z977 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffff87c1fffc003f 0xfbfffe1f07fff000

def z978 : W := mkw 0x042566b400000000 0x2010959ad0000000 0x0e7fe7fe0000001d 0x3039ff9ff8000000

def z979 : W := mkw 0x02108001910c0248 0x0008420006443009 0x0e7f8001911c0ffd 0x0439fe000644703f

def z980 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xffffffff8000c03f 0xf7fffffffe000300

def z981 : W := mkw 0x0635f731910ce6ea 0x2418d7dcc644339b 0x0e7ffe31911cfffd 0x2439fff8c64473ff

def z982 : W := mkw 0x02148211910cc6ea 0x040852084644331b 0x0e7f8631911ccffd 0x2439fe18c644733f

def z983 : W := mkw 0x02108043ffffcfee 0x4c0842010fffff3f 0x00000001ffffcfe0 0x0c00000007ffff3f

def z984 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xf0007fc1fe03fe22 0xffc001ff07f80ff8

def z985 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318c07fe1ffc0ff9 0x64c6301ff87ff03f

def z986 : W := mkw 0xac257fbc00000000 0x32b095fef0000000 0xfe7ffffe0000001f 0xf3f9fffff8000000

def z987 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffff8001ffff003f 0xfffffe0007fffc00

def z988 : W := mkw 0xae0055415a02ac00 0x02b8015505680ab0 0xff807fc1ffe3fe3f 0xfffe01ff07ff8ff8

def z989 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0xf18c1ffe7fff3ffb 0xffc6307ff9fffcff

def z990 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xfe7f8001fffc002c 0xcbf9fe0007fff000

def z991 : W := mkw 0xfbda800195580000 0x03ef6a0006556000 0xffff80019ffc003f 0xcbfffe00067ff000

def z992 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x3e7fe7f1911ccfff 0x74f9ff9fc644733f

def z993 : W := mkw 0x0635e631910cc6ea 0x2418d798c644331b 0x0e7f8631911ccff8 0x0439fe18c644733f

def z994 : W := mkw 0xae01d5415a0aac02 0x26b8075505682ab0 0xfe03ffc1fe03fe2f 0xfff80fff07f80ff8

def z995 : W := mkw 0x0020282a002151b0 0x000080a0a8008546 0xc180783fe1e3f1f7 0xbf0601e0ff878fc7

def z996 : W := mkw 0xfdef7fbc04500000 0x33f7bdfef0114000 0xfffffffe0ee0001f 0xfbfffffff83b8000

def z997 : W := mkw 0xfbda888dfdd80000 0x53ef6a2237f76000 0xffff800ffffc003f 0xcbfffe003ffff000

def z998 : W := mkw 0xfbda998dfdd80000 0x53ef6a6637f76000 0xf18019cffffc0022 0xdbc600673ffff000

def z999 : W := mkw 0x0635e6b5910cc6ea 0x2418d79ad644331b 0x0e7fe7ff911ccffd 0x3439ff9ffe44733f

def z1000 : W := mkw 0x108c02d606770b4c 0x0842300b5819dc2d 0x318c07fe1ffc0ffb 0x48c6301ff87ff03f

def z1001 : W := mkw 0xef72fd29f988f4b0 0x43bdcbf4a7e623d2 0xce73f801e000f004 0x8339cfe0078003c0

def z1002 : W := mkw 0xfbda8001fdd80000 0x43ef6a0007f76000 0xffff8001effc0016 0xcbfffe0007bff000

def z1003 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xfffffffe10000e3f 0xf7fffffff8400038

def z1004 : W := mkw 0x14ad7fbc00000000 0x3052b5fef0000000 0x3ffffffe0000001f 0x70fffffff8000000

def z1005 : W := mkw 0xfdef7fbc00000000 0x33f7bdfef0000000 0xffffffffe000f01f 0xf3ffffffff8003c0

def z1006 : W := mkw 0x0235a231910cc6ea 0x2408d688c644331b 0x0e7f8031911ccffd 0x0439fe00c644733f

def z1007 : W := mkw 0x04356630810442e8 0x2010d598c204110b 0x0e7fe631911ccffd 0x2439ff98c644733f

def z1008 : W := mkw 0xed637d2800000000 0x33b58df4a0000000 0xfff3fffe0000001f 0xf3ffcffff8000000

def z1009 : W := mkw 0x0000004206770b4c 0x080000010819dc2d 0x318007fe1fff0ffb 0x7cc6001ff87ffc3f

def z1010 : W := mkw 0x51fdaabea5fd53fe 0x2d47f6aafa97f54f 0x01ff803e01fc01d0 0x0007fe00f807f007

def z1011 : W := mkw 0xf9da0000a5d00000 0x03e7680002974000 0xffff8001fffc003f 0xcbfffe0007fff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z7,z5]),(0,[z0,z1,z2,z3,z4,z8,z5]),(0,[z0,z1,z2,z3,z9,z4,z5]),(0,[z0,z1,z2,z10,z3,z4,z5]),(1,[z0,z1,z2,z11,z5,z12])],[(0,[z0,z1,z2,z13,z3,z4,z5]),(0,[z0,z14,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z3,z4,z5]),(0,[z15,z0,z1,z2,z3,z4,z16]),(1,[z0,z1,z2,z17,z4,z5]),(0,[z0,z1,z2,z18,z3,z4,z5])],[(0,[z19,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z20,z4,z5]),(0,[z0,z21,z1,z2,z3,z4,z5])],[(0,[z22,z0,z1,z2,z3,z4,z5]),(0,[z0,z23,z1,z2,z3,z4,z5]),(0,[z24,z0,z1,z2,z25,z4,z5]),(0,[z0,z1,z26,z3,z4,z27,z5])],[(0,[z0,z1,z2,z3,z28,z4,z5]),(0,[z0,z1,z2,z29,z3,z4,z5]),(0,[z0,z30,z1,z2,z3,z4,z5])],[(1,[z31,z0,z32,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z33,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z34,z5]),(0,[z1,z2,z3,z35,z4,z5,z36]),(0,[z0,z1,z37,z3,z38,z4,z5]),(0,[z0,z1,z2,z3,z39,z4,z40])]],
   [[(0,[z24,z0,z41,z2,z3,z4,z5])],[(0,[z19,z0,z1,z2,z3,z4,z42]),(0,[z43,z0,z1,z2,z3,z4,z5])],[(0,[z44,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z27,z5,z12]),(0,[z0,z1,z2,z3,z4,z5,z45]),(0,[z0,z1,z2,z46,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z47]),(0,[z0,z1,z2,z48,z3,z4,z5]),(0,[z49,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z50]),(1,[z0,z1,z3,z51,z4,z5]),(0,[z0,z1,z2,z52,z3,z4,z5])],[(0,[z53,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z54,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z55]),(0,[z56,z0,z1,z2,z3,z39,z4])],[(0,[z57,z58,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z59,z4,z5]),(0,[z0,z60,z1,z2,z3,z4,z5])]],
   [[(0,[z19,z0,z61,z2,z3,z4,z5]),(1,[z62,z0,z1,z2,z3,z4]),(0,[z0,z1,z63,z2,z3,z4,z5]),(0,[z64,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z65,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z66])],[(0,[z0,z1,z2,z3,z51,z4,z5]),(1,[z0,z1,z67,z3,z4,z68])],[(0,[z0,z1,z2,z69,z3,z4,z5]),(0,[z70,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z71,z4,z5]),(0,[z0,z72,z1,z2,z3,z4,z5])],[(0,[z0,z1,z1,z2,z3,z4,z5]),(1,[z73,z1,z74,z3,z4,z5]),(0,[z0,z1,z75,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z76])],[(1,[z0,z1,z77,z2,z3,z4]),(0,[z78,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z79,z5]),(0,[z80,z0,z1,z2,z3,z4,z5])],[(0,[z23,z1,z2,z3,z81,z4,z5]),(0,[z82,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z83]),(0,[z0,z84,z2,z3,z4,z85,z5]),(0,[z0,z1,z2,z86,z3,z39,z4]),(0,[z0,z1,z2,z3,z4,z5,z40]),(0,[z0,z1,z2,z3,z87,z4,z5])],[(0,[z0,z1,z2,z3,z4,z88,z5]),(0,[z89,z90,z0,z1,z2,z3,z5])],[(0,[z0,z1,z91,z2,z3,z4,z5]),(0,[z92,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z93,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z94])],[(0,[z0,z95,z1,z2,z3,z4,z5]),(1,[z24,z0,z2,z25,z4,z5]),(0,[z0,z1,z2,z3,z96,z4,z5]),(0,[z97,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z98,z3,z4,z5]),(0,[z0,z1,z2,z99,z3,z4,z5]),(0,[z100,z0,z1,z2,z3,z4,z5])],[(0,[z22,z23,z1,z2,z3,z4,z5]),(0,[z101,z0,z1,z2,z3,z4,z5]),(0,[z90,z0,z1,z2,z3,z4,z5])],[(0,[z102,z103,z1,z2,z3,z4,z5]),(0,[z104,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z105,z4,z5])],[(0,[z106,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z107,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z108,z4,z5]),(0,[z109,z0,z1,z2,z3,z4,z5]),(0,[z0,z110,z1,z2,z3,z4,z5]),(0,[z0,z1,z67,z2,z3,z4,z5])],[(0,[z0,z111,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z112,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z113,z5]),(0,[z19,z114,z1,z2,z3,z4,z5]),(0,[z0,z1,z61,z2,z3,z4,z5]),(0,[z114,z23,z1,z2,z3,z4,z5]),(0,[z31,z0,z1,z37,z3,z4,z5]),(0,[z0,z1,z115,z2,z3,z4,z5]),(0,[z0,z1,z2,z37,z3,z4,z5]),(0,[z0,z1,z2,z116,z3,z4,z5]),(0,[z0,z1,z2,z117,z3,z4,z5]),(0,[z118,z0,z1,z2,z119,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z120]),(0,[z15,z1,z2,z3,z81,z4,z5]),(0,[z0,z121,z1,z2,z3,z122,z4]),(0,[z90,z0,z1,z2,z3,z4,z123]),(0,[z0,z1,z2,z124,z3,z4,z5]),(1,[z56,z0,z1,z3,z39,z4])],[(0,[z125,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z126,z3,z4,z5]),(0,[z0,z1,z2,z3,z127,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z128])],[(0,[z0,z129,z1,z2,z3,z4,z5]),(0,[z130,z0,z131,z1,z3,z4,z5]),(0,[z132,z0,z1,z2,z3,z4,z5]),(0,[z0,z133,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z134,z4,z5]),(0,[z0,z135,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z136,z3,z4,z5]),(0,[z0,z1,z2,z3,z137,z4,z5]),(0,[z15,z0,z1,z2,z3,z138,z4])],[(0,[z0,z1,z2,z3,z139,z4,z5]),(0,[z0,z1,z2,z140,z3,z4,z5]),(0,[z0,z1,z141,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z142]),(0,[z143,z0,z1,z2,z3,z4,z5]),(0,[z118,z0,z1,z2,z3,z4,z40])],[(0,[z0,z1,z2,z3,z4,z5,z144]),(0,[z0,z1,z2,z3,z4,z5,z145]),(0,[z0,z1,z2,z3,z146,z4,z5]),(0,[z0,z1,z2,z3,z147,z4,z5]),(0,[z0,z1,z2,z148,z3,z4,z5]),(0,[z0,z1,z2,z3,z149,z4,z5])]],
   [[(0,[z114,z1,z2,z3,z4,z5,z50]),(0,[z150,z90,z1,z2,z3,z4,z5])],[(0,[z151,z0,z1,z2,z3,z4,z5]),(0,[z152,z0,z1,z2,z3,z4,z5]),(0,[z0,z84,z1,z2,z3,z4,z76]),(0,[z0,z1,z153,z2,z3,z4,z5]),(0,[z0,z1,z2,z119,z3,z4,z5])],[(0,[z154,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z155,z3,z4,z5])],[(0,[z0,z1,z2,z156,z3,z4,z5]),(0,[z0,z1,z2,z3,z157,z4,z5]),(0,[z0,z1,z2,z3,z158,z4,z5])],[(0,[z0,z1,z2,z159,z3,z4,z5]),(0,[z160,z0,z1,z2,z3,z4,z5]),(0,[z130,z0,z161,z2,z3,z4,z5]),(0,[z0,z1,z2,z162,z3,z4,z5])],[(0,[z0,z1,z163,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z164])],[(0,[z0,z1,z165,z2,z3,z4,z5]),(0,[z166,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z167])],[(0,[z168,z0,z1,z2,z3,z4,z5]),(0,[z169,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z170,z4,z5]),(1,[z1,z2,z3,z171,z4,z5]),(0,[z0,z1,z172,z2,z3,z4,z5])]],
   [[(0,[z0,z173,z1,z2,z3,z4,z5]),(0,[z174,z0,z1,z2,z3,z4,z5])],[(0,[z175,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z176]),(0,[z0,z1,z2,z3,z177,z4,z5]),(0,[z0,z1,z2,z11,z4,z5,z12])],[(0,[z178,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z179]),(0,[z0,z1,z180,z2,z3,z4,z5]),(0,[z1,z2,z3,z181,z4,z5,z123]),(0,[z182,z0,z1,z2,z3,z4,z5]),(0,[z183,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z184,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z16]),(0,[z0,z2,z3,z147,z4,z5,z123]),(0,[z0,z1,z2,z3,z185,z4,z5]),(0,[z0,z1,z3,z39,z4,z5,z68]),(0,[z0,z1,z2,z3,z186,z4,z5])],[(0,[z0,z1,z2,z187,z3,z4,z5]),(0,[z188,z0,z1,z2,z3,z81,z4]),(0,[z0,z1,z2,z3,z4,z5,z189]),(0,[z0,z1,z2,z190,z3,z4,z5])],[(0,[z0,z1,z2,z3,z191,z4,z5]),(0,[z192,z0,z1,z2,z3,z4,z193]),(0,[z0,z2,z3,z194,z4,z85,z5]),(0,[z0,z1,z2,z195,z3,z4,z5])],[(0,[z0,z196,z1,z2,z3,z4,z5]),(0,[z130,z0,z1,z2,z3,z197,z5]),(0,[z0,z1,z2,z3,z198,z4,z5]),(0,[z0,z199,z1,z2,z3,z4,z5]),(0,[z58,z0,z1,z2,z3,z122,z5])],[(0,[z0,z1,z2,z3,z200,z4,z5]),(0,[z0,z1,z2,z201,z3,z4,z5]),(0,[z0,z1,z202,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z203,z5])]],
   [[(0,[z0,z1,z204,z2,z3,z4,z5]),(0,[z205,z0,z1,z2,z3,z4,z5])],[(0,[z103,z0,z1,z2,z206,z4,z5]),(0,[z0,z1,z2,z207,z3,z4,z5]),(0,[z0,z1,z2,z3,z208,z4,z5]),(0,[z0,z1,z2,z3,z209,z4,z5])],[(0,[z210,z0,z1,z2,z3,z4,z5]),(0,[z0,z84,z1,z2,z3,z211,z4]),(0,[z212,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z2,z3,z4,z5]),(0,[z31,z0,z1,z2,z3,z4,z5]),(0,[z213,z0,z1,z2,z3,z4,z5]),(0,[z214,z0,z1,z2,z3,z4,z5]),(1,[z0,z161,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z42]),(0,[z215,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z216,z4,z5]),(0,[z0,z1,z2,z217,z3,z4,z5]),(0,[z0,z1,z2,z119,z4,z5,z40])],[(0,[z130,z31,z0,z1,z3,z4,z5]),(0,[z0,z218,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z219,z3,z4,z5]),(0,[z151,z1,z2,z3,z206,z4,z5]),(0,[z220,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z221,z4,z5]),(0,[z0,z1,z2,z222,z3,z4,z5]),(0,[z0,z1,z2,z3,z223,z4,z5]),(0,[z0,z1,z224,z2,z3,z4,z5])],[(0,[z0,z1,z225,z2,z3,z4,z5]),(0,[z56,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z226,z3,z4,z5]),(0,[z0,z1,z227,z2,z3,z4,z5]),(0,[z118,z0,z1,z2,z3,z4,z5])],[(0,[z228,z0,z1,z2,z3,z4,z5]),(0,[z15,z0,z1,z2,z3,z4,z5]),(0,[z0,z229,z1,z2,z3,z4,z5]),(0,[z0,z121,z2,z3,z4,z5,z123])],[(0,[z230,z0,z1,z2,z3,z4,z5]),(0,[z231,z0,z1,z2,z3,z4,z5]),(0,[z232,z0,z1,z2,z3,z4,z5])],[(0,[z233,z0,z1,z2,z3,z4,z5])],[],[(0,[z234,z0,z1,z2,z3,z4,z5]),(0,[z235,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z197,z5])],[(0,[z31,z0,z1,z236,z3,z4,z5]),(1,[z237,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z238,z4,z5]),(0,[z239,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z240,z2,z3,z4,z5]),(0,[z0,z1,z2,z86,z3,z4,z5])],[(1,[z101,z1,z2,z3,z4,z5])]],
   [[(0,[z102,z0,z1,z2,z206,z4,z5]),(0,[z0,z1,z2,z3,z241,z4,z5])],[(0,[z0,z1,z2,z3,z242,z4,z5]),(0,[z243,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z244,z2,z3,z4,z5]),(0,[z245,z1,z2,z3,z4,z5,z123])],[(0,[z0,z1,z2,z3,z246,z4,z5]),(0,[z0,z1,z2,z3,z247,z4,z5]),(0,[z0,z1,z2,z3,z248,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z249]),(0,[z0,z1,z2,z250,z3,z4,z5])],[(0,[z0,z251,z1,z2,z3,z4,z5]),(0,[z151,z1,z63,z2,z3,z4,z5]),(0,[z0,z1,z252,z2,z3,z4,z5]),(0,[z253,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z254,z3,z4,z5]),(0,[z0,z1,z2,z3,z122,z4,z5])],[(0,[z31,z0,z1,z32,z3,z4,z5]),(0,[z0,z1,z2,z32,z3,z4,z5]),(0,[z0,z1,z2,z3,z255,z4,z5])],[(0,[z256,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z257,z3,z4,z5]),(0,[z258,z0,z1,z2,z3,z4,z5]),(0,[z259,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z260,z3,z4,z5]),(0,[z261,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z262,z1,z2,z3,z81,z4,z5]),(0,[z263,z0,z1,z2,z3,z4,z5]),(0,[z0,z131,z1,z37,z3,z4,z5]),(0,[z0,z41,z1,z264,z2,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z83]),(0,[z0,z1,z2,z3,z35,z4,z5]),(0,[z265,z0,z1,z2,z3,z4,z5]),(0,[z266,z0,z1,z2,z3,z4,z5])],[(0,[z0,z267,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z268,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z269,z5]),(0,[z270,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z271,z2,z3,z4,z5])],[(0,[z1,z2,z3,z81,z4,z5,z36]),(0,[z0,z1,z2,z17,z32,z4,z5]),(0,[z272,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z273,z4,z5]),(0,[z0,z1,z2,z274,z3,z4,z5])],[(0,[z275,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z67,z2,z3,z4,z68])],[(0,[z276,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z35,z4,z123]),(0,[z0,z1,z2,z3,z277,z4,z5])]],
   [[(0,[z114,z0,z1,z2,z3,z5,z50])],[(0,[z278,z0,z1,z2,z3,z4,z5]),(0,[z31,z0,z131,z2,z3,z4,z5]),(0,[z0,z1,z236,z2,z3,z4,z5]),(0,[z279,z0,z1,z2,z3,z4,z5]),(0,[z58,z0,z121,z1,z2,z3,z4]),(0,[z0,z1,z2,z86,z4,z5,z40]),(0,[z0,z1,z280,z2,z3,z4,z5])],[(0,[z281,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z282,z3,z4,z5]),(0,[z0,z1,z2,z283,z3,z4,z5]),(0,[z284,z0,z1,z2,z3,z4,z5]),(0,[z285,z0,z1,z26,z3,z4,z5]),(0,[z143,z0,z1,z2,z11,z4,z5])],[(0,[z0,z286,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z287,z3,z4,z5])],[(0,[z114,z0,z1,z2,z3,z5,z193]),(1,[z130,z0,z1,z38,z4,z5]),(0,[z288,z0,z1,z2,z3,z4,z5])],[(0,[z289,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z204,z61,z2,z3,z5]),(1,[z0,z1,z2,z3,z138,z4]),(0,[z290,z0,z1,z2,z3,z4,z5]),(0,[z291,z0,z1,z2,z3,z4,z5]),(0,[z292,z0,z1,z2,z3,z4,z5]),(0,[z293,z0,z1,z2,z3,z4,z5]),(1,[z0,z84,z2,z3,z85,z5]),(0,[z0,z1,z2,z3,z4,z85,z5]),(0,[z0,z1,z2,z3,z294,z4,z5]),(0,[z0,z1,z2,z3,z295,z4,z5])],[(0,[z296,z0,z1,z2,z3,z4,z5]),(0,[z73,z1,z2,z74,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z297])],[(0,[z298,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z299]),(0,[z0,z1,z2,z3,z4,z300,z5]),(0,[z301,z0,z1,z2,z3,z4,z5]),(0,[z58,z0,z1,z2,z3,z4,z5])]],
   [[(1,[z151,z1,z63,z3,z4,z5]),(0,[z0,z1,z2,z3,z171,z4,z5]),(0,[z118,z0,z1,z2,z86,z3,z4])],[(0,[z0,z1,z2,z302,z3,z4,z5]),(0,[z0,z1,z2,z3,z303,z4,z5]),(0,[z0,z1,z2,z304,z3,z4,z5])],[(0,[z305,z0,z1,z2,z3,z4,z5]),(0,[z57,z192,z0,z1,z2,z3,z4]),(0,[z0,z306,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z307,z4,z5])],[(0,[z0,z1,z2,z308,z3,z4,z5]),(0,[z0,z1,z2,z3,z309,z4,z5]),(0,[z310,z0,z1,z2,z3,z4,z5])],[(0,[z311,z0,z1,z2,z3,z4,z5]),(0,[z312,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z147,z4,z36]),(0,[z313,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z314,z5]),(0,[z0,z1,z2,z3,z39,z4,z5])],[(0,[z102,z0,z1,z2,z315,z4,z5])],[(0,[z73,z151,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z316,z3,z4,z5]),(0,[z0,z317,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z318,z3,z4,z5]),(0,[z0,z1,z2,z11,z3,z4,z5]),(0,[z0,z1,z319,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z320,z5]),(0,[z0,z321,z1,z2,z3,z4,z5]),(0,[z322,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z323,z4,z5]),(0,[z0,z1,z2,z324,z3,z4,z5]),(0,[z58,z90,z0,z1,z2,z3,z4])]],
   [[(0,[z22,z0,z23,z2,z3,z4,z5]),(0,[z0,z1,z2,z325,z3,z4,z5]),(0,[z0,z1,z2,z326,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z327,z5]),(0,[z56,z0,z1,z3,z39,z4,z5])],[(0,[z0,z1,z2,z3,z81,z4,z83])],[(0,[z328,z0,z1,z2,z3,z4,z5]),(0,[z262,z0,z121,z1,z2,z3,z4]),(0,[z329,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z181,z4,z5]),(0,[z130,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z330,z4,z5])],[(0,[z331,z0,z1,z2,z3,z4,z5]),(0,[z0,z131,z1,z2,z3,z4,z5]),(0,[z0,z332,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z333]),(0,[z0,z334,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z335,z5])],[(0,[z80,z0,z1,z2,z3,z4,z85]),(0,[z0,z1,z2,z336,z3,z4,z5])],[(0,[z0,z337,z1,z2,z3,z4,z5]),(0,[z24,z0,z1,z264,z2,z4,z5]),(0,[z57,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z338,z4,z5])],[(0,[z0,z1,z2,z3,z339,z4,z5]),(0,[z340,z0,z1,z2,z3,z4,z5]),(0,[z341,z0,z1,z2,z3,z4,z5]),(0,[z342,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z27,z5]),(0,[z0,z1,z2,z343,z3,z4,z5])],[(0,[z0,z1,z344,z2,z3,z4,z5]),(0,[z345,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z346]),(0,[z0,z1,z2,z347,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z68,z40]),(0,[z0,z1,z348,z2,z3,z4,z5])]],
   [[(0,[z262,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z349,z4,z5]),(0,[z0,z1,z2,z3,z350,z4,z5])],[(0,[z1,z2,z74,z3,z206,z4,z5]),(0,[z0,z1,z351,z2,z3,z4,z5])],[(0,[z62,z0,z1,z61,z2,z3,z4]),(0,[z352,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z5]),(0,[z353,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z354,z3,z4,z5])],[(0,[z256,z0,z1,z61,z2,z3,z5]),(0,[z0,z1,z2,z3,z355,z4,z5]),(0,[z0,z1,z2,z3,z4,z356,z5]),(0,[z57,z0,z1,z2,z3,z4,z123])],[(0,[z15,z0,z84,z1,z2,z3,z5]),(0,[z0,z1,z357,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z25,z4,z5]),(0,[z214,z0,z1,z3,z25,z4,z5]),(0,[z358,z0,z1,z2,z3,z4,z5])],[(0,[z19,z192,z1,z2,z3,z4,z5]),(0,[z359,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z360,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z123,z36]),(0,[z31,z0,z2,z32,z3,z4,z5]),(0,[z0,z41,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z361]),(0,[z0,z1,z362,z2,z3,z4,z5])],[(0,[z15,z0,z1,z2,z3,z81,z5]),(0,[z363,z0,z1,z2,z3,z4,z5]),(0,[z0,z131,z1,z236,z3,z4,z5]),(0,[z0,z1,z2,z3,z364,z4,z5]),(0,[z130,z0,z1,z2,z3,z4,z365]),(0,[z0,z1,z2,z3,z4,z5,z366]),(0,[z0,z1,z2,z3,z367,z4,z5])],[(0,[z0,z1,z368,z2,z3,z4,z5]),(0,[z0,z1,z2,z369,z3,z4,z5]),(0,[z56,z0,z1,z2,z3,z4,z68]),(0,[z370,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z371,z4,z5]),(0,[z0,z1,z2,z372,z3,z4,z5]),(0,[z262,z90,z0,z1,z2,z3,z4]),(0,[z24,z0,z1,z2,z373,z4,z5]),(0,[z0,z1,z2,z3,z374,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z123]),(0,[z0,z1,z2,z3,z4,z5,z375]),(0,[z0,z376,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z5]),(0,[z19,z1,z61,z2,z3,z4,z5]),(0,[z0,z1,z377,z2,z3,z4,z5]),(0,[z0,z1,z378,z2,z3,z4,z5]),(0,[z379,z0,z1,z2,z3,z4,z5]),(0,[z380,z0,z1,z2,z3,z4,z5]),(0,[z143,z0,z1,z2,z3,z5,z12])],[(0,[z0,z1,z2,z381,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z4,z5])],[(0,[z0,z1,z2,z3,z382,z4,z5]),(0,[z245,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z383,z11,z3,z5])],[(0,[z103,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z384,z4,z5]),(0,[z0,z1,z2,z385,z3,z4,z5])],[(0,[z386,z0,z1,z2,z3,z35,z5]),(0,[z0,z131,z1,z32,z3,z4,z5])],[(0,[z0,z1,z2,z86,z3,z4,z68]),(0,[z387,z0,z1,z2,z3,z4,z5]),(0,[z388,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z389])]],
   [[(0,[z73,z0,z1,z63,z3,z4,z5]),(0,[z0,z1,z2,z3,z390,z4,z5]),(0,[z0,z1,z2,z391,z3,z4,z5]),(0,[z0,z1,z2,z3,z147,z35,z4]),(0,[z0,z1,z392,z2,z3,z4,z5]),(0,[z90,z0,z1,z2,z3,z147,z4])],[(0,[z393,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z394,z4,z5]),(0,[z57,z0,z2,z3,z147,z4,z5]),(0,[z0,z1,z2,z3,z4,z395,z5])],[(0,[z0,z1,z2,z3,z4,z42,z5]),(0,[z0,z1,z2,z396,z3,z4,z5]),(0,[z0,z1,z2,z3,z397,z4,z5]),(0,[z0,z1,z2,z3,z147,z4,z193]),(0,[z0,z1,z2,z3,z398,z4,z5])],[(0,[z0,z1,z2,z3,z399,z4,z5]),(0,[z0,z1,z2,z3,z400,z4,z5]),(0,[z0,z1,z2,z3,z401,z4,z5]),(0,[z90,z72,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z402,z5]),(0,[z57,z0,z121,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z403,z5]),(0,[z0,z1,z2,z404,z3,z4,z5])],[(0,[z405,z0,z1,z2,z3,z4,z5]),(0,[z406,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z365]),(0,[z0,z407,z1,z2,z3,z4,z5]),(0,[z0,z408,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z409,z4,z5])],[(0,[z0,z1,z2,z373,z3,z4,z5]),(0,[z0,z1,z2,z410,z3,z4,z5]),(0,[z0,z1,z2,z3,z411,z4,z5])],[(0,[z114,z262,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z412,z3,z4,z5]),(0,[z0,z1,z2,z413,z3,z4,z5]),(0,[z414,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z415,z2,z3,z4,z5])]],
   [[(0,[z416,z0,z1,z2,z3,z4,z5]),(0,[z151,z0,z1,z63,z3,z4,z5]),(0,[z0,z417,z1,z2,z3,z4,z5]),(0,[z0,z84,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z418,z3,z4,z5]),(0,[z130,z0,z1,z264,z3,z4,z5])],[(0,[z419,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z122,z4,z36]),(0,[z420,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z421,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z197,z5]),(0,[z0,z1,z264,z2,z38,z4,z5]),(0,[z0,z1,z2,z3,z422,z4,z5]),(0,[z0,z1,z2,z423,z3,z4,z5]),(0,[z0,z424,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z81,z4,z5]),(0,[z58,z15,z0,z1,z2,z3,z5]),(0,[z89,z0,z2,z3,z194,z4,z5]),(0,[z143,z0,z1,z2,z383,z4,z5]),(0,[z0,z1,z2,z3,z4,z425,z5]),(0,[z0,z1,z2,z426,z3,z4,z5])],[(0,[z102,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z427])],[(0,[z428,z0,z1,z2,z3,z4,z5]),(0,[z429,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z295,z4,z27,z5]),(0,[z0,z1,z2,z3,z430,z4,z5])],[(0,[z0,z1,z431,z2,z3,z4,z5]),(0,[z432,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z67,z3,z4,z5,z68])],[(0,[z433,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z434,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z435]),(0,[z0,z1,z2,z3,z436,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z437]),(0,[z0,z1,z2,z3,z438,z4,z5])],[(0,[z439,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z440,z4,z5]),(1,[z150,z1,z2,z3,z4,z5])]],
   [[(0,[z441,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z442,z4,z5])],[(0,[z443,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z444]),(0,[z103,z1,z2,z3,z206,z4,z5]),(0,[z188,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z445,z3,z4,z5]),(0,[z0,z1,z2,z446,z3,z4,z5]),(0,[z90,z0,z84,z1,z2,z3,z5])],[(0,[z0,z1,z2,z447,z3,z4,z5]),(0,[z386,z0,z1,z2,z3,z4,z5]),(0,[z237,z0,z1,z2,z3,z4,z5]),(0,[z24,z0,z1,z2,z3,z4,z5]),(0,[z448,z0,z1,z2,z3,z4,z5]),(0,[z118,z0,z1,z2,z86,z4,z5]),(0,[z0,z1,z2,z449,z3,z4,z5])],[(0,[z0,z1,z2,z450,z3,z4,z5]),(0,[z451,z0,z1,z2,z3,z4,z5]),(1,[z188,z0,z1,z2,z3,z4]),(1,[z262,z1,z2,z3,z35,z4]),(0,[z0,z1,z2,z3,z4,z123,z193])],[(0,[z0,z1,z452,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z453,z4,z5])],[(0,[z0,z1,z2,z454,z3,z4,z5]),(0,[z0,z1,z2,z3,z455,z4,z5]),(0,[z456,z0,z1,z2,z3,z4,z5])],[(0,[z89,z0,z1,z2,z3,z122,z5]),(1,[z0,z121,z2,z3,z4,z123]),(0,[z0,z1,z2,z3,z457,z4,z5]),(0,[z0,z1,z2,z3,z38,z4,z5]),(0,[z0,z1,z458,z2,z3,z4,z5])],[(0,[z0,z1,z459,z2,z3,z4,z5]),(0,[z192,z0,z1,z2,z3,z4,z5]),(0,[z460,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z461,z2,z3,z4,z5]),(0,[z0,z1,z462,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z463]),(0,[z0,z464,z1,z2,z3,z4,z5])],[(0,[z103,z0,z1,z2,z315,z4,z5]),(0,[z0,z1,z465,z2,z3,z4,z5]),(0,[z0,z121,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z466,z4,z5]),(0,[z467,z0,z1,z2,z3,z4,z5])],[],[(0,[z468,z0,z1,z2,z3,z4,z5]),(0,[z130,z110,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z469,z4,z5]),(0,[z0,z1,z2,z470,z3,z4,z5])],[(0,[z62,z0,z1,z2,z3,z4,z5]),(0,[z192,z1,z2,z3,z4,z5,z36]),(0,[z58,z0,z1,z2,z3,z4,z36]),(0,[z0,z1,z2,z3,z4,z5,z471]),(0,[z472,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z473,z3,z4,z5])],[(0,[z0,z1,z2,z3,z474,z4,z5]),(0,[z0,z1,z2,z3,z475,z4,z5]),(0,[z0,z476,z1,z2,z3,z4,z5])],[(0,[z0,z2,z32,z3,z25,z4,z5]),(0,[z0,z41,z1,z2,z373,z4,z5]),(1,[z72,z1,z2,z3,z4,z5])],[(0,[z262,z192,z1,z2,z3,z4,z5]),(0,[z192,z90,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z477,z3,z4,z5]),(0,[z56,z0,z1,z67,z3,z4,z5]),(0,[z0,z1,z2,z478,z3,z4,z5]),(0,[z0,z1,z2,z3,z122,z5,z193])]],
   [[(0,[z0,z1,z2,z3,z479,z4,z5])],[(0,[z0,z1,z480,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z481,z4,z5]),(0,[z482,z0,z1,z2,z3,z4,z5])],[(1,[z0,z131,z236,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z483]),(0,[z0,z84,z1,z2,z3,z122,z5]),(0,[z0,z1,z2,z484,z3,z4,z5]),(0,[z0,z485,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z486]),(0,[z1,z63,z2,z74,z3,z4,z5]),(0,[z130,z0,z196,z2,z3,z4,z5]),(0,[z487,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z488,z3,z4,z5]),(0,[z90,z0,z1,z2,z3,z122,z4]),(0,[z150,z0,z1,z2,z3,z4,z5])],[(0,[z0,z2,z373,z3,z25,z4,z5]),(0,[z0,z84,z1,z2,z3,z194,z5]),(0,[z130,z0,z1,z2,z37,z4,z5]),(0,[z489,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z122,z35,z4]),(0,[z0,z1,z2,z17,z3,z4,z5]),(0,[z0,z1,z2,z490,z3,z4,z5]),(0,[z491,z0,z1,z2,z3,z4,z5]),(0,[z285,z0,z1,z2,z3,z27,z5])],[(0,[z0,z1,z2,z492,z3,z4,z5]),(0,[z0,z1,z493,z2,z3,z4,z5]),(0,[z0,z1,z494,z2,z3,z4,z5])],[(0,[z0,z1,z495,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z122,z4,z193])]],
   [[(0,[z0,z236,z2,z32,z3,z4,z5]),(0,[z0,z1,z2,z496,z3,z4,z5]),(0,[z497,z0,z1,z2,z3,z4,z5]),(0,[z498,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z499,z3,z4,z5]),(0,[z130,z0,z1,z2,z3,z4,z500]),(0,[z501,z0,z1,z2,z3,z4,z5])],[(0,[z0,z0,z1,z2,z3,z4,z5]),(0,[z19,z0,z23,z2,z3,z4,z5]),(0,[z502,z0,z1,z2,z3,z4,z5]),(0,[z19,z1,z2,z3,z35,z4,z5]),(0,[z503,z0,z1,z2,z3,z4,z5]),(0,[z0,z504,z1,z2,z3,z4,z5]),(1,[z110,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z68])],[(0,[z23,z1,z61,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z122,z193])],[(0,[z0,z1,z2,z3,z211,z4,z5]),(0,[z0,z1,z2,z3,z505,z4,z5]),(0,[z0,z1,z2,z3,z506,z4,z5]),(0,[z507,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z508,z4,z5]),(0,[z509,z0,z1,z2,z3,z4,z5]),(0,[z510,z0,z1,z2,z3,z4,z5]),(0,[z262,z0,z1,z2,z3,z4,z36]),(0,[z0,z1,z2,z3,z35,z511,z5]),(0,[z130,z24,z0,z1,z2,z4,z5]),(0,[z512,z0,z1,z2,z3,z4,z5]),(0,[z513,z0,z1,z2,z3,z4,z5])],[(0,[z514,z0,z1,z2,z3,z4,z5]),(0,[z1,z2,z315,z3,z206,z4,z5]),(0,[z89,z114,z0,z1,z2,z3,z5]),(0,[z0,z84,z1,z2,z3,z85,z5]),(0,[z515,z0,z1,z2,z3,z4,z5]),(0,[z516,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z36]),(0,[z0,z1,z2,z3,z4,z5,z517])]],
   [[(1,[z89,z0,z2,z3,z194,z5]),(0,[z0,z1,z2,z3,z4,z5,z518]),(0,[z519,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z295,z5,z12])],[(0,[z0,z520,z1,z2,z3,z4,z5]),(0,[z0,z131,z236,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z500]),(0,[z285,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z521,z2,z3,z4,z5]),(0,[z90,z0,z1,z2,z3,z5,z193])],[(0,[z522,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z523,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z524]),(0,[z1,z2,z3,z81,z4,z5,z50]),(0,[z525,z0,z1,z2,z3,z4,z5]),(1,[z0,z196,z2,z3,z4,z5]),(0,[z0,z1,z264,z2,z3,z4,z5]),(0,[z0,z1,z2,z383,z4,z5,z12])],[(0,[z526,z0,z1,z2,z3,z4,z5])],[(0,[z285,z0,z1,z2,z3,z295,z5]),(0,[z0,z1,z2,z527,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z528,z5])],[(0,[z529,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z530]),(0,[z1,z2,z3,z171,z4,z85,z5]),(0,[z58,z90,z0,z1,z2,z3,z5])],[(0,[z0,z1,z531,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z532,z4,z5]),(0,[z533,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z534,z5]),(0,[z0,z1,z2,z3,z535,z4,z5])]],
   [[(0,[z58,z0,z1,z2,z3,z35,z4]),(0,[z536,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z500])],[(0,[z0,z1,z2,z3,z4,z5,z537]),(0,[z538,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z539,z2,z3,z4,z5]),(0,[z0,z1,z2,z11,z3,z5,z12]),(1,[z0,z1,z2,z119,z4,z40])],[(0,[z0,z1,z540,z2,z3,z4,z5]),(0,[z0,z1,z2,z541,z3,z4,z5]),(0,[z542,z0,z1,z2,z3,z4,z5]),(0,[z130,z284,z1,z2,z3,z4,z5]),(0,[z543,z0,z1,z2,z3,z4,z5]),(0,[z58,z0,z1,z2,z3,z4,z193])],[(0,[z0,z1,z2,z3,z544,z4,z5]),(0,[z0,z545,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z546,z5]),(0,[z0,z1,z2,z3,z4,z365,z5]),(1,[z285,z0,z1,z3,z295,z5]),(0,[z0,z1,z2,z3,z547,z4,z5]),(0,[z548,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z549,z3,z4,z5])],[(0,[z102,z1,z2,z315,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z550]),(0,[z0,z1,z2,z551,z3,z4,z5]),(0,[z0,z1,z2,z552,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z553,z5]),(0,[z554,z0,z1,z2,z3,z4,z5])],[(0,[z0,z555,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z556,z3,z4,z5])],[(0,[z0,z1,z557,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z206,z4,z5]),(0,[z0,z558,z1,z2,z3,z4,z5]),(1,[z386,z0,z1,z2,z3,z5]),(0,[z89,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z559,z4,z5])]],
   [[(0,[z0,z560,z1,z2,z3,z4,z5]),(0,[z89,z0,z84,z2,z3,z4,z5]),(1,[z561,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z562,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z563])],[(0,[z564,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z565,z4,z5]),(0,[z566,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z567,z5,z123]),(0,[z568,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z569,z3,z4,z5])],[(0,[z0,z1,z570,z2,z3,z4,z5]),(0,[z0,z1,z571,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z572,z4,z5]),(0,[z573,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z574,z4,z5]),(0,[z0,z1,z2,z3,z575,z4,z5]),(0,[z0,z1,z2,z3,z567,z4,z5]),(0,[z0,z1,z576,z2,z3,z4,z5])],[(0,[z577,z0,z1,z2,z3,z4,z5]),(1,[z15,z1,z2,z3,z81,z5]),(0,[z0,z1,z2,z3,z578,z4,z5]),(0,[z0,z1,z2,z3,z579,z4,z5])],[(0,[z580,z0,z1,z2,z3,z4,z5]),(0,[z581,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z582]),(0,[z130,z0,z1,z3,z38,z4,z5]),(0,[z0,z1,z26,z2,z3,z27,z5])],[(0,[z114,z0,z1,z2,z3,z4,z5]),(0,[z583,z0,z1,z2,z3,z4,z5]),(0,[z0,z584,z1,z2,z3,z4,z5])],[(1,[z103,z1,z2,z206,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z585]),(0,[z0,z1,z2,z586,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z587])]],
   [[(1,[z19,z61,z2,z3,z4,z5]),(0,[z102,z1,z2,z74,z3,z4,z5]),(0,[z0,z1,z2,z588,z3,z4,z5]),(0,[z589,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z436,z4]),(1,[z80,z0,z1,z2,z3,z4])],[(0,[z262,z0,z1,z2,z3,z35,z4]),(0,[z0,z1,z2,z3,z590,z4,z5]),(1,[z284,z1,z2,z3,z4,z5])],[(0,[z0,z1,z77,z61,z2,z3,z4]),(0,[z0,z1,z2,z3,z591,z4,z5])],[(0,[z114,z1,z2,z3,z4,z5,z36]),(0,[z262,z0,z1,z2,z3,z4,z193]),(0,[z0,z1,z2,z592,z3,z4,z5]),(0,[z593,z0,z1,z2,z3,z4,z5])],[(0,[z594,z0,z1,z2,z3,z4,z5]),(0,[z0,z131,z2,z3,z25,z4,z5]),(0,[z0,z1,z595,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z596,z4,z5]),(0,[z0,z1,z2,z597,z3,z4,z5]),(0,[z0,z1,z598,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z599,z4,z5]),(0,[z0,z1,z2,z119,z3,z4,z40])],[(0,[z73,z0,z1,z74,z3,z4,z5]),(0,[z0,z600,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z12]),(0,[z601,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z193])],[(0,[z22,z0,z61,z2,z3,z4,z5]),(1,[z22,z23,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z602]),(0,[z101,z1,z2,z3,z4,z85,z5]),(0,[z561,z0,z1,z2,z3,z5,z123]),(0,[z0,z1,z603,z2,z3,z4,z5])],[(0,[z604,z0,z1,z2,z3,z4,z5]),(1,[z245,z1,z2,z3,z4,z5])]],
   [[(0,[z102,z151,z1,z2,z3,z4,z5]),(0,[z605,z0,z1,z2,z3,z4,z5]),(0,[z561,z0,z1,z2,z3,z4,z5]),(0,[z0,z606,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z607,z3,z4,z5]),(1,[z0,z1,z264,z37,z4,z5]),(0,[z0,z1,z26,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z608,z4,z5]),(0,[z57,z0,z1,z2,z3,z147,z4]),(0,[z130,z0,z1,z2,z3,z338,z5]),(0,[z0,z1,z2,z3,z4,z5,z609]),(0,[z0,z1,z2,z3,z610,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z611]),(0,[z15,z0,z1,z2,z3,z5,z50]),(1,[z0,z1,z26,z3,z27,z5]),(0,[z285,z0,z1,z3,z295,z4,z5])],[(0,[z19,z0,z1,z2,z3,z4,z6]),(0,[z192,z0,z1,z2,z3,z4,z36]),(0,[z192,z0,z121,z1,z2,z3,z4]),(0,[z262,z1,z2,z3,z35,z4,z5]),(0,[z0,z1,z26,z2,z3,z295,z5])],[(0,[z612,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z613,z4,z5]),(0,[z151,z0,z1,z74,z3,z4,z5]),(0,[z0,z1,z614,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z511,z5]),(0,[z615,z0,z1,z2,z3,z4,z5]),(1,[z0,z41,z2,z373,z4,z5]),(0,[z0,z1,z161,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z511,z5]),(0,[z0,z41,z131,z2,z3,z4,z5]),(0,[z0,z1,z2,z616,z3,z4,z5]),(0,[z0,z1,z617,z2,z3,z4,z5]),(1,[z214,z0,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z618]),(0,[z0,z1,z2,z3,z619,z4,z5])],[(0,[z620,z0,z1,z2,z3,z4,z5]),(0,[z621,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z138,z4,z5]),(0,[z15,z0,z1,z2,z3,z5,z193]),(0,[z0,z1,z2,z3,z622,z4,z5]),(0,[z0,z1,z2,z3,z623,z4,z5]),(1,[z0,z1,z2,z3,z4,z76]),(0,[z0,z1,z2,z3,z4,z5,z624]),(0,[z0,z1,z2,z625,z3,z4,z5]),(0,[z626,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z51,z25,z4,z5]),(0,[z627,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z628,z2,z3,z4,z5])],[],[(0,[z0,z1,z629,z2,z3,z4,z5]),(0,[z0,z1,z2,z630,z3,z4,z5]),(0,[z0,z1,z631,z2,z3,z4,z5]),(0,[z0,z1,z264,z37,z3,z4,z5])],[(0,[z0,z1,z2,z315,z3,z4,z5]),(0,[z89,z0,z1,z2,z3,z194,z5]),(0,[z632,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z383,z3,z27,z5])],[(0,[z23,z1,z2,z3,z35,z4,z5]),(0,[z114,z15,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z633,z3,z4,z5]),(0,[z0,z1,z2,z3,z634,z4,z5])],[(0,[z0,z1,z635,z2,z3,z4,z5]),(0,[z636,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z637]),(0,[z0,z1,z638,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z639,z4,z5])],[(0,[z73,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z194,z4,z5]),(0,[z0,z1,z2,z3,z640,z4,z5]),(0,[z0,z1,z2,z641,z3,z4,z5])],[(0,[z0,z1,z2,z3,z642,z4,z5]),(0,[z0,z1,z2,z3,z643,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z644,z4,z5]),(0,[z645,z0,z1,z2,z3,z4,z5]),(1,[z143,z0,z1,z2,z383,z5])],[(0,[z0,z1,z2,z3,z4,z646,z5]),(1,[z0,z1,z2,z3,z338,z5]),(0,[z0,z647,z1,z2,z3,z4,z5]),(0,[z648,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z649,z4,z5])],[(0,[z0,z1,z2,z3,z650,z4,z5]),(0,[z0,z1,z2,z3,z651,z4,z5]),(0,[z0,z121,z1,z2,z3,z4,z123])],[(0,[z19,z1,z2,z3,z81,z4,z5]),(0,[z652,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z653,z3,z4,z5]),(0,[z654,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z204,z2,z3,z5]),(1,[z114,z1,z2,z3,z5,z50]),(1,[z192,z1,z2,z3,z4,z36]),(0,[z89,z0,z1,z2,z3,z85,z5])],[(0,[z0,z1,z2,z3,z655,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z656]),(0,[z0,z1,z2,z3,z436,z4,z85]),(0,[z0,z657,z1,z2,z3,z4,z5]),(1,[z58,z90,z0,z1,z2,z3])],[(0,[z0,z1,z658,z2,z3,z4,z5]),(0,[z0,z1,z2,z74,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z659,z5]),(0,[z0,z41,z1,z2,z25,z4,z5]),(0,[z660,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z383,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z661,z5]),(0,[z0,z662,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z663]),(0,[z0,z41,z2,z373,z3,z4,z5]),(1,[z0,z1,z2,z3,z211,z4]),(1,[z57,z0,z2,z3,z147,z4])],[],[(0,[z0,z1,z2,z3,z4,z5,z664]),(0,[z89,z15,z0,z1,z2,z3,z5]),(0,[z0,z1,z665,z2,z3,z4,z5]),(0,[z0,z1,z2,z383,z3,z295,z5]),(0,[z143,z0,z1,z2,z383,z3,z5])],[(0,[z666,z0,z1,z2,z3,z4,z5]),(0,[z667,z0,z1,z2,z3,z4,z5])],[(0,[z668,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z669,z4,z5]),(0,[z0,z1,z2,z3,z670,z4,z5]),(0,[z0,z671,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z672,z5]),(0,[z0,z1,z264,z2,z37,z4,z5])],[(0,[z0,z1,z67,z2,z3,z39,z4])],[(0,[z0,z1,z2,z3,z673,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z674])],[(0,[z0,z1,z2,z3,z4,z5,z675])]],
   [[(0,[z192,z0,z1,z2,z3,z35,z4]),(0,[z0,z676,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z677,z5]),(0,[z0,z678,z1,z2,z3,z4,z5])],[(0,[z192,z23,z1,z2,z3,z4,z5]),(0,[z679,z0,z1,z2,z3,z4,z5]),(0,[z680,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z681,z4,z5]),(0,[z0,z41,z2,z32,z3,z4,z5])],[(0,[z24,z0,z2,z3,z25,z4,z5]),(0,[z0,z1,z2,z682,z3,z4,z5]),(0,[z0,z1,z683,z2,z3,z4,z5]),(0,[z684,z0,z1,z2,z3,z4,z5])],[(0,[z19,z22,z1,z2,z3,z4,z5]),(0,[z0,z1,z77,z2,z3,z4,z5]),(0,[z0,z685,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z686,z4,z5]),(0,[z57,z262,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z86,z119,z3,z4])],[(0,[z0,z1,z2,z3,z4,z5,z687]),(1,[z102,z1,z2,z315,z4,z5]),(0,[z130,z0,z41,z1,z2,z4,z5]),(0,[z57,z0,z1,z2,z3,z122,z4])],[(0,[z0,z1,z2,z688,z3,z4,z5]),(0,[z689,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z690,z5]),(1,[z1,z2,z3,z181,z4,z5]),(0,[z0,z1,z2,z691,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z16])]],
   [[(1,[z256,z0,z1,z2,z3,z5]),(0,[z0,z692,z1,z2,z3,z4,z5]),(0,[z693,z0,z1,z2,z3,z4,z5])],[(0,[z114,z0,z84,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z694,z4,z5])],[(0,[z114,z58,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z695,z4,z5]),(1,[z0,z1,z2,z3,z567,z5])],[(0,[z114,z0,z1,z2,z3,z81,z5]),(0,[z0,z1,z2,z3,z696,z4,z5]),(0,[z697,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z698,z4,z5])],[(0,[z0,z699,z1,z2,z3,z4,z5]),(1,[z118,z0,z1,z2,z86,z4])],[(0,[z0,z1,z2,z3,z700,z4,z5]),(0,[z0,z1,z2,z701,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z702,z5]),(0,[z703,z0,z1,z2,z3,z4,z5]),(0,[z0,z704,z1,z2,z3,z4,z5]),(0,[z0,z121,z1,z2,z3,z147,z4]),(0,[z130,z0,z1,z2,z38,z4,z5])],[(0,[z0,z1,z2,z3,z705,z4,z5]),(0,[z237,z0,z1,z2,z32,z4,z5]),(0,[z0,z1,z2,z706,z3,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z707]),(0,[z15,z1,z2,z3,z81,z138]),(0,[z101,z1,z2,z3,z436,z4])],[(0,[z708,z1,z2,z3,z4,z5]),(0,[z709,z0,z1,z2,z3,z4])],[(0,[z0,z1,z710,z3,z4,z5]),(0,[z0,z1,z2,z3,z511,z123]),(0,[z711,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z712,z4,z5])],[(0,[z713,z0,z1,z2,z3,z4]),(0,[z0,z236,z714,z3,z4,z5]),(0,[z0,z1,z2,z3,z715,z5]),(0,[z561,z0,z121,z2,z3,z123]),(0,[z130,z0,z1,z38,z4,z5]),(0,[z0,z1,z2,z484,z4,z40])]],
   [[(0,[z245,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z716]),(0,[z0,z1,z2,z717,z3,z5]),(1,[z1,z2,z3,z718,z5]),(0,[z0,z1,z3,z719,z4,z5]),(0,[z130,z110,z1,z38,z4,z5]),(0,[z0,z1,z2,z3,z338,z500]),(0,[z720,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z721,z4]),(0,[z358,z1,z2,z3,z4,z36]),(0,[z0,z1,z2,z3,z4,z722]),(0,[z0,z84,z2,z3,z350,z5]),(0,[z89,z0,z1,z2,z3,z436]),(0,[z56,z0,z1,z3,z39,z4]),(0,[z118,z0,z1,z2,z723,z4])],[(0,[z0,z1,z724,z3,z4,z5]),(0,[z19,z202,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z718,z5]),(0,[z386,z1,z2,z3,z5,z36]),(0,[z31,z237,z0,z32,z4,z5]),(0,[z725,z1,z2,z3,z4,z5]),(0,[z0,z1,z726,z3,z4,z5]),(0,[z0,z1,z2,z3,z727,z4])],[(0,[z15,z1,z2,z3,z81,z83]),(0,[z1,z2,z3,z4,z728,z36]),(0,[z237,z0,z2,z25,z4,z5]),(0,[z130,z0,z1,z13,z4,z5]),(0,[z0,z161,z2,z3,z338,z5]),(0,[z143,z0,z1,z2,z383,z5])]],
   [[(0,[z0,z1,z2,z729,z4,z5]),(0,[z0,z1,z2,z730,z4,z5]),(0,[z114,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z731,z4,z5]),(0,[z0,z732,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z733,z5]),(0,[z0,z1,z2,z3,z4,z734]),(0,[z262,z1,z2,z3,z4,z659]),(0,[z0,z1,z2,z3,z735,z4])],[(1,[z736,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z737,z5]),(0,[z738,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z739]),(0,[z740,z1,z2,z3,z4,z5]),(0,[z150,z1,z2,z3,z5,z193])],[(0,[z0,z1,z2,z3,z4,z741]),(0,[z0,z742,z2,z3,z4,z5]),(0,[z72,z1,z2,z3,z122,z4])],[(0,[z0,z743,z1,z2,z3,z4]),(0,[z192,z1,z2,z3,z4,z728]),(0,[z58,z693,z0,z1,z2,z3]),(0,[z0,z1,z2,z3,z4,z744])]],
   [[(0,[z0,z1,z204,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z745]),(0,[z0,z1,z2,z746,z3,z4]),(0,[z192,z1,z2,z3,z4,z36]),(0,[z130,z0,z1,z651,z4,z5]),(0,[z0,z1,z2,z3,z4,z747]),(0,[z0,z1,z2,z3,z4,z748]),(0,[z0,z1,z264,z749,z4,z5])],[(0,[z750,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z751,z5]),(0,[z0,z1,z2,z752,z4,z5]),(0,[z58,z90,z0,z1,z2,z3])],[(0,[z114,z1,z2,z3,z5,z435]),(0,[z753,z1,z2,z3,z4,z5]),(0,[z245,z90,z1,z2,z3,z4]),(0,[z754,z1,z2,z3,z4,z5])],[(0,[z130,z0,z1,z38,z4,z365])]],
   [[(0,[z0,z1,z2,z3,z755,z5]),(0,[z19,z736,z2,z3,z4,z5]),(0,[z693,z1,z2,z3,z81,z5]),(0,[z0,z2,z756,z25,z4,z5]),(0,[z214,z24,z0,z25,z4,z5]),(0,[z57,z0,z1,z2,z3,z567]),(0,[z110,z1,z2,z3,z4,z500]),(0,[z275,z0,z1,z2,z383,z5])],[(0,[z0,z1,z2,z3,z757,z5]),(0,[z0,z1,z2,z758,z3,z5]),(0,[z0,z1,z2,z759,z3,z4]),(0,[z256,z0,z1,z77,z2,z3]),(0,[z594,z192,z1,z2,z3,z4]),(0,[z1,z63,z760,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z761]),(0,[z0,z762,z2,z3,z4,z5]),(0,[z15,z704,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z763,z5]),(0,[z245,z561,z1,z2,z3,z5])],[(0,[z1,z2,z3,z35,z4,z6]),(0,[z764,z1,z2,z3,z4,z5]),(0,[z57,z0,z2,z3,z735,z4]),(0,[z0,z765,z2,z3,z4,z5])],[(0,[z1,z2,z3,z171,z4,z5]),(0,[z245,z121,z2,z3,z4,z123]),(0,[z110,z161,z2,z3,z4,z5]),(0,[z285,z0,z1,z3,z766,z5])]],
   [[(0,[z0,z1,z2,z767,z4,z5]),(0,[z0,z1,z2,z3,z4,z768]),(0,[z0,z41,z161,z2,z4,z5]),(0,[z89,z0,z2,z3,z194,z5]),(0,[z0,z1,z2,z3,z338,z365]),(0,[z769,z1,z2,z3,z4,z5])],[(0,[z770,z0,z1,z2,z3,z5]),(0,[z284,z1,z2,z3,z338,z5]),(0,[z771,z1,z2,z3,z4,z5])],[(0,[z114,z262,z1,z2,z3,z193])],[(0,[z0,z1,z2,z3,z772,z5]),(0,[z0,z1,z2,z3,z773,z4]),(0,[z0,z774,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z728]),(0,[z0,z1,z37,z453,z4,z5]),(0,[z0,z84,z2,z3,z436,z85]),(0,[z0,z1,z2,z3,z4,z775])]],
   [[(0,[z19,z62,z61,z2,z3,z4]),(0,[z0,z1,z2,z776,z3,z5]),(0,[z0,z1,z2,z3,z777,z5]),(0,[z778,z0,z2,z3,z4,z5]),(1,[z0,z714,z3,z4,z5]),(0,[z0,z2,z3,z779,z4,z5]),(0,[z780,z1,z2,z3,z4,z5]),(0,[z0,z196,z2,z3,z4,z500])],[(0,[z73,z1,z760,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z728])],[(0,[z0,z1,z2,z3,z4,z781]),(0,[z328,z114,z1,z2,z3,z5]),(0,[z23,z2,z3,z208,z4,z5]),(0,[z0,z1,z2,z3,z782,z5]),(0,[z0,z1,z2,z3,z783,z5]),(0,[z130,z310,z0,z1,z4,z5]),(0,[z0,z784,z1,z2,z3,z193])],[(0,[z785,z0,z1,z2,z3,z4])]],
   [[(0,[z102,z1,z2,z315,z4,z5]),(0,[z114,z215,z1,z2,z3,z5]),(0,[z786,z0,z1,z2,z3,z5]),(0,[z0,z1,z787,z3,z4,z5]),(0,[z0,z2,z3,z147,z735,z4]),(0,[z0,z1,z2,z3,z4,z500])],[(0,[z1,z2,z3,z181,z4,z5]),(0,[z262,z1,z2,z3,z4,z728]),(0,[z130,z0,z504,z1,z4,z5]),(0,[z0,z121,z1,z2,z3,z567]),(0,[z0,z1,z2,z318,z5,z12])],[(0,[z0,z1,z2,z3,z788,z5]),(0,[z0,z1,z2,z3,z4,z16]),(0,[z0,z789,z2,z3,z4,z5]),(0,[z192,z560,z1,z2,z3,z4]),(0,[z790,z1,z2,z3,z4,z5])],[(0,[z256,z0,z1,z2,z3,z5]),(0,[z689,z1,z2,z206,z4,z5]),(0,[z0,z714,z32,z3,z4,z5]),(0,[z0,z161,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z779,z5]),(0,[z0,z121,z2,z3,z735,z4]),(0,[z285,z0,z1,z3,z295,z5])]],
   [[(0,[z114,z1,z2,z3,z113,z5]),(0,[z0,z1,z2,z791,z3,z4]),(0,[z0,z1,z2,z3,z567,z35]),(0,[z792,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z793,z5]),(0,[z0,z1,z2,z3,z567,z5]),(0,[z101,z84,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z4,z794]),(0,[z441,z1,z2,z3,z4,z36]),(0,[z182,z1,z2,z3,z35,z4]),(0,[z0,z1,z3,z795,z4,z5]),(0,[z796,z1,z2,z3,z4,z5]),(0,[z90,z0,z1,z91,z2,z3])],[(0,[z19,z256,z61,z2,z3,z5]),(0,[z23,z1,z204,z2,z3,z5]),(0,[z386,z0,z1,z2,z3,z5]),(0,[z114,z1,z2,z3,z718,z5]),(0,[z114,z558,z1,z2,z3,z5])]],
   [[(0,[z23,z2,z3,z9,z4,z5]),(0,[z370,z1,z2,z3,z35,z4]),(0,[z0,z1,z2,z3,z4,z797]),(0,[z561,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z798,z4]),(0,[z799,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z171,z436,z4]),(0,[z0,z196,z2,z3,z197,z5]),(0,[z0,z800,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z801]),(0,[z58,z0,z1,z2,z3,z138]),(0,[z24,z0,z2,z756,z4,z5]),(0,[z0,z1,z2,z3,z802,z5])],[(0,[z0,z1,z2,z3,z4,z803]),(0,[z804,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z122,z403]),(0,[z58,z0,z1,z2,z3,z269])]],
   [[(0,[z0,z1,z2,z3,z4,z805]),(0,[z23,z736,z2,z3,z4,z5]),(0,[z15,z1,z2,z3,z81,z5]),(0,[z0,z1,z2,z3,z806,z5]),(0,[z0,z84,z1,z2,z3,z436]),(0,[z70,z0,z1,z2,z3,z122]),(0,[z648,z0,z1,z3,z295,z5])],[(0,[z0,z1,z2,z3,z4,z807]),(1,[z1,z760,z3,z4,z5]),(0,[z114,z1,z2,z3,z672,z5]),(0,[z15,z188,z1,z2,z3,z81]),(0,[z15,z0,z1,z2,z3,z76]),(0,[z262,z188,z1,z2,z3,z4]),(0,[z808,z0,z1,z2,z4,z5]),(0,[z0,z1,z809,z3,z4,z5]),(0,[z284,z196,z2,z3,z4,z5])],[(0,[z0,z1,z810,z3,z4,z5]),(0,[z19,z188,z1,z2,z3,z4]),(0,[z386,z23,z1,z2,z3,z5]),(0,[z237,z0,z1,z2,z4,z5]),(0,[z0,z1,z811,z3,z4,z5]),(0,[z0,z1,z2,z3,z812,z5]),(0,[z72,z1,z2,z3,z147,z4])],[(0,[z62,z0,z1,z204,z2,z3]),(0,[z0,z1,z760,z3,z4,z5]),(0,[z103,z1,z2,z206,z4,z5]),(0,[z114,z0,z1,z2,z3,z83]),(0,[z0,z1,z2,z3,z813,z5]),(0,[z0,z161,z2,z3,z4,z365]),(0,[z0,z1,z2,z3,z197,z500])]],
   [[(0,[z19,z61,z2,z3,z4,z5]),(0,[z19,z638,z2,z3,z4,z5]),(0,[z62,z256,z0,z1,z2,z3]),(0,[z814,z1,z2,z3,z4,z5])],[(0,[z0,z1,z815,z3,z4,z5]),(0,[z284,z1,z2,z3,z4,z5]),(0,[z31,z0,z32,z3,z4,z5]),(0,[z0,z816,z2,z3,z4,z5]),(0,[z0,z1,z2,z752,z11,z5])],[(0,[z0,z1,z2,z3,z4,z817]),(0,[z0,z1,z2,z3,z818,z5]),(0,[z0,z1,z2,z3,z4,z819]),(0,[z0,z1,z2,z820,z3,z5]),(0,[z0,z1,z2,z3,z138,z193]),(0,[z237,z0,z41,z2,z4,z5]),(0,[z0,z1,z2,z821,z4,z5]),(0,[z822,z1,z2,z3,z4,z5]),(0,[z84,z2,z3,z171,z85,z5]),(0,[z0,z161,z2,z3,z197,z5]),(0,[z823,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z824]),(0,[z192,z72,z1,z2,z3,z4]),(0,[z0,z1,z825,z2,z3,z4]),(0,[z1,z2,z3,z826,z4,z5]),(0,[z0,z133,z2,z3,z4,z123]),(0,[z130,z0,z161,z38,z4,z5]),(0,[z0,z1,z2,z3,z4,z827]),(0,[z0,z1,z3,z39,z727,z4])]],
   [[(0,[z828,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z829]),(0,[z0,z84,z202,z2,z3,z5]),(0,[z0,z830,z2,z3,z4,z5]),(0,[z0,z1,z3,z766,z27,z5])],[(0,[z831,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z832,z4,z5]),(0,[z0,z1,z348,z3,z4,z68]),(0,[z0,z133,z1,z2,z3,z122]),(1,[z0,z784,z1,z2,z3])],[(0,[z22,z23,z2,z3,z4,z5]),(0,[z19,z61,z2,z3,z4,z42])],[(0,[z245,z1,z2,z3,z4,z5]),(0,[z833,z0,z1,z2,z3,z5]),(0,[z151,z1,z760,z3,z4,z5]),(0,[z245,z1,z2,z3,z4,z36]),(0,[z834,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z51,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z835,z5]),(0,[z0,z1,z2,z3,z836,z5]),(0,[z1,z2,z837,z3,z4,z5]),(0,[z838,z0,z1,z2,z3,z4]),(0,[z24,z0,z51,z25,z4,z5])],[(0,[z0,z1,z2,z3,z4,z839]),(0,[z0,z41,z2,z217,z4,z5]),(0,[z0,z1,z2,z3,z840,z4]),(0,[z0,z1,z2,z756,z4,z5]),(0,[z0,z1,z3,z749,z4,z5]),(0,[z0,z1,z2,z723,z4,z40])],[(0,[z841,z0,z1,z2,z3,z4]),(0,[z842,z0,z1,z2,z3,z5]),(0,[z0,z1,z843,z3,z4,z5]),(0,[z844,z1,z2,z3,z4,z5]),(0,[z57,z0,z280,z2,z3,z4]),(0,[z0,z1,z3,z727,z4,z5])],[(0,[z1,z736,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z845,z4]),(0,[z0,z1,z2,z837,z4,z5]),(0,[z0,z1,z2,z846,z4,z5]),(0,[z0,z1,z2,z3,z847,z5]),(0,[z0,z1,z2,z3,z4,z848])]],
   [[(0,[z849,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z850,z4]),(0,[z58,z0,z1,z2,z3,z659]),(0,[z31,z0,z714,z3,z4,z5]),(0,[z90,z0,z784,z1,z2,z3])],[(0,[z1,z2,z3,z35,z4,z664]),(0,[z851,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z511,z5]),(0,[z110,z1,z2,z3,z338,z5]),(0,[z284,z1,z2,z3,z4,z365]),(1,[z0,z1,z2,z723,z4])],[(0,[z19,z61,z2,z3,z4,z6]),(0,[z19,z1,z77,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z852]),(0,[z188,z0,z1,z2,z3,z4]),(0,[z262,z1,z2,z3,z35,z4]),(0,[z214,z0,z1,z3,z4,z5]),(0,[z89,z0,z2,z3,z779,z5]),(0,[z150,z58,z90,z1,z2,z3])],[(0,[z0,z1,z2,z853,z4,z5])]],
   [[(0,[z1,z2,z760,z3,z4,z5]),(0,[z0,z1,z2,z3,z854,z5]),(0,[z0,z1,z2,z3,z4,z83]),(0,[z262,z1,z2,z3,z35,z511]),(0,[z0,z1,z2,z3,z855,z5]),(0,[z89,z0,z576,z2,z3,z5]),(0,[z284,z1,z2,z3,z197,z5]),(0,[z0,z856,z2,z3,z4,z5]),(0,[z0,z1,z3,z766,z4,z5]),(0,[z0,z1,z2,z723,z119,z4])],[(0,[z1,z2,z3,z81,z534,z5]),(0,[z0,z1,z857,z3,z4,z5]),(0,[z0,z1,z858,z3,z4,z5]),(0,[z192,z1,z244,z2,z3,z4]),(0,[z0,z1,z714,z3,z4,z5]),(0,[z0,z1,z2,z3,z859,z5]),(0,[z860,z1,z2,z3,z4,z5]),(0,[z0,z1,z861,z2,z3,z4]),(0,[z130,z0,z1,z749,z4,z5]),(0,[z862,z1,z2,z3,z4,z5])],[(0,[z0,z121,z2,z3,z567,z123]),(0,[z130,z284,z1,z38,z4,z5])],[(0,[z736,z61,z2,z3,z4,z5]),(0,[z22,z736,z2,z3,z4,z5]),(0,[z863,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z864,z5]),(0,[z0,z784,z1,z2,z3,z5])]],
   [[(0,[z89,z0,z539,z2,z3,z5]),(0,[z1,z2,z3,z35,z4,z728]),(0,[z0,z1,z2,z865,z4,z5]),(0,[z24,z0,z2,z25,z4,z5])],[(0,[z0,z1,z2,z3,z866,z5]),(0,[z0,z1,z2,z3,z138,z4]),(0,[z0,z1,z2,z3,z4,z867]),(0,[z0,z1,z2,z3,z4,z868]),(0,[z0,z84,z2,z3,z85,z5]),(0,[z0,z196,z2,z3,z338,z5])],[(0,[z0,z1,z2,z869,z3,z4]),(0,[z0,z1,z870,z3,z4,z5]),(0,[z0,z2,z3,z871,z4,z5]),(0,[z0,z1,z2,z872,z4,z5]),(0,[z0,z131,z161,z3,z4,z5]),(0,[z130,z0,z1,z38,z4,z500]),(0,[z0,z1,z2,z383,z752,z5])],[(0,[z0,z873,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z138,z511]),(0,[z130,z0,z41,z131,z4,z5]),(0,[z0,z874,z2,z3,z4,z5])]],
   [[(0,[z151,z1,z63,z3,z4,z5]),(0,[z0,z875,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z147,z511]),(0,[z58,z0,z1,z2,z3,z511]),(0,[z876,z1,z2,z3,z4,z5])],[(0,[z72,z1,z2,z3,z4,z5]),(0,[z89,z0,z1,z2,z3,z138]),(0,[z31,z237,z0,z1,z4,z5]),(0,[z214,z0,z131,z3,z4,z5]),(0,[z877,z1,z2,z3,z4,z5]),(0,[z0,z1,z878,z3,z4,z5]),(0,[z879,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z338,z5]),(0,[z880,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z881,z4]),(0,[z882,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z883,z4]),(0,[z15,z1,z2,z3,z87,z5]),(0,[z884,z1,z2,z3,z4,z5]),(0,[z89,z101,z1,z2,z3,z5]),(0,[z143,z0,z1,z2,z752,z5]),(0,[z885,z1,z2,z3,z4,z5])]],
   [[(0,[z103,z1,z2,z837,z4,z5]),(0,[z0,z1,z2,z3,z4,z886])],[(0,[z0,z1,z887,z3,z4,z5]),(0,[z114,z1,z2,z3,z5,z50]),(0,[z0,z131,z236,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z888]),(0,[z0,z1,z2,z3,z4,z889]),(0,[z80,z101,z1,z2,z3,z4])],[(0,[z890,z0,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z891,z5]),(0,[z1,z2,z3,z4,z728,z5]),(0,[z0,z892,z1,z2,z3,z4]),(0,[z1,z2,z3,z893,z4,z5]),(0,[z894,z1,z2,z3,z4,z5]),(0,[z214,z24,z0,z1,z4,z5]),(0,[z895,z0,z1,z3,z4,z5]),(0,[z0,z1,z264,z412,z4,z5]),(0,[z57,z245,z1,z2,z3,z4]),(1,[z0,z1,z3,z766,z5])],[(0,[z1,z2,z3,z81,z4,z6]),(0,[z0,z1,z2,z3,z4,z896]),(0,[z0,z1,z2,z3,z4,z897]),(0,[z898,z1,z2,z3,z4,z5]),(0,[z899,z1,z2,z3,z4,z5]),(0,[z900,z1,z2,z3,z4,z5]),(0,[z72,z1,z2,z3,z4,z123])]],
   [[(0,[z0,z1,z3,z901,z4,z5]),(0,[z0,z1,z2,z3,z4,z902]),(0,[z0,z1,z2,z903,z4,z5]),(0,[z0,z1,z2,z904,z4,z5]),(0,[z24,z0,z161,z2,z4,z5]),(0,[z0,z1,z2,z3,z211,z4]),(0,[z80,z1,z2,z3,z171,z4]),(0,[z57,z0,z2,z3,z147,z4]),(0,[z0,z121,z2,z3,z350,z4])],[(0,[z0,z1,z2,z3,z4,z905]),(0,[z0,z2,z3,z906,z4,z5]),(0,[z110,z196,z2,z3,z4,z5]),(0,[z130,z0,z196,z38,z4,z5]),(0,[z907,z1,z2,z3,z4,z5])],[(0,[z0,z736,z2,z3,z4,z5]),(0,[z19,z1,z204,z2,z3,z5]),(0,[z0,z1,z2,z3,z908,z5]),(1,[z0,z1,z2,z752,z5])],[(0,[z0,z1,z2,z3,z4,z909]),(0,[z0,z1,z2,z3,z910,z4]),(0,[z90,z0,z1,z2,z3,z686]),(0,[z0,z560,z2,z3,z4,z123]),(0,[z245,z1,z2,z3,z35,z4]),(0,[z89,z150,z1,z2,z3,z5]),(0,[z130,z0,z1,z38,z197,z5]),(0,[z0,z911,z2,z3,z4,z5]),(0,[z912,z1,z2,z3,z4,z5]),(0,[z414,z0,z1,z2,z86,z4]),(0,[z0,z1,z2,z723,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z913,z5])],[(0,[z0,z1,z2,z3,z914,z5]),(0,[z110,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z915,z4,z5]),(0,[z0,z1,z2,z3,z4,z916]),(0,[z245,z1,z2,z3,z4,z193]),(0,[z1,z2,z3,z917,z4,z5])],[(0,[z23,z1,z77,z2,z3,z4]),(0,[z0,z1,z2,z3,z918,z5]),(0,[z0,z1,z919,z3,z4,z5]),(0,[z101,z84,z2,z3,z85,z5]),(0,[z0,z1,z2,z3,z122,z193]),(0,[z0,z784,z1,z2,z3,z122]),(0,[z58,z0,z784,z1,z2,z3])],[(1,[z0,z2,z756,z4,z5]),(0,[z0,z2,z3,z735,z4,z5]),(0,[z1,z2,z3,z920,z4,z5]),(0,[z0,z1,z37,z749,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z921]),(0,[z0,z1,z2,z3,z4,z922]),(0,[z188,z72,z1,z2,z3,z4]),(0,[z192,z0,z1,z2,z3,z511]),(0,[z1,z2,z3,z923,z4,z5]),(0,[z0,z1,z2,z3,z766,z5]),(0,[z924,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z925,z4,z5]),(0,[z441,z0,z1,z2,z3,z193]),(0,[z0,z1,z2,z926,z4,z5]),(0,[z90,z0,z1,z2,z3,z76]),(0,[z0,z1,z2,z3,z122,z76])],[(0,[z19,z77,z61,z2,z3,z4]),(0,[z0,z1,z2,z927,z4,z5]),(0,[z1,z2,z3,z4,z718,z5]),(0,[z237,z0,z161,z2,z4,z5]),(0,[z0,z1,z2,z3,z928,z5]),(0,[z0,z1,z2,z3,z929,z4]),(0,[z930,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z567,z181,z5]),(0,[z0,z931,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z932,z3,z4,z5]),(0,[z0,z1,z2,z86,z723,z4])],[(0,[z102,z1,z2,z837,z4,z5]),(0,[z0,z196,z2,z3,z4,z5]),(0,[z0,z2,z3,z735,z4,z123])],[(0,[z933,z1,z2,z3,z4,z5]),(0,[z150,z58,z1,z2,z3,z5])],[(0,[z0,z1,z2,z934,z3,z5]),(0,[z114,z58,z1,z2,z3,z36]),(0,[z0,z1,z2,z3,z4,z935]),(0,[z0,z131,z714,z3,z4,z5]),(0,[z0,z1,z2,z3,z936,z4])]],
   [[(0,[z31,z0,z161,z3,z4,z5]),(0,[z0,z1,z2,z3,z937,z4]),(0,[z90,z0,z1,z2,z3,z624]),(0,[z58,z72,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z192,z1,z2,z3,z4,z6]),(0,[z0,z84,z2,z3,z779,z5]),(0,[z110,z1,z2,z3,z4,z365]),(0,[z938,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z939]),(0,[z151,z1,z614,z3,z4,z5]),(0,[z0,z1,z2,z3,z567,z36]),(0,[z57,z0,z75,z2,z3,z4]),(0,[z0,z161,z2,z3,z4,z500])],[(0,[z15,z1,z2,z3,z718,z5]),(0,[z0,z1,z2,z3,z4,z940]),(0,[z1,z2,z3,z941,z4,z5]),(0,[z56,z0,z1,z3,z727,z4])]],
   [[(0,[z262,z1,z2,z3,z87,z4]),(0,[z0,z1,z2,z942,z4,z5]),(0,[z943,z0,z1,z2,z3,z4]),(0,[z110,z1,z2,z3,z197,z5]),(0,[z0,z1,z2,z752,z5,z12]),(0,[z0,z1,z2,z119,z4,z40]),(0,[z0,z1,z2,z723,z3,z4])],[(0,[z944,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z945,z4]),(0,[z946,z1,z2,z3,z4,z5]),(0,[z118,z0,z1,z2,z86,z4])],[(0,[z0,z1,z2,z3,z947,z5]),(0,[z0,z1,z2,z3,z948,z5]),(0,[z0,z84,z2,z3,z85,z76]),(0,[z0,z1,z2,z3,z4,z949])],[(0,[z0,z1,z2,z3,z4,z42]),(0,[z950,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z951]),(1,[z0,z2,z3,z735,z4]),(0,[z952,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z953]),(0,[z0,z1,z2,z3,z954,z5]),(0,[z1,z2,z3,z686,z4,z36]),(1,[z0,z1,z749,z4,z5]),(0,[z0,z1,z2,z11,z5,z12])],[(0,[z102,z1,z2,z360,z4,z5]),(0,[z0,z2,z714,z3,z4,z5]),(0,[z1,z2,z3,z955,z4,z5]),(0,[z956,z1,z2,z3,z4,z5]),(0,[z957,z1,z2,z3,z4,z5]),(0,[z0,z196,z2,z3,z4,z365]),(0,[z958,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z959]),(0,[z1,z2,z3,z81,z718,z5]),(0,[z262,z0,z1,z2,z3,z511]),(0,[z0,z1,z2,z17,z4,z5]),(0,[z214,z0,z161,z3,z4,z5]),(0,[z0,z1,z749,z38,z4,z5]),(0,[z0,z1,z67,z3,z727,z4])],[(0,[z0,z1,z2,z3,z960,z5]),(0,[z15,z0,z1,z2,z3,z83]),(0,[z0,z1,z2,z3,z122,z511]),(0,[z237,z0,z131,z1,z4,z5]),(0,[z0,z1,z961,z3,z4,z5]),(0,[z0,z2,z3,z756,z4,z5])]],
   [[(0,[z962,z0,z1,z2,z3,z5]),(0,[z1,z2,z315,z837,z4,z5]),(0,[z0,z84,z1,z2,z3,z138]),(0,[z0,z1,z2,z3,z963,z4]),(0,[z0,z1,z2,z3,z964,z4]),(0,[z90,z0,z1,z2,z3,z567]),(0,[z965,z0,z1,z2,z3,z5])],[(0,[z19,z204,z61,z2,z3,z5]),(0,[z15,z1,z2,z3,z81,z16]),(0,[z150,z84,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z365])],[(0,[z0,z1,z2,z3,z4,z966]),(0,[z0,z1,z2,z3,z967,z5]),(0,[z0,z1,z968,z3,z4,z5]),(0,[z0,z1,z2,z3,z969,z4]),(0,[z0,z131,z3,z323,z4,z5]),(0,[z214,z0,z41,z1,z4,z5]),(0,[z0,z2,z3,z194,z779,z5])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z970,z2,z3,z5]),(0,[z468,z1,z74,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z971]),(0,[z972,z0,z1,z2,z4,z5]),(0,[z0,z2,z373,z756,z4,z5]),(0,[z130,z0,z1,z38,z338,z5])]],
   [[(0,[z114,z1,z462,z2,z3,z5]),(0,[z973,z1,z2,z3,z4,z5]),(0,[z121,z2,z3,z181,z4,z123]),(0,[z284,z1,z2,z3,z4,z500]),(0,[z0,z1,z2,z3,z197,z5]),(0,[z0,z1,z2,z3,z974,z5])],[(0,[z1,z760,z74,z3,z4,z5]),(0,[z114,z0,z1,z2,z3,z76]),(0,[z0,z1,z2,z752,z3,z5])],[(0,[z101,z1,z2,z3,z4,z5]),(0,[z0,z41,z2,z756,z4,z5]),(0,[z0,z1,z2,z3,z4,z975]),(0,[z0,z1,z2,z749,z4,z5]),(0,[z0,z1,z3,z727,z4,z68]),(0,[z58,z90,z72,z1,z2,z3])],[(0,[z0,z1,z2,z3,z976,z5]),(0,[z0,z1,z2,z3,z977,z5]),(0,[z0,z1,z2,z3,z436,z4]),(0,[z80,z0,z1,z2,z3,z4]),(0,[z978,z0,z1,z2,z3,z4]),(0,[z284,z161,z2,z3,z4,z5])]],
   [[(0,[z114,z14,z1,z2,z3,z5]),(0,[z245,z121,z1,z2,z3,z4]),(0,[z561,z1,z2,z3,z181,z5]),(0,[z979,z1,z2,z3,z4,z5]),(0,[z0,z784,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z980]),(0,[z1,z2,z837,z206,z4,z5]),(0,[z981,z1,z2,z3,z4,z5]),(0,[z982,z1,z2,z3,z4,z5])],[(0,[z983,z0,z1,z2,z3,z4]),(1,[z1,z2,z837,z4,z5]),(0,[z0,z1,z2,z984,z4,z5]),(0,[z31,z0,z17,z32,z4,z5])],[(0,[z0,z985,z2,z3,z4,z5]),(0,[z0,z1,z2,z986,z3,z4]),(0,[z150,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z987,z5]),(0,[z0,z1,z2,z988,z4,z5]),(0,[z80,z0,z84,z2,z3,z85]),(0,[z233,z0,z1,z3,z39,z4])]],
   [[(0,[z62,z0,z1,z2,z3,z4]),(0,[z0,z989,z2,z3,z4,z5]),(0,[z188,z1,z2,z3,z4,z36]),(0,[z0,z1,z2,z3,z990,z5]),(0,[z214,z0,z32,z3,z4,z5]),(0,[z0,z84,z2,z3,z211,z85])],[(0,[z0,z1,z2,z3,z991,z5]),(0,[z992,z1,z2,z3,z4,z5]),(0,[z993,z1,z2,z3,z4,z5]),(0,[z0,z1,z67,z3,z4,z68])],[(0,[z0,z1,z2,z994,z4,z5]),(0,[z995,z0,z1,z3,z4,z5]),(0,[z0,z41,z2,z124,z4,z5]),(0,[z0,z1,z3,z295,z766,z5])],[(0,[z0,z1,z2,z3,z4,z996]),(0,[z73,z1,z74,z3,z4,z5]),(0,[z262,z386,z1,z2,z3,z35]),(0,[z353,z0,z2,z3,z147,z4]),(0,[z245,z1,z2,z3,z567,z5]),(0,[z0,z376,z2,z3,z147,z4])]],
   [[(0,[z0,z1,z77,z2,z3,z4]),(0,[z0,z1,z2,z3,z997,z5]),(0,[z114,z1,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z65,z193]),(0,[z262,z386,z1,z2,z3,z5]),(0,[z262,z699,z1,z2,z3,z4]),(0,[z0,z1,z264,z37,z4,z5]),(0,[z0,z1,z2,z3,z197,z365]),(0,[z370,z0,z1,z2,z3,z193])],[(0,[z19,z386,z1,z2,z3,z5]),(0,[z0,z121,z638,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z998]),(1,[z0,z2,z3,z779,z5]),(0,[z999,z1,z2,z3,z4,z5]),(0,[z0,z121,z2,z3,z4,z123]),(0,[z0,z1000,z2,z3,z4,z5]),(0,[z0,z2,z3,z1001,z4,z5]),(0,[z0,z1,z26,z3,z27,z5]),(0,[z0,z1,z493,z3,z27,z5])],[(0,[z0,z1,z2,z3,z1002,z5]),(0,[z0,z1,z2,z3,z4,z1003]),(0,[z0,z1,z1004,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1005]),(0,[z0,z2,z3,z779,z85,z5])]],
   [[(0,[z0,z41,z2,z373,z4,z5]),(0,[z0,z1,z2,z3,z567,z193]),(1,[z0,z1,z3,z727,z4]),(0,[z1006,z1,z2,z3,z4,z5])],[(0,[z0,z1,z26,z3,z766,z5])],[(0,[z0,z1,z204,z77,z2,z3]),(0,[z188,z23,z1,z2,z3,z4]),(0,[z1,z2,z3,z81,z4,z16]),(0,[z262,z72,z1,z2,z3,z4]),(0,[z1007,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1008,z4]),(0,[z0,z1,z2,z3,z4,z76]),(0,[z1009,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z1010,z4,z5]),(0,[z1,z2,z3,z718,z5,z50]),(0,[z0,z1,z2,z3,z1011,z5]),(0,[z0,z131,z115,z3,z4,z5]),(0,[z0,z1,z2,z3,z567,z76])]]]

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
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 560).take 442) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1002)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [560, 442] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 96).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 96).take 32).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [96, 32] = true :=
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

end PEqualNP.Outside.L_meta_42544

theorem PEqualNP.Outside.L_meta_42544 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276812992 * 2 ^ 32 + 4241029248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276812992 * 2 ^ 32 + 4241029248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_42544.solve