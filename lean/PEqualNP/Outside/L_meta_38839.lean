import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38839

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
  Nat.testBit (4276808928 * 2 ^ 32 + 4274056384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x08116ce4711e1e65#64 ++ 0x21022d9c8e23c3cc#64 ++ 0x8833fde4f13e3e67#64 ++ 0xd1067fbc9e27c7cc#64 : BitVec 256),
   (0x0044e02d014282a8#64 ++ 0x40089c05a0285055#64 ++ 0xf8cce27f01c7c7ff#64 ++ 0xbf199c4fe038f8ff#64 : BitVec 256),
   (0x030b0302b6056851#64 ++ 0x8061606056c0ad0a#64 ++ 0xbf0f0387fe07f87f#64 ++ 0x77e1e070ffc0ff0f#64 : BitVec 256),
   (0x05b003d00aa87506#64 ++ 0x00b6007a01550ea0#64 ++ 0xfff003f81ff87f86#64 ++ 0xfffe007f03ff0ff0#64 : BitVec 256),
   (0x16efb4001df78000#64 ++ 0x02ddf68003bef000#64 ++ 0xd7fffc001fff8005#64 ++ 0xfaffff8003fff000#64 : BitVec 256),
   (0x27fedbffc0000000#64 ++ 0x04ffdb7ff8000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 2]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [13, 7]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0xf8cce27f01c7c7ff 0xbf199c4fe038f8ff

def z1 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0xbf0f0387fe07f87f 0x77e1e070ffc0ff0f

def z2 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xfff003f81ff87f86 0xfffe007f03ff0ff0

def z3 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x8833fde4f13e3e67 0xd1067fbc9e27c7cc

def z4 : W := mkw 0x0db10fd07abc7d47 0x21b621fa0f578fa8 0xfff31ff8fff87f86 0xfffe63ff1fff0ff0

def z5 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xd7fffc001fff8005 0xfaffff8003fff000

def z6 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z7 : W := mkw 0x001048e440081404 0x0002091c88010280 0x8833fde4f1383e07 0xd1067fbc9e2707c0

def z8 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0xfffffffffff87f87 0xffffffffffff0ff0

def z9 : W := mkw 0x000000000aa87506 0x0000000001550ea0 0x180000001ff87f84 0x0300000003ff0ff0

def z10 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x08000000113e3e64 0x010000000227c7cc

def z11 : W := mkw 0x100124001df78000 0x0200248003bef000 0x9033fc001fff8005 0xd2067f8003fff000

def z12 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x073ffc001e3f8001 0x40e7ff8003c7f000

def z13 : W := mkw 0x05f4e3fd0beaf7ae 0x40be9c7fa17d5ef5 0xfffce3ff1fffffff 0xffff9c7fe3ffffff

def z14 : W := mkw 0x08106ce4411a1624 0x21020d9c882342c4 0x0030fc6001380600 0x80061f8c002700c0

def z15 : W := mkw 0x0855eced715e9eed 0x610abd9dae2bd3dd 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z16 : W := mkw 0x21104bffc00002a8 0x4422097ff8000055 0x280003ffe00047fa 0x0500007ffc0008ff

def z17 : W := mkw 0x001048e440000000 0x0002091c88000000 0x8033fde4e0000003 0xd0067fbc9c000000

def z18 : W := mkw 0x16ee90000ce18000 0x02ddd200019c3000 0x57cc00000ec18000 0x2af9800001d83000

def z19 : W := mkw 0x0855ece4715e9e65 0x210abd9c8e2bd3cc 0xd8fffde4f1ffbe67 0xfb1fffbc9e3ff7cc

def z20 : W := mkw 0x0044a00001428000 0x0008940000285000 0xd0cce00001c78005 0xba199c000038f000

def z21 : W := mkw 0x16ab14001cb50000 0x02d562800396a000 0x07331c001e380000 0x40e6638003c70000

def z22 : W := mkw 0x16eff42d1df782a8 0x42ddfe85a3bef055 0xfffffe7f1fffc7ff 0xffffffcfe3fff8ff

def z23 : W := mkw 0x07bb03d2bead7d57 0x80f7607a57d5afaa 0xffff03ffffffffff 0xffffe07fffffffff

def z24 : W := mkw 0x030a030280000000 0x0061406050000000 0xa70f0387e0000003 0x74e1e070fc000000

def z25 : W := mkw 0x100124001df78000 0x0200248003bef000 0x100000001fff8004 0x0200000003fff000

def z26 : W := mkw 0x1efffce47dff9e65 0x23dfff9c8fbff3cc 0xdffffde4ffffbe67 0xfbffffbc9ffff7cc

def z27 : W := mkw 0x05a003100aa87506 0x00b4006201550ea0 0x7fc002181ff87f84 0x2ff8004303ff0ff0

def z28 : W := mkw 0x24f4d8fd40000000 0x049e9b1fa8000000 0x40f0fc7800000000 0x881e1f8f00000000

def z29 : W := mkw 0x27ffdbfff6056851 0x84fffb7ffec0ad0a 0xfffffffffe07f87f 0xffffffffffc0ff0f

def z30 : W := mkw 0x001000c000081404 0x0002001800010280 0x883001e011383e06 0xd106003c022707c0

def z31 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0x000ffc07e0000001 0x0001ff80fc000000

def z32 : W := mkw 0x030a030282006000 0x0061406050400c00 0xbf0f0387fe007807 0x77e1e070ffc00f00

def z33 : W := mkw 0x001048e440000000 0x0002091c88000000 0x000001e4e0000002 0x0000003c9c000000

def z34 : W := mkw 0x04b000d008a81506 0x0096001a011502a0 0xf8f0027801f84786 0xbf1e004f003f08f0

def z35 : W := mkw 0x16efb4091df78088 0x42ddf68123bef011 0xf7fffe1b1fffc19d 0xfeffffc363fff833

def z36 : W := mkw 0x06eef02d014282a8 0x40ddde05a0285055 0xfffffe7f01c7c7ff 0xffffffcfe038f8ff

def z37 : W := mkw 0x27ba1bd2c0000000 0x04f7437a58000000 0x07331d80e0000000 0x40e663b01c000000

def z38 : W := mkw 0x0001240011160000 0x000024800222c000 0x8033fc00113e0005 0xd0067f800227c000

def z39 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xbf3003801e387806 0x77e6007003c70f00

def z40 : W := mkw 0x21100bd2c0000000 0x0422017a58000000 0x00000180e0000000 0x000000301c000000

def z41 : W := mkw 0x05b103d03aac7d47 0x00b6207a07558fa8 0xfff303fcfffe7fe7 0xfffe607f9fffcffc

def z42 : W := mkw 0x0001000030040841 0x0000200006008108 0x88030184f0063867 0x510060309e00c70c

def z43 : W := mkw 0x0054e0ed014a96ac 0x400a9c1da02952d5 0xf8fce3ff11ffffff 0xff1f9c7fe23fffff

def z44 : W := mkw 0x26eed82fc0000000 0x04dddb05f8000000 0xc7fffc07e0000001 0xf8ffff80fc000000

def z45 : W := mkw 0x034ec32f80000000 0x0069d865f0000000 0xe7cfe3ffe0000003 0xfcf9fc7ffc000000

def z46 : W := mkw 0x17ffb7d01ffff506 0x02fff6fa03fffea0 0xfffffff81fffff87 0xffffffff03fffff0

def z47 : W := mkw 0x0044e02d0beaf7ae 0x40089c05a17d5ef5 0xf8cce27f1fffffff 0xbf199c4fe3ffffff

def z48 : W := mkw 0x08110cc0701c1c45 0x210221980e038388 0x00331d80f0383800 0x400663b01e070700

def z49 : W := mkw 0x0044c02d00000000 0x00089805a0000000 0xe0cce27f00000003 0xbc199c4fe0000000

def z50 : W := mkw 0x16efb4001df782a8 0x42ddf68003bef055 0xdffffc001fffc7fd 0xfbffff8003fff8ff

def z51 : W := mkw 0x09104bf462087f67 0x2122097e8c410fec 0x280003fce0007fe2 0x0500007f9c000ffc

def z52 : W := mkw 0x0db16ff47bbe7f67 0x21b62dfe8f77cfec 0xfff3fffcfffe7fe7 0xfffe7fff9fffcffc

def z53 : W := mkw 0x05b04bf440000000 0x00b6097e88000000 0xe7f3fffce0000003 0xfcfe7fff9c000000

def z54 : W := mkw 0x020b0002b6056851 0x8041600056c0ad0a 0x180f0007fe07f87d 0x0301e000ffc0ff0f

def z55 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z56 : W := mkw 0x00002000014282a8 0x4000040000285055 0x0000000000078078 0x000000000000f00f

def z57 : W := mkw 0x0044800900408088 0x4008900120081011 0x70cc021b00c1c198 0x2e19804360183833

def z58 : W := mkw 0x21104bffc0000000 0x0422097ff8000000 0x200003ffe0000002 0x0400007ffc000000

def z59 : W := mkw 0x07bb03d2b6056851 0x80f7607a56c0ad0a 0xffff03fffe07f87f 0xffffe07fffc0ff0f

def z60 : W := mkw 0x011003c002087404 0x0022007800410e80 0xbf3003e01f387e06 0xf7e6007c03e70fc0

def z61 : W := mkw 0x011003d002087506 0x0022007a00410ea0 0x280003f800007f82 0x0500007f00000ff0

def z62 : W := mkw 0x04b000c008a81404 0x0096001801150280 0xdff001e01ff83e06 0xfbfe003c03ff07c0

def z63 : W := mkw 0x0000602d014282a8 0x40000c05a0285055 0x3800027f01c7c7fe 0x0700004fe038f8ff

def z64 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xfffffe071fffc07f 0xffffffc0e3fff80f

def z65 : W := mkw 0x034fe32fb747eaf9 0xc069fc65f6e8fd5f 0xffcfe3ffffc7ffff 0xfff9fc7ffff8ffff

def z66 : W := mkw 0x224ef82fc14282a8 0x4449df05f8285055 0x000ffc07e0078079 0x0001ff80fc00f00f

def z67 : W := mkw 0x0b1b6fe6f71f7e75 0xa1636dfcdee3efce 0xbf3fffe7ff3ffe7f 0xf7e7fffcffe7ffcf

def z68 : W := mkw 0x100124003ff7e851 0x8200248007fefd0a 0x180000001ffff87c 0x0300000003ffff0f

def z69 : W := mkw 0x124fb4001df78000 0x0249f68003bef000 0x100ffc001fff8005 0x0201ff8003fff000

def z70 : W := mkw 0x34f4fcfd49f28000 0x069e9f9fa93e5000 0x40f0fc7801f80000 0x881e1f8f003f0000

def z71 : W := mkw 0x37ee931b8ce18000 0x06fdd263719c3000 0x77cc021b0ec18000 0x2ef9804361d83000

def z72 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x073001801e383800 0x40e6003003c70700

def z73 : W := mkw 0x031a4be6c0000000 0x0063497cd8000000 0xa73fffe7e0000003 0xf4e7fffcfc000000

def z74 : W := mkw 0x04b000d008a81506 0x0096001a011502a0 0xd7f000781ff80784 0xfafe000f03ff00f0

def z75 : W := mkw 0x0001000036056851 0x8000200006c0ad0a 0x180000001e07f87c 0x0300000003c0ff0f

def z76 : W := mkw 0x05b003d000000000 0x00b6007a00000000 0xe7f003f800000002 0xfcfe007f00000000

def z77 : W := mkw 0x030b0302b0040841 0x0061606056008108 0xaf0f0387f0063867 0x75e1e070fe00c70c

def z78 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x40c0e07801c00780 0x88181c0f003800f0

def z79 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800018010003806 0x5100003002000700

def z80 : W := mkw 0x17efb7001ff7e000 0x02fdf6e003fefc00 0xffffff801ffff807 0xfffffff003ffff00

def z81 : W := mkw 0x06ee900000000000 0x00ddd20000000000 0xc7fffc0000000001 0xf8ffff8000000000

def z82 : W := mkw 0x27ba1bd2caa87506 0x04f7437a59550ea0 0x07331d80fe383800 0x40e663b01fc70700

def z83 : W := mkw 0x14a124001df78000 0x0294248003bef000 0xd7f000001fff8004 0xfafe000003fff000

def z84 : W := mkw 0x0044a00901428088 0x4008940120285011 0xf0cce21b01c7c19d 0xbe199c436038f833

def z85 : W := mkw 0x0000402400000000 0x0000080480000000 0x8000e06400000003 0x90001c0c80000000

def z86 : W := mkw 0x27fedbffc0408088 0x44ffdb7ff8081011 0xf7ffffffe0c1c19b 0xfefffffffc183833

def z87 : W := mkw 0x011003d2a2087d57 0x8022007a54410faa 0x280003ffe0007ffa 0x0500007ffc000fff

def z88 : W := mkw 0x27ffdbfff4050851 0x84fffb7ffe80a10a 0xe7ffffffe007807b 0xfcfffffffc00f00f

def z89 : W := mkw 0x0000000022006851 0x8000000004400d0a 0x0800000000007878 0x0100000000000f0f

def z90 : W := mkw 0x0000000000000000 0x0000000000000000 0xb80c02070007c07f 0x37018040e000f80f

def z91 : W := mkw 0x17eff72fbff7eaf9 0xc2fdfee5f7fefd5f 0xffffffffffffffff 0xffffffffffffffff

def z92 : W := mkw 0x27bb1bd2f6056851 0x84f7637a5ec0ad0a 0xbf3f1f87fe07f87f 0x77e7e3f0ffc0ff0f

def z93 : W := mkw 0x0045e02d31468ae9 0x4008bc05a628d15d 0xf8cfe3fff1c7ffff 0xff19fc7ffe38ffff

def z94 : W := mkw 0x37feffffc9f28000 0x06ffdffff93e5000 0xe7ffffffe1f80003 0xfcfffffffc3f0000

def z95 : W := mkw 0x24b018d040000000 0x0496031a08000000 0x00301c0000000000 0x0006038000000000

def z96 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x370f0383fe01f818 0x66e1e0707fc03f03

def z97 : W := mkw 0x0054c8ed40000000 0x000a991da8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z98 : W := mkw 0x134fb702b757e851 0x8269f6e056eafd0a 0xbf0fff87fe07f87f 0x77e1fff0ffc0ff0f

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0xf8c0027801c04786 0xbf18004f003808f0

def z100 : W := mkw 0x04b000d008a81506 0x0096001a011502a0 0x40f0007801f80780 0x881e000f003f00f0

def z101 : W := mkw 0x030a030280000000 0x0061406050000000 0x270c020300000000 0x24e1804060000000

def z102 : W := mkw 0x0854eced415a96ac 0x610a9d9da82b52d5 0xf8fcfe7f01ffc7ff 0xbf1f9fcfe03ff8ff

def z103 : W := mkw 0x0b1b6fe6f11e1e65 0x21636dfcde23c3cc 0xaf3fffe7f13e3e67 0xf5e7fffcfe27c7cc

def z104 : W := mkw 0x27fefbffcbeaf7ae 0x44ffdf7ff97d5ef5 0xffffffffffffffff 0xffffffffffffffff

def z105 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x2f030387fe00787a 0x45e06070ffc00f0f

def z106 : W := mkw 0x0100030002006000 0x0020006000400c00 0xbf0003801e007806 0x77e0007003c00f00

def z107 : W := mkw 0x27fedbffc2006000 0x04ffdb7ff8400c00 0xfffffffffe007807 0xffffffffffc00f00

def z108 : W := mkw 0x020b0002b4050851 0x804160005680a10a 0x880f0187f007b87f 0x5101e030fe00f70f

def z109 : W := mkw 0x2ffffffff11e1e65 0x25fffffffe23c3cc 0xeffffffff13e3e67 0xfdfffffffe27c7cc

def z110 : W := mkw 0x17fff7fd1ffff7ae 0x42fffeffa3fffef5 0xffffffff1fffffff 0xffffffffe3ffffff

def z111 : W := mkw 0x16aa10000ca10000 0x02d5420001942000 0x070000000e000000 0x00e0000001c00000

def z112 : W := mkw 0x024fe02d154782a8 0x4049fc05a2a8f055 0xffcfe27f1fc7c7ff 0xfff9fc4fe3f8f8ff

def z113 : W := mkw 0x05b003d2aaa87d57 0x80b6007a55550faa 0xfff003fffff87ffe 0xfffe007fffff0fff

def z114 : W := mkw 0x0100031002006102 0x0020006200400c20 0x2000021800004180 0x0400004300000830

def z115 : W := mkw 0x124fb40015578000 0x0249f68002aaf000 0x000ffc0000078001 0x0001ff800000f000

def z116 : W := mkw 0x06ee900008a00000 0x00ddd20001140000 0xd7fffc001ff80005 0xfaffff8003ff0000

def z117 : W := mkw 0x2044d82d40000000 0x04089b05a8000000 0x0000fc0000000000 0x00001f8000000000

def z118 : W := mkw 0x0845e42d315e9eed 0x6108bc85a62bd3dd 0xf8cce27f11ffffff 0xbf199c4fe23fffff

def z119 : W := mkw 0x06ef900014050000 0x00ddf2000280a000 0xd7fffc001e078005 0xfaffff8003c0f000

def z120 : W := mkw 0x05a003100aa06102 0x00b4006201540c20 0x77c002180ec04180 0x2ef8004301d80830

def z121 : W := mkw 0x37ffffffddf78000 0x06fffffffbbef000 0xf7ffffffffff8007 0xfefffffffffff000

def z122 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xfffffe781fffc787 0xffffffcf03fff8f0

def z123 : W := mkw 0x1ffffff47fffff67 0x23fffffe8fffffec 0xfffffffcffffffe7 0xffffffff9ffffffc

def z124 : W := mkw 0x01000302a2006851 0x8020006054400d0a 0xbf000387fe00787e 0x77e00070ffc00f0f

def z125 : W := mkw 0x29104bffe0081e65 0x2522097ffc0103cc 0x280003ffe0003e62 0x0500007ffc0007cc

def z126 : W := mkw 0x020b0002b4050851 0x804160005680a10a 0xb80f0207e007c07f 0x3701e040fc00f80f

def z127 : W := mkw 0x0000000000408088 0x4000000000081011 0x1000000000c1c198 0x0200000000183833

def z128 : W := mkw 0x08112cc0711e1c45 0x210225980e23c388 0x8033fd80f13e3805 0xd0067fb01e27c700

def z129 : W := mkw 0x00002000014282a8 0x4000040000285055 0x1800000001c7c7fc 0x030000000038f8ff

def z130 : W := mkw 0x0a1b6ce6f51f1e75 0xa1436d9cdea3e3ce 0x883ffde7f13fbe7f 0xd107ffbcfe27f7cf

def z131 : W := mkw 0x010003000aa87506 0x0020006001550ea0 0xbf0003801ff87f86 0x77e0007003ff0ff0

def z132 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0xb83fffe7f13ffe7f 0xf707fffcfe27ffcf

def z133 : W := mkw 0x020b0002b4050851 0x804160005680a10a 0x000f0007e0078079 0x0001e000fc00f00f

def z134 : W := mkw 0x0000000000000000 0x0000000000000000 0x280002070000407a 0x05000040e000080f

def z135 : W := mkw 0x011003d002087506 0x0022007a00410ea0 0x0000018000003800 0x0000003000000700

def z136 : W := mkw 0x16efb4001ffff506 0x02ddf68003fffea0 0xdffffc001fffff85 0xfbffff8003fffff0

def z137 : W := mkw 0x27ee931b80000000 0x04fdd26370000000 0x67cc021b00000000 0x2cf9804360000000

def z138 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0xffcf03ffffc7ffff 0xfff9e07ffff8ffff

def z139 : W := mkw 0x1045a4001df78000 0x0208b48003bef000 0xd0cce0001fff8005 0xba199c0003fff000

def z140 : W := mkw 0x08016c2471160a61 0x21002d848e22c14c 0x0003fc04e0060061 0x00007f809c00c00c

def z141 : W := mkw 0x21104bffc0000000 0x0422097ff8000000 0xa033ffffe0000003 0xd4067ffffc000000

def z142 : W := mkw 0x030b030294050000 0x006160605280a000 0xb70f0387fe078007 0x76e1e070ffc0f000

def z143 : W := mkw 0x0b1b6fe6f71f7e75 0xa1636dfcdee3efce 0x8f33fde4ff3e3e67 0xd1e67fbc9fe7c7cc

def z144 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xffffffffe1c04787 0xfffffffffc3808f0

def z145 : W := mkw 0x030a030286016010 0x8061406050c02c02 0x370c02030e01c018 0x26e1804061c03803

def z146 : W := mkw 0x17ef9302bee5e851 0x82fdf26057dcbd0a 0xffcf0387fec7f87f 0x7ff9e070ffd8ff0f

def z147 : W := mkw 0x06ee900000000000 0x00ddd20000000000 0x47cc000000000000 0x28f9800000000000

def z148 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x47f001f81ff83f80 0xc8fe003f03ff07f0

def z149 : W := mkw 0x17efb7029df78000 0x02fdf6e053bef000 0xf7ffff87ffff8007 0xfefffff0fffff000

def z150 : W := mkw 0x0044c02d00000000 0x00089805a0000000 0xf8cce27f0007c07f 0xbf199c4fe000f80f

def z151 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x57cffc000ec78001 0x2af9ff8001d8f000

def z152 : W := mkw 0x080124003bbe7f67 0x210024800777cfec 0x180000001ffe7fe4 0x0300000003ffcffc

def z153 : W := mkw 0x224ef82fc14282a8 0x4449df05f8285055 0xf8cffe7fe1c7c7ff 0xbf19ffcffc38f8ff

def z154 : W := mkw 0x0100030002006000 0x0020006000400c00 0xffc003f81fc07f86 0xfff8007f03f80ff0

def z155 : W := mkw 0x27fefbffc1428000 0x04ffdf7ff8285000 0xf7ffffffe1c78007 0xfefffffffc38f000

def z156 : W := mkw 0x08116ce4715e9eed 0x61022d9c8e2bd3dd 0x9833fde4f1ffffff 0xd3067fbc9e3fffff

def z157 : W := mkw 0x17ab1702beb56851 0x82f562e057d6ad0a 0xbf3f1f87fe3ff87f 0x77e7e3f0ffc7ff0f

def z158 : W := mkw 0x07bb03d2bead7d57 0x80f7607a57d5afaa 0x07330180fe383800 0x40e660301fc70700

def z159 : W := mkw 0x17ee93028ee1e010 0x82fdd26051dc3c02 0x77cc02030ec1c018 0x2ef9804061d83803

def z160 : W := mkw 0x17efb702bff7e851 0x82fdf6e057fefd0a 0xffffff87fffff87f 0xfffffff0ffffff0f

def z161 : W := mkw 0x27fe93db8aa87506 0x04ffd27b71550ea0 0xfffc03fb1ff87f86 0xffff807f63ff0ff0

def z162 : W := mkw 0x07ef9302b6056851 0x80fdf26056c0ad0a 0xffffff87fe07f87f 0xfffffff0ffc0ff0f

def z163 : W := mkw 0x27fedbffc00002a8 0x44ffdb7ff8000055 0xefffffffe00047fb 0xfdfffffffc0008ff

def z164 : W := mkw 0x27ef931bb6056851 0x84fdf26376c0ad0a 0xffcf039ffe07f87f 0x7ff9e073ffc0ff0f

def z165 : W := mkw 0x01010302b6056851 0x8020206056c0ad0a 0x38000387fe07f87e 0x07000070ffc0ff0f

def z166 : W := mkw 0x0044c02d000002a8 0x40089805a0000055 0xe8cce27f000047fb 0xbd199c4fe00008ff

def z167 : W := mkw 0x0fbb6ff6ffbf7f77 0xa1f76dfedff7efee 0xffffffffffffffff 0xffffffffffffffff

def z168 : W := mkw 0x24e4901900000000 0x049c920320000000 0x40c0001800000000 0x0818000300000000

def z169 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x58c0e07801c7c7fc 0x8b181c0f0038f8ff

def z170 : W := mkw 0x05b003d00aa06102 0x00b6007a01540c20 0xf7f003f80ec04182 0xfefe007f01d80830

def z171 : W := mkw 0x0000602401020220 0x00000c0480204044 0x8800e06401060667 0x91001c0c8020c0cc

def z172 : W := mkw 0x08010400301c1c45 0x2100208006038388 0x0000000010383800 0x0000000002070700

def z173 : W := mkw 0x08114ce4701c1c45 0x2102299c8e038388 0x8033fde4f0383803 0xd0067fbc9e070700

def z174 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x70cce21f00c7c1f9 0x2e199c43e018f83f

def z175 : W := mkw 0x16eff42d1df782a8 0x42ddfe85a3bef055 0xd7fffc781fff8785 0xfaffff8f03fff0f0

def z176 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x000ce00700078079 0x00019c00e000f00f

def z177 : W := mkw 0x034f830bb645e8d9 0xc069f06176c8bd1b 0xffcf039ffec7f9ff 0x7ff9e073ffd8ff3f

def z178 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x70cce27b01c1c798 0xae199c4f603838f3

def z179 : W := mkw 0x14e4b40009f28000 0x029c9680013e5000 0x40f0fc0001f80000 0x881e1f80003f0000

def z180 : W := mkw 0x08116ce4771f7e75 0xa1022d9c8ee3efce 0x9833fde4ff3ffe7f 0xd3067fbc9fe7ffcf

def z181 : W := mkw 0x04a0000008a00000 0x0094000001140000 0xd7f000001ff80004 0xfafe000003ff0000

def z182 : W := mkw 0x27fedbffc8a00000 0x04ffdb7ff9140000 0xf7fffffffff80007 0xfeffffffffff0000

def z183 : W := mkw 0x124ff42d155782a8 0x4249fe85a2aaf055 0xf8cffe7f01c7c7ff 0xbf19ffcfe038f8ff

def z184 : W := mkw 0x21104bffc2087506 0x0422097ff8410ea0 0x280003ffe0007f82 0x0500007ffc000ff0

def z185 : W := mkw 0x16ab34001db70000 0x02d5668003b6e000 0x8733fc001f3e0005 0xd0e67f8003e7c000

def z186 : W := mkw 0x0855eced711e1e65 0x210abd9dae23c3cc 0xe8fffffff13e3e67 0xfd1ffffffe27c7cc

def z187 : W := mkw 0x16ef94001cb50000 0x02ddf2800396a000 0xc7fffc001e380001 0xf8ffff8003c70000

def z188 : W := mkw 0x16eeb4000df38000 0x02ddd68001be7000 0x57fcfc000ff98000 0xaaff9f8001ff3000

def z189 : W := mkw 0x0000000000081404 0x0000000000010280 0x0800000011383e04 0x01000000022707c0

def z190 : W := mkw 0x0000482440000000 0x0000090488000000 0x0003fc04e0000001 0x00007f809c000000

def z191 : W := mkw 0x0800000020081e65 0x21000000040103cc 0x0800000000003e60 0x01000000000007cc

def z192 : W := mkw 0x27fefbffc14282a8 0x44ffdf7ff8285055 0xffffffffe1c7c7ff 0xfffffffffc38f8ff

def z193 : W := mkw 0x020b000014050000 0x004160000280a000 0x970f00001e078005 0x72e1e00003c0f000

def z194 : W := mkw 0x17ab1702beb56851 0x82f562e057d6ad0a 0x07331d80fe383800 0x40e663b01fc70700

def z195 : W := mkw 0x08106ce4411a1624 0x21020d9c882342c4 0x8033fde4e1380603 0xd0067fbc9c2700c0

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000001e000004 0x72e0000003c00000

def z197 : W := mkw 0x020a000000000000 0x0041400000000000 0x870f000000000001 0x70e1e00000000000

def z198 : W := mkw 0x0001000030040841 0x0000200006008108 0x0800000010063864 0x010000000200c70c

def z199 : W := mkw 0x0000402d00000000 0x00000805a0000000 0x2000027f00000002 0x0400004fe0000000

def z200 : W := mkw 0x37ffbfd2ddf78000 0x06fff7fa5bbef000 0xd7fffd80ffff8005 0xfaffffb01ffff000

def z201 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x77f002780ff84780 0xaefe004f01ff08f0

def z202 : W := mkw 0x05b003d002006000 0x00b6007a00400c00 0xfff003f81e007806 0xfffe007f03c00f00

def z203 : W := mkw 0x0b1b0fc2f61d7c55 0xa16361f85ec3af8a 0xbf3f1f87fe3ff87f 0x77e7e3f0ffc7ff0f

def z204 : W := mkw 0x37ffffffd5578000 0x06fffffffaaaf000 0xe7ffffffe0078003 0xfcfffffffc00f000

def z205 : W := mkw 0x17bb17d01ebd7506 0x02f762fa03d7aea0 0x07331d801e383800 0x40e663b003c70700

def z206 : W := mkw 0x011003d002087506 0x0022007a00410ea0 0xa83003f811387f86 0xd506007f02270ff0

def z207 : W := mkw 0x0000000002006000 0x0000000000400c00 0x180000001e007804 0x0300000003c00f00

def z208 : W := mkw 0x0000000020000841 0x0000000004000108 0x08000184e0003862 0x010000309c00070c

def z209 : W := mkw 0x01000302a2006851 0x8020006054400d0a 0x28000387e000787a 0x05000070fc000f0f

def z210 : W := mkw 0x081048e460081e65 0x2102091c8c0103cc 0x883001e4f1383e66 0xd106003c9e2707cc

def z211 : W := mkw 0x0001240031160841 0x000024800622c108 0x8833fd84f13e3867 0xd1067fb09e27c70c

def z212 : W := mkw 0x0b1b4be6f60d7e75 0xa163697cdec1afce 0xbf0f03e7fe07fe7f 0x77e1e07cffc0ffcf

def z213 : W := mkw 0x08002400011a1624 0x21000480002342c4 0x0000000001380600 0x00000000002700c0

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x180000000007c07c 0x030000000000f80f

def z215 : W := mkw 0x27fefbffc1020220 0x04ffdf7ff8204044 0xefffffffe1060667 0xfdfffffffc20c0cc

def z216 : W := mkw 0x0000000000000000 0x0000000000000000 0x900c000000078005 0x320180000000f000

def z217 : W := mkw 0x05a003000aa06000 0x00b4006001540c00 0xfff003801ff87806 0xfffe007003ff0f00

def z218 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x3f0c02031e07f87c 0x27e1804063c0ff0f

def z219 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x07030180fe003800 0x40e060301fc00700

def z220 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xfffc03ff1fffffff 0xffff807fe3ffffff

def z221 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x40cce07f01c787f9 0x88199c0fe038f0ff

def z222 : W := mkw 0x05a003100aa06102 0x00b4006201540c20 0xf7f002181ff84184 0xfefe004303ff0830

def z223 : W := mkw 0x00006024014282a8 0x40000c0480285055 0x9800e06401c7c7ff 0x93001c0c8038f8ff

def z224 : W := mkw 0x0cb06cf449ba1726 0x21960d9e893742e4 0x40f0fc7801f80780 0x881e1f8f003f00f0

def z225 : W := mkw 0x05b003d000081404 0x00b6007a00010280 0xeff003f811383e06 0xfdfe007f022707c0

def z226 : W := mkw 0x16eff42d1df782a8 0x42ddfe85a3bef055 0xd7fffc071fff807d 0xfaffff80e3fff00f

def z227 : W := mkw 0x1efffce45dff9624 0x23dfff9c8bbff2c4 0xd7fffc601fff8605 0xfaffff8c03fff0c0

def z228 : W := mkw 0x234edb2fc0000000 0x0469db65f8000000 0xa70fff87e0000003 0x74e1fff0fc000000

def z229 : W := mkw 0x0000200001020220 0x0000040000204044 0x0800000001060664 0x010000000020c0cc

def z230 : W := mkw 0x14e4b40009f28000 0x029c9680013e5000 0xd7f0fc001ff80004 0xfafe1f8003ff0000

def z231 : W := mkw 0x04f4e0fd09ea97ae 0x409e9c1fa13d52f5 0xf8fce27f01ffc7ff 0xbf1f9c4fe03ff8ff

def z232 : W := mkw 0x001148e470040841 0x0002291c8e008108 0x8833fde4f0063867 0xd1067fbc9e00c70c

def z233 : W := mkw 0x16fffce45df78000 0x02dfff9c8bbef000 0xd7fffde4ffff8007 0xfaffffbc9ffff000

def z234 : W := mkw 0x1eeffc247df78a61 0x23ddff848fbef14c 0xd7fffc04ffff8065 0xfaffff809ffff00c

def z235 : W := mkw 0x08116ce47bbe7f67 0x21022d9c8f77cfec 0x9833fde4fffe7fe7 0xd3067fbc9fffcffc

def z236 : W := mkw 0x2a5ffceff11e1e65 0x254bff9dfe23c3cc 0x883ffde7f13e3e67 0xd107ffbcfe27c7cc

def z237 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0c0000001c00004 0xba18000000380000

def z238 : W := mkw 0x001048e440000000 0x0002091c88000000 0x0030fc6000000000 0x80061f8c00000000

def z239 : W := mkw 0x1001240015578000 0x0200248002aaf000 0x0000000000078000 0x000000000000f000

def z240 : W := mkw 0x05f4e3fd014282a8 0x40be9c7fa0285055 0xfffce3ff01c7c7ff 0xffff9c7fe038f8ff

def z241 : W := mkw 0x001000c000081404 0x0002001800010280 0x0030018010383800 0x4006003002070700

def z242 : W := mkw 0x034fc32fb6056851 0x8069f865f6c0ad0a 0xffcfe3fffe07f87f 0xfff9fc7fffc0ff0f

def z243 : W := mkw 0x04b000d008a81506 0x0096001a011502a0 0xc8f001f811f83f86 0xd91e003f023f07f0

def z244 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x0033fde0f1383e00 0xc0067fbc1e2707c0

def z245 : W := mkw 0x36effc2fddf78000 0x06ddff85fbbef000 0xd7fffc07ffff8005 0xfaffff80fffff000

def z246 : W := mkw 0x2100031b80000000 0x0420006370000000 0x2000021b00000000 0x0400004360000000

def z247 : W := mkw 0x0044c02d00000000 0x00089805a0000000 0x000ce00700000001 0x00019c00e0000000

def z248 : W := mkw 0x07bb03d2bead7d57 0x80f7607a57d5afaa 0xbf3f0387fe3ff87f 0x77e7e070ffc7ff0f

def z249 : W := mkw 0x07bb03d01ead7506 0x00f7607a03d5aea0 0xffff03f81fffff87 0xffffe07f03fffff0

def z250 : W := mkw 0x0045e02d3747eaf9 0xc008bc05a6e8fd5f 0xf8cce27f1fc7ffff 0xbf199c4fe3f8ffff

def z251 : W := mkw 0x27eedb3fc0000000 0x04fddb67f8000000 0x67cffe1fe0000001 0x2cf9ffc3fc000000

def z252 : W := mkw 0x27fedbffcaa06102 0x04ffdb7ff9540c20 0xf7ffffffeec04183 0xfefffffffdd80830

def z253 : W := mkw 0x06efb40011160000 0x00ddf6800222c000 0xc7fffc00113e0005 0xf8ffff800227c000

def z254 : W := mkw 0x030b6326b7076a71 0x80616c64d6e0ed4e 0xbf0fe3e7ff07fe7f 0xf7e1fc7cffe0ffcf

def z255 : W := mkw 0x0100030000000000 0x0020006000000000 0xa700038000000002 0x74e0007000000000

def z256 : W := mkw 0x020b240015170000 0x0041648002a2e000 0x973ffc001f3f8005 0xf2e7ff8003e7f000

def z257 : W := mkw 0x220a1802c0000000 0x0441430058000000 0x00031c00e0000000 0x000063801c000000

def z258 : W := mkw 0x16ef94001cf58000 0x02ddf280039eb000 0x57ff1c001ef98000 0x6affe38003df3000

def z259 : W := mkw 0x16ab34001df78000 0x02d5668003bef000 0x17331c001fff8004 0x42e6638003fff000

def z260 : W := mkw 0x25b04bffc0000000 0x04b6097ff8000000 0xe7f003ffe0000002 0xfcfe007ffc000000

def z261 : W := mkw 0x081048e460081e65 0x2102091c8c0103cc 0x080001e4e0003e62 0x0100003c9c0007cc

def z262 : W := mkw 0x0001040010140000 0x0000208002028000 0x00331c0010380000 0x4006638002070000

def z263 : W := mkw 0x08116ced711e1eed 0x61022d9dae23c3dd 0xa833fffff13e7fff 0xd5067ffffe27cfff

def z264 : W := mkw 0x14e4f42d09f282a8 0x429c9e85a13e5055 0xf8fcfe7f01ffc7ff 0xbf1f9fcfe03ff8ff

def z265 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0xf8f3fffcf1fe7fe7 0xff1e7fff9e3fcffc

def z266 : W := mkw 0x0044a00001428000 0x0008940000285000 0xf8cce27801c7c787 0xbf199c4f0038f8f0

def z267 : W := mkw 0x224e900b80000000 0x0449d20170000000 0x000c000300000000 0x0001800060000000

def z268 : W := mkw 0x18116ce47dff9e65 0x23022d9c8fbff3cc 0x9833fde4ffffbe67 0xd3067fbc9ffff7cc

def z269 : W := mkw 0x030a030280000000 0x0061406050000000 0xbf0f0387e007c07f 0x77e1e070fc00f80f

def z270 : W := mkw 0x08006c2441120220 0x21000d8488224044 0x0000fc0000000000 0x00001f8000000000

def z271 : W := mkw 0x04a000000aa87506 0x0094000001550ea0 0xdff000001ff87f84 0xfbfe000003ff0ff0

def z272 : W := mkw 0x27fedbffc6016010 0x84ffdb7ff8c02c02 0xf7ffffffee01c01b 0xfefffffffdc03803

def z273 : W := mkw 0x0000000000000000 0x0000000000000000 0x1800000001c04784 0x03000000003808f0

def z274 : W := mkw 0x011043fd020877ae 0x4022087fa0410ef5 0x280003ff00007ffa 0x0500007fe0000fff

def z275 : W := mkw 0x0845ec2d71568ae9 0x6108bd85ae2ad15d 0xf8cffe7fe1c7c7ff 0xbf19ffcffc38f8ff

def z276 : W := mkw 0x001124c0111e1404 0x000224980223c280 0x8833fde0113e3e07 0xd1067fbc0227c7c0

def z277 : W := mkw 0x030a030286016010 0x8061406050c02c02 0xb70f0387ee01c01b 0x76e1e070fdc03803

def z278 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x8833fc00113e3e65 0xd1067f800227c7cc

def z279 : W := mkw 0x0000402d000002a8 0x40000805a0000055 0x2800027f000047fa 0x0500004fe00008ff

def z280 : W := mkw 0x27fe9bd2c0000000 0x04ffd37a58000000 0xc7fffd80e0000001 0xf8ffffb01c000000

def z281 : W := mkw 0x17bb17d01ebd7506 0x02f762fa03d7aea0 0xfff31ff81ff87f86 0xfffe63ff03ff0ff0

def z282 : W := mkw 0x0044800900408088 0x4008900120081011 0xf8cc027b01c1c79e 0xbf19804f603838f3

def z283 : W := mkw 0x0cb16ce479be1e65 0x21962d9c8f37c3cc 0xdff3fde4fffe3e67 0xfbfe7fbc9fffc7cc

def z284 : W := mkw 0x0854e8ed614a9eed 0x610a9d1dac2953dd 0xf8cce3ffe1c7ffff 0xbf199c7ffc38ffff

def z285 : W := mkw 0x020a000280000000 0x0041400050000000 0x000f0007e0000001 0x0001e000fc000000

def z286 : W := mkw 0x0000000000000000 0x0000000000000000 0x70c0021800c04180 0x2e18004300180830

def z287 : W := mkw 0x16efb402bdf78851 0x82ddf68057bef10a 0xd7fffc07ffff807d 0xfaffff80fffff00f

def z288 : W := mkw 0x08012400371f7e75 0xa100248006e3efce 0x180000001f3ffe7c 0x0300000003e7ffcf

def z289 : W := mkw 0x05a003100aa06102 0x00b4006201540c20 0x070000000e000000 0x00e0000001c00000

def z290 : W := mkw 0x011003d002087506 0x0022007a00410ea0 0xbf0003f81e007f86 0x77e0007f03c00ff0

def z291 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0xe0cffe7fe0000003 0xbc19ffcffc000000

def z292 : W := mkw 0x011003d002087506 0x0022007a00410ea0 0xf8c003f801c07f86 0xbf18007f00380ff0

def z293 : W := mkw 0x081124c0311e1e65 0x210224980623c3cc 0x883001e0113e3e66 0xd106003c0227c7cc

def z294 : W := mkw 0x0044a00001428000 0x0008940000285000 0x000ce00000078001 0x00019c000000f000

def z295 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x88030184f13e3e67 0x510060309e27c7cc

def z296 : W := mkw 0x024e900000000000 0x0049d20000000000 0x000ffc0000000001 0x0001ff8000000000

def z297 : W := mkw 0x011003d00aa87506 0x0022007a01550ea0 0x380003f81ff87f86 0x0700007f03ff0ff0

def z298 : W := mkw 0x020b0002b4050851 0x804160005680a10a 0x00030000e0000000 0x000060001c000000

def z299 : W := mkw 0x0a1b6ce4751f1e65 0x21436d9c8ea3e3cc 0x9f3ffde4ff3fbe67 0xf3e7ffbc9fe7f7cc

def z300 : W := mkw 0x120b140014150000 0x024162800282a000 0x00031c0000000000 0x0000638000000000

def z301 : W := mkw 0x034ee32f814282a8 0x4069dc65f0285055 0xffcfe3ffe1c7c7ff 0xfff9fc7ffc38f8ff

def z302 : W := mkw 0x07ab0312bea56953 0x80f5606257d4ad2a 0xffcf039ffec7f9ff 0x7ff9e073ffd8ff3f

def z303 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x0033fd84f03e3861 0x40067fb09e07c70c

def z304 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0xe7fffffffe383803 0xfcffffffffc70700

def z305 : W := mkw 0x124fb402b5578851 0x8249f68056aaf10a 0x000ffc07e0078079 0x0001ff80fc00f00f

def z306 : W := mkw 0x21104bffe2006851 0x8422097ffc400d0a 0x280003ffe000787a 0x0500007ffc000f0f

def z307 : W := mkw 0x2ffedbffe0081e65 0x25ffdb7ffc0103cc 0xefffffffe0003e63 0xfdfffffffc0007cc

def z308 : W := mkw 0x0001000030040841 0x0000200006008108 0x00030180f0003800 0x400060301e000700

def z309 : W := mkw 0x27ba5bf6c0000000 0x04f74b7ed8000000 0x8733fde4e0000003 0xd0e67fbc9c000000

def z310 : W := mkw 0x04a1240019b60000 0x009424800336c000 0xd7f3fc001ffe0005 0xfafe7f8003ffc000

def z311 : W := mkw 0x24f4d8fd48a81506 0x049e9b1fa91502a0 0x40f0fc7801f80780 0x881e1f8f003f00f0

def z312 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x073ffd87e0000001 0x40e7ffb0fc000000

def z313 : W := mkw 0x05b023d00beaf7ae 0x40b6047a017d5ef5 0xfff003f81ffffffe 0xfffe007f03ffffff

def z314 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xe7f003f81e383802 0xfcfe007f03c70700

def z315 : W := mkw 0x081048ed60081eed 0x6102091dac0103dd 0x280003ffe0007ffa 0x0500007ffc000fff

def z316 : W := mkw 0x09104be6e2087e75 0xa122097cdc410fce 0x280003e7e0007e7a 0x0500007cfc000fcf

def z317 : W := mkw 0x04a0000000000000 0x0094000000000000 0xc7f0000000000000 0xf8fe000000000000

def z318 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0xd0cce00701c7807d 0xba199c00e038f00f

def z319 : W := mkw 0x0044c02d00408088 0x40089805a0081011 0xf0cce27f00c1c19b 0xbe199c4fe0183833

def z320 : W := mkw 0x17efb702bff7e851 0x82fdf6e057fefd0a 0xd7fffd80ffffb805 0xfaffffb01ffff700

def z321 : W := mkw 0x001060e4010a1624 0x00020c1c802142c4 0x8830e1e4113e3e67 0xd1061c3c8227c7cc

def z322 : W := mkw 0x37ffffffddf782a8 0x46fffffffbbef055 0xffffffffffffc7ff 0xfffffffffffff8ff

def z323 : W := mkw 0x06eeb00001428000 0x00ddd60000285000 0xd7fffc0001c78005 0xfaffff800038f000

def z324 : W := mkw 0x0001000034050851 0x800020000680a10a 0x0000000000078078 0x000000000000f00f

def z325 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xffffffffe007c07f 0xfffffffffc00f80f

def z326 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x68f003f801f87f82 0x8d1e007f003f0ff0

def z327 : W := mkw 0x130b2702bff7e851 0x826164e057fefd0a 0xbf0f0387fffff87f 0x77e1e070ffffff0f

def z328 : W := mkw 0x0000200001020000 0x0000040000204000 0x8000e00001060005 0x90001c000020c000

def z329 : W := mkw 0x16efb4003ff7e851 0x82ddf68007fefd0a 0xdffffc001ffff87d 0xfbffff8003ffff0f

def z330 : W := mkw 0x0044c02d00000000 0x00089805a0000000 0xf8cce27f01c04787 0xbf199c4fe03808f0

def z331 : W := mkw 0x0000000000000000 0x0000000000000000 0x40c0007801c00780 0x8818000f003800f0

def z332 : W := mkw 0x2ffffffff15e9eed 0x65fffffffe2bd3dd 0xfffffffff1ffffff 0xfffffffffe3fffff

def z333 : W := mkw 0x020a000284010010 0x8041400050802002 0x000c000300018018 0x0001800060003003

def z334 : W := mkw 0x020b0002b4050851 0x804160005680a10a 0x970f0007fe07807d 0x72e1e000ffc0f00f

def z335 : W := mkw 0x27fedbffc2087506 0x04ffdb7ff8410ea0 0xefffffffe0007f83 0xfdfffffffc000ff0

def z336 : W := mkw 0x17ffb7d01ffff506 0x02fff6fa03fffea0 0xd7fffd801fffb805 0xfaffffb003fff700

def z337 : W := mkw 0x0000240001120000 0x0000048000224000 0x0030fc0001380000 0x80061f8000270000

def z338 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x57cc00001fff8004 0x2af9800003fff000

def z339 : W := mkw 0x0001642411160220 0x00002c848222c044 0x8833fc64113e0667 0xd1067f8c8227c0cc

def z340 : W := mkw 0x0801240031160a61 0x210024800622c14c 0x0000000000060060 0x000000000000c00c

def z341 : W := mkw 0x100124001ffff506 0x0200248003fffea0 0x180000001fffff84 0x0300000003fffff0

def z342 : W := mkw 0x020b000034050841 0x004160000680a108 0x9f0f0184fe07b867 0x73e1e0309fc0f70c

def z343 : W := mkw 0x05f4e3fd0beaf7ae 0x40be9c7fa17d5ef5 0xfff0e3f81ff87f86 0xfffe1c7f03ff0ff0

def z344 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x970f0180fe07b805 0x72e1e0301fc0f700

def z345 : W := mkw 0x001000d000081506 0x0002001a000102a0 0x0000007800000780 0x0000000f000000f0

def z346 : W := mkw 0x0001240011160000 0x000024800222c000 0x0003fc0000060001 0x00007f800000c000

def z347 : W := mkw 0x1cf5fce479fe9e65 0x239ebf9c8f3fd3cc 0xc8f3fde4f1fe3e67 0xd91e7fbc9e3fc7cc

def z348 : W := mkw 0x030b030296056010 0x8061606052c0ac02 0xb70f02031e07c01d 0x76e1e04063c0f803

def z349 : W := mkw 0x0045a40011568000 0x0008b480022ad000 0xd0fffc0011ff8005 0xfa1fff80023ff000

def z350 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x8f030184fe063867 0x51e060309fc0c70c

def z351 : W := mkw 0x0100030280000000 0x0020006050000000 0x20000387e0000002 0x04000070fc000000

def z352 : W := mkw 0x0001240011160000 0x000024800222c000 0x00000000113e0004 0x000000000227c000

def z353 : W := mkw 0x16ee90000ce18000 0x02ddd200019c3000 0xd7fffc000ec18001 0xfaffff8001d83000

def z354 : W := mkw 0x030a0302a2006851 0x8061406054400d0a 0xaf0f0387e000787b 0x75e1e070fc000f0f

def z355 : W := mkw 0x01000302a2006851 0x8020006054400d0a 0x00000180e0003800 0x000000301c000700

def z356 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x8f3001e01f383e06 0xd1e6003c03e707c0

def z357 : W := mkw 0x08114ce4701c1e65 0x2102299c8e0383cc 0x08331de4f0383e62 0x410663bc9e0707cc

def z358 : W := mkw 0x0101030036056851 0x8020206006c0ad0a 0xbf0003801e07f87e 0x77e0007003c0ff0f

def z359 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x2f3003f81e387f82 0x45e6007f03c70ff0

def z360 : W := mkw 0x05f4c3fd0aa87506 0x00be987fa1550ea0 0xfffce3ff1ff87f87 0xffff9c7fe3ff0ff0

def z361 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x180ce00701c7c7fd 0x03019c00e038f8ff

def z362 : W := mkw 0x00002000014282a8 0x4000040000285055 0xf8c0027801c7c7fe 0xbf18004f0038f8ff

def z363 : W := mkw 0x16ab14001cb50000 0x02d562800396a000 0xd7f31c001ff80004 0xfafe638003ff0000

def z364 : W := mkw 0x06eed02d00000000 0x00ddda05a0000000 0xe7fffe7f00000003 0xfcffffcfe0000000

def z365 : W := mkw 0x06fed8e440000000 0x00dfdb1c88000000 0xc7fffde4e0000003 0xf8ffffbc9c000000

def z366 : W := mkw 0x05b063f40baa7726 0x00b60c7e81754ee4 0xfff0e3fc1ffe7fe7 0xfffe1c7f83ffcffc

def z367 : W := mkw 0x27fedbffc8a81506 0x04ffdb7ff91502a0 0xe7ffffffe1f80783 0xfcfffffffc3f00f0

def z368 : W := mkw 0x081148e4700c1e65 0x2102291c8e0183cc 0x880301e4f0063e67 0x5100603c9e00c7cc

def z369 : W := mkw 0x0000602401020220 0x00000c0480204044 0xf8c0e27c01c647e7 0xbf181c4f8038c8fc

def z370 : W := mkw 0x180124003dff9e65 0x2300248007bff3cc 0x180000001fffbe64 0x0300000003fff7cc

def z371 : W := mkw 0x030a030286016010 0x8061406050c02c02 0x070000000e000000 0x00e0000001c00000

def z372 : W := mkw 0x1044b40001528000 0x02089680002a5000 0x0000fc0000000000 0x00001f8000000000

def z373 : W := mkw 0x231b4bfff6056851 0x8463697ffec0ad0a 0xbf0f03fffe07f87f 0x77e1e07fffc0ff0f

def z374 : W := mkw 0x27eed33f80000000 0x04fdda67f0000000 0xe7cce27f00000003 0xbcf99c4fe0000000

def z375 : W := mkw 0x201048fd40000000 0x0402091fa8000000 0x0000007800000000 0x0000000f00000000

def z376 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x7fc003f80ec07f82 0x2ff8007f01d80ff0

def z377 : W := mkw 0x27fedbffc0081404 0x04ffdb7ff8010280 0xeffffffff1383e07 0xfdfffffffe2707c0

def z378 : W := mkw 0x030b2702b7176851 0x806164e056e2ed0a 0xbf3fff87ff3ff87f 0xf7e7fff0ffe7ff0f

def z379 : W := mkw 0x0044800900408088 0x4008900120081011 0x40c0001800c00180 0x0818000300180030

def z380 : W := mkw 0x0144e32d0342e2a8 0x40289c65a0685c55 0xffcce3ff1fc7ffff 0xfff99c7fe3f8ffff

def z381 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x280f0387e007f87b 0x0501e070fc00ff0f

def z382 : W := mkw 0x1000240009f28000 0x02000480013e5000 0x0000000001f80000 0x00000000003f0000

def z383 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x080001e4f13e3e66 0x0100003c9e27c7cc

def z384 : W := mkw 0x14a0140008b00000 0x0294028001160000 0x00301c0000380000 0x0006038000070000

def z385 : W := mkw 0x0855eced715e9eed 0x610abd9dae2bd3dd 0x883ffde7f13fbe7f 0xd107ffbcfe27f7cf

def z386 : W := mkw 0x2ffffffffbbe7f67 0x25ffffffff77cfec 0xfffffffffffe7fe7 0xffffffffffffcffc

def z387 : W := mkw 0x081048e460081e65 0x2102091c8c0103cc 0x8833fde4e0003e63 0xd1067fbc9c0007cc

def z388 : W := mkw 0x0001602431060a61 0x00002c048620c14c 0x8803e1e4f1063e67 0xd1007c3c9e20c7cc

def z389 : W := mkw 0x16eff4241df78220 0x02ddfe8483bef044 0xdffffc641fff8667 0xfbffff8c83fff0cc

def z390 : W := mkw 0x0000000900000088 0x4000000120000011 0x2000021b00004198 0x0400004360000833

def z391 : W := mkw 0x05b003d000000000 0x00b6007a00000000 0xfff003f801c04786 0xfffe007f003808f0

def z392 : W := mkw 0x37efb71b9df78000 0x06fdf6e373bef000 0xf7fffe1b1fff8005 0xfeffffc363fff000

def z393 : W := mkw 0x08012400315e9eed 0x61002480062bd3dd 0x1800000011fffffc 0x03000000023fffff

def z394 : W := mkw 0x01000302a2006851 0x8020006054400d0a 0xb80c0387e007f87f 0x37018070fc00ff0f

def z395 : W := mkw 0x0000602401020220 0x00000c0480204044 0x0000e06001000600 0x80001c0c002000c0

def z396 : W := mkw 0x2cf5fcfd711e1e65 0x259ebf9fae23c3cc 0xc8f3fdfcf13e3e67 0xd91e7fbf9e27c7cc

def z397 : W := mkw 0x0044800000408000 0x0008900000081000 0x50cc000000c18000 0x2a19800000183000

def z398 : W := mkw 0x05a003100aa06102 0x00b4006201540c20 0xffc003981ec07986 0x7ff8007303d80f30

def z399 : W := mkw 0x00116ce451160000 0x00022d9c8a22c000 0x8033fde4f13e0007 0xd0067fbc9e27c000

def z400 : W := mkw 0x034fe32fb747eaf9 0xc069fc65f6e8fd5f 0xbf0fe387fe07f87f 0x77e1fc70ffc0ff0f

def z401 : W := mkw 0x27fefbffc14282a8 0x44ffdf7ff8285055 0xe7ffffffe007807b 0xfcfffffffc00f00f

def z402 : W := mkw 0x0001000030040841 0x0000200006008108 0xb80f0387f007f87f 0x7701e070fe00ff0f

def z403 : W := mkw 0x030a030286016010 0x8061406050c02c02 0xbf0c02070e07c07f 0x37e18040e1c0f80f

def z404 : W := mkw 0x07fe93d00aa87506 0x00ffd27a01550ea0 0xfffffff81ff87f87 0xffffffff03ff0ff0

def z405 : W := mkw 0x011003d000000000 0x0022007a00000000 0x200003f800000002 0x0400007f00000000

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x300c02030001c018 0x2601804060003803

def z407 : W := mkw 0x04b000d008a81506 0x0096001a011502a0 0x0030000000380000 0x0006000000070000

def z408 : W := mkw 0x0df5effd7bfeffef 0x61bebdffaf7fdffd 0xffffffffffffffff 0xffffffffffffffff

def z409 : W := mkw 0x00000000000002a8 0x4000000000000055 0x08000000000047f8 0x01000000000008ff

def z410 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0xf8c0e27801c04786 0xbf181c4f003808f0

def z411 : W := mkw 0x0044a00001428000 0x0008940000285000 0xf8cce20701c7c07f 0xbf199c40e038f80f

def z412 : W := mkw 0x2a4ffc2ff1160a61 0x2549ff85fe22c14c 0x000ffc07e0060061 0x0001ff80fc00c00c

def z413 : W := mkw 0x25b04bffcaa87506 0x04b6097ff9550ea0 0xfff003fffff87f86 0xfffe007fffff0ff0

def z414 : W := mkw 0x06ab00001ca50000 0x00d560000394a000 0xd7ff00001fff8005 0xfaffe00003fff000

def z415 : W := mkw 0x07ba03d28aa87506 0x00f7407a51550ea0 0xffff03fffff87f87 0xffffe07fffff0ff0

def z416 : W := mkw 0x09116ff4731e7f67 0x21222dfe8e63cfec 0xa833fffcf13e7fe7 0xd5067fff9e27cffc

def z417 : W := mkw 0x030a030280000000 0x0061406050000000 0x07030180e0000000 0x40e060301c000000

def z418 : W := mkw 0x0000000000000000 0x0000000000000000 0xf8cc027f01c7c7ff 0xbf19804fe038f8ff

def z419 : W := mkw 0x225ed8efc0000000 0x044bdb1df8000000 0x803ffde7e0000003 0xd007ffbcfc000000

def z420 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0xa70f0387fe003803 0x74e1e070ffc00700

def z421 : W := mkw 0x0db04bf46aa87f67 0x21b6097e8d550fec 0xfff003fcfff87fe6 0xfffe007f9fff0ffc

def z422 : W := mkw 0x16eeb0000de38000 0x02ddd60001bc7000 0xd7cce0000fc78005 0xbaf99c0001f8f000

def z423 : W := mkw 0x27ee931b8aa06102 0x04fdd26371540c20 0x77cc021b0ec04180 0x2ef9804361d80830

def z424 : W := mkw 0x1efffced7dff9eed 0x63dfff9dafbff3dd 0xffffffffffffffff 0xffffffffffffffff

def z425 : W := mkw 0x04a0000008a00000 0x0094000001140000 0xfff002781ff84786 0xfffe004f03ff08f0

def z426 : W := mkw 0x1ebb7ce47dbf1e65 0x23d76f9c8fb7e3cc 0x8f33fde4ff3e3e67 0xd1e67fbc9fe7c7cc

def z427 : W := mkw 0x16eff42d1df78000 0x02ddfe85a3bef000 0xf7fffe7f1fff8007 0xfeffffcfe3fff000

def z428 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x67fcfe7b00000000 0xacff9fcf60000000

def z429 : W := mkw 0x0054e8ed414282a8 0x400a9d1da8285055 0xf8ffffffe1c7c7ff 0xff1ffffffc38f8ff

def z430 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x0000e00000000000 0x00001c0000000000

def z431 : W := mkw 0x0800482460000a61 0x210009048c00014c 0x00000004e0000060 0x000000009c00000c

def z432 : W := mkw 0x26fed8ffc0000000 0x04dfdb1ff8000000 0x40fffc7fe0000001 0x881fff8ffc000000

def z433 : W := mkw 0x235edbffc0000000 0x046bdb7ff8000000 0x200fffffe0000003 0x0401fffffc000000

def z434 : W := mkw 0x27ee931b80000000 0x04fdd26370000000 0xe7fffe1b00000001 0xfcffffc360000000

def z435 : W := mkw 0x05b04bf44aa87506 0x00b6097e89550ea0 0xfff3fffcfff87f87 0xfffe7fff9fff0ff0

def z436 : W := mkw 0x07ab0302bea56851 0x80f5606057d4ad0a 0xffff0387fffff87f 0xffffe070ffffff0f

def z437 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c000700078079 0x00018000e000f00f

def z438 : W := mkw 0x0000402d000002a8 0x40000805a0000055 0x0000007800000780 0x0000000f000000f0

def z439 : W := mkw 0x14e4900008e08000 0x029c9200011c1000 0x40c0000000c00000 0x0818000000180000

def z440 : W := mkw 0x031b03c2b60d7c55 0x8063607856c1af8a 0xbf3f03e7ff3ffe7f 0xf7e7e07cffe7ffcf

def z441 : W := mkw 0x37ffffffdffff506 0x06fffffffbfffea0 0xffffffffffffff87 0xfffffffffffffff0

def z442 : W := mkw 0x0044e02d01428000 0x00089c05a0285000 0xf0cce27f01c78007 0xbe199c4fe038f000

def z443 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0xc8c0e07c01c607e7 0x99181c0f8038c0fc

def z444 : W := mkw 0x16ee90090ce18088 0x42ddd201219c3011 0x77cc021b0ec1c198 0x2ef9804361d83833

def z445 : W := mkw 0x034ee32f8743e2b8 0xc069dc65f0e87c57 0xffcce27f0fc7c7ff 0xbff99c4fe1f8f8ff

def z446 : W := mkw 0x04b000d00aa87506 0x0096001a01550ea0 0x58f000781ff87f84 0x8b1e000f03ff0ff0

def z447 : W := mkw 0x15b127d01ffff506 0x02b624fa03fffea0 0xfff003f81fffff86 0xfffe007f03fffff0

def z448 : W := mkw 0x0001000036056851 0x8000200006c0ad0a 0x98030184fe07f87f 0x530060309fc0ff0f

def z449 : W := mkw 0x1045e42d1df782a8 0x4208bc85a3bef055 0xf8cce27f1fffc7ff 0xbf199c4fe3fff8ff

def z450 : W := mkw 0x16efb4003df78841 0x02ddf68007bef108 0xdffffd84ffffb867 0xfbffffb09ffff70c

def z451 : W := mkw 0x17ffb7d2bffffd57 0x82fff6fa57ffffaa 0xffffffffffffffff 0xffffffffffffffff

def z452 : W := mkw 0x024fe02fb5478af9 0xc049fc05f6a8f15f 0xf8cfe27fe1c7c7ff 0xbf19fc4ffc38f8ff

def z453 : W := mkw 0x0000000006016010 0x8000000000c02c02 0x100000000e01c018 0x0200000001c03803

def z454 : W := mkw 0x0000602d010202a8 0x40000c05a0204055 0xa800e27f010647ff 0x95001c4fe020c8ff

def z455 : W := mkw 0x37ffdfffdcb50000 0x06fffbfffb96a000 0xe7fffffffe380003 0xfcffffffffc70000

def z456 : W := mkw 0x0044800900408088 0x4008900120081011 0xf8cc021f00c7c1ff 0x3f198043e018f83f

def z457 : W := mkw 0x124e900004418000 0x0249d20000883000 0x000c000000018000 0x0001800000003000

def z458 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x1f3001801ff87f84 0x43e6003003ff0ff0

def z459 : W := mkw 0x0044e02401428220 0x00089c0480285044 0xd8cce06401c78667 0xbb199c0c8038f0cc

def z460 : W := mkw 0x001008c040000000 0x0002011808000000 0x00331d80e0000000 0x400663b01c000000

def z461 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x070f0187fe07b879 0x40e1e030ffc0f70f

def z462 : W := mkw 0x27ba1bd2c0000000 0x04f7437a58000000 0xe7f31ff8e0000002 0xfcfe63ff1c000000

def z463 : W := mkw 0x00000002a0000851 0x800000005400010a 0x00000007e0000078 0x00000000fc00000f

def z464 : W := mkw 0x07ba03d28ea97516 0x80f7407a51d52ea2 0xfffc03fb1ff9ff9e 0xffff807f63ff3ff3

def z465 : W := mkw 0x0045e42d115682a8 0x4008bc85a22ad055 0xf8fffe7f11ffc7ff 0xff1fffcfe23ff8ff

def z466 : W := mkw 0x0100432fa2006af9 0xc0200865f4400d5f 0x280003ffe0007ffa 0x0500007ffc000fff

def z467 : W := mkw 0x000000000aa87506 0x0000000001550ea0 0xf8c002781ff87f86 0xbf18004f03ff0ff0

def z468 : W := mkw 0x0000602401020220 0x00000c0480204044 0xb80ce2670107c67f 0xb7019c4ce020f8cf

def z469 : W := mkw 0x37bb1fd2dcb50000 0x06f763fa5b96a000 0x07331d80fe380000 0x40e663b01fc70000

def z470 : W := mkw 0x2ffffffff71f7e75 0xa5fffffffee3efce 0xffffffffff3ffe7f 0xffffffffffe7ffcf

def z471 : W := mkw 0x08110cc0701c1c45 0x210221980e038388 0x88331de0f1383e06 0xd10663bc1e2707c0

def z472 : W := mkw 0x0a0b6c26f5170a71 0xa1416d84dea2e14e 0x000ffc07e0078079 0x0001ff80fc00f00f

def z473 : W := mkw 0x1a4ffc2475578a61 0x2349ff848eaaf14c 0x000ffc04e0078061 0x0001ff809c00f00c

def z474 : W := mkw 0x0b0b6f26f7176a71 0xa1616de4dee2ed4e 0xbf0fff87fe07f87f 0x77e1fff0ffc0ff0f

def z475 : W := mkw 0x1ebb1cc07cbd1c45 0x23d763980f97a388 0x07331d80fe383800 0x40e663b01fc70700

def z476 : W := mkw 0x0044800900408088 0x4008900120081011 0x000c000300018018 0x0001800060003003

def z477 : W := mkw 0x24f4d8fd40000000 0x049e9b1fa8000000 0xc0f3fdfce0000003 0xd81e7fbf9c000000

def z478 : W := mkw 0x05f483d90ae8f58e 0x40be907b215d1eb1 0xfffc03fb1ff9ff9e 0xffff807f63ff3ff3

def z479 : W := mkw 0x0000000000000000 0x0000000000000000 0x80030184e0000003 0x500060309c000000

def z480 : W := mkw 0x14e5b40019f68000 0x029cb680033ed000 0xc0f3fc0011fe0005 0xd81e7f80023fc000

def z481 : W := mkw 0x0855eced715e9eed 0x610abd9dae2bd3dd 0xc8f3fdfcf1fe3fe7 0xd91e7fbf9e3fc7fc

def z482 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0c0027800000002 0xbc18004f00000000

def z483 : W := mkw 0x14e5b4001df78000 0x029cb68003bef000 0x50f0fc001fff8004 0x8a1e1f8003fff000

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0x8033fc0000000001 0xd0067f8000000000

def z485 : W := mkw 0x27ba1bd2c0000000 0x04f7437a58000000 0xa73f1f87e0000003 0x74e7e3f0fc000000

def z486 : W := mkw 0x030b432fb6056af9 0xc0616865f6c0ad5f 0xbf0f03fffe07ffff 0x77e1e07fffc0ffff

def z487 : W := mkw 0x04b000d000000000 0x0096001a00000000 0x40f0007800000000 0x881e000f00000000

def z488 : W := mkw 0x0154e3fd034af7ae 0x402a9c7fa0695ef5 0xf8cce3ff01c7ffff 0xbf199c7fe038ffff

def z489 : W := mkw 0x0044a00001428000 0x0008940000285000 0x40c0e00001c00000 0x88181c0000380000

def z490 : W := mkw 0x27ffdbffd4050000 0x04fffb7ffa80a000 0xf7fffffffe078007 0xfeffffffffc0f000

def z491 : W := mkw 0x024fe02fb5478af9 0xc049fc05f6a8f15f 0x000fe007e0078079 0x0001fc00fc00f00f

def z492 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x0033fc64e13e0661 0x80067f8c9c27c0cc

def z493 : W := mkw 0x2000482fc0000000 0x04000905f8000000 0x00000007e0000000 0x00000000fc000000

def z494 : W := mkw 0x05f4c3fd00000000 0x00be987fa0000000 0xe7fce3ff00000003 0xfcff9c7fe0000000

def z495 : W := mkw 0x124fb40015578000 0x0249f68002aaf000 0x803ffc00113f8005 0xd007ff800227f000

def z496 : W := mkw 0x04f4e0fd09ea97ae 0x409e9c1fa13d52f5 0x40f0e07801f80780 0x881e1c0f003f00f0

def z497 : W := mkw 0x07aa03128ea16112 0x80f5406251d42c22 0x77cc021b0ec1c198 0x2ef9804361d83833

def z498 : W := mkw 0x08110cc0701c1c45 0x210221980e038388 0x88331d84f03e3867 0x510663b09e07c70c

def z499 : W := mkw 0x16ee90000ce18000 0x02ddd200019c3000 0xd7fc00001ff98004 0xfaff800003ff3000

def z500 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x47f3fc001ff80000 0xc8fe7f8003ff0000

def z501 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0xb80ce2070007c07f 0x37019c40e000f80f

def z502 : W := mkw 0x0db10fd07abc7d47 0x21b621fa0f578fa8 0x07331d80fe383800 0x40e663b01fc70700

def z503 : W := mkw 0x0044c02d004082a8 0x40089805a0081055 0x78cc027f00c1c7fa 0x2f19804fe01838ff

def z504 : W := mkw 0x01010302b2046851 0x8020206056408d0a 0xa8030387f006787f 0x55006070fe00cf0f

def z505 : W := mkw 0x020b000014050000 0x004160000280a000 0xbf0f02071e07c07f 0x77e1e040e3c0f80f

def z506 : W := mkw 0x08016c2471160a61 0x21002d848e22c14c 0x8033fc04f13e0065 0xd0067f809e27c00c

def z507 : W := mkw 0x001000c00aa87506 0x0002001801550ea0 0x983001e01ff87f86 0xd306003c03ff0ff0

def z508 : W := mkw 0x020b000036056851 0x8041600006c0ad0a 0x9f0f00001e07f87d 0x73e1e00003c0ff0f

def z509 : W := mkw 0x0000000000000000 0x0000000000000000 0x2800027800004782 0x0500004f000008f0

def z510 : W := mkw 0x0000402d000002a8 0x40000805a0000055 0xb80c027f0007c7ff 0x3701804fe000f8ff

def z511 : W := mkw 0x16eef02d0de382a8 0x42ddde05a1bc7055 0xffcce27f0fc7c7ff 0xbff99c4fe1f8f8ff

def z512 : W := mkw 0x27fffbfff747eaf9 0xc4ffff7ffee8fd5f 0xffffffffffc7ffff 0xfffffffffff8ffff

def z513 : W := mkw 0x05e483190ae0e18a 0x40bc9063215c1c31 0x77cc021b0ec1c198 0x2ef9804361d83833

def z514 : W := mkw 0x020a000004010000 0x0041400000802000 0x170c00000e018000 0x22e1800001c03000

def z515 : W := mkw 0x0100030282006010 0x8020006050400c02 0x2000020300004018 0x0400004060000803

def z516 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x67cc03ffe0000002 0x2cf9807ffc000000

def z517 : W := mkw 0x030b030016056000 0x0061606002c0ac00 0xbf0f03801e07f807 0x77e1e07003c0ff00

def z518 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x0830fc60113e3e64 0x81061f8c0227c7cc

def z519 : W := mkw 0x0001000036056851 0x8000200006c0ad0a 0x000000001e003800 0x0000000003c00700

def z520 : W := mkw 0x081008c060081c45 0x210201180c010388 0x00000180e0003800 0x000000301c000700

def z521 : W := mkw 0x27ee931b80000000 0x04fdd26370000000 0xe7cf039fe0000003 0x7cf9e073fc000000

def z522 : W := mkw 0x08016c24711e1e65 0x21002d848e23c3cc 0x0803fc04f13e3e65 0x01007f809e27c7cc

def z523 : W := mkw 0x37fedbffcce18000 0x06ffdb7ff99c3000 0xf7ffffffeec18003 0xfefffffffdd83000

def z524 : W := mkw 0x1eefb4003dff9e65 0x23ddf68007bff3cc 0xdffffc001fffbe65 0xfbffff8003fff7cc

def z525 : W := mkw 0x26fed8fd40000000 0x04dfdb1fa8000000 0xc7fffc7800000001 0xf8ffff8f00000000

def z526 : W := mkw 0x001000c000000000 0x0002001800000000 0x803001e000000002 0xd006003c00000000

def z527 : W := mkw 0x07fe93d000000000 0x00ffd27a00000000 0xe7fffff800000003 0xfcffffff00000000

def z528 : W := mkw 0x24f4d8fd40000000 0x049e9b1fa8000000 0xe0fcfe7f00000003 0xbc1f9fcfe0000000

def z529 : W := mkw 0x27ffdbfffead7d57 0x84fffb7fffd5afaa 0xffffffffffffffff 0xffffffffffffffff

def z530 : W := mkw 0x0000402d000002a8 0x40000805a0000055 0xf8c0027f01c047fe 0xbf18004fe03808ff

def z531 : W := mkw 0x16efb40015578000 0x02ddf68002aaf000 0xc7fffc0000078001 0xf8ffff800000f000

def z532 : W := mkw 0x234fdb2ff6056851 0x8469fb65fec0ad0a 0xbf0fff87fe07f87f 0x77e1fff0ffc0ff0f

def z533 : W := mkw 0x27ffffffd1160000 0x04fffffffa22c000 0xe7fffffff13e0007 0xfcfffffffe27c000

def z534 : W := mkw 0x07ee930280000000 0x00fdd26050000000 0xe7ffff87e0000003 0xfcfffff0fc000000

def z535 : W := mkw 0x07ba03d280000000 0x00f7407a50000000 0xe7ff03ffe0000003 0xfcffe07ffc000000

def z536 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x880ce0670107867f 0x91019c0ce020f0cf

def z537 : W := mkw 0x14f4b4d009fa9506 0x029e969a013f52a0 0x40f0fc7801f80780 0x881e1f8f003f00f0

def z538 : W := mkw 0x15f4b7d00bfaf506 0x02be96fa017f5ea0 0xfff0fff81ff87f86 0xfffe1fff03ff0ff0

def z539 : W := mkw 0x04e4e02d09e282a8 0x409c9c05a13c5055 0xfffce27f1fffc7ff 0xffff9c4fe3fff8ff

def z540 : W := mkw 0x0000602401020220 0x00000c0480204044 0x0000e00400060061 0x00001c008000c00c

def z541 : W := mkw 0x08016c2471160a61 0x21002d848e22c14c 0x8803fc64e1060667 0x91007f8c9c20c0cc

def z542 : W := mkw 0x100104001cb50000 0x020020800396a000 0x000000001e380000 0x0000000003c70000

def z543 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x370f0207ee07c079 0x26e1e040fdc0f80f

def z544 : W := mkw 0x08016c2471160a61 0x21002d848e22c14c 0x8803fd84f0063867 0x51007fb09e00c70c

def z545 : W := mkw 0x081048e440081624 0x2102091c880102c4 0x0000006000000600 0x0000000c000000c0

def z546 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0xe0cce27f0007807b 0xbc199c4fe000f00f

def z547 : W := mkw 0x27eef33f814282a8 0x44fdde67f0285055 0xffcce27f01c7c7ff 0xbff99c4fe038f8ff

def z548 : W := mkw 0x04e4900000000000 0x009c920000000000 0x40f0fc0000000000 0x881e1f8000000000

def z549 : W := mkw 0x08106ce4611a1e65 0x21020d9c8c2343cc 0x0830fde4e1383e62 0x81061fbc9c2707cc

def z550 : W := mkw 0x05e4e33d0be2e3aa 0x40bc9c67a17c5c75 0xffcce27f0fc7c7ff 0xbff99c4fe1f8f8ff

def z551 : W := mkw 0x0000402d000002a8 0x40000805a0000055 0x0000000700000078 0x00000000e000000f

def z552 : W := mkw 0x124fb40015578000 0x0249f68002aaf000 0xd0cffc0001c78005 0xba19ff800038f000

def z553 : W := mkw 0x081068e4610a1e65 0x21020d1c8c2143cc 0x8800e1e4e1063e67 0x91001c3c9c20c7cc

def z554 : W := mkw 0x17efb7029ff7e010 0x82fdf6e053fefc02 0xf7fffe031fffc01d 0xfeffffc063fff803

def z555 : W := mkw 0x36fffcfd5df78000 0x06dfff9fabbef000 0xd7fffc781fff8005 0xfaffff8f03fff000

def z556 : W := mkw 0x030b0302b4050851 0x806160605680a10a 0xa70f0387e007807b 0x74e1e070fc00f00f

def z557 : W := mkw 0x24f4f8fd414282a8 0x449e9f1fa8285055 0x40f0fc7801c00780 0x881e1f8f003800f0

def z558 : W := mkw 0x0db127d03bbe7f67 0x21b624fa0777cfec 0xfff003f81ffe7fe6 0xfffe007f03ffcffc

def z559 : W := mkw 0x29116ffff11e1e65 0x25222dfffe23c3cc 0xa833fffff13e3e67 0xd5067ffffe27c7cc

def z560 : W := mkw 0x000020000beaf7ae 0x40000400017d5ef5 0x180000001ffffffc 0x0300000003ffffff

def z561 : W := mkw 0x124fb40015578000 0x0249f68002aaf000 0x970ffc001e078005 0x72e1ff8003c0f000

def z562 : W := mkw 0x0db16ff47bbe7f67 0x21b62dfe8f77cfec 0x8f33fde4ff3e3e67 0xd1e67fbc9fe7c7cc

def z563 : W := mkw 0x27fe9bdbc0000000 0x04ffd37b78000000 0x67ff1f9be0000000 0x6cffe3f37c000000

def z564 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xd7f001801ff83804 0xfafe003003ff0700

def z565 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x280ce27f0007c7fb 0x05019c4fe000f8ff

def z566 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x77f003981ef87980 0x6efe007303df0f30

def z567 : W := mkw 0x001100c0300c1c45 0x0002201806018388 0x883301e4f13e3e67 0xd106603c9e27c7cc

def z568 : W := mkw 0x08112cc0711e1e65 0x210225980e23c3cc 0x08331d80f13e3e64 0x410663b01e27c7cc

def z569 : W := mkw 0x04e4a00009e28000 0x009c9400013c5000 0xd7fce0001fff8005 0xfaff9c0003fff000

def z570 : W := mkw 0x27ba1bd2caa87506 0x04f7437a59550ea0 0xfff31ff8fff87f86 0xfffe63ff1fff0ff0

def z571 : W := mkw 0x001000c000081404 0x0002001800010280 0x0030006001380600 0x8006000c002700c0

def z572 : W := mkw 0x120b24001df78000 0x0241648003bef000 0x970f00001fff8005 0x72e1e00003fff000

def z573 : W := mkw 0x16ab14001cb50000 0x02d562800396a000 0x973f1c001e3f8005 0x72e7e38003c7f000

def z574 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0xbf030380fe007806 0x77e060701fc00f00

def z575 : W := mkw 0x1effbcc07dff9c45 0x23dff7980fbff388 0xd7fffd80ffffb805 0xfaffffb01ffff700

def z576 : W := mkw 0x124ff42d155782a8 0x4249fe85a2aaf055 0x000ffc0700078079 0x0001ff80e000f00f

def z577 : W := mkw 0x031b03d2b60d7d57 0x8063607a56c1afaa 0xbf0f03fffe07ffff 0x77e1e07fffc0ffff

def z578 : W := mkw 0x0044a009014282a8 0x4008940120285055 0x78cc021b01c7c7fc 0x2f1980436038f8ff

def z579 : W := mkw 0x034e830b8641e098 0xc069d06170c83c13 0x77cc021b0ec1c198 0x2ef9804361d83833

def z580 : W := mkw 0x17fe93d00ee9f506 0x02ffd27a01dd3ea0 0xfffc03f81ff9ff86 0xffff807f03ff3ff0

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0xb800020000004006 0x3700004000000800

def z582 : W := mkw 0x0044800900000000 0x0008900120000000 0x60cc021b00000000 0x2c19804360000000

def z583 : W := mkw 0x05b043fd0aa877ae 0x40b6087fa1550ef5 0xfff003ff1ff87ffe 0xfffe007fe3ff0fff

def z584 : W := mkw 0x0001000036056851 0x8000200006c0ad0a 0xb80c02071e07f87f 0x37018040e3c0ff0f

def z585 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x68c0e27f01c047fa 0x8d181c4fe03808ff

def z586 : W := mkw 0x1a5ffce4755f9e65 0x234bff9c8eabf3cc 0x883ffde4f13fbe67 0xd107ffbc9e27f7cc

def z587 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0xe0cce27f01c00783 0xbc199c4fe03800f0

def z588 : W := mkw 0x0db16ff4711e1e65 0x21b62dfe8e23c3cc 0xeff3fffcf13e3e67 0xfdfe7fff9e27c7cc

def z589 : W := mkw 0x05b127d01bbe7506 0x00b624fa0377cea0 0xfff3fff81ffe7f87 0xfffe7fff03ffcff0

def z590 : W := mkw 0x05b003d002087506 0x00b6007a00410ea0 0xeff003f800007f82 0xfdfe007f00000ff0

def z591 : W := mkw 0x27aa131280000000 0x04f5426250000000 0x0700000000000000 0x00e0000000000000

def z592 : W := mkw 0x034fa302b747e851 0x8069f46056e8fd0a 0xffcfe387ffc7f87f 0xfff9fc70fff8ff0f

def z593 : W := mkw 0x27ee931b80408088 0x44fdd26370081011 0x77cc021b00c1c198 0x2ef9804360183833

def z594 : W := mkw 0x0001000014050000 0x000020000280a000 0x100000001e078004 0x0200000003c0f000

def z595 : W := mkw 0x2cf4fcfd411a1624 0x259e9f9fa82342c4 0x40f0fc7801380600 0x881e1f8f002700c0

def z596 : W := mkw 0x000120003747eaf9 0xc000240006e8fd5f 0x180000001fc7fffc 0x0300000003f8ffff

def z597 : W := mkw 0x030b0302bead7d57 0x8061606057d5afaa 0xbf0f0387ffffffff 0x77e1e070ffffffff

def z598 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x47f3fdf8e0000000 0xc8fe7fbf1c000000

def z599 : W := mkw 0x37fffffffff7e851 0x86fffffffffefd0a 0xfffffffffffff87f 0xffffffffffffff0f

def z600 : W := mkw 0x2ffffffff1160a61 0x25fffffffe22c14c 0xe7ffffffe0060063 0xfcfffffffc00c00c

def z601 : W := mkw 0x2fffdffff01c1c45 0x25fffbfffe038388 0xe7fffffff0383803 0xfcfffffffe070700

def z602 : W := mkw 0x224fd82ff4050851 0x8449fb05fe80a10a 0x000ffc07e0078079 0x0001ff80fc00f00f

def z603 : W := mkw 0x324ffc2fd5578000 0x0649ff85faaaf000 0x000ffc07e0078001 0x0001ff80fc00f000

def z604 : W := mkw 0x2ffeffffc11a1624 0x25ffdffff82342c4 0xe7ffffffe1380603 0xfcfffffffc2700c0

def z605 : W := mkw 0x030a030286016010 0x8061406050c02c02 0xbf0c03831e01f81e 0x77e1807063c03f03

def z606 : W := mkw 0x0b5fefeff75ffefd 0xe16bfdfdfeebffdf 0xffffffffffffffff 0xffffffffffffffff

def z607 : W := mkw 0x14e4f42d09f282a8 0x429c9e85a13e5055 0x40f0fc7801f80780 0x881e1f8f003f00f0

def z608 : W := mkw 0x25f4dbffc0000000 0x04be9b7ff8000000 0x60f0ffffe0000002 0x8c1e1ffffc000000

def z609 : W := mkw 0x0044a000014282a8 0x4008940000285055 0xd8cce00001c7c7fd 0xbb199c000038f8ff

def z610 : W := mkw 0x27bb1bd2f6056851 0x84f7637a5ec0ad0a 0x07331d80fe003800 0x40e663b01fc00700

def z611 : W := mkw 0x17ee93100ee1e102 0x02fdd26201dc3c20 0x77cc02180ec1c180 0x2ef9804301d83830

def z612 : W := mkw 0x0b0b2702b71f7e75 0xa16164e056e3efce 0xbf0f0387ff3ffe7f 0x77e1e070ffe7ffcf

def z613 : W := mkw 0x17ffb7d01df78000 0x02fff6fa03bef000 0xf7fffff81fff8007 0xfeffffff03fff000

def z614 : W := mkw 0x14e4b40009f28000 0x029c9680013e5000 0xd0fcfc0001ff8005 0xba1f9f80003ff000

def z615 : W := mkw 0x08116ce4511e1624 0x21022d9c8a23c2c4 0x8033fc60113e0605 0xd0067f8c0227c0c0

def z616 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800000400060067 0x110000008000c00c

def z617 : W := mkw 0x2fbb1fd2f01c1c45 0x25f763fa5e038388 0x07331d80f0383800 0x40e663b01e070700

def z618 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800006001000606 0x9100000c002000c0

def z619 : W := mkw 0x06aa100000000000 0x00d5420000000000 0x07331c0000000000 0x40e6638000000000

def z620 : W := mkw 0x031b4be6f6056851 0x8063697cdec0ad0a 0xbf3fffe7fe07f87f 0xf7e7fffcffc0ff0f

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00c020700000003 0x34018040e0000000

def z622 : W := mkw 0x020b000014050000 0x004160000280a000 0x070300001e000000 0x40e0600003c00000

def z623 : W := mkw 0x001000c000081404 0x0002001800010280 0x080001e000003e02 0x0100003c000007c0

def z624 : W := mkw 0x27ffdbfff6056851 0x84fffb7ffec0ad0a 0xe7fffffffe003803 0xfcffffffffc00700

def z625 : W := mkw 0x05a003100aa06102 0x00b4006201540c20 0xffc002780fc04786 0xbff8004f01f808f0

def z626 : W := mkw 0x0001000030040841 0x0000200006008108 0x00030004e0060061 0x000060009c00c00c

def z627 : W := mkw 0x05b103d03ead7d57 0x80b6207a07d5afaa 0xfff003f81ffffffe 0xfffe007f03ffffff

def z628 : W := mkw 0x0000200001428000 0x0000040000285000 0x1000000001c78004 0x020000000038f000

def z629 : W := mkw 0x09116fe4731e7e65 0x21222dfc8e63cfcc 0xbf33ffe4ff3e7e67 0xf7e67ffc9fe7cfcc

def z630 : W := mkw 0x05a0031000000000 0x00b4006200000000 0x67c0021800000000 0x2cf8004300000000

def z631 : W := mkw 0x000000000aa87506 0x0000000001550ea0 0x000000001e383800 0x0000000003c70700

def z632 : W := mkw 0x27ba5bffc0000000 0x04f74b7ff8000000 0x27331fffe0000002 0x44e663fffc000000

def z633 : W := mkw 0x00002000014282a8 0x4000040000285055 0x0000000001c00780 0x00000000003800f0

def z634 : W := mkw 0x001068e441020220 0x00020d1c88204044 0x8833fde4e1060667 0xd1067fbc9c20c0cc

def z635 : W := mkw 0x16ef90001ce58000 0x02ddf200039cb000 0xd7cf00001ec78005 0x7af9e00003d8f000

def z636 : W := mkw 0x1fffffe6fffffe75 0xa3fffffcdfffffce 0xffffffe7fffffe7f 0xfffffffcffffffcf

def z637 : W := mkw 0x05b003d008a81506 0x00b6007a011502a0 0xe7f003f801f80782 0xfcfe007f003f00f0

def z638 : W := mkw 0x16eeb40009f28000 0x02ddd680013e5000 0xc7fffc0001f80001 0xf8ffff80003f0000

def z639 : W := mkw 0x1cf4fce449fa9624 0x239e9f9c893f52c4 0x40f0fc6001f80600 0x881e1f8c003f00c0

def z640 : W := mkw 0x05b003d000000000 0x00b6007a00000000 0x0730018000000000 0x40e6003000000000

def z641 : W := mkw 0x0144e32fa342eaf9 0xc0289c65f4685d5f 0xf8cce3ffe1c7ffff 0xbf199c7ffc38ffff

def z642 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0xd0cce07801c78785 0xba199c0f0038f0f0

def z643 : W := mkw 0x030a0302a6016851 0x8061406054c02d0a 0x3f0c0387ee01f87a 0x27e18070fdc03f0f

def z644 : W := mkw 0x16ffb4d01dff9506 0x02dff69a03bff2a0 0xd7fffc781fff8785 0xfaffff8f03fff0f0

def z645 : W := mkw 0x04a0001008a00102 0x0094000201140020 0x40c0001800c00180 0x0818000300180030

def z646 : W := mkw 0x27ee931b86016010 0x84fdd26370c02c02 0x77cc021b0e01c018 0x2ef9804361c03803

def z647 : W := mkw 0x0044e02d01020220 0x00089c05a0204044 0xe8cce27f01060667 0xbd199c4fe020c0cc

def z648 : W := mkw 0x2fbb7ff6f11e1e65 0x25f76ffede23c3cc 0x8f33fde4f13e3e67 0xd1e67fbc9e27c7cc

def z649 : W := mkw 0x030b2302b747eaf9 0xc061646056e8fd5f 0xbf0f0387ffc7ffff 0x77e1e070fff8ffff

def z650 : W := mkw 0x04a0000008a00000 0x0094000001140000 0x40f0000001f80000 0x881e0000003f0000

def z651 : W := mkw 0x0efffce4711e1e65 0x21dfff9c8e23c3cc 0xcffffde4f13e3e67 0xf9ffffbc9e27c7cc

def z652 : W := mkw 0x08010c0070140841 0x210021800e028108 0x00031c00e0000000 0x000063801c000000

def z653 : W := mkw 0x0854eced415a96ac 0x610a9d9da82b52d5 0x40f0fc7801f80780 0x881e1f8f003f00f0

def z654 : W := mkw 0x2154cbffc0000000 0x042a997ff8000000 0xe0cce3ffe0000003 0xbc199c7ffc000000

def z655 : W := mkw 0x024fa00015478000 0x0049f40002a8f000 0xd7cfe0001fc78005 0xfaf9fc0003f8f000

def z656 : W := mkw 0x27fefbffc14282a8 0x44ffdf7ff8285055 0xe7ffffffe1c00783 0xfcfffffffc3800f0

def z657 : W := mkw 0x0cb16cf479be1f67 0x21962d9e8f37c3ec 0xc8f3fdfcf1fe3fe7 0xd91e7fbf9e3fc7fc

def z658 : W := mkw 0x0000000008a00000 0x0000000001140000 0x100000001ff80004 0x0200000003ff0000

def z659 : W := mkw 0x000100003ead7d57 0x8000200007d5afaa 0x180000001ffffffc 0x0300000003ffffff

def z660 : W := mkw 0x09116fe6f31e7e75 0xa1222dfcde63cfce 0xa833ffe7f13e7e7f 0xd5067ffcfe27cfcf

def z661 : W := mkw 0x08116ce471160a61 0x21022d9c8e22c14c 0x8033fde4e0060063 0xd0067fbc9c00c00c

def z662 : W := mkw 0x0845ec2d71568ae9 0x6108bd85ae2ad15d 0x000ffc07e0078079 0x0001ff80fc00f00f

def z663 : W := mkw 0x27fedbffe2006851 0x84ffdb7ffc400d0a 0xefffffffe000787b 0xfdfffffffc000f0f

def z664 : W := mkw 0x27fe93db80000000 0x04ffd27b70000000 0xe7fc03fb00000002 0xfcff807f60000000

def z665 : W := mkw 0x0100030002006000 0x0020006000400c00 0x070001801e003800 0x40e0003003c00700

def z666 : W := mkw 0x27ffdbfff0040841 0x04fffb7ffe008108 0xeffffffff0063867 0xfdfffffffe00c70c

def z667 : W := mkw 0x08100cc040181404 0x2102019808030280 0x00301c0000380000 0x0006038000070000

def z668 : W := mkw 0x0000402400000220 0x0000080480000044 0x0800006400000662 0x0100000c800000cc

def z669 : W := mkw 0x0100030002006000 0x0020006000400c00 0x2800038000007802 0x0500007000000f00

def z670 : W := mkw 0x020b000014050000 0x004160000280a000 0x000f000000078001 0x0001e0000000f000

def z671 : W := mkw 0x0101030032046841 0x0020206006408d08 0xbf030384fe067867 0x77e060709fc0cf0c

def z672 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x0803fde4e0063e63 0x01007fbc9c00c7cc

def z673 : W := mkw 0x100000000ce18000 0x02000000019c3000 0x100000000ec18000 0x0200000001d83000

def z674 : W := mkw 0x04a0000008a00000 0x0094000001140000 0x073000001e380000 0x40e6000003c70000

def z675 : W := mkw 0x001000c000081404 0x0002001800010280 0xf8f003f811f87f86 0xff1e007f023f0ff0

def z676 : W := mkw 0x05f4a3d00beaf506 0x00be947a017d5ea0 0xfffce3f81fffff87 0xffff9c7f03fffff0

def z677 : W := mkw 0x231a4bffc0000000 0x0463497ff8000000 0xa70f03ffe0000003 0x74e1e07ffc000000

def z678 : W := mkw 0x25f4dbfd4aa87506 0x04be9b7fa9550ea0 0xfff0fff81ff87f86 0xfffe1fff03ff0ff0

def z679 : W := mkw 0x2154ebffc14282a8 0x442a9d7ff8285055 0xf8cce3ffe1c7c7ff 0xbf199c7ffc38f8ff

def z680 : W := mkw 0x0044800000000000 0x0008900000000000 0xc0cce00000000001 0xb8199c0000000000

def z681 : W := mkw 0x08016424311e1e65 0x21002c848623c3cc 0x8800e064113e3e67 0x91001c0c8227c7cc

def z682 : W := mkw 0x08106ce4411a1624 0x21020d9c882342c4 0x8830fde011383e06 0xd1061fbc022707c0

def z683 : W := mkw 0x0100030002006000 0x0020006000400c00 0x370002000e004000 0x26e0004001c00800

def z684 : W := mkw 0x0db06ff44bba7726 0x21b60dfe89774ee4 0xfff0fff81ff87f86 0xfffe1fff03ff0ff0

def z685 : W := mkw 0x04a0000008a00000 0x0094000001140000 0x57c000000ec00000 0x2af8000001d80000

def z686 : W := mkw 0x17efb7101ff7e102 0x02fdf6e203fefc20 0xf7fffe181fffc185 0xfeffffc303fff830

def z687 : W := mkw 0x3ffffffffdff9e65 0x27ffffffffbff3cc 0xffffffffffffbe67 0xfffffffffffff7cc

def z688 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x1f030180fe07f87c 0x43e060301fc0ff0f

def z689 : W := mkw 0x0000000008a81506 0x00000000011502a0 0x0000000001f80780 0x00000000003f00f0

def z690 : W := mkw 0x07bb03d2bead7d57 0x80f7607a57d5afaa 0xfff303f8fff87f86 0xfffe607f1fff0ff0

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0x8030000011380004 0xd006000002270000

def z692 : W := mkw 0x0100030002006000 0x0020006000400c00 0xbf0c03871e07f87f 0x77e18070e3c0ff0f

def z693 : W := mkw 0x100124001df782a8 0x4200248003bef055 0x180000001fffc7fc 0x0300000003fff8ff

def z694 : W := mkw 0x24f4f8fd414282a8 0x449e9f1fa8285055 0xf8fcfe7f01c7c7ff 0xbf1f9fcfe038f8ff

def z695 : W := mkw 0x05b003d008a00000 0x00b6007a01140000 0xf7f003f81ff80006 0xfefe007f03ff0000

def z696 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x40fffc0001ff8001 0x881fff80003ff000

def z697 : W := mkw 0x16ffb4c01dff9404 0x02dff69803bff280 0xdffffde01fffbe07 0xfbffffbc03fff7c0

def z698 : W := mkw 0x0000000002087506 0x0000000000410ea0 0x0800000000007f80 0x0100000000000ff0

def z699 : W := mkw 0x25f4dbfd40000000 0x04be9b7fa8000000 0xe7f0fff800000002 0xfcfe1fff00000000

def z700 : W := mkw 0x0001000010040000 0x0000200002008000 0x8003000010060005 0x500060000200c000

def z701 : W := mkw 0x0044c02d00000000 0x00089805a0000000 0x40c0e07800000000 0x88181c0f00000000

def z702 : W := mkw 0x08106ce4411a1624 0x21020d9c882342c4 0x8830fc64013e0667 0x91061f8c8027c0cc

def z703 : W := mkw 0x0b1b0fc2f61d7c55 0xa16361f85ec3af8a 0x07331d80fe383800 0x40e663b01fc70700

def z704 : W := mkw 0x00002000014282a8 0x4000040000285055 0xb80c020701c7c7ff 0x37018040e038f8ff

def z705 : W := mkw 0x000000000aa06102 0x0000000001540c20 0x100000000ec04180 0x0200000001d80830

def z706 : W := mkw 0x07ffe3ffbfefffff 0xc0fffc7ff7fdffff 0xffffe3ffffffffff 0xfffffc7fffffffff

def z707 : W := mkw 0x24f4d8fd48a81506 0x049e9b1fa91502a0 0xc8f3fdfcf1f83f87 0xd91e7fbf9e3f07f0

def z708 : W := mkw 0x034fe32fb747eaf9 0xc069fc65f6e8fd5f 0x47c3e1f8ffc03f80 0xc8f87c3f1ff807f0

def z709 : W := mkw 0x1db127d03fffff67 0x23b624fa07ffffec 0xfff003f81fffffe6 0xfffe007f03fffffc

def z710 : W := mkw 0x26fed8ffc0000000 0x04dfdb1ff8000000 0xe0fffe7fe0000003 0xbc1fffcffc000000

def z711 : W := mkw 0x08012400331e7e65 0x210024800663cfcc 0x180000001f3e7e64 0x0300000003e7cfcc

def z712 : W := mkw 0x04b000d00aa87506 0x0096001a01550ea0 0xdff000781ff87f84 0xfbfe000f03ff0ff0

def z713 : W := mkw 0x07fe93d28aa87506 0x00ffd27a51550ea0 0xfffffffffff87f87 0xffffffffffff0ff0

def z714 : W := mkw 0x08116ce4711e1eed 0x61022d9c8e23c3dd 0x8833fde4f13e7fff 0xd1067fbc9e27cfff

def z715 : W := mkw 0x0da16f347bb66b63 0x21b42de68f76cd6c 0x77c3fe1ceec641e1 0x2ef87fc39dd8c83c

def z716 : W := mkw 0x27ba3bd2c14282a8 0x44f7477a58285055 0x1f331d80e1c7c7fc 0x43e663b01c38f8ff

def z717 : W := mkw 0x16fed8e44ce18000 0x02dfdb1c899c3000 0xd7fffde4eec18003 0xfaffffbc9dd83000

def z718 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x78cce27b01c7c7fc 0xaf199c4f6038f8ff

def z719 : W := mkw 0x1eefb4003df78a61 0x23ddf68007bef14c 0xd7fffc001fff8065 0xfaffff8003fff00c

def z720 : W := mkw 0x08558cc9705c9ccd 0x610ab1992e0b9399 0x70ff1f9bf0f9f998 0x6e1fe3f37e1f3f33

def z721 : W := mkw 0x16ab542d1cb502a8 0x42d56a85a396a055 0x2f331e7f1e3847fa 0x45e663cfe3c708ff

def z722 : W := mkw 0x05f4e3fd0beaf7ae 0x40be9c7fa17d5ef5 0x073ce1871e3fb879 0x40e79c30e3c7f70f

def z723 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0xf8cce3ff11c7ffff 0xff199c7fe238ffff

def z724 : W := mkw 0x06bb00d2bcad1d57 0x80d7601a5795a3aa 0x40ff007fe1ff87f9 0x881fe00ffc3ff0ff

def z725 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0xf7fffffffef87983 0xfeffffffffdf0f30

def z726 : W := mkw 0x21104bffc2087506 0x0422097ff8410ea0 0x200003ffe0003802 0x0400007ffc000700

def z727 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0xe8f3fffcf13e3e67 0xfd1e7fff9e27c7cc

def z728 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x88300000113e3e64 0xd10600000227c7cc

def z729 : W := mkw 0x27fe9bd2c0000000 0x04ffd37a58000000 0x073ffd80e0000001 0x40e7ffb01c000000

def z730 : W := mkw 0x011003c002087404 0x0022007800410e80 0xfff003f81ff87f86 0xfffe007f03ff0ff0

def z731 : W := mkw 0x0044c82d40000000 0x00089905a8000000 0x000ffc07e0000001 0x0001ff80fc000000

def z732 : W := mkw 0x235edbffc0000000 0x046bdb7ff8000000 0xa70fffffe0000003 0x74e1fffffc000000

def z733 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x7ff002781ff87f84 0xaffe004f03ff0ff0

def z734 : W := mkw 0x27fe9bd2c0000000 0x04ffd37a58000000 0xe7ffff87e0000003 0xfcfffff0fc000000

def z735 : W := mkw 0x235edbffc0000000 0x046bdb7ff8000000 0xa03fffffe0000003 0xd407fffffc000000

def z736 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xffffffffe0004007 0xfffffffffc000800

def z737 : W := mkw 0x25b04bffcaa87506 0x04b6097ff9550ea0 0xfff3fffffff87f87 0xfffe7fffffff0ff0

def z738 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x57fffc000fff8001 0xaaffff8001fff000

def z739 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x0833fde4f03e3e63 0x41067fbc9e07c7cc

def z740 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0xefffffffe1f87f83 0xfdfffffffc3f0ff0

def z741 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xcff001f81ff83f86 0xd9fe003f03ff07f0

def z742 : W := mkw 0x27fedbffc8a00000 0x04ffdb7ff9140000 0xf7ffffffeec00003 0xfefffffffdd80000

def z743 : W := mkw 0x16ab34001db70000 0x02d5668003b6e000 0x0733fc001e3e0001 0x40e67f8003c7c000

def z744 : W := mkw 0x001048e440000000 0x0002091c88000000 0xa03fffe7e0000003 0xf407fffcfc000000

def z745 : W := mkw 0x08012400375ffefd 0xe100248006ebffdf 0x180000001ffffffc 0x0300000003ffffff

def z746 : W := mkw 0x05b003d28aa87506 0x00b6007a51550ea0 0xfff003fffff87f86 0xfffe007fffff0ff0

def z747 : W := mkw 0x2fefb71bb11e1e65 0x25fdf6e37623c3cc 0x6fcc021b113e3e64 0x2df980436227c7cc

def z748 : W := mkw 0x08116ced715e9eed 0x61022d9dae2bd3dd 0xb833fffff1ffffff 0xd7067ffffe3fffff

def z749 : W := mkw 0x31116fffddf78000 0x06222dfffbbef000 0x300003ffffff8006 0x0600007ffffff000

def z750 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0xc0cffc07e0000001 0xb819ff80fc000000

def z751 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x00000000103e3860 0x000000000207c70c

def z752 : W := mkw 0x06ee900008a00000 0x00ddd20001140000 0xc7fffc001e380001 0xf8ffff8003c70000

def z753 : W := mkw 0x001048e440081404 0x0002091c88010280 0x8033fde4e1380603 0xd0067fbc9c2700c0

def z754 : W := mkw 0x27fedbf6c0000000 0x04ffdb7ed8000000 0xc7fffde4e0000003 0xf8ffffbc9c000000

def z755 : W := mkw 0x001048ed40000000 0x0002091da8000000 0xa033ffffe0000003 0xd4067ffffc000000

def z756 : W := mkw 0x0000602401020220 0x00000c0480204044 0xf8cce27f01c7c7ff 0xbf199c4fe038f8ff

def z757 : W := mkw 0x09104bf6e2087f77 0xa122097edc410fee 0x280003ffe0007ffa 0x0500007ffc000fff

def z758 : W := mkw 0x16efb4029df78010 0x82ddf68053bef002 0xd7fffc031fff801d 0xfaffff8063fff003

def z759 : W := mkw 0x001048e440000000 0x0002091c88000000 0x0033fc64e0000001 0x80067f8c9c000000

def z760 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x0033fd80f0383800 0x40067fb01e070700

def z761 : W := mkw 0x27fe9bd2c0000000 0x04ffd37a58000000 0xe7fffff8e0000003 0xfcffffff1c000000

def z762 : W := mkw 0x16eeb4000df38000 0x02ddd68001be7000 0x47f0fc000ff80000 0x88fe1f8001ff0000

def z763 : W := mkw 0x17efb702bff7e851 0x82fdf6e057fefd0a 0x7fcc02031ffff87c 0x2ff9804063ffff0f

def z764 : W := mkw 0x27fedbffc8a81404 0x04ffdb7ff9150280 0xfffffffffff83e07 0xffffffffffff07c0

def z765 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xf7fffe071fff8007 0xfeffffc0e3fff000

def z766 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0x40cffc7fe0000001 0x8819ff8ffc000000

def z767 : W := mkw 0x04a1240019b60000 0x009424800336c000 0x8733fc001f3e0005 0xd0e67f8003e7c000

def z768 : W := mkw 0x0b1a6fe6c71b7634 0xa1634dfcd8e36ec6 0x373cfe630f39c618 0xa6e79fcc61e738c3

def z769 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0x200ffe7fe0000003 0x0401ffcffc000000

def z770 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xe7f003f81ff83f82 0xfcfe007f03ff07f0

def z771 : W := mkw 0x180124003dff9eed 0x6300248007bff3dd 0x180000001ffffffc 0x0300000003ffffff

def z772 : W := mkw 0x26fed8efc0000000 0x04dfdb1df8000000 0xc7fffde7e0000003 0xf8ffffbcfc000000

def z773 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x68cce27f01c7c7fb 0x8d199c4fe038f8ff

def z774 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xfff003ff1ff87ffe 0xfffe007fe3ff0fff

def z775 : W := mkw 0x031a4be6c6016010 0x8063497cd8c02c02 0xb73fffe7ee01c01b 0xf6e7fffcfdc03803

def z776 : W := mkw 0x05b04bf44aa06102 0x00b6097e89540c20 0xf7f3fffceec04183 0xfefe7fff9dd80830

def z777 : W := mkw 0x27fedbffc0000088 0x44ffdb7ff8000011 0xe7ffffffe000419b 0xfcfffffffc000833

def z778 : W := mkw 0x16efb4029df78000 0x02ddf68053bef000 0xd7fffc07ffff8005 0xfaffff80fffff000

def z779 : W := mkw 0x081124c0311e1e65 0x210224980623c3cc 0x08300180113e3e64 0x410600300227c7cc

def z780 : W := mkw 0x135fb7d0175ff506 0x026bf6fa02ebfea0 0x280ffff80007ff83 0x0501ffff0000fff0

def z781 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x0000000011383e00 0x00000000022707c0

def z782 : W := mkw 0x04b048f440000000 0x0096091e88000000 0xc0f3fdfce0000003 0xd81e7fbf9c000000

def z783 : W := mkw 0x27fedbffc00002a8 0x44ffdb7ff8000055 0xffffffffe007c7ff 0xfffffffffc00f8ff

def z784 : W := mkw 0x27fedbffc2087506 0x04ffdb7ff8410ea0 0xe7ffffffe0003803 0xfcfffffffc000700

def z785 : W := mkw 0x001048e440081404 0x0002091c88010280 0x8033fde4f0383803 0xd0067fbc9e070700

def z786 : W := mkw 0x201048fd40000000 0x0402091fa8000000 0x8033fdfce0000003 0xd0067fbf9c000000

def z787 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x5ff001f81ff87f84 0xcbfe003f03ff0ff0

def z788 : W := mkw 0x124ff42fb5578af9 0xc249fe85f6aaf15f 0x000ffc07e0078079 0x0001ff80fc00f00f

def z789 : W := mkw 0x081048e440081624 0x2102091c880102c4 0x8033fde4e0000603 0xd0067fbc9c0000c0

def z790 : W := mkw 0x01104bf442087506 0x0022097e88410ea0 0xa833fffce0007f83 0xd5067fff9c000ff0

def z791 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xfff303fcfff87f87 0xfffe607f9fff0ff0

def z792 : W := mkw 0x031a4be6c2087404 0x0063497cd8410e80 0xbf3fffe7ff387e07 0xf7e7fffcffe70fc0

def z793 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x88000060113e3e66 0x9100000c0227c7cc

def z794 : W := mkw 0x08112cc0711e1c45 0x210225980e23c388 0x0033fd80f1383800 0xc0067fb01e270700

def z795 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xdffffc601fff8607 0xfbffff8c03fff0c0

def z796 : W := mkw 0x17ee93028ee1e010 0x82fdd26051dc3c02 0xf7ffff87eec1c01b 0xfefffff0fdd83803

def z797 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x8833fde0f1383e06 0xd1067fbc1e2707c0

def z798 : W := mkw 0x27fedbffc6016010 0x84ffdb7ff8c02c02 0xe7ffffffee000003 0xfcfffffffdc00000

def z799 : W := mkw 0x06eed82440000000 0x00dddb0488000000 0xc7fffc04e0000001 0xf8ffff809c000000

def z800 : W := mkw 0x16efb4001df782a8 0x42ddf68003bef055 0xd7fffc001fff807d 0xfaffff8003fff00f

def z801 : W := mkw 0x100124003df78851 0x8200248007bef10a 0x100000001fff807c 0x0200000003fff00f

def z802 : W := mkw 0x15e4b702abf2e851 0x82bc96e0557e5d0a 0x68f0ff87e1f8787a 0x8d1e1ff0fc3f0f0f

def z803 : W := mkw 0x27fedbffc2087506 0x04ffdb7ff8410ea0 0xfffffffffe007f87 0xffffffffffc00ff0

def z804 : W := mkw 0x24f4f8fd49ea97ae 0x449e9f1fa93d52f5 0x40f0fc7801f80780 0x881e1f8f003f00f0

def z805 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x67fffe7fe0000001 0xacffffcffc000000

def z806 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x67cfffffe0000003 0x2cf9fffffc000000

def z807 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0x0003fc00e0000000 0x00007f801c000000

def z808 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x77f003f81ff87f80 0xeefe007f03ff0ff0

def z809 : W := mkw 0x17ee93028ee1e010 0x82fdd26051dc3c02 0x57cc00000ec18000 0x2af9800001d83000

def z810 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0xfffffffffe387807 0xffffffffffc70f00

def z811 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x60ffffffe0000003 0x8c1ffffffc000000

def z812 : W := mkw 0x0044a009014282a8 0x4008940120285055 0xf8cc027b01c7c7fe 0xbf19804f6038f8ff

def z813 : W := mkw 0x08116ce4715e9eed 0x61022d9c8e2bd3dd 0xf8f3fffcf1ffffff 0xff1e7fff9e3fffff

def z814 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xfffc03ff1ff87f87 0xffff807fe3ff0ff0

def z815 : W := mkw 0x16efb402bdf78851 0x82ddf68057bef10a 0xd7fffc00ffff8005 0xfaffff801ffff000

def z816 : W := mkw 0x27fedbffc0081404 0x04ffdb7ff8010280 0xefffffffe0003e03 0xfdfffffffc0007c0

def z817 : W := mkw 0x001048e440000000 0x0002091c88000000 0xe0f3fffce0000003 0xfc1e7fff9c000000

def z818 : W := mkw 0x37fedbffcce18088 0x46ffdb7ff99c3011 0xf7ffffffeec1c19b 0xfefffffffdd83833

def z819 : W := mkw 0x25b00bd2caa87506 0x04b6017a59550ea0 0xfff003f8fff87f86 0xfffe007f1fff0ff0

def z820 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x0800000000063e60 0x010000000000c7cc

def z821 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x9f33fde4ff3e3e67 0xf3e67fbc9fe7c7cc

def z822 : W := mkw 0x0801240035170a71 0xa100248006a2e14e 0x0000000000078078 0x000000000000f00f

def z823 : W := mkw 0x27fedbffcaa06102 0x04ffdb7ff9540c20 0xf7fffffffff84187 0xfeffffffffff0830

def z824 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xe7ffffffe1c00783 0xfcfffffffc3800f0

def z825 : W := mkw 0x221a58e6c0000000 0x04434b1cd8000000 0x8033fde4e0000003 0xd0067fbc9c000000

def z826 : W := mkw 0x25f4dbfd40000000 0x04be9b7fa8000000 0xe7f3fffce0000003 0xfcfe7fff9c000000

def z827 : W := mkw 0x27fedbffc6016010 0x84ffdb7ff8c02c02 0xfffffffffe01f81f 0xffffffffffc03f03

def z828 : W := mkw 0x08114ce4701c1c45 0x2102299c8e038388 0x8833fde4f1383e07 0xd1067fbc9e2707c0

def z829 : W := mkw 0x14a124001df78000 0x0294248003bef000 0xd7f3fc001fff8005 0xfafe7f8003fff000

def z830 : W := mkw 0x124fb40015578000 0x0249f68002aaf000 0x973ffc001f3f8005 0xf2e7ff8003e7f000

def z831 : W := mkw 0x27ee931b8ae0e18a 0x44fdd263715c1c31 0x77cc021b0ec1c198 0x2ef9804361d83833

def z832 : W := mkw 0x224ed82fc0408088 0x4449db05f8081011 0x70cffe1fe0c1c199 0x2e19ffc3fc183833

def z833 : W := mkw 0x27fedbffc8a00000 0x04ffdb7ff9140000 0xe7ffffffe1f80003 0xfcfffffffc3f0000

def z834 : W := mkw 0x16ab34001df78000 0x02d5668003bef000 0x9733fc001fff8005 0xd2e67f8003fff000

def z835 : W := mkw 0x06ee900280000000 0x00ddd20050000000 0xc7fffc07e0000001 0xf8ffff80fc000000

def z836 : W := mkw 0x001068e4410a1624 0x00020d1c882142c4 0x8833fde4f13e3e67 0xd1067fbc9e27c7cc

def z837 : W := mkw 0x0044a009014282a8 0x4008940120285055 0x70cc021b00c7c1f8 0x2e1980436018f83f

def z838 : W := mkw 0x2044f82d414282a8 0x44089f05a8285055 0xf8ccfe7f01c7c7ff 0xbf199fcfe038f8ff

def z839 : W := mkw 0x234edb2fc6016010 0x8469db65f8c02c02 0x370ffe07ee01c019 0x26e1ffc0fdc03803

def z840 : W := mkw 0x21104bffc2087506 0x0422097ff8410ea0 0xa833fffff1387f87 0xd5067ffffe270ff0

def z841 : W := mkw 0x05a003100aa87506 0x00b4006201550ea0 0xffc002781ff87f86 0xbff8004f03ff0ff0

def z842 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0xc8f3fdfcf1fe3fe7 0xd91e7fbf9e3fc7fc

def z843 : W := mkw 0x01104be440000000 0x0022097c88000000 0xa733ffe4e0000003 0xf4e67ffc9c000000

def z844 : W := mkw 0x001048e44aa87506 0x0002091c89550ea0 0x9833fde4fff87f87 0xd3067fbc9fff0ff0

def z845 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0xbf0f0387ffc7ffff 0x77e1e070fff8ffff

def z846 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xf7ffffffe001c01b 0xfefffffffc003803

def z847 : W := mkw 0x225ed8ffc0000000 0x044bdb1ff8000000 0x000ffc7fe0000001 0x0001ff8ffc000000

def z848 : W := mkw 0x27fedbffc8a00000 0x04ffdb7ff9140000 0xfffffffffff84787 0xffffffffffff08f0

def z849 : W := mkw 0x2ffedbffc0081624 0x25ffdb7ff80102c4 0xe7ffffffe0000603 0xfcfffffffc0000c0

def z850 : W := mkw 0x224ed82fc4010010 0x8449db05f8802002 0x000ffc07e0018019 0x0001ff80fc003003

def z851 : W := mkw 0x021a48e440000000 0x0043491c88000000 0x873ffde4e0000003 0xf0e7ffbc9c000000

def z852 : W := mkw 0x06ef90001ca50000 0x00ddf2000394a000 0xd7fffc001fff8005 0xfaffff8003fff000

def z853 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0xa00ffe07e0000003 0x3401ffc0fc000000

def z854 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0xfff3fff8fff87f86 0xfffe7fff1fff0ff0

def z855 : W := mkw 0x05f4cbfd4aa87506 0x00be997fa9550ea0 0xfffffffffff87f87 0xffffffffffff0ff0

def z856 : W := mkw 0x36efb40b9df78000 0x06ddf68173bef000 0xd7fffc031fff8005 0xfaffff8063fff000

def z857 : W := mkw 0x07ba4bf6c0000000 0x00f7497ed8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z858 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0xffcf039ffec7f9ff 0x7ff9e073ffd8ff3f

def z859 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0xf8cffe7fe1c04787 0xbf19ffcffc3808f0

def z860 : W := mkw 0x16ef94001cb50000 0x02ddf2800396a000 0xd7fffc001e3f8005 0xfaffff8003c7f000

def z861 : W := mkw 0x08116ced711e1eed 0x61022d9dae23c3dd 0x8833fde7f13e3e7f 0xd1067fbcfe27c7cf

def z862 : W := mkw 0x09104be6e2087e75 0xa122097cdc410fce 0x080001e4e0003e62 0x0100003c9c0007cc

def z863 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0xffcf0387ffc7f87f 0xfff9e070fff8ff0f

def z864 : W := mkw 0x27fedbffc2006000 0x04ffdb7ff8400c00 0xfffffffffe07f87f 0xffffffffffc0ff0f

def z865 : W := mkw 0x224ed82fc0408088 0x4449db05f8081011 0x000ffc07e0018019 0x0001ff80fc003003

def z866 : W := mkw 0x21104bffc20877ae 0x4422097ff8410ef5 0x280003ffe0007ffa 0x0500007ffc000fff

def z867 : W := mkw 0x08116ce4715e9e65 0x21022d9c8e2bd3cc 0x9833fde4f1ffbe67 0xd3067fbc9e3ff7cc

def z868 : W := mkw 0x16efb4091df78088 0x42ddf68123bef011 0xfffffe7b1fffc79f 0xffffffcf63fff8f3

def z869 : W := mkw 0x0054c8ed40408088 0x400a991da8081011 0xf0ffffffe0c1c19b 0xfe1ffffffc183833

def z870 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0xa833fffcf13e7fe7 0xd5067fff9e27cffc

def z871 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x88000180113e3e66 0x510000300227c7cc

def z872 : W := mkw 0x06eeb00009e28000 0x00ddd600013c5000 0xd7fffc001fff8005 0xfaffff8003fff000

def z873 : W := mkw 0x27ba5bf6caa87506 0x04f74b7ed9550ea0 0x8f33fde4ff383e07 0xd1e67fbc9fe707c0

def z874 : W := mkw 0x225ed8efc0000000 0x044bdb1df8000000 0x003ffd87e0000001 0x4007ffb0fc000000

def z875 : W := mkw 0x27eedb3fc0000000 0x04fddb67f8000000 0xe7cfff9fe0000003 0x7cf9fff3fc000000

def z876 : W := mkw 0x27eedb3fc0000000 0x04fddb67f8000000 0xe7fffe1fe0000001 0xfcffffc3fc000000

def z877 : W := mkw 0x27fe9bd2caa87506 0x04ffd37a59550ea0 0xd7fffd80fff83805 0xfaffffb01fff0700

def z878 : W := mkw 0x08012400351f1e75 0xa100248006a3e3ce 0x08000000113fbe7c 0x010000000227f7cf

def z879 : W := mkw 0x28116cfd711e1e65 0x25022d9fae23c3cc 0x8833fdfcf13e3e67 0xd1067fbf9e27c7cc

def z880 : W := mkw 0x17ee930b8ee1e098 0xc2fdd26171dc3c13 0x77cc021b0ec1c198 0x2ef9804361d83833

def z881 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xdffffd801fffb807 0xfbffffb003fff700

def z882 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x7fc003f81ff87f86 0x2ff8007f03ff0ff0

def z883 : W := mkw 0x01104bf440000000 0x0022097e88000000 0xa033fffce0000003 0xd4067fff9c000000

def z884 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0x800ffc67e0000003 0x9001ff8cfc000000

def z885 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xf7fffffffe000007 0xfeffffffffc00000

def z886 : W := mkw 0x37ee931b8ee1e102 0x06fdd26371dc3c20 0x77cc021b0ec1c180 0x2ef9804361d83830

def z887 : W := mkw 0x26eed83fc0000000 0x04dddb07f8000000 0x40cffc1fe0000001 0x0819ff83fc000000

def z888 : W := mkw 0x27ba5bf6c0000000 0x04f74b7ed8000000 0x0733fde0e0000000 0xc0e67fbc1c000000

def z889 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x370f0387fe07f879 0x66e1e070ffc0ff0f

def z890 : W := mkw 0x14e4b40009f28000 0x029c9680013e5000 0x57f0fc000ff80000 0xaafe1f8001ff0000

def z891 : W := mkw 0x27bb1bd2fead7d57 0x84f7637a5fd5afaa 0x07331d80fe383800 0x40e663b01fc70700

def z892 : W := mkw 0x00116ce4511e1404 0x00022d9c8a23c280 0x8833fde4f13e3e07 0xd1067fbc9e27c7c0

def z893 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xdffffc001fffc07d 0xfbffff8003fff80f

def z894 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x1800000011fe7fe4 0x03000000023fcffc

def z895 : W := mkw 0x01104bf442087506 0x0022097e88410ea0 0x280003fce0007f82 0x0500007f9c000ff0

def z896 : W := mkw 0x0101030032046841 0x0020206006408d08 0xbf0f0387fe07f87f 0x77e1e070ffc0ff0f

def z897 : W := mkw 0x030a0302a6016851 0x8061406054c02d0a 0xbf0c0387ee07f87f 0x37e18070fdc0ff0f

def z898 : W := mkw 0x08116ce4715e9eed 0x61022d9c8e2bd3dd 0xb83fffe7f1ffffff 0xf707fffcfe3fffff

def z899 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x70cce27f01c7c7f9 0xae199c4fe038f8ff

def z900 : W := mkw 0x27ee931b8ea16112 0x84fdd26371d42c22 0x77cc021b0ec1c198 0x2ef9804361d83833

def z901 : W := mkw 0x36efb4191df78000 0x06ddf68323bef000 0xd7fffc181fff8005 0xfaffff8303fff000

def z902 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0xf8cfe3ffe1c7c7ff 0xff19fc7ffc38f8ff

def z903 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0xf8c0027811fe7fe6 0xbf18004f023fcffc

def z904 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0x000ffc07e0078079 0x0001ff80fc00f00f

def z905 : W := mkw 0x0054c8ed40000000 0x000a991da8000000 0x803ffde7e0000003 0xd007ffbcfc000000

def z906 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xefffffffe1000607 0xfdfffffffc2000c0

def z907 : W := mkw 0x16eeb40009f28000 0x02ddd680013e5000 0xd7fffc001ff80005 0xfaffff8003ff0000

def z908 : W := mkw 0x04a0000008a00000 0x0094000001140000 0xd7f3fc001ff80005 0xfafe7f8003ff0000

def z909 : W := mkw 0x00002000014282a8 0x4000040000285055 0xf8cc027f01c7c7ff 0xbf19804fe038f8ff

def z910 : W := mkw 0x16efb4001df782a8 0x42ddf68003bef055 0xfffffe781fffc7ff 0xffffffcf03fff8ff

def z911 : W := mkw 0x1efed8e46ce99e65 0x23dfdb1c8d9d33cc 0x5fcc01e4eec1be62 0x2bf9803c9dd837cc

def z912 : W := mkw 0x08114ce4701c1c45 0x2102299c8e038388 0x8833fde4f03e3867 0xd1067fbc9e07c70c

def z913 : W := mkw 0x225ed8efc0000000 0x044bdb1df8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z914 : W := mkw 0x27fedbffc0000220 0x04ffdb7ff8000044 0xefffffffe0000663 0xfdfffffffc0000cc

def z915 : W := mkw 0x24f5d8fd76056851 0x849ebb1faec0ad0a 0x58f0fc781e07f87c 0x8b1e1f8f03c0ff0f

def z916 : W := mkw 0x07fedbf440000000 0x00ffdb7e88000000 0xe7fffffce0000003 0xfcffffff9c000000

def z917 : W := mkw 0x16efb4001df78088 0x42ddf68003bef011 0xd7fffc001fffc19d 0xfaffff8003fff833

def z918 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x57cc00000ec78000 0x2af9800001d8f000

def z919 : W := mkw 0x08012400371f7e75 0xa100248006e3efce 0x080000001f3e3e64 0x0100000003e7c7cc

def z920 : W := mkw 0x09104bf462087f67 0x2122097e8c410fec 0x080001e4e0003e62 0x0100003c9c0007cc

def z921 : W := mkw 0x081124c0315e9eed 0x61022498062bd3dd 0xf8f003f811fffffe 0xff1e007f023fffff

def z922 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xc7f3fc001ffe0005 0xd8fe7f8003ffc000

def z923 : W := mkw 0x001124c0311e1c45 0x000224980623c388 0x8833fde4f13e3e67 0xd1067fbc9e27c7cc

def z924 : W := mkw 0x235edbffc0000000 0x046bdb7ff8000000 0x000ffd87e0000001 0x0001ffb0fc000000

def z925 : W := mkw 0x24f4d8fd40000000 0x049e9b1fa8000000 0x40f3fc7ce0000001 0x881e7f8f9c000000

def z926 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x3f0c0387fe07f87e 0x27e18070ffc0ff0f

def z927 : W := mkw 0x16ef94001cb50000 0x02ddf2800396a000 0x073ffc001e380001 0x40e7ff8003c70000

def z928 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xeffffffff0003807 0xfdfffffffe000700

def z929 : W := mkw 0x0801240031160a61 0x210024800622c14c 0x0800000010063864 0x010000000200c70c

def z930 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x18000000113ffe7c 0x030000000227ffcf

def z931 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xf7fffe181fffc185 0xfeffffc303fff830

def z932 : W := mkw 0x16efb4003df78841 0x02ddf68007bef108 0xffffff87fffff87f 0xfffffff0ffffff0f

def z933 : W := mkw 0x27ba5bf6caa87506 0x04f74b7ed9550ea0 0xfff3fffcfff87f87 0xfffe7fff9fff0ff0

def z934 : W := mkw 0x081124c0311e1e65 0x210224980623c3cc 0x080001e0113e3e66 0x0100003c0227c7cc

def z935 : W := mkw 0x180124003dff9c45 0x2300248007bff388 0x100000001fffb804 0x0200000003fff700

def z936 : W := mkw 0x08012400311e1eed 0x610024800623c3dd 0x08000000113e7ffc 0x010000000227cfff

def z937 : W := mkw 0x16ab14001cb50000 0x02d562800396a000 0x8733fc001e380001 0xd0e67f8003c70000

def z938 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xc7fffc001e3f8001 0xf8ffff8003c7f000

def z939 : W := mkw 0x09104befe2087efd 0xe122097dfc410fdf 0x280003ffe0007ffa 0x0500007ffc000fff

def z940 : W := mkw 0x0044e82d414282a8 0x40089d05a8285055 0xf8cffe7fe1c7c7ff 0xbf19ffcffc38f8ff

def z941 : W := mkw 0x224ed82fc00002a8 0x4449db05f8000055 0x000ffc07e0000079 0x0001ff80fc00000f

def z942 : W := mkw 0x27fedbffc0081404 0x04ffdb7ff8010280 0xe7ffffffe1380603 0xfcfffffffc2700c0

def z943 : W := mkw 0x07fe93d280000000 0x00ffd27a50000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z944 : W := mkw 0x27fedbffcaa06102 0x04ffdb7ff9540c20 0xe7ffffffee000003 0xfcfffffffdc00000

def z945 : W := mkw 0x234edb2fc0000000 0x0469db65f8000000 0x270ffe07e0000001 0x24e1ffc0fc000000

def z946 : W := mkw 0x234edb2fc0000000 0x0469db65f8000000 0x200fff87e0000003 0x0401fff0fc000000

def z947 : W := mkw 0x16eeb4000df38000 0x02ddd68001be7000 0xd7fcfc001ff98004 0xfaff9f8003ff3000

def z948 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0xb80c0207113ffe7f 0x37018040e227ffcf

def z949 : W := mkw 0x180124003fffff67 0x2300248007ffffec 0x180000001fffffe4 0x0300000003fffffc

def z950 : W := mkw 0x235edbffc0000000 0x046bdb7ff8000000 0xe0cfffffe0000003 0xbc19fffffc000000

def z951 : W := mkw 0x16ef94001cb50000 0x02ddf2800396a000 0x47f3fc001e380000 0xc8fe7f8003c70000

def z952 : W := mkw 0x08116ced711e1eed 0x61022d9dae23c3dd 0xb83ffffff13fffff 0xf707fffffe27ffff

def z953 : W := mkw 0x27fedbffc2006102 0x04ffdb7ff8400c20 0xe7ffffffe0004183 0xfcfffffffc000830

def z954 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0xefffffffff383e07 0xfdffffffffe707c0

def z955 : W := mkw 0x0845a409315e9eed 0x6108b481262bd3dd 0x78cc021b11fffffc 0x2f198043623fffff

def z956 : W := mkw 0x25b04bffc0000000 0x04b6097ff8000000 0xe7f3ffffe0000003 0xfcfe7ffffc000000

def z957 : W := mkw 0x0000000000000000 0x0000000000000000 0x8033fd84e0000003 0xd0067fb09c000000

def z958 : W := mkw 0x08116ced711e1eed 0x61022d9dae23c3dd 0xf8f3fffff1fe7fff 0xff1e7ffffe3fcfff

def z959 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xfff003fc1ffe7fe7 0xfffe007f83ffcffc

def z960 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x0833fde4f1383e62 0xc1067fbc9e2707cc

def z961 : W := mkw 0x27fedbffc0081404 0x04ffdb7ff8010280 0xe7fffffff0383803 0xfcfffffffe070700

def z962 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x67fffffbe0000000 0xecffffff7c000000

def z963 : W := mkw 0x010003000aa87506 0x0020006001550ea0 0xffc003f81ff87f86 0xfff8007f03ff0ff0

def z964 : W := mkw 0x01012702b3166851 0x802024e05662cd0a 0xa833ff87f13e787f 0xd5067ff0fe27cf0f

def z965 : W := mkw 0x06ab24001db70000 0x00d5648003b6e000 0xd7fffc001fff8005 0xfaffff8003fff000

def z966 : W := mkw 0x27fedbffc2087506 0x04ffdb7ff8410ea0 0xeffffffff1387f87 0xfdfffffffe270ff0

def z967 : W := mkw 0x1cf4fced49fa96ac 0x639e9f9da93f52d5 0x40f0fc7801f80780 0x881e1f8f003f00f0

def z968 : W := mkw 0x224ed82fcaa87506 0x0449db05f9550ea0 0x180ffc07fff87f85 0x0301ff80ffff0ff0

def z969 : W := mkw 0x0a1b48e4740d1e65 0x2143691c8e81a3cc 0x9f0f01e4fe07be67 0x73e1e03c9fc0f7cc

def z970 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0xe7fffffffff83f83 0xfcffffffffff07f0

def z971 : W := mkw 0x27fedbffc641e098 0xc4ffdb7ff8c83c13 0xf7ffffffeec1c19b 0xfefffffffdd83833

def z972 : W := mkw 0x030b0312b6056953 0x8061606256c0ad2a 0xbf0f039ffe07f9ff 0x77e1e073ffc0ff3f

def z973 : W := mkw 0x06efb40019b60000 0x00ddf6800336c000 0xd7fffc001ffe0005 0xfaffff8003ffc000

def z974 : W := mkw 0x0801240037176a71 0xa100248006e2ed4e 0x180000001e07f87c 0x0300000003c0ff0f

def z975 : W := mkw 0x0db127d03fbf7f77 0xa1b624fa07f7efee 0xfff003f81ffffffe 0xfffe007f03ffffff

def z976 : W := mkw 0x05b00bd04aa87506 0x00b6017a09550ea0 0xfff31ff8fff87f86 0xfffe63ff1fff0ff0

def z977 : W := mkw 0x04b000d008a81506 0x0096001a011502a0 0xdff001f81ff83f86 0xfbfe003f03ff07f0

def z978 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xefffffffe0004783 0xfdfffffffc0008f0

def z979 : W := mkw 0x100124003ff7eaf9 0xc200248007fefd5f 0x180000001ffffffc 0x0300000003ffffff

def z980 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xd7fffd84ffff8007 0xfaffffb09ffff000

def z981 : W := mkw 0x0801240039be1e65 0x210024800737c3cc 0x180000001ffe3e64 0x0300000003ffc7cc

def z982 : W := mkw 0x16eeb4000df38000 0x02ddd68001be7000 0xd7fffc000ff98001 0xfaffff8001ff3000

def z983 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xd7f3fc001ff80004 0xfafe7f8003ff0000

def z984 : W := mkw 0x08116ce4711e1c45 0x21022d9c8e23c388 0x8033fde4f13e3807 0xd0067fbc9e27c700

def z985 : W := mkw 0x37fedbffcee1e102 0x06ffdb7ff9dc3c20 0xf7ffffffeec1c183 0xfefffffffdd83830

def z986 : W := mkw 0x16ab34001db70000 0x02d5668003b6e000 0x973ffc001f3f8005 0xf2e7ff8003e7f000

def z987 : W := mkw 0x06ba58e440000000 0x00d74b1c88000000 0x8733fde4e0000003 0xd0e67fbc9c000000

def z988 : W := mkw 0x1044f42d015282a8 0x42089e85a02a5055 0xf8ccfe7f01c7c7ff 0xbf199fcfe038f8ff

def z989 : W := mkw 0x08012400331e7f67 0x210024800663cfec 0x08000000113e7fe4 0x010000000227cffc

def z990 : W := mkw 0x16ef94001cb50000 0x02ddf2800396a000 0xd7fffc001ff80005 0xfaffff8003ff0000

def z991 : W := mkw 0x08012400331e7e75 0xa10024800663cfce 0x08000000113e7e7c 0x010000000227cfcf

def z992 : W := mkw 0x001048e440000000 0x0002091c88000000 0x0033fde0e0000000 0xc0067fbc1c000000

def z993 : W := mkw 0x27ba5bffc0000000 0x04f74b7ff8000000 0xa733ffffe0000003 0xd4e67ffffc000000

def z994 : W := mkw 0x08114ce4701c1c45 0x2102299c8e038388 0x0033fd84f0383801 0x40067fb09e070700

def z995 : W := mkw 0x16efb4091df78000 0x02ddf68123bef000 0xf7fffe1b1fff8005 0xfeffffc363fff000

def z996 : W := mkw 0x020b0002b4050851 0x804160005680a10a 0x9f0f0187fe07b87f 0x73e1e030ffc0f70f

def z997 : W := mkw 0x0001240037176851 0x8000248006e2ed0a 0x180000001f3ff87c 0x0300000003e7ff0f

def z998 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0x073ffd87fe383801 0x40e7ffb0ffc70700

def z999 : W := mkw 0x224e9802c0000000 0x0449d30058000000 0x000ffc00e0000001 0x0001ff801c000000

def z1000 : W := mkw 0x08106ce4611a1e65 0x21020d9c8c2343cc 0x8833fde4e1383e63 0xd1067fbc9c2707cc

def z1001 : W := mkw 0x16ef94001cf58000 0x02ddf280039eb000 0xd7fffc001ef98001 0xfaffff8003df3000

def z1002 : W := mkw 0x16efb4003df78841 0x02ddf68007bef108 0xdffffc001fffb865 0xfbffff8003fff70c

def z1003 : W := mkw 0x09012700331e7e65 0x212024e00663cfcc 0xbf0003801f3e7e66 0x77e0007003e7cfcc

def z1004 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x973ffc001e3f8005 0x72e7ff8003c7f000

def z1005 : W := mkw 0x1eefb4003dff9e65 0x23ddf68007bff3cc 0x5fcc00001fffbe64 0x2bf9800003fff7cc

def z1006 : W := mkw 0x37fedbffcee9f506 0x06ffdb7ff9dd3ea0 0xfffffffffff9ff87 0xffffffffffff3ff0

def z1007 : W := mkw 0x08116ced711e1e65 0x21022d9dae23c3cc 0xa833fffff13e3e67 0xd5067ffffe27c7cc

def z1008 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0xb833ffe4f13e7e67 0xf7067ffc9e27cfcc

def z1009 : W := mkw 0x001048e440000000 0x0002091c88000000 0xf8f3fffce1c04787 0xff1e7fff9c3808f0

def z1010 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x8833fd84f13e3e67 0xd1067fb09e27c7cc

def z1011 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x57fffc001ff98000 0xeaffff8003ff3000

def z1012 : W := mkw 0x08116ce4751f1e65 0x21022d9c8ea3e3cc 0x9833fde4ff3fbe67 0xd3067fbc9fe7f7cc

def z1013 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x173ffc001fff8005 0x42e7ff8003fff000

def z1014 : W := mkw 0x0000482440000000 0x0000090488000000 0x8003fd84e0000003 0x50007fb09c000000

def z1015 : W := mkw 0x18116ce4755f9e65 0x23022d9c8eabf3cc 0x8833fde4f13fbe67 0xd1067fbc9e27f7cc

def z1016 : W := mkw 0x16efb4001df78220 0x02ddf68003bef044 0xdffffc001fff8665 0xfbffff8003fff0cc

def z1017 : W := mkw 0x29104bffe2087f67 0x2522097ffc410fec 0x280003ffe0007fe2 0x0500007ffc000ffc

def z1018 : W := mkw 0x180124003df78a61 0x2300248007bef14c 0x100000001fff8064 0x0200000003fff00c

def z1019 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0xbf3fff87fe07f87f 0xf7e7fff0ffc0ff0f

def z1020 : W := mkw 0x27fedbffc2006000 0x04ffdb7ff8400c00 0xffffffffffc07f87 0xfffffffffff80ff0

def z1021 : W := mkw 0x001048e440000000 0x0002091c88000000 0xb83fffe7e007c07f 0xf707fffcfc00f80f

def z1022 : W := mkw 0x0044c02d00000000 0x00089805a0000000 0xf8cce27f01c7c7ff 0xbf199c4fe038f8ff

def z1023 : W := mkw 0x27fedbffcaa06000 0x04ffdb7ff9540c00 0xfffffffffff87807 0xffffffffffff0f00

def z1024 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xf7ffffffe0078007 0xfefffffffc00f000

def z1025 : W := mkw 0x07ee93028aa06000 0x00fdd26051540c00 0xffffff87fff87807 0xfffffff0ffff0f00

def z1026 : W := mkw 0x14e5b40019f68000 0x029cb680033ed000 0xd7f3fc001ffe0005 0xfafe7f8003ffc000

def z1027 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x47fffc001fff8001 0xc8ffff8003fff000

def z1028 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x0733fd80e0000000 0x40e67fb01c000000

def z1029 : W := mkw 0x0000402400000000 0x0000080480000000 0x8800e06401000607 0x91001c0c802000c0

def z1030 : W := mkw 0x08116cf4711e1f67 0x21022d9e8e23c3ec 0x8833fdfcf13e3fe7 0xd1067fbf9e27c7fc

def z1031 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x08000060113e3e64 0x0100000c0227c7cc

def z1032 : W := mkw 0x0000000000000000 0x0000000000000000 0x88030184f0003807 0x510060309e000700

def z1033 : W := mkw 0x17bb17d2bebd7d57 0x82f762fa57d7afaa 0x07331d80fe383800 0x40e663b01fc70700

def z1034 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xd7f001f81ff83f84 0xfafe003f03ff07f0

def z1035 : W := mkw 0x27fedbffc8a81506 0x04ffdb7ff91502a0 0xffffffffe1f84787 0xfffffffffc3f08f0

def z1036 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0xeffffffffe387f83 0xfdffffffffc70ff0

def z1037 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0xa83fffe7f13e3e67 0xf507fffcfe27c7cc

def z1038 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xe7fffffff1380007 0xfcfffffffe270000

def z1039 : W := mkw 0x0044800900408088 0x4008900120081011 0xf8cc027f01c7c7ff 0xbf19804fe038f8ff

def z1040 : W := mkw 0x180124003ffffe75 0xa300248007ffffce 0x180000001ffffe7c 0x0300000003ffffcf

def z1041 : W := mkw 0x2044d82d40000000 0x04089b05a8000000 0x0003fc04e0000001 0x00007f809c000000

def z1042 : W := mkw 0x031b4be6f60d7c55 0x8063697cdec1af8a 0xbf3fffe7ff3ffe7f 0xf7e7fffcffe7ffcf

def z1043 : W := mkw 0x16ee90000ce18000 0x02ddd200019c3000 0xd7fffc001ff98005 0xfaffff8003ff3000

def z1044 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x67f3ffffe0000002 0xccfe7ffffc000000

def z1045 : W := mkw 0x04b048e448a00000 0x0096091c89140000 0xd7f3fde4fff80007 0xfafe7fbc9fff0000

def z1046 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x8033fd84f13e3865 0xd0067fb09e27c70c

def z1047 : W := mkw 0x27fedbffc2006010 0x84ffdb7ff8400c02 0xe7ffffffe000401b 0xfcfffffffc000803

def z1048 : W := mkw 0x091127d0331e7f67 0x212224fa0663cfec 0x280003f8113e7fe6 0x0500007f0227cffc

def z1049 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x983ffde4f13fbe67 0xf307ffbc9e27f7cc

def z1050 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xe7f3fff8e0000002 0xfcfe7fff1c000000

def z1051 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xfffffe001fffc007 0xffffffc003fff800

def z1052 : W := mkw 0x0da127103bbe7f67 0x21b424e20777cfec 0x7fc002181ffe7fe4 0x2ff8004303ffcffc

def z1053 : W := mkw 0x0db127d0311e1e65 0x21b624fa0623c3cc 0xeff003f8113e3e66 0xfdfe007f0227c7cc

def z1054 : W := mkw 0x1801240035578a61 0x2300248006aaf14c 0x0000000000078060 0x000000000000f00c

def z1055 : W := mkw 0x0054c8ed40081404 0x000a991da8010280 0xf8fffffff1f87f87 0xff1ffffffe3f0ff0

def z1056 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0xd8f3fde4f1fe3e67 0xfb1e7fbc9e3fc7cc

def z1057 : W := mkw 0x05f4cbfd40000000 0x00be997fa8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1058 : W := mkw 0x01000302a2006851 0x8020006054400d0a 0xbf0c0387fe07f87f 0x77e18070ffc0ff0f

def z1059 : W := mkw 0x27fedbffc0408088 0x44ffdb7ff8081011 0xffffffffe1c1c79f 0xfffffffffc3838f3

def z1060 : W := mkw 0x08012400315e9e65 0x21002480062bd3cc 0x1800000011ffbe64 0x03000000023ff7cc

def z1061 : W := mkw 0x09104bfd62087fef 0x6122097fac410ffd 0x280003ffe0007ffa 0x0500007ffc000fff

def z1062 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0xffcce27f1fc7c7ff 0xfff99c4fe3f8f8ff

def z1063 : W := mkw 0x0a4fec2ff5578af9 0xe149fd85feaaf15f 0x000ffc07e0078079 0x0001ff80fc00f00f

def z1064 : W := mkw 0x16efb4091df78088 0x42ddf68123bef011 0xd7fffc031fff801d 0xfaffff8063fff003

def z1065 : W := mkw 0x37ee931b8ee1e010 0x86fdd26371dc3c02 0x77cc021b0ec1c018 0x2ef9804361d83803

def z1066 : W := mkw 0x08116ce4715e9eed 0x61022d9c8e2bd3dd 0x8833fde4f13fbe7f 0xd1067fbc9e27f7cf

def z1067 : W := mkw 0x06ee900000000000 0x00ddd20000000000 0xc7fffd84e0000003 0xf8ffffb09c000000

def z1068 : W := mkw 0x27fedbffc6016010 0x84ffdb7ff8c02c02 0xffffffffee07c07f 0xfffffffffdc0f80f

def z1069 : W := mkw 0x24f4d8fd40000000 0x049e9b1fa8000000 0x40f3fdf8e0000000 0xc81e7fbf1c000000

def z1070 : W := mkw 0x14e5b4001df78000 0x029cb68003bef000 0xd7f0fc001fff8004 0xfafe1f8003fff000

def z1071 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0xa833ffe7f13e7e7f 0xd5067ffcfe27cfcf

def z1072 : W := mkw 0x14e4b40009f28000 0x029c9680013e5000 0xd7fcfc001fff8005 0xfaff9f8003fff000

def z1073 : W := mkw 0x16efb4001db70000 0x02ddf68003b6e000 0xc7fffc001f3e0005 0xf8ffff8003e7c000

def z1074 : W := mkw 0x37fedbffcce18000 0x06ffdb7ff99c3000 0xf7fffffffff98007 0xfeffffffffff3000

def z1075 : W := mkw 0x27fedbffc04082a8 0x44ffdb7ff8081055 0xffffffffe0c1c7fb 0xfffffffffc1838ff

def z1076 : W := mkw 0x06fe98c040000000 0x00dfd31808000000 0xc7fffd80e0000001 0xf8ffffb01c000000

def z1077 : W := mkw 0x15a127003ff7e851 0x82b424e007fefd0a 0xfff003801ffff87e 0xfffe007003ffff0f

def z1078 : W := mkw 0x18012400355f9e65 0x2300248006abf3cc 0x08000000113fbe64 0x010000000227f7cc

def z1079 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xefffffffe000407b 0xfdfffffffc00080f

def z1080 : W := mkw 0x04e5a40019f68000 0x009cb480033ed000 0xd7fffc001fff8005 0xfaffff8003fff000

def z1081 : W := mkw 0x37fedbffcee1e010 0x86ffdb7ff9dc3c02 0xf7ffffffeec1c01b 0xfefffffffdd83803

def z1082 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xfffffe7f1fffc7ff 0xffffffcfe3fff8ff

def z1083 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x0733fc001e380000 0x40e67f8003c70000

def z1084 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x370c02030e07c078 0x26e1804061c0f80f

def z1085 : W := mkw 0x035ecbefc0000000 0x006bd97df8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1086 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x9833fde4f13ffe7f 0xd3067fbc9e27ffcf

def z1087 : W := mkw 0x07ee930280000000 0x00fdd26050000000 0xc7fffd80e0000001 0xf8ffffb01c000000

def z1088 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xffffffffe1c7c7ff 0xfffffffffc38f8ff

def z1089 : W := mkw 0x27fedbffcea16112 0x84ffdb7ff9d42c22 0xf7ffffffeec1c19b 0xfefffffffdd83833

def z1090 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x8f0f0187fe07b87f 0x51e1e030ffc0f70f

def z1091 : W := mkw 0x235edbefc0000000 0x046bdb7df8000000 0xa73fffe7e0000003 0xf4e7fffcfc000000

def z1092 : W := mkw 0x08012400311e1c45 0x210024800623c388 0x00000000113e3804 0x000000000227c700

def z1093 : W := mkw 0x0db127d03bbe7f67 0x21b624fa0777cfec 0x0f3001801f3e3e64 0x41e6003003e7c7cc

def z1094 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xfffc03fb1ff9ff9e 0xffff807f63ff3ff3

def z1095 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x9833fde4f1fe7fe7 0xd3067fbc9e3fcffc

def z1096 : W := mkw 0x08106ce4411a1624 0x21020d9c882342c4 0x8833fde4f1383e07 0xd1067fbc9e2707c0

def z1097 : W := mkw 0x27ba5bf6c0000000 0x04f74b7ed8000000 0x0733fd84e0000001 0x40e67fb09c000000

def z1098 : W := mkw 0x16efb4003df78841 0x02ddf68007bef108 0xd7fffd80ffffb805 0xfaffffb01ffff700

def z1099 : W := mkw 0x27ee931b8aa06102 0x04fdd26371540c20 0x67cc021b0e000000 0x2cf9804361c00000

def z1100 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x57fcfc001fff8004 0xaaff9f8003fff000

def z1101 : W := mkw 0x27fedbffcae0e18a 0x44ffdb7ff95c1c31 0xf7ffffffeec1c19b 0xfefffffffdd83833

def z1102 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xdffffc041fff8067 0xfbffff8083fff00c

def z1103 : W := mkw 0x27fedbffcea97516 0x84ffdb7ff9d52ea2 0xfffffffffff9ff9f 0xffffffffffff3ff3

def z1104 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x8033fde0f13e3e05 0xd0067fbc1e27c7c0

def z1105 : W := mkw 0x0054c8ed40000000 0x000a991da8000000 0xc0f3fdfce0000003 0xd81e7fbf9c000000

def z1106 : W := mkw 0x0001240031160841 0x000024800622c108 0x8033fd80f13e3805 0xd0067fb01e27c700

def z1107 : W := mkw 0x27fedbffc8a00000 0x04ffdb7ff9140000 0xe7fffffffe380003 0xfcffffffffc70000

def z1108 : W := mkw 0x27fedbffc2006000 0x04ffdb7ff8400c00 0xf7ffffffee004003 0xfefffffffdc00800

def z1109 : W := mkw 0x020b240015170000 0x0041648002a2e000 0x8733fc001f3e0005 0xd0e67f8003e7c000

def z1110 : W := mkw 0x29104bffe2087e75 0xa522097ffc410fce 0x280003ffe0007e7a 0x0500007ffc000fcf

def z1111 : W := mkw 0x21104bfd42087506 0x0422097fa8410ea0 0x280003f800007f82 0x0500007f00000ff0

def z1112 : W := mkw 0x0db127d03bfeffef 0x61b624fa077fdffd 0xfff003f81ffffffe 0xfffe007f03ffffff

def z1113 : W := mkw 0x26eed82fc0000000 0x04dddb05f8000000 0x073ffc07e0000001 0x40e7ff80fc000000

def z1114 : W := mkw 0x37fedbffc4418000 0x06ffdb7ff8883000 0xe7ffffffe0018003 0xfcfffffffc003000

def z1115 : W := mkw 0x16efb4003df78851 0x82ddf68007bef10a 0xd7fffc001fff807d 0xfaffff8003fff00f

def z1116 : W := mkw 0x001008c040000000 0x0002011808000000 0x8033fd80e0000001 0xd0067fb01c000000

def z1117 : W := mkw 0x080124003bfeffef 0x61002480077fdffd 0x180000001ffffffc 0x0300000003ffffff

def z1118 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0xb80ffe07e007c07f 0x3701ffc0fc00f80f

def z1119 : W := mkw 0x26fed8ffc0000000 0x04dfdb1ff8000000 0xc7fffc7fe0000001 0xf8ffff8ffc000000

def z1120 : W := mkw 0x024ed82440000000 0x0049db0488000000 0x000ffc04e0000001 0x0001ff809c000000

def z1121 : W := mkw 0x27fedbffcae8f58e 0x44ffdb7ff95d1eb1 0xfffffffffff9ff9f 0xffffffffffff3ff3

def z1122 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x883ffde7f13fbe7f 0xd107ffbcfe27f7cf

def z1123 : W := mkw 0x05a003000aa06000 0x00b4006001540c00 0xfff003f81ff87f86 0xfffe007f03ff0ff0

def z1124 : W := mkw 0x26fed8ffc0000000 0x04dfdb1ff8000000 0xc0fffdffe0000003 0xd81fffbffc000000

def z1125 : W := mkw 0x0b0b2702b71f7e75 0xa16164e056e3efce 0x3f0c02031f3ffe7c 0x27e1804063e7ffcf

def z1126 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x78cc027f01c7c7fe 0x2f19804fe038f8ff

def z1127 : W := mkw 0x0fbb0fd2febd7d57 0xa1f761fa5fd7afaa 0x07331d80fe383800 0x40e663b01fc70700

def z1128 : W := mkw 0x27ba5bf6c0000000 0x04f74b7ed8000000 0xe7f3fffce0000003 0xfcfe7fff9c000000

def z1129 : W := mkw 0x27fedbffc2087404 0x04ffdb7ff8410e80 0xffffffffff387e07 0xffffffffffe70fc0

def z1130 : W := mkw 0x27fedbffc00002a8 0x44ffdb7ff8000055 0xffffffffe1c047ff 0xfffffffffc3808ff

def z1131 : W := mkw 0x08110cc0701c1c45 0x210221980e038388 0x8033fd80f0383801 0xd0067fb01e070700

def z1132 : W := mkw 0x00116ce471160841 0x00022d9c8e22c108 0x8833fde4f13e3867 0xd1067fbc9e27c70c

def z1133 : W := mkw 0x27ba5bf6c0000000 0x04f74b7ed8000000 0xa73fffe7e0000003 0xf4e7fffcfc000000

def z1134 : W := mkw 0x16efb402bdf78851 0x82ddf68057bef10a 0xdffffd87ffffb87f 0xfbffffb0fffff70f

def z1135 : W := mkw 0x26eed82fc0000000 0x04dddb05f8000000 0xe7fffe7fe0000003 0xfcffffcffc000000

def z1136 : W := mkw 0x1801240039fe9e65 0x23002480073fd3cc 0x0800000011fe3e64 0x01000000023fc7cc

def z1137 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0xffffffffffffffff 0xffffffffffffffff

def z1138 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xfff003f81ffffffe 0xfffe007f03ffffff

def z1139 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x0833fd84f13e3e65 0x41067fb09e27c7cc

def z1140 : W := mkw 0x26fed8ffc0000000 0x04dfdb1ff8000000 0x40f3fc78e0000000 0x881e7f8f1c000000

def z1141 : W := mkw 0x231a4bffc0000000 0x0463497ff8000000 0xa73fffffe0000003 0xf4e7fffffc000000

def z1142 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xfff3fff81ff87f87 0xfffe7fff03ff0ff0

def z1143 : W := mkw 0x001048e440000000 0x0002091c88000000 0x8833fde4e0060067 0xd1067fbc9c00c00c

def z1144 : W := mkw 0x27fedbffc2006000 0x04ffdb7ff8400c00 0xefffffffe0007803 0xfdfffffffc000f00

def z1145 : W := mkw 0x14e4b40009f28000 0x029c9680013e5000 0x47f0fc001ff80000 0xc8fe1f8003ff0000

def z1146 : W := mkw 0x27eedb3fc0000000 0x04fddb67f8000000 0x070ffc07e0000001 0x00e1ff80fc000000

def z1147 : W := mkw 0x08116ce4751f1e75 0xa1022d9c8ea3e3ce 0x8833fde4f13fbe7f 0xd1067fbc9e27f7cf

def z1148 : W := mkw 0x27fedbffc0408088 0x44ffdb7ff8081011 0xe7ffffffe0c00183 0xfcfffffffc180030

def z1149 : W := mkw 0x16ab34001db70000 0x02d5668003b6e000 0x0733fc001f380000 0xc0e67f8003e70000

def z1150 : W := mkw 0x0044e42d015282a8 0x40089c85a02a5055 0xf8fcfe7f01ffc7ff 0xbf1f9fcfe03ff8ff

def z1151 : W := mkw 0x16efb4001df782a8 0x42ddf68003bef055 0xfffffe071fffc7ff 0xffffffc0e3fff8ff

def z1152 : W := mkw 0x0000000000000000 0x0000000000000000 0x8033fc0011380005 0xd0067f8002270000

def z1153 : W := mkw 0x08112cc0711e1c45 0x210225980e23c388 0x8833fd84f13e3867 0xd1067fb09e27c70c

def z1154 : W := mkw 0x001048e440000000 0x0002091c88000000 0x0033fd84e0000001 0x40067fb09c000000

def z1155 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xefffffffe0060067 0xfdfffffffc00c00c

def z1156 : W := mkw 0x16efb4091df78088 0x42ddf68123bef011 0xfffffe1f1fffc1ff 0xffffffc3e3fff83f

def z1157 : W := mkw 0x0801240031568ae9 0x61002480062ad15d 0x1800000001c7c7fc 0x030000000038f8ff

def z1158 : W := mkw 0x21104bffe2087d57 0x8422097ffc410faa 0x280003ffe0007ffa 0x0500007ffc000fff

def z1159 : W := mkw 0x100124003df78841 0x0200248007bef108 0x180000001fffb864 0x0300000003fff70c

def z1160 : W := mkw 0x001048ed400002a8 0x4002091da8000055 0xa833ffffe00047fb 0xd5067ffffc0008ff

def z1161 : W := mkw 0x081048e460081e65 0x2102091c8c0103cc 0x8833fde4f1383e67 0xd1067fbc9e2707cc

def z1162 : W := mkw 0x2000482fc0000000 0x04000905f8000000 0x0003fc07e0000001 0x00007f80fc000000

def z1163 : W := mkw 0x024e900280000000 0x0049d20050000000 0x000ffc07e0000001 0x0001ff80fc000000

def z1164 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x67ffff9fe0000001 0x6cfffff3fc000000

def z1165 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0xfffc03f81fffff87 0xffff807f03fffff0

def z1166 : W := mkw 0x37fedbffc8e08000 0x06ffdb7ff91c1000 0xe7ffffffe0c00003 0xfcfffffffc180000

def z1167 : W := mkw 0x27eedb3fcaa06102 0x04fddb67f9540c20 0x77cffe1feec04181 0x2ef9ffc3fdd80830

def z1168 : W := mkw 0x0000482440000000 0x0000090488000000 0x8003fc64e0000003 0x90007f8c9c000000

def z1169 : W := mkw 0x16efb4101df78102 0x02ddf68203bef020 0xd7fffc181fff8185 0xfaffff8303fff030

def z1170 : W := mkw 0x27eedb3fc0000000 0x04fddb67f8000000 0xe7cffe7fe0000003 0xbcf9ffcffc000000

def z1171 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x0833fde4e13e3e63 0x81067fbc9c27c7cc

def z1172 : W := mkw 0x09104bf442087726 0x2122097e88410ee4 0x280003f800007f82 0x0500007f00000ff0

def z1173 : W := mkw 0x225ed8efc0000000 0x044bdb1df8000000 0x003ffc67e0000001 0x8007ff8cfc000000

def z1174 : W := mkw 0x025ed8e440000000 0x004bdb1c88000000 0x803ffde4e0000003 0xd007ffbc9c000000

def z1175 : W := mkw 0x225ed8efc0000000 0x044bdb1df8000000 0x000ffde7e0000003 0x0001ffbcfc000000

def z1176 : W := mkw 0x08112cc0711e1c45 0x210225980e23c388 0x0033fd80f03e3801 0x40067fb01e07c700

def z1177 : W := mkw 0x0054e8ed414a96ac 0x400a9d1da82952d5 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z1178 : W := mkw 0x0cf4ecfd49fa97ae 0x619e9d9fa93f52f5 0x40f0fc7801f80780 0x881e1f8f003f00f0

def z1179 : W := mkw 0x27fedbffcaa877ae 0x44ffdb7ff9550ef5 0xfffffffffff87fff 0xffffffffffff0fff

def z1180 : W := mkw 0x08116ce4715e9eed 0x61022d9c8e2bd3dd 0x8833fde4f1fe3fe7 0xd1067fbc9e3fc7fc

def z1181 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xc7fffd87e0000001 0xf8ffffb0fc000000

def z1182 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xf7fffe781fff8007 0xfeffffcf03fff000

def z1183 : W := mkw 0x234edb2fc2006000 0x0469db65f8400c00 0xbf0fff87fe007807 0x77e1fff0ffc00f00

def z1184 : W := mkw 0x030a030282006000 0x0061406050400c00 0xbf0f0387fe07f87f 0x77e1e070ffc0ff0f

def z1185 : W := mkw 0x120b24001df78000 0x0241648003bef000 0x973ffc001fff8005 0xf2e7ff8003fff000

def z1186 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0x78cce27f00c7c7fb 0x2f199c4fe018f8ff

def z1187 : W := mkw 0x130b1702b6156851 0x826162e056c2ad0a 0xbf0f1f87fe07f87f 0x77e1e3f0ffc0ff0f

def z1188 : W := mkw 0x08012400351f1e65 0x2100248006a3e3cc 0x180000001f3fbe64 0x0300000003e7f7cc

def z1189 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x47fffdffe0000001 0xc8ffffbffc000000

def z1190 : W := mkw 0x27fedbffc2087506 0x04ffdb7ff8410ea0 0xffffffffe1c07f87 0xfffffffffc380ff0

def z1191 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x273fffffe0000003 0x44e7fffffc000000

def z1192 : W := mkw 0x235edbffc2087506 0x046bdb7ff8410ea0 0x280fffffe0007f83 0x0501fffffc000ff0

def z1193 : W := mkw 0x16fffce45dff9404 0x02dfff9c8bbff280 0xdffffde4ffffbe07 0xfbffffbc9ffff7c0

def z1194 : W := mkw 0x27ba1bd2c0000000 0x04f7437a58000000 0x8733fd80e0000001 0xd0e67fb01c000000

def z1195 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0xbf0f03e7ff07fe7f 0xf7e1e07cffe0ffcf

def z1196 : W := mkw 0x001048e440000000 0x0002091c88000000 0x0003fde4e0000003 0x00007fbc9c000000

def z1197 : W := mkw 0x05b003d00aa87506 0x00b6007a01550ea0 0x6ff003f81ff87f82 0xcdfe007f03ff0ff0

def z1198 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xdffffc001fffc785 0xfbffff8003fff8f0

def z1199 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xc7fffdf8e0000001 0xf8ffffbf1c000000

def z1200 : W := mkw 0x27eedb2fc0000000 0x04fddb65f8000000 0xe7ffff87e0000003 0xfcfffff0fc000000

def z1201 : W := mkw 0x01104be442006000 0x0022097c88400c00 0xbf33ffe4fe007807 0xf7e67ffc9fc00f00

def z1202 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z1203 : W := mkw 0x100124003ffffd57 0x8200248007ffffaa 0x180000001ffffffc 0x0300000003ffffff

def z1204 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x970f0187fe07b87d 0x72e1e030ffc0f70f

def z1205 : W := mkw 0x06fed8e448a81404 0x00dfdb1c89150280 0xdffffde4fff83e07 0xfbffffbc9fff07c0

def z1206 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x8833fd84f03e3867 0x51067fb09e07c70c

def z1207 : W := mkw 0x27fedbffc0408000 0x04ffdb7ff8081000 0xf7ffffffe0c18003 0xfefffffffc183000

def z1208 : W := mkw 0x0044a00001428000 0x0008940000285000 0xf8cce27f01c7c7ff 0xbf199c4fe038f8ff

def z1209 : W := mkw 0x08114ce4701c1c45 0x2102299c8e038388 0x0033fde0f0383800 0xc0067fbc1e070700

def z1210 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0xbf3f0387ff3ff87f 0xf7e7e070ffe7ff0f

def z1211 : W := mkw 0x25b01bd04aa87506 0x04b6037a09550ea0 0xfff01ff81ff87f86 0xfffe03ff03ff0ff0

def z1212 : W := mkw 0x024fa40015578000 0x0049f48002aaf000 0xd7fffc001fff8005 0xfaffff8003fff000

def z1213 : W := mkw 0x0cb124d039be1f67 0x2196249a0737c3ec 0x48f0007811fe3fe4 0x891e000f023fc7fc

def z1214 : W := mkw 0x001148e4700c1c45 0x0002291c8e018388 0x8833fde4f13e3e67 0xd1067fbc9e27c7cc

def z1215 : W := mkw 0x1001240035578851 0x8200248006aaf10a 0x0000000000078078 0x000000000000f00f

def z1216 : W := mkw 0x1cb124c03dff9e65 0x2396249807bff3cc 0xdff001e01fffbe66 0xfbfe003c03fff7cc

def z1217 : W := mkw 0x0801642d311e1eed 0x61002c85a623c3dd 0x2800027f113e7ffe 0x0500004fe227cfff

def z1218 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xf7fffe031fffc01d 0xfeffffc063fff803

def z1219 : W := mkw 0x08016c2471160a61 0x21002d848e22c14c 0x8833fd84f13e3867 0xd1067fb09e27c70c

def z1220 : W := mkw 0x25f4dbffc0000000 0x04be9b7ff8000000 0xe0f3ffffe0000003 0xdc1e7ffffc000000

def z1221 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0xf8fffe7f01c7c7ff 0xff1fffcfe038f8ff

def z1222 : W := mkw 0x021a48e6c0000000 0x0043491cd8000000 0x803ffde7e0000003 0xd007ffbcfc000000

def z1223 : W := mkw 0x0801240039be1f67 0x210024800737c3ec 0x0800000011fe3fe4 0x01000000023fc7fc

def z1224 : W := mkw 0x07ba4bf6caa87506 0x00f7497ed9550ea0 0xfffffffffff87f87 0xffffffffffff0ff0

def z1225 : W := mkw 0x24b058f440000000 0x04960b1e88000000 0x8033fde4e0000003 0xd0067fbc9c000000

def z1226 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0x870ffc07e0000001 0x70e1ff80fc000000

def z1227 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x88000004113e3e67 0x110000008227c7cc

def z1228 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x8033fde4f03e3863 0xd0067fbc9e07c70c

def z1229 : W := mkw 0x16ab34001db70000 0x02d5668003b6e000 0xd7f3fc001ffe0005 0xfafe7f8003ffc000

def z1230 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0x800ffd87e0000003 0x5001ffb0fc000000

def z1231 : W := mkw 0x0000482440000000 0x0000090488000000 0x8033fc04e0000001 0xd0067f809c000000

def z1232 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0x803ffc07e0000001 0xd007ff80fc000000

def z1233 : W := mkw 0x001048e440081404 0x0002091c88010280 0x080001e4e0003e02 0x0100003c9c0007c0

def z1234 : W := mkw 0x27fe9bd2caa87506 0x04ffd37a59550ea0 0xfffffff8fff87f87 0xffffffff1fff0ff0

def z1235 : W := mkw 0x27fedbffc8a81506 0x04ffdb7ff91502a0 0xf7fffffffff80787 0xfeffffffffff00f0

def z1236 : W := mkw 0x08012400311e1e65 0x210024800623c3cc 0x00000000013e0660 0x000000000027c0cc

def z1237 : W := mkw 0x0001240031160841 0x000024800622c108 0x08000000113e3864 0x010000000227c70c

def z1238 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xc7fffc001ff80001 0xf8ffff8003ff0000

def z1239 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xd7fffc781fff8785 0xfaffff8f03fff0f0

def z1240 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x1f0f0187fe07f87d 0x43e1e030ffc0ff0f

def z1241 : W := mkw 0x0054c8e440000000 0x000a991c88000000 0xc0fffde4e0000003 0xf81fffbc9c000000

def z1242 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x0033fde4f13e3e61 0xc0067fbc9e27c7cc

def z1243 : W := mkw 0x27fe9bd2c0000000 0x04ffd37a58000000 0x47f3fd80e0000000 0xc8fe7fb01c000000

def z1244 : W := mkw 0x04a0240009b20000 0x0094048001364000 0xd7f0fc001ff80004 0xfafe1f8003ff0000

def z1245 : W := mkw 0x0ca1240039be1e65 0x219424800737c3cc 0xdff000001ffe3e64 0xfbfe000003ffc7cc

def z1246 : W := mkw 0x080124003bbe7f67 0x210024800777cfec 0x080000001f3e3e64 0x0100000003e7c7cc

def z1247 : W := mkw 0x020a4826c0000000 0x00414904d8000000 0x000ffc07e0000001 0x0001ff80fc000000

def z1248 : W := mkw 0x0801240031160a61 0x210024800622c14c 0x00000000113e0064 0x000000000227c00c

def z1249 : W := mkw 0x26ee9802c0000000 0x04ddd30058000000 0xc7fffc00e0000001 0xf8ffff801c000000

def z1250 : W := mkw 0x034e930280000000 0x0069d26050000000 0xa70fff87e0000003 0x74e1fff0fc000000

def z1251 : W := mkw 0x100124003ff7e851 0x8200248007fefd0a 0x100000001fffb804 0x0200000003fff700

def z1252 : W := mkw 0x0001240011160000 0x000024800222c000 0x9733fc001f3e0005 0xf2e67f8003e7c000

def z1253 : W := mkw 0x27fedbffc8a00102 0x04ffdb7ff9140020 0xe7ffffffe0c00183 0xfcfffffffc180030

def z1254 : W := mkw 0x0001642431160a61 0x00002c848622c14c 0x8833fde4f13e3e67 0xd1067fbc9e27c7cc

def z1255 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xf7ffffffe1c00007 0xfefffffffc380000

def z1256 : W := mkw 0x05b003d28aa87516 0x80b6007a51550ea2 0xfff003fb1ff87f9e 0xfffe007f63ff0ff3

def z1257 : W := mkw 0x27fedbffc2006000 0x04ffdb7ff8400c00 0xe7fffffffe003803 0xfcffffffffc00700

def z1258 : W := mkw 0x234edb3fc0000000 0x0469db67f8000000 0x200ffe1fe0000001 0x0401ffc3fc000000

def z1259 : W := mkw 0x16efb4091df782a8 0x42ddf68123bef055 0xfffffe1b1fffc7fd 0xffffffc363fff8ff

def z1260 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0xd7fffc071fff807d 0xfaffff80e3fff00f

def z1261 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xa73fff87e0000003 0x74e7fff0fc000000

def z1262 : W := mkw 0x001048e440000220 0x0002091c88000044 0x8833fde4e0000663 0xd1067fbc9c0000cc

def z1263 : W := mkw 0x2054d8ed40000000 0x040a9b1da8000000 0x8033fde4e0000003 0xd0067fbc9c000000

def z1264 : W := mkw 0x04f4d8e440000000 0x009e9b1c88000000 0xc0f3fde4e0000003 0xd81e7fbc9c000000

def z1265 : W := mkw 0x27fe9bdbc0000000 0x04ffd37b78000000 0xe7ffff9be0000001 0xfcfffff37c000000

def z1266 : W := mkw 0x27fedbffc00002a8 0x44ffdb7ff8000055 0xe7ffffffe0000783 0xfcfffffffc0000f0

def z1267 : W := mkw 0x180124003dbf1e65 0x2300248007b7e3cc 0x080000001f3e3e64 0x0100000003e7c7cc

def z1268 : W := mkw 0x27fedbffc0081506 0x04ffdb7ff80102a0 0xe7ffffffe0000783 0xfcfffffffc0000f0

def z1269 : W := mkw 0x05b04bf44aa87506 0x00b6097e89550ea0 0x8733fde4fe383803 0xd0e67fbc9fc70700

def z1270 : W := mkw 0x27fedbffc8a81506 0x04ffdb7ff91502a0 0xeffffffff1f83f87 0xfdfffffffe3f07f0

def z1271 : W := mkw 0x080124003fbf7f77 0xa100248007f7efee 0x180000001ffffffc 0x0300000003ffffff

def z1272 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0xbf0f03fffe07ffff 0x77e1e07fffc0ffff

def z1273 : W := mkw 0x091127c0371f7e75 0xa12224f806e3efce 0xbf3003e01f3ffe7e 0xf7e6007c03e7ffcf

def z1274 : W := mkw 0x27fedbffc8a81506 0x04ffdb7ff91502a0 0xe7ffffffe0380003 0xfcfffffffc070000

def z1275 : W := mkw 0x001048e440000000 0x0002091c88000000 0x8833fde4f0003807 0xd1067fbc9e000700

def z1276 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xc7f3fdfce0000003 0xd8fe7fbf9c000000

def z1277 : W := mkw 0x25f4dbfd4aa87506 0x04be9b7fa9550ea0 0xfff3fffcfff87f87 0xfffe7fff9fff0ff0

def z1278 : W := mkw 0x07fedbe6c0000000 0x00ffdb7cd8000000 0xe7ffffe7e0000003 0xfcfffffcfc000000

def z1279 : W := mkw 0x27fedbffc4010010 0x84ffdb7ff8802002 0xe7ffffffe001801b 0xfcfffffffc003003

def z1280 : W := mkw 0x26eed82fc0000000 0x04dddb05f8000000 0x47cffc07e0000001 0x28f9ff80fc000000

def z1281 : W := mkw 0x224ed82fc00002a8 0x4449db05f8000055 0x280ffe7fe00047fb 0x0501ffcffc0008ff

def z1282 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0x873ffde7e0000003 0xd0e7ffbcfc000000

def z1283 : W := mkw 0x08112cc0711e1c45 0x210225980e23c388 0x8833fde0f13e3e07 0xd1067fbc1e27c7c0

def z1284 : W := mkw 0x26eed82fc0000000 0x04dddb05f8000000 0x40fffc07e0000001 0x881fff80fc000000

def z1285 : W := mkw 0x100124003757e851 0x8200248006eafd0a 0x180000001e07f87c 0x0300000003c0ff0f

def z1286 : W := mkw 0x04b000c008a81404 0x0096001801150280 0xfff003f81ff87f86 0xfffe007f03ff0ff0

def z1287 : W := mkw 0x031a4be6c0000000 0x0063497cd8000000 0x8733fde4e0000003 0xd0e67fbc9c000000

def z1288 : W := mkw 0x21104bf6c0000000 0x0422097ed8000000 0x8033fde4e0000003 0xd0067fbc9c000000

def z1289 : W := mkw 0x15b127d03ffffd57 0x82b624fa07ffffaa 0xfff003f81ffffffe 0xfffe007f03ffffff

def z1290 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0xffcf03fffe07f87f 0xfff9e07fffc0ff0f

def z1291 : W := mkw 0x27fedbffc20877ae 0x44ffdb7ff8410ef5 0xefffffffe0007ffb 0xfdfffffffc000fff

def z1292 : W := mkw 0x16efb402bdf78851 0x82ddf68057bef10a 0xfffffe07ffffc07f 0xffffffc0fffff80f

def z1293 : W := mkw 0x04b048f448a81506 0x0096091e891502a0 0xc0f3fdfce1f80783 0xd81e7fbf9c3f00f0

def z1294 : W := mkw 0x0801240031568ae9 0x61002480062ad15d 0x0000000000078078 0x000000000000f00f

def z1295 : W := mkw 0x01104be6c0000000 0x0022097cd8000000 0xa033ffe7e0000003 0xd4067ffcfc000000

def z1296 : W := mkw 0x0801240031160a61 0x210024800622c14c 0x0800000001060664 0x010000000020c0cc

def z1297 : W := mkw 0x27fedbffc0408088 0x44ffdb7ff8081011 0xe7ffffffe001801b 0xfcfffffffc003003

def z1298 : W := mkw 0x030a030280000000 0x0061406050000000 0xa73fff87e0000003 0xf4e7fff0fc000000

def z1299 : W := mkw 0x24f4d8fd40000000 0x049e9b1fa8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1300 : W := mkw 0x04e4900008a00000 0x009c920001140000 0xd7f0fc001ff80004 0xfafe1f8003ff0000

def z1301 : W := mkw 0x37fedbffcca10000 0x06ffdb7ff9942000 0xe7ffffffee000003 0xfcfffffffdc00000

def z1302 : W := mkw 0x16efb4003df78841 0x02ddf68007bef108 0xd7fffc04ffff8065 0xfaffff809ffff00c

def z1303 : W := mkw 0x26eed82fc8a00000 0x04dddb05f9140000 0xd7fffc07fff80005 0xfaffff80ffff0000

def z1304 : W := mkw 0x201048efc0000000 0x0402091df8000000 0x8033fde7e0000003 0xd0067fbcfc000000

def z1305 : W := mkw 0x09104be462087e65 0x2122097c8c410fcc 0x280003e4e0007e62 0x0500007c9c000fcc

def z1306 : W := mkw 0x234edb2fc0000000 0x0469db65f8000000 0x070ffd87e0000001 0x40e1ffb0fc000000

def z1307 : W := mkw 0x030a4b26c0000000 0x00614964d8000000 0xa70fff87e0000003 0x74e1fff0fc000000

def z1308 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x873ffc001f3f8005 0xd0e7ff8003e7f000

def z1309 : W := mkw 0x04a000000aa87506 0x0094000001550ea0 0xfff002781ff87f86 0xfffe004f03ff0ff0

def z1310 : W := mkw 0x0044c02d004082a8 0x40089805a0081055 0xf8cc027f00c7c7ff 0x3f19804fe018f8ff

def z1311 : W := mkw 0x324ed82fc4418000 0x0649db05f8883000 0x000ffc07e0018001 0x0001ff80fc003000

def z1312 : W := mkw 0x16efb4001df782a8 0x42ddf68003bef055 0xd7fffc001fff8785 0xfaffff8003fff0f0

def z1313 : W := mkw 0x27fedbffc0408088 0x44ffdb7ff8081011 0xffffffffe0c7c1ff 0xfffffffffc18f83f

def z1314 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0xf7fffffffff83807 0xfeffffffffff0700

def z1315 : W := mkw 0x08016424311e1e65 0x21002c848623c3cc 0x08000064113e3e66 0x0100000c8227c7cc

def z1316 : W := mkw 0x08116ced711e1eed 0x61022d9dae23c3dd 0x8833fdfcf13e3fe7 0xd1067fbf9e27c7fc

def z1317 : W := mkw 0x224ed82fc0000000 0x0449db05f8000000 0x60cffe1fe0000001 0x2c19ffc3fc000000

def z1318 : W := mkw 0x36eed82fcce18000 0x06dddb05f99c3000 0x57cffc07eec18001 0x2af9ff80fdd83000

def z1319 : W := mkw 0x26fed8ffc8a81506 0x04dfdb1ff91502a0 0x40fffc7fe1f80781 0x881fff8ffc3f00f0

def z1320 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x2f0f0387fe07f87b 0x45e1e070ffc0ff0f

def z1321 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x57f3fc001fff8004 0xcafe7f8003fff000

def z1322 : W := mkw 0x16efb4091df78088 0x42ddf68123bef011 0xd7fffc181fff8185 0xfaffff8303fff030

def z1323 : W := mkw 0x05b04bf440000000 0x00b6097e88000000 0x8733fde4e0000003 0xd0e67fbc9c000000

def z1324 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xe7ffffffe007807b 0xfcfffffffc00f00f

def z1325 : W := mkw 0x220a5826c0000000 0x04414b04d8000000 0x0003fc04e0000001 0x00007f809c000000

def z1326 : W := mkw 0x0044e02d014282a8 0x40089c05a0285055 0xf8fce27f11ffc7ff 0xff1f9c4fe23ff8ff

def z1327 : W := mkw 0x0844ec2d415282a8 0x61089d85a82a5055 0xf8ccfe7f01c7c7ff 0xbf199fcfe038f8ff

def z1328 : W := mkw 0x27fedbffcaa06102 0x04ffdb7ff9540c20 0xffffffffefc04787 0xfffffffffdf808f0

def z1329 : W := mkw 0x225ed8efc0081404 0x044bdb1df8010280 0x883ffde7f1383e07 0xd107ffbcfe2707c0

def z1330 : W := mkw 0x0000402d000002a8 0x40000805a0000055 0xf8cc027f01c7c7ff 0xbf19804fe038f8ff

def z1331 : W := mkw 0x1a4ffc2d75578ae9 0x6349ff85aeaaf15d 0x000ffc07e0078079 0x0001ff80fc00f00f

def z1332 : W := mkw 0x234edb2fc0000000 0x0469db65f8000000 0xe7cfffffe0000003 0xfcf9fffffc000000

def z1333 : W := mkw 0x020b000034050841 0x004160000680a108 0xbf0f0387fe07f87f 0x77e1e070ffc0ff0f

def z1334 : W := mkw 0x21104bffc0000000 0x0422097ff8000000 0x2003ffffe0000003 0x04007ffffc000000

def z1335 : W := mkw 0x27fedbffc0000000 0x04ffdb7ff8000000 0xf7ffffffe0c04183 0xfefffffffc180830

def z1336 : W := mkw 0x001048e440000000 0x0002091c88000000 0x8033fde4f1380007 0xd0067fbc9e270000

def z1337 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0xffffffffeec07f83 0xfffffffffdd80ff0

def z1338 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x8033fde4f1383e03 0xd0067fbc9e2707c0

def z1339 : W := mkw 0x16eeb4000df38000 0x02ddd68001be7000 0xd7fcfc000fff8005 0xbaff9f8001fff000

def z1340 : W := mkw 0x27fedbffc4010000 0x04ffdb7ff8802000 0xf7ffffffee018003 0xfefffffffdc03000

def z1341 : W := mkw 0x030b0702b6156851 0x806160e056c2ad0a 0xbf3f1f87fe3ff87f 0x77e7e3f0ffc7ff0f

def z1342 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0x3f0f0387ee07f87b 0x27e1e070fdc0ff0f

def z1343 : W := mkw 0x16efb4001df78000 0x02ddf68003bef000 0x57fffc001eff8001 0x6affff8003dff000

def z1344 : W := mkw 0x08112cc0711e1e65 0x210225980e23c3cc 0x8833fd80f13e3e65 0xd1067fb01e27c7cc

def z1345 : W := mkw 0x27ee931b80000000 0x04fdd26370000000 0xe7ffff9fe0000003 0xfcfffff3fc000000

def z1346 : W := mkw 0x08012400315e9eed 0x61002480062bd3dd 0x08000000113fbe7c 0x010000000227f7cf

def z1347 : W := mkw 0x08116ce4711e1e65 0x21022d9c8e23c3cc 0x0833fde0f13e3e64 0xc1067fbc1e27c7cc

def z1348 : W := mkw 0x08114ce4701c1e65 0x2102299c8e0383cc 0x8833fde4f0383e63 0xd1067fbc9e0707cc

def z1349 : W := mkw 0x26fed8ffc0000000 0x04dfdb1ff8000000 0x003ffc07e0000001 0x0007ff80fc000000

def z1350 : W := mkw 0x27fedbffc0081404 0x04ffdb7ff8010280 0xfffffffff1f87f87 0xfffffffffe3f0ff0

def z1351 : W := mkw 0x0044c82d40000000 0x00089905a8000000 0xe0cffe7fe0000003 0xbc19ffcffc000000

def z1352 : W := mkw 0x001048e440081404 0x0002091c88010280 0x0030fc6001380600 0x80061f8c002700c0

def z1353 : W := mkw 0x06fed8ed40000000 0x00dfdb1da8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1354 : W := mkw 0x001048e440081404 0x0002091c88010280 0x8833fde4e0003e03 0xd1067fbc9c0007c0

def z1355 : W := mkw 0x27fedbffcaa06102 0x04ffdb7ff9540c20 0xfffffffffec07987 0xffffffffffd80f30

def z1356 : W := mkw 0x001008c040081404 0x0002011808010280 0x00331d80f0383800 0x400663b01e070700

def z1357 : W := mkw 0x07fedbf44aa87506 0x00ffdb7e89550ea0 0xfffffffcfff87f87 0xffffffff9fff0ff0

def z1358 : W := mkw 0x08012400315e9eed 0x61002480062bd3dd 0x0800000011fe3fe4 0x01000000023fc7fc

def z1359 : W := mkw 0x04b048e440000000 0x0096091c88000000 0xc7f3fde4e0000003 0xf8fe7fbc9c000000

def z1360 : W := mkw 0x001048e440000000 0x0002091c88000000 0x8833fde4e1000607 0xd1067fbc9c2000c0

def z1361 : W := mkw 0x26fed8fd40000000 0x04dfdb1fa8000000 0xc7fffdfce0000003 0xf8ffffbf9c000000

def z1362 : W := mkw 0x27fedbffc00002a8 0x44ffdb7ff8000055 0xe7ffffffe000007b 0xfcfffffffc00000f

def z1363 : W := mkw 0x081124c0311e1e65 0x210224980623c3cc 0x08300060113e3e64 0x8106000c0227c7cc

def z1364 : W := mkw 0x030b0302b6056851 0x8061606056c0ad0a 0xa70f0387fe07b87b 0x74e1e070ffc0f70f

def z1365 : W := mkw 0x07eed32f80000000 0x00fdda65f0000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1366 : W := mkw 0x17ee93128ee1e112 0x82fdd26251dc3c22 0x77cc021b0ec1c198 0x2ef9804361d83833

def z1367 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0xf7ffffffeff84783 0xfefffffffdff08f0

def z1368 : W := mkw 0x27fedbffcaa87506 0x04ffdb7ff9550ea0 0x47f3fdf8fff83f80 0xc8fe7fbf1fff07f0

def z1369 : W := mkw 0x2154cbffc0000000 0x042a997ff8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1370 : W := mkw 0x06efb40015170000 0x00ddf68002a2e000 0xd7fffc001f3f8005 0xfaffff8003e7f000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z0,z1,z2,z5,z8]),(0,[z9,z0,z1,z2,z10,z3,z5]),(0,[z0,z1,z2,z3,z11,z5,z6])],[(0,[z0,z1,z2,z3,z12,z5,z6]),(0,[z0,z1,z2,z13,z3,z5,z6]),(0,[z0,z1,z2,z14,z15,z5,z6]),(0,[z0,z1,z2,z3,z5,z16,z6]),(0,[z17,z0,z1,z2,z3,z18,z5])],[(0,[z0,z1,z2,z3,z19,z5,z6]),(0,[z17,z20,z0,z1,z2,z3,z5]),(0,[z1,z2,z3,z21,z5,z22,z6]),(0,[z0,z1,z2,z23,z3,z5,z8]),(0,[z0,z24,z1,z2,z3,z25,z5]),(0,[z0,z1,z2,z10,z3,z5,z26]),(0,[z17,z0,z1,z27,z2,z3,z5])],[(0,[z0,z2,z3,z5,z28,z6,z29]),(0,[z30,z0,z1,z2,z3,z5,z31]),(0,[z0,z32,z1,z2,z3,z5,z6]),(0,[z33,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z34,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z35,z6]),(0,[z0,z1,z2,z3,z5,z28,z8]),(0,[z0,z1,z2,z36,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z37,z29]),(0,[z38,z0,z1,z2,z3,z18,z6])],[(0,[z0,z1,z39,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z40,z6]),(0,[z0,z1,z2,z41,z3,z5,z6]),(0,[z42,z0,z1,z2,z10,z3,z5]),(0,[z0,z43,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z44])],[(0,[z0,z1,z45,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z46,z6]),(0,[z0,z47,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z48,z18,z5,z6]),(0,[z49,z0,z1,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z5,z50,z6]),(0,[z0,z1,z2,z3,z51,z52,z6]),(0,[z0,z1,z2,z53,z3,z52,z5]),(0,[z0,z54,z1,z2,z3,z5,z6]),(0,[z55,z0,z1,z2,z10,z3,z5])],[(0,[z56,z0,z1,z2,z3,z5,z6]),(0,[z57,z0,z1,z2,z48,z5,z6]),(0,[z0,z1,z2,z3,z22,z58,z6]),(0,[z0,z1,z2,z59,z3,z5,z6])],[(0,[z0,z60,z1,z2,z3,z5,z6]),(0,[z0,z61,z1,z2,z10,z3,z5]),(0,[z0,z1,z62,z2,z3,z5,z6]),(0,[z63,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z64,z6]),(0,[z0,z65,z2,z23,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z66,z6]),(0,[z0,z1,z2,z10,z3,z67,z5]),(0,[z0,z1,z2,z3,z68,z5,z6]),(0,[z0,z1,z2,z3,z69,z5,z6]),(1,[z38,z0,z1,z2,z26,z6]),(0,[z0,z1,z2,z3,z5,z6,z70]),(0,[z0,z1,z2,z3,z5,z6,z71])],[(0,[z0,z1,z72,z23,z3,z5,z6]),(1,[z0,z1,z73,z2,z3,z5]),(0,[z0,z1,z74,z2,z3,z5,z6]),(0,[z75,z0,z1,z2,z3,z5,z31]),(0,[z0,z1,z76,z2,z3,z5,z6]),(0,[z0,z77,z1,z2,z3,z5,z6])],[(0,[z78,z0,z1,z2,z3,z5,z31]),(0,[z79,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z80,z6]),(0,[z75,z0,z1,z2,z81,z3,z5]),(0,[z0,z1,z2,z3,z5,z82,z8]),(0,[z0,z1,z2,z3,z83,z5,z6]),(0,[z84,z0,z1,z2,z3,z5,z6])],[(0,[z85,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z86]),(0,[z17,z0,z1,z2,z3,z5,z22]),(0,[z0,z87,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z88]),(0,[z89,z0,z1,z2,z3,z5,z6])],[(0,[z90,z0,z1,z2,z3,z64,z6]),(0,[z0,z1,z2,z3,z5,z91,z6]),(0,[z17,z0,z1,z2,z13,z3,z5]),(0,[z0,z1,z2,z3,z5,z92,z6]),(0,[z0,z93,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z94])]],
   [[(0,[z0,z1,z2,z3,z5,z95,z6]),(0,[z0,z96,z1,z2,z3,z5,z6]),(0,[z0,z97,z1,z2,z3,z5,z6]),(0,[z75,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z98,z5,z6]),(0,[z33,z17,z0,z1,z2,z3,z5])],[(0,[z99,z0,z1,z2,z3,z5,z31]),(0,[z0,z1,z100,z2,z3,z5,z31]),(0,[z0,z101,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z102,z5,z6]),(0,[z0,z1,z2,z3,z103,z5,z6]),(0,[z0,z1,z2,z3,z5,z8,z104]),(1,[z0,z1,z2,z3,z25,z58])],[(0,[z0,z105,z1,z2,z3,z5,z6]),(0,[z0,z106,z1,z2,z3,z5,z107]),(0,[z0,z108,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z8,z109])],[(0,[z0,z1,z2,z3,z5,z110,z6]),(0,[z0,z1,z2,z3,z111,z5,z6]),(0,[z20,z0,z1,z2,z3,z5,z6]),(0,[z0,z106,z1,z2,z10,z3,z5]),(0,[z0,z112,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z113,z3,z5,z6]),(0,[z0,z114,z1,z2,z3,z5,z6]),(0,[z0,z61,z1,z2,z3,z115,z6]),(1,[z0,z1,z2,z116,z3,z8]),(0,[z9,z0,z1,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z5,z117,z31]),(0,[z0,z1,z2,z10,z3,z118,z5])],[(0,[z0,z24,z1,z2,z10,z3,z5]),(0,[z0,z1,z2,z119,z3,z5,z6]),(0,[z17,z0,z1,z120,z2,z5,z6]),(0,[z17,z0,z1,z2,z3,z5,z109])],[(0,[z57,z1,z2,z48,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z5,z28]),(1,[z17,z0,z1,z120,z2,z5]),(1,[z0,z1,z2,z81,z3,z121])],[(0,[z99,z0,z1,z2,z3,z122,z6]),(0,[z0,z1,z2,z3,z5,z123,z6]),(0,[z7,z0,z1,z2,z5,z6,z8]),(0,[z0,z1,z2,z81,z3,z5,z8])],[(0,[z0,z124,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z125]),(0,[z0,z1,z2,z3,z25,z5,z121])]],
   [[(0,[z0,z126,z1,z2,z3,z5,z6]),(0,[z127,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z128,z5,z6]),(0,[z129,z49,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z130,z5,z6]),(0,[z0,z131,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z10,z3,z115,z5])],[(0,[z0,z1,z2,z3,z132,z5,z6]),(0,[z0,z133,z1,z2,z10,z3,z5]),(0,[z42,z0,z1,z2,z3,z5,z31]),(0,[z17,z0,z1,z2,z3,z5,z6])],[(0,[z134,z0,z1,z2,z3,z5,z6]),(0,[z0,z135,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z136,z6]),(1,[z0,z1,z2,z10,z5,z137])],[(0,[z99,z0,z138,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z5,z8]),(1,[z20,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z139,z5,z6]),(1,[z0,z1,z120,z140,z5,z6]),(0,[z0,z1,z120,z2,z140,z5,z6]),(0,[z55,z0,z1,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z25,z5,z31]),(0,[z0,z1,z2,z3,z5,z141,z6]),(0,[z85,z17,z0,z1,z2,z3,z5]),(0,[z0,z142,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z143,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z144]),(0,[z0,z145,z1,z2,z18,z5,z6]),(0,[z0,z1,z2,z3,z5,z146,z6]),(0,[z0,z1,z2,z147,z3,z5,z6])],[(0,[z0,z1,z148,z2,z3,z5,z6]),(0,[z0,z106,z2,z23,z3,z5,z6]),(0,[z42,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z149,z6]),(0,[z150,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z151,z5,z6]),(1,[z0,z1,z2,z152,z3,z5]),(0,[z0,z61,z1,z2,z3,z5,z31]),(0,[z0,z1,z2,z10,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z31,z153])],[(0,[z0,z154,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z12,z6]),(0,[z0,z1,z2,z3,z5,z6,z104]),(0,[z0,z1,z2,z3,z5,z6,z155]),(1,[z0,z1,z2,z156,z5,z6])],[(0,[z17,z57,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z157,z6]),(1,[z1,z2,z158,z3,z5,z6]),(0,[z0,z1,z2,z5,z159,z160,z6]),(0,[z55,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z161,z6]),(0,[z0,z1,z2,z162,z3,z5,z6])]],
   [[(1,[z0,z1,z2,z3,z5,z163]),(0,[z0,z1,z2,z3,z5,z164,z6]),(0,[z0,z165,z1,z2,z3,z5,z6]),(0,[z166,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z167,z5,z6]),(0,[z0,z1,z2,z3,z5,z168,z6]),(0,[z0,z61,z1,z2,z3,z5,z8]),(0,[z17,z0,z1,z2,z3,z5,z58])],[(0,[z17,z78,z0,z1,z2,z3,z5]),(0,[z169,z0,z1,z2,z3,z5,z6]),(0,[z30,z0,z1,z2,z52,z5,z6]),(0,[z0,z1,z170,z2,z10,z3,z5])],[(0,[z171,z0,z1,z2,z10,z3,z5]),(0,[z0,z1,z2,z15,z52,z5,z6]),(0,[z0,z1,z2,z172,z3,z5,z6]),(0,[z129,z0,z1,z2,z173,z5,z6]),(1,[z0,z1,z2,z3,z5,z107]),(0,[z174,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z65,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z175,z6]),(0,[z176,z0,z1,z2,z10,z3,z5]),(0,[z0,z1,z177,z2,z3,z5,z6]),(0,[z178,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z10,z3,z179,z5]),(0,[z0,z1,z2,z3,z180,z5,z6]),(0,[z0,z1,z181,z2,z3,z5,z182]),(0,[z0,z1,z2,z3,z183,z5,z6]),(1,[z0,z1,z2,z3,z184,z8]),(1,[z0,z1,z2,z10,z3,z5])],[(0,[z0,z1,z2,z3,z185,z5,z6]),(0,[z0,z1,z2,z3,z21,z5,z31]),(0,[z0,z1,z2,z3,z186,z5,z6]),(0,[z0,z1,z2,z3,z187,z5,z6]),(1,[z0,z1,z2,z3,z188,z6]),(0,[z0,z24,z2,z3,z5,z6,z29]),(0,[z75,z0,z1,z2,z3,z5,z29]),(0,[z189,z0,z1,z2,z3,z5,z6]),(0,[z190,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z181,z2,z81,z3,z6]),(0,[z0,z1,z2,z191,z3,z5,z6])],[(0,[z0,z1,z2,z3,z21,z160,z6]),(0,[z0,z1,z2,z3,z5,z28,z192]),(0,[z0,z106,z1,z2,z3,z5,z31]),(1,[z0,z193,z2,z3,z160,z6]),(0,[z0,z1,z2,z3,z5,z194,z6]),(0,[z0,z1,z2,z195,z3,z5,z6]),(0,[z30,z17,z0,z1,z2,z3,z5]),(0,[z17,z17,z0,z1,z2,z3,z5])],[(0,[z129,z0,z1,z2,z156,z5,z6]),(0,[z196,z0,z1,z2,z3,z5,z6]),(0,[z0,z197,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z68,z5,z160]),(0,[z0,z24,z1,z2,z3,z5,z31]),(0,[z198,z0,z1,z2,z10,z3,z5])]],
   [[(0,[z90,z0,z1,z2,z10,z3,z5]),(0,[z57,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z48,z67,z5,z6]),(0,[z199,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z200]),(0,[z0,z1,z201,z2,z3,z5,z6]),(0,[z0,z1,z202,z2,z3,z5,z6]),(1,[z9,z0,z1,z3,z5,z31])],[(0,[z0,z1,z72,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z203,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z204]),(0,[z0,z1,z2,z3,z5,z153,z6])],[(0,[z0,z106,z1,z2,z3,z5,z8]),(0,[z0,z193,z1,z2,z3,z5,z8]),(0,[z75,z0,z1,z2,z3,z25,z5]),(0,[z0,z1,z2,z3,z5,z205,z6]),(0,[z17,z0,z1,z2,z3,z5,z137]),(0,[z0,z1,z2,z3,z25,z58,z6])],[(0,[z0,z97,z1,z2,z3,z15,z5]),(0,[z0,z206,z1,z2,z3,z5,z6])],[(0,[z0,z133,z1,z2,z3,z5,z31])],[(0,[z129,z0,z1,z2,z10,z3,z5]),(0,[z207,z0,z1,z2,z3,z5,z6]),(0,[z208,z0,z1,z2,z3,z5,z6]),(0,[z0,z209,z1,z2,z3,z160,z6]),(0,[z0,z1,z181,z2,z3,z5,z31]),(0,[z0,z1,z2,z210,z3,z5,z6])],[(0,[z49,z0,z1,z2,z3,z5,z192]),(0,[z0,z1,z181,z2,z3,z160,z6]),(0,[z211,z0,z1,z2,z5,z160,z6]),(1,[z0,z1,z2,z5,z159,z6]),(0,[z0,z209,z1,z2,z3,z179,z6]),(1,[z0,z1,z2,z3,z5,z182]),(0,[z0,z1,z2,z3,z212,z5,z6]),(1,[z0,z1,z2,z3,z5,z141])],[(0,[z0,z1,z181,z2,z3,z179,z6]),(0,[z0,z61,z1,z2,z3,z5,z44]),(0,[z0,z1,z2,z213,z10,z3,z5])]],
   [[(0,[z214,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z48,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z215]),(0,[z0,z1,z2,z3,z22,z46,z6]),(0,[z0,z133,z1,z2,z3,z5,z8]),(0,[z0,z209,z193,z2,z3,z5,z6]),(1,[z0,z1,z76,z3,z5,z8])],[(0,[z216,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z140,z48,z5,z6]),(0,[z0,z1,z217,z2,z3,z5,z6]),(0,[z17,z0,z218,z1,z2,z3,z5])],[(0,[z0,z219,z1,z2,z3,z5,z6]),(1,[z0,z1,z220,z3,z5,z6]),(0,[z0,z106,z133,z2,z3,z5,z6]),(1,[z0,z61,z1,z3,z115,z6]),(0,[z7,z0,z1,z2,z3,z5,z8])],[(0,[z221,z0,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z5,z46]),(0,[z0,z1,z222,z2,z3,z5,z6]),(0,[z223,z0,z1,z2,z3,z5,z6])],[(0,[z17,z0,z1,z2,z3,z15,z5]),(0,[z0,z1,z2,z3,z21,z58,z6]),(0,[z0,z1,z2,z3,z224,z5,z6]),(0,[z0,z1,z120,z2,z10,z3,z5])],[(0,[z0,z1,z2,z15,z18,z5,z6]),(0,[z0,z1,z2,z14,z3,z5,z31]),(0,[z17,z0,z1,z2,z3,z5,z160]),(0,[z0,z1,z2,z3,z179,z5,z31]),(0,[z190,z0,z1,z2,z140,z3,z5]),(0,[z0,z1,z225,z2,z3,z5,z6])],[(0,[z90,z0,z1,z220,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z226,z6]),(0,[z0,z1,z2,z48,z5,z137,z6]),(0,[z0,z100,z2,z23,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z227,z6])],[(0,[z176,z0,z1,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z5,z228,z6]),(0,[z0,z1,z2,z3,z5,z44,z6]),(1,[z0,z1,z2,z3,z5,z31]),(0,[z0,z1,z2,z10,z3,z25,z5])]],
   [[(0,[z99,z176,z1,z2,z3,z5,z6]),(1,[z176,z1,z72,z3,z5,z6]),(0,[z229,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z230,z5,z6]),(0,[z0,z1,z231,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z67,z5,z6]),(0,[z232,z0,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z5,z233])],[(1,[z42,z0,z2,z67,z5,z6]),(0,[z0,z1,z120,z140,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z234,z6]),(0,[z0,z1,z2,z3,z235,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z236]),(0,[z0,z1,z2,z3,z25,z5,z58])],[(0,[z237,z0,z1,z2,z3,z5,z6]),(0,[z171,z0,z1,z2,z3,z5,z8]),(0,[z238,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z160,z8])],[(0,[z90,z0,z1,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z239,z5,z6]),(0,[z0,z1,z2,z240,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z31,z31])],[(1,[z0,z1,z2,z3,z122,z6]),(0,[z241,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z242,z2,z3,z5,z6]),(0,[z0,z145,z1,z2,z67,z5,z6]),(0,[z0,z1,z243,z2,z3,z5,z6]),(0,[z0,z1,z181,z2,z3,z58,z6])],[(1,[z0,z1,z2,z244,z5,z6]),(0,[z0,z1,z2,z3,z18,z5,z8]),(0,[z0,z1,z2,z3,z5,z6,z245]),(0,[z0,z1,z2,z3,z5,z246,z6])],[(0,[z247,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z248,z3,z5,z6]),(0,[z0,z1,z2,z249,z3,z5,z6]),(0,[z0,z250,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z251,z6]),(0,[z0,z1,z120,z2,z3,z5,z252]),(0,[z0,z1,z2,z253,z3,z5,z6])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z0,z1,z254,z2,z3,z5,z6]),(0,[z0,z255,z1,z2,z3,z5,z6]),(0,[z0,z256,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z14,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z257,z6]),(0,[z0,z1,z2,z3,z258,z5,z6]),(0,[z0,z1,z2,z3,z259,z5,z6]),(0,[z129,z0,z1,z2,z3,z5,z31]),(0,[z38,z0,z209,z1,z2,z3,z6]),(0,[z0,z24,z1,z2,z3,z5,z29]),(0,[z0,z1,z2,z3,z5,z260,z6]),(0,[z0,z1,z2,z261,z3,z26,z6]),(0,[z0,z1,z2,z5,z137,z6,z109])],[(0,[z90,z0,z1,z2,z244,z5,z6]),(1,[z0,z138,z2,z3,z5,z6]),(0,[z262,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z263,z5,z6]),(0,[z0,z1,z2,z3,z25,z5,z192]),(0,[z0,z1,z2,z23,z3,z5,z31]),(0,[z0,z1,z2,z3,z264,z5,z6])],[(0,[z0,z209,z1,z2,z261,z3,z6]),(0,[z0,z1,z2,z81,z10,z3,z5])],[(0,[z0,z1,z2,z3,z265,z5,z6]),(0,[z266,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z267,z31]),(0,[z0,z1,z2,z3,z5,z268,z6])],[(0,[z99,z0,z1,z72,z3,z5,z6]),(0,[z0,z1,z100,z72,z3,z5,z6]),(0,[z0,z269,z1,z2,z3,z5,z6]),(0,[z129,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z270,z3,z5,z6]),(0,[z0,z145,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z58,z31]),(0,[z0,z1,z2,z3,z58,z6,z121]),(0,[z0,z1,z271,z2,z3,z5,z6])],[(0,[z171,z0,z1,z2,z15,z5,z6]),(0,[z0,z1,z2,z3,z5,z37,z6]),(1,[z0,z1,z2,z3,z5,z272])],[(0,[z0,z1,z2,z3,z179,z22,z6]),(0,[z0,z1,z2,z3,z5,z22,z31]),(0,[z0,z1,z2,z3,z5,z137,z6])],[(1,[z90,z65,z2,z3,z5,z6]),(0,[z273,z0,z1,z2,z3,z5,z6]),(0,[z0,z274,z1,z2,z3,z5,z6]),(0,[z0,z1,z120,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z275,z5,z6]),(0,[z276,z0,z1,z2,z3,z5,z6]),(0,[z238,z17,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z233,z6]),(0,[z0,z277,z1,z2,z10,z3,z5]),(0,[z0,z1,z2,z278,z3,z5,z6])]],
   [[(0,[z90,z99,z1,z2,z3,z5,z6]),(0,[z279,z0,z1,z2,z3,z5,z280]),(0,[z0,z1,z2,z3,z5,z281,z6]),(1,[z0,z133,z100,z3,z5,z6]),(0,[z282,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z283,z5,z6]),(0,[z0,z1,z2,z3,z5,z58,z8]),(0,[z38,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z284,z5,z6])],[(0,[z0,z285,z1,z2,z3,z5,z6]),(0,[z9,z0,z1,z3,z5,z31,z6]),(0,[z0,z1,z2,z10,z10,z3,z5])],[(0,[z286,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z22,z8]),(0,[z0,z1,z2,z3,z5,z280,z6]),(0,[z0,z1,z2,z10,z3,z21,z5]),(0,[z0,z133,z1,z2,z3,z287,z6]),(0,[z42,z0,z1,z2,z3,z188,z6]),(0,[z42,z0,z1,z2,z18,z5,z6]),(0,[z0,z1,z2,z288,z3,z67,z5])],[(0,[z0,z1,z289,z2,z3,z5,z6]),(1,[z0,z1,z2,z288,z3,z5]),(0,[z0,z290,z1,z2,z3,z5,z6]),(0,[z0,z1,z120,z2,z3,z5,z8]),(0,[z38,z0,z1,z2,z3,z5,z8])],[(1,[z0,z1,z2,z3,z5,z291]),(0,[z0,z292,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z293,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z26,z6])],[(0,[z294,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z158,z23,z3,z5,z6]),(0,[z0,z1,z2,z295,z3,z5,z6]),(0,[z0,z296,z1,z2,z3,z5,z6]),(0,[z0,z297,z1,z2,z3,z5,z6])],[(0,[z0,z298,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z299,z5,z6])],[(0,[z0,z1,z2,z3,z300,z5,z6]),(0,[z279,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z301,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z140,z3,z5,z6]),(0,[z0,z1,z2,z302,z3,z5,z6])],[(0,[z99,z0,z1,z2,z303,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z304]),(1,[z279,z1,z2,z3,z21,z6])],[(0,[z0,z1,z2,z13,z10,z3,z5]),(0,[z0,z1,z2,z3,z305,z5,z6]),(0,[z0,z1,z2,z3,z5,z306,z6]),(0,[z0,z1,z2,z116,z3,z6,z8]),(0,[z0,z1,z2,z3,z5,z6,z307])],[(0,[z308,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z309]),(0,[z0,z1,z2,z3,z5,z31,z29]),(1,[z30,z17,z0,z1,z2,z5]),(1,[z0,z1,z310,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z311,z6])],[(0,[z78,z219,z1,z2,z3,z5,z6]),(0,[z99,z0,z1,z2,z3,z5,z312]),(0,[z0,z1,z2,z15,z67,z5,z6]),(0,[z0,z1,z2,z313,z3,z5,z6]),(0,[z0,z1,z314,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z287,z6]),(0,[z0,z193,z2,z3,z5,z160,z6]),(0,[z0,z1,z2,z81,z3,z5,z31])],[(0,[z0,z1,z2,z315,z3,z5,z6]),(1,[z0,z1,z2,z3,z316,z6]),(0,[z0,z193,z1,z2,z10,z3,z5]),(0,[z0,z1,z317,z2,z3,z5,z6]),(0,[z318,z0,z1,z2,z3,z5,z6]),(0,[z319,z0,z1,z2,z10,z3,z5])],[(0,[z0,z1,z2,z3,z5,z320,z6]),(0,[z321,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z322]),(0,[z0,z1,z2,z323,z3,z5,z6]),(0,[z42,z0,z145,z2,z3,z5,z6]),(0,[z324,z0,z1,z2,z3,z5,z8])]],
   [[(1,[z0,z1,z2,z3,z5,z325]),(0,[z0,z1,z326,z2,z3,z5,z6]),(1,[z190,z0,z1,z2,z3,z5]),(0,[z0,z61,z1,z2,z81,z3,z6]),(0,[z0,z1,z2,z116,z3,z5,z8]),(0,[z0,z1,z2,z10,z3,z5,z121]),(0,[z0,z1,z2,z3,z327,z5,z6])],[(0,[z0,z1,z2,z220,z3,z5,z6]),(0,[z99,z219,z1,z2,z3,z5,z6]),(0,[z328,z0,z1,z2,z3,z5,z6]),(0,[z57,z0,z1,z2,z3,z185,z6]),(0,[z211,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z28,z6]),(0,[z0,z1,z2,z3,z5,z329,z6]),(0,[z330,z0,z1,z2,z3,z5,z8])],[(0,[z331,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z5,z31]),(0,[z0,z1,z2,z3,z5,z6,z332]),(0,[z0,z333,z1,z2,z3,z5,z6]),(0,[z0,z334,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z335]),(0,[z0,z1,z2,z10,z3,z18,z5])],[(0,[z0,z1,z2,z3,z5,z336,z6]),(0,[z0,z1,z2,z3,z5,z35,z6]),(0,[z0,z1,z2,z3,z21,z46,z6]),(0,[z337,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z338,z5,z6])],[(0,[z90,z0,z1,z2,z3,z5,z325]),(0,[z339,z0,z1,z2,z3,z5,z6]),(0,[z30,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z340,z3,z5,z6]),(0,[z0,z1,z2,z10,z3,z5,z31])],[(0,[z0,z1,z2,z3,z179,z21,z6]),(0,[z0,z1,z140,z3,z52,z5,z6])],[(0,[z0,z1,z2,z3,z341,z5,z6]),(0,[z0,z1,z2,z2,z3,z5,z31]),(0,[z0,z342,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z343,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z86]),(0,[z0,z344,z1,z2,z3,z5,z6]),(0,[z345,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z73,z2,z3,z5,z6]),(0,[z346,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z347,z6]),(0,[z0,z348,z1,z2,z3,z5,z6])],[(0,[z17,z0,z219,z1,z2,z3,z5]),(0,[z1,z2,z48,z3,z15,z5,z6]),(0,[z0,z349,z1,z2,z3,z5,z6]),(0,[z0,z350,z1,z2,z3,z5,z6]),(1,[z57,z1,z2,z48,z5,z6]),(0,[z49,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z31,z192]),(0,[z0,z61,z1,z2,z3,z160,z6]),(0,[z0,z351,z1,z2,z3,z5,z6]),(0,[z75,z0,z1,z2,z3,z5,z28]),(0,[z352,z0,z1,z2,z10,z3,z5]),(0,[z0,z1,z2,z3,z353,z5,z6]),(0,[z0,z354,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z64,z6]),(0,[z0,z355,z1,z2,z3,z5,z6]),(0,[z0,z1,z356,z2,z3,z5,z6]),(0,[z0,z1,z2,z357,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z5,z37]),(0,[z0,z106,z1,z23,z3,z5,z6]),(0,[z0,z61,z1,z2,z3,z179,z6]),(0,[z30,z0,z1,z2,z5,z137,z6]),(0,[z0,z1,z2,z2,z3,z5,z8]),(0,[z0,z358,z1,z2,z3,z5,z31])],[(0,[z0,z1,z2,z15,z5,z137,z6]),(0,[z0,z1,z359,z2,z3,z5,z6]),(0,[z0,z1,z2,z360,z3,z5,z6]),(0,[z0,z1,z181,z2,z3,z46,z6]),(0,[z361,z0,z1,z2,z3,z5,z6]),(0,[z362,z0,z1,z2,z3,z5,z31])],[(0,[z0,z1,z2,z3,z363,z5,z6]),(0,[z0,z1,z2,z364,z3,z5,z6]),(1,[z0,z1,z2,z3,z187,z6]),(0,[z0,z1,z2,z365,z3,z5,z6])],[(0,[z0,z1,z2,z366,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z367]),(0,[z0,z1,z2,z3,z316,z67,z6]),(0,[z0,z1,z2,z368,z3,z5,z6]),(0,[z75,z0,z1,z2,z3,z5,z6]),(0,[z369,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z370,z6])],[(0,[z78,z0,z1,z2,z3,z5,z6]),(0,[z0,z371,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z309,z6]),(0,[z129,z0,z1,z2,z3,z5,z192]),(0,[z0,z1,z2,z3,z372,z5,z6]),(0,[z0,z1,z120,z2,z52,z5,z6]),(0,[z0,z1,z2,z3,z51,z5,z6]),(0,[z0,z1,z2,z3,z5,z373,z6])],[(0,[z0,z1,z2,z3,z5,z374,z6]),(0,[z0,z1,z2,z10,z3,z5,z22]),(0,[z49,z0,z1,z2,z3,z5,z37]),(0,[z0,z1,z2,z3,z5,z375,z6]),(0,[z0,z1,z2,z152,z3,z5,z6]),(0,[z0,z1,z376,z2,z3,z5,z6])]],
   [[(0,[z0,z133,z1,z23,z3,z5,z6]),(0,[z30,z0,z1,z3,z52,z5,z6]),(1,[z0,z1,z2,z116,z3,z6])],[(0,[z0,z1,z2,z13,z3,z5,z8]),(0,[z0,z193,z1,z2,z3,z5,z31]),(0,[z30,z0,z1,z2,z3,z5,z377]),(0,[z0,z1,z378,z2,z3,z5,z6])],[(0,[z379,z0,z1,z2,z3,z5,z6]),(0,[z99,z0,z1,z2,z3,z5,z6]),(0,[z176,z0,z1,z72,z3,z5,z6]),(0,[z0,z380,z1,z2,z3,z5,z6]),(0,[z0,z1,z100,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z52,z5,z31]),(0,[z0,z381,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z81,z3,z25,z6])],[(1,[z0,z97,z1,z2,z3,z5]),(0,[z0,z1,z2,z173,z3,z5,z6]),(0,[z42,z0,z2,z3,z67,z5,z6]),(0,[z0,z1,z2,z3,z382,z5,z6]),(0,[z0,z1,z2,z3,z5,z46,z31]),(0,[z0,z32,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z383,z3,z5,z6])],[(0,[z0,z1,z2,z3,z384,z5,z6]),(0,[z0,z1,z2,z3,z5,z117,z6]),(0,[z30,z0,z1,z120,z3,z5,z6]),(0,[z17,z0,z1,z2,z140,z3,z5]),(0,[z9,z0,z1,z2,z3,z5,z6])],[(0,[z99,z0,z1,z2,z265,z5,z6]),(0,[z0,z1,z2,z3,z385,z5,z6]),(0,[z0,z1,z2,z3,z179,z18,z6]),(0,[z0,z1,z2,z3,z5,z8,z386]),(0,[z0,z1,z2,z387,z3,z5,z6])],[(0,[z388,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z389,z6]),(0,[z390,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z10,z48,z3,z5]),(0,[z0,z1,z391,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z52,z5,z8]),(0,[z0,z1,z2,z3,z5,z6,z392])],[(1,[z0,z1,z2,z393,z3,z5]),(0,[z0,z1,z2,z14,z48,z5,z6]),(0,[z20,z1,z2,z3,z5,z22,z6]),(0,[z279,z0,z1,z2,z128,z5,z6]),(0,[z0,z394,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z46,z8]),(0,[z0,z61,z1,z2,z3,z58,z6])]],
   [[(0,[z395,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z396]),(1,[z7,z0,z1,z2,z3,z5])],[(0,[z99,z0,z1,z13,z3,z5,z6]),(0,[z0,z1,z100,z13,z3,z5,z6]),(0,[z397,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z163]),(0,[z56,z0,z1,z2,z3,z5,z8])],[(0,[z42,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z398,z2,z3,z5,z6]),(0,[z75,z17,z0,z1,z2,z3,z5]),(0,[z399,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z400,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z401]),(0,[z17,z0,z1,z72,z2,z3,z5]),(0,[z402,z0,z1,z2,z3,z5,z6]),(0,[z0,z403,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z18,z5,z141]),(0,[z0,z1,z2,z404,z3,z5,z6]),(0,[z0,z1,z2,z81,z3,z5,z58])],[(0,[z55,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z107]),(0,[z0,z405,z1,z2,z3,z5,z6]),(0,[z0,z1,z76,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z25,z5,z6])],[(0,[z406,z0,z1,z2,z3,z5,z6]),(0,[z90,z1,z65,z2,z3,z5,z6]),(0,[z0,z1,z2,z10,z3,z5,z29])],[(0,[z0,z1,z407,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z408,z5,z6]),(0,[z176,z1,z72,z2,z3,z5,z6]),(0,[z409,z0,z1,z2,z3,z5,z6]),(0,[z410,z0,z1,z2,z3,z5,z6]),(0,[z411,z0,z1,z2,z3,z5,z6]),(0,[z0,z61,z1,z2,z261,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z412]),(0,[z0,z1,z2,z3,z5,z413,z6])],[(1,[z0,z1,z2,z303,z5,z6]),(0,[z99,z17,z0,z1,z2,z3,z5]),(0,[z279,z0,z1,z2,z3,z5,z163]),(0,[z38,z0,z1,z2,z10,z3,z5])]],
   [[(0,[z0,z1,z2,z414,z3,z5,z6]),(0,[z0,z1,z2,z415,z3,z5,z6]),(0,[z0,z1,z2,z3,z416,z5,z6])],[(0,[z171,z0,z1,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z5,z160,z31]),(0,[z0,z1,z2,z3,z115,z5,z31]),(1,[z0,z1,z2,z3,z184,z6]),(0,[z9,z17,z0,z1,z2,z3,z5])],[(0,[z90,z1,z72,z2,z3,z5,z6]),(0,[z0,z417,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z25,z5,z37]),(0,[z418,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z386]),(0,[z0,z1,z2,z3,z5,z419,z6]),(0,[z0,z1,z3,z5,z31,z6,z8]),(0,[z0,z1,z2,z3,z5,z31,z121]),(0,[z0,z1,z2,z10,z3,z5,z58])],[(1,[z0,z1,z2,z3,z5,z312]),(0,[z20,z0,z1,z2,z3,z5,z8]),(0,[z279,z0,z1,z2,z10,z3,z5]),(0,[z0,z1,z2,z81,z3,z5,z192]),(0,[z0,z420,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z179,z5,z160,z6]),(0,[z0,z1,z2,z3,z5,z184,z8]),(0,[z0,z1,z2,z3,z421,z5,z6]),(0,[z0,z1,z2,z10,z261,z3,z5])],[(0,[z0,z1,z2,z3,z422,z5,z6]),(0,[z0,z24,z1,z2,z3,z5,z28]),(0,[z17,z0,z1,z2,z3,z115,z5]),(1,[z0,z1,z2,z5,z423,z6]),(0,[z0,z1,z2,z3,z18,z5,z31])],[(0,[z0,z1,z2,z3,z5,z424,z6]),(0,[z0,z1,z425,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z426,z6]),(0,[z0,z1,z2,z81,z3,z21,z6]),(0,[z0,z1,z2,z3,z115,z5,z8])],[(0,[z0,z1,z2,z3,z21,z5,z6]),(0,[z0,z1,z2,z3,z5,z427,z6]),(0,[z0,z1,z2,z3,z5,z428,z6])],[(0,[z0,z106,z1,z2,z3,z5,z6]),(0,[z42,z17,z0,z1,z2,z3,z5]),(0,[z17,z0,z209,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z252]),(0,[z0,z1,z2,z3,z5,z8,z8]),(1,[z0,z1,z2,z293,z3,z5]),(0,[z17,z0,z429,z1,z2,z3,z5])]],
   [[(0,[z430,z0,z1,z2,z3,z5,z6]),(1,[z0,z145,z2,z14,z5,z6]),(0,[z0,z24,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z431,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z432,z6]),(0,[z17,z0,z1,z2,z3,z52,z5]),(0,[z0,z1,z2,z3,z5,z433,z6]),(0,[z0,z1,z2,z3,z5,z434,z6]),(0,[z55,z17,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z10,z3,z5,z192]),(0,[z0,z1,z100,z2,z3,z5,z367]),(0,[z0,z1,z2,z261,z3,z5,z31]),(0,[z17,z0,z1,z2,z435,z3,z5])],[(0,[z17,z0,z24,z1,z2,z3,z5]),(0,[z0,z1,z2,z436,z3,z5,z6]),(0,[z0,z61,z1,z2,z3,z5,z335]),(0,[z0,z1,z2,z10,z3,z5,z137])],[(0,[z437,z0,z1,z2,z3,z5,z6]),(0,[z438,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z439,z5,z6]),(1,[z0,z1,z2,z3,z68,z5]),(0,[z0,z1,z440,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z8,z441]),(0,[z442,z0,z1,z2,z3,z5,z6])],[(0,[z0,z133,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z23,z3,z5]),(0,[z443,z0,z1,z2,z3,z5,z6]),(0,[z0,z209,z1,z2,z3,z5,z6]),(1,[z211,z0,z1,z2,z5,z6])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z444,z5,z6]),(0,[z0,z1,z445,z2,z3,z5,z6]),(0,[z0,z1,z446,z2,z3,z5,z6]),(1,[z30,z0,z1,z52,z5,z6]),(0,[z0,z1,z181,z2,z3,z5,z6]),(0,[z0,z1,z181,z2,z261,z3,z6]),(0,[z0,z1,z2,z261,z3,z5,z8]),(0,[z0,z1,z2,z3,z447,z5,z6])],[(0,[z448,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z449,z5,z6])]],
   [[(0,[z42,z0,z1,z2,z3,z450,z6])],[(0,[z49,z1,z2,z3,z5,z6,z192]),(0,[z0,z1,z2,z3,z5,z451,z6]),(0,[z0,z452,z1,z2,z3,z5,z6]),(0,[z453,z0,z1,z2,z3,z5,z6]),(0,[z454,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z455]),(0,[z0,z133,z1,z100,z3,z5,z6]),(0,[z456,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z457,z5,z6]),(0,[z38,z0,z1,z2,z3,z5,z31])],[(0,[z0,z1,z458,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z156,z5,z6])],[(0,[z0,z1,z65,z2,z3,z5,z8]),(0,[z1,z72,z2,z13,z3,z5,z6]),(0,[z0,z1,z2,z152,z3,z52,z5]),(0,[z0,z1,z2,z3,z5,z6,z8]),(0,[z459,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z370]),(0,[z460,z17,z0,z1,z2,z3,z5])],[(0,[z0,z219,z2,z23,z3,z5,z6]),(0,[z99,z0,z461,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z462,z6]),(0,[z0,z1,z2,z10,z3,z15,z5]),(0,[z463,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z10,z3,z3,z5])],[(0,[z0,z1,z2,z244,z3,z5,z6]),(0,[z78,z0,z65,z2,z3,z5,z6]),(1,[z99,z1,z13,z3,z5,z6]),(0,[z279,z0,z1,z2,z3,z5,z31]),(0,[z418,z1,z2,z23,z3,z5,z6]),(0,[z0,z1,z2,z14,z3,z5,z6]),(0,[z0,z1,z2,z464,z3,z5,z6]),(0,[z0,z1,z2,z3,z179,z5,z6]),(0,[z0,z1,z2,z10,z3,z5,z160]),(1,[z0,z1,z2,z3,z51,z6]),(0,[z17,z0,z1,z76,z2,z3,z5]),(0,[z0,z465,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z81,z3,z6,z121])],[(0,[z0,z466,z1,z2,z3,z5,z6]),(0,[z467,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z31,z109])]],
   [[(1,[z0,z1,z2,z3,z5,z6]),(0,[z176,z0,z1,z2,z3,z5,z6]),(0,[z468,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z31,z28]),(0,[z0,z1,z2,z3,z5,z6,z469])],[(0,[z0,z1,z2,z3,z5,z6,z470]),(0,[z30,z17,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z441]),(0,[z0,z61,z1,z3,z115,z5,z6]),(0,[z0,z429,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z471,z3,z5,z6]),(0,[z0,z145,z1,z2,z14,z5,z6])],[(1,[z0,z1,z2,z265,z5,z6]),(0,[z0,z1,z2,z3,z5,z122,z6]),(0,[z198,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z472,z5,z6]),(0,[z0,z145,z2,z14,z3,z5,z6]),(1,[z0,z1,z2,z53,z3,z5]),(0,[z0,z1,z181,z3,z5,z46,z6]),(0,[z0,z1,z2,z3,z5,z473,z6])],[(0,[z90,z0,z1,z2,z3,z5,z6]),(0,[z30,z0,z1,z2,z140,z5,z6]),(0,[z0,z1,z2,z3,z474,z5,z6]),(0,[z0,z1,z2,z3,z5,z31,z6]),(0,[z0,z1,z2,z3,z5,z423,z8]),(0,[z0,z1,z2,z3,z5,z475,z6]),(0,[z0,z1,z2,z81,z3,z5,z121])],[(0,[z476,z0,z1,z2,z3,z5,z6]),(0,[z0,z145,z1,z2,z3,z5,z477])],[(0,[z0,z1,z2,z478,z3,z5,z6]),(0,[z479,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z480,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z272]),(0,[z0,z61,z1,z2,z3,z46,z6])],[(0,[z0,z1,z2,z3,z481,z5,z6]),(0,[z482,z0,z1,z2,z3,z5,z6]),(0,[z176,z0,z1,z13,z3,z5,z6]),(0,[z0,z1,z2,z3,z483,z5,z6]),(0,[z0,z1,z310,z2,z3,z5,z6]),(0,[z484,z17,z0,z1,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z485,z6]),(0,[z0,z1,z2,z48,z3,z5,z8]),(0,[z0,z1,z486,z2,z3,z5,z6]),(0,[z279,z0,z1,z2,z263,z5,z6]),(0,[z0,z1,z487,z2,z3,z5,z6]),(0,[z0,z1,z2,z10,z14,z3,z5]),(0,[z0,z488,z1,z2,z3,z5,z6]),(1,[z7,z0,z1,z2,z5,z6])],[(0,[z489,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z312,z6]),(0,[z0,z1,z72,z2,z3,z5,z304]),(0,[z38,z0,z1,z2,z15,z5,z6]),(0,[z129,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z490])],[(0,[z0,z491,z1,z2,z3,z5,z6]),(0,[z0,z219,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z492,z3,z5,z6]),(0,[z0,z1,z2,z23,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z493,z31])],[(0,[z0,z1,z2,z303,z3,z5,z6]),(0,[z0,z1,z2,z494,z3,z5,z6]),(0,[z0,z1,z2,z393,z3,z15,z5]),(0,[z129,z1,z2,z3,z5,z37,z6]),(0,[z0,z1,z2,z213,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z159,z6])],[(0,[z171,z17,z0,z1,z2,z3,z5]),(0,[z57,z0,z1,z2,z3,z35,z6]),(0,[z0,z1,z2,z3,z5,z267,z6]),(0,[z0,z1,z2,z3,z495,z5,z6]),(2,[z7,z0,z1,z2,z5])],[(1,[z17,z0,z1,z2,z15,z5]),(0,[z0,z1,z2,z3,z160,z26,z6]),(1,[z0,z1,z2,z3,z5,z377]),(1,[z17,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z58,z6])],[(0,[z0,z1,z496,z2,z3,z5,z6]),(0,[z0,z1,z2,z497,z3,z5,z6]),(0,[z17,z0,z1,z100,z2,z3,z5]),(0,[z0,z2,z14,z3,z67,z5,z6]),(0,[z17,z0,z61,z1,z2,z3,z5]),(0,[z0,z1,z76,z3,z5,z6,z8])],[(0,[z0,z1,z2,z498,z3,z5,z6]),(0,[z279,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z5,z22,z6]),(0,[z0,z1,z2,z3,z499,z5,z6]),(0,[z0,z1,z2,z18,z5,z26,z6])]],
   [[(0,[z0,z1,z2,z3,z500,z5,z6]),(0,[z501,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z67,z5,z8]),(0,[z0,z1,z120,z2,z3,z5,z6]),(0,[z0,z1,z76,z2,z10,z3,z5]),(1,[z0,z1,z2,z261,z18,z6])],[(0,[z90,z17,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z115,z21,z6]),(0,[z0,z1,z2,z3,z5,z6,z29]),(0,[z0,z1,z2,z3,z502,z5,z6]),(0,[z503,z0,z1,z2,z3,z5,z6]),(0,[z0,z504,z1,z2,z3,z5,z6])],[(0,[z0,z505,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z28,z37]),(0,[z0,z1,z2,z506,z3,z5,z6]),(0,[z38,z0,z61,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z239,z5,z8]),(0,[z479,z17,z0,z1,z2,z3,z5]),(0,[z507,z0,z1,z2,z3,z5,z6]),(0,[z0,z508,z1,z2,z3,z5,z6])],[(0,[z509,z0,z1,z2,z3,z5,z6]),(0,[z510,z0,z1,z2,z3,z5,z6]),(0,[z9,z0,z1,z76,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z338,z5])],[(0,[z99,z0,z1,z2,z3,z5,z144]),(0,[z0,z1,z2,z3,z5,z82,z6]),(0,[z0,z1,z2,z3,z5,z31,z137]),(0,[z0,z1,z2,z3,z511,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z512]),(0,[z0,z1,z2,z513,z3,z5,z6]),(0,[z57,z0,z1,z2,z3,z5,z86]),(0,[z129,z17,z0,z1,z2,z3,z5]),(1,[z0,z1,z2,z3,z450,z6]),(0,[z0,z514,z1,z2,z3,z5,z6]),(0,[z0,z515,z1,z2,z3,z5,z6]),(0,[z30,z0,z1,z2,z3,z5,z251]),(0,[z0,z1,z2,z3,z5,z516,z6])],[(0,[z20,z0,z1,z2,z10,z3,z5]),(0,[z0,z517,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z13,z3,z5,z31]),(0,[z0,z1,z2,z518,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z325]),(0,[z519,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z520,z3,z5,z6]),(0,[z0,z1,z2,z81,z3,z22,z6]),(0,[z0,z1,z2,z3,z5,z521,z6]),(0,[z17,z0,z1,z120,z2,z3,z5]),(0,[z0,z1,z2,z522,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z5,z26]),(1,[z0,z1,z2,z3,z5,z523]),(0,[z0,z1,z2,z10,z3,z5,z524]),(0,[z0,z1,z2,z3,z5,z524,z6])],[(0,[z0,z1,z2,z261,z3,z21,z6]),(1,[z0,z1,z2,z3,z5,z419])],[(0,[z0,z1,z2,z3,z5,z525,z6]),(0,[z526,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z527,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z335]),(0,[z0,z1,z2,z435,z3,z5,z6])],[(1,[z0,z1,z2,z132,z5,z6]),(0,[z0,z1,z2,z3,z5,z528,z6]),(0,[z0,z461,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z287,z6]),(0,[z0,z145,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z8,z529])],[(0,[z0,z133,z65,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z37,z8]),(0,[z42,z0,z1,z2,z67,z5,z6]),(0,[z0,z193,z1,z2,z3,z160,z6]),(0,[z30,z0,z1,z2,z10,z3,z5]),(0,[z530,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z116,z3,z5,z6]),(1,[z0,z1,z2,z365,z3,z5]),(0,[z17,z0,z1,z2,z10,z3,z5])],[(0,[z219,z1,z65,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z263,z5,z6]),(0,[z17,z49,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z192]),(0,[z17,z0,z133,z1,z2,z3,z5]),(0,[z0,z193,z1,z2,z3,z179,z6]),(0,[z0,z1,z2,z3,z5,z137,z8]),(0,[z0,z1,z2,z3,z531,z5,z6]),(0,[z0,z1,z2,z3,z5,z532,z6]),(0,[z0,z1,z2,z3,z5,z6,z533]),(0,[z0,z1,z2,z81,z3,z5,z6])],[(1,[z0,z1,z2,z534,z3,z5]),(0,[z0,z1,z2,z340,z140,z3,z5])]],
   [[(0,[z90,z0,z1,z2,z132,z5,z6]),(0,[z129,z0,z1,z2,z3,z187,z6]),(0,[z0,z1,z2,z535,z3,z5,z6]),(0,[z0,z1,z2,z3,z179,z26,z6]),(0,[z536,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z537,z5,z6]),(0,[z0,z1,z2,z3,z5,z26,z31]),(0,[z0,z1,z2,z293,z3,z5,z31]),(0,[z0,z1,z2,z10,z3,z5,z109])],[(1,[z0,z1,z2,z3,z50,z6]),(0,[z0,z1,z2,z3,z538,z5,z6]),(0,[z0,z1,z2,z10,z3,z5,z28]),(0,[z0,z1,z539,z2,z3,z5,z6])],[(0,[z540,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z541,z3,z5,z6]),(0,[z38,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z542,z5,z6]),(0,[z49,z0,z1,z2,z10,z3,z5]),(0,[z17,z0,z1,z2,z3,z67,z5]),(0,[z0,z543,z1,z2,z3,z5,z6])],[(1,[z0,z461,z2,z3,z5,z6]),(0,[z171,z0,z1,z2,z48,z5,z6]),(0,[z0,z1,z2,z3,z15,z5,z6]),(0,[z0,z1,z2,z544,z3,z5,z6]),(0,[z0,z1,z2,z545,z3,z5,z6]),(0,[z0,z1,z76,z2,z3,z5,z31]),(0,[z546,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z31,z532]),(0,[z0,z1,z2,z261,z18,z5,z6]),(0,[z0,z277,z1,z2,z3,z5,z6])],[(1,[z17,z0,z1,z2,z48,z5]),(0,[z0,z1,z2,z3,z5,z26,z8]),(0,[z0,z1,z2,z3,z83,z5,z31]),(0,[z0,z1,z2,z3,z5,z547,z6])],[(0,[z0,z1,z73,z2,z3,z67,z5]),(0,[z0,z1,z548,z2,z3,z5,z6]),(0,[z0,z1,z2,z10,z3,z5,z6])],[(0,[z279,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z549,z3,z5,z6]),(0,[z0,z1,z2,z550,z3,z5,z6]),(1,[z0,z1,z2,z435,z3,z5])],[(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z551,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z181,z2,z3,z5,z433]),(0,[z0,z1,z2,z172,z10,z3,z5])]],
   [[(0,[z0,z1,z65,z2,z10,z3,z5]),(0,[z0,z1,z2,z3,z552,z5,z6]),(0,[z0,z1,z2,z140,z3,z5,z8]),(0,[z526,z17,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z553,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z529]),(0,[z0,z61,z1,z2,z3,z5,z6]),(0,[z189,z0,z1,z2,z10,z3,z5]),(0,[z0,z1,z2,z191,z10,z3,z5])],[(0,[z279,z20,z1,z2,z3,z5,z6]),(0,[z20,z0,z1,z2,z3,z5,z31]),(0,[z129,z0,z1,z2,z3,z50,z6]),(0,[z17,z0,z106,z1,z2,z3,z5]),(0,[z0,z1,z3,z115,z5,z46,z6])],[(0,[z0,z1,z2,z10,z3,z5,z37]),(0,[z0,z358,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z10,z5,z137,z6])],[(0,[z90,z0,z65,z2,z3,z5,z6]),(0,[z17,z0,z1,z65,z2,z3,z5]),(0,[z57,z0,z1,z2,z10,z3,z5]),(0,[z0,z1,z2,z3,z5,z554,z6]),(0,[z0,z1,z2,z3,z5,z6,z555]),(0,[z0,z1,z2,z3,z5,z311,z8]),(0,[z0,z556,z1,z2,z3,z5,z6]),(0,[z362,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z304]),(0,[z0,z1,z72,z2,z10,z3,z5]),(0,[z0,z1,z2,z3,z5,z557,z6]),(1,[z0,z209,z2,z3,z179,z6]),(1,[z0,z1,z2,z3,z558,z5]),(0,[z0,z1,z2,z3,z5,z6,z559])],[(0,[z560,z0,z1,z2,z3,z5,z6]),(1,[z418,z1,z2,z3,z5,z6]),(1,[z75,z0,z2,z3,z5,z28])],[(0,[z0,z1,z2,z3,z561,z5,z6]),(1,[z17,z0,z1,z2,z10,z5])]],
   [[(0,[z0,z1,z2,z3,z562,z5,z6]),(0,[z0,z1,z2,z3,z5,z563,z6]),(0,[z0,z1,z564,z2,z3,z5,z6]),(0,[z42,z0,z1,z2,z14,z5,z6]),(0,[z0,z1,z2,z3,z18,z160,z6]),(0,[z565,z0,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z5,z31]),(1,[z17,z0,z1,z2,z5,z109])],[(0,[z0,z1,z566,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z185,z6]),(0,[z567,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z433]),(0,[z17,z0,z1,z2,z81,z3,z5])],[(0,[z171,z57,z1,z2,z3,z5,z6]),(0,[z460,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z568,z3,z5,z6]),(0,[z0,z193,z1,z2,z3,z5,z6]),(0,[z0,z193,z1,z2,z261,z3,z6]),(0,[z75,z0,z2,z3,z5,z28,z6]),(0,[z0,z1,z2,z3,z5,z6,z182]),(0,[z319,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z569,z2,z3,z5,z6]),(0,[z0,z1,z2,z140,z15,z5,z6]),(0,[z0,z1,z2,z393,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z570,z6]),(0,[z571,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z52,z5,z6])],[(0,[z38,z0,z1,z2,z48,z5,z6]),(1,[z0,z256,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z572,z5,z6]),(0,[z30,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z340,z3,z5,z8]),(0,[z17,z0,z1,z2,z3,z5,z8])],[(0,[z0,z1,z2,z3,z573,z5,z6]),(0,[z0,z574,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z575,z6]),(0,[z0,z1,z2,z3,z576,z5,z6]),(0,[z0,z1,z2,z10,z140,z3,z5]),(0,[z0,z1,z577,z2,z3,z5,z6]),(0,[z17,z578,z0,z1,z2,z3,z5])],[(1,[z0,z1,z148,z3,z5,z6]),(0,[z0,z1,z579,z2,z3,z5,z6]),(0,[z0,z219,z1,z2,z10,z3,z5]),(0,[z0,z1,z2,z534,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z580,z6])],[(0,[z581,z0,z1,z2,z3,z5,z6]),(0,[z582,z0,z1,z2,z3,z5,z6]),(0,[z0,z106,z1,z100,z3,z5,z6]),(0,[z0,z106,z1,z2,z3,z5,z432]),(0,[z0,z1,z2,z3,z5,z6,z121])]],
   [[],[(0,[z0,z1,z2,z583,z3,z5,z6]),(0,[z49,z0,z1,z2,z3,z5,z8]),(0,[z584,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z100,z2,z3,z5,z228]),(0,[z585,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z586,z6]),(0,[z0,z1,z27,z2,z3,z5,z6])],[(0,[z90,z78,z1,z2,z3,z5,z6]),(0,[z90,z0,z1,z148,z3,z5,z6]),(0,[z587,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z588,z5,z6]),(0,[z7,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z589,z3,z5,z6]),(0,[z0,z1,z590,z2,z3,z5,z6])],[(0,[z0,z1,z65,z2,z3,z5,z31]),(1,[z0,z1,z2,z3,z5,z144]),(0,[z0,z1,z2,z3,z5,z591,z6]),(0,[z0,z1,z592,z2,z3,z5,z6]),(0,[z20,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z128,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z593,z6]),(0,[z42,z38,z0,z1,z2,z5,z6]),(0,[z594,z0,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z179,z5])],[(0,[z78,z0,z219,z2,z3,z5,z6]),(0,[z190,z0,z1,z2,z3,z5,z31]),(0,[z229,z0,z1,z2,z10,z3,z5])],[(0,[z0,z1,z2,z3,z115,z22,z6]),(0,[z484,z0,z1,z2,z3,z5,z6]),(0,[z352,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z595])],[(0,[z596,z0,z1,z2,z3,z5,z6]),(0,[z78,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z13,z23,z3,z5,z6]),(0,[z0,z1,z597,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z500,z6]),(1,[z0,z1,z2,z3,z5,z598]),(0,[z17,z0,z1,z2,z15,z5,z6]),(0,[z57,z0,z1,z2,z3,z5,z31]),(0,[z0,z256,z1,z2,z3,z67,z6]),(0,[z0,z1,z2,z3,z5,z6,z599]),(0,[z0,z1,z2,z3,z5,z6,z600]),(0,[z0,z1,z2,z10,z3,z5,z46])]],
   [[(0,[z0,z1,z72,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z5,z6,z601]),(0,[z0,z1,z2,z3,z5,z602,z6]),(0,[z0,z1,z2,z3,z5,z184,z6]),(0,[z0,z218,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z603])],[(0,[z0,z1,z2,z3,z5,z598,z6]),(0,[z0,z1,z2,z3,z5,z6,z604]),(0,[z0,z605,z1,z2,z3,z5,z6]),(0,[z38,z0,z1,z2,z261,z5,z6]),(0,[z0,z1,z170,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z606,z5,z6]),(0,[z99,z0,z1,z2,z3,z5,z8]),(0,[z171,z0,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z48,z3,z5]),(0,[z0,z1,z2,z3,z607,z5,z6]),(0,[z0,z1,z2,z158,z3,z5,z6]),(0,[z0,z1,z100,z2,z3,z5,z8]),(0,[z38,z0,z145,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z608,z6]),(0,[z0,z1,z2,z3,z5,z160,z6]),(0,[z0,z1,z2,z3,z115,z5,z6]),(0,[z609,z0,z1,z2,z3,z5,z6])],[(0,[z90,z0,z1,z2,z3,z500,z6]),(0,[z90,z0,z1,z2,z3,z5,z598]),(0,[z57,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z610,z6]),(0,[z17,z0,z1,z181,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z611,z6]),(0,[z0,z1,z2,z10,z3,z612,z5])],[(0,[z0,z1,z72,z2,z3,z5,z8]),(0,[z0,z209,z2,z3,z179,z5,z6]),(0,[z0,z1,z2,z3,z5,z613,z6]),(0,[z9,z0,z1,z2,z3,z5,z8])],[(0,[z0,z1,z2,z3,z614,z5,z6]),(0,[z0,z1,z2,z3,z316,z5,z6]),(0,[z0,z1,z2,z615,z3,z5,z6]),(1,[z0,z1,z3,z5,z31,z8]),(0,[z0,z1,z2,z3,z18,z5,z6]),(0,[z17,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z3,z118,z5,z6])],[(0,[z616,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z261,z3,z22,z6]),(0,[z0,z209,z1,z2,z10,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z617])],[(0,[z618,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z48,z3,z5,z31]),(0,[z0,z1,z2,z619,z3,z5,z6]),(1,[z0,z1,z2,z173,z5,z6]),(0,[z0,z1,z2,z3,z5,z8,z29]),(0,[z38,z0,z1,z181,z2,z3,z6]),(0,[z0,z1,z181,z2,z10,z3,z5]),(0,[z0,z1,z620,z2,z3,z5,z6])]],
   [[(0,[z621,z0,z1,z2,z3,z5,z6]),(0,[z0,z622,z1,z2,z3,z5,z6]),(1,[z171,z1,z2,z15,z5,z6]),(1,[z0,z1,z2,z3,z5,z432]),(0,[z0,z145,z1,z2,z10,z3,z5]),(1,[z0,z24,z2,z3,z5,z29]),(0,[z623,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z10,z3,z353,z5])],[(0,[z0,z1,z2,z3,z5,z6,z624]),(0,[z0,z219,z1,z2,z3,z5,z31]),(0,[z0,z1,z625,z2,z3,z5,z6]),(0,[z626,z0,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z5,z29]),(0,[z0,z1,z2,z627,z3,z5,z6])],[(0,[z628,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z629,z5,z6]),(1,[z0,z1,z2,z3,z5,z251]),(0,[z0,z1,z2,z10,z3,z52,z5]),(0,[z0,z1,z2,z3,z558,z5,z6])],[(0,[z0,z1,z630,z2,z3,z5,z6]),(0,[z0,z1,z2,z261,z3,z5,z6])],[(0,[z631,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z291,z6]),(0,[z0,z1,z2,z3,z5,z632,z6]),(1,[z49,z1,z2,z3,z5,z192]),(1,[z129,z1,z2,z3,z5,z37]),(0,[z0,z1,z2,z3,z25,z5,z8]),(0,[z0,z1,z2,z3,z5,z6,z109])],[(0,[z633,z0,z1,z2,z3,z5,z6]),(0,[z634,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z31,z37]),(0,[z0,z1,z2,z3,z635,z5,z6])],[(0,[z57,z0,z1,z2,z15,z5,z6]),(0,[z38,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z5,z636,z6]),(0,[z0,z1,z637,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z638,z5,z6]),(0,[z17,z0,z1,z2,z3,z25,z5])],[(0,[z279,z1,z2,z3,z21,z5,z6]),(0,[z0,z1,z2,z3,z188,z5,z6]),(0,[z0,z1,z2,z3,z67,z5,z31]),(0,[z0,z1,z2,z3,z5,z639,z6]),(0,[z17,z0,z1,z2,z261,z3,z5])]],
   [[(0,[z0,z1,z640,z2,z3,z5,z6]),(0,[z17,z0,z145,z1,z2,z3,z5]),(0,[z0,z641,z1,z2,z3,z5,z6]),(0,[z642,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z181,z2,z3,z115,z6]),(0,[z0,z643,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z0,z1,z2,z3,z5,z644,z6]),(1,[z0,z1,z2,z3,z5,z477])],[(0,[z20,z0,z1,z2,z3,z21,z6]),(0,[z129,z0,z1,z2,z3,z5,z37]),(0,[z0,z1,z645,z2,z3,z5,z6]),(0,[z0,z1,z2,z534,z3,z5,z160]),(0,[z0,z1,z2,z3,z5,z646,z6]),(0,[z647,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z10,z3,z558,z5])],[(0,[z0,z1,z2,z3,z5,z6,z648]),(0,[z0,z1,z2,z53,z3,z5,z6]),(0,[z38,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z8,z192]),(0,[z0,z1,z649,z2,z3,z5,z6]),(0,[z0,z1,z650,z2,z3,z5,z6]),(1,[z0,z1,z2,z5,z423,z8]),(0,[z0,z1,z2,z3,z651,z5,z6])],[(0,[z99,z1,z2,z13,z3,z5,z6]),(0,[z0,z1,z2,z652,z3,z5,z6]),(0,[z0,z1,z72,z2,z3,z5,z291]),(0,[z0,z1,z2,z3,z653,z5,z6]),(0,[z0,z1,z2,z3,z5,z654,z6]),(0,[z0,z24,z1,z2,z81,z3,z5]),(0,[z247,z0,z1,z2,z3,z5,z31])],[(0,[z0,z655,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z656]),(0,[z0,z1,z2,z3,z21,z5,z8]),(0,[z17,z0,z1,z2,z3,z5,z192]),(0,[z0,z133,z1,z2,z3,z230,z6]),(0,[z0,z1,z2,z3,z657,z5,z6]),(0,[z658,z0,z1,z2,z3,z5,z6])],[(0,[z279,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z659,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z660,z5,z6]),(0,[z0,z1,z2,z661,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z257,z31])]],
   [[(0,[z0,z1,z2,z3,z662,z5,z6]),(0,[z0,z24,z1,z2,z3,z5,z8])],[(1,[z78,z219,z2,z3,z5,z6]),(0,[z17,z0,z193,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z663]),(0,[z0,z209,z1,z2,z3,z5,z31]),(0,[z0,z1,z120,z2,z5,z137,z6]),(0,[z0,z1,z2,z3,z5,z664,z6]),(0,[z0,z1,z2,z3,z5,z423,z6]),(0,[z0,z1,z2,z5,z423,z6,z8])],[(1,[z0,z1,z181,z3,z46,z6]),(0,[z0,z1,z2,z3,z612,z5,z6])],[(0,[z0,z133,z219,z2,z3,z5,z6]),(0,[z0,z1,z2,z23,z10,z3,z5]),(0,[z0,z145,z1,z2,z3,z5,z31]),(1,[z0,z1,z2,z3,z5,z252])],[(0,[z0,z665,z1,z2,z3,z5,z6]),(0,[z57,z0,z1,z2,z3,z5,z309]),(0,[z0,z1,z2,z3,z5,z6,z666]),(0,[z0,z1,z2,z3,z5,z31,z236]),(0,[z578,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z667,z3,z5,z6]),(0,[z668,z0,z1,z2,z3,z5,z6]),(0,[z0,z669,z1,z2,z3,z5,z6]),(0,[z0,z670,z1,z2,z3,z5,z6]),(0,[z38,z0,z193,z1,z2,z3,z6]),(0,[z0,z209,z1,z2,z3,z5,z8]),(0,[z75,z0,z24,z2,z3,z5,z6]),(0,[z0,z671,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z192,z29]),(0,[z0,z1,z2,z3,z5,z6,z377]),(0,[z0,z1,z2,z672,z3,z5,z6]),(0,[z0,z1,z181,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z18,z5,z523]),(0,[z0,z1,z2,z3,z673,z5,z6]),(0,[z17,z0,z1,z620,z2,z3,z5])],[(0,[z0,z1,z674,z2,z3,z5,z6]),(0,[z675,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z676,z3,z5,z6]),(1,[z0,z106,z23,z3,z5,z6]),(0,[z324,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z228]),(0,[z0,z1,z2,z3,z5,z677,z6]),(0,[z0,z1,z2,z3,z5,z678,z6]),(0,[z38,z0,z1,z2,z5,z26,z6]),(0,[z190,z17,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z679,z6])]],
   [[(0,[z0,z1,z138,z2,z3,z5,z6]),(0,[z680,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z681,z3,z5,z6]),(0,[z0,z285,z1,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z5,z31,z245]),(0,[z38,z17,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z340,z10,z3,z5])],[(1,[z0,z1,z2,z3,z5,z280]),(0,[z17,z0,z1,z2,z3,z21,z5]),(0,[z0,z1,z2,z682,z3,z5,z6]),(1,[z0,z1,z2,z3,z230,z6]),(0,[z330,z0,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z3,z5])],[(0,[z0,z683,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z684,z5,z6])],[(0,[z1,z2,z3,z5,z37,z6,z192]),(0,[z0,z133,z100,z2,z3,z5,z6]),(0,[z0,z1,z685,z2,z3,z5,z6]),(0,[z0,z61,z1,z181,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z493,z6]),(0,[z0,z1,z2,z3,z184,z6,z8])],[(0,[z279,z17,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z288,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z686,z6]),(0,[z0,z296,z1,z2,z3,z5,z31]),(0,[z0,z1,z2,z365,z3,z5,z26])],[(0,[z0,z1,z2,z3,z5,z6,z687]),(0,[z0,z1,z2,z3,z5,z370,z26])],[(0,[z219,z1,z72,z2,z3,z5,z6]),(0,[z0,z1,z2,z48,z52,z5,z6]),(0,[z0,z688,z1,z2,z3,z5,z6]),(0,[z689,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z14,z3,z5,z8]),(0,[z0,z1,z2,z3,z179,z5,z8]),(0,[z0,z1,z310,z2,z3,z52,z6])],[(0,[z0,z1,z2,z81,z3,z5,z37]),(0,[z0,z1,z2,z140,z3,z5,z31])]],
   [[(0,[z0,z1,z2,z690,z3,z5,z6]),(0,[z99,z0,z1,z2,z3,z12,z6]),(0,[z176,z0,z1,z2,z3,z5,z8]),(0,[z691,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z8]),(0,[z17,z0,z1,z2,z5,z6,z109])],[(0,[z0,z692,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z693,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z367]),(0,[z0,z145,z1,z2,z3,z5,z272]),(0,[z75,z0,z1,z2,z10,z3,z5]),(0,[z0,z1,z2,z3,z5,z694,z6]),(0,[z0,z1,z695,z2,z3,z5,z6])],[(0,[z90,z0,z219,z2,z3,z5,z6]),(0,[z78,z0,z1,z2,z10,z3,z5]),(0,[z17,z0,z1,z2,z48,z5,z6]),(0,[z0,z1,z2,z3,z696,z5,z6]),(0,[z0,z1,z2,z3,z5,z697,z6]),(1,[z0,z1,z2,z340,z3,z5]),(0,[z698,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z523])],[(0,[z0,z1,z2,z3,z22,z160,z6])],[(0,[z90,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z699,z6]),(0,[z700,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z31,z8])],[(0,[z701,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z702,z3,z5,z6]),(0,[z17,z176,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z450,z6]),(0,[z0,z1,z2,z3,z703,z5,z6]),(0,[z704,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z120,z2,z3,z5,z419]),(0,[z0,z1,z2,z3,z5,z8,z121]),(0,[z0,z1,z2,z261,z3,z18,z6])],[(0,[z99,z0,z1,z2,z10,z3,z5]),(0,[z0,z1,z100,z2,z10,z3,z5]),(0,[z705,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z706,z3,z5,z6]),(0,[z171,z1,z2,z3,z15,z5,z6]),(0,[z0,z1,z2,z3,z5,z477,z6]),(0,[z17,z0,z1,z2,z3,z5,z121])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z99,z1,z13,z3,z12,z6]),(0,[z0,z61,z1,z3,z115,z31])],[(0,[z0,z1,z2,z3,z5,z707]),(0,[z0,z1,z2,z3,z5,z251]),(0,[z17,z0,z1,z2,z5,z236])],[(0,[z0,z708,z2,z3,z5,z6]),(0,[z0,z1,z2,z156,z5,z6]),(0,[z0,z256,z1,z2,z48,z6]),(0,[z0,z1,z2,z3,z25,z184]),(0,[z0,z1,z2,z3,z5,z709])],[],[(0,[z0,z1,z2,z3,z5,z163]),(0,[z0,z1,z2,z173,z5,z37]),(0,[z30,z0,z1,z152,z52,z5]),(0,[z484,z0,z1,z2,z3,z233])],[(0,[z0,z1,z2,z3,z5,z710]),(0,[z0,z1,z2,z711,z3,z5]),(0,[z0,z1,z712,z3,z5,z6]),(0,[z190,z30,z0,z1,z2,z5]),(0,[z460,z578,z1,z2,z3,z5])],[(0,[z99,z1,z13,z10,z3,z5]),(0,[z57,z1,z2,z48,z5,z86])],[(0,[z0,z1,z2,z303,z122,z6]),(0,[z503,z1,z2,z48,z5,z6]),(0,[z0,z1,z2,z713,z3,z5])],[(0,[z418,z219,z2,z3,z5,z6]),(0,[z0,z1,z2,z714,z5,z6]),(0,[z0,z1,z120,z715,z5,z6]),(0,[z0,z1,z2,z3,z184,z8])],[(0,[z49,z1,z2,z3,z5,z716]),(0,[z704,z1,z2,z3,z5,z37]),(0,[z0,z193,z2,z10,z3,z160]),(0,[z0,z1,z2,z3,z5,z717]),(0,[z33,z0,z1,z2,z3,z338])],[(0,[z20,z1,z2,z10,z3,z22]),(0,[z418,z1,z2,z3,z5,z8]),(0,[z718,z1,z2,z3,z5,z6]),(0,[z0,z32,z1,z2,z116,z3]),(0,[z0,z1,z2,z3,z719,z8])],[(0,[z0,z1,z2,z244,z5,z31]),(0,[z0,z1,z2,z3,z122,z312]),(0,[z0,z1,z2,z720,z5,z6]),(1,[z1,z2,z3,z721,z6]),(0,[z17,z0,z1,z2,z5,z159])],[(0,[z1,z2,z722,z3,z5,z6]),(0,[z723,z1,z2,z3,z5,z6]),(0,[z9,z0,z1,z3,z5,z31])],[(0,[z30,z0,z1,z435,z3,z5])],[(0,[z0,z131,z1,z3,z5,z31])],[(0,[z0,z138,z2,z3,z5,z31]),(0,[z0,z133,z724,z3,z5,z6]),(0,[z0,z145,z2,z14,z5,z8]),(0,[z211,z0,z193,z1,z2,z6]),(0,[z7,z0,z1,z120,z2,z5])]],
   [[(0,[z78,z219,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z725])],[(0,[z0,z1,z2,z3,z726,z304]),(0,[z20,z1,z2,z3,z721,z6])],[(0,[z0,z1,z2,z727,z5,z6]),(0,[z0,z1,z2,z3,z5,z252])],[(0,[z0,z1,z2,z728,z3,z5]),(0,[z0,z1,z2,z3,z5,z729])],[(0,[z0,z730,z1,z3,z5,z6]),(0,[z211,z0,z1,z2,z5,z8]),(0,[z0,z1,z76,z3,z5,z8])],[(0,[z0,z461,z2,z3,z5,z144]),(0,[z675,z17,z0,z1,z2,z5])],[(0,[z731,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z732]),(0,[z7,z0,z1,z5,z31,z8])],[(0,[z0,z2,z724,z3,z5,z6]),(0,[z17,z0,z1,z733,z3,z5])],[(0,[z0,z1,z2,z3,z5,z734]),(0,[z129,z1,z2,z3,z118,z5]),(0,[z0,z1,z2,z3,z5,z735]),(0,[z0,z1,z2,z5,z137,z252])],[(0,[z0,z1,z2,z3,z5,z736]),(0,[z99,z1,z13,z3,z5,z31]),(0,[z0,z145,z2,z14,z5,z272]),(0,[z0,z1,z2,z3,z5,z737])],[(0,[z0,z1,z2,z3,z738,z6]),(1,[z0,z724,z3,z5,z6])],[(0,[z0,z1,z2,z739,z5,z6]),(0,[z0,z1,z2,z393,z156,z5]),(0,[z17,z57,z1,z2,z48,z5]),(0,[z0,z1,z2,z3,z5,z740])],[(0,[z0,z1,z741,z3,z5,z6]),(0,[z0,z1,z715,z52,z5,z6]),(0,[z0,z1,z2,z3,z5,z742]),(0,[z0,z1,z2,z3,z743,z6]),(0,[z189,z7,z0,z1,z2,z5])],[(0,[z744,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z745,z3,z5]),(0,[z0,z1,z746,z3,z5,z6]),(0,[z0,z1,z2,z3,z51,z8]),(0,[z0,z61,z1,z3,z421,z6]),(0,[z0,z1,z2,z5,z747,z109])],[(0,[z17,z0,z1,z2,z518,z5]),(0,[z0,z1,z2,z116,z3,z184])],[(0,[z0,z1,z2,z3,z5,z8]),(0,[z510,z1,z2,z3,z21,z6]),(0,[z42,z0,z73,z2,z67,z5]),(0,[z0,z1,z2,z748,z5,z6]),(0,[z0,z1,z2,z3,z5,z749])]],
   [[(0,[z0,z1,z2,z3,z122,z6]),(0,[z0,z1,z2,z3,z5,z750]),(0,[z0,z1,z2,z81,z3,z335])],[(0,[z0,z1,z2,z751,z3,z5]),(0,[z0,z1,z2,z752,z3,z304]),(0,[z17,z0,z1,z2,z278,z5])],[(0,[z0,z1,z2,z265,z5,z8]),(0,[z753,z0,z1,z2,z3,z5]),(0,[z7,z0,z1,z2,z115,z5]),(0,[z9,z7,z0,z1,z2,z5]),(0,[z0,z1,z2,z261,z18,z141])],[(0,[z0,z1,z2,z3,z5,z754]),(0,[z755,z0,z1,z2,z263,z5]),(0,[z756,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z757,z6])],[(0,[z129,z1,z2,z3,z50,z37])],[(0,[z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z2,z3,z758,z6])],[(0,[z759,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z760,z5,z6]),(0,[z705,z17,z0,z1,z2,z5])],[(0,[z99,z0,z1,z435,z3,z5]),(0,[z7,z0,z1,z2,z5,z8])],[(0,[z0,z1,z2,z3,z5,z761]),(0,[z0,z1,z2,z3,z762,z6]),(0,[z0,z1,z2,z3,z5,z763])],[(0,[z0,z1,z2,z3,z5,z272]),(0,[z17,z0,z1,z2,z3,z316]),(0,[z0,z1,z2,z3,z5,z764])],[(0,[z0,z1,z2,z3,z765,z6]),(0,[z0,z1,z2,z3,z5,z766]),(0,[z0,z1,z767,z2,z3,z6]),(0,[z0,z2,z768,z67,z5,z6]),(0,[z0,z1,z2,z152,z3,z51])],[(0,[z17,z429,z1,z2,z48,z5]),(0,[z0,z1,z2,z3,z5,z769]),(0,[z0,z1,z41,z3,z5,z8]),(0,[z7,z0,z1,z2,z5,z423])],[(0,[z0,z1,z2,z244,z5,z325]),(0,[z0,z1,z770,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z771]),(0,[z7,z0,z1,z2,z5,z441])],[(0,[z0,z1,z2,z3,z5,z772]),(0,[z0,z1,z2,z3,z5,z44]),(0,[z0,z1,z2,z116,z3,z182])],[(0,[z578,z1,z2,z48,z5,z6]),(0,[z773,z1,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z179,z5])],[(0,[z0,z1,z774,z3,z5,z6]),(0,[z0,z1,z775,z2,z3,z5]),(0,[z0,z1,z120,z2,z776,z5]),(0,[z0,z1,z76,z116,z3,z8])]],
   [[(0,[z219,z72,z23,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z777]),(0,[z0,z1,z2,z3,z778,z6])],[(0,[z0,z1,z2,z779,z3,z5]),(0,[z0,z1,z2,z3,z450,z31]),(0,[z0,z1,z2,z3,z780,z6])],[(0,[z0,z1,z220,z132,z5,z6]),(0,[z0,z1,z2,z781,z244,z5]),(0,[z0,z1,z2,z3,z187,z31]),(0,[z0,z1,z782,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z783]),(0,[z0,z1,z2,z116,z3,z121])],[(0,[z0,z1,z2,z3,z5,z784]),(0,[z42,z0,z2,z67,z450,z6])],[(1,[z785,z0,z1,z2,z5]),(0,[z1,z2,z720,z15,z5,z6]),(0,[z0,z1,z2,z5,z159,z786]),(0,[z352,z0,z1,z2,z3,z524])],[(0,[z0,z1,z2,z3,z500,z598]),(0,[z0,z1,z787,z3,z5,z6]),(0,[z0,z1,z3,z788,z5,z6]),(0,[z0,z1,z2,z315,z18,z6]),(0,[z0,z1,z2,z789,z3,z5]),(0,[z30,z0,z1,z435,z5,z6]),(0,[z0,z790,z1,z2,z3,z5]),(0,[z17,z0,z1,z2,z5,z586])],[(0,[z1,z2,z3,z21,z721,z6]),(0,[z0,z1,z791,z3,z5,z6]),(0,[z0,z1,z792,z2,z3,z5]),(0,[z0,z1,z181,z3,z46,z8]),(0,[z0,z61,z1,z3,z780,z6])],[(0,[z0,z1,z2,z132,z5,z31]),(0,[z42,z0,z2,z10,z67,z5])],[(0,[z211,z0,z1,z2,z21,z6]),(0,[z0,z1,z2,z3,z25,z58])],[(0,[z0,z133,z34,z3,z5,z6])],[(0,[z0,z1,z2,z793,z3,z5]),(0,[z7,z176,z0,z1,z2,z5])],[],[(0,[z0,z1,z2,z10,z132,z5]),(0,[z0,z1,z2,z3,z50,z31]),(0,[z0,z1,z2,z794,z5,z6]),(0,[z0,z1,z2,z10,z5,z747])],[(0,[z0,z1,z2,z3,z795,z6]),(0,[z0,z1,z2,z3,z12,z144]),(0,[z17,z0,z1,z2,z128,z5])],[(0,[z0,z1,z148,z10,z3,z5]),(0,[z0,z1,z2,z3,z721,z6]),(0,[z0,z1,z2,z534,z3,z21]),(0,[z0,z1,z2,z3,z5,z796]),(0,[z0,z1,z2,z3,z5,z335]),(0,[z7,z0,z1,z2,z239,z5]),(0,[z0,z277,z2,z213,z3,z5])],[(0,[z0,z1,z2,z797,z5,z6]),(0,[z0,z1,z2,z3,z5,z798])]],
   [[(0,[z17,z0,z209,z2,z3,z179]),(0,[z0,z1,z76,z3,z184,z8]),(0,[z38,z17,z0,z1,z2,z26]),(0,[z0,z1,z2,z3,z749,z121])],[(0,[z0,z1,z2,z799,z3,z5]),(0,[z0,z1,z2,z3,z800,z8])],[(0,[z0,z138,z72,z3,z5,z6]),(0,[z0,z461,z2,z3,z5,z8]),(0,[z171,z17,z1,z2,z15,z5]),(0,[z20,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z801,z5]),(0,[z0,z2,z3,z802,z160,z6]),(0,[z211,z0,z1,z181,z2,z6]),(0,[z0,z1,z2,z3,z5,z803]),(0,[z0,z1,z120,z140,z5,z6]),(0,[z0,z1,z3,z558,z5,z8])],[],[(0,[z0,z2,z3,z5,z804,z6]),(0,[z17,z0,z1,z2,z3,z187]),(0,[z0,z1,z2,z3,z5,z805]),(0,[z0,z133,z100,z3,z5,z367]),(0,[z42,z7,z0,z1,z2,z5]),(0,[z0,z1,z2,z3,z5,z806]),(0,[z0,z1,z2,z152,z3,z5]),(0,[z190,z0,z1,z2,z293,z5])],[(0,[z0,z1,z220,z3,z5,z807]),(0,[z17,z0,z1,z148,z3,z5]),(0,[z0,z1,z808,z3,z5,z6]),(0,[z0,z1,z2,z5,z809,z6]),(0,[z211,z0,z61,z1,z2,z6])],[(0,[z0,z1,z2,z3,z5,z810]),(0,[z0,z1,z2,z303,z5,z312]),(0,[z0,z1,z2,z3,z5,z811]),(0,[z190,z812,z1,z2,z3,z5])],[(0,[z90,z65,z2,z132,z5,z6]),(0,[z675,z0,z1,z52,z5,z6]),(0,[z0,z1,z2,z813,z5,z31])],[(0,[z0,z1,z814,z3,z5,z6]),(0,[z0,z1,z2,z3,z815,z6]),(0,[z785,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z816]),(0,[z17,z812,z1,z2,z3,z5]),(1,[z0,z1,z2,z5,z747])],[(0,[z817,z0,z1,z2,z265,z5]),(0,[z0,z1,z2,z3,z5,z818]),(0,[z0,z1,z3,z5,z819,z6]),(0,[z1,z2,z3,z5,z37,z716]),(0,[z0,z1,z2,z820,z3,z5])],[(0,[z129,z1,z2,z173,z5,z37]),(0,[z17,z0,z1,z2,z3,z184])],[(0,[z0,z1,z2,z821,z5,z6]),(0,[z0,z1,z2,z822,z3,z5]),(0,[z0,z1,z2,z3,z802,z6]),(0,[z0,z61,z1,z3,z413,z6]),(0,[z0,z1,z2,z3,z5,z823])],[(0,[z99,z1,z722,z3,z5,z6]),(0,[z0,z1,z2,z3,z188,z6]),(0,[z0,z209,z2,z3,z179,z8]),(1,[z7,z0,z1,z2,z116])],[(0,[z0,z1,z2,z3,z5,z824]),(0,[z17,z0,z1,z2,z265,z5]),(0,[z0,z1,z2,z3,z5,z825]),(0,[z0,z1,z2,z3,z5,z826]),(0,[z0,z193,z2,z3,z160,z6]),(0,[z0,z1,z2,z3,z5,z827]),(0,[z0,z1,z2,z828,z5,z8]),(0,[z0,z296,z1,z2,z3,z245])],[(0,[z129,z1,z2,z156,z5,z37]),(0,[z7,z0,z1,z2,z5,z184]),(0,[z0,z1,z2,z3,z829,z31]),(0,[z38,z0,z1,z2,z10,z26])],[(0,[z0,z1,z2,z3,z830,z6]),(0,[z0,z1,z310,z2,z53,z3]),(0,[z0,z1,z2,z5,z831,z8])]],
   [[(0,[z0,z1,z2,z3,z35,z8]),(0,[z0,z1,z2,z3,z185,z8]),(0,[z17,z0,z1,z791,z3,z5])],[(0,[z0,z1,z148,z3,z5,z31]),(0,[z0,z1,z2,z3,z5,z832]),(0,[z0,z1,z2,z3,z5,z833]),(1,[z7,z0,z1,z2,z5]),(0,[z0,z1,z2,z3,z83,z493]),(0,[z507,z0,z1,z3,z5,z31])],[],[(0,[z0,z1,z2,z3,z834,z6]),(0,[z7,z0,z106,z1,z2,z5]),(0,[z7,z0,z1,z2,z184,z8])],[(0,[z418,z1,z2,z760,z5,z6]),(0,[z30,z0,z1,z52,z5,z31]),(0,[z0,z1,z2,z116,z3,z58])],[(0,[z0,z1,z220,z3,z5,z598]),(0,[z17,z0,z1,z2,z5,z601]),(0,[z0,z1,z2,z835,z3,z5]),(0,[z211,z17,z0,z1,z2,z5]),(0,[z0,z1,z310,z2,z152,z3]),(0,[z0,z1,z2,z3,z5,z182]),(0,[z7,z0,z1,z2,z81,z5]),(0,[z0,z1,z2,z3,z5,z141])],[(0,[z836,z0,z1,z2,z5,z8]),(0,[z7,z837,z0,z1,z2,z5])],[(0,[z0,z1,z148,z244,z5,z6]),(0,[z219,z138,z2,z3,z5,z6])],[(0,[z0,z1,z2,z132,z5,z325]),(0,[z0,z1,z2,z3,z187,z192]),(0,[z1,z2,z3,z5,z838,z6]),(0,[z0,z1,z2,z3,z5,z839]),(0,[z0,z1,z2,z3,z5,z840]),(0,[z17,z0,z1,z841,z3,z5])],[(0,[z0,z1,z2,z842,z5,z6]),(0,[z49,z429,z1,z2,z3,z5]),(0,[z0,z843,z1,z2,z3,z5]),(0,[z0,z193,z378,z2,z3,z6])],[(0,[z844,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z303,z5,z6]),(0,[z17,z276,z0,z1,z2,z5])],[(0,[z0,z845,z2,z3,z5,z6]),(0,[z30,z0,z1,z2,z435,z5]),(0,[z17,z0,z1,z181,z3,z46])],[(0,[z0,z1,z2,z128,z5,z280])],[(0,[z0,z1,z2,z3,z5,z846]),(0,[z0,z1,z2,z3,z500,z8]),(0,[z42,z0,z2,z288,z67,z5]),(0,[z0,z1,z2,z3,z5,z847])],[(0,[z0,z1,z2,z3,z5,z312]),(0,[z176,z1,z72,z3,z5,z6]),(0,[z0,z1,z2,z10,z3,z450])]],
   [[(0,[z0,z1,z2,z3,z5,z848]),(0,[z17,z0,z1,z2,z568,z5]),(0,[z0,z1,z2,z3,z5,z849]),(0,[z0,z1,z2,z534,z5,z159])],[(0,[z90,z65,z148,z3,z5,z6]),(0,[z78,z219,z2,z10,z3,z5]),(0,[z0,z1,z2,z3,z5,z850]),(0,[z30,z7,z0,z1,z2,z5]),(0,[z7,z0,z1,z2,z140,z5])],[(0,[z279,z1,z2,z10,z3,z21]),(0,[z0,z1,z2,z18,z450,z6]),(0,[z0,z851,z1,z2,z3,z5]),(0,[z0,z1,z2,z852,z3,z8]),(0,[z7,z0,z1,z2,z5,z121])],[(0,[z171,z1,z2,z15,z5,z31]),(0,[z211,z0,z1,z2,z10,z5]),(0,[z7,z0,z209,z1,z2,z5]),(0,[z0,z1,z3,z184,z31,z8])],[(0,[z0,z1,z2,z3,z5,z853]),(0,[z0,z1,z2,z3,z5,z854]),(0,[z211,z0,z1,z2,z22,z6]),(0,[z7,z0,z1,z2,z116,z3])],[(1,[z1,z722,z3,z5,z6]),(0,[z75,z0,z2,z3,z327,z5])],[(0,[z99,z138,z13,z3,z5,z6]),(0,[z0,z1,z2,z265,z122,z6]),(0,[z0,z1,z2,z10,z3,z122])],[(0,[z171,z97,z1,z2,z15,z5]),(0,[z0,z1,z2,z855,z3,z5]),(0,[z0,z1,z2,z3,z31,z856]),(0,[z0,z1,z2,z3,z25,z524])],[(0,[z0,z491,z1,z3,z5,z8]),(0,[z0,z1,z2,z263,z5,z6]),(0,[z17,z0,z1,z2,z5,z648]),(0,[z0,z1,z2,z857,z3,z5]),(0,[z190,z0,z1,z435,z3,z5])],[(0,[z211,z0,z1,z2,z5,z6]),(0,[z30,z0,z1,z2,z53,z5])],[(0,[z90,z65,z2,z3,z5,z598]),(0,[z0,z1,z2,z3,z184,z335])],[(0,[z0,z858,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z859]),(0,[z1,z2,z158,z3,z5,z8]),(0,[z42,z0,z2,z768,z5,z6])],[(0,[z0,z1,z2,z3,z860,z6]),(0,[z0,z1,z2,z861,z5,z6]),(0,[z0,z145,z2,z10,z14,z5]),(0,[z0,z1,z181,z3,z46,z182])],[(0,[z0,z1,z2,z3,z862,z6]),(0,[z0,z863,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z864]),(0,[z0,z1,z2,z3,z5,z865]),(0,[z17,z0,z1,z2,z299,z5]),(0,[z0,z1,z2,z3,z866,z8])],[(0,[z0,z1,z2,z867,z5,z6]),(0,[z0,z1,z2,z3,z868,z6]),(0,[z479,z0,z620,z2,z3,z5])],[(0,[z0,z138,z13,z3,z5,z6]),(0,[z0,z869,z1,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z870,z5,z6]),(0,[z0,z1,z2,z3,z5,z370])],[(0,[z17,z0,z1,z220,z3,z5]),(0,[z7,z0,z1,z2,z5,z22])],[(0,[z0,z1,z148,z3,z5,z325]),(0,[z0,z1,z2,z871,z3,z5]),(0,[z0,z1,z2,z3,z51,z6]),(0,[z0,z1,z2,z340,z5,z423]),(0,[z0,z1,z2,z184,z423,z8])],[(0,[z0,z1,z2,z872,z3,z6]),(0,[z0,z1,z3,z5,z66,z8]),(0,[z30,z17,z0,z1,z435,z5])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z873]),(0,[z0,z1,z2,z3,z5,z874]),(0,[z0,z1,z2,z3,z5,z875]),(0,[z0,z1,z2,z3,z5,z876])],[(0,[z785,z0,z1,z2,z5,z304]),(0,[z0,z1,z2,z3,z5,z877]),(0,[z0,z1,z2,z878,z3,z5]),(0,[z0,z1,z2,z5,z6,z879])],[(0,[z0,z1,z2,z5,z880,z6]),(0,[z0,z1,z2,z3,z881,z6]),(0,[z7,z0,z1,z2,z261,z5]),(0,[z17,z0,z1,z882,z3,z5])],[(0,[z0,z883,z1,z2,z3,z5])],[(0,[z7,z0,z1,z72,z2,z5]),(0,[z0,z1,z2,z3,z5,z884]),(0,[z0,z1,z2,z3,z5,z885]),(0,[z0,z1,z2,z5,z6,z886])],[(0,[z0,z1,z2,z3,z5,z887]),(0,[z190,z7,z0,z1,z2,z5])],[(0,[z0,z1,z313,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z888])],[(0,[z0,z889,z2,z3,z5,z6]),(0,[z99,z7,z0,z1,z2,z5]),(0,[z0,z1,z2,z3,z5,z309]),(0,[z0,z1,z2,z3,z890,z6]),(0,[z0,z1,z2,z340,z3,z719]),(0,[z1,z2,z3,z5,z891,z8]),(0,[z892,z0,z1,z2,z5,z8])],[(0,[z0,z219,z220,z3,z5,z6]),(0,[z0,z1,z2,z3,z893,z6]),(0,[z0,z1,z2,z894,z265,z5]),(0,[z49,z1,z2,z3,z5,z153]),(0,[z17,z0,z895,z1,z2,z3])],[(0,[z0,z1,z2,z781,z3,z5])],[(0,[z0,z1,z220,z3,z5,z8]),(0,[z0,z896,z2,z3,z5,z6]),(0,[z0,z897,z2,z3,z5,z6]),(0,[z0,z106,z23,z3,z5,z8]),(0,[z0,z1,z2,z898,z5,z6])],[(0,[z17,z20,z1,z2,z3,z22]),(0,[z899,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z900,z6]),(0,[z0,z1,z2,z3,z801,z287]),(0,[z0,z1,z2,z3,z6,z901]),(0,[z7,z0,z1,z2,z5,z29]),(0,[z17,z902,z1,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z903,z3,z5]),(0,[z7,z49,z0,z1,z2,z5]),(0,[z0,z1,z2,z3,z230,z8]),(0,[z0,z1,z3,z5,z8,z603])],[(0,[z0,z1,z2,z3,z5,z904]),(0,[z0,z1,z2,z3,z5,z377]),(0,[z0,z1,z2,z261,z416,z6])],[(0,[z0,z905,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z906]),(0,[z0,z1,z2,z10,z173,z5])],[(0,[z279,z17,z1,z2,z3,z21]),(0,[z150,z1,z2,z3,z5,z192]),(0,[z0,z1,z2,z3,z907,z6]),(0,[z7,z0,z145,z1,z2,z5]),(0,[z7,z0,z1,z2,z5,z58]),(0,[z0,z1,z2,z261,z18,z6]),(0,[z0,z1,z908,z2,z435,z3])],[(0,[z324,z7,z0,z1,z2,z5]),(0,[z909,z1,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z910,z6]),(0,[z0,z1,z2,z911,z26,z6]),(0,[z17,z0,z1,z225,z2,z5]),(0,[z17,z0,z1,z2,z5,z559])],[(0,[z0,z461,z2,z3,z122,z6])],[],[],[(0,[z0,z1,z2,z912,z5,z6]),(0,[z0,z1,z2,z3,z5,z913]),(0,[z17,z0,z1,z2,z293,z5])],[],[(0,[z0,z1,z2,z3,z5,z914]),(0,[z211,z0,z1,z2,z18,z6])],[(0,[z176,z1,z72,z3,z5,z304]),(0,[z0,z1,z2,z393,z5,z137]),(0,[z634,z0,z1,z2,z10,z5])],[(0,[z42,z0,z2,z316,z67,z6]),(0,[z0,z2,z3,z5,z28,z915]),(0,[z0,z1,z2,z916,z3,z5]),(0,[z7,z0,z1,z2,z5,z137])],[(0,[z17,z321,z0,z1,z2,z5]),(0,[z0,z1,z2,z3,z917,z6]),(0,[z0,z1,z202,z3,z5,z8]),(0,[z7,z0,z1,z2,z918,z5])],[(0,[z0,z1,z2,z919,z3,z5]),(0,[z0,z1,z2,z3,z920,z6]),(0,[z0,z1,z2,z921,z3,z5]),(0,[z42,z0,z256,z2,z67,z6]),(0,[z0,z1,z2,z116,z3,z6])]],
   [[(0,[z17,z0,z1,z2,z481,z5]),(0,[z1,z2,z3,z5,z716,z192]),(0,[z7,z0,z1,z2,z5,z311])],[(0,[z0,z1,z220,z3,z64,z6]),(0,[z90,z708,z2,z3,z5,z6])],[(0,[z0,z1,z2,z835,z3,z287]),(0,[z0,z256,z1,z2,z3,z31]),(0,[z7,z0,z1,z2,z116,z6])],[(0,[z0,z1,z2,z3,z922,z6]),(0,[z90,z65,z2,z3,z5,z8]),(0,[z923,z0,z1,z2,z5,z6])],[(0,[z17,z176,z1,z72,z3,z5]),(0,[z7,z0,z1,z2,z2,z5])],[(0,[z0,z1,z2,z3,z5,z924]),(0,[z0,z1,z2,z116,z3,z37]),(0,[z30,z17,z0,z1,z27,z5]),(0,[z0,z1,z2,z3,z5,z925])],[(0,[z0,z1,z2,z3,z64,z31]),(0,[z0,z1,z2,z393,z3,z5]),(0,[z0,z1,z181,z10,z3,z46]),(0,[z0,z926,z2,z3,z5,z6])],[(0,[z99,z17,z1,z13,z3,z5]),(0,[z7,z0,z1,z2,z15,z5]),(0,[z223,z1,z2,z15,z5,z6]),(0,[z7,z20,z0,z1,z2,z5]),(0,[z7,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z927,z31])],[(0,[z0,z1,z722,z3,z5,z6]),(0,[z0,z1,z2,z10,z3,z50]),(0,[z0,z1,z2,z3,z5,z928]),(0,[z0,z1,z2,z929,z3,z5]),(0,[z75,z0,z1,z2,z116,z3])],[(0,[z0,z1,z2,z930,z132,z5]),(0,[z369,z1,z2,z15,z5,z6])],[(0,[z0,z1,z2,z3,z931,z6]),(0,[z0,z1,z2,z3,z932,z6]),(0,[z362,z1,z2,z3,z5,z37]),(0,[z38,z0,z1,z2,z26,z8])],[(0,[z0,z1,z2,z3,z5,z933]),(0,[z319,z1,z2,z3,z5,z192]),(0,[z0,z1,z2,z934,z3,z5])],[(0,[z7,z0,z1,z65,z2,z5]),(0,[z0,z1,z2,z3,z5,z935]),(0,[z0,z1,z2,z936,z3,z5]),(0,[z0,z1,z2,z10,z5,z423]),(0,[z17,z0,z1,z2,z3,z937])],[(0,[z0,z1,z2,z3,z938,z6]),(0,[z171,z1,z2,z720,z5,z6]),(0,[z279,z1,z2,z3,z21,z8]),(0,[z0,z1,z2,z81,z3,z200]),(0,[z0,z1,z2,z261,z18,z523]),(0,[z399,z0,z1,z2,z10,z5])],[(0,[z0,z1,z2,z3,z939,z6]),(0,[z0,z1,z2,z10,z3,z185]),(0,[z0,z1,z733,z3,z5,z6]),(0,[z940,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z5,z617])],[(0,[z17,z0,z1,z2,z682,z5]),(0,[z0,z145,z2,z768,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z941]),(0,[z0,z1,z2,z3,z5,z942]),(0,[z0,z1,z2,z3,z184,z6]),(0,[z0,z61,z1,z10,z3,z115])],[(0,[z0,z1,z2,z943,z3,z5]),(0,[z0,z1,z2,z3,z287,z8]),(0,[z0,z209,z2,z3,z179,z6])],[(0,[z418,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z10,z3,z64]),(0,[z0,z1,z2,z3,z719,z6]),(0,[z247,z1,z2,z3,z5,z153])],[(0,[z0,z1,z2,z244,z5,z598]),(0,[z0,z138,z2,z3,z5,z144]),(0,[z0,z1,z2,z3,z5,z944]),(0,[z0,z1,z2,z128,z5,z31]),(0,[z0,z1,z2,z3,z5,z945])],[(0,[z0,z1,z2,z10,z180,z5]),(0,[z17,z0,z1,z2,z5,z109])],[(0,[z219,z2,z248,z3,z5,z6]),(0,[z0,z1,z2,z265,z5,z312]),(0,[z0,z1,z2,z173,z5,z31]),(0,[z0,z1,z2,z3,z5,z946]),(0,[z0,z1,z2,z10,z3,z719])],[(0,[z90,z65,z2,z3,z64,z6]),(0,[z0,z1,z2,z3,z947,z6]),(0,[z17,z0,z1,z2,z103,z5]),(0,[z0,z218,z2,z3,z5,z28])],[(0,[z0,z145,z2,z14,z5,z6])],[(0,[z7,z0,z1,z2,z184,z6])],[(0,[z0,z1,z2,z948,z3,z5]),(0,[z0,z1,z2,z156,z5,z31]),(0,[z0,z1,z2,z3,z5,z949]),(0,[z0,z895,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z5,z950])],[(0,[z0,z1,z2,z3,z951,z6]),(0,[z0,z1,z3,z447,z5,z8])],[(0,[z0,z1,z2,z3,z35,z309]),(0,[z0,z1,z2,z3,z185,z309]),(0,[z0,z193,z2,z3,z68,z160]),(0,[z0,z1,z2,z952,z5,z6])],[(0,[z0,z1,z2,z3,z12,z8]),(0,[z99,z1,z13,z3,z5,z144]),(0,[z0,z1,z2,z3,z5,z953])],[(0,[z219,z708,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z48,z5]),(0,[z0,z1,z2,z5,z8,z886])],[]],
   [[(0,[z0,z1,z2,z3,z5,z954]),(0,[z42,z0,z256,z1,z2,z6]),(0,[z0,z1,z181,z589,z3,z6])],[(0,[z0,z1,z2,z3,z955,z5]),(0,[z0,z1,z2,z3,z5,z956])],[(0,[z957,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z958,z5,z6])],[(0,[z0,z1,z2,z776,z3,z5])],[(0,[z0,z1,z959,z3,z5,z6]),(0,[z0,z1,z2,z960,z5,z6]),(0,[z0,z1,z181,z2,z534,z3]),(0,[z0,z334,z2,z3,z160,z6])],[(0,[z17,z0,z1,z2,z132,z5]),(0,[z0,z1,z2,z3,z5,z961]),(0,[z1,z2,z48,z720,z5,z6]),(0,[z17,z0,z1,z2,z5,z747])],[(0,[z0,z1,z2,z3,z5,z962]),(0,[z0,z963,z1,z3,z5,z6]),(0,[z0,z1,z2,z10,z303,z5])],[(0,[z0,z1,z2,z3,z64,z325]),(0,[z78,z219,z2,z3,z5,z31]),(0,[z17,z0,z461,z2,z3,z5]),(0,[z0,z1,z2,z3,z353,z121])],[(0,[z0,z964,z1,z2,z3,z6])],[(0,[z7,z0,z1,z2,z10,z5])],[(0,[z0,z1,z2,z265,z5,z6]),(0,[z0,z1,z2,z965,z3,z6]),(0,[z75,z0,z2,z3,z5,z311]),(0,[z190,z940,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z966])],[(0,[z1,z708,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z967,z6]),(1,[z0,z2,z768,z5,z6]),(0,[z211,z0,z1,z2,z534,z5]),(0,[z0,z1,z76,z3,z5,z968])],[(0,[z0,z1,z2,z81,z3,z455]),(0,[z0,z1,z2,z3,z5,z432]),(0,[z0,z1,z2,z10,z3,z188]),(0,[z0,z1,z2,z3,z969,z6]),(0,[z0,z24,z2,z3,z5,z29])],[(0,[z0,z1,z2,z3,z5,z970]),(0,[z90,z17,z65,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z971]),(0,[z279,z1,z2,z128,z21,z6]),(0,[z0,z1,z2,z5,z159,z8]),(0,[z238,z0,z218,z2,z3,z5])],[(0,[z0,z381,z2,z3,z179,z6]),(0,[z17,z7,z0,z1,z2,z5]),(0,[z0,z972,z2,z3,z5,z6]),(0,[z0,z1,z2,z973,z3,z8])],[(0,[z7,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z974,z3,z5])]],
   [[(0,[z17,z0,z1,z2,z130,z5]),(0,[z0,z1,z2,z3,z975,z5])],[(0,[z0,z461,z2,z303,z5,z6]),(0,[z0,z1,z976,z3,z5,z6]),(0,[z0,z1,z977,z3,z5,z6]),(0,[z0,z61,z1,z3,z115,z8]),(0,[z7,z0,z1,z76,z5,z8])],[(0,[z0,z1,z2,z3,z5,z978]),(0,[z0,z1,z2,z534,z3,z22]),(0,[z0,z1,z116,z3,z31,z8]),(0,[z0,z1,z2,z81,z3,z469])],[],[(0,[z0,z1,z2,z3,z979,z5]),(0,[z190,z0,z1,z120,z140,z5])],[(0,[z0,z461,z2,z3,z5,z312]),(0,[z1,z2,z3,z720,z5,z6]),(0,[z279,z1,z2,z3,z21,z163]),(0,[z7,z0,z1,z2,z5,z37]),(0,[z0,z1,z2,z3,z980,z6]),(0,[z0,z1,z2,z981,z3,z5]),(0,[z0,z1,z2,z10,z3,z982])],[(0,[z0,z1,z2,z3,z983,z6]),(0,[z0,z1,z148,z132,z5,z6]),(0,[z0,z1,z2,z984,z5,z6]),(0,[z38,z0,z515,z1,z2,z6]),(0,[z0,z1,z2,z3,z5,z985]),(0,[z0,z1,z2,z3,z5,z968]),(0,[z0,z1,z170,z3,z5,z8]),(0,[z0,z1,z2,z116,z10,z3])],[(0,[z0,z1,z2,z3,z122,z31]),(0,[z0,z256,z1,z73,z2,z3]),(0,[z0,z1,z27,z3,z5,z31])],[(0,[z0,z1,z2,z15,z5,z141]),(0,[z17,z0,z133,z100,z3,z5]),(0,[z42,z0,z2,z67,z5,z8]),(0,[z30,z0,z1,z10,z52,z5])],[(0,[z0,z1,z2,z3,z986,z6]),(0,[z0,z1,z2,z263,z5,z280]),(0,[z0,z1,z2,z987,z3,z5]),(0,[z1,z2,z3,z988,z5,z6])],[(0,[z99,z1,z220,z3,z5,z6]),(0,[z418,z65,z2,z3,z5,z6]),(0,[z129,z7,z0,z1,z2,z5]),(0,[z0,z100,z724,z3,z5,z6]),(0,[z0,z1,z2,z5,z137,z377]),(0,[z0,z1,z2,z989,z3,z5]),(0,[z0,z1,z2,z3,z990,z8])],[(0,[z0,z1,z2,z173,z5,z192]),(0,[z17,z1,z2,z158,z3,z5]),(0,[z38,z0,z1,z2,z299,z6]),(0,[z0,z1,z2,z991,z3,z5])],[(0,[z0,z1,z2,z244,z5,z8]),(0,[z992,z0,z1,z2,z244,z5]),(0,[z0,z1,z2,z3,z5,z993]),(0,[z0,z1,z2,z263,z5,z31]),(0,[z0,z1,z2,z10,z3,z230]),(0,[z0,z193,z2,z159,z160,z6]),(0,[z7,z0,z1,z2,z5,z377]),(0,[z0,z1,z2,z994,z5,z6])],[(0,[z17,z0,z106,z23,z3,z5])],[(0,[z0,z1,z2,z3,z995,z6]),(0,[z211,z0,z1,z2,z26,z6]),(0,[z0,z996,z2,z3,z5,z6]),(0,[z0,z1,z181,z3,z46,z6]),(0,[z997,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z132,z5,z598]),(0,[z0,z1,z2,z3,z5,z998]),(0,[z0,z1,z2,z3,z5,z999]),(0,[z0,z1,z2,z1000,z5,z6]),(0,[z0,z1,z2,z140,z293,z5]),(0,[z0,z61,z1,z3,z115,z44]),(0,[z189,z0,z1,z3,z558,z5])]],
   [[(0,[z0,z138,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z22,z280]),(0,[z0,z1,z2,z10,z156,z5]),(0,[z0,z1,z2,z3,z5,z523]),(0,[z0,z1,z2,z10,z3,z1001]),(0,[z0,z1,z2,z10,z3,z1002])],[(0,[z0,z1,z2,z3,z1003,z5]),(0,[z0,z1,z5,z31,z423,z8])],[(0,[z0,z1,z2,z3,z1004,z6]),(0,[z0,z1,z2,z173,z187,z6]),(0,[z0,z1,z76,z435,z3,z5]),(0,[z0,z1,z2,z3,z5,z1005])],[(0,[z1,z2,z3,z721,z22,z6]),(0,[z0,z1,z2,z3,z5,z1006])],[(0,[z0,z1,z2,z1007,z5,z6])],[(0,[z0,z1,z2,z1008,z5,z6]),(0,[z1009,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z1010,z5,z6]),(1,[z30,z0,z1,z435,z5]),(0,[z9,z0,z1,z3,z558,z5])],[(0,[z0,z1,z2,z156,z187,z6])],[(0,[z0,z1,z2,z3,z1011,z6]),(0,[z0,z133,z100,z3,z5,z8]),(0,[z0,z193,z2,z534,z3,z160]),(0,[z0,z1,z2,z3,z778,z31])],[(0,[z1,z722,z13,z3,z5,z6]),(0,[z1,z2,z3,z721,z5,z6]),(0,[z17,z0,z1,z2,z3,z450]),(0,[z0,z1,z2,z1012,z5,z6])],[(0,[z0,z1,z2,z3,z1013,z6]),(0,[z0,z1,z2,z3,z800,z6])],[(0,[z0,z461,z2,z3,z5,z6]),(0,[z99,z1,z13,z3,z5,z8]),(0,[z0,z1,z314,z3,z5,z8]),(0,[z1014,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z5,z1015,z8]),(0,[z0,z1,z2,z3,z83,z58])],[(0,[z0,z1,z2,z10,z3,z1016])],[(0,[z0,z461,z2,z265,z5,z6]),(0,[z7,z0,z24,z1,z2,z5]),(0,[z0,z1,z2,z435,z3,z5]),(0,[z0,z1,z2,z3,z6,z1017])],[(0,[z0,z1,z2,z340,z3,z5]),(0,[z17,z0,z1,z2,z522,z5])],[(0,[z0,z1,z2,z244,z64,z6]),(0,[z17,z0,z1,z2,z3,z122]),(0,[z0,z1,z2,z3,z5,z1018]),(0,[z17,z0,z1019,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z1020])],[(0,[z1021,z0,z1,z2,z3,z5]),(0,[z190,z0,z1,z27,z3,z5])],[(0,[z0,z1,z100,z435,z3,z5]),(0,[z0,z61,z1,z435,z3,z5]),(0,[z7,z330,z0,z1,z2,z5])],[(0,[z241,z17,z0,z1,z2,z5]),(0,[z0,z1,z310,z2,z3,z8]),(0,[z1022,z1,z2,z3,z5,z8])],[(0,[z0,z1,z2,z3,z5,z304]),(0,[z0,z1,z2,z3,z5,z1023]),(0,[z0,z1,z2,z68,z5,z159]),(0,[z7,z0,z1,z2,z52,z5])],[(0,[z0,z1,z2,z3,z5,z1024]),(0,[z0,z1,z2,z828,z5,z6]),(0,[z0,z1,z2,z3,z316,z8]),(0,[z0,z1,z2,z1025,z3,z5])],[(0,[z279,z1,z2,z263,z21,z6]),(0,[z0,z1,z2,z3,z1026,z6])],[(0,[z0,z1,z2,z3,z1027,z6]),(0,[z0,z1,z2,z5,z831,z6]),(0,[z0,z1,z2,z3,z21,z280]),(0,[z0,z1,z2,z3,z5,z1028]),(0,[z1029,z7,z0,z1,z2,z5])],[(0,[z0,z1,z2,z3,z35,z6]),(0,[z0,z1,z2,z3,z185,z6])],[(0,[z0,z1,z148,z3,z5,z598]),(0,[z0,z1,z2,z303,z12,z6]),(0,[z20,z1,z2,z3,z22,z31]),(0,[z0,z1,z2,z1030,z5,z6]),(0,[z0,z1,z120,z140,z5,z31]),(0,[z0,z1,z2,z261,z911,z6])],[(0,[z0,z1,z2,z1031,z3,z5]),(0,[z1032,z7,z0,z1,z2,z5]),(0,[z0,z285,z2,z3,z5,z532])],[(0,[z584,z0,z2,z3,z5,z28]),(0,[z17,z0,z1,z2,z550,z5])],[(0,[z1,z2,z3,z5,z1033,z6]),(0,[z957,z211,z0,z1,z2,z5])],[(0,[z0,z1,z2,z3,z12,z312]),(0,[z279,z1,z2,z3,z721,z6])],[(0,[z0,z1,z1034,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1035]),(0,[z836,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z15,z5,z309]),(0,[z0,z24,z1,z2,z116,z3])],[(0,[z0,z1,z2,z3,z5,z1036]),(0,[z0,z1,z3,z5,z968,z8]),(0,[z0,z1,z589,z3,z5,z8])]],
   [[(0,[z0,z1,z2,z1037,z5,z6]),(0,[z57,z1,z2,z48,z5,z8]),(0,[z0,z1,z73,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1038]),(0,[z0,z32,z2,z3,z5,z529])],[(0,[z0,z154,z1,z3,z5,z8])],[],[(0,[z176,z1,z72,z10,z3,z5]),(0,[z0,z1,z2,z3,z187,z8]),(0,[z1039,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z188,z31]),(0,[z0,z1,z2,z3,z5,z1040])],[(0,[z0,z1,z2,z435,z48,z5]),(0,[z0,z1,z2,z3,z5,z1041]),(0,[z0,z193,z2,z3,z160,z31]),(0,[z7,z0,z1,z1042,z2,z5])],[(0,[z503,z1,z2,z3,z21,z6]),(0,[z42,z0,z2,z67,z188,z6]),(0,[z17,z0,z1,z2,z5,z396]),(0,[z0,z1,z2,z3,z1043,z8])],[(0,[z0,z1,z2,z3,z500,z6]),(0,[z0,z1,z2,z3,z5,z1044]),(0,[z17,z0,z1,z289,z2,z5]),(0,[z0,z1,z2,z3,z1001,z6]),(0,[z0,z193,z2,z3,z802,z6]),(0,[z0,z1,z2,z10,z5,z646]),(0,[z0,z1,z1045,z2,z3,z5])],[(0,[z0,z1,z2,z1046,z5,z6]),(0,[z0,z1,z2,z3,z5,z1047]),(0,[z30,z0,z1,z52,z5,z251]),(0,[z0,z1,z2,z3,z6,z856]),(0,[z190,z0,z1,z120,z2,z5])],[(0,[z0,z1,z2,z132,z5,z8]),(0,[z17,z0,z1,z2,z385,z5]),(0,[z0,z1,z2,z261,z444,z6]),(0,[z7,z0,z1,z2,z23,z5]),(0,[z0,z145,z2,z14,z5,z477])],[(0,[z0,z1,z2,z293,z5,z267])],[(0,[z0,z1,z2,z852,z3,z6]),(0,[z42,z17,z0,z2,z67,z5]),(0,[z0,z1,z2,z3,z1048,z5])],[(0,[z0,z1,z2,z1049,z5,z6]),(0,[z402,z0,z2,z67,z5,z6]),(0,[z0,z1,z3,z715,z5,z6]),(0,[z0,z1,z2,z3,z911,z6])],[(0,[z0,z1,z2,z3,z5,z1050]),(0,[z708,z65,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z173,z5]),(0,[z17,z0,z256,z1,z2,z3]),(0,[z0,z1,z3,z5,z31,z8])],[],[(0,[z0,z1,z2,z3,z1051,z6]),(0,[z0,z1,z2,z3,z1052,z5]),(0,[z0,z1,z2,z5,z423,z252]),(0,[z0,z1,z2,z3,z1053,z5]),(0,[z0,z1,z2,z3,z5,z1054])],[(0,[z0,z1,z2,z3,z239,z184]),(0,[z1,z2,z3,z5,z838,z31]),(0,[z17,z940,z1,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z10,z244,z5]),(0,[z0,z1055,z1,z2,z3,z5]),(0,[z0,z1,z76,z5,z423,z8])],[(0,[z0,z1,z2,z1056,z5,z6]),(0,[z0,z1,z2,z1057,z3,z5]),(0,[z0,z1058,z2,z3,z5,z6]),(0,[z418,z106,z23,z3,z5,z6]),(0,[z106,z158,z23,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1059])],[(0,[z0,z1,z2,z3,z12,z6]),(0,[z0,z1,z2,z303,z5,z31]),(0,[z17,z0,z1,z2,z513,z5]),(0,[z0,z1,z2,z1060,z3,z5]),(0,[z940,z1,z2,z3,z5,z31])],[(0,[z1,z2,z158,z3,z5,z6]),(0,[z0,z1,z2,z3,z1061,z6]),(0,[z129,z1,z2,z3,z5,z37]),(0,[z1062,z1,z2,z3,z5,z6])],[],[(0,[z0,z1,z3,z1063,z5,z6]),(0,[z0,z1,z2,z3,z866,z6]),(0,[z0,z1,z2,z3,z1064,z6]),(0,[z0,z1,z2,z5,z6,z1065]),(0,[z0,z1,z2,z1066,z5,z8]),(0,[z0,z1,z2,z116,z3,z82])],[(0,[z176,z1,z72,z3,z5,z31]),(0,[z0,z724,z23,z3,z5,z6]),(0,[z0,z1,z2,z1067,z3,z450])],[(0,[z0,z1,z2,z3,z5,z1068]),(0,[z0,z1,z2,z3,z5,z1069]),(0,[z17,z0,z1,z2,z681,z5]),(0,[z0,z1,z2,z3,z5,z107]),(0,[z75,z0,z2,z3,z612,z5]),(0,[z17,z0,z1,z2,z118,z5])],[(0,[z0,z1,z2,z10,z3,z5]),(0,[z7,z57,z0,z1,z2,z5]),(0,[z0,z1,z2,z3,z1070,z6]),(0,[z0,z1,z2,z3,z5,z477]),(0,[z0,z2,z3,z5,z915,z29]),(0,[z0,z1,z3,z780,z5,z6])],[(0,[z0,z1,z2,z1071,z5,z6]),(0,[z0,z1,z2,z3,z1072,z6]),(0,[z0,z126,z100,z3,z5,z6]),(0,[z0,z1,z2,z3,z1073,z6]),(1,[z0,z2,z3,z802,z6]),(0,[z17,z0,z1,z120,z140,z5]),(0,[z0,z1,z2,z3,z5,z1074]),(0,[z0,z1,z2,z3,z5,z1075])],[(0,[z0,z1,z2,z1076,z3,z5]),(0,[z42,z0,z378,z2,z5,z6]),(0,[z0,z1,z2,z184,z423,z6])],[(0,[z0,z1,z2,z132,z64,z6]),(0,[z530,z1,z2,z3,z21,z6]),(0,[z0,z145,z2,z14,z5,z31]),(0,[z0,z1,z2,z3,z1077,z5]),(0,[z0,z1,z2,z3,z58,z182]),(0,[z0,z1,z2,z3,z5,z1078]),(0,[z0,z1,z2,z5,z423,z8])],[(0,[z7,z0,z1,z2,z5,z26])],[(0,[z17,z0,z1,z2,z497,z5])],[(0,[z0,z1,z2,z3,z5,z1079])],[(0,[z0,z1,z1080,z2,z3,z6]),(0,[z63,z1,z2,z3,z21,z6]),(0,[z0,z1,z435,z3,z5,z31])]],
   [[(0,[z0,z1,z2,z936,z263,z5]),(0,[z211,z0,z1,z2,z5,z31]),(0,[z0,z1,z2,z3,z5,z1081]),(0,[z17,z0,z1,z2,z3,z980])],[(0,[z17,z0,z1,z2,z3,z50]),(0,[z0,z1,z2,z3,z1082,z6]),(0,[z0,z1,z2,z3,z1083,z6]),(0,[z7,z0,z1084,z1,z2,z5]),(0,[z38,z0,z1,z2,z911,z6])],[(0,[z0,z1,z148,z3,z5,z8]),(0,[z0,z1,z2,z5,z159,z6])],[(0,[z90,z7,z0,z1,z2,z5]),(0,[z0,z1,z1085,z2,z3,z5]),(0,[z1,z2,z3,z5,z891,z6]),(0,[z892,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z8,z1017]),(0,[z0,z1,z695,z3,z5,z8])],[(0,[z0,z1,z2,z1086,z5,z6]),(0,[z0,z1,z2,z1087,z3,z5]),(0,[z0,z138,z2,z3,z122,z6]),(0,[z30,z0,z1,z3,z558,z5]),(0,[z7,z0,z32,z1,z2,z5])],[(0,[z418,z1,z2,z3,z5,z1028]),(0,[z0,z1,z2,z3,z5,z1088]),(0,[z0,z1,z2,z3,z5,z1089]),(0,[z7,z0,z1,z2,z67,z5]),(0,[z30,z0,z1,z52,z5,z8]),(0,[z7,z0,z1,z2,z5,z386]),(0,[z17,z0,z1,z2,z5,z423])],[(0,[z0,z1,z220,z3,z5,z6]),(0,[z0,z1090,z2,z3,z5,z6]),(0,[z0,z1,z2,z10,z3,z12]),(0,[z0,z106,z23,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z228]),(0,[z0,z1,z2,z3,z5,z1091]),(0,[z7,z0,z1,z2,z14,z5])],[(0,[z992,z0,z1,z2,z3,z5]),(0,[z17,z0,z1,z2,z3,z185]),(0,[z0,z1,z2,z1092,z3,z5]),(0,[z0,z1,z3,z5,z31,z570])],[(0,[z0,z1,z2,z3,z1093,z5]),(0,[z0,z1,z2,z3,z5,z280]),(0,[z330,z1,z2,z3,z5,z192]),(0,[z0,z1,z2,z3,z230,z6]),(1,[z0,z1,z715,z5,z6]),(0,[z17,z0,z1,z908,z2,z3]),(0,[z0,z1,z2,z3,z58,z749])],[(0,[z0,z1,z1094,z3,z5,z6]),(0,[z0,z1,z2,z48,z5,z309]),(0,[z0,z1,z2,z3,z51,z31])],[],[(0,[z0,z1,z2,z3,z5,z31]),(0,[z17,z0,z1,z2,z3,z64]),(0,[z176,z1,z72,z3,z5,z291]),(0,[z0,z106,z23,z3,z5,z432]),(0,[z0,z106,z724,z3,z5,z6]),(0,[z0,z504,z2,z3,z179,z6])],[(0,[z0,z1,z2,z1095,z5,z6])],[(0,[z42,z0,z2,z67,z5,z6]),(0,[z0,z1,z2,z1096,z5,z8])],[(0,[z99,z1,z13,z3,z122,z6]),(0,[z17,z0,z1,z2,z172,z5]),(0,[z0,z1,z2,z3,z5,z1097]),(0,[z7,z0,z61,z1,z2,z5])],[(0,[z0,z1,z2,z3,z1098,z6]),(0,[z0,z1,z2,z5,z1099,z6]),(0,[z17,z0,z1,z2,z357,z5]),(0,[z0,z1,z2,z173,z50,z6]),(0,[z0,z1,z2,z3,z1100,z6])]],
   [[(0,[z0,z1,z2,z435,z15,z5]),(0,[z0,z1,z590,z3,z5,z8])],[(0,[z0,z1,z2,z3,z5,z1101]),(0,[z0,z1,z2,z18,z554,z6])],[(0,[z0,z1,z2,z3,z1102,z6]),(0,[z17,z0,z1,z2,z5,z332]),(0,[z411,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z5,z1103])],[(0,[z0,z1,z2,z156,z50,z6]),(0,[z0,z61,z1,z3,z115,z335])],[(0,[z0,z1,z2,z1104,z5,z6]),(0,[z0,z1105,z1,z2,z3,z5]),(0,[z0,z403,z2,z14,z5,z6])],[(0,[z0,z1,z148,z3,z64,z6]),(0,[z1106,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z1107])],[(0,[z0,z1,z425,z3,z46,z6]),(0,[z0,z1,z2,z3,z5,z1108])],[(0,[z0,z1109,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1110]),(0,[z0,z1,z2,z81,z3,z149]),(0,[z0,z1,z2,z3,z1111,z6])],[(0,[z0,z1,z2,z3,z1112,z5]),(0,[z0,z1,z2,z3,z5,z1113]),(0,[z30,z0,z1,z715,z5,z6]),(0,[z0,z1,z2,z3,z5,z1114]),(0,[z0,z1,z2,z3,z1115,z8])],[(0,[z1116,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z1117,z3,z5]),(0,[z0,z1,z2,z116,z423,z8])],[(0,[z90,z65,z2,z3,z5,z6]),(0,[z7,z0,z193,z1,z2,z5]),(0,[z812,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z588,z5]),(0,[z0,z1,z2,z261,z18,z31])],[(0,[z0,z1,z2,z3,z5,z1118]),(0,[z0,z133,z100,z3,z5,z6]),(0,[z0,z1,z2,z3,z910,z31])],[(0,[z0,z1,z2,z3,z5,z1119]),(0,[z0,z1,z2,z10,z195,z5]),(0,[z0,z1120,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1121]),(0,[z7,z0,z1,z76,z2,z5])],[(0,[z0,z1,z2,z1122,z5,z6]),(0,[z0,z1,z1123,z3,z5,z6]),(0,[z17,z0,z1,z2,z303,z5]),(0,[z0,z1,z2,z3,z5,z1124]),(0,[z0,z1,z2,z288,z3,z5]),(0,[z0,z1,z2,z3,z1125,z5]),(0,[z0,z1,z181,z3,z538,z6]),(0,[z232,z0,z1,z2,z10,z5]),(0,[z17,z1126,z1,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z291]),(0,[z129,z1,z2,z3,z5,z82]),(0,[z0,z1,z2,z3,z5,z915])],[(0,[z0,z342,z2,z3,z160,z6]),(0,[z0,z1,z2,z10,z3,z51])],[(0,[z1,z2,z3,z1127,z5,z6]),(0,[z38,z0,z1,z2,z26,z6]),(0,[z0,z1,z2,z81,z3,z233])],[(0,[z0,z1,z2,z3,z5,z1128]),(0,[z0,z1,z73,z2,z15,z5]),(0,[z0,z1,z2,z3,z5,z1129])],[(0,[z0,z1,z2,z3,z5,z1130]),(0,[z0,z1,z2,z1131,z5,z6])],[(0,[z0,z1,z2,z3,z5,z86]),(0,[z279,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z450,z8]),(0,[z17,z0,z1,z2,z3,z188]),(0,[z0,z145,z2,z5,z146,z6]),(0,[z7,z0,z1,z2,z5,z82])],[(0,[z0,z1,z2,z48,z5,z141]),(0,[z418,z1,z2,z10,z3,z5]),(0,[z189,z17,z0,z1,z2,z5]),(0,[z0,z1,z2,z116,z3,z31]),(0,[z17,z0,z1,z976,z3,z5])],[(0,[z30,z0,z1,z53,z52,z5]),(0,[z0,z1,z2,z3,z58,z335]),(0,[z0,z1,z908,z2,z3,z6])],[(0,[z1022,z1,z2,z3,z5,z6]),(0,[z1132,z0,z1,z2,z5,z6]),(0,[z30,z17,z0,z1,z2,z5]),(0,[z0,z1,z310,z2,z3,z6])],[(0,[z0,z665,z23,z3,z5,z6]),(0,[z0,z1,z2,z3,z287,z6])],[(0,[z0,z1,z458,z3,z5,z31]),(0,[z0,z1,z2,z3,z316,z6]),(0,[z0,z1,z140,z3,z558,z5]),(0,[z526,z0,z1,z435,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1133]),(0,[z7,z0,z133,z1,z2,z5]),(0,[z0,z1,z2,z3,z1134,z6])],[(0,[z0,z1,z2,z3,z5,z325]),(0,[z17,z0,z1,z120,z2,z5])],[(0,[z0,z1,z2,z3,z5,z1135])],[(0,[z0,z65,z220,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1136]),(0,[z0,z1,z120,z340,z140,z5])],[(0,[z418,z1,z2,z3,z1082,z6]),(0,[z418,z1,z2,z3,z1083,z6])]],
   [[(0,[z0,z1,z2,z3,z50,z8])],[(0,[z176,z0,z1,z435,z3,z5]),(0,[z0,z24,z2,z162,z3,z5]),(0,[z0,z1,z2,z3,z25,z329]),(0,[z7,z0,z1,z2,z25,z5]),(0,[z0,z1,z2,z10,z5,z137])],[(0,[z0,z1,z2,z3,z5,z1137]),(0,[z0,z1,z1138,z3,z5,z6]),(0,[z0,z1,z2,z1139,z5,z6]),(0,[z0,z1,z181,z404,z3,z6])],[(0,[z418,z1,z2,z3,z5,z1088])],[(0,[z418,z1,z220,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1140])],[(0,[z0,z1,z2,z10,z3,z287]),(0,[z17,z0,z1,z2,z3,z230]),(0,[z0,z1,z2,z3,z5,z1141]),(0,[z30,z17,z0,z1,z120,z5]),(0,[z17,z0,z1,z1142,z3,z5])],[(0,[z1143,z0,z1,z2,z3,z5]),(0,[z63,z1,z2,z3,z5,z37]),(0,[z0,z1,z2,z3,z5,z1144]),(0,[z0,z1,z340,z3,z558,z5]),(0,[z17,z0,z1,z2,z383,z5])],[(0,[z17,z0,z1,z2,z5,z252]),(0,[z0,z1,z2,z3,z184,z31])],[(0,[z0,z1,z2,z265,z12,z6]),(0,[z0,z1,z2,z3,z1145,z6]),(0,[z0,z209,z2,z3,z179,z31]),(0,[z0,z2,z3,z5,z915,z6])],[(0,[z0,z1,z2,z3,z5,z1146]),(0,[z17,z0,z1,z2,z156,z5]),(0,[z418,z1,z2,z3,z5,z31]),(0,[z211,z0,z193,z2,z160,z6]),(0,[z0,z1,z2,z261,z660,z6]),(0,[z17,z0,z1,z2,z295,z5]),(0,[z0,z1,z120,z2,z53,z5]),(0,[z17,z0,z1,z2,z5,z611]),(0,[z0,z1,z2,z1147,z5,z8]),(0,[z55,z7,z0,z1,z2,z5])],[(0,[z0,z1,z73,z2,z48,z5])],[(0,[z0,z1,z2,z3,z5,z1148]),(0,[z0,z1,z2,z3,z1149,z6]),(0,[z1150,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1151,z6]),(0,[z1152,z7,z0,z1,z2,z5])],[(0,[z0,z1,z2,z1153,z5,z6]),(0,[z57,z1,z2,z48,z5,z309]),(0,[z0,z2,z14,z768,z5,z6]),(0,[z0,z1,z3,z115,z780,z6])],[(0,[z17,z0,z926,z2,z3,z5])],[(0,[z0,z1,z140,z715,z5,z6])],[(0,[z0,z138,z2,z303,z5,z6])]],
   [[(0,[z17,z0,z1,z2,z19,z5]),(0,[z0,z297,z1,z3,z5,z31])],[(0,[z744,z0,z1,z2,z132,z5]),(0,[z1154,z0,z1,z2,z303,z5]),(1,[z0,z1,z3,z780,z6])],[(0,[z0,z1,z2,z3,z5,z1155]),(0,[z57,z1,z2,z10,z48,z5])],[(0,[z0,z138,z2,z3,z5,z312]),(0,[z0,z256,z1,z2,z3,z8]),(0,[z0,z1,z2,z3,z1156,z6]),(0,[z0,z1,z2,z1157,z3,z5])],[(0,[z7,z0,z1,z2,z21,z5]),(0,[z7,z0,z1,z2,z5,z529]),(0,[z0,z1,z2,z3,z1158,z8])],[(0,[z0,z1,z220,z3,z500,z6]),(0,[z17,z0,z1,z625,z2,z5]),(0,[z0,z1,z2,z3,z1159,z450])],[(0,[z1160,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z973,z3,z6]),(0,[z362,z1,z2,z3,z5,z257])],[(1,[z1,z2,z3,z5,z716]),(0,[z0,z2,z3,z802,z5,z6])],[(0,[z0,z1,z2,z10,z3,z35]),(0,[z418,z17,z1,z2,z3,z5]),(0,[z324,z0,z1,z2,z116,z3]),(0,[z7,z0,z1,z2,z116,z5]),(0,[z0,z1,z2,z1161,z5,z8]),(0,[z0,z1,z2,z3,z5,z1162])],[(0,[z99,z1,z13,z303,z5,z6]),(0,[z171,z7,z0,z1,z2,z5]),(0,[z0,z1,z2,z3,z693,z58]),(0,[z0,z1,z391,z3,z5,z8]),(0,[z17,z0,z1,z2,z549,z5]),(0,[z0,z1163,z1,z2,z3,z5]),(0,[z0,z61,z1,z3,z115,z6])],[(0,[z0,z1,z2,z3,z5,z1164]),(0,[z0,z1,z2,z1066,z5,z6]),(0,[z0,z1,z2,z10,z5,z71])],[(0,[z0,z1,z1165,z3,z5,z6]),(0,[z0,z1,z2,z3,z122,z144]),(0,[z0,z1,z2,z15,z185,z6]),(0,[z0,z1,z2,z3,z5,z1166])],[(0,[z0,z1,z2,z10,z3,z500]),(0,[z0,z1,z2,z116,z3,z192]),(0,[z0,z1,z724,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1167]),(0,[z0,z1,z120,z140,z5,z419]),(0,[z0,z1019,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z749])],[(0,[z99,z1,z13,z3,z5,z312]),(0,[z1168,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1169,z6]),(1,[z7,z0,z1,z2,z184])],[(0,[z0,z1,z2,z3,z5,z1170]),(0,[z0,z1,z2,z1171,z5,z6]),(0,[z0,z1,z2,z3,z1172,z6]),(0,[z0,z1,z2,z3,z5,z1173]),(0,[z0,z24,z2,z3,z5,z532]),(0,[z7,z0,z1,z181,z2,z5]),(0,[z0,z1174,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1175]),(0,[z0,z1,z2,z10,z5,z268])],[(0,[z0,z269,z2,z3,z5,z29])]],
   [[(0,[z0,z1,z2,z1176,z5,z6]),(0,[z7,z0,z1177,z1,z2,z5]),(0,[z7,z0,z1,z2,z3,z184]),(0,[z0,z1,z3,z5,z31,z968])],[(0,[z0,z1,z2,z265,z5,z31]),(0,[z0,z2,z3,z1178,z5,z6]),(0,[z0,z1,z2,z3,z5,z1179]),(0,[z0,z1,z271,z3,z5,z31])],[(0,[z0,z1,z2,z1180,z5,z6]),(0,[z0,z1,z2,z3,z990,z6]),(0,[z38,z0,z1,z2,z283,z6])],[(0,[z38,z0,z1,z2,z424,z6]),(0,[z38,z0,z1,z2,z426,z6]),(0,[z0,z1,z2,z293,z3,z5])],[(0,[z0,z1,z2,z244,z5,z6]),(0,[z0,z1,z2,z3,z5,z1181]),(0,[z0,z1,z2,z3,z1182,z6]),(0,[z0,z1,z2,z128,z5,z8]),(0,[z7,z0,z1,z2,z18,z5]),(0,[z0,z1,z2,z5,z6,z747])],[(0,[z0,z1,z2,z10,z387,z5])],[(0,[z176,z1,z722,z3,z5,z6]),(0,[z0,z1,z2,z3,z35,z86]),(0,[z0,z1,z2,z3,z185,z86]),(0,[z0,z1,z2,z173,z5,z8]),(0,[z0,z106,z23,z3,z5,z107]),(0,[z0,z1,z2,z3,z5,z1183]),(0,[z0,z1184,z2,z3,z5,z8]),(0,[z7,z0,z1,z2,z5,z31])],[(0,[z171,z1,z2,z15,z5,z8]),(0,[z17,z1,z2,z48,z15,z5]),(0,[z166,z1,z2,z3,z5,z192]),(0,[z0,z106,z23,z10,z3,z5])],[(0,[z0,z138,z2,z3,z5,z6]),(0,[z0,z461,z2,z3,z12,z6]),(0,[z0,z1,z2,z3,z1185,z6]),(0,[z0,z1,z120,z10,z140,z5])],[(0,[z1186,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z776,z5]),(0,[z7,z0,z1,z2,z340,z5]),(0,[z0,z1,z3,z5,z8,z412])],[(0,[z90,z65,z2,z3,z500,z6]),(0,[z454,z1,z2,z15,z5,z6]),(0,[z0,z1,z2,z156,z5,z8]),(0,[z0,z1,z2,z3,z937,z6])],[(0,[z0,z138,z2,z265,z5,z6]),(0,[z0,z2,z3,z1187,z5,z6]),(0,[z171,z1,z2,z393,z15,z5]),(0,[z17,z0,z1,z2,z393,z5]),(0,[z0,z1,z181,z3,z780,z6])],[(0,[z0,z1,z2,z1188,z3,z5])],[(0,[z0,z1,z225,z3,z5,z8])],[(0,[z0,z1,z2,z3,z5,z1189]),(0,[z0,z461,z2,z10,z3,z5]),(0,[z0,z1,z2,z3,z5,z1190])],[(0,[z0,z1,z2,z3,z5,z1191]),(0,[z0,z1,z310,z2,z10,z3]),(0,[z0,z1,z2,z3,z5,z1192]),(0,[z7,z0,z1,z2,z5,z1193]),(0,[z0,z1,z2,z81,z3,z245])]],
   [[(0,[z0,z1,z74,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z1194])],[(0,[z0,z1,z2,z3,z64,z598]),(0,[z0,z1195,z2,z3,z5,z6])],[(0,[z99,z1,z13,z3,z5,z6]),(0,[z0,z1,z2,z1096,z5,z6]),(0,[z1196,z0,z1,z2,z3,z5]),(0,[z56,z7,z0,z1,z2,z5])],[(0,[z0,z1,z1197,z3,z5,z6]),(0,[z0,z1,z2,z3,z1198,z6]),(0,[z0,z1,z2,z5,z1015,z6]),(0,[z0,z1,z2,z994,z5,z31])],[(0,[z0,z1,z2,z3,z5,z1199]),(0,[z456,z1,z2,z48,z5,z6]),(0,[z0,z1,z2,z3,z5,z1200])],[(0,[z99,z1,z13,z265,z5,z6]),(0,[z0,z1201,z1,z2,z3,z5]),(0,[z0,z1,z2,z1202,z5,z6]),(0,[z0,z1,z2,z3,z1203,z5]),(0,[z0,z1,z181,z3,z46,z31])],[(0,[z279,z7,z0,z1,z2,z5]),(0,[z0,z1,z2,z116,z340,z3])],[(0,[z0,z1,z2,z53,z3,z5]),(0,[z0,z1,z2,z5,z31,z423])],[(0,[z78,z219,z2,z3,z5,z8]),(0,[z0,z1204,z2,z3,z5,z6]),(0,[z0,z1,z2,z1205,z3,z5])],[(0,[z17,z0,z1,z2,z244,z5]),(0,[z0,z1,z2,z1206,z5,z6]),(0,[z0,z1,z2,z3,z5,z1207]),(0,[z1208,z1,z2,z3,z5,z6]),(0,[z902,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1209,z5,z6])],[(0,[z0,z106,z23,z3,z5,z31]),(0,[z324,z0,z2,z3,z5,z311]),(0,[z38,z0,z1,z2,z475,z6])],[(0,[z17,z78,z219,z2,z3,z5]),(0,[z0,z1,z310,z2,z15,z6]),(0,[z0,z256,z1,z2,z288,z3]),(0,[z0,z1,z113,z3,z5,z8])],[(0,[z418,z1,z72,z3,z5,z6]),(0,[z0,z1,z2,z10,z263,z5]),(0,[z0,z1,z2,z3,z1002,z6])],[(0,[z817,z0,z1,z2,z3,z5]),(0,[z0,z1210,z2,z3,z5,z6])],[(0,[z0,z1,z3,z5,z1211,z6]),(0,[z1,z72,z722,z3,z5,z6])],[(0,[z190,z0,z1,z2,z15,z5]),(0,[z211,z0,z1,z2,z450,z6]),(0,[z0,z61,z1,z2,z534,z3]),(0,[z190,z0,z1,z2,z3,z5]),(0,[z0,z1,z120,z2,z435,z5]),(0,[z0,z1,z2,z116,z423,z6])]],
   [[(0,[z0,z1212,z1,z2,z3,z6]),(0,[z0,z1,z3,z5,z31,z161]),(0,[z0,z1,z2,z3,z5,z747]),(0,[z229,z1,z2,z3,z118,z5])],[(0,[z17,z0,z1,z2,z3,z5]),(0,[z0,z461,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z1213,z5]),(0,[z1214,z0,z1,z2,z5,z8])],[(0,[z0,z1,z2,z3,z1215,z5]),(0,[z0,z1,z435,z3,z5,z46]),(0,[z0,z1,z2,z3,z5,z1216])],[(0,[z0,z1,z2,z1217,z3,z5]),(0,[z17,z0,z1,z2,z210,z5])],[(0,[z0,z1,z2,z3,z1218,z6]),(0,[z0,z1,z2,z1219,z5,z6]),(0,[z0,z1,z2,z3,z5,z1220]),(0,[z0,z1,z2,z10,z261,z18])],[(0,[z0,z1,z170,z340,z3,z5])],[(0,[z0,z1,z2,z48,z185,z6]),(0,[z17,z578,z1,z2,z48,z5]),(0,[z0,z1,z1142,z3,z5,z6]),(0,[z0,z1,z2,z5,z137,z747])],[(0,[z0,z1,z3,z5,z968,z6]),(0,[z1221,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z122,z8]),(0,[z57,z1,z2,z48,z5,z6]),(0,[z30,z17,z0,z1,z52,z5]),(0,[z330,z1,z2,z3,z5,z104])],[(0,[z0,z1,z2,z81,z3,z322]),(0,[z0,z1,z2,z116,z3,z104])],[(0,[z0,z1,z2,z3,z5,z716]),(0,[z0,z1222,z1,z2,z3,z5]),(0,[z0,z1,z2,z1223,z3,z5]),(0,[z0,z1,z2,z3,z450,z6]),(0,[z211,z0,z209,z1,z2,z6]),(0,[z17,z0,z1,z2,z651,z5])],[(0,[z0,z1,z2,z3,z187,z6]),(0,[z0,z1,z2,z1224,z3,z5]),(0,[z0,z358,z2,z3,z5,z28])],[(0,[z0,z1,z2,z3,z5,z1225]),(0,[z0,z1,z2,z128,z5,z163]),(0,[z7,z0,z1,z2,z5,z192]),(0,[z0,z1,z2,z3,z5,z367]),(0,[z0,z1,z2,z3,z5,z1226]),(0,[z0,z209,z2,z3,z802,z6]),(0,[z0,z1,z2,z368,z18,z6])],[(0,[z0,z1,z2,z1227,z3,z5]),(0,[z0,z1,z2,z1228,z5,z6]),(0,[z129,z1,z2,z3,z5,z716]),(0,[z0,z1,z2,z340,z3,z1043]),(0,[z0,z1,z2,z3,z1043,z6]),(0,[z38,z0,z1,z2,z365,z26])],[(0,[z0,z1,z2,z3,z1229,z6]),(0,[z0,z1,z2,z53,z48,z5]),(0,[z0,z1,z2,z3,z5,z1230]),(0,[z1231,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1232])],[(0,[z17,z0,z1,z2,z3,z12]),(0,[z0,z1,z2,z5,z1099,z304]),(0,[z0,z1,z2,z3,z35,z31]),(0,[z0,z1,z2,z3,z185,z31]),(0,[z1233,z7,z0,z1,z2,z5])]],
   [[(0,[z0,z1,z2,z132,z5,z6]),(0,[z0,z1,z2,z3,z5,z1234]),(0,[z0,z1,z2,z3,z5,z1235]),(0,[z0,z1,z3,z5,z31,z413]),(0,[z0,z1,z2,z18,z911,z6])],[(0,[z0,z1,z2,z3,z187,z37]),(0,[z0,z1,z2,z1236,z3,z5]),(0,[z17,z0,z145,z2,z14,z5]),(0,[z7,z7,z0,z1,z2,z5]),(0,[z17,z0,z1,z2,z116,z3]),(0,[z0,z1,z2,z365,z3,z5])],[(0,[z0,z97,z1,z2,z3,z5]),(0,[z0,z1,z310,z2,z48,z6]),(0,[z1237,z211,z0,z1,z2,z5]),(0,[z0,z1,z2,z10,z5,z159])],[(0,[z0,z1,z2,z3,z1238,z6]),(0,[z17,z567,z0,z1,z2,z5])],[],[],[(0,[z0,z1,z2,z3,z1239,z6]),(0,[z418,z138,z2,z3,z5,z6]),(0,[z0,z1,z2,z303,z5,z144]),(0,[z190,z0,z1,z2,z48,z5]),(0,[z279,z1,z2,z3,z21,z280]),(0,[z578,z1,z2,z3,z5,z37]),(0,[z0,z1,z2,z3,z5,z786])],[(0,[z0,z1240,z2,z3,z5,z6]),(0,[z0,z1241,z1,z2,z3,z5]),(0,[z1,z2,z158,z10,z3,z5]),(0,[z17,z0,z1,z170,z2,z5])],[(0,[z17,z0,z1,z2,z48,z5]),(0,[z0,z1,z73,z2,z3,z316]),(0,[z7,z0,z1,z2,z5,z160])],[(0,[z0,z1,z2,z1242,z5,z6])],[(0,[z0,z1,z148,z3,z5,z853]),(0,[z0,z1,z2,z3,z64,z8]),(0,[z468,z1,z2,z15,z5,z6]),(0,[z0,z2,z3,z179,z802,z6]),(0,[z0,z1,z2,z3,z5,z1243]),(0,[z0,z1,z446,z3,z5,z31])],[(0,[z1,z72,z690,z3,z5,z6]),(0,[z0,z1,z1244,z2,z3,z6]),(0,[z1237,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1245,z5]),(0,[z38,z0,z342,z1,z2,z6])],[(0,[z0,z1,z2,z1246,z3,z5]),(0,[z0,z1247,z1,z2,z3,z5]),(0,[z0,z1,z2,z293,z5,z137])],[(0,[z0,z1,z2,z3,z500,z31]),(0,[z0,z1,z120,z140,z5,z252]),(0,[z0,z1,z2,z1248,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1249]),(0,[z266,z1,z2,z3,z22,z6]),(0,[z17,z0,z61,z1,z3,z115])],[]],
   [[(0,[z211,z0,z1,z2,z68,z5]),(0,[z0,z1,z2,z53,z3,z51]),(0,[z0,z1,z2,z813,z5,z6])],[(0,[z0,z1,z2,z3,z982,z6]),(0,[z0,z1,z1250,z2,z3,z5])],[(0,[z7,z0,z1,z2,z13,z5]),(0,[z1116,z0,z1,z2,z128,z5]),(0,[z0,z1,z2,z5,z911,z6])],[(0,[z0,z1,z2,z3,z5,z807]),(0,[z0,z1,z2,z244,z500,z6]),(0,[z0,z1,z2,z3,z1251,z5]),(0,[z410,z219,z2,z3,z5,z6]),(0,[z1154,z0,z1,z2,z3,z5]),(0,[z1252,z0,z1,z2,z3,z6]),(0,[z418,z1,z2,z1202,z5,z6]),(0,[z0,z1,z2,z3,z5,z1253]),(0,[z0,z1,z2,z5,z423,z6]),(0,[z17,z0,z1,z2,z10,z5])],[(0,[z1254,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z1255]),(0,[z0,z1,z625,z140,z5,z6]),(0,[z0,z1,z1256,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1257]),(0,[z0,z1,z637,z3,z5,z8]),(0,[z75,z0,z2,z3,z5,z915]),(0,[z0,z1,z2,z3,z5,z433]),(0,[z1126,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1258]),(0,[z17,z0,z1,z2,z3,z1259])],[(0,[z0,z1,z120,z5,z161,z6])],[(0,[z0,z1,z2,z3,z829,z6]),(0,[z0,z1,z2,z340,z3,z184])],[(0,[z0,z1,z2,z3,z1260,z6]),(0,[z0,z1,z2,z930,z3,z5]),(0,[z0,z1,z2,z3,z5,z1261]),(0,[z1262,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z12,z31]),(0,[z418,z1,z13,z3,z5,z6]),(0,[z0,z1,z2,z3,z1158,z6]),(0,[z319,z1,z2,z172,z3,z5])],[(0,[z0,z1,z148,z3,z5,z6]),(0,[z0,z1,z220,z10,z3,z5]),(0,[z20,z1,z2,z3,z22,z8]),(0,[z1,z2,z158,z3,z5,z31]),(0,[z0,z1,z2,z3,z5,z1263]),(0,[z17,z0,z1,z2,z3,z51]),(0,[z0,z1,z120,z140,z5,z8])],[(0,[z38,z0,z1,z2,z575,z6]),(0,[z0,z1,z2,z3,z68,z5]),(0,[z0,z1,z1264,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1265]),(0,[z0,z2,z3,z5,z804,z8])],[(0,[z0,z1,z2,z3,z5,z1266]),(0,[z0,z292,z1,z3,z115,z6]),(0,[z30,z0,z1,z52,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1267]),(0,[z0,z1,z2,z5,z159,z1081])],[(0,[z0,z1,z2,z3,z5,z144]),(0,[z755,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1268]),(0,[z30,z0,z1,z51,z52,z6]),(0,[z0,z1,z2,z3,z1070,z31])]],
   [[(0,[z0,z1,z148,z3,z5,z970]),(0,[z0,z1,z2,z894,z3,z5]),(0,[z0,z1,z2,z1269,z3,z5]),(0,[z0,z1,z2,z10,z3,z316]),(0,[z0,z1,z2,z3,z5,z1270]),(0,[z0,z1,z3,z5,z31,z678])],[(0,[z0,z1,z2,z752,z3,z6]),(0,[z0,z1,z425,z3,z5,z8]),(0,[z0,z1,z2,z1271,z3,z5])],[(0,[z0,z1272,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1273,z5])],[(0,[z0,z1,z2,z3,z5,z1274]),(0,[z1275,z0,z1,z2,z3,z5]),(0,[z0,z895,z1,z2,z435,z3])],[(0,[z0,z1,z2,z3,z5,z1276]),(0,[z0,z1,z841,z3,z5,z6]),(0,[z0,z1,z2,z128,z22,z6]),(0,[z0,z1,z2,z3,z188,z8])],[(0,[z0,z1,z2,z263,z5,z163]),(0,[z0,z1,z2,z3,z5,z1277]),(0,[z0,z193,z2,z3,z160,z8]),(0,[z0,z1,z2,z715,z5,z6]),(0,[z17,z718,z1,z2,z3,z5])],[(0,[z17,z0,z1,z2,z5,z377])],[(0,[z9,z0,z1,z3,z5,z968]),(0,[z0,z1,z2,z10,z3,z1043])],[(0,[z0,z1,z2,z1278,z3,z5]),(0,[z0,z24,z2,z3,z5,z915]),(0,[z0,z1,z2,z10,z661,z5])],[(0,[z57,z1,z2,z48,z35,z6]),(0,[z57,z1,z2,z48,z185,z6]),(0,[z0,z1,z2,z5,z159,z31]),(0,[z7,z0,z1,z2,z5,z104])],[(0,[z0,z1,z2,z53,z15,z5]),(0,[z0,z1,z2,z3,z5,z1279]),(0,[z0,z1,z2,z768,z5,z6]),(0,[z30,z0,z1,z52,z5,z377]),(0,[z7,z0,z1,z2,z5,z109]),(0,[z0,z1,z2,z3,z5,z1280])],[(0,[z0,z1,z2,z3,z5,z1281]),(0,[z0,z2,z3,z768,z5,z6]),(0,[z7,z0,z1,z2,z5,z28]),(0,[z0,z1,z435,z140,z3,z5]),(0,[z17,z0,z1,z2,z3,z1100])],[(0,[z0,z1,z2,z3,z5,z1282]),(0,[z0,z1,z2,z1283,z5,z6]),(0,[z171,z1,z2,z15,z5,z6]),(0,[z0,z1,z201,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z1284]),(0,[z190,z0,z1,z2,z5,z236])],[(0,[z0,z1,z220,z3,z5,z31]),(0,[z30,z0,z1,z310,z52,z6]),(0,[z0,z1,z2,z3,z1285,z5])],[(0,[z0,z1,z2,z3,z500,z325]),(0,[z785,z0,z1,z72,z2,z5]),(0,[z0,z1,z2,z3,z1016,z6]),(0,[z0,z1,z2,z955,z15,z5]),(0,[z17,z0,z1,z2,z3,z287]),(0,[z0,z1,z2,z81,z3,z749])],[(0,[z90,z65,z2,z10,z3,z5]),(0,[z0,z1,z1286,z3,z5,z6]),(0,[z0,z1,z2,z10,z5,z593]),(0,[z0,z1,z2,z3,z230,z31])]],
   [[(0,[z49,z1,z2,z3,z5,z192]),(0,[z0,z1,z2,z3,z1115,z6]),(0,[z0,z133,z100,z10,z3,z5])],[(0,[z0,z1,z1287,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1288])],[(0,[z0,z1,z2,z3,z1289,z5])],[(0,[z0,z1,z220,z244,z5,z6]),(0,[z0,z1,z2,z303,z5,z8]),(0,[z0,z1290,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1291]),(0,[z0,z1,z2,z3,z1292,z6]),(0,[z1,z2,z3,z5,z716,z6]),(0,[z0,z1,z1293,z2,z3,z5]),(1,[z0,z1,z2,z911,z6])],[(0,[z17,z0,z1,z2,z15,z5]),(0,[z0,z1,z2,z1294,z3,z5]),(0,[z0,z1,z2,z10,z128,z5]),(0,[z42,z0,z2,z67,z5,z31]),(0,[z0,z1295,z1,z2,z3,z5])],[(0,[z0,z1,z2,z1296,z3,z5]),(0,[z75,z7,z0,z1,z2,z5])],[(0,[z0,z1,z2,z3,z5,z1297]),(0,[z0,z1298,z1,z2,z3,z5]),(0,[z85,z429,z1,z2,z3,z5])],[(0,[z0,z154,z23,z3,z5,z6]),(0,[z176,z1,z72,z3,z5,z8]),(0,[z0,z1,z360,z3,z5,z31])],[(0,[z0,z1,z2,z3,z5,z1299]),(0,[z0,z1,z2,z3,z25,z16])],[(0,[z0,z1,z1300,z2,z3,z6])],[(0,[z7,z0,z219,z1,z2,z5]),(0,[z0,z1,z2,z172,z173,z5])],[(0,[z0,z1,z2,z3,z5,z1301]),(0,[z0,z1,z2,z128,z21,z6]),(0,[z0,z1,z2,z10,z3,z187]),(0,[z0,z1,z2,z3,z1302,z6]),(0,[z0,z1,z2,z3,z5,z1303]),(0,[z0,z1,z2,z3,z5,z1304])],[(0,[z0,z1,z2,z3,z1305,z6]),(0,[z17,z0,z193,z2,z3,z160])],[(0,[z90,z65,z220,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1306]),(0,[z0,z1307,z1,z2,z3,z5]),(0,[z0,z1,z376,z3,z5,z8])],[(0,[z0,z1,z2,z3,z1308,z6]),(0,[z0,z1,z1309,z3,z5,z6]),(0,[z0,z133,z100,z3,z5,z228]),(0,[z1310,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z132,z500,z6]),(1,[z708,z2,z3,z5,z6]),(0,[z0,z1,z2,z751,z303,z5]),(0,[z7,z0,z1,z2,z435,z5]),(0,[z0,z1,z2,z3,z5,z1311])]],
   [[(0,[z0,z1,z2,z3,z1312,z6]),(0,[z0,z1,z2,z263,z5,z8]),(0,[z0,z133,z100,z3,z230,z6]),(0,[z0,z1,z2,z3,z5,z1313])],[(0,[z17,z0,z1,z2,z3,z35]),(0,[z0,z1,z2,z3,z5,z1314]),(0,[z0,z24,z620,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z419]),(0,[z0,z1,z2,z10,z3,z184])],[(0,[z90,z65,z2,z3,z5,z31]),(0,[z0,z1,z2,z1315,z3,z5]),(0,[z0,z209,z2,z3,z212,z6]),(0,[z812,z1,z2,z3,z5,z31])],[(0,[z0,z1,z2,z1316,z5,z6]),(0,[z0,z692,z23,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1317]),(0,[z0,z1,z2,z1092,z128,z5]),(0,[z0,z133,z100,z3,z5,z31]),(0,[z0,z1,z2,z3,z5,z1318])],[(0,[z0,z1,z2,z10,z265,z5]),(0,[z0,z1,z625,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z1319]),(0,[z0,z1,z435,z23,z3,z5]),(0,[z198,z0,z2,z3,z612,z5])],[(0,[z17,z0,z1,z2,z3,z500])],[(0,[z0,z1320,z2,z3,z5,z6]),(0,[z1214,z0,z1,z2,z5,z6]),(0,[z7,z0,z1,z100,z2,z5]),(0,[z0,z1,z2,z534,z3,z5])],[(0,[z0,z1,z2,z3,z1321,z6]),(0,[z129,z1,z2,z3,z187,z37]),(0,[z0,z1,z2,z288,z3,z316]),(0,[z0,z1,z404,z3,z5,z31])],[(0,[z90,z65,z2,z244,z5,z6]),(0,[z0,z1,z2,z3,z1322,z6]),(0,[z99,z461,z13,z3,z5,z6]),(1,[z1,z2,z720,z5,z6]),(0,[z0,z1,z2,z3,z50,z6]),(0,[z0,z256,z145,z1,z2,z6]),(0,[z0,z32,z2,z3,z5,z29]),(0,[z56,z1,z2,z3,z5,z82])],[(0,[z0,z1,z2,z1323,z3,z5]),(0,[z7,z0,z1,z2,z5,z46]),(0,[z38,z0,z1,z2,z26,z31])],[(0,[z0,z1,z2,z3,z5,z1324]),(0,[z0,z1,z2,z3,z5,z1325])],[(0,[z0,z61,z1,z3,z305,z6]),(0,[z0,z209,z2,z10,z3,z179]),(0,[z1326,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z872,z3,z8]),(0,[z38,z0,z1,z2,z370,z26]),(0,[z0,z1,z2,z3,z25,z749])],[(0,[z279,z1,z2,z3,z21,z31]),(0,[z1,z2,z3,z1327,z5,z6]),(0,[z0,z1,z415,z3,z5,z31])],[(0,[z17,z0,z138,z2,z3,z5]),(0,[z785,z0,z1,z2,z3,z5]),(0,[z171,z1,z2,z10,z15,z5]),(0,[z282,z1,z2,z48,z5,z6])],[(0,[z0,z1,z220,z3,z5,z325]),(0,[z0,z1,z2,z3,z5,z1328]),(0,[z909,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1329])],[(0,[z0,z256,z1,z2,z10,z3]),(0,[z0,z1,z310,z2,z3,z31]),(0,[z17,z0,z1,z310,z2,z3])]],
   [[(0,[z1330,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z287,z31])],[(0,[z0,z1,z3,z5,z1331,z6]),(0,[z0,z1,z2,z1147,z5,z6]),(0,[z0,z1,z2,z3,z316,z31])],[(0,[z0,z1,z2,z3,z5,z1332]),(0,[z0,z1333,z2,z3,z5,z6]),(0,[z0,z505,z2,z3,z160,z6]),(0,[z0,z1,z2,z3,z5,z1334]),(0,[z38,z7,z0,z1,z2,z5])],[(0,[z17,z0,z1,z2,z498,z5]),(0,[z0,z1,z2,z3,z5,z1335]),(0,[z38,z0,z1,z2,z450,z6]),(0,[z0,z277,z2,z3,z5,z29])],[(0,[z0,z1,z220,z3,z5,z1137]),(0,[z0,z1,z2,z3,z726,z6]),(0,[z0,z1,z2,z3,z558,z5]),(0,[z1336,z0,z1,z2,z3,z5])],[(0,[z75,z0,z2,z3,z5,z28]),(0,[z0,z1,z3,z780,z46,z6]),(0,[z0,z1,z2,z81,z3,z184])],[(0,[z17,z0,z1,z2,z955,z5]),(0,[z467,z0,z1,z3,z5,z31]),(1,[z0,z1,z3,z5,z968]),(0,[z0,z1,z2,z3,z5,z1337])],[(0,[z0,z1,z2,z5,z900,z8])],[],[(0,[z0,z1,z148,z3,z500,z6]),(0,[z0,z1,z2,z1338,z5,z6]),(0,[z0,z1,z2,z3,z1339,z6]),(0,[z609,z1,z2,z3,z22,z6]),(0,[z0,z394,z2,z3,z179,z6]),(0,[z0,z1,z2,z3,z5,z1340])],[(0,[z17,z0,z1,z2,z471,z5]),(0,[z0,z1341,z2,z3,z5,z6]),(0,[z0,z1,z3,z576,z5,z8]),(0,[z0,z1342,z2,z3,z5,z6]),(0,[z0,z358,z2,z3,z5,z117])],[(0,[z7,z78,z0,z1,z2,z5]),(0,[z0,z1,z2,z3,z1343,z6]),(0,[z0,z256,z1,z2,z15,z6]),(0,[z0,z256,z1,z2,z3,z6])],[(0,[z57,z1,z2,z48,z5,z31]),(0,[z0,z1,z2,z3,z907,z8]),(0,[z0,z1,z2,z261,z18,z8])],[(0,[z0,z1,z2,z1344,z5,z6]),(0,[z0,z1,z2,z3,z5,z1345])],[(0,[z0,z1,z2,z1346,z3,z5]),(1,[z0,z2,z3,z5,z915]),(0,[z0,z1,z2,z10,z235,z5])],[(0,[z0,z1,z2,z3,z64,z6]),(0,[z0,z1,z2,z1347,z5,z6]),(0,[z0,z1,z2,z1348,z5,z6]),(0,[z0,z1,z2,z3,z1259,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z1349]),(0,[z0,z1,z2,z3,z5,z1350]),(0,[z84,z1,z2,z3,z22,z6]),(0,[z1351,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z1161,z5,z6]),(0,[z1352,z7,z0,z1,z2,z5]),(0,[z0,z1,z2,z3,z927,z6])],[(0,[z0,z1,z2,z1353,z3,z5]),(0,[z0,z133,z100,z3,z287,z6]),(0,[z1354,z0,z1,z2,z3,z5])],[(0,[z501,z1,z72,z3,z5,z6]),(0,[z0,z1,z2,z1067,z3,z5])],[(0,[z90,z65,z2,z3,z5,z325]),(0,[z0,z1,z2,z3,z5,z1355]),(0,[z0,z1,z2,z293,z52,z5]),(0,[z1356,z7,z0,z1,z2,z5]),(0,[z0,z1,z2,z1357,z3,z5])],[(0,[z0,z1,z2,z81,z3,z182]),(0,[z0,z1,z882,z3,z5,z6])],[(0,[z78,z708,z2,z3,z5,z6]),(0,[z0,z1,z2,z265,z5,z144]),(0,[z17,z0,z1,z2,z263,z5]),(0,[z0,z1,z3,z5,z602,z8]),(0,[z17,z1221,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z598]),(0,[z0,z1,z2,z1358,z3,z5]),(0,[z0,z138,z2,z3,z12,z6])],[(0,[z90,z138,z2,z3,z5,z6]),(0,[z0,z1,z1359,z2,z3,z5]),(0,[z0,z1,z2,z116,z3,z8])],[(0,[z1360,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1361]),(0,[z0,z1,z2,z191,z3,z353])],[(0,[z0,z1,z2,z3,z5,z1362]),(0,[z0,z1,z2,z1363,z3,z5]),(0,[z0,z1,z2,z81,z3,z121]),(1,[z0,z1,z2,z3,z749])],[(0,[z0,z1364,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z116,z8])],[(0,[z0,z1,z2,z1365,z3,z5]),(0,[z57,z1,z2,z720,z5,z6]),(0,[z0,z380,z23,z3,z5,z6]),(0,[z0,z1,z2,z5,z1366,z6]),(0,[z0,z1,z2,z3,z5,z1367])],[(0,[z1,z72,z220,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1368]),(0,[z0,z138,z2,z10,z3,z5]),(0,[z0,z1,z2,z128,z5,z6]),(0,[z17,z0,z1,z2,z186,z5]),(0,[z0,z1,z2,z116,z3,z441])],[(0,[z0,z1,z2,z3,z5,z1369]),(0,[z0,z1,z2,z1370,z3,z6]),(0,[z17,z0,z43,z1,z2,z5]),(0,[z17,z0,z1,z2,z261,z18])],[(0,[z0,z1184,z2,z3,z5,z6]),(0,[z0,z1,z2,z173,z5,z6]),(0,[z0,z1,z2,z3,z1159,z5]),(0,[z0,z1,z627,z3,z5,z8]),(0,[z0,z1,z2,z3,z338,z58])],[(0,[z0,z1,z181,z3,z46,z433])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 497) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 497).take 500) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 997).take 410) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1407)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [497, 500, 410] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 120).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 120).take 127).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 247).take 123).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 370).take 126).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 496).take 16).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [120, 127, 123, 126, 16] = true :=
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

end PEqualNP.Outside.L_meta_38839

theorem PEqualNP.Outside.L_meta_38839 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4274056384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4274056384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38839.solve