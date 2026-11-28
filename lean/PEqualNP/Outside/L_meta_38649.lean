import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38649

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
  Nat.testBit (4276808362 * 2 ^ 32 + 4241025160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00084812711086ac#64 ++ 0xa00109024e2210d5#64 ++ 0x9818f8fff1118fff#64 ++ 0xd3031f1ffe2231ff#64 : BitVec 256),
   (0x0063234900673151#64 ++ 0x400c6469200ce62a#64 ++ 0xe8e7274901fff1ff#64 ++ 0xbd1ce4e9203ffe3f#64 : BitVec 256),
   (0x0b05c58e161a5a61#64 ++ 0x8160b8b1c2c34b4c#64 ++ 0xbf07c78e3e1e7e67#64 ++ 0x77e0f8f1c7c3cfcc#64 : BitVec 256),
   (0x15b806f02ba06d86#64 ++ 0x02b700de05740db0#64 ++ 0xfff807f03fe07f86#64 ++ 0xffff00fe07fc0ff0#64 : BitVec 256),
   (0x26def8003ddd8000#64 ++ 0x04dbdf0007bbb000#64 ++ 0xf7fff8003fff8005#64 ++ 0xfeffff0007fff000#64 : BitVec 256),
   (0x07f7b7ed80000000#64 ++ 0x00fef6fdb0000000#64 ++ 0xc7ffffffc0000003#64 ++ 0xf8fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.or, [6, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [12, 4]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x88002049011181ff 0x910004092022303f

def z1 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x9818f8fff1118fff 0xd3031f1ffe2231ff

def z2 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe8e7274901fff1ff 0xbd1ce4e9203ffe3f

def z3 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xc7ffffffc0000003 0xf8fffffff8000000

def z4 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf07e7cf3f1fffff 0xf7e0fcf9e7e3ffff

def z5 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff807f03fe07f86 0xffff00fe07fc0ff0

def z6 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7fff8003fff8005 0xfeffff0007fff000

def z7 : W := mkw 0x006b6b5b7177b7fd 0xe00d6d6b6e2ef6ff 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z8 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf07c78e3e1e7e67 0x77e0f8f1c7c3cfcc

def z9 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xc7ffff0000000001 0xf8ffffe000000000

def z10 : W := mkw 0x09004482161a5a61 0x8120089042c34b4c 0xbf0007803e1e7e66 0x77e000f007c3cfcc

def z11 : W := mkw 0x24da380029c58000 0x049b47000538b000 0x40f8380001e18000 0x881f0700003c3000

def z12 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xfffff8ffffff8fff 0xffffff1ffffff1ff

def z13 : W := mkw 0x0000000000000000 0x0000000000000000 0x8018f8ffc0000003 0xd0031f1ff8000000

def z14 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0x68e7070001fff1fc 0x2d1ce0e0003ffe3f

def z15 : W := mkw 0x26fffb5b7dffb7fd 0xe4dfff6b6fbff6ff 0xffffffffffffffff 0xffffffffffffffff

def z16 : W := mkw 0x0498000029800000 0x0093000005300000 0xf7f800003fe00004 0xfeff000007fc0000

def z17 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0xefffffffc1fff1ff 0xfdfffffff83ffe3f

def z18 : W := mkw 0x2246f800145d8000 0x0448df00028bb000 0x0007f800001f8001 0x0000ff000003f000

def z19 : W := mkw 0x37fefef03ffded86 0x06ffdfde07ffbdb0 0xfffffff03fffff87 0xfffffffe07fffff0

def z20 : W := mkw 0x26def8107ddd848c 0x24dbdf020fbbb091 0xf7fff871ffff819d 0xfeffff0e3ffff033

def z21 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1800000031118ffc 0x03000000062231ff

def z22 : W := mkw 0x0042200000450000 0x000844000008a000 0xe8e7204901ff81ff 0xbd1ce409203ff03f

def z23 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x9800204931118fff 0x93000409262231ff

def z24 : W := mkw 0x079494a480000000 0x00f2929490000000 0x0718d8b6c0000000 0x40e31b16d8000000

def z25 : W := mkw 0x224ef8003ddd8000 0x0449df0007bbb000 0x3007f8003fff8005 0x0600ff0007fff000

def z26 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe8ffffffc1fff1ff 0xfd1ffffff83ffe3f

def z27 : W := mkw 0x0008001021000484 0x0001000204200090 0x1800000031000f84 0x03000000062001f0

def z28 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0x60e7070000ee7000 0x2c1ce0e0001dce00

def z29 : W := mkw 0x0001010800000000 0x0000202100000000 0x8007070800000003 0x3000e0e100000000

def z30 : W := mkw 0x14b84a7279b0a7ae 0xa297094e4f3614f5 0xd8f8f8fff1f18fff 0xdb1f1f1ffe3e31ff

def z31 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0x67e700000eee0000 0x2cfce00001ddc000

def z32 : W := mkw 0x05b006e000202100 0x00b600dc00040420 0xeff807f001e07186 0xfdff00fe003c0e30

def z33 : W := mkw 0x08004002161a5a61 0x8100080042c34b4c 0x380000003e1e7e64 0x0700000007c3cfcc

def z34 : W := mkw 0x0ff7f7ef961a5a61 0x81fefefdf2c34b4c 0xfffffffffe1e7e67 0xffffffffffc3cfcc

def z35 : W := mkw 0x0a05c10e141a1261 0x8140b821c283424c 0x0007c00e001e0061 0x0000f801c003c00c

def z36 : W := mkw 0x2a47f90e145f9261 0x8548ff21c28bf24c 0x0007f80e001f8061 0x0000ff01c003f00c

def z37 : W := mkw 0x100800102b804c86 0x0201000205700990 0x100000003e000e00 0x0200000007c001c0

def z38 : W := mkw 0x15b806f02b804c86 0x02b700de05700990 0xd7f807f03e000e02 0xfaff00fe07c001c0

def z39 : W := mkw 0x06deb00029800000 0x00dbd60005300000 0xf7fff8003fe00005 0xfeffff0007fc0000

def z40 : W := mkw 0x0000480250108228 0xa00009004a021045 0x0000f80fc0118079 0x00001f01f802300f

def z41 : W := mkw 0x0b05cd8e561ada69 0xa160b9b1cac35b4d 0xbf07ff8ffe1ffe7f 0x77e0fff1ffc3ffcf

def z42 : W := mkw 0x224ef800355d8000 0x0449df0006abb000 0x901ff800311f8005 0xd203ff000623f000

def z43 : W := mkw 0x0901058e02025a61 0x812020b1c0404b4c 0xa807078e001e7e67 0x3500e0f1c003cfcc

def z44 : W := mkw 0x0490000000000000 0x0092000000000000 0xc7f8000000000000 0xf8ff000000000000

def z45 : W := mkw 0x0008001021000484 0x0001000204200090 0x981800f031000f86 0xd303001e062001f0

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x8818f8ffc11181ff 0xd1031f1ff822303f

def z47 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0x60e7274101eff198 0xac1ce4e8203dfe33

def z48 : W := mkw 0x0a05c10e141a1261 0x8140b821c283424c 0x9807c08e301e0e67 0x5300f811c603c1cc

def z49 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1818d8b6f1118ffc 0x43031b16de2231ff

def z50 : W := mkw 0x14b802702ba06d86 0x0297004e05740db0 0x78f800703fe07f84 0x8f1f000e07fc0ff0

def z51 : W := mkw 0x04f2326180000000 0x009e464c30000000 0x40f83871c0000000 0x881f070e38000000

def z52 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xfffff8493fff81ff 0xffffff0927fff03f

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0xb70000003e000004 0x76e0000007c00000

def z54 : W := mkw 0x05b006e000000000 0x00b600dc00000000 0xc7f8ffffc0000003 0xf8ff1ffff8000000

def z55 : W := mkw 0x15b84ef27bb0efae 0xa2b709de4f761df5 0xfff8fffffff1ffff 0xffff1ffffffe3fff

def z56 : W := mkw 0x27f7b7ed8ccd0000 0x04fef6fdb199a000 0xe7ffffffceee0003 0xfcfffffff9ddc000

def z57 : W := mkw 0x2246b000044d0000 0x0448d6000089a000 0x00070000000e0000 0x0000e0000001c000

def z58 : W := mkw 0x0020024000202100 0x0004004800040420 0xe8e0074001e07186 0xbd1c00e8003c0e30

def z59 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0x40e7204901ff81f9 0x881ce409203ff03f

def z60 : W := mkw 0x3ffffffe3fffffe7 0x87ffffffc7fffffc 0xfffffffe3fffffe7 0xffffffffc7fffffc

def z61 : W := mkw 0x24fb3b4929e7b151 0x449f6769253cf62a 0xe8ff3f4901fff1ff 0xbd1fe7e9203ffe3f

def z62 : W := mkw 0x0305858c00000000 0x0060b0b180000000 0x8707c78e00000003 0x70e0f8f1c0000000

def z63 : W := mkw 0x0008480031108000 0x0001090006221000 0x9018f80031118005 0xd2031f0006223000

def z64 : W := mkw 0x0001010800021041 0x0000202100004208 0xa8070708001e7067 0x3500e0e10003ce0c

def z65 : W := mkw 0x0100048002004800 0x0020009000400900 0xbf0007803e007e06 0x77e000f007c00fc0

def z66 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff8ffffffe07f87 0xffff1ffffffc0ff0

def z67 : W := mkw 0x05b006e000000000 0x00b600dc00000000 0xc7f807f000000002 0xf8ff00fe00000000

def z68 : W := mkw 0x0043210900471051 0x400864212008e20a 0x00072009001f8079 0x0000e4012003f00f

def z69 : W := mkw 0x159804b02b804c86 0x02b3009605700990 0x171800b03e000e00 0x42e3001607c001c0

def z70 : W := mkw 0x2fdffd9e7fdfdeed 0xa5fbffb3cffbfbdd 0xffffffffffffffff 0xffffffffffffffff

def z71 : W := mkw 0x04f2326180000000 0x009e464c30000000 0xc0f8f8ffc0000003 0xd81f1f1ff8000000

def z72 : W := mkw 0x0b05858c060a5841 0x0160b0b180c14b08 0x270707000e0e7000 0x24e0e0e001c1ce00

def z73 : W := mkw 0x15fb27f92be77dd7 0x42bf64ff257cefba 0xffff27f93fffffff 0xffffe4ff27ffffff

def z74 : W := mkw 0x200848003ddd8000 0x0401090007bbb000 0x300000003fff8004 0x0600000007fff000

def z75 : W := mkw 0x14b8027029a02586 0x0297004e053404b0 0x40f8007001e00180 0x881f000e003c0030

def z76 : W := mkw 0x1fbdc7fe3fba7fe7 0x83f7b8ffc7f74ffc 0xffffc7fe3ffe7fe7 0xfffff8ffc7ffcffc

def z77 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0x77f807b03ee07e00 0x6eff00f607dc0fc0

def z78 : W := mkw 0x05b84ef2711086ac 0xa0b709de4e2210d5 0xdff8fffff1118fff 0xfbff1ffffe2231ff

def z79 : W := mkw 0x0267e349147f3151 0x404cfc69228fe62a 0xffe7e7493ffff1ff 0xfffcfce927fffe3f

def z80 : W := mkw 0x0063234900000000 0x000c646920000000 0xc0e7274900000003 0xb81ce4e920000000

def z81 : W := mkw 0x012107ed80000000 0x002420fdb0000000 0x8018ffffc0000003 0xd0031ffff8000000

def z82 : W := mkw 0x0062224100652110 0x400c4448200ca422 0x40e0204101e18198 0x881c0408203c3033

def z83 : W := mkw 0x079595ac80000000 0x00f2b2b590000000 0x871fdfbec0000003 0x70e3fbf7d8000000

def z84 : W := mkw 0x05b107ed80000000 0x00b620fdb0000000 0xc7f807ffc0000002 0xf8ff00fff8000000

def z85 : W := mkw 0x006a2a516165a59c 0x600d454a2c2cb4b3 0x40f83871c1e18198 0x881f070e383c3033

def z86 : W := mkw 0x07f7b7ed80202100 0x00fef6fdb0040420 0xefffffffc1e07187 0xfdfffffff83c0e30

def z87 : W := mkw 0x0204800000000000 0x0040900000000000 0x8707c00000000001 0x70e0f80000000000

def z88 : W := mkw 0x2247f90d945d8000 0x0448ff21b28bb000 0x0007f80fc01f8001 0x0000ff01f803f000

def z89 : W := mkw 0x0000400210100220 0x8000080042020044 0x9800c08e30100e67 0x53001811c60201cc

def z90 : W := mkw 0x0b04c48616184a20 0x81609890c2c30944 0x1700c0863e000e00 0x42e01810c7c001c0

def z91 : W := mkw 0x06f7b34900000000 0x00def66920000000 0xc7ffff4900000003 0xf8ffffe920000000

def z92 : W := mkw 0x0063234900021041 0x000c646920004208 0xe8e72749001e7067 0xbd1ce4e92003ce0c

def z93 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff827f93ff1ffff 0xffff04ff27fe3fff

def z94 : W := mkw 0x100800102ba06d86 0x0201000205740db0 0x380000003fe07f84 0x0700000007fc0ff0

def z95 : W := mkw 0x0b25c7ef961a5a61 0x8164b8fdf2c34b4c 0xbf07c7fffe1e7e67 0x77e0f8ffffc3cfcc

def z96 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0xe7fff8000eee0001 0xfcffff0001ddc000

def z97 : W := mkw 0x17ffb7fdaba06d86 0x02fff6ffb5740db0 0xffff07f03fe07f86 0xffffe0fe07fc0ff0

def z98 : W := mkw 0x0020024000673151 0x40040048000ce62a 0xe8e0074001fff1fe 0xbd1c00e8003ffe3f

def z99 : W := mkw 0x0b67e7cf167f7b71 0xc16cfcf9e2cfef6e 0xffe7e7cf3fffffff 0xfffcfcf9e7ffffff

def z100 : W := mkw 0x0247b10d80471051 0x4048f621b008e20a 0x0007f80fc01f8079 0x0000ff01f803f00f

def z101 : W := mkw 0x2267fb49147fb151 0x444cff69228ff62a 0xe8e7ff4901fff1ff 0xbd1cffe9203ffe3f

def z102 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000f80fc0000001 0x00001f01f8000000

def z103 : W := mkw 0x0100048002004800 0x0020009000400900 0x270007000e007000 0x24e000e001c00e00

def z104 : W := mkw 0x0000480010108000 0x0000090002021000 0x0000f80000118001 0x00001f0000023000

def z105 : W := mkw 0x0246e000145d0000 0x0048dc00028ba000 0xf7e7e0003fff8005 0xfefcfc0007fff000

def z106 : W := mkw 0x06d6b00000000000 0x00dad60000000000 0xc7fff80000000001 0xf8ffff0000000000

def z107 : W := mkw 0x08084812771adeed 0xa10109024ee35bdd 0x380000003f1ffffc 0x0700000007e3ffff

def z108 : W := mkw 0x0b0dcd9e771adeed 0xa161b9b3cee35bdd 0xbf1fffffff1fffff 0xf7e3ffffffe3ffff

def z109 : W := mkw 0x0042200000450000 0x000844000008a000 0xe0e7200001ff8005 0xbc1ce400003ff000

def z110 : W := mkw 0x26def8103ddd8484 0x04dbdf0207bbb090 0xfffff8f03fff8f87 0xffffff1e07fff1f0

def z111 : W := mkw 0x17f7b7ed8aa06902 0x02fef6fdb1540d20 0xe7ffffffcee07003 0xfcfffffff9dc0e00

def z112 : W := mkw 0x010004a480000000 0x0020009490000000 0x000000b6c0000000 0x00000016d8000000

def z113 : W := mkw 0x07b597ed80000000 0x00f6b2fdb0000000 0x0718dfffc0000002 0x40e31bfff8000000

def z114 : W := mkw 0x0021034900223151 0x400420692004462a 0x08000749000071fa 0x010000e920000e3f

def z115 : W := mkw 0x269cd8003d988000 0x04d39b0007b31000 0x1718d8003e000000 0x42e31b0007c00000

def z116 : W := mkw 0x34fa3a7029e5a586 0x069f474e053cb4b0 0x40f8387001e18180 0x881f070e003c3030

def z117 : W := mkw 0x000808106100848c 0x200101020c201091 0x8018f8ffc101819b 0xd0031f1ff8203033

def z118 : W := mkw 0x1fbd87fc2faa7dc7 0x03f7b0ff85f54fb8 0xffff07f03fee7f86 0xffffe0fe07fdcff0

def z119 : W := mkw 0x24d2300008c50000 0x049a46000118a000 0x40e0000000e00000 0x081c0000001c0000

def z120 : W := mkw 0x2fdffd8e3fdfda61 0x85fbffb1c7fbfb4c 0xffffff8e3ffffe67 0xfffffff1c7ffffcc

def z121 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1018f8f7f1018f98 0xc2031f1efe2031f3

def z122 : W := mkw 0x0901458e161a5a61 0x812028b1c2c34b4c 0x3800078e3e1e7e66 0x070000f1c7c3cfcc

def z123 : W := mkw 0x0304848400000000 0x0060909080000000 0x0700c08600000000 0x40e01810c0000000

def z124 : W := mkw 0x079cdcb6f11086ac 0xa0f39b96de2210d5 0x1718d8b6f0000e00 0x42e31b16de0001c0

def z125 : W := mkw 0x0101058802025841 0x002020b100404b08 0xbf0707883e1e7e67 0x77e0e0f107c3cfcc

def z126 : W := mkw 0x0247b10d80000000 0x0048f621b0000000 0x0007f80fc0000001 0x0000ff01f8000000

def z127 : W := mkw 0x00000012400006ac 0xa0000002480000d5 0x080000ffc0000ffa 0x0100001ff80001ff

def z128 : W := mkw 0x27dffd8c3ddd8000 0x04fbffb187bbb000 0xf7ffff8e3fff8007 0xfefffff1c7fff000

def z129 : W := mkw 0x0021034900223151 0x400420692004462a 0x880027490111f1ff 0x910004e920223e3f

def z130 : W := mkw 0x0042200000673151 0x40084400000ce62a 0xe8e7200001fff1fd 0xbd1ce400003ffe3f

def z131 : W := mkw 0x032587ed80000000 0x0064b0fdb0000000 0x8707c7ffc0000003 0x70e0f8fff8000000

def z132 : W := mkw 0x0063235b406737fd 0xe00c646b680ce6ff 0xe8e727ffc1ffffff 0xbd1ce4fff83fffff

def z133 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0x67e7070000ee7000 0x2cfce0e0001dce00

def z134 : W := mkw 0x0b05c58e16184a20 0x8160b8b1c2c30944 0x9707c78e3e000e03 0x72e0f8f1c7c001c0

def z135 : W := mkw 0x0021034900223151 0x400420692004462a 0xe8e0074901e071fe 0xbd1c00e9203c0e3f

def z136 : W := mkw 0x0042200000450000 0x000844000008a000 0x40e0200001e18000 0x881c0400003c3000

def z137 : W := mkw 0x0008001021000484 0x0001000204200090 0x9818f8fff1000f87 0xd3031f1ffe2001f0

def z138 : W := mkw 0x27fffffffddd86ac 0xa4ffffffffbbb0d5 0xffffffffffff8fff 0xfffffffffffff1ff

def z139 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x9018f8b6f1118e05 0xd2031f16de2231c0

def z140 : W := mkw 0x016327c902677951 0x402c64f9204cef2a 0xffe727c93fffffff 0xfffce4f927ffffff

def z141 : W := mkw 0x17ffb7fdaba06d86 0x02fff6ffb5740db0 0xffffffffffe07f87 0xfffffffffffc0ff0

def z142 : W := mkw 0x0001010800673151 0x40002021000ce62a 0xa807070801fff1ff 0x3500e0e1003ffe3f

def z143 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xf7fff8b6ffff8e05 0xfeffff16dffff1c0

def z144 : W := mkw 0x0305c58e10100220 0x8060b8b1c2020044 0x9f07c78e30100e67 0x73e0f8f1c60201cc

def z145 : W := mkw 0x08084812771adeed 0xa10109024ee35bdd 0xb818f8ffff1fffff 0xd7031f1fffe3ffff

def z146 : W := mkw 0x012107ed80000000 0x002420fdb0000000 0x000007ffc0000002 0x000000fff8000000

def z147 : W := mkw 0x15b006e00aa06902 0x02b600dc01540d20 0x67e007000ee07000 0x2cfc00e001dc0e00

def z148 : W := mkw 0x249848003ddd8000 0x0493090007bbb000 0xf7f800003fff8004 0xfeff000007fff000

def z149 : W := mkw 0x0a47e10f145f1271 0xc148fc21e28be24e 0x0007e00f001f8079 0x0000fc01e003f00f

def z150 : W := mkw 0x0000480250108228 0xa00009004a021045 0x8800f84fc11181ff 0x91001f09f822303f

def z151 : W := mkw 0x17feb6f02ba06d86 0x02ffd6de05740db0 0xfffffff03fe07f87 0xfffffffe07fc0ff0

def z152 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0x3f0707003e1e7e64 0x27e0e0e007c3cfcc

def z153 : W := mkw 0x0901058c02025841 0x012020b180404b08 0x0000070000007000 0x000000e000000e00

def z154 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xc7ff07f000000002 0xf8ffe0fe00000000

def z155 : W := mkw 0x0b25c7cf163a7b71 0xc164b8f9e2c74f6e 0xbf07c7cf3e1e7fff 0x77e0f8f9e7c3cfff

def z156 : W := mkw 0x11284ef27330efae 0xa22509de4e661df5 0x9818fffff111ffff 0xd3031ffffe223fff

def z157 : W := mkw 0x0204c00014180000 0x0040980002830000 0xb707c0003e1e0005 0x76e0f80007c3c000

def z158 : W := mkw 0x0b05858c060a5841 0x0160b0b180c14b08 0xa707c78e0e0e7003 0x74e0f8f1c1c1ce00

def z159 : W := mkw 0x112006f002206d86 0x022400de00440db0 0xe8e007f001e07f86 0xbd1c00fe003c0ff0

def z160 : W := mkw 0x26def8027ddd8228 0xa4dbdf004fbbb045 0xf7fff80fffff807d 0xfeffff01fffff00f

def z161 : W := mkw 0x0000000000471051 0x400000000008e20a 0x00000000001f8078 0x000000000003f00f

def z162 : W := mkw 0x269490000c880000 0x04d2920001910000 0x070000000e000000 0x00e0000001c00000

def z163 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xcfffffffc11181ff 0xf9fffffff822303f

def z164 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0xefe7274901fff1ff 0xbdfce4e9203ffe3f

def z165 : W := mkw 0x15fb27f92ba06d86 0x02bf64ff25740db0 0xffff27f93fe07f87 0xffffe4ff27fc0ff0

def z166 : W := mkw 0x17bc96f4aba06d86 0x02f792de95740db0 0xfff8dff6ffe07f86 0xffff1bfedffc0ff0

def z167 : W := mkw 0x14b80a7069a0a58e 0x2297014e0d3414b1 0x40f83871c1e18198 0x881f070e383c3033

def z168 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000200900118079 0x000004012002300f

def z169 : W := mkw 0x04f2326180000000 0x009e464c30000000 0x40e0000000000000 0x081c000000000000

def z170 : W := mkw 0x0063234900202100 0x000c646920040420 0xe8e7274901e07187 0xbd1ce4e9203c0e30

def z171 : W := mkw 0x0020024000202100 0x0004004800040420 0x40e0004001e00180 0x881c0008003c0030

def z172 : W := mkw 0x05b006e002004800 0x00b600dc00400900 0xfff807f03e007e06 0xffff00fe07c00fc0

def z173 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0x0807c78e001e7e63 0x0100f8f1c003cfcc

def z174 : W := mkw 0x26deb0002dcd0000 0x04dbd60005b9a000 0xf7ff00003fee0004 0xfeffe00007fdc000

def z175 : W := mkw 0x07d6b4a480000000 0x00fad69490000000 0xc7fff8b6c0000001 0xf8ffff16d8000000

def z176 : W := mkw 0x112806f02ba06d86 0x022500de05740db0 0x380007f03fe07f86 0x070000fe07fc0ff0

def z177 : W := mkw 0x0000480250108228 0xa00009004a021045 0x0000d806c0000000 0x00001b00d8000000

def z178 : W := mkw 0x1008001029a02586 0x02010002053404b0 0x0000000001e00180 0x00000000003c0030

def z179 : W := mkw 0x2fd7b58c0ecf5841 0x05faf6b181d9eb08 0x67e707000eee7000 0x2cfce0e001ddce00

def z180 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0x171ff8003e1f8001 0x42e3ff0007c3f000

def z181 : W := mkw 0x012006e000000000 0x002400dc00000000 0x000007f000000002 0x000000fe00000000

def z182 : W := mkw 0x0b0ccc967718ceac 0xa1619992cee319d5 0x1718d8b6fe000e00 0x42e31b16dfc001c0

def z183 : W := mkw 0x07f7ffefd0108228 0xa0fefffdfa021045 0xc7ffffffc011807b 0xf8fffffff802300f

def z184 : W := mkw 0x079cdcb6f11086ac 0xa0f39b96de2210d5 0x9f18f8fff1118fff 0xd3e31f1ffe2231ff

def z185 : W := mkw 0x0000400010100000 0x0000080002020000 0x9000c00030100005 0x5200180006020000

def z186 : W := mkw 0x15b806f02be77dd7 0x42b700de057cefba 0xfff807f03ffffffe 0xffff00fe07ffffff

def z187 : W := mkw 0x0b0ccc967718ceac 0xa1619992cee319d5 0x9f18f8ffff118fff 0xd3e31f1fffe231ff

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z189 : W := mkw 0x0043210900471051 0x400864212008e20a 0x88072049011f81ff 0x9100e4092023f03f

def z190 : W := mkw 0x269cd8127d9886ac 0xa4d39b024fb310d5 0x1718d8b6fe000e00 0x42e31b16dfc001c0

def z191 : W := mkw 0x06d6b00000000000 0x00dad60000000000 0x47e7000000000000 0x28fce00000000000

def z192 : W := mkw 0x04984812799086ac 0xa09309024f3210d5 0xfff8f8fffff18fff 0xffff1f1ffffe31ff

def z193 : W := mkw 0x14b8027029a02586 0x0297004e053404b0 0xd8f800f031e00f86 0xdb1f001e063c01f0

def z194 : W := mkw 0x00080812610086ac 0xa00101024c2010d5 0x081838ffc1018ffa 0x8103071ff82031ff

def z195 : W := mkw 0x07fffffff11086ac 0xa0fffffffe2210d5 0xdffffffff1118fff 0xfbfffffffe2231ff

def z196 : W := mkw 0x26d6f8001cdd8000 0x04dadf00039bb000 0x67e7f8000eff8001 0x2cfcff0001dff000

def z197 : W := mkw 0x0b05858c060a5841 0x0160b0b180c14b08 0xbf0707803e0e7e06 0x77e0e0f007c1cfc0

def z198 : W := mkw 0x0062224100673151 0x400c4448200ce62a 0x68e0204101fff1fc 0x8d1c0408203ffe3f

def z199 : W := mkw 0x0f95d5ae961a5a61 0x81f2bab5d2c34b4c 0xbf1fdfbefe1e7e67 0x77e3fbf7dfc3cfcc

def z200 : W := mkw 0x0008001021000484 0x0001000204200090 0x981820f931118fff 0xd303041f262231ff

def z201 : W := mkw 0x00294b5b7132b7fd 0xe005296b6e2656ff 0x9818fffff111ffff 0xd3031ffffe223fff

def z202 : W := mkw 0x15b806e02ba06902 0x02b700dc05740d20 0xf7f807003fe07004 0xfeff00e007fc0e00

def z203 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x9818d8f6f1000f86 0xd3031b1ede2001f0

def z204 : W := mkw 0x27defc803fddc800 0x04fbdf9007fbb900 0xffffff803ffffe07 0xfffffff007ffffc0

def z205 : W := mkw 0x0ff7f7ef941a1261 0x81fefefdf283424c 0xc7ffffffc01e0063 0xf8fffffff803c00c

def z206 : W := mkw 0x1020027000202586 0x0204004e000404b0 0x0000007000000180 0x0000000e00000030

def z207 : W := mkw 0x279cdca4bd988000 0x04f39b9497b31000 0x1718d8b6fe000000 0x42e31b16dfc00000

def z208 : W := mkw 0x27ffbfeda9c58000 0x04fff7fdb538b000 0xc7ffffffc1e18003 0xf8fffffff83c3000

def z209 : W := mkw 0x37fffffdbffded86 0x06ffffffb7ffbdb0 0xffffffffffffff87 0xfffffffffffffff0

def z210 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0xe7ffffffc0ee7003 0xfcfffffff81dce00

def z211 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0x77e700003fff8004 0x2efce00007fff000

def z212 : W := mkw 0x020cc80035188000 0x0041990006a31000 0xb71ff8003f1f8005 0xf6e3ff0007e3f000

def z213 : W := mkw 0x07ffffedb1108000 0x00fffffdb6221000 0xd7fffffff1118007 0xfafffffffe223000

def z214 : W := mkw 0x0000400014180000 0x0000080002830000 0x300000003e1e0004 0x0600000007c3c000

def z215 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1000000030000e00 0x02000000060001c0

def z216 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1018d8b6f0000e00 0x42031b16de0001c0

def z217 : W := mkw 0x0204c00014180000 0x0040980002830000 0x1700c0003e000000 0x42e0180007c00000

def z218 : W := mkw 0x1f9dc5be3f9a5ee7 0x83f3b8b7c7f34bdc 0xbf1fc7be3e1e7e67 0x77e3f8f7c7c3cfcc

def z219 : W := mkw 0x0008001021000484 0x0001000204200090 0x101800b030000e00 0x42030016060001c0

def z220 : W := mkw 0x15b006e00aa06902 0x02b600dc01540d20 0xe7f807f00ee07002 0xfcff00fe01dc0e00

def z221 : W := mkw 0x0f9dc58e3f9a5a61 0x81f3b8b1c7f34b4c 0xffffc78e3ffe7e67 0xfffff8f1c7ffcfcc

def z222 : W := mkw 0x000808106100848c 0x200101020c201091 0x00183871c1018198 0x8003070e38203033

def z223 : W := mkw 0x26d6f0001cdd0000 0x04dade00039ba000 0xf7e7c0003efe0005 0x7efcf80007dfc000

def z224 : W := mkw 0x100800102be77dd7 0x42010002057cefba 0x380000003ffffffc 0x0700000007ffffff

def z225 : W := mkw 0x059804802b804800 0x00b3009005700900 0xfff807803fe07e06 0xffff00f007fc0fc0

def z226 : W := mkw 0x07f7b7ed80652110 0x40fef6fdb00ca422 0xc7ffffffc1e1819b 0xf8fffffff83c3033

def z227 : W := mkw 0x0000000002004800 0x0000000000400900 0x380000003e007e04 0x0700000007c00fc0

def z228 : W := mkw 0x07f7f7ef90100220 0x80fefefdf2020044 0xdffffffff0100e67 0xfbfffffffe0201cc

def z229 : W := mkw 0x05f327e900000000 0x00be64fd20000000 0xc7ff27f900000003 0xf8ffe4ff20000000

def z230 : W := mkw 0x0267b34d80000000 0x004cf669b0000000 0xc0e7ff4fc0000003 0xb81cffe9f8000000

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000049000001fa 0x010000092000003f

def z232 : W := mkw 0x0b47e58e165f5a61 0x8168fcb1c2cbeb4c 0xffe7e78e3ffffe67 0xfffcfcf1c7ffffcc

def z233 : W := mkw 0x0063234900471051 0x400c64692008e20a 0xc0e72749001f807b 0xb81ce4e92003f00f

def z234 : W := mkw 0x27f7b7ed8ccd0000 0x04fef6fdb199a000 0x67e707000eee0000 0x2cfce0e001ddc000

def z235 : W := mkw 0x05b806e029800000 0x00b700dc05300000 0xf7f807f03fe00006 0xfeff00fe07fc0000

def z236 : W := mkw 0x26def8023ddd8220 0x84dbdf0047bbb044 0xfffff88e3fff8e67 0xffffff11c7fff1cc

def z237 : W := mkw 0x2246f802545d8228 0xa448df004a8bb045 0x0007f80fc01f8079 0x0000ff01f803f00f

def z238 : W := mkw 0x26def8003d988000 0x04dbdf0007b31000 0xd7fff8003e000001 0xfaffff0007c00000

def z239 : W := mkw 0x15b806f26ba06fae 0xa2b700de4d740df5 0xfff807ffffe07ffe 0xffff00fffffc0fff

def z240 : W := mkw 0x0000000000202100 0x0000000000040420 0x2800000001e07184 0x05000000003c0e30

def z241 : W := mkw 0x0000480250108228 0xa00009004a021045 0x0000000000118078 0x000000000002300f

def z242 : W := mkw 0x100848127bb0efae 0xa20109024f761df5 0x380000003ff1fffc 0x0700000007fe3fff

def z243 : W := mkw 0x0304c48016184800 0x0060989002c30900 0xbf07c7803e1e7e07 0x77e0f8f007c3cfc0

def z244 : W := mkw 0x06d6b00000000000 0x00dad60000000000 0xc7fff8ffc0000003 0xf8ffff1ff8000000

def z245 : W := mkw 0x0305858c02004800 0x0060b0b180400900 0xbf07c78e3e007e07 0x77e0f8f1c7c00fc0

def z246 : W := mkw 0x0000000000673151 0x40000000000ce62a 0x2800000001fff1fc 0x05000000003ffe3f

def z247 : W := mkw 0x0100448212104a20 0x8020089042420944 0xbf00c78e3e107e67 0x77e018f1c7c20fcc

def z248 : W := mkw 0x0901058e02025a61 0x812020b1c0404b4c 0x0800078e00007e62 0x010000f1c0000fcc

def z249 : W := mkw 0x112006f002206d86 0x022400de00440db0 0x080007f000007f82 0x010000fe00000ff0

def z250 : W := mkw 0x0fb5c7ee161a5a61 0x81f6b8fdc2c34b4c 0xffffc7fe3e1e7e67 0xfffff8ffc7c3cfcc

def z251 : W := mkw 0x15fb27f92be77dd7 0x42bf64ff257cefba 0xffff07f03fee7f86 0xffffe0fe07fdcff0

def z252 : W := mkw 0x006b6b5b7177b7fd 0xe00d6d6b6e2ef6ff 0xf8e7274931ffffff 0xbf1ce4e9263fffff

def z253 : W := mkw 0x0b04c48616184a20 0x81609890c2c30944 0xbf00c7863e007e06 0x77e018f0c7c00fc0

def z254 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0x47ffdfb6c0000000 0x68fffbf6d8000000

def z255 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018d8b6c0000000 0x40031b16d8000000

def z256 : W := mkw 0x0a05810c040a1041 0x0140b02180814208 0x00070000000e0000 0x0000e0000001c000

def z257 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800000800100067 0x110000010002000c

def z258 : W := mkw 0x07f7b7ed80021041 0x00fef6fdb0004208 0xefffffffc01e7067 0xfdfffffff803ce0c

def z259 : W := mkw 0x14fa227129e52596 0x429f444e253ca4b2 0x40f8207101e18198 0x881f040e203c3033

def z260 : W := mkw 0x004b691b715796fd 0xe0096d236e2af2df 0x981ff8fff11f8fff 0xd303ff1ffe23f1ff

def z261 : W := mkw 0x27f7ffed945d8000 0x04fefffdb28bb000 0xc7ffffffc01f8003 0xf8fffffff803f000

def z262 : W := mkw 0x0000400210100220 0x8000080042020044 0x1800000030100e64 0x03000000060201cc

def z263 : W := mkw 0x0108049023004c84 0x0021009204600990 0xbf1807f03f007f86 0xf7e300fe07e00ff0

def z264 : W := mkw 0x26f7b3490cef3151 0x44def669219de62a 0xefe727490ffff1ff 0xbdfce4e921fffe3f

def z265 : W := mkw 0x0498000029800000 0x0093000005300000 0x40f8000001e00000 0x881f0000003c0000

def z266 : W := mkw 0x192107fe02227fe7 0x832420ffc0444ffc 0x080007fe00007fe2 0x010000ffc0000ffc

def z267 : W := mkw 0x0000000000223151 0x400000000004462a 0x08000000000071f8 0x0100000000000e3f

def z268 : W := mkw 0x112006e002206902 0x022400dc00440d20 0x0000070000007000 0x000000e000000e00

def z269 : W := mkw 0x2008080029c58000 0x040101000538b000 0x0000000001e18000 0x00000000003c3000

def z270 : W := mkw 0x27fefee03ddd8000 0x04ffdfdc07bbb000 0xf7fffff03fff8007 0xfefffffe07fff000

def z271 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x981800f031118ffe 0xd303001e062231ff

def z272 : W := mkw 0x00080012610006ac 0xa00100024c2000d5 0x981800fff1000ffe 0xd303001ffe2001ff

def z273 : W := mkw 0x15f327e90ae77953 0x42be64fd215cef2a 0xefe727490ffff1ff 0xbdfce4e921fffe3f

def z274 : W := mkw 0x0100048002004800 0x0020009000400900 0x170000803e000e00 0x42e0001007c001c0

def z275 : W := mkw 0x030dcd9e711086ac 0xa061b9b3ce2210d5 0x9f1ffffff1118fff 0xf3e3fffffe2231ff

def z276 : W := mkw 0x000848127177b7fd 0xe00109024e2ef6ff 0xb818f8fff1ffffff 0xd7031f1ffe3fffff

def z277 : W := mkw 0x06f7b36d80000000 0x00def66db0000000 0x40fff87fc0000001 0x881fff0ff8000000

def z278 : W := mkw 0x27ffffedbddd8000 0x04fffffdb7bbb000 0xf7ffffffffff8007 0xfefffffffffff000

def z279 : W := mkw 0x0021035b402237fd 0xe004206b680446ff 0x080007ffc0007ffa 0x010000fff8000fff

def z280 : W := mkw 0x26fffb493dffb151 0x44dfff6927bff62a 0xffffff493ffff1ff 0xffffffe927fffe3f

def z281 : W := mkw 0x106b23592be77dd7 0x420d646b257cefba 0xf8e727493fffffff 0xbf1ce4e927ffffff

def z282 : W := mkw 0x300848103ffded86 0x0601090207ffbdb0 0x380000003fffff84 0x0700000007fffff0

def z283 : W := mkw 0x0000000000652110 0x40000000000ca422 0x0000000001e18198 0x00000000003c3033

def z284 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0x7fe007003fe07f84 0x2ffc00e007fc0ff0

def z285 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf1ffffffe1e7e67 0xf7e3ffffffc3cfcc

def z286 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0x47e7070000000000 0x28fce0e000000000

def z287 : W := mkw 0x204a68003ddd8000 0x04094d0007bbb000 0xf0e720003fff8005 0xbe1ce40007fff000

def z288 : W := mkw 0x0042200100450010 0x400844002008a002 0x0000200100018018 0x0000040020003003

def z289 : W := mkw 0x15b006e00aa06902 0x02b600dc01540d20 0xefe007400fe07186 0xbdfc00e801fc0e30

def z290 : W := mkw 0x0a05c90e541a9269 0xa140b921ca83524d 0x0007f80fc01f8079 0x0000ff01f803f00f

def z291 : W := mkw 0x112806f023206d86 0x022500de04640db0 0x981807f031007f86 0xd30300fe06200ff0

def z292 : W := mkw 0x27defca4bddd8000 0x04fbdf9497bbb000 0xf7fff8b6ffff8005 0xfeffff16dffff000

def z293 : W := mkw 0x26fefa413dfda110 0x44dfdf4827bfb422 0xf7fff8413fff819d 0xfeffff0827fff033

def z294 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x9800c08e31118fff 0x53001811c62231ff

def z295 : W := mkw 0x1ffff7ffbfba7fe7 0x83fffefff7f74ffc 0xfffffffffffe7fe7 0xffffffffffffcffc

def z296 : W := mkw 0x26fffb493ddd8000 0x04dfff6927bbb000 0xf7ffff493fff8007 0xfeffffe927fff000

def z297 : W := mkw 0x0b04c48616184a20 0x81609890c2c30944 0xb707c0863e1e0e05 0x76e0f810c7c3c1c0

def z298 : W := mkw 0x2fffffefbfdfda61 0x85fffffdf7fbfb4c 0xfffffffffffffe67 0xffffffffffffffcc

def z299 : W := mkw 0x220cc8003ddd8000 0x0441990007bbb000 0xb707c0003fff8005 0x76e0f80007fff000

def z300 : W := mkw 0x0062224100000000 0x000c444820000000 0x40e0204100000000 0x881c040820000000

def z301 : W := mkw 0x0063234900652110 0x400c6469200ca422 0xc0e7274901e1819b 0xb81ce4e9203c3033

def z302 : W := mkw 0x0062224100652110 0x400c4448200ca422 0xe8e0274101e1f19e 0xbd1c04e8203c3e33

def z303 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000204900000003 0x9000040920000000

def z304 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0x77ffd8003eee0000 0x6efffb0007ddc000

def z305 : W := mkw 0x0008480031108000 0x0001090006221000 0x1000000031118004 0x0200000006223000

def z306 : W := mkw 0x200848127ddd86ac 0xa40109024fbbb0d5 0x380000003fff8ffc 0x0700000007fff1ff

def z307 : W := mkw 0x17f7b7ed8aa06902 0x02fef6fdb1540d20 0x67e707000ee07000 0x2cfce0e001dc0e00

def z308 : W := mkw 0x0800400216184a20 0x8100080042c30944 0x100000003e000e00 0x0200000007c001c0

def z309 : W := mkw 0x112107f902227dd7 0x422420ff20444fba 0x080007f900007ffa 0x010000ff20000fff

def z310 : W := mkw 0x17f7b7fd82206d86 0x02fef6ffb0440db0 0xcfffffffc0007f83 0xf9fffffff8000ff0

def z311 : W := mkw 0x0347b58d80000000 0x0068f6b1b0000000 0x8707ff8fc0000003 0x70e0fff1f8000000

def z312 : W := mkw 0x0063234900000000 0x000c646920000000 0xc0ffffffc0000003 0xf81ffffff8000000

def z313 : W := mkw 0x00636b4b5077b379 0xe00c6d696a0ef66f 0xe8e7ff4fc1fff1ff 0xbd1cffe9f83ffe3f

def z314 : W := mkw 0x110004b002004c86 0x0220009600400990 0x000000b000000e00 0x00000016000001c0

def z315 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1818d8fff0000ffa 0x43031b1ffe0001ff

def z316 : W := mkw 0x200848003ddd8000 0x0401090007bbb000 0xb018f8003fff8005 0xd6031f0007fff000

def z317 : W := mkw 0x17ffb7fda9a02586 0x02fff6ffb53404b0 0xc7ffffffc1e00183 0xf8fffffff83c0030

def z318 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0x3707c7863e0e7e00 0x66e0f8f0c7c1cfc0

def z319 : W := mkw 0x0020024100202110 0x4004004820040422 0x0000004100000198 0x0000000820000033

def z320 : W := mkw 0x0020024000000000 0x0004004800000000 0xc0e0074000000002 0xb81c00e800000000

def z321 : W := mkw 0x006b2359216735d5 0x400d646b242ce6ba 0xf8ff27f931ffffff 0xff1fe4ff263fffff

def z322 : W := mkw 0x1fb587ec0eaa7943 0x03f6b0fd81d54f28 0x67e707000eee7000 0x2cfce0e001ddce00

def z323 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0x67f807700fe07180 0xacff00ee01fc0e30

def z324 : W := mkw 0x37defcb03fddcc86 0x06fbdf9607fbb990 0xf7fff8b03fff8e05 0xfeffff1607fff1c0

def z325 : W := mkw 0x0042300180000000 0x0008460030000000 0x00003801c0000000 0x0000070038000000

def z326 : W := mkw 0x0a05c10e141a1261 0x8140b821c283424c 0xb707c00e3e1e0065 0x76e0f801c7c3c00c

def z327 : W := mkw 0x0000000000000000 0x0000000000000000 0x801800f000000002 0xd003001e00000000

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000000011181fc 0x010000000022303f

def z329 : W := mkw 0x0008000029800000 0x0001000005300000 0x300000003fe00004 0x0600000007fc0000

def z330 : W := mkw 0x0ff7b7ef82025a61 0x81fef6fdf0404b4c 0xcfffffffc0007e63 0xf9fffffff8000fcc

def z331 : W := mkw 0x200000000ccd0000 0x040000000199a000 0x200000000eee0000 0x0400000001ddc000

def z332 : W := mkw 0x24da780039d58000 0x049b4f00073ab000 0xd0f8f80031f18005 0xda1f1f00063e3000

def z333 : W := mkw 0x15fa26f02be56d86 0x02bf44de057cadb0 0xffff27f03fffff87 0xffffe4fe07fffff0

def z334 : W := mkw 0x07fffffff177b7fd 0xe0fffffffe2ef6ff 0xfffffffff1ffffff 0xfffffffffe3fffff

def z335 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x9818d8bef0100e67 0x53031b17de0201cc

def z336 : W := mkw 0x04da200029c50000 0x009b44000538a000 0xf7ff20003fff8005 0xfeffe40007fff000

def z337 : W := mkw 0x15b84ef27bb0efae 0xa2b709de4f761df5 0xfff807f03ff1fffe 0xffff00fe07fe3fff

def z338 : W := mkw 0x0a67e34f147f3371 0xc14cfc69e28fe66e 0xe8e7e74f01fff1ff 0xbd1cfce9e03ffe3f

def z339 : W := mkw 0x15f327e90ae77953 0x42be64fd215cef2a 0x67e707000eee7000 0x2cfce0e001ddce00

def z340 : W := mkw 0x0ffffffff71adeed 0xa1fffffffee35bdd 0xffffffffff1fffff 0xffffffffffe3ffff

def z341 : W := mkw 0x37bcdef03fb8ed86 0x06f79bde07f71db0 0xfff8dff03fe07f86 0xffff1bfe07fc0ff0

def z342 : W := mkw 0x0204800004080000 0x0040900000810000 0x270700000e0e0000 0x24e0e00001c1c000

def z343 : W := mkw 0x0001010800021041 0x0000202100004208 0x00070008001e0061 0x0000e0010003c00c

def z344 : W := mkw 0x006a6a537175a7bc 0xe00d4d4a6e2eb4f7 0xd8f8f8fff1f18fff 0xdb1f1f1ffe3e31ff

def z345 : W := mkw 0x0008480231108220 0x8001090046221044 0x9818f88e31118e67 0xd3031f11c62231cc

def z346 : W := mkw 0x15b80ef06ba0ed8e 0x22b701de0d741db1 0xfff83ff1ffe1ff9e 0xffff07fe3ffc3ff3

def z347 : W := mkw 0x07f7b7ed80450000 0x00fef6fdb008a000 0xe7ffffffc1ff8007 0xfcfffffff83ff000

def z348 : W := mkw 0x0490000008800000 0x0092000001100000 0x67e000000ee00000 0x2cfc000001dc0000

def z349 : W := mkw 0x0000000240000228 0xa000000048000045 0x0000000fc0000078 0x00000001f800000f

def z350 : W := mkw 0x0042200000000000 0x0008440000000000 0xc0e7200000000001 0xb81ce40000000000

def z351 : W := mkw 0x06d6b00000450000 0x00dad6000008a000 0xe7fff80001ff8005 0xfcffff00003ff000

def z352 : W := mkw 0x0b67a7cd066f7951 0x416cf4f9a0cdef2a 0x67e707000eee7000 0x2cfce0e001ddce00

def z353 : W := mkw 0x0b67e7cf167f7b71 0xc16cfcf9e2cfef6e 0xffe7c78e3efe7e67 0x7ffcf8f1c7dfcfcc

def z354 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xfffff8003fff8ffd 0xffffff0007fff1ff

def z355 : W := mkw 0x04f2326180652110 0x409e464c300ca422 0x40f83871c1e18198 0x881f070e383c3033

def z356 : W := mkw 0x112107fd82206d86 0x022420ffb0440db0 0x080007ffc0007f82 0x010000fff8000ff0

def z357 : W := mkw 0x016327ed80000000 0x002c64fdb0000000 0xc0e727ffc0000003 0xb81ce4fff8000000

def z358 : W := mkw 0x09094d9e7312deed 0xa12129b3ce625bdd 0x9818fffff111ffff 0xd3031ffffe223fff

def z359 : W := mkw 0x0063234900450000 0x000c64692008a000 0xe0e7274901ff8007 0xbc1ce4e9203ff000

def z360 : W := mkw 0x05f236e180000000 0x00be46dc30000000 0xc7f83ff1c0000002 0xf8ff07fe38000000

def z361 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7fff8ffffff8007 0xfeffff1ffffff000

def z362 : W := mkw 0x04f3336980673151 0x409e666d300ce62a 0xe8ff3f79c1fff1ff 0xbd1fe7ef383ffe3f

def z363 : W := mkw 0x280848023fdfda61 0x8501090047fbfb4c 0x380000003ffffe64 0x0700000007ffffcc

def z364 : W := mkw 0x0009491a711296ed 0xa00129234e2252dd 0xb81ffffff11fffff 0xf703fffffe23ffff

def z365 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1018f8bff0118e79 0x42031f17fe0231cf

def z366 : W := mkw 0x06d6f00014180000 0x00dade0002830000 0xf7fff8003e1e0005 0xfeffff0007c3c000

def z367 : W := mkw 0x1000001002206d86 0x0200000200440db0 0x0800000000007f80 0x0100000000000ff0

def z368 : W := mkw 0x0ff7b7ed860a5841 0x01fef6fdb0c14b08 0xe7ffffffce0e7003 0xfcfffffff9c1ce00

def z369 : W := mkw 0x0247b10d80000000 0x0048f621b0000000 0x801ff8ffc0000003 0xd003ff1ff8000000

def z370 : W := mkw 0x06f7b34900673151 0x40def669200ce62a 0xefffff4901fff1ff 0xfdffffe9203ffe3f

def z371 : W := mkw 0x102802502ba06d86 0x0205004a05740db0 0xf8e007403fe07f86 0xbf1c00e807fc0ff0

def z372 : W := mkw 0x0800000202025a61 0x8100000040404b4c 0x0800000000007e60 0x0100000000000fcc

def z373 : W := mkw 0x15b907f82ba27dc7 0x02b720ff05744fb8 0xffff07f83ffe7fe7 0xffffe0ff07ffcffc

def z374 : W := mkw 0x2f9cdc863f98ca20 0x85f39b90c7f31944 0x1718d8863e000e00 0x42e31b10c7c001c0

def z375 : W := mkw 0x0001010800021041 0x0000202100004208 0x0800070800007062 0x010000e100000e0c

def z376 : W := mkw 0x0008480031108000 0x0001090006221000 0x9018f8fff1118007 0xd2031f1ffe223000

def z377 : W := mkw 0x000848107110848c 0x200109020e221091 0x9018f871f111819d 0xd2031f0e3e223033

def z378 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x9018f8fff0000e03 0xd2031f1ffe0001c0

def z379 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe8e7070800fe7067 0x3d1ce0e1001fce0c

def z380 : W := mkw 0x0000000000673151 0x40000000000ce62a 0xa800204901fff1ff 0x95000409203ffe3f

def z381 : W := mkw 0x24da380029c58000 0x049b47000538b000 0xf7f838003fe18004 0xfeff070007fc3000

def z382 : W := mkw 0x0498001029800484 0x0093000205300090 0xfff800f03fe00f86 0xffff001e07fc01f0

def z383 : W := mkw 0x04fa3a71e100848c 0x209f474e3c201091 0x40f83871c1018198 0x881f070e38203033

def z384 : W := mkw 0x0028025021202584 0x0005004a042404b0 0xf8f807f031e07f86 0xff1f00fe063c0ff0

def z385 : W := mkw 0x15b006e00aa06902 0x02b600dc01540d20 0xffe007803ee07e06 0x7ffc00f007dc0fc0

def z386 : W := mkw 0x1b25c7fe163a7fe7 0x8364b8ffc2c74ffc 0xbf07c7fe3e1e7fe7 0x77e0f8ffc7c3cffc

def z387 : W := mkw 0x012107ed80000000 0x002420fdb0000000 0x0000070000000000 0x000000e000000000

def z388 : W := mkw 0x2fd7f58e1edf5a61 0x85fafeb1c3dbeb4c 0xffe7c78e3efe7e67 0x7ffcf8f1c7dfcfcc

def z389 : W := mkw 0x07b587ec00000000 0x00f6b0fd80000000 0xc7ffc7fe00000003 0xf8fff8ffc0000000

def z390 : W := mkw 0x04fb234929e73151 0x409f6469253ce62a 0xffff27493ffff1ff 0xffffe4e927fffe3f

def z391 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x180000fff1118ffe 0x0300001ffe2231ff

def z392 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0xe7e720000fff8005 0xbcfce40001fff000

def z393 : W := mkw 0x000848127177b7fd 0xe00109024e2ef6ff 0x3800000031fffffc 0x07000000063fffff

def z394 : W := mkw 0x0b0dcd9e771adeed 0xa161b9b3cee35bdd 0xbf1fdfbefe1e7e67 0x77e3fbf7dfc3cfcc

def z395 : W := mkw 0x0000000000673151 0x40000000000ce62a 0x2000000000ee7000 0x04000000001dce00

def z396 : W := mkw 0x100000000aa06902 0x0200000001540d20 0x200000000ee07000 0x0400000001dc0e00

def z397 : W := mkw 0x1fbcc6f63fb86fa6 0x83f798dec7f70df4 0xfff8c7f63fe07f86 0xffff18fec7fc0ff0

def z398 : W := mkw 0x0b25c7ce163a7b61 0x8164b8f9c2c74f6c 0xffe7c7ce3ffe7fe7 0xfffcf8f9c7ffcffc

def z399 : W := mkw 0x0a47f10f941a1261 0x8148fe21f283424c 0x0007f80fc01e0061 0x0000ff01f803c00c

def z400 : W := mkw 0x200848003d988000 0x0401090007b31000 0x100000003e000000 0x0200000007c00000

def z401 : W := mkw 0x2204d80014188000 0x04409b0002831000 0x0000d80000000000 0x00001b0000000000

def z402 : W := mkw 0x0062224100652110 0x400c4448200ca422 0xc8e0204901f181ff 0x991c0409203e303f

def z403 : W := mkw 0x26deb8002dcd8000 0x04dbd70005b9b000 0x67ff38000fef8000 0xacffe70001fdf000

def z404 : W := mkw 0x0020024000202100 0x0004004800040420 0xe8e0274901f1f1ff 0xbd1c04e9203e3e3f

def z405 : W := mkw 0x000808106100848c 0x200101020c201091 0x0000000001018198 0x0000000000203033

def z406 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0x2707c70e0e1e7061 0x24e0f8e1c1c3ce0c

def z407 : W := mkw 0x07b496e480000000 0x00f692dc90000000 0xc7f8dff6c0000002 0xf8ff1bfed8000000

def z408 : W := mkw 0x0000000000000000 0x0000000000000000 0x9800008030000e06 0x53000010060001c0

def z409 : W := mkw 0x07d7b5ad80000000 0x00faf6b5b0000000 0x071ff8bfc0000001 0x40e3ff17f8000000

def z410 : W := mkw 0x112006f242206fae 0xa22400de48440df5 0x080007ffc0007ffa 0x010000fff8000fff

def z411 : W := mkw 0x1fffe7ff3fff7ff7 0xc3fffcffe7ffeffe 0xffffe7ff3fffffff 0xfffffcffe7ffffff

def z412 : W := mkw 0x0b05c58c161a5841 0x0160b8b182c34b08 0xb707c7003e1e7005 0x76e0f8e007c3ce00

def z413 : W := mkw 0x079494a480000000 0x00f2929490000000 0x8718f8ffc0000003 0xd0e31f1ff8000000

def z414 : W := mkw 0x00000012400006ac 0xa0000002480000d5 0x0800000000000ff8 0x01000000000001ff

def z415 : W := mkw 0x2247f909145f9051 0x4448ff21228bf20a 0x0007f809001f8079 0x0000ff012003f00f

def z416 : W := mkw 0x0a0dc91e751a96ed 0xa141b923cea352dd 0x981ff8fff11f8fff 0xd303ff1ffe23f1ff

def z417 : W := mkw 0x37fefef27ffdefae 0xa6ffdfde4fffbdf5 0xffffffffffffffff 0xffffffffffffffff

def z418 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0x47e7ff0fc0000001 0x28fcffe1f8000000

def z419 : W := mkw 0x0ff7f7ef967f7b71 0xc1fefefdf2cfef6e 0xffffffffffffffff 0xffffffffffffffff

def z420 : W := mkw 0x15b806f029a02586 0x02b700de053404b0 0xc7f807f001e00182 0xf8ff00fe003c0030

def z421 : W := mkw 0x0100048000000000 0x0020009000000000 0x8700078000000002 0x70e000f000000000

def z422 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0x08072749001ff1fb 0x0100e4e92003fe3f

def z423 : W := mkw 0x07f6b6e580000000 0x00fed6dcb0000000 0x47f8f8f7c0000000 0xc8ff1f1ef8000000

def z424 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x9818f80031118ffd 0xd3031f00062231ff

def z425 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0x68e7074900ee71fa 0x2d1ce0e9201dce3f

def z426 : W := mkw 0x000808106100848c 0x200101020c201091 0x88183879c11181ff 0x9103070f3822303f

def z427 : W := mkw 0x26deb80029c58000 0x04dbd7000538b000 0xc7fff80001e18001 0xf8ffff00003c3000

def z428 : W := mkw 0x0305858c00000000 0x0060b0b180000000 0x871fffffc0000003 0xf0e3fffff8000000

def z429 : W := mkw 0x0247b10d80000000 0x0048f621b0000000 0x0007000000000000 0x0000e00000000000

def z430 : W := mkw 0x27ffffedbdffb151 0x44fffffdb7bff62a 0xfffffffffffff1ff 0xfffffffffffffe3f

def z431 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x18183871f1118ffc 0x8303070e3e2231ff

def z432 : W := mkw 0x37feb6f02fed6d86 0x06ffd6de05fdadb0 0xffff07f03fee7f86 0xffffe0fe07fdcff0

def z433 : W := mkw 0x0043210900471051 0x400864212008e20a 0xe0e7200901ff807d 0xbc1ce401203ff00f

def z434 : W := mkw 0x0b67a7cd066f7951 0x416cf4f9a0cdef2a 0xefe727490ffff1ff 0xbdfce4e921fffe3f

def z435 : W := mkw 0x26fefa403dfda100 0x04dfdf4807bfb420 0xffffff403ffff187 0xffffffe807fffe30

def z436 : W := mkw 0x0001010d80000000 0x00002021b0000000 0x0000000fc0000000 0x00000001f8000000

def z437 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0x57f8f8003fe18000 0xcaff1f0007fc3000

def z438 : W := mkw 0x01084c927310ceac 0xa02109924e6219d5 0xbf18ffffff11ffff 0xf7e31fffffe23fff

def z439 : W := mkw 0x0204c00214180220 0x8040980042830044 0xbf07c08e3e1e0e67 0x77e0f811c7c3c1cc

def z440 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000c08e00000003 0x50001811c0000000

def z441 : W := mkw 0x0367a7cd00000000 0x006cf4f9a0000000 0xc7e7e7cf00000003 0xf8fcfcf9e0000000

def z442 : W := mkw 0x07f7b7ed82004800 0x00fef6fdb0400900 0xfffffffffe007e07 0xffffffffffc00fc0

def z443 : W := mkw 0x000808106100848c 0x200101020c201091 0x00181830c0000000 0x0003030618000000

def z444 : W := mkw 0x0000400210100220 0x8000080042020044 0x0000c00e00100061 0x00001801c002000c

def z445 : W := mkw 0x0008080021008000 0x0001010004201000 0x0018380001018000 0x8003070000203000

def z446 : W := mkw 0x0b47f58f961a5a61 0x8168feb1f2c34b4c 0xbf07ff8ffe1e7e67 0x77e0fff1ffc3cfcc

def z447 : W := mkw 0x35fa3ef02be5ed86 0x06bf47de057cbdb0 0xfff83ff03fe1ff86 0xffff07fe07fc3ff0

def z448 : W := mkw 0x0801410a161a5a61 0x8100282142c34b4c 0xb80707083e1e7e67 0x3700e0e107c3cfcc

def z449 : W := mkw 0x0490102080000000 0x0092020410000000 0x00181830c0000000 0x0003030618000000

def z450 : W := mkw 0x0b0dcd9e771adeed 0xa161b9b3cee35bdd 0xbf07c78e3f1fffff 0x77e0f8f1c7e3ffff

def z451 : W := mkw 0x0305c58c14180000 0x0060b8b182830000 0xb707c78e3e1e0007 0x76e0f8f1c7c3c000

def z452 : W := mkw 0x14fb237929e735d7 0x429f646f253ce6ba 0xe8ff277901fff1ff 0xbd1fe4ef203ffe3f

def z453 : W := mkw 0x0901458e12125a61 0x812028b1c2424b4c 0x9800c78e30107e67 0x530018f1c6020fcc

def z454 : W := mkw 0x07fffffff11086ac 0xa0fffffffe2210d5 0xd7fffffff0000e03 0xfafffffffe0001c0

def z455 : W := mkw 0x00284a527130a7ac 0xa005094a4e2614f5 0xf8f8fffff1f1ffff 0xff1f1ffffe3e3fff

def z456 : W := mkw 0x0694900000000000 0x00d2920000000000 0x0718d80000000000 0x40e31b0000000000

def z457 : W := mkw 0x07f7b7ed80223151 0x40fef6fdb004462a 0xcfffffffc00071fb 0xf9fffffff8000e3f

def z458 : W := mkw 0x0267b34d80673151 0x404cf669b00ce62a 0xe8e7ff4fc1fff1ff 0xbd1cffe9f83ffe3f

def z459 : W := mkw 0x00084012311006a4 0x80010802462200d4 0x9818c0fe31100fe7 0xd303181fc62201fc

def z460 : W := mkw 0x24da381069c5848c 0x249b47020d38b091 0x40f83871c1e18198 0x881f070e383c3033

def z461 : W := mkw 0x006b6b493177b151 0x400d6d69262ef62a 0xf8ffff4931fff1ff 0xff1fffe9263ffe3f

def z462 : W := mkw 0x2498180029808000 0x0493030005301000 0x0018180000000000 0x0003030000000000

def z463 : W := mkw 0x06def80031108000 0x00dbdf0006221000 0xd7fff80031118005 0xfaffff0006223000

def z464 : W := mkw 0x00000012400006ac 0xa0000002480000d5 0x880020ffc1118fff 0x9100041ff82231ff

def z465 : W := mkw 0x0863634b167f7b71 0xc10c6c6962cfef6e 0xf8e727493fffffff 0xbf1ce4e927ffffff

def z466 : W := mkw 0x2fdffd8c3fdfd841 0x05fbffb187fbfb08 0xf7ffff003ffff005 0xfeffffe007fffe00

def z467 : W := mkw 0x07f7b7ed80471051 0x40fef6fdb008e20a 0xc7ffffffc01f807b 0xf8fffffff803f00f

def z468 : W := mkw 0x0021034900223151 0x400420692004462a 0x0000070000007000 0x000000e000000e00

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0x8018f80000000001 0xd0031f0000000000

def z470 : W := mkw 0x2b47fd8e165fda61 0x8568ffb1c2cbfb4c 0xbf07ff8e3e1ffe67 0x77e0fff1c7c3ffcc

def z471 : W := mkw 0x0063234900000000 0x000c646920000000 0xc8e72749011181ff 0xb91ce4e92022303f

def z472 : W := mkw 0x0000001000000484 0x0000000200000090 0x080000f000000f82 0x0100001e000001f0

def z473 : W := mkw 0x08004002141a1261 0x810008004283424c 0x00000000001e0060 0x000000000003c00c

def z474 : W := mkw 0x15b006f00aa06d86 0x02b600de01540db0 0x6fe007f00ee07f82 0x2dfc00fe01dc0ff0

def z475 : W := mkw 0x15b907fdaba06d86 0x02b720ffb5740db0 0xfff807ffffe07f86 0xffff00fffffc0ff0

def z476 : W := mkw 0x00000012400006ac 0xa0000002480000d5 0x8818f8ffc0000ffb 0xd1031f1ff80001ff

def z477 : W := mkw 0x079494a480000000 0x00f2929490000000 0x0700000000000000 0x00e0000000000000

def z478 : W := mkw 0x0001410a10121261 0x800028214202424c 0xb807c78e301e7e67 0x7700f8f1c603cfcc

def z479 : W := mkw 0x092107ef82025a61 0x812420fdf0404b4c 0x080007ffc0007e62 0x010000fff8000fcc

def z480 : W := mkw 0x04fa7a73f11086ac 0xa09f4f4e7e2210d5 0xd8f8f8fff1118fff 0xdb1f1f1ffe2231ff

def z481 : W := mkw 0x36def8103ffded86 0x06dbdf0207ffbdb0 0xfffff8003fffff85 0xffffff0007fffff0

def z482 : W := mkw 0x0042200000450000 0x000844000008a000 0x60e7000000ee0000 0x2c1ce000001dc000

def z483 : W := mkw 0x159804b02ba06d86 0x02b3009605740db0 0x3f1800b03fe07f84 0x47e3001607fc0ff0

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0070000001e0005 0x3400e0000003c000

def z485 : W := mkw 0x0498000029800000 0x0093000005300000 0x171800003e000000 0x42e3000007c00000

def z486 : W := mkw 0x04b0026000000000 0x0096004c00000000 0x40f8007000000000 0x881f000e00000000

def z487 : W := mkw 0x0901058e02025a61 0x812020b1c0404b4c 0xbf00078e3e007e66 0x77e000f1c7c00fcc

def z488 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0e0000001e00004 0xbc1c0000003c0000

def z489 : W := mkw 0x17ffb7fdabe77dd7 0x42fff6ffb57cefba 0xffffffffffffffff 0xffffffffffffffff

def z490 : W := mkw 0x37f6b6e00eed6902 0x06fed6dc01ddad20 0x67e707000eee7000 0x2cfce0e001ddce00

def z491 : W := mkw 0x269cd8003d988000 0x04d39b0007b31000 0xb71fd8003e1e0005 0x76e3fb0007c3c000

def z492 : W := mkw 0x0020024000202100 0x0004004800040420 0x0800074000007182 0x010000e800000e30

def z493 : W := mkw 0x2edff90e3ddf9261 0x85dbff21c7bbf24c 0xf7fff80e3fff8065 0xfeffff01c7fff00c

def z494 : W := mkw 0x07f7f7ed94180000 0x00fefefdb2830000 0xf7fffffffe1e0007 0xfeffffffffc3c000

def z495 : W := mkw 0x269cd8127d9886ac 0xa4d39b024fb310d5 0x9f18f8ffff118fff 0xd3e31f1fffe231ff

def z496 : W := mkw 0x004a6812715586ac 0xa0094d024e2ab0d5 0xf8fff8fff1ff8fff 0xff1fff1ffe3ff1ff

def z497 : W := mkw 0x0008000021000000 0x0001000004200000 0x9018000031000004 0xd203000006200000

def z498 : W := mkw 0x0498480039908000 0x0093090007321000 0xf7f8f8003ff18005 0xfeff1f0007fe3000

def z499 : W := mkw 0x159004a00a804802 0x02b2009401500900 0x070000000e000000 0x00e0000001c00000

def z500 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0x47e707ffc0000002 0x28fce0fff8000000

def z501 : W := mkw 0x0020026180000000 0x0004004c30000000 0x00000071c0000000 0x0000000e38000000

def z502 : W := mkw 0x0247f90fd0108228 0xa048ff21fa021045 0x0007f80fc0118079 0x0000ff01f802300f

def z503 : W := mkw 0x0305858c00021041 0x0060b0b180004208 0xaf07c78e001e7067 0x75e0f8f1c003ce0c

def z504 : W := mkw 0x15b846f23bb06fa6 0x82b708de47760df4 0xfff8c7fe3ff07fe7 0xffff18ffc7fe0ffc

def z505 : W := mkw 0x27ffffedbddd8000 0x04fffffdb7bbb000 0xf7ffff003fff8005 0xfeffffe007fff000

def z506 : W := mkw 0x14b8027029a02586 0x0297004e053404b0 0xf7f800703fe00184 0xfeff000e07fc0030

def z507 : W := mkw 0x0b0dc59e371a5ee5 0x8161b8b3c6e34bdc 0xbf1fc7fe3f1e7fe7 0xf7e3f8ffc7e3cffc

def z508 : W := mkw 0x224ef812755d86ac 0xa449df024eabb0d5 0x981ff8fff11f8fff 0xd303ff1ffe23f1ff

def z509 : W := mkw 0x0043210900471051 0x400864212008e20a 0x00070000000e0000 0x0000e0000001c000

def z510 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0x48e0274901e1f1fa 0x891c04e9203c3e3f

def z511 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800070000007006 0x350000e000000e00

def z512 : W := mkw 0x206b6b493dffb151 0x440d6d6927bff62a 0xf8e727493ffff1ff 0xbf1ce4e927fffe3f

def z513 : W := mkw 0x1b0dc59e3fba7fe7 0x8361b8b3c7f74ffc 0xbf07c78e3ffe7fe7 0x77e0f8f1c7ffcffc

def z514 : W := mkw 0x0b05858e02025a61 0x8160b0b1c0404b4c 0x8f07c78e00007e63 0x71e0f8f1c0000fcc

def z515 : W := mkw 0x0000480250108228 0xa00009004a021045 0x9800f88ff0118e7f 0x53001f11fe0231cf

def z516 : W := mkw 0x05b006e000000000 0x00b600dc00000000 0x47e0070000000000 0x28fc00e000000000

def z517 : W := mkw 0x0008480031108000 0x0001090006221000 0x9818f849311181ff 0xd3031f092622303f

def z518 : W := mkw 0x36fefa703dfda586 0x06dfdf4e07bfb4b0 0xf7fff8703fff8185 0xfeffff0e07fff030

def z519 : W := mkw 0x17ffb7fdab804c86 0x02fff6ffb5700990 0xd7fffffffe000e03 0xfaffffffffc001c0

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000ffc0000002 0x0000001ff8000000

def z521 : W := mkw 0x07d7b58c00000000 0x00faf6b180000000 0xc7ffff8e00000003 0xf8fffff1c0000000

def z522 : W := mkw 0x096327cf02677b71 0xc12c64f9e04cef6e 0xe8e727cf01ffffff 0xbd1ce4f9e03fffff

def z523 : W := mkw 0x0b05c59e561a5eed 0xa160b8b3cac34bdd 0xbf07c7fffe1e7fff 0x77e0f8ffffc3cfff

def z524 : W := mkw 0x0b05c58e167f7b71 0xc160b8b1c2cfef6e 0xbf07c78e3fffffff 0x77e0f8f1c7ffffff

def z525 : W := mkw 0x0205810c00000000 0x0040b02180000000 0x0007c00e00000001 0x0000f801c0000000

def z526 : W := mkw 0x20004800145d8000 0x04000900028bb000 0x00000000001f8000 0x000000000003f000

def z527 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1800f80ff1118ffd 0x03001f01fe2231ff

def z528 : W := mkw 0x26f7b3490cef3151 0x44def669219de62a 0x67e707000eee7000 0x2cfce0e001ddce00

def z529 : W := mkw 0x0008480031108000 0x0001090006221000 0x1018d80030000000 0x42031b0006000000

def z530 : W := mkw 0x012006c002206900 0x002400d800440d20 0xffe007c03fe07f86 0xfffc00f807fc0ff0

def z531 : W := mkw 0x0a04c00614180220 0x81409800c2830044 0x0000c00600000000 0x00001800c0000000

def z532 : W := mkw 0x05f327e900673151 0x40be64fd200ce62a 0xefff27f901fff1ff 0xfdffe4ff203ffe3f

def z533 : W := mkw 0x26dff9093ddf9051 0x44dbff2127bbf20a 0xf7fff8093fff807d 0xfeffff0127fff00f

def z534 : W := mkw 0x0b04c48616184a20 0x81609890c2c30944 0x9f00c08e3e100e67 0x53e01811c7c201cc

def z535 : W := mkw 0x2edef8023fdfda61 0x85dbdf0047fbfb4c 0xfffff8003ffffe65 0xffffff0007ffffcc

def z536 : W := mkw 0x24fa3a4129e5a110 0x449f4748253cb422 0x40f8384101e18198 0x881f0708203c3033

def z537 : W := mkw 0x0204900480000000 0x0040920090000000 0x0000d806c0000000 0x00001b00d8000000

def z538 : W := mkw 0x08004002167f7b71 0xc100080042cfef6e 0x380000003ffffffc 0x0700000007ffffff

def z539 : W := mkw 0x0a05c10e161a5a61 0x8140b821c2c34b4c 0x3807c00e3e1e7e65 0x0700f801c7c3cfcc

def z540 : W := mkw 0x0fd7f58e161a5a61 0x81fafeb1c2c34b4c 0xffffff8e3e1e7e67 0xfffffff1c7c3cfcc

def z541 : W := mkw 0x08004002161a5a61 0x8100080042c34b4c 0xb800c08e3e1e7e67 0x57001811c7c3cfcc

def z542 : W := mkw 0x2b0dcd8e3fdfda61 0x8561b9b1c7fbfb4c 0xbf07c78e3ffffe67 0x77e0f8f1c7ffffcc

def z543 : W := mkw 0x2fffffcf3ffffb71 0xc5fffff9e7ffff6e 0xffffffcf3fffffff 0xfffffff9e7ffffff

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x00183871c0000000 0x8003070e38000000

def z545 : W := mkw 0x35b84ef03ffded86 0x06b709de07ffbdb0 0xfff807f03fffff86 0xffff00fe07fffff0

def z546 : W := mkw 0x00000012400006ac 0xa0000002480000d5 0x000000b6c0000e00 0x00000016d80001c0

def z547 : W := mkw 0x0008001021000484 0x0001000204200090 0x0018007001000180 0x8003000e00200030

def z548 : W := mkw 0x0b67e7cf161a5a61 0x816cfcf9e2c34b4c 0xffe7e7cf3e1e7e67 0xfffcfcf9e7c3cfcc

def z549 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0x1f00c78e3e007e62 0x43e018f1c7c00fcc

def z550 : W := mkw 0x180840123fba7fe7 0x8301080247f74ffc 0x380000003ffe7fe4 0x0700000007ffcffc

def z551 : W := mkw 0x0001010800021041 0x0000202100004208 0xa8072749011ff1ff 0xb500e4e92023fe3f

def z552 : W := mkw 0x069cc0003d980000 0x00d3980007b30000 0xf7ffc0003ffe0005 0xfefff80007ffc000

def z553 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0x1f1807f03e007f82 0x43e300fe07c00ff0

def z554 : W := mkw 0x0021034900673151 0x40042069200ce62a 0x2800074901fff1fe 0x050000e9203ffe3f

def z555 : W := mkw 0x1fb5c7ee1eba7b63 0x83f6b8fdc3d74f6c 0xffe7c78e3efe7e67 0x7ffcf8f1c7dfcfcc

def z556 : W := mkw 0x0a04c002161a5a61 0x8140980042c34b4c 0xbf07c0003e1e7e65 0x77e0f80007c3cfcc

def z557 : W := mkw 0x0a05c10e141a1261 0x8140b821c283424c 0xa807c70e001e7067 0x3500f8e1c003ce0c

def z558 : W := mkw 0x0062224100652110 0x400c4448200ca422 0xe0e7204101ff819d 0xbc1ce408203ff033

def z559 : W := mkw 0x0043690b50579279 0xe0086d216a0af24f 0x0007f80fc01f8079 0x0000ff01f803f00f

def z560 : W := mkw 0x0b6fefdf777ffffd 0xe16dfdfbeeefffff 0xffffffffffffffff 0xffffffffffffffff

def z561 : W := mkw 0x159804b02b804c86 0x02b3009605700990 0xbf1807b03e007e06 0x77e300f607c00fc0

def z562 : W := mkw 0x0001010800021041 0x0000202100004208 0x20070700000e7000 0x2400e0e00001ce00

def z563 : W := mkw 0x26def8003dffb151 0x44dbdf0007bff62a 0xfffff8003ffff1fd 0xffffff0007fffe3f

def z564 : W := mkw 0x2246f800145d8000 0x0448df00028bb000 0xe0e7f80001ff8005 0xbc1cff00003ff000

def z565 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0x47ff3f71c0000000 0xa8ffe7ee38000000

def z566 : W := mkw 0x07ffbffde100848c 0x20fff7ffbc201091 0xc7ffffffc101819b 0xf8fffffff8203033

def z567 : W := mkw 0x00004812501086ac 0xa00009024a0210d5 0x0800f8ffc0118ffb 0x01001f1ff80231ff

def z568 : W := mkw 0x07f6b6e000000000 0x00fed6dc00000000 0xc7fffff000000003 0xf8fffffe00000000

def z569 : W := mkw 0x15b84ef03bb0ed86 0x02b709de07761db0 0xfff8fff03ff1ff87 0xffff1ffe07fe3ff0

def z570 : W := mkw 0x012107ed80223151 0x402420fdb004462a 0x080007ffc00071fa 0x010000fff8000e3f

def z571 : W := mkw 0x15fa36f1aba06d86 0x02bf46de35740db0 0xfff83ff1ffe07f86 0xffff07fe3ffc0ff0

def z572 : W := mkw 0x159804b02b804c86 0x02b3009605700990 0xf7f800b03fe00e04 0xfeff001607fc01c0

def z573 : W := mkw 0x1db846f23fba7fe7 0x83b708de47f74ffc 0xfff807f03ffe7fe6 0xffff00fe07ffcffc

def z574 : W := mkw 0x0043210900673151 0x40086421200ce62a 0x2807200901fff1fd 0x0500e401203ffe3f

def z575 : W := mkw 0x0000400210100220 0x8000080042020044 0x9818f8fff0100e67 0xd3031f1ffe0201cc

def z576 : W := mkw 0x0043210800471041 0x000864210008e208 0xe8e7270801fff067 0xbd1ce4e1003ffe0c

def z577 : W := mkw 0x0063634b10773371 0xc00c6c69620ee66e 0xf8e7e7cf31ffffff 0xff1cfcf9e63fffff

def z578 : W := mkw 0x07f7b7ffc00006ac 0xa0fef6fff80000d5 0xcfffffffc0000ffb 0xf9fffffff80001ff

def z579 : W := mkw 0x17fffffffbb0efae 0xa2ffffffff761df5 0xfffffffffff1ffff 0xfffffffffffe3fff

def z580 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0x1707c08e3e1e0e61 0x42e0f811c7c3c1cc

def z581 : W := mkw 0x2f9ddd8e3f9ada61 0x85f3bbb1c7f35b4c 0xbf1fdf8e3e1e7e67 0x77e3fbf1c7c3cfcc

def z582 : W := mkw 0x0100048002004800 0x0020009000400900 0x0800078000007e02 0x010000f000000fc0

def z583 : W := mkw 0x020cc812751886ac 0xa04199024ea310d5 0xbf1ff8ffff1f8fff 0xf7e3ff1fffe3f1ff

def z584 : W := mkw 0x0062224100652110 0x400c4448200ca422 0x40e0000000e00000 0x081c0000001c0000

def z585 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe8e7074001ee7186 0xbd1ce0e8003dce30

def z586 : W := mkw 0x14b8027029a02586 0x0297004e053404b0 0xe8f8077001e07186 0xbd1f00ee003c0e30

def z587 : W := mkw 0x0008480271108228 0xa00109004e221045 0x9018f80ff111807d 0xd2031f01fe22300f

def z588 : W := mkw 0x1fbdcffe7fbaffef 0xa3f7b9ffcff75ffd 0xffffffffffffffff 0xffffffffffffffff

def z589 : W := mkw 0x14b0026008a02102 0x0296004c01140420 0x40e0000000e00000 0x081c0000001c0000

def z590 : W := mkw 0x024ff91ff11086ac 0xa049ff23fe2210d5 0x981ff8fff1118fff 0xd303ff1ffe2231ff

def z591 : W := mkw 0x0204c00014180000 0x0040980002830000 0x0007c000001e0001 0x0000f8000003c000

def z592 : W := mkw 0x0b0dcd8e371ada61 0x8161b9b1c6e35b4c 0xbf1fff8e3f1ffe67 0xf7e3fff1c7e3ffcc

def z593 : W := mkw 0x0b47e58f165f5a71 0xc168fcb1e2cbeb4e 0xbf07e78f3e1ffe7f 0x77e0fcf1e7c3ffcf

def z594 : W := mkw 0x200848127ddd86ac 0xa40109024fbbb0d5 0xb818f8ffffff8fff 0xd7031f1ffffff1ff

def z595 : W := mkw 0x24fa3a61a9c58000 0x049f474c3538b000 0x40f83871c1e18000 0x881f070e383c3000

def z596 : W := mkw 0x04d2300000000000 0x009a460000000000 0x40f8380000000000 0x881f070000000000

def z597 : W := mkw 0x0021034800223141 0x0004206900044628 0xe8e7074801fe71e7 0xbd1ce0e9003fce3c

def z598 : W := mkw 0x07ffb7fda1000484 0x00fff6ffb4200090 0xdffffffff1000f87 0xfbfffffffe2001f0

def z599 : W := mkw 0x0000080040008008 0x2000010008001001 0x00003801c0018018 0x0000070038003003

def z600 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0x60e7270900fff079 0x2c1ce4e1201ffe0f

def z601 : W := mkw 0x0000000200000220 0x8000000040000044 0x0800008e00000e62 0x01000011c00001cc

def z602 : W := mkw 0x05b806f021000484 0x00b700de04200090 0xdff807f031000f86 0xfbff00fe062001f0

def z603 : W := mkw 0x0b05858e060a5a61 0x8160b0b1c0c14b4c 0x2f07078e0e0e7e62 0x25e0e0f1c1c1cfcc

def z604 : W := mkw 0x200848003dffb151 0x4401090007bff62a 0x380000003ffff1fc 0x0700000007fffe3f

def z605 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe0e7274900ee7003 0xbc1ce4e9201dce00

def z606 : W := mkw 0x092107cf02227b71 0xc12420f9e0444f6e 0x080007cf00007ffa 0x010000f9e0000fff

def z607 : W := mkw 0x0b05c58e141a1261 0x8160b8b1c283424c 0x8707c78e001e0063 0x70e0f8f1c003c00c

def z608 : W := mkw 0x059004a000000000 0x00b2009400000000 0x071800b000000000 0x40e3001600000000

def z609 : W := mkw 0x016327ed80673151 0x402c64fdb00ce62a 0xe8e727ffc1fff1ff 0xbd1ce4fff83ffe3f

def z610 : W := mkw 0x149800102ba06d86 0x0293000205740db0 0xfff800003fe07f84 0xffff000007fc0ff0

def z611 : W := mkw 0x27ffffedbd988000 0x04fffffdb7b31000 0xd7fffffffe000003 0xfaffffffffc00000

def z612 : W := mkw 0x100848127bb0efae 0xa20109024f761df5 0xb818f8fffff1ffff 0xd7031f1ffffe3fff

def z613 : W := mkw 0x00004012501006ac 0xa00008024a0200d5 0x9800c0fff0100fff 0x5300181ffe0201ff

def z614 : W := mkw 0x05f337ed80000000 0x00be66fdb0000000 0x40f83fffc0000002 0x881f07fff8000000

def z615 : W := mkw 0x379cdcb03f98cc86 0x06f39b9607f31990 0x1718d8b03e000e00 0x42e31b1607c001c0

def z616 : W := mkw 0x000808106100848c 0x200101020c201091 0x981838f1f1018f9e 0xd303071e3e2031f3

def z617 : W := mkw 0x0000400210100220 0x8000080042020044 0x9800e0cf31118fff 0xd3001c19e62231ff

def z618 : W := mkw 0x24da380029c58000 0x049b47000538b000 0xe0ff380001ff8005 0xbc1fe700003ff000

def z619 : W := mkw 0x15b006f002206d86 0x02b600de00440db0 0xcff807f000007f82 0xf9ff00fe00000ff0

def z620 : W := mkw 0x1f9cc4b63f984ea6 0x83f39896c7f309d4 0x1718c0b63e000e00 0x42e31816c7c001c0

def z621 : W := mkw 0x15b907f92ba27dd7 0x42b720ff25744fba 0xfff807f93fe07ffe 0xffff00ff27fc0fff

def z622 : W := mkw 0x0305858c00000000 0x0060b0b180000000 0x0707070000000000 0x20e0e0e000000000

def z623 : W := mkw 0x0ff7f7ef961a5a61 0x81fefefdf2c34b4c 0xffe7c78e3e1e7e67 0x7ffcf8f1c7c3cfcc

def z624 : W := mkw 0x15984cb27b90ceae 0xa2b309964f7219d5 0x1718d8b6fe000e00 0x42e31b16dfc001c0

def z625 : W := mkw 0x24da78003ddd8000 0x049b4f0007bbb000 0x70f838003fff8004 0x8e1f070007fff000

def z626 : W := mkw 0x01294ffff11086ac 0xa02529fffe2210d5 0x9818fffff1118fff 0xd3031ffffe2231ff

def z627 : W := mkw 0x0000400210100220 0x8000080042020044 0x1000c08630000e00 0x42001810c60001c0

def z628 : W := mkw 0x1db907fe2ba27fe7 0x83b720ffc5744ffc 0xfff807fe3fe07fe6 0xffff00ffc7fc0ffc

def z629 : W := mkw 0x269cd8003ddd8000 0x04d39b0007bbb000 0x3718d8003fff8004 0x46e31b0007fff000

def z630 : W := mkw 0x0000480250108228 0xa00009004a021045 0x8018f8ffc011807b 0xd0031f1ff802300f

def z631 : W := mkw 0x0901059e42025eed 0xa12020b3c8404bdd 0x080007ffc0007ffa 0x010000fff8000fff

def z632 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000204101018198 0x8000040820203033

def z633 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0x57f800f03fe00f80 0xcaff001e07fc01f0

def z634 : W := mkw 0x06d7b10d80000000 0x00daf621b0000000 0xc7fff80fc0000001 0xf8ffff01f8000000

def z635 : W := mkw 0x26dff90dbddd8000 0x04dbff21b7bbb000 0xf7fff80fffff8005 0xfeffff01fffff000

def z636 : W := mkw 0x0063234900223151 0x400c64692004462a 0xc8e72749000071fb 0xb91ce4e920000e3f

def z637 : W := mkw 0x26dff9083ddf9041 0x04dbff2107bbf208 0xffffff083ffff067 0xffffffe107fffe0c

def z638 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xc7e7c78e00000003 0x78fcf8f1c0000000

def z639 : W := mkw 0x0001010900021051 0x400020212000420a 0x0000000900000078 0x000000012000000f

def z640 : W := mkw 0x004a680031558000 0x00094d00062ab000 0xf0fff80031ff8005 0xfe1fff00063ff000

def z641 : W := mkw 0x26d6f800145d8000 0x04dadf00028bb000 0xc7fff800001f8001 0xf8ffff000003f000

def z642 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x0018f87fc11181f9 0x80031f0ff822303f

def z643 : W := mkw 0x07ffb7eda9800000 0x00fff6fdb5300000 0xf7ffffffffe00007 0xfefffffffffc0000

def z644 : W := mkw 0x0b04848406084800 0x0160909080c10900 0x070000000e000000 0x00e0000001c00000

def z645 : W := mkw 0x0063234900000000 0x000c646920000000 0x40e7070000000000 0x281ce0e000000000

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000200001118005 0x9000040000223000

def z647 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0x48f807f001e07f82 0x891f00fe003c0ff0

def z648 : W := mkw 0x0b04c486161a5a61 0x81609890c2c34b4c 0x3f00c0863e1e7e64 0x47e01810c7c3cfcc

def z649 : W := mkw 0x26fefa61bddd8000 0x04dfdf4c37bbb000 0xf7fff871ffff8005 0xfeffff0e3ffff000

def z650 : W := mkw 0x116327f902677dd7 0x422c64ff204cefba 0xe8e727f901ffffff 0xbd1ce4ff203fffff

def z651 : W := mkw 0x15b84ef27bb0efae 0xa2b709de4f761df5 0xfff8dff6ffe07f86 0xffff1bfedffc0ff0

def z652 : W := mkw 0x08000000060a5841 0x0100000000c14b08 0x200000000e0e7000 0x0400000001c1ce00

def z653 : W := mkw 0x006b2b596167b5dd 0x600d656b2c2cf6bb 0xe8ff3f79c1fff1ff 0xbd1fe7ef383ffe3f

def z654 : W := mkw 0x0205c108141a1041 0x0040b82102834208 0xbf07c7083e1e7067 0x77e0f8e107c3ce0c

def z655 : W := mkw 0x0020024000202100 0x0004004800040420 0x60e0070000e07000 0x2c1c00e0001c0e00

def z656 : W := mkw 0x2fdefc863fddca20 0x85fbdf90c7fbb944 0xf7fff8863fff8e05 0xfeffff10c7fff1c0

def z657 : W := mkw 0x0f94d4a696184a20 0x81f29a94d2c30944 0x1718d8b6fe000e00 0x42e31b16dfc001c0

def z658 : W := mkw 0x15fa26f12be56d96 0x42bf44de257cadb2 0xfff827f13fe1ff9e 0xffff04fe27fc3ff3

def z659 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0x40fff80001ff8001 0x881fff00003ff000

def z660 : W := mkw 0x15fb6ffb7bf7ffff 0xe2bf6dff6f7effff 0xffffffffffffffff 0xffffffffffffffff

def z661 : W := mkw 0x26fffb493dffb151 0x44dfff6927bff62a 0xf7ffff003ffff005 0xfeffffe007fffe00

def z662 : W := mkw 0x269cd8003d988000 0x04d39b0007b31000 0xf7f8d8003fe00004 0xfeff1b0007fc0000

def z663 : W := mkw 0x0043210900471051 0x400864212008e20a 0xa8072709001ff07f 0x3500e4e12003fe0f

def z664 : W := mkw 0x04f3336980000000 0x009e666d30000000 0xc0ff3f79c0000003 0xb81fe7ef38000000

def z665 : W := mkw 0x0101058c00000000 0x002020b180000000 0x0000078e00000002 0x000000f1c0000000

def z666 : W := mkw 0x24da781279d586ac 0xa49b4f024f3ab0d5 0xd8f8f8fff1f18fff 0xdb1f1f1ffe3e31ff

def z667 : W := mkw 0x110804902ba06d86 0x0221009205740db0 0xbf0007803fe07f86 0x77e000f007fc0ff0

def z668 : W := mkw 0x2042380000458000 0x040847000008b000 0x0000380000018000 0x0000070000003000

def z669 : W := mkw 0x0b05858c060a5841 0x0160b0b180c14b08 0xaf0707080e1e7067 0x35e0e0e101c3ce0c

def z670 : W := mkw 0x179c94b4ab804c86 0x02f3929695700990 0x1718d8b6fe000e00 0x42e31b16dfc001c0

def z671 : W := mkw 0x0367a7cd00673151 0x406cf4f9a00ce62a 0xefe7e7cf01fff1ff 0xfdfcfcf9e03ffe3f

def z672 : W := mkw 0x1498003029800486 0x0293000605300090 0x0018003000000000 0x0003000600000000

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800004001000186 0x9100000800200030

def z674 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe0e7270001fff005 0xbc1ce4e0003ffe00

def z675 : W := mkw 0x0000000000021041 0x0000000000004208 0x28000000001e7064 0x050000000003ce0c

def z676 : W := mkw 0x17bd87fc2ba06d86 0x02f7b0ff85740db0 0xffffc7fe3fe07f87 0xfffff8ffc7fc0ff0

def z677 : W := mkw 0x0246b00000000000 0x0048d60000000000 0x0007f80000000001 0x0000ff0000000000

def z678 : W := mkw 0x06f6b26180000000 0x00ded64c30000000 0xc7fff871c0000001 0xf8ffff0e38000000

def z679 : W := mkw 0x0900048602004a20 0x81200090c0400944 0x0000008600000e00 0x00000010c00001c0

def z680 : W := mkw 0x0021034900223151 0x400420692004462a 0xa8070749001e71ff 0x3500e0e92003ce3f

def z681 : W := mkw 0x100800102ba06d86 0x0201000205740db0 0xb81800f03fe07f86 0xd703001e07fc0ff0

def z682 : W := mkw 0x0042200000450000 0x000844000008a000 0x00072000001f8001 0x0000e4000003f000

def z683 : W := mkw 0x112006f002206d86 0x022400de00440db0 0xbf0007f03e007f86 0x77e000fe07c00ff0

def z684 : W := mkw 0x0021034900000000 0x0004206920000000 0x0000074900000002 0x000000e920000000

def z685 : W := mkw 0x0ff7f7ef96184a20 0x81fefefdf2c30944 0xd7fffffffe000e03 0xfaffffffffc001c0

def z686 : W := mkw 0x0ff7b7ed860a5841 0x01fef6fdb0c14b08 0x67e707000e0e7000 0x2cfce0e001c1ce00

def z687 : W := mkw 0x006b6b5b711086ac 0xa00d6d6b6e2210d5 0xd8fffffff1118fff 0xfb1ffffffe2231ff

def z688 : W := mkw 0x04b8024029a02100 0x0097004805340420 0xfff807403fe07186 0xffff00e807fc0e30

def z689 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xc7e7274900000003 0xb8fce4e920000000

def z690 : W := mkw 0x37fefee03ffde902 0x06ffdfdc07ffbd20 0xf7ffff003ffff005 0xfeffffe007fffe00

def z691 : W := mkw 0x15984cb27b90ceae 0xa2b309964f7219d5 0x9f18f8ffff118fff 0xd3e31f1fffe231ff

def z692 : W := mkw 0x2246f800145d8000 0x0448df00028bb000 0xb707f8003e1f8005 0x76e0ff0007c3f000

def z693 : W := mkw 0x17bcc6f03fb86d86 0x02f798de07f70db0 0xffffc7f03ffe7f87 0xfffff8fe07ffcff0

def z694 : W := mkw 0x0008481031108484 0x0001090206221090 0x9818f8f031118f87 0xd3031f1e062231f0

def z695 : W := mkw 0x0000000000450000 0x000000000008a000 0x2000000001ff8004 0x04000000003ff000

def z696 : W := mkw 0x14fa3271a9a02586 0x029f464e353404b0 0x40f83871c1e00180 0x881f070e383c0030

def z697 : W := mkw 0x06def812711086ac 0xa0dbdf024e2210d5 0xdffff8fff1118fff 0xfbffff1ffe2231ff

def z698 : W := mkw 0x0062224000652100 0x000c4448000ca420 0xe8e7274001fff187 0xbd1ce4e8003ffe30

def z699 : W := mkw 0x000000104000048c 0x2000000208000091 0x00000071c0000198 0x0000000e38000033

def z700 : W := mkw 0x37fffff93ffffdd7 0x46ffffff27ffffba 0xfffffff93fffffff 0xffffffff27ffffff

def z701 : W := mkw 0x269cd8003d988000 0x04d39b0007b31000 0x9718f8003f118005 0xd2e31f0007e23000

def z702 : W := mkw 0x012107ffc00006ac 0xa02420fff80000d5 0x080007ffc0000ffa 0x010000fff80001ff

def z703 : W := mkw 0x0043210900000000 0x0008642120000000 0x0007200900000001 0x0000e40120000000

def z704 : W := mkw 0x0367b7ed80000000 0x006cf6fdb0000000 0x0007ffffc0000003 0x0000fffff8000000

def z705 : W := mkw 0x159804b02b804c86 0x02b3009605700990 0x9f1800f03f000f86 0xd3e3001e07e001f0

def z706 : W := mkw 0x0801010e00021261 0x81002021c000424c 0x0000000e00000060 0x00000001c000000c

def z707 : W := mkw 0x0cf27263961a5a61 0x819e4e4c72c34b4c 0x78f83871fe1e7e64 0x8f1f070e3fc3cfcc

def z708 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff807b03ee07e06 0x7fff00f607dc0fc0

def z709 : W := mkw 0x15b80ef06ba0ed8e 0x22b701de0d741db1 0xfff807f03fe1ff9e 0xffff00fe07fc3ff3

def z710 : W := mkw 0x07f7b7ed80021041 0x00fef6fdb0004208 0xcfffffffc0007063 0xf9fffffff8000e0c

def z711 : W := mkw 0x192107fc02227dc7 0x032420ff80444fb8 0x080007f000007f82 0x010000fe00000ff0

def z712 : W := mkw 0x0304848006084800 0x0060909000c10900 0xbf0707803e0e7e06 0x77e0e0f007c1cfc0

def z713 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe8e7074001fff1fe 0xbd1ce0e8003ffe3f

def z714 : W := mkw 0x0b0d8d9c670adccd 0x2161b1b38ce15b99 0x271f3f71cf0ff198 0xa4e3e7ee39e1fe33

def z715 : W := mkw 0x086b6b5b777ffffd 0xe10d6d6b6eefffff 0xf8e727493fffffff 0xbf1ce4e927ffffff

def z716 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0x67e700000fff8004 0x2cfce00001fff000

def z717 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf1fdfbefe1e7e67 0x77e3fbf7dfc3cfcc

def z718 : W := mkw 0x0021034900223151 0x400420692004462a 0x080007ffc00071fa 0x010000fff8000e3f

def z719 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0x7fe700003fff8ffc 0x2ffce00007fff1ff

def z720 : W := mkw 0x15b806e02ba06902 0x02b700dc05740d20 0xfff807803fe07e06 0xffff00f007fc0fc0

def z721 : W := mkw 0x0305858c02025841 0x0060b0b180404b08 0xbf07c78e3e1e7e67 0x77e0f8f1c7c3cfcc

def z722 : W := mkw 0x00000012400006ac 0xa0000002480000d5 0x8818f8ffc1118fff 0xd1031f1ff82231ff

def z723 : W := mkw 0x3366fef0167ded86 0x066cdfde02cfbdb0 0x0807fff0001fff83 0x0100fffe0003fff0

def z724 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7e720003fff8005 0xbefce40007fff000

def z725 : W := mkw 0x07b496e480000000 0x00f692dc90000000 0x47f8d8f6c0000000 0xc8ff1b1ed8000000

def z726 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0x77ff38003fff8004 0xaeffe70007fff000

def z727 : W := mkw 0x2a47f90f945f9261 0x8548ff21f28bf24c 0x0007f80fc01f8061 0x0000ff01f803f00c

def z728 : W := mkw 0x2ddb3d8e2bc7da61 0x85bb67b1c578fb4c 0x48f83f8e01e1fe62 0x891f07f1c03c3fcc

def z729 : W := mkw 0x079494a480000000 0x00f2929490000000 0xc7f8d8b6c0000000 0xf8ff1b16d8000000

def z730 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xfffff8ffffff81ff 0xffffff1ffffff03f

def z731 : W := mkw 0x006b6b5b7177b7fd 0xe00d6d6b6e2ef6ff 0x70ffdfb6f0ee7e00 0x6e1ffbf6de1dcfc0

def z732 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0x7ff807703fe07f84 0xafff00ee07fc0ff0

def z733 : W := mkw 0x0000000000673151 0x40000000000ce62a 0xa818f8ffc1fff1ff 0xd5031f1ff83ffe3f

def z734 : W := mkw 0x006a6a537175a7bc 0xe00d4d4a6e2eb4f7 0x58e0204131f18ffc 0x8b1c0408263e31ff

def z735 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0xe7ffffffc1eff19b 0xfcfffffff83dfe33

def z736 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1000000030118e78 0x02000000060231cf

def z737 : W := mkw 0x27f7b7ed8cef3151 0x44fef6fdb19de62a 0xefffffffcffff1ff 0xfdfffffff9fffe3f

def z738 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0x67ffd8000eee0000 0x6cfffb0001ddc000

def z739 : W := mkw 0x100848127bb0efae 0xa20109024f761df5 0x380000003fe07f84 0x0700000007fc0ff0

def z740 : W := mkw 0x05f327e900000000 0x00be64fd20000000 0xc7ffffffc0000003 0xf8fffffff8000000

def z741 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0x77e7f8003fff8005 0x2efcff0007fff000

def z742 : W := mkw 0x112907f923227dd7 0x422520ff24644fba 0x981827f93111ffff 0xd30304ff26223fff

def z743 : W := mkw 0x1f9cccb67f98ceae 0xa3f39996cff319d5 0x1718d8b6fe000e00 0x42e31b16dfc001c0

def z744 : W := mkw 0x07fffffff11086ac 0xa0fffffffe2210d5 0x5fe7070031118ffc 0x2bfce0e0062231ff

def z745 : W := mkw 0x34fa3a7069e5a58e 0x269f474e0d3cb4b1 0x40f83871c1e18198 0x881f070e383c3033

def z746 : W := mkw 0x012107c902227951 0x402420f920444f2a 0x080007c900007ffa 0x010000f920000fff

def z747 : W := mkw 0x26def8107ddd848c 0x24dbdf020fbbb091 0xfffff8f1ffff8f9f 0xffffff1e3ffff1f3

def z748 : W := mkw 0x26def8023ddd8220 0x84dbdf0047bbb044 0xfffff8003fff8e65 0xffffff0007fff1cc

def z749 : W := mkw 0x200848127dffb7fd 0xe40109024fbff6ff 0x380000003ffffffc 0x0700000007ffffff

def z750 : W := mkw 0x0b05858c060a5841 0x0160b0b180c14b08 0xbf0707883e1e7e67 0x77e0e0f107c3cfcc

def z751 : W := mkw 0x06f7b36d80000000 0x00def66db0000000 0xc0ffff7fc0000003 0xb81fffeff8000000

def z752 : W := mkw 0x080848127312deed 0xa10109024e625bdd 0x180000003111fffc 0x0300000006223fff

def z753 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7fff8f03fff8007 0xfeffff1e07fff000

def z754 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe0ffffffc0ee7003 0xfc1ffffff81dce00

def z755 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0xe7fff8ffceee0003 0xfcffff1ff9ddc000

def z756 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0xefffffffc0fe7067 0xfdfffffff81fce0c

def z757 : W := mkw 0x000848127132b7fd 0xe00109024e2656ff 0x180000003111fffc 0x0300000006223fff

def z758 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff8dff6ffe07f86 0xffff1bfedffc0ff0

def z759 : W := mkw 0x0ff7b7ed86084800 0x01fef6fdb0c10900 0xc7ffffffce000003 0xf8fffffff9c00000

def z760 : W := mkw 0x106b6b5b7bf7ffff 0xe20d6d6b6f7effff 0xf8e727493fffffff 0xbf1ce4e927ffffff

def z761 : W := mkw 0x15b80ef06ba0ed8e 0x22b701de0d741db1 0xfff8ffffffe1ff9f 0xffff1ffffffc3ff3

def z762 : W := mkw 0x20084812755d86ac 0xa40109024eabb0d5 0x18000000311f8ffc 0x030000000623f1ff

def z763 : W := mkw 0x0304c48216184a20 0x8060989042c30944 0xbf07c78e3e1e7e67 0x77e0f8f1c7c3cfcc

def z764 : W := mkw 0x07f7b7ed80471051 0x40fef6fdb008e20a 0xcfffffffc11f81ff 0xf9fffffff823f03f

def z765 : W := mkw 0x26def801bddd8000 0x04dbdf0037bbb000 0xf7fff801ffff8005 0xfeffff003ffff000

def z766 : W := mkw 0x0b66e6c7167d6b30 0xc16cdcd8e2cfad66 0x57e0e0c73fe18f98 0xcafc1c18e7fc31f3

def z767 : W := mkw 0x36def8303ddd8486 0x06dbdf0607bbb090 0xf7fff8303fff8005 0xfeffff0607fff000

def z768 : W := mkw 0x1ebdc37e3dba37e7 0x83d7b86fc7b746fc 0x40ffc07e01fe01e1 0x881ff80fc03fc03c

def z769 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff8c7fe3fe07f87 0xffff18ffc7fc0ff0

def z770 : W := mkw 0x10284a527bb0efae 0xa205094a4f761df5 0xf8e027493ff1ffff 0xbf1c04e927fe3fff

def z771 : W := mkw 0x07f7b7ed82025841 0x00fef6fdb0404b08 0xfffffffffe1e7e67 0xffffffffffc3cfcc

def z772 : W := mkw 0x07f7b7ed80652110 0x40fef6fdb00ca422 0xe7ffffffc1ff819f 0xfcfffffff83ff033

def z773 : W := mkw 0x2008481279d586ac 0xa40109024f3ab0d5 0x1800000031f18ffc 0x03000000063e31ff

def z774 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe8e727ffc1fff1ff 0xbd1ce4fff83ffe3f

def z775 : W := mkw 0x07d6b4a480000000 0x00fad69490000000 0x47ffd8b6c0000000 0x68fffb16d8000000

def z776 : W := mkw 0x15b006e00aa06902 0x02b600dc01540d20 0xfff807f03ee07e06 0xffff00fe07dc0fc0

def z777 : W := mkw 0x069cc8003d988000 0x00d3990007b31000 0xf7fff8003fff8005 0xfeffff0007fff000

def z778 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0x3707c78e3e1e7e61 0x66e0f8f1c7c3cfcc

def z779 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xffe007403fe07f86 0xbffc00e807fc0ff0

def z780 : W := mkw 0x0ff7b7ed840a1041 0x01fef6fdb0814208 0xc7ffffffc00e0003 0xf8fffffff801c000

def z781 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xc7ffffffc1118007 0xf8fffffff8223000

def z782 : W := mkw 0x0490000000000000 0x0092000000000000 0xc7f8f8ffc0000003 0xf8ff1f1ff8000000

def z783 : W := mkw 0x04f2326180000000 0x009e464c30000000 0x40f8f87fc0000001 0x881f1f0ff8000000

def z784 : W := mkw 0x27d6b4a48ccd0000 0x04fad6949199a000 0x67ffd8b6ceee0000 0x6cfffb16d9ddc000

def z785 : W := mkw 0x14b802502ba06d86 0x0297004a05740db0 0xfff807403fe07f86 0xffff00e807fc0ff0

def z786 : W := mkw 0x26def8103ddd8484 0x04dbdf0207bbb090 0xf7fff8703fff8185 0xfeffff0e07fff030

def z787 : W := mkw 0x07d7b58c00000000 0x00faf6b180000000 0xc7ffffffc0000003 0xf8fffffff8000000

def z788 : W := mkw 0x04d2200008c50000 0x009a44000118a000 0x67e700000eee0000 0x2cfce00001ddc000

def z789 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff807f03ff1fffe 0xffff00fe07fe3fff

def z790 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe8ff3f79c1fff1ff 0xbd1fe7ef383ffe3f

def z791 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff807003fe07f84 0xffff00e007fc0ff0

def z792 : W := mkw 0x26deb8002dcd8000 0x04dbd70005b9b000 0xf7ff38003fef8004 0xfeffe70007fdf000

def z793 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0x3f07c70e3e1e7e65 0x27e0f8e1c7c3cfcc

def z794 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xfffff8803fff8e07 0xffffff1007fff1c0

def z795 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7fff8b6ffff8005 0xfeffff16dffff000

def z796 : W := mkw 0x26d6b0124ccd06ac 0xa4dad6024999a0d5 0x6fe700ffceee0ffa 0x2dfce01ff9ddc1ff

def z797 : W := mkw 0x05b006e002206900 0x00b600dc00440d20 0xfff807f03fe07f86 0xffff00fe07fc0ff0

def z798 : W := mkw 0x34fa3a71a9e5a586 0x069f474e353cb4b0 0x40f83871c1e18180 0x881f070e383c3030

def z799 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018f8bfc0000001 0x40031f17f8000000

def z800 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xfffff8493fff8fff 0xffffff0927fff1ff

def z801 : W := mkw 0x15b816f0aba06d86 0x02b702de15740db0 0xfff81ff0ffe07f86 0xffff03fe1ffc0ff0

def z802 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0x40ffffffc0000003 0x881ffffff8000000

def z803 : W := mkw 0x17f7b7ed88a02102 0x02fef6fdb1140420 0xc7ffffffc0e00003 0xf8fffffff81c0000

def z804 : W := mkw 0x112107e902227953 0x422420fd20444f2a 0x08000749000071fa 0x010000e920000e3f

def z805 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0x370707003e0e7e00 0x26e0e0e007c1cfc0

def z806 : W := mkw 0x112107f802227dc7 0x022420ff00444fb8 0x080007f800007fe2 0x010000ff00000ffc

def z807 : W := mkw 0x012107ed80000000 0x002420fdb0000000 0x0018dfffc0000002 0x40031bfff8000000

def z808 : W := mkw 0x07f7b7ed82206900 0x00fef6fdb0440d20 0xffffffffffe07f87 0xfffffffffffc0ff0

def z809 : W := mkw 0x0267b34d80000000 0x004cf669b0000000 0xc0ffffffc0000003 0xf81ffffff8000000

def z810 : W := mkw 0x06f7b34900000000 0x00def66920000000 0xc7ffffffc0000003 0xf8fffffff8000000

def z811 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0x77ffd8003fff8004 0x6efffb0007fff000

def z812 : W := mkw 0x26def8103ddd8484 0x04dbdf0207bbb090 0xfffff8003fff8f85 0xffffff0007fff1f0

def z813 : W := mkw 0x26deb8002dcd8000 0x04dbd70005b9b000 0xe7ff38000fff8005 0xbcffe70001fff000

def z814 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0xe7fff8000fff8005 0xfcffff0001fff000

def z815 : W := mkw 0x17f7b7ed8ae77953 0x42fef6fdb15cef2a 0x67e707000eee7000 0x2cfce0e001ddce00

def z816 : W := mkw 0x079494a480673151 0x40f29294900ce62a 0x2f18d8b6c1fff1fc 0x45e31b16d83ffe3f

def z817 : W := mkw 0x26def8107ddd848c 0x24dbdf020fbbb091 0xf7fff8ffffff819f 0xfeffff1ffffff033

def z818 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xc7ffdfbec0000003 0x78fffbf7d8000000

def z819 : W := mkw 0x059004800a804800 0x00b2009001500900 0xffe007803ee07e06 0x7ffc00f007dc0fc0

def z820 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xb707c78e3e0e7e03 0x76e0f8f1c7c1cfc0

def z821 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7e7c0003fff8005 0x7efcf80007fff000

def z822 : W := mkw 0x07f6b6e000000000 0x00fed6dc00000000 0xc7ffffffc0000003 0xf8fffffff8000000

def z823 : W := mkw 0x012806d023206d84 0x002500da04640db0 0xfff807f03fe07f86 0xffff00fe07fc0ff0

def z824 : W := mkw 0x0b05c5ae961a5a61 0x8160b8b5d2c34b4c 0xbf07c7befe1e7e67 0x77e0f8f7dfc3cfcc

def z825 : W := mkw 0x0000000000000000 0x0000000000000000 0x9818f8fff0000e07 0xd3031f1ffe0001c0

def z826 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff8fff03fe07f87 0xffff1ffe07fc0ff0

def z827 : W := mkw 0x079494a480000000 0x00f2929490000000 0x0718f8f7c0000000 0xc0e31f1ef8000000

def z828 : W := mkw 0x26deb0102dcd0484 0x04dbd60205b9a090 0xffff00f03fee0f86 0xffffe01e07fdc1f0

def z829 : W := mkw 0x07f7b7ed80202100 0x00fef6fdb0040420 0xc7ffffffc1e00183 0xf8fffffff83c0030

def z830 : W := mkw 0x07f7b7ed80223151 0x40fef6fdb004462a 0xcfffffffc111f1ff 0xf9fffffff8223e3f

def z831 : W := mkw 0x08084812777ffffd 0xe10109024eefffff 0x380000003ffffffc 0x0700000007ffffff

def z832 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0x68e7074901fff1fe 0x2d1ce0e9203ffe3f

def z833 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xf8e727c931ffffff 0xff1ce4f9263fffff

def z834 : W := mkw 0x0b05c58e561a5a69 0xa160b8b1cac34b4d 0xbf07c78ffe1e7e7f 0x77e0f8f1ffc3cfcf

def z835 : W := mkw 0x06d6b00000000000 0x00dad60000000000 0xc7fff8b6c0000001 0xf8ffff16d8000000

def z836 : W := mkw 0x26def8107ddd848c 0x24dbdf020fbbb091 0xf7fff830ffff8005 0xfeffff061ffff000

def z837 : W := mkw 0x26deb0002dcd0000 0x04dbd60005b9a000 0xf7fff8003fee0005 0xfeffff0007fdc000

def z838 : W := mkw 0x2f9cdc967f98ceac 0xa5f39b92cff319d5 0x1718d8b6fe000e00 0x42e31b16dfc001c0

def z839 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0x7ff807b03fe07f84 0x6fff00f607fc0ff0

def z840 : W := mkw 0x000848127175a7bc 0xe00109024e2eb4f7 0x1800000031f18ffc 0x03000000063e31ff

def z841 : W := mkw 0x00084812799086ac 0xa00109024f3210d5 0x380000003ff18ffc 0x0700000007fe31ff

def z842 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7fff8493fff8007 0xfeffff0927fff000

def z843 : W := mkw 0x0042200000450000 0x000844000008a000 0xe0fff8ffc1ff8007 0xfc1fff1ff83ff000

def z844 : W := mkw 0x26deb8002dcd8000 0x04dbd70005b9b000 0xe7fff8000fef8001 0xfcffff0001fdf000

def z845 : W := mkw 0x06f7b36d80673151 0x40def66db00ce62a 0x40fff87fc1ff81f9 0x881fff0ff83ff03f

def z846 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7fff88e3fff8007 0xfeffff11c7fff000

def z847 : W := mkw 0x0101458a12125a61 0x802028b142424b4c 0xbf07c78e3e1e7e67 0x77e0f8f1c7c3cfcc

def z848 : W := mkw 0x17f7b7ed82206902 0x02fef6fdb0440d20 0xc7ffffffc0007003 0xf8fffffff8000e00

def z849 : W := mkw 0x0100048000000000 0x0020009000000000 0x8718ffffc0000003 0xf0e31ffff8000000

def z850 : W := mkw 0x26fffb493dffb151 0x44dfff6927bff62a 0xfffffffffffff1ff 0xfffffffffffffe3f

def z851 : W := mkw 0x0809491a771adeed 0xa10129234ee35bdd 0xb80727493f1fffff 0xb700e4e927e3ffff

def z852 : W := mkw 0x379cdcb27f98ceae 0xa6f39b964ff319d5 0x1718d8b6fe000e00 0x42e31b16dfc001c0

def z853 : W := mkw 0x07b587ec00000000 0x00f6b0fd80000000 0xc7ffffffc0000003 0xf8fffffff8000000

def z854 : W := mkw 0x016327ed80000000 0x002c64fdb0000000 0xc0ffffffc0000003 0xf81ffffff8000000

def z855 : W := mkw 0x0ff7b7ed860a5841 0x01fef6fdb0c14b08 0xfffffffffe0e7e07 0xffffffffffc1cfc0

def z856 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x9800008031118ffe 0x53000010062231ff

def z857 : W := mkw 0x059004a000000000 0x00b2009400000000 0x0718d8b6c0000000 0x40e31b16d8000000

def z858 : W := mkw 0x26def804bddd8000 0x04dbdf0097bbb000 0xf7fff806ffff8005 0xfeffff00dffff000

def z859 : W := mkw 0x0b05858c060a5841 0x0160b0b180c14b08 0xbf07c78e3e0e7e07 0x77e0f8f1c7c1cfc0

def z860 : W := mkw 0x24da68003ddd8000 0x049b4d0007bbb000 0xf7ff20003fff8005 0xfeffe40007fff000

def z861 : W := mkw 0x192107ff02227ff7 0xc32420ffe0444ffe 0x080007ff00007ffa 0x010000ffe0000fff

def z862 : W := mkw 0x15db25b92bc75cd7 0x42bb64b72578eb9a 0x171f20b93e1f8e79 0x42e3e41727c3f1cf

def z863 : W := mkw 0x0694902480000000 0x00d2920490000000 0x0018d836c0000000 0x00031b06d8000000

def z864 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf07c7ce3f1e7fe7 0xf7e0f8f9c7e3cffc

def z865 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf0707083e1e7e67 0x37e0e0e107c3cfcc

def z866 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe8e7270001fff1fd 0xbd1ce4e0003ffe3f

def z867 : W := mkw 0x2ff7b7ed8ecf5841 0x05fef6fdb1d9eb08 0xe7ffffffceee7003 0xfcfffffff9ddce00

def z868 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0x3f07c7863e1e7e64 0x67e0f8f0c7c3cfcc

def z869 : W := mkw 0x26bddb493dbab151 0x44d7bb6927b7562a 0x1f18df493e0071fa 0x43e31be927c00e3f

def z870 : W := mkw 0x21294fedbddd8000 0x042529fdb7bbb000 0x300007ffffff8006 0x060000fffffff000

def z871 : W := mkw 0x0042300180000000 0x0008460030000000 0x8018f8ffc0000003 0xd0031f1ff8000000

def z872 : W := mkw 0x0062224000673151 0x400c4448000ce62a 0xe8e7274001fff1ff 0xbd1ce4e8003ffe3f

def z873 : W := mkw 0x092107cd02227951 0x412420f9a0444f2a 0x0000070000007000 0x000000e000000e00

def z874 : W := mkw 0x0000400210100220 0x8000080042020044 0x9818f8fff1118fff 0xd3031f1ffe2231ff

def z875 : W := mkw 0x00080812610086ac 0xa00101024c2010d5 0x8818f8ffc1018ffb 0xd1031f1ff82031ff

def z876 : W := mkw 0x07f7b7ed80202110 0x40fef6fdb0040422 0xc7ffffffc000019b 0xf8fffffff8000033

def z877 : W := mkw 0x17f7b7ed8ae77953 0x42fef6fdb15cef2a 0xefffffffcffff1ff 0xfdfffffff9fffe3f

def z878 : W := mkw 0x06dee0003ddd0000 0x00dbdc0007bba000 0xf7ffe0003fff8005 0xfefffc0007fff000

def z879 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf07c7cf3e1e7fff 0x77e0f8f9e7c3cfff

def z880 : W := mkw 0x26deb0002dcd0000 0x04dbd60005b9a000 0xf7ff20003fff8005 0xfeffe40007fff000

def z881 : W := mkw 0x0043210900471051 0x400864212008e20a 0x0007f80fc01f8079 0x0000ff01f803f00f

def z882 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe8e7070801fff1ff 0x3d1ce0e1003ffe3f

def z883 : W := mkw 0x100848127b90ceae 0xa20109024f7219d5 0x180000003f118ffc 0x0300000007e231ff

def z884 : W := mkw 0x26def8023ddd8220 0x84dbdf0047bbb044 0xfffff8ffffff8e67 0xffffff1ffffff1cc

def z885 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff827f93fe07f87 0xffff04ff27fc0ff0

def z886 : W := mkw 0x0b05cd8e161ada61 0x8160b9b1c2c35b4c 0xbf07ff8e3e1ffe67 0x77e0fff1c7c3ffcc

def z887 : W := mkw 0x06deb00029c50000 0x00dbd6000538a000 0xf7fff8003fff8005 0xfeffff0007fff000

def z888 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xf7fff8bfffff8e7d 0xfeffff17fffff1cf

def z889 : W := mkw 0x15b80ef06ba0ed8e 0x22b701de0d741db1 0xfff81ff0ffe07f86 0xffff03fe1ffc0ff0

def z890 : W := mkw 0x0063234d80673151 0x400c6469b00ce62a 0xe8e7274fc1fff1ff 0xbd1ce4e9f83ffe3f

def z891 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1800200931118ffd 0x03000401262231ff

def z892 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe8ffff4901fff1ff 0xfd1fffe9203ffe3f

def z893 : W := mkw 0x204a68127ddd86ac 0xa4094d024fbbb0d5 0xf8e720493fff8fff 0xbf1ce40927fff1ff

def z894 : W := mkw 0x0062224100652110 0x400c4448200ca422 0x40f83871c1e18198 0x881f070e383c3033

def z895 : W := mkw 0x300848127ffdefae 0xa60109024fffbdf5 0x380000003ffffffc 0x0700000007ffffff

def z896 : W := mkw 0x1008481279b0a7ae 0xa20109024f3614f5 0x1800000031f18ffc 0x03000000063e31ff

def z897 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0xe7ffffffc1fff007 0xfcfffffff83ffe00

def z898 : W := mkw 0x0304848400000000 0x0060909080000000 0x8718f8ffc0000003 0xd0e31f1ff8000000

def z899 : W := mkw 0x26d6f8025cdd8228 0xa4dadf004b9bb045 0x67e7f80fceff8079 0x2cfcff01f9dff00f

def z900 : W := mkw 0x06f6b26180000000 0x00ded64c30000000 0xc7fff8ffc0000003 0xf8ffff1ff8000000

def z901 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf1fffffff1fffff 0xf7e3ffffffe3ffff

def z902 : W := mkw 0x0043210800673151 0x40086421000ce62a 0xe8e7270801fff1ff 0xbd1ce4e1003ffe3f

def z903 : W := mkw 0x024ee812755d86ac 0xa049dd024eabb0d5 0xfffff8ffffff8fff 0xffffff1ffffff1ff

def z904 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xf7fff8ffffff8e07 0xfeffff1ffffff1c0

def z905 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0x7ff807f03ee07f82 0x6fff00fe07dc0ff0

def z906 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0x071fffffc0000003 0x40e3fffff8000000

def z907 : W := mkw 0x0b05c58f161a5a71 0xc160b8b1e2c34b4e 0xbf07c78f3e1e7e7f 0x77e0f8f1e7c3cfcf

def z908 : W := mkw 0x206b6b5b7dffb7fd 0xe40d6d6b6fbff6ff 0xf8e727493fffffff 0xbf1ce4e927ffffff

def z909 : W := mkw 0x200848127d9886ac 0xa40109024fb310d5 0x100000003e000e00 0x0200000007c001c0

def z910 : W := mkw 0x07d7b5ad80000000 0x00faf6b5b0000000 0x871fffbfc0000003 0x70e3fff7f8000000

def z911 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7ff00003fff8004 0xfeffe00007fff000

def z912 : W := mkw 0x0204900480000000 0x0040920090000000 0x0018d8b6c0000000 0x40031b16d8000000

def z913 : W := mkw 0x0694900000000000 0x00d2920000000000 0x0718d8b6c0000000 0x40e31b16d8000000

def z914 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0x77e700003eee0000 0x2efce00007ddc000

def z915 : W := mkw 0x0000000000000000 0x0000000000000000 0x8018d8f6c0000002 0xd0031b1ed8000000

def z916 : W := mkw 0x04f3336980673151 0x409e666d300ce62a 0xe8ffffffc1fff1ff 0xfd1ffffff83ffe3f

def z917 : W := mkw 0x06f7b36d80000000 0x00def66db0000000 0xc7fff87fc0000001 0xf8ffff0ff8000000

def z918 : W := mkw 0x04b0026000000000 0x0096004c00000000 0xc0f8f8ffc0000003 0xd81f1f1ff8000000

def z919 : W := mkw 0x15fb27f92be77dd7 0x42bf64ff257cefba 0xffffffffffffffff 0xffffffffffffffff

def z920 : W := mkw 0x192947fe33327fe7 0x832528ffc6664ffc 0x9818c7fe31107fe7 0xd30318ffc6220ffc

def z921 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xcfffffffc1000187 0xf9fffffff8200030

def z922 : W := mkw 0x07f6b6e580000000 0x00fed6dcb0000000 0xc7f8fff7c0000002 0xf8ff1ffef8000000

def z923 : W := mkw 0x159804b02b804c86 0x02b3009605700990 0xfff807b03fe07e06 0xffff00f607fc0fc0

def z924 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7fff8093fff807d 0xfeffff0127fff00f

def z925 : W := mkw 0x079494a480000000 0x00f2929490000000 0x0718f8bfc0000001 0x40e31f17f8000000

def z926 : W := mkw 0x04b8025029a02584 0x0097004a053404b0 0xfff807f03fe07f86 0xffff00fe07fc0ff0

def z927 : W := mkw 0x07f7b7ed84080000 0x00fef6fdb0810000 0xe7ffffffce0e0003 0xfcfffffff9c1c000

def z928 : W := mkw 0x0a05c10a161a5a61 0x8140b82142c34b4c 0xbf07c7083e1e7e67 0x77e0f8e107c3cfcc

def z929 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0x48e7274901fff1fb 0x891ce4e9203ffe3f

def z930 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe8ff27f901fff1ff 0xfd1fe4ff203ffe3f

def z931 : W := mkw 0x06d6b00000450000 0x00dad6000008a000 0xeffff8ffc1ff81ff 0xfdffff1ff83ff03f

def z932 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0x7fe007f03fe07f86 0x2ffc00fe07fc0ff0

def z933 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0x67e7f8000eee0001 0x2cfcff0001ddc000

def z934 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0x57fff8003fff8001 0xcaffff0007fff000

def z935 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018f87fc0000001 0x80031f0ff8000000

def z936 : W := mkw 0x0b04c482161a5a61 0x8160989042c34b4c 0xbf07c7803e1e7e67 0x77e0f8f007c3cfcc

def z937 : W := mkw 0x05b806e02b804800 0x00b700dc05700900 0xfff807f03fe07e06 0xffff00fe07fc0fc0

def z938 : W := mkw 0x15b806f12ba06d96 0x42b700de25740db2 0xfff807f13fe07f9e 0xffff00fe27fc0ff3

def z939 : W := mkw 0x0063334980673151 0x400c6669300ce62a 0xe8e73f49c1fff1ff 0xbd1ce7e9383ffe3f

def z940 : W := mkw 0x0062224100000000 0x000c444820000000 0xc0f8f8ffc0000003 0xd81f1f1ff8000000

def z941 : W := mkw 0x15b006e00aa06902 0x02b600dc01540d20 0x77e007803ee07e00 0x6efc00f007dc0fc0

def z942 : W := mkw 0x26def8103ddd8484 0x04dbdf0207bbb090 0xfffff8f93fff8fff 0xffffff1f27fff1ff

def z943 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0x47fff8ffc0000001 0xc8ffff1ff8000000

def z944 : W := mkw 0x0b0dcd9e771adeed 0xa161b9b3cee35bdd 0x3f0707003f1ffffc 0x27e0e0e007e3ffff

def z945 : W := mkw 0x059804902b804c84 0x00b3009205700990 0xfff807f03fe07f86 0xffff00fe07fc0ff0

def z946 : W := mkw 0x07d7b5ad80000000 0x00faf6b5b0000000 0xc7fff8bfc0000001 0xf8ffff17f8000000

def z947 : W := mkw 0x010004a480000000 0x0020009490000000 0x0018d8b6c0000000 0x40031b16d8000000

def z948 : W := mkw 0x06d7b10d80000000 0x00daf621b0000000 0xc7fff8ffc0000003 0xf8ffff1ff8000000

def z949 : W := mkw 0x0367b7ed80000000 0x006cf6fdb0000000 0x801fffffc0000003 0xd003fffff8000000

def z950 : W := mkw 0x06d6f000145d0000 0x00dade00028ba000 0xf7fff8003fff8005 0xfeffff0007fff000

def z951 : W := mkw 0x04da681279d586ac 0xa09b4d024f3ab0d5 0xfffff8ffffff8fff 0xffffff1ffffff1ff

def z952 : W := mkw 0x15b04ee25ab0eb2a 0xa2b609dc4b561d65 0x67e0ff0fcef1f079 0x2cfc1fe1f9de3e0f

def z953 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0xe7e700000fee0004 0xbcfce00001fdc000

def z954 : W := mkw 0x07f7b7ed80471051 0x40fef6fdb008e20a 0xe7ffffffc1ff807f 0xfcfffffff83ff00f

def z955 : W := mkw 0x006b6b5b7177b7fd 0xe00d6d6b6e2ef6ff 0x78e7070031fffffc 0x2f1ce0e0063fffff

def z956 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x00000000011181f8 0x000000000022303f

def z957 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0x67e720000fef8000 0xacfce40001fdf000

def z958 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0x67fff8000fff8001 0xacffff0001fff000

def z959 : W := mkw 0x05b006e000202100 0x00b600dc00040420 0xeff8ffffc1f1f1ff 0xfdff1ffff83e3e3f

def z960 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0xe7e700000efe0005 0x3cfce00001dfc000

def z961 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0x67e720000eff8001 0x2cfce40001dff000

def z962 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xffe007803fe07f86 0x7ffc00f007fc0ff0

def z963 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1800000030100e64 0x03000000060201cc

def z964 : W := mkw 0x07d6b4a480000000 0x00fad69490000000 0xc7fff8ffc0000003 0xf8ffff1ff8000000

def z965 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf07c7003e1e7e65 0x77e0f8e007c3cfcc

def z966 : W := mkw 0x26def8027ddd8228 0xa4dbdf004fbbb045 0xf7fff806ffff8005 0xfeffff00dffff000

def z967 : W := mkw 0x07d6b4a480000000 0x00fad69490000000 0x071ff8b6c0000001 0x40e3ff16d8000000

def z968 : W := mkw 0x15b006e00aa06902 0x02b600dc01540d20 0xe7f8ffffcee07003 0xfcff1ffff9dc0e00

def z969 : W := mkw 0x080848127718ceac 0xa10109024ee319d5 0x100000003e000e00 0x0200000007c001c0

def z970 : W := mkw 0x0247b10d80000000 0x0048f621b0000000 0x001ff87fc0000001 0x8003ff0ff8000000

def z971 : W := mkw 0x26d6b8000ccd8000 0x04dad7000199b000 0x67e738000eef8000 0x2cfce70001ddf000

def z972 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0xcfffffffc1e1f1fb 0xf9fffffff83c3e3f

def z973 : W := mkw 0x079595ad80000000 0x00f2b2b5b0000000 0x0718d8bfc0000000 0x40e31b17f8000000

def z974 : W := mkw 0x159804b02b804c86 0x02b3009605700990 0x170000003e000e00 0x02e0000007c001c0

def z975 : W := mkw 0x0b05858c060a5841 0x0160b0b180c14b08 0xa71fffffce0e7003 0xf4e3fffff9c1ce00

def z976 : W := mkw 0x0205c10a141a1261 0x8040b8214283424c 0xbf07c78e3e1e7e67 0x77e0f8f1c7c3cfcc

def z977 : W := mkw 0x0063236980673151 0x400c646d300ce62a 0xe8e72779c1fff1ff 0xbd1ce4ef383ffe3f

def z978 : W := mkw 0x192107fe42227fef 0xa32420ffc8444ffd 0x080007ffc0007ffa 0x010000fff8000fff

def z979 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf07e78f3e1ffe7f 0x77e0fcf1e7c3ffcf

def z980 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xffe727493ffff1ff 0xfffce4e927fffe3f

def z981 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xf7fff8003fff8e05 0xfeffff0007fff1c0

def z982 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf07ff8ffe1e7e67 0x77e0fff1ffc3cfcc

def z983 : W := mkw 0x0694c0001c980000 0x00d2980003930000 0xf7e7c0003efe0005 0x7efcf80007dfc000

def z984 : W := mkw 0x0b05cd8e561ada69 0xa160b9b1cac35b4d 0xbf1ffffffe1ffe7f 0xf7e3ffffffc3ffcf

def z985 : W := mkw 0x27f7b7ed8cef3151 0x44fef6fdb19de62a 0xe7ffffffceee7003 0xfcfffffff9ddce00

def z986 : W := mkw 0x27f7b7ed8c880000 0x04fef6fdb1910000 0xc7ffffffce000003 0xf8fffffff9c00000

def z987 : W := mkw 0x0ff7b7ed82025841 0x01fef6fdb0404b08 0xc7ffffffc0007003 0xf8fffffff8000e00

def z988 : W := mkw 0x11294ffb7332ffff 0xe22529ff6e665fff 0x9818fffff111ffff 0xd3031ffffe223fff

def z989 : W := mkw 0x26def8027ddd8228 0xa4dbdf004fbbb045 0xf7fff8003fff807d 0xfeffff0007fff00f

def z990 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x9800004031118ffe 0x93000008062231ff

def z991 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0x47ffdfffc0000002 0x68fffbfff8000000

def z992 : W := mkw 0x0b05c58f961a5a61 0x8160b8b1f2c34b4c 0xbf07c78ffe1e7e67 0x77e0f8f1ffc3cfcc

def z993 : W := mkw 0x07f7b7ed80652110 0x40fef6fdb00ca422 0xcfffffffc1f181ff 0xf9fffffff83e303f

def z994 : W := mkw 0x07b496e480202100 0x00f692dc90040420 0xeff8dff6c1e07186 0xfdff1bfed83c0e30

def z995 : W := mkw 0x26d6f0021cdd0220 0x84dade00439ba044 0xffe7c08e3efe0e67 0x7ffcf811c7dfc1cc

def z996 : W := mkw 0x112107fb42227fff 0xe22420ff68444fff 0x080007ffc0007ffa 0x010000fff8000fff

def z997 : W := mkw 0x07f7b7ed80021041 0x00fef6fdb0004208 0xefffffffc11ff1ff 0xfdfffffff823fe3f

def z998 : W := mkw 0x0043210800471041 0x000864210008e208 0xe8e7274901fff1ff 0xbd1ce4e9203ffe3f

def z999 : W := mkw 0x2247f90b545f9279 0xe448ff216a8bf24f 0x0007f80fc01f8079 0x0000ff01f803f00f

def z1000 : W := mkw 0x14fa3271a9e52596 0x429f464e353ca4b2 0x40f83871c1e18198 0x881f070e383c3033

def z1001 : W := mkw 0x124fb11daba06d86 0x0249f623b5740db0 0x3807f80fffe07f85 0x0700ff01fffc0ff0

def z1002 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1800000030000ff8 0x03000000060001ff

def z1003 : W := mkw 0x0008001021000484 0x0001000204200090 0x9818f8fff1118fff 0xd3031f1ffe2231ff

def z1004 : W := mkw 0x092107cd02227951 0x412420f9a0444f2a 0x08000749000071fa 0x010000e920000e3f

def z1005 : W := mkw 0x24fa3a5169e5a59c 0x649f474a2d3cb4b3 0x40f83871c1e18198 0x881f070e383c3033

def z1006 : W := mkw 0x07f6b6e580652110 0x40fed6dcb00ca422 0x47f8f8f7c1e18198 0xc8ff1f1ef83c3033

def z1007 : W := mkw 0x0246b00000000000 0x0048d60000000000 0x801ff8ffc0000003 0xd003ff1ff8000000

def z1008 : W := mkw 0x17f7b7ed8a804802 0x02fef6fdb1500900 0xc7ffffffce000003 0xf8fffffff9c00000

def z1009 : W := mkw 0x07f7b7ed80471051 0x40fef6fdb008e20a 0xc7ffffffc00e0003 0xf8fffffff801c000

def z1010 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7fff8003eee0001 0xfeffff0007ddc000

def z1011 : W := mkw 0x192107ff82227fe7 0x832420fff0444ffc 0x080007ffc0007fe2 0x010000fff8000ffc

def z1012 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0x67ff38000eee0000 0xacffe70001ddc000

def z1013 : W := mkw 0x07f7b7ed80450000 0x00fef6fdb008a000 0xc7ffffffc1e18003 0xf8fffffff83c3000

def z1014 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xfffff8003fff81fd 0xffffff0007fff03f

def z1015 : W := mkw 0x0347b58d80000000 0x0068f6b1b0000000 0x871fffffc0000003 0xf0e3fffff8000000

def z1016 : W := mkw 0x05b107ed80000000 0x00b620fdb0000000 0xc7f8ffffc0000003 0xf8ff1ffff8000000

def z1017 : W := mkw 0x0a47f10f945f1271 0xc148fe21f28be24e 0x0007f80fc01f8079 0x0000ff01f803f00f

def z1018 : W := mkw 0x00004812501086ac 0xa00009024a0210d5 0x8818f8ffc0118ffb 0xd1031f1ff80231ff

def z1019 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xc7ffffb6c0000001 0xf8fffff6d8000000

def z1020 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0xefffffffc1ee7187 0xfdfffffff83dce30

def z1021 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0x77ffd8b6feee0e00 0x6efffb16dfddc1c0

def z1022 : W := mkw 0x00294b5b7132b7fd 0xe005296b6e2656ff 0x180007493111fffe 0x030000e926223fff

def z1023 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0x67ffdfb6c0ee7000 0x6cfffbf6d81dce00

def z1024 : W := mkw 0x07d7b5ad80000000 0x00faf6b5b0000000 0x071fd8b6c0000000 0x40e3fb16d8000000

def z1025 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xf7fffffffe000007 0xfeffffffffc00000

def z1026 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0x77fff8003fef8000 0xeeffff0007fdf000

def z1027 : W := mkw 0x0000000000000000 0x0000000000000000 0x8018d8bec0000003 0x50031b17d8000000

def z1028 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0x68e7270901fff1fd 0x2d1ce4e1203ffe3f

def z1029 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0xf7e700003eee0004 0x7efce00007ddc000

def z1030 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf1fff8e3e1e7e67 0xf7e3fff1c7c3cfcc

def z1031 : W := mkw 0x07f6b6e580000000 0x00fed6dcb0000000 0x47f8d8b6c0000000 0x48ff1b16d8000000

def z1032 : W := mkw 0x06f7b34900673151 0x40def669200ce62a 0xefffffffc1fff1ff 0xfdfffffff83ffe3f

def z1033 : W := mkw 0x200848127d9886ac 0xa40109024fb310d5 0x9818f8ffff118fff 0xd3031f1fffe231ff

def z1034 : W := mkw 0x079494a480000000 0x00f2929490000000 0x871fd8b6c0000001 0x70e3fb16d8000000

def z1035 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0x77fff8003eff8001 0x6effff0007dff000

def z1036 : W := mkw 0x0000000000000000 0x0000000000000000 0x8818f8ffc1000187 0xd1031f1ff8200030

def z1037 : W := mkw 0x0901458a161a5a61 0x812028b142c34b4c 0xbf0707883e1e7e67 0x77e0e0f107c3cfcc

def z1038 : W := mkw 0x00084812715796fd 0xe00109024e2af2df 0x18000000311f8ffc 0x030000000623f1ff

def z1039 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xfffff8403fff8187 0xffffff0807fff030

def z1040 : W := mkw 0x0101058c00000000 0x002020b180000000 0x8018ffffc0000003 0xd0031ffff8000000

def z1041 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xf7f807f03ee07e02 0xfeff00fe07dc0fc0

def z1042 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0x68e7274101fff1fc 0xad1ce4e8203ffe3f

def z1043 : W := mkw 0x26def8107ddd848c 0x24dbdf020fbbb091 0xf7fff8003fff819d 0xfeffff0007fff033

def z1044 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe8e7ff4fc1fff1ff 0xbd1cffe9f83ffe3f

def z1045 : W := mkw 0x27f7b7ed88c50000 0x04fef6fdb118a000 0xc7ffffffc0e00003 0xf8fffffff81c0000

def z1046 : W := mkw 0x224ee8003ddd8000 0x0449dd0007bbb000 0xf7e7e0003fff8005 0xfefcfc0007fff000

def z1047 : W := mkw 0x04f3336980000000 0x009e666d30000000 0xc0ffffffc0000003 0xf81ffffff8000000

def z1048 : W := mkw 0x0001010800021041 0x0000202100004208 0xa81fffffc01e7067 0xf503fffff803ce0c

def z1049 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018d8ffc0000002 0x40031b1ff8000000

def z1050 : W := mkw 0x07b597ed80000000 0x00f6b2fdb0000000 0x0718dfb6c0000000 0x40e31bf6d8000000

def z1051 : W := mkw 0x07f7b7ed88800000 0x00fef6fdb1100000 0xe7ffffffcee00003 0xfcfffffff9dc0000

def z1052 : W := mkw 0x14fa227129e52596 0x429f444e253ca4b2 0x40f8007001e00180 0x881f000e003c0030

def z1053 : W := mkw 0x069c80002d880000 0x00d3900005b10000 0xf7ff00003fee0004 0xfeffe00007fdc000

def z1054 : W := mkw 0x15b806f4aba06d86 0x02b700de95740db0 0xfff807f6ffe07f86 0xffff00fedffc0ff0

def z1055 : W := mkw 0x2a47f90e545f9269 0xa548ff21ca8bf24d 0x0007f80fc01f8079 0x0000ff01f803f00f

def z1056 : W := mkw 0x07f7b7ed80450010 0x40fef6fdb008a002 0xc7ffffffc001801b 0xf8fffffff8003003

def z1057 : W := mkw 0x07f7b7ed80021051 0x40fef6fdb000420a 0xc7ffffffc000007b 0xf8fffffff800000f

def z1058 : W := mkw 0x0b05858c060a5841 0x0160b0b180c14b08 0x370707803e0e7e00 0x66e0e0f007c1cfc0

def z1059 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7fff871ffff8005 0xfeffff0e3ffff000

def z1060 : W := mkw 0x0b05cd8e561ada69 0xa160b9b1cac35b4d 0xbf07c78e3e1ffe7f 0x77e0f8f1c7c3ffcf

def z1061 : W := mkw 0x07b597ed80000000 0x00f6b2fdb0000000 0x871fdfffc0000003 0x70e3fbfff8000000

def z1062 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1818f8fff1018ffa 0xc3031f1ffe2031ff

def z1063 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf07c7863e0e7e06 0x77e0f8f0c7c1cfc0

def z1064 : W := mkw 0x04f2326180652110 0x409e464c300ca422 0xc8f8f8ffc1f181ff 0xd91f1f1ff83e303f

def z1065 : W := mkw 0x06d7b12d80000000 0x00daf625b0000000 0x001ff83fc0000001 0x0003ff07f8000000

def z1066 : W := mkw 0x07f7b7ed80652110 0x40fef6fdb00ca422 0xefffffffc1e1f19f 0xfdfffffff83c3e33

def z1067 : W := mkw 0x07f7b7ed80223151 0x40fef6fdb004462a 0xefffffffc1e071ff 0xfdfffffff83c0e3f

def z1068 : W := mkw 0x0042200000000000 0x0008440000000000 0xc0fff8ffc0000003 0xf81fff1ff8000000

def z1069 : W := mkw 0x0100048002004800 0x0020009000400900 0xffe007803fe07e06 0xfffc00f007fc0fc0

def z1070 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf07e78e3f1ffe67 0xf7e0fcf1c7e3ffcc

def z1071 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xfffff871ffff8ffd 0xffffff0e3ffff1ff

def z1072 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xfffff8b6ffff8ffd 0xffffff16dffff1ff

def z1073 : W := mkw 0x0000000000000000 0x0000000000000000 0x8018f8ffc011807b 0xd0031f1ff802300f

def z1074 : W := mkw 0x07d6b4a480450000 0x00fad6949008a000 0xe7fff8b6c1ff8005 0xfcffff16d83ff000

def z1075 : W := mkw 0x012006e000000000 0x002400dc00000000 0x8018ffffc0000003 0xd0031ffff8000000

def z1076 : W := mkw 0x26def8023ddd8220 0x84dbdf0047bbb044 0xfffff8cf3fff8fff 0xffffff19e7fff1ff

def z1077 : W := mkw 0x06f6b26580000000 0x00ded64cb0000000 0x40f8f877c0000000 0x881f1f0ef8000000

def z1078 : W := mkw 0x07f7b7ed80223151 0x40fef6fdb004462a 0xc7ffffffc0007003 0xf8fffffff8000e00

def z1079 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff807ffffe07f86 0xffff00fffffc0ff0

def z1080 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xf7f807b03fe07e04 0xfeff00f607fc0fc0

def z1081 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf07e7cf3e1e7e67 0xf7e0fcf9e7c3cfcc

def z1082 : W := mkw 0x079595ac80000000 0x00f2b2b590000000 0x071fdfb6c0000000 0x60e3fbf6d8000000

def z1083 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0xe7ff00000eee0000 0xfcffe00001ddc000

def z1084 : W := mkw 0x37f7b7ed8eed6902 0x06fef6fdb1ddad20 0xe7ffffffceee7003 0xfcfffffff9ddce00

def z1085 : W := mkw 0x112006f002206d86 0x022400de00440db0 0xffe007f03fe07f86 0xfffc00fe07fc0ff0

def z1086 : W := mkw 0x0ff7b7ed866f7951 0x41fef6fdb0cdef2a 0x67e707000eee7000 0x2cfce0e001ddce00

def z1087 : W := mkw 0x100848127b90ceae 0xa20109024f7219d5 0x100000003e000e00 0x0200000007c001c0

def z1088 : W := mkw 0x07f7b7ed80021041 0x00fef6fdb0004208 0xc7ffffffc01e0063 0xf8fffffff803c00c

def z1089 : W := mkw 0x07f7b7ed80450000 0x00fef6fdb008a000 0xc7ffffffc01f8003 0xf8fffffff803f000

def z1090 : W := mkw 0x159804902ba06d86 0x02b3009205740db0 0xfff807803fe07f86 0xffff00f007fc0ff0

def z1091 : W := mkw 0x06f7b36d80000000 0x00def66db0000000 0xc0fff8ffc0000003 0xd81fff1ff8000000

def z1092 : W := mkw 0x07b496e480000000 0x00f692dc90000000 0x47f8dfb6c0000000 0x68ff1bf6d8000000

def z1093 : W := mkw 0x0062224000652100 0x000c4448000ca420 0xe8e7274901fff1ff 0xbd1ce4e9203ffe3f

def z1094 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0xf8f8f8fff1f18fff 0xff1f1f1ffe3e31ff

def z1095 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0xe7e7c0000eee0001 0x7cfcf80001ddc000

def z1096 : W := mkw 0x2a47f10e145f1261 0x8548fe21c28be24c 0x0007c00e001e0061 0x0000f801c003c00c

def z1097 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xfffff8f6ffff8f87 0xffffff1edffff1f0

def z1098 : W := mkw 0x07f7b7ed80223141 0x00fef6fdb0044628 0xefffffffc1fe71e7 0xfdfffffff83fce3c

def z1099 : W := mkw 0x07f7b7ed80652100 0x00fef6fdb00ca420 0xefffffffc1fff187 0xfdfffffff83ffe30

def z1100 : W := mkw 0x024ee800355d8000 0x0049dd0006abb000 0xf7fff8003fff8005 0xfeffff0007fff000

def z1101 : W := mkw 0x079494a480000000 0x00f2929490000000 0x8718d8f6c0000002 0xd0e31b1ed8000000

def z1102 : W := mkw 0x0ff7b7ed860a5841 0x01fef6fdb0c14b08 0xefffffffce1e7067 0xfdfffffff9c3ce0c

def z1103 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf07c78e3f1fffff 0x77e0f8f1c7e3ffff

def z1104 : W := mkw 0x0101058802025841 0x002020b100404b08 0xbf0707803e0e7e06 0x77e0e0f007c1cfc0

def z1105 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1000000031118e04 0x02000000062231c0

def z1106 : W := mkw 0x07f7b7ed82004800 0x00fef6fdb0400900 0xcfffffffc0007e03 0xf9fffffff8000fc0

def z1107 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0x60e7274901fff1f9 0xac1ce4e9203ffe3f

def z1108 : W := mkw 0x280848127fdfdeed 0xa50109024ffbfbdd 0x380000003ffffffc 0x0700000007ffffff

def z1109 : W := mkw 0x112107fd82227dd7 0x422420ffb0444fba 0x080007ffc0007ffa 0x010000fff8000fff

def z1110 : W := mkw 0x26def8027ddd8228 0xa4dbdf004fbbb045 0xf7fff8ffffff807f 0xfeffff1ffffff00f

def z1111 : W := mkw 0x0247b10d80000000 0x0048f621b0000000 0x001ff8bfc0000001 0x4003ff17f8000000

def z1112 : W := mkw 0x192107ee02227b63 0x832420fdc0444f6c 0x0800078e00007e62 0x010000f1c0000fcc

def z1113 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xe7ffffffc1e00007 0xfcfffffff83c0000

def z1114 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf0707803e1e7e66 0x77e0e0f007c3cfcc

def z1115 : W := mkw 0x07d7b5ac80000000 0x00faf6b590000000 0xc7ffffbec0000003 0xf8fffff7d8000000

def z1116 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1018f8fff1118ff9 0xc2031f1ffe2231ff

def z1117 : W := mkw 0x26def0003ddd0000 0x04dbde0007bba000 0xf7ffc0003ffe0005 0xfefff80007ffc000

def z1118 : W := mkw 0x069cc0123d9806a4 0x80d3980247b300d4 0xffffc0fe3ffe0fe7 0xfffff81fc7ffc1fc

def z1119 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x9800000831118fff 0x13000001062231ff

def z1120 : W := mkw 0x07f7b7ed80450000 0x00fef6fdb008a000 0xe7ffffffc0ee0003 0xfcfffffff81dc000

def z1121 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0x5ff807f03fe07f82 0xcbff00fe07fc0ff0

def z1122 : W := mkw 0x26d6f0001cdd0000 0x04dade00039ba000 0xf7fff8003efe0005 0xfeffff0007dfc000

def z1123 : W := mkw 0x0b05cd8e561ada69 0xa160b9b1cac35b4d 0xbf07ffcfff1fffff 0xf7e0fff9ffe3ffff

def z1124 : W := mkw 0x07b597ed80000000 0x00f6b2fdb0000000 0x8718ffffc0000003 0xd0e31ffff8000000

def z1125 : W := mkw 0x07d6b4a580000000 0x00fad694b0000000 0x0718f8b7c0000000 0x40e31f16f8000000

def z1126 : W := mkw 0x26d6f8001cdd8000 0x04dadf00039bb000 0xe7fff8000eff8001 0xfcffff0001dff000

def z1127 : W := mkw 0x000848127130a7ac 0xa00109024e2614f5 0x3800000031f1fffc 0x07000000063e3fff

def z1128 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xc7ffffffc011807b 0xf8fffffff802300f

def z1129 : W := mkw 0x006b6b5b711086ac 0xa00d6d6b6e2210d5 0xd8e7274931118fff 0xbb1ce4e9262231ff

def z1130 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xffe7c78e3ffe7e67 0xfffcf8f1c7ffcfcc

def z1131 : W := mkw 0x059004a000000000 0x00b2009400000000 0x8718f8ffc0000003 0xd0e31f1ff8000000

def z1132 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xf7fff87fffff81fd 0xfeffff0ffffff03f

def z1133 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7ffd8003fee0004 0xfefffb0007fdc000

def z1134 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7ffd8003efe0005 0x7efffb0007dfc000

def z1135 : W := mkw 0x26def8027ddd8228 0xa4dbdf004fbbb045 0xfffff88fffff8e7f 0xffffff11fffff1cf

def z1136 : W := mkw 0x07f7b7ed80223151 0x40fef6fdb004462a 0xefffffffc01e71ff 0xfdfffffff803ce3f

def z1137 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff83ff1ffe07f86 0xffff07fe3ffc0ff0

def z1138 : W := mkw 0x0246e002145d0220 0x8048dc00428ba044 0xffe7e0cf3fff8fff 0xfffcfc19e7fff1ff

def z1139 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0x1f07c78e3e1e7e63 0x43e0f8f1c7c3cfcc

def z1140 : W := mkw 0x079595ac80000000 0x00f2b2b590000000 0x0718dfbec0000002 0x40e31bf7d8000000

def z1141 : W := mkw 0x0305858c00000000 0x0060b0b180000000 0x871fdfbec0000003 0x70e3fbf7d8000000

def z1142 : W := mkw 0x07f7b7ed80202100 0x00fef6fdb0040420 0xefffffffc1f1f1ff 0xfdfffffff83e3e3f

def z1143 : W := mkw 0x079494a480000000 0x00f2929490000000 0x8f18f8ffc11181ff 0xd1e31f1ff822303f

def z1144 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7fff80fffff8005 0xfeffff01fffff000

def z1145 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0xcfffffffc01ff1fb 0xf9fffffff803fe3f

def z1146 : W := mkw 0x0ff7b7ed866f7951 0x41fef6fdb0cdef2a 0xefffffffcffff1ff 0xfdfffffff9fffe3f

def z1147 : W := mkw 0x179494a48a804802 0x02f2929491500900 0x0718d8b6ce000000 0x40e31b16d9c00000

def z1148 : W := mkw 0x34fa327029e52586 0x069f464e053ca4b0 0x40f8007001e00180 0x881f000e003c0030

def z1149 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1000000031018f98 0x02000000062031f3

def z1150 : W := mkw 0x0490102080000000 0x0092020410000000 0x0018d8b6c0000000 0x40031b16d8000000

def z1151 : W := mkw 0x09294fdf7332fffd 0xe12529fbee665fff 0x9818fffff111ffff 0xd3031ffffe223fff

def z1152 : W := mkw 0x0009491a711296ed 0xa00129234e2252dd 0xb8070708311fffff 0x3700e0e10623ffff

def z1153 : W := mkw 0x15b80ef06ba0ed8e 0x22b701de0d741db1 0xfff83ff9fff1ffff 0xffff07ff3ffe3fff

def z1154 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xfffff80fffff8ffd 0xffffff01fffff1ff

def z1155 : W := mkw 0x1ff7b7ed8eaa7943 0x03fef6fdb1d54f28 0xe7ffffffceee7003 0xfcfffffff9ddce00

def z1156 : W := mkw 0x26def8023ddd8220 0x84dbdf0047bbb044 0xf7fff80e3fff8065 0xfeffff01c7fff00c

def z1157 : W := mkw 0x0305c58c16184800 0x0060b8b182c30900 0xbf07c78e3e1e7e07 0x77e0f8f1c7c3cfc0

def z1158 : W := mkw 0x04da680039d58000 0x009b4d00073ab000 0xf7fff8003fff8005 0xfeffff0007fff000

def z1159 : W := mkw 0x032587ed80000000 0x0064b0fdb0000000 0x871fffffc0000003 0xf0e3fffff8000000

def z1160 : W := mkw 0x0a47e10f145f1271 0xc148fc21e28be24e 0x0007c00e001e0061 0x0000f801c003c00c

def z1161 : W := mkw 0x0b04c48616184a20 0x81609890c2c30944 0x170000003e000e00 0x02e0000007c001c0

def z1162 : W := mkw 0x016327ed80673151 0x402c64fdb00ce62a 0xe8ffffffc1fff1ff 0xfd1ffffff83ffe3f

def z1163 : W := mkw 0x012107ed80223151 0x402420fdb004462a 0x8818ffffc111f1ff 0xd1031ffff8223e3f

def z1164 : W := mkw 0x092147cf12327b71 0xc12428f9e2464f6e 0x9800e7cf3111ffff 0xd3001cf9e6223fff

def z1165 : W := mkw 0x2246f800145d8000 0x0448df00028bb000 0xf7e7f8003fff8005 0xfefcff0007fff000

def z1166 : W := mkw 0x07f7b7ed80450000 0x00fef6fdb008a000 0xefffffffc1ff81ff 0xfdfffffff83ff03f

def z1167 : W := mkw 0x07f7b7ed82677951 0x40fef6fdb04cef2a 0xffffffffffffffff 0xffffffffffffffff

def z1168 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0xb818fffff111ffff 0xf7031ffffe223fff

def z1169 : W := mkw 0x27f7b7ed8ccd0000 0x04fef6fdb199a000 0xe7ffffffcfff8007 0xfcfffffff9fff000

def z1170 : W := mkw 0x35b81ef02ba0ed86 0x06b703de05741db0 0xfff81ff03fe07f86 0xffff03fe07fc0ff0

def z1171 : W := mkw 0x0901058e02025a61 0x812020b1c0404b4c 0xbf07078e3e1e7e67 0x77e0e0f1c7c3cfcc

def z1172 : W := mkw 0x07b597ed80223151 0x40f6b2fdb004462a 0x0f18dfffc00071fa 0x41e31bfff8000e3f

def z1173 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xe7ffffffc01e0007 0xfcfffffff803c000

def z1174 : W := mkw 0x0001010d80000000 0x00002021b0000000 0x8018f8ffc0000003 0xd0031f1ff8000000

def z1175 : W := mkw 0x0204900480000000 0x0040920090000000 0x8018f8ffc0000003 0xd0031f1ff8000000

def z1176 : W := mkw 0x0694900000000000 0x00d2920000000000 0x8718f8ffc0000003 0xd0e31f1ff8000000

def z1177 : W := mkw 0x17f7b7ed8aa06902 0x02fef6fdb1540d20 0xfffffffffee07e07 0xffffffffffdc0fc0

def z1178 : W := mkw 0x269cd8003d988000 0x04d39b0007b31000 0x170000003e000000 0x02e0000007c00000

def z1179 : W := mkw 0x26def820bddd8000 0x04dbdf0417bbb000 0xf7fff830ffff8005 0xfeffff061ffff000

def z1180 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0x3f07078e3e1e7e66 0x27e0e0f1c7c3cfcc

def z1181 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0xe7e720000eee0001 0xbcfce40001ddc000

def z1182 : W := mkw 0x079494a480000000 0x00f2929490000000 0x8718d8bec0000003 0x50e31b17d8000000

def z1183 : W := mkw 0x079494a482004800 0x00f2929490400900 0xbf18dfb6fe007e06 0x77e31bf6dfc00fc0

def z1184 : W := mkw 0x06def0003d980000 0x00dbde0007b30000 0xf7fff8003ffe0005 0xfeffff0007ffc000

def z1185 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0x47fffff7c0000000 0xe8fffffef8000000

def z1186 : W := mkw 0x27f7b7ed844d0000 0x04fef6fdb089a000 0xc7ffffffc00e0003 0xf8fffffff801c000

def z1187 : W := mkw 0x100848127330efae 0xa20109024e661df5 0x180000003111fffc 0x0300000006223fff

def z1188 : W := mkw 0x200848127ddd86ac 0xa40109024fbbb0d5 0x300000003fff8e04 0x0600000007fff1c0

def z1189 : W := mkw 0x00284a527130a7ac 0xa005094a4e2614f5 0xf8e0074031f1fffe 0xbf1c00e8063e3fff

def z1190 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0x3f07c78e3e0e7e62 0x67e0f8f1c7c1cfcc

def z1191 : W := mkw 0x26d6f0001cdd0000 0x04dade00039ba000 0x67e7c0000efe0001 0x2cfcf80001dfc000

def z1192 : W := mkw 0x08084812751a96ed 0xa10109024ea352dd 0x18000000311f8ffc 0x030000000623f1ff

def z1193 : W := mkw 0x0204800000000000 0x0040900000000000 0x871ff8ffc0000003 0xf0e3ff1ff8000000

def z1194 : W := mkw 0x15b84ef27bb0efae 0xa2b709de4f761df5 0x7fe007003ff1fffc 0x2ffc00e007fe3fff

def z1195 : W := mkw 0x0367a7cd00673151 0x406cf4f9a00ce62a 0xefffffffc1fff1ff 0xfdfffffff83ffe3f

def z1196 : W := mkw 0x269cd8003d988000 0x04d39b0007b31000 0xf7ffd8003ffe0005 0xfefffb0007ffc000

def z1197 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff807f93fe07ffe 0xffff00ff27fc0fff

def z1198 : W := mkw 0x0b67e7cf167f7b71 0xc16cfcf9e2cfef6e 0xffffffffffffffff 0xffffffffffffffff

def z1199 : W := mkw 0x26d6f8001cdd8000 0x04dadf00039bb000 0x67e7d8000eee0000 0x2cfcfb0001ddc000

def z1200 : W := mkw 0x0b05858e060a5a61 0x8160b0b1c0c14b4c 0xbf07078e3e0e7e66 0x77e0e0f1c7c1cfcc

def z1201 : W := mkw 0x17f7b7ed8ae77953 0x42fef6fdb15cef2a 0xe7ffffffceee7003 0xfcfffffff9ddce00

def z1202 : W := mkw 0x010004a480000000 0x0020009490000000 0x8018f8ffc0000003 0xd0031f1ff8000000

def z1203 : W := mkw 0x00084812711296ed 0xa00109024e2252dd 0x38000000311ffffc 0x070000000623ffff

def z1204 : W := mkw 0x0305858c00021041 0x0060b0b180004208 0xaf1fffffc11ff1ff 0xf5e3fffff823fe3f

def z1205 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0x77e007003ee07e00 0x2efc00e007dc0fc0

def z1206 : W := mkw 0x14fa227029e52586 0x029f444e053ca4b0 0x40f8207001e18180 0x881f040e003c3030

def z1207 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1800004931118ffe 0x03000009262231ff

def z1208 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0xe7ffffffc0fff07b 0xfcfffffff81ffe0f

def z1209 : W := mkw 0x0020024000000000 0x0004004800000000 0xc0f8ffffc0000003 0xf81f1ffff8000000

def z1210 : W := mkw 0x08084812771adeed 0xa10109024ee35bdd 0x380000003e1e7e64 0x0700000007c3cfcc

def z1211 : W := mkw 0x079595ac80021041 0x00f2b2b590004208 0xaf1fdfbec01e7067 0x75e3fbf7d803ce0c

def z1212 : W := mkw 0x069480000c880000 0x00d2900001910000 0x67e700000eee0000 0x2cfce00001ddc000

def z1213 : W := mkw 0x0204c00014180000 0x0040980002830000 0xf7e7c0003ffe0005 0xfefcf80007ffc000

def z1214 : W := mkw 0x07f7b7ed80652110 0x40fef6fdb00ca422 0xc7ffffffc0e00003 0xf8fffffff81c0000

def z1215 : W := mkw 0x0a47e10e145f1261 0x8148fc21c28be24c 0x0007e00e001f8061 0x0000fc01c003f00c

def z1216 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0x77f807f03fe07f80 0xeeff00fe07fc0ff0

def z1217 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff827f13fe1ff9e 0xffff04fe27fc3ff3

def z1218 : W := mkw 0x07d7b5ad80471051 0x40faf6b5b008e20a 0x071ff8bfc01f8079 0x40e3ff17f803f00f

def z1219 : W := mkw 0x07f7b7ed80021041 0x00fef6fdb0004208 0xe7ffffffc00e7003 0xfcfffffff801ce00

def z1220 : W := mkw 0x0246a000044d0000 0x0048d4000089a000 0xe7e720000fff8005 0xbcfce40001fff000

def z1221 : W := mkw 0x26def8107ddd848c 0x24dbdf020fbbb091 0xfffff879ffff81ff 0xffffff0f3ffff03f

def z1222 : W := mkw 0x26d6f0001cdd0000 0x04dade00039ba000 0x77e700003efe0004 0x2efce00007dfc000

def z1223 : W := mkw 0x07f6b6e580000000 0x00fed6dcb0000000 0xc7fff8f7c0000001 0xf8ffff1ef8000000

def z1224 : W := mkw 0x26d6f8001cdd8000 0x04dadf00039bb000 0x67e700000eff8000 0x2cfce00001dff000

def z1225 : W := mkw 0x004b691b715796fd 0xe0096d236e2af2df 0x18072009311f8ffd 0x0300e4012623f1ff

def z1226 : W := mkw 0x0020026180000000 0x0004004c30000000 0x8018f8ffc0000003 0xd0031f1ff8000000

def z1227 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xcfffffffc00001fb 0xf9fffffff800003f

def z1228 : W := mkw 0x05f337ed80000000 0x00be66fdb0000000 0xc0f8ffffc0000003 0xd81f1ffff8000000

def z1229 : W := mkw 0x112107f902227dd7 0x422420ff20444fba 0x080007f000007f82 0x010000fe00000ff0

def z1230 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf07c7fffe1e7e67 0x77e0f8ffffc3cfcc

def z1231 : W := mkw 0x092107ef82227b71 0xc12420fdf0444f6e 0x080007ffc0007ffa 0x010000fff8000fff

def z1232 : W := mkw 0x07b597ec80000000 0x00f6b2fd90000000 0xc7ffdffec0000003 0xf8fffbffd8000000

def z1233 : W := mkw 0x26deb0002dcd0000 0x04dbd60005b9a000 0x77e700003fee0004 0x2efce00007fdc000

def z1234 : W := mkw 0x00084812751886ac 0xa00109024ea310d5 0x380000003f1f8ffc 0x0700000007e3f1ff

def z1235 : W := mkw 0x17f7b7ed8aa06902 0x02fef6fdb1540d20 0xefffffffcfe07187 0xfdfffffff9fc0e30

def z1236 : W := mkw 0x279494a48c880000 0x04f2929491910000 0x0718d8b6ce000000 0x40e31b16d9c00000

def z1237 : W := mkw 0x26def8103ddd8484 0x04dbdf0207bbb090 0xf7fff8b03fff8e05 0xfeffff1607fff1c0

def z1238 : W := mkw 0x0001010800000000 0x0000202100000000 0x801fffffc0000003 0xf003fffff8000000

def z1239 : W := mkw 0x19294ffe7332ffef 0xa32529ffce665ffd 0x9818fffff111ffff 0xd3031ffffe223fff

def z1240 : W := mkw 0x07b496e580000000 0x00f692dcb0000000 0x0718d8f7c0000000 0x40e31b1ef8000000

def z1241 : W := mkw 0x26def8123ddd86a4 0x84dbdf0247bbb0d4 0xfffff8fe3fff8fe7 0xffffff1fc7fff1fc

def z1242 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xfffff8083fff8067 0xffffff0107fff00c

def z1243 : W := mkw 0x0021034900223151 0x400420692004462a 0x8818ffffc00071fb 0xd1031ffff8000e3f

def z1244 : W := mkw 0x17b496e48aa06902 0x02f692dc91540d20 0x67f8dfb6cee07000 0x6cff1bf6d9dc0e00

def z1245 : W := mkw 0x112806d02ba06d86 0x022500da05740db0 0xffe007c03fe07f86 0xfffc00f807fc0ff0

def z1246 : W := mkw 0x26d6f0001cdd0000 0x04dade00039ba000 0x77e7c0003eee0000 0x6efcf80007ddc000

def z1247 : W := mkw 0x07f7b7ed80471041 0x00fef6fdb008e208 0xefffffffc1fff067 0xfdfffffff83ffe0c

def z1248 : W := mkw 0x0063234900673151 0x400c6469200ce62a 0xe8e7e7cf01fff1ff 0xfd1cfcf9e03ffe3f

def z1249 : W := mkw 0x07f7b7ed80202100 0x00fef6fdb0040420 0xcfffffffc0007183 0xf9fffffff8000e30

def z1250 : W := mkw 0x2b05dd8e161ada61 0x8560bbb1c2c35b4c 0xbf07df8e3e1e7e67 0x77e0fbf1c7c3cfcc

def z1251 : W := mkw 0x15b806f1aba06d86 0x02b700de35740db0 0xfff807f1ffe07f86 0xffff00fe3ffc0ff0

def z1252 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0xbf18f8ffff118fff 0xf7e31f1fffe231ff

def z1253 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0x47ffffbfc0000001 0x68fffff7f8000000

def z1254 : W := mkw 0x200848127d9886ac 0xa40109024fb310d5 0x180000003f118ffc 0x0300000007e231ff

def z1255 : W := mkw 0x2edef8063ddd8220 0x85dbdf00c7bbb044 0xf7fff8063fff8005 0xfeffff00c7fff000

def z1256 : W := mkw 0x0043210900000000 0x0008642120000000 0x801ff8ffc0000003 0xd003ff1ff8000000

def z1257 : W := mkw 0x07d7b5ad80000000 0x00faf6b5b0000000 0x871ff8ffc0000003 0xd0e3ff1ff8000000

def z1258 : W := mkw 0x0000000000000000 0x0000000000000000 0x8018f8b6c0000001 0xd0031f16d8000000

def z1259 : W := mkw 0x00084812715586ac 0xa00109024e2ab0d5 0x3800000031ff8ffc 0x07000000063ff1ff

def z1260 : W := mkw 0x0b05d58e961a5a61 0x8160bab1d2c34b4c 0xbf07df8efe1e7e67 0x77e0fbf1dfc3cfcc

def z1261 : W := mkw 0x0020024000202100 0x0004004800040420 0xe8f807f001e07186 0xfd1f00fe003c0e30

def z1262 : W := mkw 0x112107e902227953 0x422420fd20444f2a 0x0000070000007000 0x000000e000000e00

def z1263 : W := mkw 0x07f6b6e580000000 0x00fed6dcb0000000 0xc7f8f8ffc0000003 0xd8ff1f1ff8000000

def z1264 : W := mkw 0x14fa2a7169e5a59e 0x629f454e2d3cb4b3 0x40f83871c1e18198 0x881f070e383c3033

def z1265 : W := mkw 0x0246e000145d0000 0x0048dc00028ba000 0xf7e7c0003efe0005 0x7efcf80007dfc000

def z1266 : W := mkw 0x04d2200008c50000 0x009a44000118a000 0xe7e720000fff8005 0xbcfce40001fff000

def z1267 : W := mkw 0x07f7b7ed82004800 0x00fef6fdb0400900 0xd7fffffffe000e03 0xfaffffffffc001c0

def z1268 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xbf1fc7fe3e1e7e67 0xf7e3f8ffc7c3cfcc

def z1269 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018f8f7c0000000 0xc0031f1ef8000000

def z1270 : W := mkw 0x0f9595ac860a5841 0x01f2b2b590c14b08 0x271fdfb6ce0e7000 0x64e3fbf6d9c1ce00

def z1271 : W := mkw 0x00084812799086ac 0xa00109024f3210d5 0xb818f8fffff18fff 0xd7031f1ffffe31ff

def z1272 : W := mkw 0x07f7b7ed80471051 0x40fef6fdb008e20a 0xefffffffc01ff07f 0xfdfffffff803fe0f

def z1273 : W := mkw 0x04da201029c50484 0x009b44020538a090 0xffff20f93fff8fff 0xffffe41f27fff1ff

def z1274 : W := mkw 0x0b05858c060a5841 0x0160b0b180c14b08 0x3f0707003e0e7e04 0x27e0e0e007c1cfc0

def z1275 : W := mkw 0x04d2300000000000 0x009a460000000000 0xc0f8f8ffc0000003 0xd81f1f1ff8000000

def z1276 : W := mkw 0x092107ce02227b61 0x812420f9c0444f6c 0x080007ce00007fe2 0x010000f9c0000ffc

def z1277 : W := mkw 0x26def8103ddd8484 0x04dbdf0207bbb090 0xfffff8ffffff8f87 0xffffff1ffffff1f0

def z1278 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xf7fff8413fff819d 0xfeffff0827fff033

def z1279 : W := mkw 0x0a47e90f545f9279 0xe148fd21ea8bf24f 0x0007f80fc01f8079 0x0000ff01f803f00f

def z1280 : W := mkw 0x0062224100652110 0x400c4448200ca422 0xc0f8f8ffc1e1819b 0xd81f1f1ff83c3033

def z1281 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff8fffffff1ffff 0xffff1ffffffe3fff

def z1282 : W := mkw 0x0021034800223141 0x0004206900044628 0xe8e7274901fff1ff 0xbd1ce4e9203ffe3f

def z1283 : W := mkw 0x0247b10d80471051 0x4048f621b008e20a 0x881ff8ffc11f81ff 0xd103ff1ff823f03f

def z1284 : W := mkw 0x2a47f90f145f9271 0xc548ff21e28bf24e 0x0007f80f001f8079 0x0000ff01e003f00f

def z1285 : W := mkw 0x0100048002004800 0x0020009000400900 0xbf0707803e1e7e07 0x77e0e0f007c3cfc0

def z1286 : W := mkw 0x0000000000000000 0x0000000000000000 0x8818f8ffc00001fb 0xd1031f1ff800003f

def z1287 : W := mkw 0x07d6b4a480000000 0x00fad69490000000 0x47f8f8b6c0000000 0xc8ff1f16d8000000

def z1288 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xfffff8beffff8e67 0xffffff17dffff1cc

def z1289 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0xb81ff8fff11f8fff 0xf703ff1ffe23f1ff

def z1290 : W := mkw 0x26d6b0000ccd0000 0x04dad6000199a000 0xefe720490fff81ff 0xbdfce40921fff03f

def z1291 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff827f03ff1ff87 0xffff04fe07fe3ff0

def z1292 : W := mkw 0x0001010800021041 0x0000202100004208 0xa807c78e001e7067 0x7500f8f1c003ce0c

def z1293 : W := mkw 0x26d6f8001cdd8000 0x04dadf00039bb000 0xe7e7f8000fff8005 0xbcfcff0001fff000

def z1294 : W := mkw 0x0305c588161a5841 0x0060b8b102c34b08 0xbf07c7883e1e7e67 0x77e0f8f107c3cfcc

def z1295 : W := mkw 0x0021034800673151 0x40042069000ce62a 0xe8e7074801fff1ff 0xbd1ce0e9003ffe3f

def z1296 : W := mkw 0x15b006f00aa06d86 0x02b600de01540db0 0xffe007f03ee07f86 0x7ffc00fe07dc0ff0

def z1297 : W := mkw 0x0498000029800000 0x0093000005300000 0xf7ff00003ffe0005 0xfeffe00007ffc000

def z1298 : W := mkw 0x092107cf02227b71 0xc12420f9e0444f6e 0x0800078e00007e62 0x010000f1c0000fcc

def z1299 : W := mkw 0x15b006e00aa06902 0x02b600dc01540d20 0xffe007c03fe07f86 0xfffc00f807fc0ff0

def z1300 : W := mkw 0x079595ac80000000 0x00f2b2b590000000 0x871fffffc0000003 0xf0e3fffff8000000

def z1301 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0x47f8ffffc0000002 0xc8ff1ffff8000000

def z1302 : W := mkw 0x26def8013ddd8010 0x44dbdf0027bbb002 0xf7fff8013fff801d 0xfeffff0027fff003

def z1303 : W := mkw 0x0367a7cd00000000 0x006cf4f9a0000000 0xc7ffffffc0000003 0xf8fffffff8000000

def z1304 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x0818f8ffc1118ffb 0x81031f1ff82231ff

def z1305 : W := mkw 0x0304848400000000 0x0060909080000000 0x0718d8b6c0000000 0x40e31b16d8000000

def z1306 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xffff07f03ffe7f87 0xffffe0fe07ffcff0

def z1307 : W := mkw 0x0ff7b7ed866f7951 0x41fef6fdb0cdef2a 0xe7ffffffceee7003 0xfcfffffff9ddce00

def z1308 : W := mkw 0x0020024000202100 0x0004004800040420 0xe8f8ffffc1e07187 0xfd1f1ffff83c0e30

def z1309 : W := mkw 0x05f327e900673151 0x40be64fd200ce62a 0xefffffffc1fff1ff 0xfdfffffff83ffe3f

def z1310 : W := mkw 0x07b496e480000000 0x00f692dc90000000 0xc7f8ffffc0000003 0xf8ff1ffff8000000

def z1311 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1800000031000f84 0x03000000062001f0

def z1312 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xfffff8f03fff8fff 0xffffff1e07fff1ff

def z1313 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0x47ffff7fc0000001 0xa8ffffeff8000000

def z1314 : W := mkw 0x26deb8106dcd848c 0x24dbd7020db9b091 0x67ff3871cfef8198 0xacffe70e39fdf033

def z1315 : W := mkw 0x04f2326180000000 0x009e464c30000000 0x40f8f8f7c0000000 0xc81f1f1ef8000000

def z1316 : W := mkw 0x269cc8003ddd8000 0x04d3990007bbb000 0xf7ffc0003fff8005 0xfefff80007fff000

def z1317 : W := mkw 0x05f236e180000000 0x00be46dc30000000 0xc7f8ffffc0000003 0xf8ff1ffff8000000

def z1318 : W := mkw 0x06f7b36d80673151 0x40def66db00ce62a 0xe8ffff7fc1fff1ff 0xbd1fffeff83ffe3f

def z1319 : W := mkw 0x079494a480000000 0x00f2929490000000 0x0718d8ffc0000002 0x40e31b1ff8000000

def z1320 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xdffffffff0000e07 0xfbfffffffe0001c0

def z1321 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0xefffffffc0ee71fb 0xfdfffffff81dce3f

def z1322 : W := mkw 0x26deb8002dcd8000 0x04dbd70005b9b000 0x67e700000fef8000 0x2cfce00001fdf000

def z1323 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xf7fff8f7ffff8f9d 0xfeffff1efffff1f3

def z1324 : W := mkw 0x34fa3a7129e5a596 0x469f474e253cb4b2 0x40f8387101e18198 0x881f070e203c3033

def z1325 : W := mkw 0x26def8007ddd8008 0x24dbdf000fbbb001 0xf7fff801ffff801d 0xfeffff003ffff003

def z1326 : W := mkw 0x01084c927310ceac 0xa02109924e6219d5 0xbf0007803f11fffe 0x77e000f007e23fff

def z1327 : W := mkw 0x07f7b7ed80202100 0x00fef6fdb0040420 0xe7ffffffc0e07003 0xfcfffffff81c0e00

def z1328 : W := mkw 0x26def8027ddd8228 0xa4dbdf004fbbb045 0xfffff84fffff81ff 0xffffff09fffff03f

def z1329 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xc7ffffffc101819b 0xf8fffffff8203033

def z1330 : W := mkw 0x0000000000000000 0x0000000000000000 0x8818f8ffc0100067 0xd1031f1ff802000c

def z1331 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x9800200031118ffd 0x93000400062231ff

def z1332 : W := mkw 0x092107df42227ffd 0xe12420fbe8444fff 0x080007ffc0007ffa 0x010000fff8000fff

def z1333 : W := mkw 0x05b006e000000000 0x00b600dc00000000 0xc7f8dff6c0000002 0xf8ff1bfed8000000

def z1334 : W := mkw 0x26deb0002dcd0000 0x04dbd60005b9a000 0x77ff00003eee0000 0x6effe00007ddc000

def z1335 : W := mkw 0x079494a480000000 0x00f2929490000000 0x8718f8b6c0000001 0xd0e31f16d8000000

def z1336 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xcfffffffc0100067 0xf9fffffff802000c

def z1337 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1800204131118ffc 0x83000408262231ff

def z1338 : W := mkw 0x15b806f06ba06d8e 0x22b700de0d740db1 0xfff807f1ffe07f9e 0xffff00fe3ffc0ff3

def z1339 : W := mkw 0x0042200000450000 0x000844000008a000 0xf7e720003fff8005 0xfefce40007fff000

def z1340 : W := mkw 0x26d6f0001cdd0000 0x04dade00039ba000 0xf7e7e0003fff8005 0xfefcfc0007fff000

def z1341 : W := mkw 0x26def8023ddd8220 0x84dbdf0047bbb044 0xf7fff8863fff8e05 0xfeffff10c7fff1c0

def z1342 : W := mkw 0x26def8003ddd8000 0x04dbdf0007bbb000 0xffffff003ffff007 0xffffffe007fffe00

def z1343 : W := mkw 0x0205810c00000000 0x0040b02180000000 0x801ff8ffc0000003 0xd003ff1ff8000000

def z1344 : W := mkw 0x0267b34d80673151 0x404cf669b00ce62a 0xe8ffffffc1fff1ff 0xfd1ffffff83ffe3f

def z1345 : W := mkw 0x05b806c02ba06900 0x00b700d805740d20 0xfff807c03fe07f86 0xffff00f807fc0ff0

def z1346 : W := mkw 0x079494a482004800 0x00f2929490400900 0x1718d8b6fe000e00 0x42e31b16dfc001c0

def z1347 : W := mkw 0x15b806f02ba06d86 0x02b700de05740db0 0xfff807f83ff07fe7 0xffff00ff07fe0ffc

def z1348 : W := mkw 0x0043210900471051 0x400864212008e20a 0x801ff8ffc01f807b 0xd003ff1ff803f00f

def z1349 : W := mkw 0x07f7b7ed82004800 0x00fef6fdb0400900 0xe7ffffffce007003 0xfcfffffff9c00e00

def z1350 : W := mkw 0x07f6b6e480000000 0x00fed6dc90000000 0xc7fffff6c0000003 0xf8fffffed8000000

def z1351 : W := mkw 0x000848127310ceac 0xa00109024e6219d5 0x380000003f11fffc 0x0700000007e23fff

def z1352 : W := mkw 0x069cc8127d9886ac 0xa0d399024fb310d5 0xfffff8ffffff8fff 0xffffff1ffffff1ff

def z1353 : W := mkw 0x26deb0002dcd0000 0x04dbd60005b9a000 0x67ff00000fee0000 0xacffe00001fdc000

def z1354 : W := mkw 0x07b597ed80000000 0x00f6b2fdb0000000 0xc7f8dfffc0000002 0xf8ff1bfff8000000

def z1355 : W := mkw 0x0490102080000000 0x0092020410000000 0x8018f8ffc0000003 0xd0031f1ff8000000

def z1356 : W := mkw 0x26d6f8001cdd8000 0x04dadf00039bb000 0xf7e7f8003eff8005 0x7efcff0007dff000

def z1357 : W := mkw 0x07f7b7ed80673151 0x40fef6fdb00ce62a 0xc7ffffffc1ff81fb 0xf8fffffff83ff03f

def z1358 : W := mkw 0x0000000000000000 0x0000000000000000 0x8018f8ffc1118007 0xd0031f1ff8223000

def z1359 : W := mkw 0x26deb8002dcd8000 0x04dbd70005b9b000 0x67ff18000eee0000 0x2cffe30001ddc000

def z1360 : W := mkw 0x04da200029c50000 0x009b44000538a000 0xf7ff00003fee0004 0xfeffe00007fdc000

def z1361 : W := mkw 0x0100048002004800 0x0020009000400900 0xbf18fffffe007e07 0xf7e31fffffc00fc0

def z1362 : W := mkw 0x012006c002206900 0x002400d800440d20 0xffe007803ee07e06 0x7ffc00f007dc0fc0

def z1363 : W := mkw 0x180848127fbaffef 0xa30109024ff75ffd 0x380000003ffffffc 0x0700000007ffffff

def z1364 : W := mkw 0x07b496e480000000 0x00f692dc90000000 0x0718dff6c0000002 0x40e31bfed8000000

def z1365 : W := mkw 0x0042200000450000 0x000844000008a000 0xe0fff80001ff8005 0xfc1fff00003ff000

def z1366 : W := mkw 0x004a6812715586ac 0xa0094d024e2ab0d5 0xf8e7200031ff8ffd 0xbf1ce400063ff1ff

def z1367 : W := mkw 0x0b05c58c161a5841 0x0160b8b182c34b08 0xbf07c7803e1e7e07 0x77e0f8f007c3cfc0

def z1368 : W := mkw 0x24da380029c58000 0x049b47000538b000 0xf7ff38003fff8005 0xfeffe70007fff000

def z1369 : W := mkw 0x26def8127ddd86ac 0xa4dbdf024fbbb0d5 0xfffff88e3fff8fff 0xffffff11c7fff1ff

def z1370 : W := mkw 0x079494a480000000 0x00f2929490000000 0x8718dfb6c0000002 0x70e31bf6d8000000

def z1371 : W := mkw 0x15b006e00aa06902 0x02b600dc01540d20 0x7fe007003ee07e04 0x2ffc00e007dc0fc0

def z1372 : W := mkw 0x192107ec02227943 0x032420fd80444f28 0x0000070000007000 0x000000e000000e00

def z1373 : W := mkw 0x00084812711086ac 0xa00109024e2210d5 0x1818f8fff0118ffb 0x43031f1ffe0231ff

def z1374 : W := mkw 0x0b04c48616184a20 0x81609890c2c30944 0xbf07c7863e1e7e07 0x77e0f8f0c7c3cfc0

def z1375 : W := mkw 0x00084812751886ac 0xa00109024ea310d5 0xb818f8ffff1f8fff 0xd7031f1fffe3f1ff

def z1376 : W := mkw 0x100848127bf7ffff 0xe20109024f7effff 0x380000003ffffffc 0x0700000007ffffff

def z1377 : W := mkw 0x0f9494a486084800 0x01f2929490c10900 0x0718d8b6ce000000 0x40e31b16d9c00000

def z1378 : W := mkw 0x15b80ef02ba0ed86 0x02b701de05741db0 0xfff83ff03fe1ff86 0xffff07fe07fc3ff0

def z1379 : W := mkw 0x0021034900000000 0x0004206920000000 0x8018ffffc0000003 0xd0031ffff8000000

def z1380 : W := mkw 0x0246a000044d0000 0x0048d4000089a000 0x67e700000eee0000 0x2cfce00001ddc000

def z1381 : W := mkw 0x0000000000000000 0x0000000000000000 0x8018f8ffc101819b 0xd0031f1ff8203033

def z1382 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xefffffffc0007007 0xfdfffffff8000e00

def z1383 : W := mkw 0x07f7b7ed80000000 0x00fef6fdb0000000 0xc7ffdff6c0000002 0xf8fffbfed8000000

def z1384 : W := mkw 0x0b05cd8e561ada69 0xa160b9b1cac35b4d 0xbf07df8efe1e7e67 0x77e0fbf1dfc3cfcc

def z1385 : W := mkw 0x079595ac80000000 0x00f2b2b590000000 0x071fd8bec0000001 0x40e3fb17d8000000

def z1386 : W := mkw 0x0b05c58e161a5a61 0x8160b8b1c2c34b4c 0xb707c7863e1e7e05 0x76e0f8f0c7c3cfc0

def z1387 : W := mkw 0x080848127718ceac 0xa10109024ee319d5 0x180000003f118ffc 0x0300000007e231ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z7,z3,z8,z5,z6]),(0,[z1,z2,z9,z3,z8,z5,z6]),(0,[z1,z2,z3,z10,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z11,z12])],[(0,[z13,z1,z14,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z12,z15]),(0,[z1,z2,z16,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z18,z6,z19]),(0,[z1,z2,z3,z8,z5,z6,z19])],[(1,[z1,z2,z3,z8,z5,z20])],[(0,[z0,z21,z1,z2,z8,z5,z6]),(0,[z1,z22,z2,z3,z8,z5,z12]),(0,[z23,z1,z2,z24,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z25,z6])],[(1,[z1,z2,z26,z8,z5,z6]),(0,[z27,z21,z1,z2,z8,z5,z6]),(0,[z21,z1,z2,z17,z8,z5,z6]),(0,[z1,z2,z17,z17,z8,z5,z6])],[(0,[z1,z28,z3,z17,z8,z5,z6]),(0,[z29,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z30,z5,z6])],[(0,[z1,z2,z7,z3,z8,z5,z12]),(0,[z21,z1,z2,z8,z5,z31,z6]),(0,[z1,z2,z32,z17,z8,z5,z6]),(0,[z1,z2,z33,z8,z34,z5,z6]),(0,[z1,z2,z3,z35,z8,z5,z6]),(1,[z1,z2,z3,z8,z6,z36])],[(0,[z1,z2,z17,z8,z37,z5,z6]),(0,[z1,z2,z3,z8,z38,z5,z6]),(0,[z1,z2,z39,z3,z8,z5,z6])],[(0,[z40,z1,z2,z3,z41,z5,z6]),(0,[z1,z2,z3,z8,z5,z42,z6]),(0,[z1,z2,z3,z43,z8,z5,z6]),(0,[z1,z2,z44,z3,z8,z5,z6])],[(0,[z45,z1,z2,z3,z8,z5,z12]),(1,[z46,z1,z2,z8,z5,z6])],[(0,[z1,z47,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z48,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z31,z19]),(0,[z49,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z50,z5,z6]),(1,[z1,z2,z51,z33,z5,z6])],[(0,[z0,z1,z2,z3,z8,z5,z52]),(0,[z13,z0,z1,z2,z8,z5,z6])],[(0,[z1,z2,z51,z3,z8,z5,z6])],[],[(0,[z53,z1,z2,z3,z8,z5,z6])]],
   [[],[(0,[z1,z2,z54,z8,z5,z55,z6]),(0,[z1,z2,z8,z5,z31,z6,z56])],[(0,[z1,z2,z3,z8,z5,z57,z6])],[(0,[z1,z58,z2,z17,z8,z5,z6]),(0,[z1,z59,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z60]),(0,[z1,z2,z3,z8,z5,z61,z6])],[(0,[z21,z1,z2,z62,z8,z5,z6]),(0,[z63,z1,z2,z3,z8,z5,z6]),(0,[z64,z1,z2,z65,z3,z5,z6])],[(0,[z1,z28,z2,z3,z8,z5,z31]),(0,[z13,z1,z2,z3,z8,z66,z6]),(0,[z1,z2,z67,z24,z8,z5,z6]),(1,[z1,z68,z3,z8,z69,z6])],[(0,[z1,z2,z3,z8,z5,z6,z70]),(0,[z1,z2,z71,z3,z8,z5,z6])],[(0,[z13,z1,z2,z72,z8,z5,z6]),(0,[z1,z2,z17,z8,z5,z73,z6]),(0,[z1,z2,z24,z8,z5,z74,z6]),(0,[z1,z2,z3,z75,z5,z76,z6])],[(1,[z1,z2,z3,z8,z5,z6])],[(0,[z0,z1,z2,z3,z8,z77,z6]),(0,[z1,z2,z78,z3,z8,z5,z6]),(0,[z1,z2,z79,z3,z8,z5,z6])],[(0,[z1,z80,z2,z17,z8,z5,z6])],[(0,[z2,z3,z8,z5,z31,z6,z12])],[(0,[z1,z2,z81,z3,z8,z5,z31]),(0,[z1,z2,z3,z8,z5,z74,z31]),(0,[z1,z82,z2,z83,z8,z5,z6]),(0,[z1,z2,z84,z3,z8,z5,z6])],[(0,[z1,z2,z3,z17,z8,z5,z12]),(1,[z1,z2,z3,z35,z75,z6])],[(0,[z1,z2,z85,z3,z8,z5,z6])],[(1,[z1,z2,z86,z8,z5,z6]),(0,[z1,z2,z87,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z88,z6])]],
   [[(0,[z45,z21,z1,z2,z8,z5,z6]),(0,[z89,z1,z2,z3,z8,z5,z31]),(0,[z64,z1,z2,z3,z90,z5,z6]),(0,[z1,z2,z91,z3,z8,z5,z6]),(0,[z1,z92,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z93,z6]),(0,[z1,z2,z3,z8,z94,z55,z6]),(0,[z1,z2,z3,z8,z95,z5,z6])],[],[(1,[z1,z2,z3,z8,z5,z96]),(0,[z1,z2,z3,z8,z5,z97,z6]),(0,[z1,z98,z2,z3,z8,z5,z6])],[(0,[z21,z1,z2,z8,z99,z5,z6]),(0,[z1,z2,z100,z17,z8,z5,z6]),(0,[z1,z2,z62,z3,z33,z5,z6]),(0,[z1,z2,z3,z8,z5,z101,z6])],[(0,[z13,z1,z2,z8,z5,z31,z6]),(0,[z102,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z103,z3,z8,z5,z6]),(0,[z104,z1,z2,z3,z8,z5,z6]),(1,[z1,z82,z3,z90,z5,z6]),(0,[z1,z82,z2,z3,z90,z5,z6])],[(0,[z1,z2,z105,z3,z8,z5,z6])],[(0,[z13,z1,z2,z106,z8,z5,z6])],[(0,[z1,z2,z107,z8,z108,z5,z6]),(0,[z1,z109,z2,z3,z8,z5,z31])],[(0,[z13,z1,z58,z2,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z110]),(1,[z1,z2,z8,z5,z111,z6]),(0,[z1,z2,z112,z24,z8,z5,z6]),(1,[z1,z2,z113,z8,z5,z6]),(0,[z1,z114,z2,z3,z8,z5,z115]),(1,[z1,z2,z3,z5,z6,z116])],[(1,[z21,z1,z2,z8,z5,z12]),(0,[z1,z114,z2,z3,z8,z5,z12]),(0,[z117,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z118,z6]),(0,[z1,z2,z3,z8,z5,z119,z31]),(0,[z1,z2,z3,z8,z5,z6,z120])],[],[(0,[z13,z1,z2,z26,z8,z5,z6]),(0,[z21,z1,z2,z3,z8,z5,z96]),(0,[z121,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z122,z8,z5,z6])],[(0,[z1,z2,z123,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z73,z12]),(0,[z1,z2,z123,z24,z8,z5,z6])]],
   [[(0,[z1,z2,z124,z3,z8,z5,z6]),(0,[z1,z58,z2,z3,z8,z5,z6]),(0,[z1,z2,z125,z3,z5,z73,z6]),(0,[z1,z2,z126,z67,z8,z5,z6])],[(0,[z28,z2,z7,z3,z8,z5,z6]),(0,[z127,z1,z2,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z128])],[(0,[z13,z1,z2,z62,z8,z5,z6]),(0,[z1,z129,z2,z3,z8,z5,z6]),(0,[z1,z130,z2,z3,z8,z5,z6]),(0,[z1,z2,z131,z3,z8,z5,z6])],[(0,[z13,z1,z1,z2,z8,z5,z6]),(0,[z1,z2,z132,z3,z8,z5,z6]),(0,[z1,z68,z2,z24,z8,z5,z6]),(0,[z1,z2,z24,z8,z5,z11,z6])],[(0,[z1,z2,z3,z8,z5,z6,z52]),(0,[z1,z2,z3,z8,z5,z31,z120]),(0,[z1,z2,z3,z133,z8,z5,z6]),(0,[z1,z2,z3,z134,z8,z5,z6]),(0,[z1,z135,z2,z3,z8,z5,z6])],[(0,[z1,z2,z126,z24,z8,z5,z6]),(0,[z64,z1,z3,z8,z99,z5,z6]),(0,[z1,z136,z2,z3,z8,z5,z6]),(0,[z137,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z138])],[(0,[z1,z58,z2,z86,z8,z5,z6])],[(0,[z139,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z140,z3,z8,z5,z6])],[(0,[z13,z64,z1,z2,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z141,z6])],[(0,[z21,z1,z2,z72,z8,z5,z6]),(0,[z1,z2,z17,z72,z8,z5,z6]),(0,[z142,z1,z2,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z5,z143]),(0,[z1,z2,z144,z3,z8,z5,z6]),(0,[z1,z2,z2,z24,z8,z5,z6]),(0,[z1,z2,z3,z145,z8,z5,z6]),(0,[z1,z2,z146,z106,z8,z5,z6])],[(0,[z1,z2,z3,z8,z69,z147,z6]),(0,[z1,z58,z2,z3,z8,z73,z6]),(0,[z1,z2,z3,z8,z5,z148,z6]),(0,[z1,z2,z3,z8,z5,z76,z6])],[(0,[z1,z2,z3,z149,z8,z99,z6])]],
   [[(0,[z13,z1,z2,z3,z8,z5,z6]),(0,[z150,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z151,z6])],[(0,[z1,z2,z3,z152,z8,z5,z6]),(0,[z1,z2,z3,z153,z8,z5,z6]),(0,[z1,z2,z154,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z155,z5,z6]),(0,[z1,z2,z3,z8,z156,z5,z6])],[(0,[z13,z1,z2,z8,z99,z5,z6]),(0,[z21,z1,z2,z157,z8,z5,z6]),(0,[z1,z2,z3,z158,z8,z5,z6]),(0,[z1,z2,z3,z8,z159,z5,z6]),(0,[z1,z2,z157,z3,z8,z5,z120])],[(0,[z40,z1,z2,z3,z8,z5,z160]),(0,[z1,z2,z3,z90,z8,z5,z31])],[(0,[z1,z2,z3,z72,z75,z5,z6])],[(0,[z13,z1,z68,z2,z8,z5,z6]),(0,[z161,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z162,z6])],[(0,[z0,z1,z2,z163,z8,z5,z6]),(0,[z1,z2,z3,z164,z8,z5,z6]),(0,[z40,z2,z3,z8,z147,z5,z6]),(0,[z1,z2,z3,z8,z5,z165,z6]),(0,[z1,z2,z24,z8,z5,z166,z6])],[(0,[z1,z2,z3,z8,z167,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z160]),(0,[z1,z24,z3,z17,z8,z5,z6])],[(0,[z168,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z169,z3,z8,z5,z6]),(0,[z1,z170,z2,z3,z8,z5,z6])],[(0,[z1,z2,z17,z8,z5,z31,z6]),(0,[z1,z171,z2,z3,z8,z5,z6]),(0,[z1,z2,z172,z3,z8,z5,z6]),(0,[z1,z2,z67,z8,z5,z141,z6]),(0,[z1,z2,z3,z173,z8,z5,z6])],[(0,[z40,z1,z2,z3,z8,z5,z174]),(1,[z1,z2,z175,z8,z5,z6]),(0,[z1,z2,z3,z8,z176,z5,z6])],[(0,[z177,z1,z2,z3,z8,z5,z6]),(0,[z21,z1,z2,z106,z8,z5,z6])],[(0,[z64,z1,z2,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z178,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z179])],[(0,[z21,z1,z58,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z180,z6]),(0,[z1,z2,z181,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z182,z5,z6]),(0,[z1,z2,z3,z183,z8,z5,z6]),(0,[z1,z2,z24,z17,z8,z5,z6]),(0,[z1,z2,z24,z184,z8,z5,z6])]],
   [[(0,[z185,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z186,z6])],[(0,[z21,z1,z80,z2,z8,z5,z6]),(0,[z1,z2,z51,z24,z8,z5,z6]),(0,[z1,z2,z3,z8,z187,z5,z6])],[(0,[z1,z82,z2,z17,z8,z5,z6])],[(0,[z188,z21,z1,z2,z8,z5,z6]),(0,[z1,z189,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z190,z12]),(0,[z1,z2,z191,z3,z8,z5,z31])],[(0,[z1,z2,z3,z72,z8,z5,z12]),(0,[z40,z1,z2,z3,z8,z5,z12]),(0,[z1,z2,z192,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z193,z5,z6]),(0,[z1,z2,z65,z157,z3,z5,z6]),(0,[z194,z1,z2,z3,z8,z5,z6])],[(0,[z13,z1,z2,z8,z75,z5,z6]),(0,[z1,z2,z146,z3,z8,z5,z6])],[(1,[z13,z2,z195,z8,z5,z6]),(0,[z1,z2,z3,z8,z147,z5,z6]),(1,[z1,z2,z65,z3,z76,z6])],[(0,[z21,z1,z1,z2,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z196]),(0,[z40,z1,z2,z3,z197,z5,z6]),(0,[z63,z1,z2,z24,z8,z5,z6]),(0,[z1,z198,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z12]),(0,[z1,z2,z3,z8,z199,z5,z6]),(0,[z200,z1,z2,z3,z8,z5,z6]),(0,[z1,z201,z2,z3,z8,z5,z6])],[],[],[(0,[z1,z2,z3,z8,z202,z5,z6]),(1,[z1,z2,z24,z8,z5,z6]),(0,[z203,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z204]),(0,[z1,z2,z3,z8,z205,z5,z6]),(0,[z1,z2,z3,z8,z206,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z207]),(0,[z1,z2,z3,z8,z5,z6,z208])],[(0,[z1,z2,z3,z8,z6,z36,z120])]],
   [[(0,[z13,z1,z2,z157,z8,z5,z6]),(1,[z1,z2,z105,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z6,z209]),(0,[z1,z2,z157,z3,z75,z5,z6])],[(1,[z1,z2,z210,z8,z5,z6]),(1,[z21,z1,z2,z8,z5,z31]),(0,[z21,z1,z2,z67,z8,z5,z6]),(0,[z1,z114,z2,z3,z8,z5,z31]),(0,[z1,z2,z24,z8,z5,z73,z6])],[(0,[z13,z1,z2,z8,z5,z211,z6]),(0,[z13,z127,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z195,z8,z5,z6]),(0,[z1,z2,z212,z3,z8,z5,z6]),(0,[z1,z2,z3,z213,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z31,z12]),(0,[z214,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z16,z3,z8,z5,z6])],[(0,[z215,z216,z1,z2,z8,z5,z6]),(0,[z1,z2,z217,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z218,z6])],[(0,[z1,z2,z3,z108,z99,z5,z6]),(0,[z1,z1,z2,z3,z8,z5,z12])],[(0,[z219,z1,z2,z3,z8,z5,z6]),(1,[z13,z1,z2,z8,z5,z12]),(0,[z21,z1,z2,z3,z8,z5,z6]),(0,[z21,z1,z2,z8,z220,z5,z6]),(0,[z1,z2,z3,z8,z147,z73,z6]),(0,[z1,z2,z3,z8,z221,z5,z6])],[(0,[z1,z2,z3,z107,z8,z5,z6]),(0,[z222,z1,z2,z3,z8,z5,z223]),(0,[z1,z2,z3,z8,z5,z73,z31])],[(0,[z21,z1,z2,z8,z69,z5,z6]),(0,[z1,z2,z17,z8,z99,z5,z6]),(0,[z1,z2,z32,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z18,z6])],[(0,[z0,z1,z2,z3,z8,z5,z31]),(0,[z1,z2,z65,z3,z8,z5,z12]),(0,[z1,z2,z3,z8,z224,z5,z6]),(0,[z1,z2,z225,z3,z8,z6,z120])],[(0,[z1,z2,z3,z226,z8,z5,z6]),(0,[z1,z109,z2,z16,z3,z8,z5]),(0,[z227,z1,z2,z3,z8,z5,z6])],[(0,[z40,z21,z1,z2,z8,z5,z6]),(0,[z21,z1,z68,z2,z8,z5,z6]),(0,[z1,z2,z3,z228,z8,z5,z6]),(0,[z45,z2,z3,z8,z5,z55,z6]),(0,[z1,z2,z106,z3,z8,z5,z12]),(0,[z1,z2,z229,z3,z8,z5,z6])],[(1,[z1,z2,z3,z152,z5,z6]),(0,[z1,z2,z230,z3,z8,z5,z6]),(0,[z1,z2,z65,z3,z8,z18,z6])],[(0,[z1,z2,z65,z3,z108,z5,z6])],[(0,[z231,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z232,z5,z6]),(0,[z1,z233,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z234]),(0,[z1,z2,z235,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z236]),(0,[z1,z2,z3,z8,z5,z237,z12]),(1,[z1,z24,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z238,z6]),(0,[z1,z2,z3,z33,z8,z5,z6])],[(0,[z13,z1,z80,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z239,z6]),(0,[z240,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z216,z1,z2,z3,z8,z5,z12]),(0,[z241,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z8,z242,z5,z55,z6]),(0,[z1,z2,z157,z3,z8,z5,z12]),(0,[z1,z2,z243,z3,z8,z5,z6])],[(1,[z1,z2,z244,z8,z5,z12]),(0,[z1,z2,z245,z3,z8,z5,z6])],[(0,[z13,z246,z1,z2,z8,z5,z6])],[(0,[z1,z2,z247,z3,z8,z5,z6]),(0,[z246,z1,z2,z3,z8,z5,z12])],[(0,[z188,z1,z2,z3,z8,z5,z31]),(0,[z1,z58,z2,z24,z8,z5,z6]),(0,[z1,z2,z157,z3,z248,z5,z6]),(0,[z1,z2,z3,z8,z249,z5,z18])],[(0,[z1,z2,z3,z8,z250,z5,z6])],[(0,[z1,z2,z3,z8,z5,z251,z6]),(1,[z1,z2,z252,z8,z5,z6]),(0,[z1,z2,z3,z253,z8,z5,z6]),(0,[z1,z68,z2,z3,z8,z69,z6])],[(0,[z0,z1,z2,z254,z8,z5,z6]),(0,[z255,z13,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z256,z8,z5,z6])],[(0,[z257,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z258,z8,z5,z6]),(0,[z1,z2,z3,z259,z5,z73,z6])],[(0,[z46,z1,z2,z17,z8,z5,z6]),(0,[z1,z2,z83,z3,z8,z5,z6])],[(0,[z1,z80,z2,z3,z8,z5,z6]),(0,[z1,z260,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z261])],[(0,[z21,z1,z2,z8,z75,z5,z6]),(0,[z262,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z263,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z264]),(0,[z1,z2,z3,z8,z5,z11,z31]),(0,[z1,z2,z17,z8,z75,z5,z6])],[(0,[z1,z2,z3,z8,z259,z5,z6]),(0,[z1,z2,z51,z3,z33,z5,z6]),(0,[z1,z2,z265,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z266,z76])],[(0,[z267,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z248,z8,z5,z11])],[(0,[z13,z1,z2,z67,z8,z5,z6]),(0,[z1,z2,z3,z8,z99,z5,z12]),(0,[z1,z2,z3,z8,z268,z5,z12]),(0,[z1,z2,z3,z8,z5,z269,z6]),(0,[z1,z2,z3,z8,z5,z6,z270])]],
   [[(0,[z1,z28,z2,z17,z8,z5,z6]),(0,[z21,z1,z2,z252,z8,z5,z6]),(0,[z1,z2,z3,z8,z94,z5,z6]),(0,[z271,z1,z2,z3,z8,z5,z6]),(0,[z272,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z7,z3,z8,z5,z31]),(0,[z1,z2,z3,z35,z8,z147,z6]),(0,[z1,z3,z90,z8,z99,z5,z6])],[(0,[z216,z1,z7,z3,z8,z5,z6]),(1,[z13,z1,z26,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z273,z6]),(0,[z1,z2,z3,z248,z8,z249,z5])],[(0,[z1,z2,z274,z3,z8,z5,z6]),(0,[z1,z2,z275,z3,z8,z5,z6]),(0,[z1,z2,z3,z248,z8,z5,z6])],[(0,[z13,z1,z2,z24,z8,z5,z6]),(0,[z45,z1,z2,z3,z8,z5,z31]),(0,[z1,z2,z3,z8,z5,z31,z264]),(0,[z1,z2,z100,z3,z8,z5,z6])],[(0,[z246,z1,z7,z3,z8,z5,z6]),(0,[z13,z1,z2,z8,z69,z5,z6]),(0,[z1,z276,z2,z3,z8,z5,z6]),(0,[z1,z2,z65,z3,z8,z76,z6])],[(0,[z216,z21,z1,z2,z8,z5,z6]),(0,[z1,z2,z24,z72,z8,z5,z6]),(0,[z1,z2,z51,z8,z5,z141,z6]),(1,[z1,z2,z277,z8,z5,z6])],[(0,[z1,z2,z106,z8,z5,z6,z278])],[(0,[z1,z279,z2,z3,z8,z5,z6]),(1,[z1,z2,z71,z8,z5,z6]),(0,[z1,z109,z2,z3,z8,z5,z280])],[(1,[z215,z1,z2,z8,z5,z6]),(0,[z246,z21,z1,z2,z8,z5,z6]),(0,[z1,z2,z81,z8,z5,z31,z6]),(0,[z1,z2,z3,z8,z281,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z282])],[(0,[z89,z1,z2,z17,z8,z5,z6]),(0,[z283,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z249,z5,z6])],[(1,[z13,z1,z2,z8,z284,z6])],[],[(0,[z188,z13,z1,z2,z8,z5,z6]),(1,[z13,z1,z2,z285,z5,z6]),(0,[z21,z1,z2,z286,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z287,z6]),(0,[z1,z288,z2,z3,z8,z5,z6]),(0,[z1,z2,z16,z3,z8,z5,z18])],[(0,[z13,z1,z2,z8,z285,z5,z6]),(0,[z21,z1,z2,z8,z108,z5,z6]),(0,[z127,z2,z3,z8,z5,z31,z6]),(0,[z246,z1,z80,z3,z8,z5,z6])]],
   [[(0,[z0,z1,z2,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z289,z5,z6]),(0,[z1,z2,z3,z290,z8,z5,z6]),(0,[z1,z2,z3,z8,z291,z5,z6]),(0,[z1,z2,z3,z8,z34,z5,z6])],[(0,[z127,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z24,z8,z5,z6,z292]),(0,[z1,z2,z3,z8,z5,z6,z293])],[(0,[z294,z1,z2,z3,z8,z5,z6])],[(0,[z0,z2,z7,z3,z8,z5,z6]),(0,[z13,z1,z2,z3,z152,z5,z6]),(0,[z1,z2,z3,z8,z75,z5,z12]),(0,[z1,z109,z2,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z295,z6])],[(0,[z1,z2,z24,z8,z5,z31,z6]),(0,[z1,z2,z3,z8,z5,z6,z296]),(0,[z1,z2,z3,z297,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z298]),(0,[z1,z2,z3,z8,z5,z299,z6])],[],[(0,[z1,z300,z2,z3,z8,z5,z6]),(0,[z1,z301,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z17,z8,z5,z31])],[(0,[z1,z302,z2,z3,z8,z5,z6])],[],[(0,[z303,z1,z2,z3,z8,z5,z6]),(0,[z0,z1,z2,z3,z8,z5,z304]),(0,[z1,z2,z146,z24,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z278])],[(0,[z305,z21,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z306,z6])],[(0,[z1,z2,z3,z248,z5,z11,z6])],[(0,[z1,z2,z3,z8,z5,z307,z6])],[(0,[z1,z2,z17,z308,z8,z5,z6]),(1,[z1,z2,z3,z8,z309,z5]),(0,[z1,z2,z3,z8,z5,z310,z6])],[(0,[z1,z2,z65,z3,z8,z5,z31]),(0,[z1,z2,z311,z3,z8,z5,z6])]],
   [[(0,[z1,z312,z2,z3,z8,z5,z6]),(0,[z1,z2,z313,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z314,z5,z6]),(0,[z315,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z316,z6])],[(0,[z1,z114,z2,z16,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z317,z6])],[(0,[z1,z2,z3,z318,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z31,z278]),(0,[z1,z319,z2,z3,z8,z5,z6])],[(0,[z2,z3,z8,z147,z5,z55,z6]),(0,[z1,z2,z81,z3,z8,z5,z6]),(0,[z1,z320,z2,z3,z8,z5,z6]),(0,[z1,z68,z2,z3,z35,z8,z6])],[(0,[z1,z2,z321,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z56]),(0,[z1,z2,z3,z8,z5,z322,z6])],[(0,[z1,z2,z3,z8,z323,z5,z6]),(0,[z1,z2,z16,z24,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z324]),(0,[z1,z2,z67,z3,z8,z141,z6])],[(0,[z1,z325,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z326,z8,z5,z6])],[],[(0,[z1,z2,z7,z17,z8,z5,z6]),(0,[z327,z13,z1,z2,z8,z5,z6]),(0,[z328,z21,z1,z2,z8,z5,z6]),(0,[z21,z1,z2,z24,z8,z5,z6]),(0,[z329,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z330,z5,z6])],[(0,[z1,z2,z3,z8,z5,z331,z6]),(0,[z21,z1,z2,z35,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z332,z6]),(0,[z1,z68,z2,z3,z8,z5,z12]),(0,[z246,z1,z2,z3,z8,z5,z31]),(0,[z1,z2,z17,z8,z69,z5,z6]),(0,[z1,z2,z3,z8,z5,z333,z6])],[(0,[z1,z2,z3,z334,z8,z5,z6]),(0,[z335,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z336,z3,z8,z5])],[(0,[z13,z1,z2,z286,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z337,z6]),(0,[z45,z1,z2,z17,z8,z5,z6]),(0,[z1,z2,z3,z338,z8,z5,z6])],[(0,[z13,z1,z2,z8,z108,z5,z6]),(0,[z45,z1,z2,z3,z8,z55,z6]),(0,[z64,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z339,z6])],[(0,[z1,z2,z3,z8,z340,z5,z6]),(0,[z1,z2,z3,z8,z5,z31,z56]),(0,[z1,z2,z3,z8,z5,z6,z341])],[(0,[z1,z2,z342,z3,z8,z5,z6]),(0,[z1,z2,z24,z3,z8,z5,z6]),(0,[z1,z2,z133,z17,z8,z5,z6]),(0,[z343,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z344,z3,z8,z5,z6]),(0,[z345,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z286,z3,z8,z5,z12]),(0,[z1,z2,z3,z33,z72,z5,z6])],[(0,[z21,z2,z286,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z346,z6]),(0,[z1,z2,z24,z8,z99,z5,z6]),(0,[z1,z109,z2,z347,z8,z5,z6])],[(0,[z1,z2,z348,z3,z8,z5,z31]),(0,[z1,z82,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z35,z75,z5,z6])],[(0,[z349,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z62,z3,z8,z5,z12]),(0,[z1,z350,z2,z3,z8,z5,z6]),(0,[z1,z2,z351,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z352,z5,z6]),(0,[z1,z2,z157,z3,z5,z6,z120])],[(0,[z1,z2,z3,z8,z353,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z354]),(0,[z1,z2,z355,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z356,z5,z6])],[(0,[z1,z2,z357,z3,z8,z5,z6])],[(1,[z1,z2,z17,z8,z5,z12]),(0,[z1,z2,z3,z8,z99,z5,z31])],[],[(0,[z222,z1,z2,z3,z8,z5,z12]),(0,[z1,z2,z3,z358,z8,z5,z6])],[(0,[z13,z1,z2,z8,z5,z141,z6])],[(0,[z1,z359,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z108,z75,z5,z6]),(0,[z1,z2,z360,z3,z8,z5,z6])],[(0,[z13,z1,z2,z8,z284,z5,z6]),(0,[z222,z1,z2,z3,z108,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z361]),(0,[z1,z2,z362,z3,z8,z5,z6])],[(0,[z21,z1,z2,z65,z8,z5,z6]),(0,[z1,z80,z2,z24,z8,z5,z6]),(0,[z1,z2,z65,z3,z5,z76,z6]),(0,[z1,z2,z3,z8,z5,z6,z363])],[(0,[z1,z364,z2,z3,z8,z5,z6]),(0,[z365,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z366,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z266,z6])]],
   [[(0,[z1,z2,z3,z8,z367,z5,z6])],[(0,[z1,z114,z2,z3,z8,z5,z280])],[(0,[z1,z2,z3,z8,z368,z5,z6]),(0,[z1,z2,z3,z8,z69,z5,z12])],[(0,[z13,z1,z2,z8,z5,z6,z19]),(0,[z1,z2,z369,z3,z8,z5,z6]),(0,[z1,z2,z370,z3,z8,z5,z6])],[(0,[z13,z63,z1,z2,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z223]),(0,[z1,z2,z3,z8,z5,z55,z6]),(0,[z1,z2,z3,z8,z371,z5,z6]),(0,[z1,z2,z3,z372,z8,z5,z6])],[(0,[z1,z2,z24,z8,z75,z5,z6])],[(0,[z1,z2,z62,z8,z34,z5,z6])],[(0,[z1,z2,z3,z8,z5,z115,z6])],[(1,[z1,z7,z17,z8,z5,z6]),(0,[z13,z1,z2,z35,z8,z5,z6]),(1,[z21,z1,z2,z8,z5,z354]),(0,[z1,z2,z65,z3,z8,z55,z6]),(0,[z1,z2,z3,z8,z5,z373,z6])],[(0,[z1,z2,z3,z8,z5,z6,z374])],[(0,[z375,z1,z2,z3,z8,z5,z6])],[(1,[z1,z2,z3,z41,z5,z6]),(0,[z376,z1,z2,z3,z8,z5,z6]),(0,[z377,z1,z2,z3,z8,z5,z6])],[(0,[z1,z114,z2,z17,z8,z5,z6])],[(0,[z378,z1,z2,z3,z8,z5,z6])],[(0,[z222,z21,z1,z2,z8,z5,z6]),(0,[z21,z1,z2,z8,z5,z6,z120]),(0,[z1,z379,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z72,z8,z5,z31]),(0,[z40,z1,z2,z3,z8,z5,z31]),(1,[z1,z2,z258,z8,z5,z6])],[(0,[z1,z2,z67,z3,z8,z5,z12])]],
   [[(0,[z380,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z381,z6])],[(0,[z1,z2,z382,z3,z8,z5,z12])],[(0,[z1,z2,z3,z8,z5,z6,z15]),(0,[z1,z2,z383,z3,z8,z5,z6]),(0,[z1,z2,z17,z8,z108,z5,z6]),(1,[z1,z80,z17,z8,z5,z6])],[],[(0,[z1,z384,z2,z3,z8,z5,z6]),(0,[z13,z1,z14,z2,z8,z5,z6]),(1,[z13,z1,z2,z8,z5,z211]),(0,[z1,z2,z3,z8,z385,z5,z6]),(0,[z1,z2,z3,z8,z5,z386,z6])],[(0,[z127,z1,z2,z24,z8,z5,z6])],[(0,[z1,z2,z3,z163,z8,z5,z6])],[(0,[z1,z2,z387,z3,z8,z5,z6]),(1,[z1,z2,z3,z197,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z388])],[(0,[z1,z2,z389,z3,z8,z5,z6]),(0,[z1,z2,z390,z3,z8,z5,z6])],[(0,[z46,z1,z2,z3,z8,z5,z6]),(0,[z391,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z392,z6]),(2,[z1,z26,z8,z5,z6])],[],[(0,[z1,z393,z2,z7,z8,z5,z6]),(0,[z1,z2,z3,z8,z394,z5,z6]),(0,[z395,z1,z2,z3,z8,z5,z6]),(0,[z13,z1,z2,z65,z8,z5,z6]),(0,[z1,z2,z3,z8,z396,z5,z6]),(0,[z1,z2,z3,z8,z5,z31,z31]),(0,[z1,z2,z3,z8,z5,z397,z6]),(0,[z1,z2,z3,z75,z5,z11,z6])],[(0,[z2,z3,z72,z8,z108,z5,z6]),(0,[z1,z2,z3,z8,z398,z5,z6]),(0,[z1,z2,z16,z3,z248,z8,z5])],[(0,[z21,z1,z2,z8,z5,z141,z6]),(1,[z89,z2,z3,z108,z5,z6]),(0,[z1,z1,z2,z3,z8,z5,z31]),(0,[z1,z2,z17,z8,z5,z141,z6]),(0,[z1,z2,z3,z399,z8,z5,z6]),(1,[z1,z2,z225,z3,z8,z6])],[(1,[z13,z1,z2,z8,z5,z31]),(0,[z127,z63,z2,z3,z8,z5,z6]),(0,[z188,z1,z2,z17,z8,z5,z6]),(0,[z1,z2,z3,z35,z8,z76,z6])]],
   [[(0,[z1,z28,z2,z3,z8,z5,z6]),(0,[z215,z21,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z31,z388]),(0,[z1,z2,z17,z8,z5,z400,z6]),(0,[z1,z2,z3,z8,z5,z401,z6])],[(0,[z21,z1,z2,z8,z5,z76,z6])],[(0,[z1,z2,z3,z8,z55,z73,z6])],[(1,[z1,z2,z3,z318,z5,z6]),(0,[z1,z402,z2,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z5,z403]),(0,[z1,z2,z106,z3,z8,z5,z31])],[(0,[z255,z1,z2,z3,z8,z5,z6]),(0,[z21,z1,z2,z158,z8,z5,z6]),(0,[z1,z404,z2,z3,z8,z5,z6]),(0,[z1,z2,z336,z3,z8,z5,z6])],[(0,[z405,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z406,z8,z5,z6]),(0,[z1,z2,z407,z3,z8,z5,z6])],[(0,[z408,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z74,z6])],[(0,[z21,z1,z2,z8,z5,z6,z19]),(0,[z1,z2,z17,z8,z5,z6,z19]),(1,[z1,z2,z409,z8,z5,z6]),(0,[z1,z2,z157,z16,z3,z8,z5])],[],[(0,[z1,z2,z3,z8,z77,z5,z6]),(0,[z216,z1,z2,z3,z8,z5,z31]),(0,[z1,z2,z3,z8,z8,z5,z6]),(0,[z1,z2,z3,z8,z108,z5,z12]),(0,[z222,z1,z2,z3,z8,z385,z6]),(0,[z1,z2,z3,z8,z410,z5,z6]),(0,[z1,z2,z157,z3,z8,z5,z31]),(0,[z1,z2,z3,z8,z5,z411,z6])],[(0,[z89,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z244,z3,z8,z5,z6]),(0,[z1,z2,z3,z412,z8,z5,z6])],[(0,[z216,z28,z2,z3,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z6,z120])],[(0,[z1,z2,z413,z3,z8,z5,z6]),(0,[z1,z2,z17,z35,z8,z5,z6])],[(1,[z13,z1,z14,z8,z5,z6]),(0,[z414,z21,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z415,z6]),(0,[z1,z2,z106,z3,z8,z5,z278]),(0,[z1,z2,z3,z416,z8,z5,z6])],[(0,[z222,z1,z2,z3,z8,z5,z31]),(0,[z1,z2,z3,z8,z5,z6,z417]),(0,[z1,z2,z126,z3,z8,z5,z12])]],
   [[(0,[z0,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z418,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z419,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z280]),(0,[z1,z2,z3,z8,z420,z5,z6])],[(1,[z1,z2,z3,z8,z5,z52]),(1,[z255,z1,z2,z8,z5,z6]),(0,[z27,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z8,z5,z306,z6]),(0,[z64,z1,z2,z24,z8,z5,z6]),(0,[z1,z2,z421,z3,z8,z5,z6]),(0,[z1,z422,z2,z3,z8,z5,z6])],[(1,[z1,z2,z423,z8,z5,z6]),(0,[z1,z109,z2,z3,z8,z249,z5]),(0,[z1,z2,z126,z8,z94,z5,z6]),(0,[z424,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z116,z19])],[(0,[z1,z425,z2,z3,z8,z5,z6]),(0,[z1,z2,z24,z24,z8,z5,z6]),(0,[z426,z1,z2,z3,z8,z5,z6]),(0,[z1,z109,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z427,z6])],[(0,[z1,z2,z24,z8,z69,z5,z6]),(0,[z1,z2,z24,z35,z8,z5,z6])],[(1,[z1,z2,z428,z8,z5,z6])],[(0,[z1,z2,z429,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z119,z6]),(0,[z40,z1,z2,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z141,z12]),(0,[z1,z2,z3,z8,z5,z6,z430]),(0,[z1,z82,z2,z24,z8,z5,z6]),(0,[z431,z1,z2,z3,z8,z5,z6])],[(0,[z40,z1,z2,z3,z8,z55,z6]),(0,[z1,z2,z3,z8,z5,z6,z432]),(0,[z1,z433,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z434,z5,z6])],[(0,[z1,z2,z3,z8,z69,z5,z31]),(0,[z1,z2,z3,z8,z5,z31,z280])],[(1,[z1,z2,z3,z8,z284,z6]),(0,[z21,z1,z2,z8,z147,z5,z6]),(0,[z1,z2,z3,z8,z94,z147,z6]),(0,[z1,z58,z2,z3,z8,z69,z6]),(0,[z1,z2,z3,z8,z5,z6,z435]),(1,[z1,z58,z3,z8,z73,z6]),(0,[z436,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z437,z6])],[(1,[z1,z2,z3,z285,z5,z6]),(0,[z21,z1,z2,z8,z5,z6,z12]),(0,[z1,z2,z3,z72,z34,z5,z6]),(1,[z1,z2,z81,z8,z5,z31]),(0,[z1,z2,z51,z33,z8,z5,z6]),(0,[z1,z2,z438,z3,z8,z5,z6])],[(0,[z1,z2,z439,z3,z8,z5,z6]),(0,[z1,z2,z65,z3,z8,z75,z6])],[(0,[z440,z13,z1,z2,z8,z5,z6]),(0,[z1,z2,z441,z3,z8,z5,z6]),(0,[z1,z2,z65,z442,z8,z5,z6])],[(0,[z443,z1,z2,z3,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z76,z6]),(1,[z1,z2,z107,z8,z5,z6])]],
   [[(0,[z444,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z31,z432]),(0,[z1,z58,z2,z409,z8,z5,z6])],[(1,[z0,z7,z3,z8,z5,z6]),(0,[z13,z1,z2,z248,z8,z5,z6])],[(0,[z13,z1,z2,z152,z8,z5,z6]),(1,[z1,z2,z226,z8,z5,z6]),(0,[z1,z2,z126,z8,z34,z5,z6])],[(0,[z445,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z12,z70]),(0,[z1,z2,z3,z8,z5,z11,z6])],[(0,[z1,z109,z2,z113,z8,z5,z6])],[(0,[z21,z1,z2,z195,z8,z5,z6]),(0,[z222,z1,z2,z3,z8,z346,z6]),(1,[z1,z2,z3,z8,z5,z160]),(0,[z1,z2,z3,z35,z8,z5,z12]),(0,[z1,z2,z3,z8,z446,z5,z6]),(1,[z1,z2,z3,z8,z5,z266]),(0,[z1,z2,z3,z8,z5,z6,z447])],[(0,[z1,z22,z2,z3,z8,z5,z6]),(0,[z1,z2,z67,z3,z8,z5,z31])],[(0,[z63,z2,z3,z8,z5,z6,z12]),(0,[z1,z2,z24,z448,z8,z5,z6]),(0,[z1,z2,z449,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z11,z6,z120])],[(0,[z1,z2,z3,z8,z450,z5,z6]),(0,[z1,z2,z449,z24,z8,z5,z6]),(0,[z1,z2,z451,z3,z8,z5,z6]),(0,[z1,z2,z3,z35,z8,z18,z6])],[(0,[z1,z2,z7,z3,z8,z5,z6]),(0,[z13,z1,z2,z8,z249,z5,z6]),(0,[z1,z2,z126,z3,z8,z141,z6]),(0,[z1,z2,z3,z8,z452,z5,z6])],[(0,[z21,z1,z2,z8,z5,z18,z6]),(0,[z1,z2,z3,z453,z8,z5,z31]),(0,[z1,z2,z65,z17,z8,z5,z6])],[(0,[z1,z2,z3,z454,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z223,z6]),(0,[z1,z2,z3,z8,z242,z5,z6]),(0,[z1,z2,z51,z3,z8,z5,z12])],[(1,[z13,z1,z2,z8,z5,z361]),(0,[z45,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z106,z17,z8,z5,z6]),(0,[z1,z455,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z90,z72,z5,z6]),(1,[z1,z2,z3,z8,z5,z174]),(0,[z1,z2,z3,z8,z75,z5,z31]),(0,[z1,z2,z456,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z249,z18])],[(0,[z1,z2,z3,z90,z8,z5,z6]),(0,[z1,z114,z2,z457,z8,z5,z6]),(0,[z1,z2,z175,z3,z8,z5,z6]),(0,[z1,z2,z458,z3,z8,z5,z6])],[(0,[z1,z2,z54,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z309,z5,z6])]],
   [[(1,[z1,z2,z146,z8,z5,z74]),(0,[z459,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z460,z6]),(0,[z1,z2,z17,z8,z5,z6,z120])],[(0,[z216,z1,z2,z17,z8,z5,z6]),(0,[z1,z2,z461,z3,z8,z5,z6]),(0,[z63,z1,z2,z3,z8,z5,z12]),(0,[z1,z2,z157,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z462,z6])],[(1,[z222,z2,z3,z72,z5,z6]),(0,[z1,z2,z351,z3,z8,z5,z6]),(0,[z1,z2,z3,z442,z8,z5,z6])],[(0,[z1,z2,z463,z3,z8,z5,z6]),(1,[z2,z3,z8,z5,z31,z12]),(0,[z1,z2,z355,z3,z8,z5,z6]),(0,[z1,z109,z2,z157,z3,z8,z5]),(0,[z464,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z465,z8,z5,z6]),(0,[z1,z2,z277,z3,z8,z5,z6])],[(0,[z246,z1,z2,z17,z8,z5,z6]),(1,[z1,z2,z3,z248,z5,z11])],[(1,[z1,z2,z3,z8,z93,z6]),(1,[z1,z2,z3,z8,z5,z12])],[(0,[z1,z2,z3,z8,z5,z166,z6]),(0,[z1,z2,z8,z94,z5,z141,z6])],[(1,[z1,z2,z413,z8,z5,z6]),(0,[z13,z1,z2,z8,z147,z5,z6]),(1,[z1,z2,z8,z368,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z466]),(0,[z1,z2,z3,z467,z8,z5,z6]),(0,[z1,z2,z106,z3,z8,z5,z74])],[(0,[z1,z468,z2,z3,z8,z5,z6])],[(0,[z13,z216,z1,z2,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z6,z12]),(0,[z1,z2,z8,z147,z5,z111,z6])],[(0,[z469,z13,z1,z2,z8,z5,z6]),(0,[z1,z2,z24,z286,z8,z5,z6])],[(0,[z1,z2,z24,z8,z108,z5,z6]),(0,[z1,z3,z8,z69,z5,z73,z6]),(0,[z1,z2,z3,z8,z5,z6,z470])],[(0,[z1,z471,z2,z3,z8,z5,z6]),(0,[z472,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z473,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z96,z6]),(0,[z1,z2,z191,z3,z8,z5,z6]),(0,[z40,z45,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z474,z5,z6]),(0,[z1,z2,z3,z8,z5,z475,z6]),(0,[z476,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z17,z8,z5,z6])]],
   [[(0,[z1,z2,z477,z3,z8,z5,z6]),(0,[z478,z1,z2,z3,z8,z5,z6]),(0,[z21,z1,z2,z3,z8,z5,z12]),(0,[z1,z2,z113,z3,z8,z5,z6]),(0,[z1,z2,z3,z479,z8,z5,z6]),(0,[z1,z2,z480,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z108,z5,z31]),(0,[z1,z2,z3,z8,z5,z6,z481])],[(0,[z13,z1,z2,z3,z8,z284,z6]),(0,[z1,z2,z3,z8,z69,z55,z6]),(0,[z1,z482,z2,z3,z8,z5,z31]),(0,[z1,z2,z3,z8,z483,z5,z6]),(0,[z484,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z485,z3,z8,z5,z6])],[(0,[z13,z1,z2,z195,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z5,z6]),(0,[z1,z2,z3,z8,z5,z12,z138]),(0,[z1,z2,z486,z3,z8,z5,z6]),(0,[z1,z2,z3,z487,z8,z5,z6])],[(0,[z1,z28,z2,z24,z8,z5,z6]),(0,[z13,z1,z2,z3,z285,z5,z6]),(0,[z1,z68,z2,z3,z8,z5,z31]),(0,[z1,z2,z17,z8,z5,z76,z6]),(0,[z488,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z489,z6])],[(0,[z21,z1,z2,z248,z8,z5,z6]),(0,[z1,z2,z17,z248,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z490])],[(0,[z1,z2,z3,z8,z5,z491,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z2,z8,z5,z18,z6]),(0,[z63,z21,z1,z2,z8,z5,z6]),(0,[z1,z2,z24,z8,z5,z141,z6]),(0,[z1,z492,z2,z3,z8,z5,z6]),(0,[z1,z58,z2,z3,z35,z8,z6])],[(0,[z0,z1,z28,z3,z8,z5,z6]),(0,[z1,z28,z2,z210,z8,z5,z6]),(0,[z255,z1,z2,z24,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z493]),(0,[z1,z2,z3,z494,z8,z5,z6])],[(0,[z1,z2,z286,z3,z8,z5,z31]),(0,[z1,z2,z3,z8,z5,z495,z6])],[(0,[z13,z40,z1,z2,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z236]),(0,[z1,z114,z2,z3,z8,z249,z5])],[(1,[z21,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z147,z141,z6]),(0,[z1,z114,z2,z3,z8,z5,z6]),(1,[z1,z2,z67,z8,z141,z6])],[(0,[z89,z1,z2,z3,z72,z5,z6]),(0,[z1,z2,z62,z3,z8,z5,z31]),(0,[z1,z496,z2,z3,z8,z5,z6])],[(0,[z21,z1,z2,z8,z249,z5,z6]),(0,[z497,z1,z2,z3,z8,z5,z6]),(0,[z1,z58,z2,z3,z8,z5,z12]),(0,[z1,z2,z17,z8,z249,z5,z6])],[(0,[z13,z222,z1,z2,z8,z5,z6]),(0,[z13,z1,z2,z33,z8,z5,z6]),(0,[z89,z1,z2,z24,z8,z5,z6])]],
   [[(0,[z1,z2,z498,z3,z8,z5,z6]),(1,[z1,z2,z17,z8,z5,z31])],[(0,[z1,z2,z3,z8,z499,z5,z6]),(0,[z21,z1,z114,z2,z8,z5,z6]),(0,[z1,z2,z500,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z73,z6]),(0,[z1,z501,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z12,z19]),(0,[z1,z2,z24,z8,z5,z6,z19]),(0,[z1,z2,z8,z34,z5,z141,z6]),(0,[z1,z2,z3,z8,z249,z5,z19])],[(0,[z21,z1,z2,z8,z34,z5,z6])],[(0,[z0,z1,z2,z24,z8,z5,z6]),(0,[z1,z2,z502,z3,z8,z5,z6]),(0,[z1,z2,z503,z17,z8,z5,z6])],[],[(0,[z1,z2,z3,z8,z5,z504,z6])],[(1,[z21,z1,z2,z8,z5,z96]),(0,[z1,z109,z2,z24,z8,z5,z6])],[(1,[z216,z28,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z505]),(0,[z1,z2,z3,z8,z506,z5,z6])],[(0,[z1,z2,z3,z8,z507,z5,z6]),(0,[z1,z114,z109,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z508,z6])],[(0,[z1,z509,z2,z3,z8,z5,z6]),(1,[z1,z2,z126,z8,z94,z6])],[(0,[z1,z2,z3,z8,z5,z66,z6]),(0,[z1,z510,z2,z3,z8,z5,z6])],[(0,[z13,z2,z3,z195,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z76,z12]),(0,[z1,z2,z3,z35,z8,z5,z31])],[(0,[z1,z2,z17,z8,z147,z5,z6]),(0,[z511,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z347,z8,z5,z6])],[(0,[z13,z1,z2,z3,z8,z5,z12]),(1,[z45,z2,z3,z8,z55,z6]),(0,[z1,z2,z3,z248,z8,z5,z12]),(1,[z1,z2,z8,z5,z6,z56]),(1,[z1,z2,z106,z8,z5,z278]),(0,[z1,z2,z3,z8,z5,z512,z6]),(0,[z1,z2,z3,z8,z5,z6,z116])],[(0,[z188,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z153,z8,z5,z12]),(0,[z1,z2,z17,z8,z5,z6,z12])]],
   [[(0,[z216,z1,z2,z3,z8,z5,z392]),(0,[z1,z14,z2,z3,z8,z5,z6]),(0,[z188,z1,z2,z24,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z513,z6]),(0,[z1,z2,z3,z514,z8,z5,z6])],[(0,[z1,z2,z254,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z77,z6]),(0,[z13,z1,z2,z8,z94,z5,z6]),(0,[z515,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z16,z3,z8,z6,z19])],[(0,[z13,z1,z2,z8,z5,z55,z6]),(0,[z1,z2,z516,z3,z8,z5,z6]),(0,[z517,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z16,z3,z8,z19])],[(0,[z1,z2,z3,z8,z5,z6,z518])],[(0,[z21,z1,z109,z2,z8,z5,z6]),(0,[z64,z1,z2,z3,z99,z5,z6]),(0,[z1,z2,z3,z8,z5,z519,z6])],[(0,[z520,z13,z1,z2,z8,z5,z6]),(0,[z1,z2,z521,z3,z8,z5,z6])],[(0,[z1,z7,z3,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z20]),(0,[z1,z2,z3,z8,z5,z12,z12]),(0,[z1,z2,z24,z8,z5,z6,z12]),(0,[z1,z2,z3,z8,z249,z5,z12]),(0,[z1,z2,z24,z8,z199,z5,z6]),(0,[z1,z2,z3,z522,z8,z5,z6]),(1,[z1,z2,z243,z3,z5,z6])],[(1,[z1,z2,z8,z5,z31,z56]),(0,[z64,z1,z82,z3,z8,z5,z6])],[(0,[z1,z2,z17,z195,z8,z5,z6]),(1,[z1,z2,z3,z8,z385,z6]),(0,[z1,z2,z3,z8,z523,z5,z6]),(0,[z1,z2,z409,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z174,z6]),(0,[z63,z1,z2,z3,z8,z5,z31]),(0,[z1,z82,z2,z3,z99,z5,z6])],[(0,[z1,z2,z3,z8,z524,z5,z6]),(0,[z1,z2,z525,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z526,z6])],[(0,[z13,z1,z28,z2,z8,z5,z6]),(0,[z527,z1,z2,z3,z8,z5,z6])],[(0,[z127,z1,z2,z3,z8,z5,z12]),(0,[z1,z2,z3,z8,z309,z5,z73]),(0,[z1,z2,z3,z8,z5,z6,z528]),(0,[z1,z2,z16,z3,z8,z5,z19])],[(0,[z1,z2,z7,z24,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z31]),(0,[z1,z2,z17,z8,z5,z18,z6]),(0,[z1,z114,z2,z157,z3,z8,z5])],[(0,[z529,z1,z2,z3,z8,z5,z6])],[(0,[z13,z1,z114,z2,z8,z5,z6]),(0,[z1,z2,z24,z195,z8,z5,z6])]],
   [[(0,[z45,z1,z2,z24,z8,z5,z6]),(0,[z1,z2,z530,z3,z8,z5,z6]),(0,[z1,z2,z3,z531,z8,z5,z6]),(0,[z1,z2,z532,z3,z8,z5,z6])],[(0,[z13,z1,z2,z8,z34,z5,z6]),(0,[z1,z2,z456,z24,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z533])],[(0,[z1,z2,z286,z17,z8,z5,z6]),(1,[z1,z114,z3,z8,z5,z115])],[(0,[z1,z2,z3,z248,z8,z5,z120])],[(0,[z13,z21,z1,z2,z8,z5,z6]),(0,[z21,z1,z2,z33,z8,z5,z6]),(0,[z1,z2,z146,z3,z8,z5,z12]),(0,[z1,z2,z17,z33,z8,z5,z6]),(0,[z1,z2,z24,z8,z5,z18,z6])],[(0,[z1,z2,z3,z534,z8,z5,z6]),(0,[z1,z2,z3,z8,z147,z5,z12]),(0,[z1,z2,z3,z8,z5,z190,z6]),(0,[z1,z2,z62,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z535]),(0,[z1,z2,z3,z8,z5,z6,z36])],[(0,[z40,z1,z2,z3,z8,z5,z6]),(0,[z1,z68,z2,z65,z3,z8,z6]),(0,[z1,z2,z3,z8,z5,z536,z6])],[],[(0,[z1,z2,z369,z8,z147,z5,z6]),(0,[z1,z2,z537,z3,z8,z5,z6]),(0,[z1,z2,z3,z538,z8,z5,z6]),(0,[z1,z2,z3,z539,z8,z5,z6])],[(0,[z1,z2,z3,z8,z540,z5,z6])],[(0,[z327,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z541,z8,z5,z6]),(0,[z222,z1,z2,z17,z8,z5,z6]),(1,[z1,z2,z24,z8,z5,z12]),(0,[z1,z2,z16,z3,z35,z8,z6])],[(0,[z13,z1,z2,z8,z5,z6,z278]),(0,[z1,z2,z3,z8,z5,z6,z6]),(0,[z1,z2,z3,z8,z5,z12,z120]),(0,[z1,z2,z24,z8,z5,z6,z120]),(0,[z1,z2,z62,z3,z34,z5,z6])],[(1,[z1,z2,z254,z8,z5,z6])],[(0,[z1,z2,z72,z8,z368,z5,z6]),(0,[z1,z82,z2,z3,z75,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z542])],[],[(0,[z1,z114,z2,z175,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z195,z8,z5,z12]),(0,[z45,z1,z2,z3,z8,z5,z110]),(0,[z1,z2,z16,z3,z8,z5,z12])],[(0,[z13,z21,z2,z3,z8,z5,z6]),(1,[z1,z2,z8,z242,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z292]),(0,[z1,z2,z3,z8,z5,z6,z543])],[(0,[z544,z13,z1,z2,z8,z5,z6]),(0,[z13,z1,z109,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z545])],[(0,[z546,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z346,z6]),(0,[z64,z1,z2,z258,z8,z5,z6]),(0,[z1,z68,z2,z407,z8,z5,z6])],[(0,[z547,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z31,z6]),(0,[z1,z2,z3,z8,z548,z5,z6]),(0,[z1,z2,z477,z24,z8,z5,z6]),(0,[z1,z2,z3,z549,z8,z5,z6])],[(0,[z1,z2,z3,z35,z8,z55,z6]),(0,[z1,z2,z3,z8,z5,z18,z12]),(0,[z1,z2,z3,z8,z37,z5,z6]),(0,[z1,z2,z336,z3,z8,z5,z73])],[(0,[z1,z1,z2,z3,z8,z5,z6]),(0,[z21,z1,z2,z8,z94,z5,z6]),(0,[z1,z2,z17,z8,z94,z5,z6]),(0,[z1,z2,z3,z8,z5,z550,z6])],[(0,[z21,z1,z2,z8,z5,z55,z6]),(0,[z1,z2,z17,z8,z5,z55,z6]),(0,[z1,z129,z2,z3,z8,z5,z31])],[(0,[z551,z1,z2,z3,z8,z5,z6]),(0,[z1,z58,z3,z8,z5,z73,z6])],[(0,[z1,z2,z126,z3,z8,z5,z31]),(0,[z1,z2,z552,z3,z8,z5,z76])],[(0,[z21,z1,z2,z8,z5,z115,z6]),(0,[z1,z2,z65,z3,z8,z5,z6])],[],[(0,[z440,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z110]),(0,[z1,z2,z3,z33,z8,z5,z12]),(0,[z215,z1,z2,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z553,z5,z6]),(0,[z1,z554,z2,z3,z8,z5,z6]),(0,[z1,z2,z106,z3,z8,z5,z6])],[(0,[z1,z2,z157,z3,z8,z5,z11])],[(0,[z13,z1,z2,z8,z5,z6,z280]),(0,[z1,z2,z3,z8,z5,z555,z6]),(0,[z1,z2,z24,z8,z5,z76,z6]),(0,[z1,z109,z2,z3,z248,z8,z5]),(0,[z1,z2,z3,z556,z8,z5,z6]),(0,[z1,z2,z16,z3,z8,z249,z6])],[(1,[z1,z2,z163,z8,z5,z6]),(0,[z1,z2,z3,z557,z8,z5,z6])]],
   [[(0,[z21,z1,z28,z2,z8,z5,z6]),(0,[z1,z2,z3,z33,z108,z5,z6]),(0,[z1,z2,z3,z8,z5,z141,z31]),(0,[z1,z114,z2,z24,z8,z5,z6]),(0,[z1,z2,z24,z248,z8,z5,z6]),(0,[z1,z558,z2,z3,z8,z5,z6])],[(0,[z89,z2,z3,z8,z108,z5,z6]),(0,[z1,z2,z67,z17,z8,z5,z6]),(0,[z1,z2,z157,z3,z8,z249,z5])],[(0,[z216,z1,z2,z3,z8,z5,z6]),(0,[z1,z559,z2,z3,z8,z5,z6]),(0,[z13,z1,z2,z16,z8,z5,z6]),(0,[z1,z2,z157,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z560,z5,z6]),(0,[z1,z2,z3,z108,z34,z5,z6]),(0,[z1,z2,z3,z8,z5,z76,z31]),(0,[z1,z2,z3,z8,z561,z5,z6])],[(0,[z562,z1,z2,z3,z8,z5,z6]),(0,[z102,z13,z1,z2,z8,z5,z6]),(0,[z89,z1,z2,z3,z8,z5,z403]),(0,[z1,z2,z3,z8,z5,z6,z563]),(0,[z1,z2,z3,z8,z5,z564,z6])],[(0,[z13,z1,z2,z3,z8,z5,z31]),(0,[z246,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z149,z8,z5,z6])],[(0,[z13,z1,z2,z7,z8,z5,z6]),(0,[z1,z2,z565,z3,z8,z5,z6]),(0,[z1,z2,z17,z8,z34,z5,z6])],[(0,[z13,z1,z2,z126,z8,z5,z6]),(0,[z1,z2,z3,z566,z8,z5,z6]),(0,[z1,z68,z3,z8,z69,z5,z6]),(0,[z567,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z568,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z569,z6]),(0,[z1,z80,z2,z3,z8,z5,z12]),(0,[z1,z2,z570,z17,z8,z5,z6]),(0,[z1,z2,z24,z8,z249,z5,z6]),(0,[z1,z2,z3,z8,z5,z571,z6])],[(0,[z21,z21,z1,z2,z8,z5,z6])],[(1,[z1,z2,z3,z8,z5,z361]),(0,[z1,z2,z252,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z162,z31]),(0,[z1,z2,z3,z8,z572,z5,z6]),(0,[z1,z2,z3,z8,z5,z573,z6]),(0,[z1,z574,z2,z3,z8,z5,z6])],[(1,[z127,z2,z3,z8,z5,z31]),(0,[z1,z2,z62,z51,z8,z5,z6]),(0,[z575,z1,z2,z3,z8,z5,z6]),(0,[z1,z576,z2,z3,z8,z5,z6])],[(0,[z1,z2,z348,z3,z8,z5,z6])],[(0,[z13,z1,z2,z8,z5,z6,z361]),(0,[z1,z2,z577,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z94,z5,z12])],[(1,[z13,z1,z2,z8,z66,z6]),(0,[z1,z2,z3,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z55,z12]),(0,[z1,z2,z3,z578,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z6,z143]),(0,[z21,z1,z2,z8,z5,z6,z278]),(0,[z1,z2,z17,z8,z5,z6,z278])],[(0,[z1,z2,z3,z8,z5,z579,z6]),(0,[z1,z2,z8,z5,z306,z6,z12]),(0,[z1,z2,z3,z8,z99,z5,z6])],[(1,[z1,z2,z83,z8,z5,z6]),(0,[z1,z2,z3,z580,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z581])],[(0,[z1,z2,z65,z3,z5,z11,z6])],[(0,[z241,z21,z1,z2,z8,z5,z6]),(0,[z1,z82,z3,z90,z8,z5,z6]),(0,[z1,z2,z582,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z5,z211]),(0,[z1,z2,z51,z3,z8,z5,z31])],[(0,[z45,z1,z2,z3,z8,z147,z6]),(0,[z1,z2,z3,z86,z8,z5,z6]),(0,[z1,z2,z583,z3,z8,z5,z6])],[(0,[z1,z584,z2,z3,z8,z5,z6]),(0,[z305,z1,z2,z3,z8,z5,z6]),(0,[z1,z585,z2,z3,z8,z5,z6]),(0,[z1,z2,z24,z8,z147,z5,z6]),(0,[z64,z1,z2,z423,z8,z5,z6]),(0,[z1,z2,z3,z8,z586,z5,z6])],[(0,[z13,z1,z2,z8,z5,z115,z6]),(0,[z1,z68,z2,z467,z8,z5,z6]),(0,[z1,z2,z243,z3,z5,z6,z19]),(0,[z587,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z588,z6]),(0,[z1,z2,z3,z8,z589,z5,z6])],[(0,[z21,z1,z2,z8,z5,z74,z6]),(1,[z40,z2,z3,z8,z147,z6]),(0,[z1,z2,z3,z8,z5,z57,z31]),(0,[z1,z2,z590,z3,z8,z5,z6])],[],[(0,[z13,z1,z2,z90,z8,z5,z6]),(0,[z1,z2,z3,z8,z147,z5,z31]),(1,[z1,z2,z407,z8,z5,z6]),(0,[z1,z2,z591,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z249,z18,z6])],[],[(0,[z21,z1,z82,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z592,z5,z6]),(0,[z1,z2,z3,z8,z34,z5,z12]),(0,[z1,z2,z3,z8,z593,z5,z6]),(0,[z1,z2,z3,z8,z5,z594,z6])],[(0,[z262,z21,z1,z2,z8,z5,z6]),(0,[z45,z1,z2,z3,z8,z5,z196]),(0,[z1,z68,z2,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z595,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z111,z6]),(0,[z1,z2,z596,z3,z8,z5,z6])],[(1,[z1,z2,z24,z8,z5,z31]),(0,[z1,z2,z17,z334,z8,z5,z6]),(1,[z1,z2,z530,z3,z8,z6]),(0,[z1,z597,z2,z3,z8,z5,z6])],[(0,[z21,z1,z2,z8,z5,z337,z6]),(0,[z1,z2,z3,z598,z8,z5,z6])],[(0,[z21,z1,z2,z8,z5,z6,z280]),(0,[z1,z2,z17,z8,z5,z6,z280]),(0,[z1,z2,z17,z8,z419,z5,z6])],[(0,[z1,z2,z503,z3,z8,z5,z6])],[(0,[z328,z1,z2,z3,z8,z5,z6]),(0,[z599,z1,z2,z3,z8,z5,z6]),(0,[z1,z600,z2,z3,z8,z5,z6]),(0,[z1,z2,z146,z3,z8,z5,z278])],[],[(0,[z216,z1,z2,z3,z8,z5,z143]),(0,[z1,z2,z3,z195,z8,z5,z31]),(0,[z21,z1,z2,z16,z8,z5,z6]),(0,[z601,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z602,z3,z8,z5,z6]),(0,[z1,z2,z3,z603,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z604,z6]),(1,[z1,z2,z552,z3,z8,z5])],[(0,[z1,z605,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z72,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z306,z12]),(0,[z1,z2,z2,z17,z8,z5,z6]),(0,[z1,z2,z17,z8,z5,z6,z430]),(0,[z1,z2,z3,z606,z8,z99,z5]),(0,[z1,z2,z3,z607,z8,z5,z6])],[(0,[z21,z1,z2,z8,z5,z6,z354]),(0,[z21,z1,z2,z3,z8,z5,z31]),(0,[z40,z1,z2,z24,z8,z5,z6]),(1,[z1,z2,z369,z8,z5,z6]),(0,[z1,z2,z608,z3,z8,z5,z6]),(0,[z1,z2,z3,z35,z8,z75,z6])],[(0,[z21,z1,z2,z7,z8,z5,z6]),(1,[z1,z393,z2,z8,z5,z6]),(0,[z64,z1,z2,z3,z75,z5,z6]),(0,[z1,z2,z609,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z610,z5,z6])],[(0,[z21,z1,z2,z126,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z18,z31]),(0,[z1,z2,z537,z24,z8,z5,z6]),(0,[z1,z82,z2,z226,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z611]),(0,[z1,z2,z3,z8,z612,z5,z6])],[(0,[z1,z2,z3,z8,z41,z5,z6]),(0,[z1,z2,z3,z197,z8,z5,z6])],[(0,[z1,z2,z24,z33,z8,z5,z6])],[]],
   [[(1,[z1,z2,z54,z8,z5,z6]),(0,[z1,z80,z3,z17,z8,z5,z6])],[],[(0,[z13,z1,z2,z3,z8,z5,z361]),(0,[z613,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z614,z3,z8,z5,z6]),(0,[z1,z2,z225,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z615])],[(0,[z89,z222,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z457,z8,z5,z6])],[(0,[z127,z21,z1,z2,z8,z5,z6]),(1,[z21,z2,z286,z8,z5,z6]),(0,[z222,z1,z2,z3,z8,z5,z20]),(0,[z616,z1,z2,z3,z8,z5,z6])],[(0,[z1,z393,z2,z3,z8,z5,z6]),(0,[z617,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z618,z6]),(0,[z1,z58,z68,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z619,z5,z6]),(0,[z1,z2,z3,z8,z5,z620,z6])],[(1,[z1,z26,z3,z8,z5,z6]),(1,[z63,z2,z3,z8,z5,z12]),(0,[z1,z109,z3,z8,z5,z6,z280]),(0,[z1,z114,z2,z3,z248,z8,z5])],[(0,[z13,z1,z2,z8,z5,z74,z6]),(0,[z1,z58,z2,z3,z8,z5,z31])],[],[(1,[z13,z1,z2,z8,z5,z6]),(0,[z89,z1,z2,z3,z108,z5,z6]),(0,[z222,z2,z3,z72,z8,z5,z6]),(1,[z1,z2,z3,z259,z5,z6]),(0,[z1,z2,z3,z8,z5,z621,z6])],[(0,[z216,z1,z28,z3,z8,z5,z6]),(0,[z21,z1,z2,z8,z450,z5,z6]),(0,[z64,z1,z2,z3,z8,z5,z12]),(0,[z1,z2,z552,z3,z8,z5,z6])],[(0,[z13,z1,z82,z2,z8,z5,z6]),(0,[z1,z2,z622,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z623,z5,z6]),(0,[z1,z2,z65,z3,z72,z5,z6]),(0,[z1,z2,z3,z8,z624,z5,z6]),(1,[z1,z2,z442,z8,z5,z6])],[(0,[z13,z1,z2,z3,z8,z5,z211]),(0,[z1,z2,z24,z3,z8,z5,z12]),(0,[z1,z2,z17,z8,z5,z115,z6]),(0,[z1,z2,z51,z17,z8,z5,z6])],[(0,[z246,z1,z28,z3,z8,z5,z6]),(0,[z21,z1,z605,z2,z8,z5,z6]),(0,[z1,z2,z65,z24,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z625,z6]),(0,[z1,z2,z626,z3,z8,z5,z6])],[(0,[z1,z80,z2,z3,z8,z5,z31])]],
   [[(0,[z1,z82,z2,z3,z8,z5,z12]),(0,[z1,z2,z24,z8,z94,z5,z6]),(0,[z1,z2,z106,z24,z8,z5,z6]),(1,[z1,z2,z62,z34,z5,z6])],[(0,[z21,z1,z2,z90,z8,z5,z6]),(0,[z1,z2,z24,z8,z5,z55,z6]),(0,[z1,z2,z17,z90,z8,z5,z6]),(1,[z1,z2,z467,z8,z5,z6])],[(0,[z627,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z286,z3,z8,z5,z6])],[(0,[z520,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z237,z6]),(0,[z1,z2,z51,z3,z34,z5,z6]),(0,[z1,z2,z3,z8,z5,z628,z6])],[(1,[z1,z2,z3,z8,z5,z354]),(0,[z1,z2,z3,z8,z5,z403,z6]),(0,[z63,z1,z2,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z629,z6]),(0,[z1,z2,z24,z8,z5,z115,z6]),(1,[z1,z2,z3,z149,z8,z6]),(0,[z630,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z631,z8,z5,z6]),(0,[z1,z2,z62,z3,z8,z5,z6])],[(0,[z216,z1,z2,z24,z8,z5,z6]),(1,[z1,z2,z244,z8,z5,z6]),(0,[z1,z2,z157,z24,z8,z5,z6])],[(0,[z632,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z633,z5,z6]),(0,[z1,z2,z634,z3,z8,z5,z6])],[(0,[z1,z2,z3,z248,z8,z5,z31]),(1,[z1,z2,z17,z8,z5,z6]),(0,[z1,z2,z3,z308,z8,z5,z6]),(0,[z1,z2,z126,z51,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z196,z6]),(0,[z246,z1,z2,z24,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z635]),(0,[z1,z636,z2,z3,z8,z5,z6])],[(1,[z13,z1,z2,z152,z5,z6]),(0,[z222,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z637]),(0,[z1,z68,z2,z3,z8,z73,z6]),(1,[z1,z109,z3,z8,z5,z280])],[(0,[z1,z2,z638,z3,z8,z5,z6]),(0,[z639,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z428,z3,z8,z5,z6]),(1,[z246,z1,z24,z8,z5,z6]),(0,[z1,z2,z67,z3,z8,z94,z6])],[],[(0,[z1,z640,z2,z3,z8,z5,z6]),(0,[z21,z1,z2,z3,z8,z5,z354]),(0,[z1,z2,z24,z8,z5,z287,z6]),(0,[z1,z2,z3,z8,z5,z641,z6]),(0,[z1,z2,z146,z8,z5,z74,z6]),(0,[z642,z1,z2,z3,z8,z5,z6])],[(0,[z255,z216,z1,z2,z8,z5,z6]),(0,[z1,z2,z146,z3,z8,z5,z74]),(0,[z1,z2,z3,z643,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z249,z5,z31]),(0,[z23,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z24,z8,z34,z5,z6])],[(0,[z1,z2,z3,z644,z8,z5,z6]),(0,[z1,z645,z2,z3,z8,z5,z6]),(0,[z21,z1,z2,z8,z5,z96,z6]),(0,[z64,z21,z1,z2,z8,z5,z6])],[(0,[z646,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z304]),(0,[z1,z2,z3,z8,z220,z5,z6])],[(0,[z1,z2,z3,z8,z647,z5,z6])],[(0,[z13,z1,z2,z8,z5,z11,z6]),(0,[z13,z1,z2,z51,z8,z5,z6]),(0,[z1,z2,z3,z8,z268,z5,z6]),(0,[z1,z2,z3,z648,z8,z5,z6]),(0,[z1,z2,z3,z8,z69,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z649]),(0,[z1,z2,z3,z8,z650,z5,z6])],[(0,[z1,z2,z3,z8,z5,z115,z12]),(0,[z1,z2,z244,z8,z5,z6,z12]),(0,[z1,z2,z3,z8,z34,z5,z31]),(0,[z1,z2,z3,z8,z291,z5,z31])],[(0,[z1,z2,z3,z8,z5,z651,z6]),(0,[z1,z2,z3,z652,z8,z5,z6]),(0,[z127,z1,z2,z3,z8,z5,z31])],[(0,[z1,z2,z653,z3,z8,z5,z6]),(1,[z1,z2,z81,z8,z5,z6])],[(0,[z1,z2,z3,z210,z8,z5,z6]),(0,[z1,z2,z17,z8,z5,z489,z6])],[(0,[z1,z2,z3,z90,z8,z5,z12]),(0,[z1,z2,z654,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z12,z278]),(0,[z1,z2,z24,z8,z5,z6,z278])],[(0,[z1,z2,z26,z3,z8,z5,z6])],[(0,[z215,z1,z2,z3,z8,z5,z6]),(0,[z1,z655,z2,z3,z8,z5,z6]),(0,[z469,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z460,z12]),(0,[z1,z2,z3,z8,z5,z6,z656]),(0,[z1,z2,z3,z8,z657,z5,z6])],[(0,[z1,z2,z3,z90,z108,z5,z6]),(0,[z1,z2,z17,z8,z5,z74,z6])],[(0,[z1,z2,z3,z8,z285,z5,z6]),(0,[z1,z2,z146,z3,z8,z5,z31])],[(0,[z13,z1,z26,z3,z8,z5,z6]),(0,[z13,z1,z2,z146,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z658,z6])]],
   [[(0,[z544,z1,z2,z3,z8,z5,z6]),(0,[z40,z1,z2,z3,z8,z147,z6])],[(0,[z1,z2,z67,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z659,z6])],[(0,[z13,z13,z1,z2,z8,z5,z6])],[(0,[z1,z2,z382,z3,z8,z5,z6]),(1,[z1,z2,z157,z3,z5,z120])],[(0,[z1,z2,z3,z8,z5,z660,z6]),(0,[z1,z2,z3,z8,z5,z6,z661]),(0,[z21,z1,z2,z8,z5,z73,z6]),(0,[z1,z468,z2,z3,z8,z5,z12]),(0,[z1,z2,z126,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z662,z6])],[(0,[z1,z2,z387,z3,z8,z5,z12]),(0,[z1,z2,z3,z453,z8,z5,z6]),(0,[z1,z663,z2,z3,z8,z5,z6])],[(1,[z1,z312,z2,z8,z5,z6]),(0,[z1,z312,z2,z7,z8,z5,z6]),(0,[z1,z82,z2,z65,z3,z5,z6]),(1,[z1,z2,z347,z8,z5,z6])],[(0,[z0,z216,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z448,z8,z5,z6]),(1,[z64,z1,z3,z99,z5,z6]),(0,[z1,z2,z530,z3,z8,z99,z6]),(0,[z1,z2,z664,z3,z8,z5,z6]),(0,[z1,z2,z8,z5,z74,z6,z278])],[(0,[z1,z2,z570,z3,z8,z5,z6]),(0,[z1,z2,z65,z277,z8,z5,z6]),(0,[z1,z2,z3,z8,z75,z5,z6])],[(0,[z2,z286,z3,z195,z8,z5,z6]),(0,[z1,z2,z665,z3,z8,z5,z6])],[(1,[z1,z14,z3,z8,z5,z6]),(0,[z414,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z16,z3,z8,z5,z31]),(0,[z1,z58,z2,z65,z3,z8,z6]),(0,[z1,z2,z3,z8,z5,z666,z6])],[(0,[z1,z2,z3,z8,z667,z5,z6])],[(0,[z1,z2,z3,z8,z5,z12,z417]),(0,[z1,z2,z3,z606,z8,z5,z6]),(0,[z1,z2,z126,z3,z8,z94,z6]),(0,[z1,z2,z65,z3,z35,z5,z6]),(0,[z1,z2,z3,z8,z5,z668,z6])],[(1,[z13,z21,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z12,z280]),(0,[z1,z2,z24,z8,z5,z6,z280])],[(0,[z1,z28,z2,z3,z8,z5,z12]),(0,[z1,z2,z608,z24,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z331,z31])]],
   [[(0,[z1,z2,z3,z669,z8,z5,z6]),(0,[z1,z28,z2,z413,z8,z5,z6]),(0,[z13,z1,z2,z17,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z670,z6])],[(0,[z64,z1,z2,z3,z8,z5,z31])],[(0,[z1,z2,z105,z3,z8,z99,z5])],[(0,[z1,z2,z3,z8,z5,z211,z6]),(0,[z1,z2,z65,z3,z8,z147,z6]),(0,[z1,z2,z24,z3,z8,z5,z31]),(0,[z1,z2,z342,z3,z8,z5,z31]),(0,[z1,z2,z671,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z304,z6]),(0,[z1,z2,z3,z8,z5,z74,z12]),(1,[z23,z1,z2,z8,z5,z6]),(0,[z1,z2,z112,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z672,z5,z6])],[(0,[z673,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z392]),(0,[z1,z2,z428,z8,z108,z5,z6]),(0,[z1,z674,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z33,z8,z5,z31]),(0,[z675,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z676,z6])],[(0,[z1,z82,z2,z3,z8,z5,z31])],[(0,[z246,z1,z24,z3,z8,z5,z6])],[(0,[z303,z13,z1,z2,z8,z5,z6]),(0,[z21,z1,z2,z8,z5,z11,z6]),(0,[z21,z1,z2,z51,z8,z5,z6]),(0,[z89,z1,z2,z3,z8,z5,z12]),(0,[z1,z2,z244,z3,z8,z5,z12]),(0,[z1,z2,z17,z8,z5,z11,z6]),(0,[z1,z2,z125,z3,z8,z5,z6]),(0,[z1,z2,z677,z3,z8,z5,z6]),(0,[z1,z2,z678,z3,z8,z5,z6])],[(1,[z1,z2,z3,z606,z8,z5]),(0,[z1,z2,z3,z679,z8,z5,z6]),(0,[z1,z680,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z681,z5,z6]),(0,[z1,z682,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z683,z5,z6])],[(0,[z1,z2,z3,z8,z108,z5,z6]),(0,[z1,z2,z3,z8,z55,z141,z6])],[(0,[z1,z482,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z66,z6]),(0,[z1,z2,z3,z72,z99,z5,z6]),(0,[z1,z2,z71,z72,z8,z5,z6]),(0,[z1,z684,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z685,z5,z6]),(0,[z1,z2,z65,z16,z3,z8,z6])],[(0,[z0,z1,z2,z3,z8,z93,z6]),(0,[z0,z1,z2,z3,z8,z5,z12]),(0,[z1,z2,z3,z8,z686,z5,z6])],[(1,[z1,z2,z8,z5,z306,z12]),(0,[z1,z2,z687,z3,z8,z5,z6]),(0,[z1,z68,z2,z3,z8,z5,z6]),(0,[z1,z2,z688,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z689,z3,z8,z5,z6]),(0,[z1,z109,z2,z3,z8,z5,z115])],[(1,[z1,z28,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z690]),(0,[z1,z109,z2,z3,z8,z5,z12]),(0,[z1,z2,z3,z8,z691,z5,z6]),(0,[z1,z2,z126,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z692,z6]),(0,[z1,z2,z3,z8,z5,z693,z6])],[(0,[z13,z1,z2,z8,z5,z73,z6]),(0,[z694,z1,z2,z3,z8,z5,z6])],[(0,[z695,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z125,z3,z5,z6]),(0,[z1,z2,z3,z8,z696,z5,z6])],[(0,[z21,z1,z2,z146,z8,z5,z6]),(0,[z1,z2,z24,z8,z371,z5,z6])],[(0,[z1,z3,z8,z5,z115,z6,z280]),(0,[z1,z2,z697,z3,z8,z5,z6]),(0,[z1,z698,z2,z3,z8,z5,z6])],[(0,[z699,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z146,z17,z8,z5,z6])],[(0,[z13,z89,z1,z2,z8,z5,z6]),(0,[z1,z2,z184,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z94,z5,z31]),(0,[z1,z2,z423,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z700])],[(0,[z1,z2,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z55,z31]),(0,[z1,z2,z62,z24,z8,z5,z6])],[(0,[z1,z2,z3,z8,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z701,z6]),(0,[z405,z21,z1,z2,z8,z5,z6]),(0,[z188,z1,z2,z3,z8,z5,z12]),(0,[z1,z2,z3,z8,z5,z400,z6]),(1,[z1,z2,z457,z8,z5,z6]),(0,[z1,z114,z3,z8,z5,z115,z6])],[(0,[z13,z45,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z284,z5,z6]),(0,[z1,z2,z702,z3,z8,z5,z6]),(0,[z1,z2,z439,z3,z8,z5,z12]),(0,[z1,z2,z24,z90,z8,z5,z6])],[(0,[z13,z1,z2,z8,z5,z66,z6]),(0,[z222,z1,z2,z3,z72,z5,z6]),(0,[z1,z2,z3,z8,z5,z115,z31]),(0,[z1,z703,z2,z3,z8,z5,z6]),(0,[z1,z2,z704,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z705,z5,z6]),(0,[z1,z2,z3,z706,z8,z5,z6])],[(0,[z0,z1,z2,z3,z318,z5,z6]),(0,[z89,z1,z2,z3,z8,z5,z236]),(0,[z222,z1,z2,z24,z8,z5,z6])],[(0,[z89,z21,z1,z2,z8,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z26,z16,z8,z5,z6]),(0,[z1,z58,z26,z8,z5,z6]),(0,[z1,z2,z8,z5,z74,z354]),(0,[z1,z2,z33,z707,z5,z6])],[(0,[z1,z2,z3,z8,z708,z6]),(0,[z1,z14,z413,z8,z5,z6]),(0,[z1,z2,z3,z8,z709,z6]),(0,[z1,z2,z86,z8,z5,z12]),(0,[z1,z2,z710,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z711]),(0,[z1,z425,z17,z8,z5,z6]),(0,[z1,z2,z712,z3,z5,z31])],[(0,[z1,z26,z3,z8,z5,z31]),(0,[z1,z80,z26,z8,z5,z6]),(0,[z1,z713,z3,z8,z5,z6]),(0,[z1,z2,z244,z8,z5,z74])],[(0,[z1,z26,z7,z8,z5,z6]),(0,[z89,z2,z3,z714,z5,z6]),(0,[z1,z2,z715,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z716]),(0,[z1,z2,z24,z717,z5,z6]),(0,[z1,z362,z24,z8,z5,z6]),(0,[z64,z1,z3,z149,z99,z6])],[(0,[z13,z21,z14,z8,z5,z6]),(0,[z1,z718,z26,z8,z5,z6]),(0,[z1,z26,z126,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z719]),(0,[z1,z2,z3,z8,z720,z6]),(0,[z45,z2,z17,z8,z55,z6]),(0,[z1,z2,z225,z3,z8,z6])],[(0,[z13,z2,z8,z108,z5,z12]),(0,[z89,z2,z24,z108,z5,z6]),(0,[z1,z2,z3,z259,z5,z31]),(0,[z1,z2,z721,z17,z5,z6])],[(0,[z722,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z723])],[(0,[z255,z1,z2,z8,z5,z724]),(0,[z13,z1,z2,z8,z66,z361]),(1,[z2,z3,z714,z5,z6]),(0,[z1,z2,z725,z8,z5,z6])],[(0,[z46,z1,z26,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z726]),(0,[z1,z2,z8,z5,z74,z361]),(0,[z1,z2,z17,z8,z5,z211]),(0,[z1,z2,z33,z450,z5,z6]),(0,[z1,z2,z16,z3,z8,z333]),(0,[z1,z2,z3,z8,z6,z727])],[(0,[z1,z2,z3,z318,z5,z6]),(0,[z1,z1,z26,z8,z5,z6]),(0,[z1,z370,z24,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z728])],[(0,[z13,z1,z2,z152,z5,z211]),(0,[z1,z2,z729,z8,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z23,z2,z7,z8,z5,z6]),(0,[z1,z26,z8,z5,z6,z361]),(0,[z1,z2,z24,z8,z5,z403]),(0,[z121,z2,z3,z8,z5,z12]),(0,[z1,z2,z62,z34,z5,z31]),(0,[z1,z2,z17,z8,z5,z730])],[(1,[z731,z3,z8,z5,z6]),(0,[z13,z1,z2,z8,z732,z6]),(0,[z544,z1,z2,z152,z5,z6]),(0,[z733,z1,z2,z8,z5,z6]),(0,[z1,z2,z734,z8,z5,z6]),(0,[z1,z2,z735,z8,z5,z6]),(0,[z1,z2,z467,z8,z5,z31])],[(0,[z736,z1,z2,z8,z5,z6]),(0,[z40,z2,z17,z8,z147,z6]),(0,[z1,z2,z8,z5,z6,z737]),(0,[z23,z1,z2,z8,z5,z738]),(0,[z1,z2,z3,z8,z18,z493])],[(0,[z1,z2,z17,z8,z385,z6])]],
   [[(0,[z1,z2,z8,z739,z5,z6]),(0,[z13,z127,z2,z8,z5,z31]),(0,[z21,z1,z2,z125,z5,z6]),(0,[z575,z2,z3,z108,z5,z6]),(0,[z1,z2,z3,z149,z8,z31]),(0,[z1,z2,z65,z3,z221,z6])],[(0,[z1,z2,z740,z8,z5,z6]),(0,[z64,z1,z26,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z741]),(0,[z1,z2,z3,z8,z742,z5]),(0,[z1,z2,z342,z3,z5,z388])],[(0,[z1,z2,z3,z8,z66,z12]),(0,[z1,z3,z8,z5,z743,z6]),(0,[z2,z3,z8,z5,z12,z528])],[(1,[z2,z744,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z745]),(0,[z1,z2,z746,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z747])],[(0,[z215,z1,z7,z8,z5,z6]),(0,[z21,z1,z2,z8,z5,z748]),(0,[z1,z2,z8,z220,z141,z6]),(0,[z1,z2,z17,z8,z5,z31])],[(0,[z1,z2,z8,z5,z749,z6]),(0,[z1,z2,z3,z750,z5,z6]),(0,[z1,z2,z62,z285,z5,z6]),(0,[z1,z2,z8,z94,z66,z6]),(0,[z21,z1,z2,z35,z75,z6]),(0,[z1,z402,z3,z90,z5,z6]),(0,[z613,z2,z3,z8,z5,z31]),(0,[z1,z2,z751,z8,z5,z6]),(0,[z1,z2,z752,z8,z5,z6])],[(0,[z13,z1,z2,z152,z5,z31]),(0,[z1,z2,z3,z8,z5,z753])],[(0,[z1,z754,z2,z8,z5,z6]),(0,[z1,z2,z8,z5,z755,z6]),(0,[z1,z2,z756,z8,z5,z6]),(0,[z1,z2,z8,z5,z31,z737]),(0,[z1,z757,z2,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z52]),(0,[z255,z1,z2,z8,z758,z6]),(0,[z1,z2,z81,z8,z5,z211]),(0,[z1,z2,z8,z5,z306,z6]),(0,[z1,z2,z146,z8,z5,z56])],[(0,[z1,z2,z8,z759,z5,z6]),(0,[z1,z2,z8,z760,z5,z6]),(0,[z1,z2,z570,z8,z5,z74]),(0,[z1,z2,z3,z8,z761,z6]),(0,[z1,z2,z8,z5,z762,z6])],[(0,[z13,z21,z2,z8,z5,z354]),(0,[z1,z26,z90,z8,z5,z6]),(0,[z1,z2,z763,z3,z5,z6]),(0,[z1,z2,z764,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z765])],[(0,[z21,z1,z2,z8,z5,z96]),(0,[z1,z2,z3,z8,z12,z36]),(0,[z1,z3,z90,z766,z5,z6])],[(0,[z216,z28,z3,z8,z5,z6]),(0,[z1,z68,z26,z8,z5,z6]),(0,[z1,z2,z428,z8,z5,z6]),(0,[z1,z2,z387,z8,z5,z306]),(0,[z1,z2,z3,z8,z5,z767]),(0,[z1,z2,z3,z35,z768,z6])],[(0,[z13,z1,z2,z8,z769,z6]),(0,[z1,z252,z17,z8,z5,z6]),(0,[z1,z2,z8,z770,z5,z6]),(0,[z1,z2,z125,z17,z5,z6]),(0,[z1,z2,z125,z771,z5,z6]),(0,[z1,z2,z772,z8,z5,z6]),(0,[z1,z2,z8,z5,z773,z6])],[(0,[z1,z774,z3,z8,z5,z6]),(0,[z137,z2,z3,z8,z55,z6]),(0,[z1,z2,z775,z8,z5,z31]),(0,[z1,z2,z126,z8,z94,z6])],[(0,[z1,z2,z457,z8,z5,z12])]],
   [[(0,[z13,z1,z2,z259,z5,z6]),(0,[z21,z1,z2,z8,z776,z6]),(0,[z1,z2,z777,z3,z8,z5])],[(0,[z1,z2,z3,z778,z5,z6]),(0,[z13,z1,z2,z8,z779,z6]),(0,[z13,z1,z68,z8,z69,z6]),(0,[z13,z1,z114,z8,z5,z115]),(0,[z1,z2,z3,z8,z284,z6]),(0,[z1,z577,z17,z8,z5,z6]),(0,[z1,z2,z8,z780,z5,z6]),(0,[z1,z58,z3,z8,z73,z6])],[(0,[z1,z2,z781,z8,z5,z6]),(0,[z1,z2,z24,z8,z284,z6]),(0,[z1,z2,z8,z5,z6,z56]),(0,[z1,z2,z782,z8,z5,z6])],[(0,[z13,z21,z2,z8,z5,z361]),(0,[z1,z2,z3,z285,z5,z6]),(0,[z1,z2,z783,z8,z5,z6]),(0,[z1,z2,z81,z8,z5,z31]),(0,[z376,z2,z3,z8,z5,z12]),(0,[z1,z2,z8,z5,z6,z784]),(0,[z1,z2,z3,z8,z785,z6]),(0,[z1,z2,z65,z277,z76,z6]),(0,[z1,z2,z3,z5,z11,z728])],[(0,[z1,z379,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z786]),(0,[z1,z2,z787,z8,z5,z12]),(0,[z1,z2,z788,z3,z8,z5]),(0,[z64,z1,z530,z3,z99,z6])],[(0,[z1,z2,z3,z8,z77,z6]),(0,[z1,z2,z3,z8,z789,z6]),(0,[z13,z1,z14,z152,z5,z6]),(0,[z1,z790,z3,z8,z5,z6]),(0,[z1,z2,z8,z34,z66,z6]),(0,[z1,z2,z3,z8,z791,z6]),(0,[z21,z2,z286,z8,z5,z354]),(0,[z1,z2,z3,z8,z5,z792])],[(0,[z13,z1,z2,z793,z5,z6]),(0,[z1,z2,z107,z8,z5,z6]),(0,[z1,z58,z3,z8,z309,z73]),(0,[z1,z2,z552,z3,z35,z8])],[(0,[z46,z2,z334,z8,z5,z6])],[(0,[z0,z7,z3,z8,z5,z6]),(0,[z21,z1,z2,z8,z66,z6]),(0,[z255,z1,z2,z152,z5,z6]),(0,[z1,z2,z3,z8,z5,z794]),(0,[z426,z2,z3,z72,z5,z6]),(0,[z1,z58,z86,z8,z73,z6]),(0,[z1,z2,z245,z34,z5,z6])],[(0,[z0,z7,z24,z8,z5,z6]),(0,[z255,z1,z2,z8,z5,z795]),(1,[z1,z2,z157,z225,z3])],[(0,[z13,z1,z2,z8,z5,z354]),(0,[z13,z1,z2,z149,z8,z6]),(0,[z13,z200,z2,z8,z5,z6]),(0,[z1,z2,z17,z8,z346,z6]),(0,[z2,z3,z8,z5,z796,z6]),(0,[z1,z2,z797,z17,z8,z6])],[(0,[z1,z14,z3,z8,z5,z211]),(0,[z1,z2,z8,z5,z31,z56]),(0,[z63,z2,z17,z8,z5,z12]),(0,[z1,z2,z530,z105,z3,z8]),(0,[z1,z2,z3,z5,z6,z798])],[(0,[z799,z1,z2,z8,z5,z6]),(0,[z21,z2,z8,z5,z594,z6]),(0,[z1,z2,z8,z5,z31,z784])],[(0,[z1,z2,z254,z8,z5,z304]),(0,[z1,z2,z24,z8,z5,z160]),(0,[z1,z2,z175,z8,z5,z12]),(0,[z1,z2,z81,z8,z5,z278]),(0,[z1,z2,z24,z8,z5,z800]),(0,[z1,z2,z24,z8,z5,z266]),(0,[z1,z2,z3,z8,z801,z6]),(0,[z1,z2,z802,z8,z5,z6])],[(0,[z13,z21,z2,z8,z5,z211]),(0,[z1,z2,z17,z259,z5,z6]),(0,[z1,z2,z24,z8,z801,z6]),(0,[z64,z1,z3,z766,z5,z6]),(0,[z1,z2,z157,z225,z3,z120])],[(0,[z1,z2,z8,z5,z803,z6]),(0,[z1,z2,z3,z8,z804,z5]),(0,[z46,z1,z2,z8,z5,z12]),(0,[z1,z2,z17,z805,z5,z6])]],
   [[(0,[z1,z26,z3,z8,z5,z361]),(0,[z1,z2,z3,z8,z806,z5]),(1,[z1,z2,z3,z768,z6])],[(0,[z13,z1,z109,z8,z5,z280]),(0,[z1,z2,z3,z152,z284,z6])],[(0,[z1,z312,z2,z8,z5,z31]),(0,[z1,z2,z3,z8,z346,z20]),(0,[z1,z2,z347,z8,z5,z31]),(0,[z1,z597,z17,z8,z5,z6])],[(0,[z1,z2,z807,z8,z5,z392]),(0,[z1,z2,z530,z808,z8,z6]),(0,[z1,z58,z336,z3,z8,z73])],[(0,[z1,z2,z809,z8,z5,z6]),(0,[z1,z2,z810,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z174]),(0,[z1,z2,z3,z8,z249,z18])],[(0,[z21,z1,z2,z8,z5,z143])],[(0,[z1,z2,z3,z8,z5,z811]),(0,[z1,z26,z8,z5,z74,z6]),(0,[z1,z14,z3,z8,z5,z31]),(0,[z1,z2,z3,z8,z5,z812]),(0,[z1,z698,z17,z8,z5,z6]),(0,[z1,z114,z3,z8,z5,z115])],[(0,[z1,z2,z3,z8,z5,z813]),(0,[z1,z2,z17,z8,z5,z814]),(0,[z2,z3,z8,z5,z815,z6]),(0,[z1,z2,z146,z8,z5,z74])],[(0,[z13,z1,z2,z8,z5,z304]),(0,[z1,z2,z17,z8,z5,z354]),(0,[z2,z3,z8,z5,z495,z31]),(0,[z1,z2,z81,z8,z5,z56]),(0,[z1,z816,z17,z8,z5,z6]),(0,[z1,z2,z17,z149,z8,z6]),(0,[z1,z2,z3,z5,z6,z728])],[(0,[z127,z1,z26,z8,z5,z6]),(0,[z13,z2,z195,z8,z5,z12]),(0,[z1,z2,z65,z3,z76,z12]),(0,[z1,z2,z3,z8,z5,z817])],[(0,[z222,z2,z3,z72,z5,z6]),(0,[z64,z1,z3,z606,z99,z5])],[(0,[z1,z2,z818,z8,z5,z6]),(0,[z13,z2,z184,z8,z5,z6]),(0,[z496,z2,z3,z8,z5,z31]),(0,[z1,z2,z819,z3,z8,z6])],[(0,[z1,z2,z3,z820,z5,z6]),(0,[z46,z2,z3,z8,z5,z12]),(0,[z1,z2,z351,z8,z5,z430]),(0,[z1,z2,z146,z8,z5,z287]),(0,[z1,z2,z3,z248,z5,z11])],[(0,[z1,z26,z8,z5,z73,z6]),(0,[z13,z1,z2,z8,z5,z821]),(0,[z1,z2,z822,z8,z5,z12]),(0,[z1,z80,z816,z8,z5,z6])],[(0,[z1,z2,z24,z8,z93,z6]),(0,[z1,z2,z3,z8,z66,z211]),(0,[z1,z2,z24,z8,z5,z12])],[(0,[z1,z2,z8,z368,z5,z6])]],
   [[(0,[z1,z2,z163,z8,z5,z304]),(0,[z13,z391,z2,z8,z5,z6]),(0,[z262,z1,z2,z450,z5,z6]),(0,[z1,z2,z3,z714,z5,z6]),(0,[z246,z1,z816,z8,z5,z6])],[(0,[z216,z28,z3,z8,z5,z143]),(0,[z1,z2,z17,z8,z5,z361]),(0,[z23,z1,z2,z8,z5,z31]),(0,[z1,z2,z3,z8,z5,z738])],[(0,[z1,z2,z823,z3,z8,z6]),(0,[z21,z1,z2,z8,z6,z36]),(0,[z1,z2,z24,z197,z5,z6]),(0,[z2,z626,z3,z8,z5,z12]),(0,[z23,z2,z477,z8,z5,z6])],[(0,[z1,z2,z210,z8,z5,z12]),(0,[z13,z1,z2,z152,z5,z361]),(0,[z1,z2,z449,z448,z5,z6]),(0,[z1,z2,z24,z824,z5,z6]),(0,[z825,z1,z2,z8,z5,z6])],[(0,[z13,z1,z2,z8,z826,z6]),(0,[z1,z2,z827,z8,z5,z6]),(0,[z642,z2,z3,z8,z5,z12])],[(0,[z1,z2,z3,z8,z5,z828])],[(0,[z255,z23,z2,z8,z5,z6]),(0,[z13,z2,z8,z5,z495,z6]),(0,[z1,z2,z829,z8,z5,z6])],[(0,[z216,z23,z2,z8,z5,z6]),(0,[z1,z26,z8,z5,z66,z6]),(0,[z2,z3,z8,z5,z508,z31]),(0,[z1,z2,z830,z8,z5,z6]),(0,[z1,z2,z105,z17,z8,z5]),(0,[z1,z17,z8,z5,z6,z207])],[(0,[z1,z2,z831,z8,z5,z6]),(0,[z13,z1,z26,z8,z284,z6]),(0,[z13,z1,z832,z8,z5,z6]),(0,[z45,z21,z2,z8,z55,z6]),(0,[z1,z833,z3,z8,z5,z6]),(0,[z1,z2,z428,z33,z5,z6]),(0,[z1,z2,z3,z834,z5,z6]),(0,[z1,z2,z16,z24,z8,z19]),(0,[z1,z2,z157,z3,z36,z120])],[(0,[z1,z2,z835,z8,z5,z143]),(0,[z246,z1,z26,z8,z5,z6]),(0,[z1,z2,z3,z8,z66,z31]),(0,[z1,z233,z17,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z836]),(0,[z1,z2,z3,z8,z5,z837]),(0,[z1,z3,z8,z5,z12,z838]),(0,[z1,z2,z51,z10,z5,z6])],[(0,[z1,z2,z3,z8,z839,z6]),(0,[z1,z2,z26,z8,z5,z361]),(0,[z1,z2,z744,z8,z5,z6])],[(0,[z1,z2,z243,z24,z5,z6]),(0,[z1,z840,z2,z8,z5,z6]),(0,[z1,z841,z2,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z842]),(0,[z1,z28,z17,z8,z5,z31]),(0,[z1,z843,z2,z8,z5,z6]),(0,[z1,z2,z3,z152,z5,z12]),(0,[z1,z2,z8,z284,z141,z6]),(0,[z21,z1,z2,z65,z76,z6]),(0,[z1,z2,z3,z8,z5,z844]),(0,[z1,z2,z845,z8,z5,z6])],[(0,[z1,z2,z24,z318,z5,z6]),(0,[z46,z7,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z846]),(0,[z1,z2,z8,z5,z111,z12]),(0,[z1,z2,z113,z8,z5,z12])],[(0,[z1,z2,z847,z3,z5,z6]),(0,[z1,z2,z8,z5,z848,z12]),(0,[z1,z2,z125,z3,z5,z31]),(0,[z1,z2,z849,z8,z5,z6])]],
   [[(0,[z1,z2,z24,z4,z5,z6]),(0,[z13,z49,z2,z8,z5,z6]),(0,[z1,z26,z8,z5,z6,z850]),(0,[z1,z2,z851,z8,z5,z6]),(0,[z1,z3,z8,z5,z6,z852]),(0,[z1,z24,z17,z8,z5,z12]),(0,[z1,z2,z191,z8,z5,z56])],[(0,[z1,z2,z853,z8,z5,z6])],[(0,[z1,z26,z8,z5,z11,z6]),(0,[z1,z26,z51,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z236]),(0,[z127,z2,z81,z8,z5,z31]),(0,[z1,z2,z16,z3,z8,z723])],[(0,[z21,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z309,z259,z5]),(0,[z1,z114,z3,z8,z650,z5]),(0,[z1,z2,z67,z8,z141,z6])],[(0,[z0,z1,z252,z8,z5,z6]),(0,[z1,z2,z854,z8,z5,z6]),(0,[z13,z1,z2,z285,z284,z6]),(0,[z1,z2,z8,z855,z5,z6]),(0,[z856,z1,z2,z8,z5,z6]),(0,[z1,z2,z65,z552,z3,z8])],[(0,[z1,z2,z857,z8,z5,z6]),(0,[z1,z2,z3,z75,z768,z6])],[(0,[z1,z2,z26,z8,z5,z211]),(0,[z1,z2,z457,z8,z5,z31]),(0,[z1,z2,z3,z8,z5,z858])],[(0,[z21,z1,z2,z859,z5,z6]),(0,[z1,z2,z81,z8,z5,z74]),(0,[z1,z2,z537,z8,z371,z6]),(0,[z1,z2,z3,z8,z5,z860]),(0,[z1,z2,z3,z8,z5,z861]),(0,[z1,z3,z8,z862,z73,z6])],[(0,[z469,z1,z2,z8,z5,z361]),(0,[z1,z2,z252,z8,z5,z12])],[(0,[z215,z1,z605,z8,z5,z6]),(0,[z1,z2,z863,z8,z5,z6])],[(0,[z1,z2,z3,z864,z5,z6]),(0,[z255,z1,z2,z865,z5,z6]),(0,[z1,z2,z3,z8,z385,z20]),(0,[z127,z2,z8,z5,z31,z56]),(0,[z1,z2,z32,z8,z141,z6])],[(0,[z13,z1,z866,z8,z5,z6]),(0,[z13,z2,z275,z8,z5,z6]),(0,[z1,z114,z3,z8,z5,z190]),(0,[z64,z1,z17,z99,z5,z6]),(0,[z1,z2,z552,z24,z8,z5]),(0,[z1,z114,z457,z8,z5,z115]),(0,[z1,z2,z8,z5,z6,z867])],[(0,[z1,z2,z24,z8,z5,z52]),(0,[z13,z1,z2,z8,z5,z392]),(0,[z13,z1,z2,z868,z5,z6]),(0,[z1,z109,z347,z8,z5,z280]),(0,[z1,z3,z8,z5,z115,z869]),(0,[z1,z2,z8,z5,z870,z278]),(0,[z1,z871,z2,z8,z5,z6])],[(0,[z1,z26,z146,z8,z5,z6]),(0,[z1,z2,z62,z199,z5,z6]),(0,[z1,z872,z3,z8,z5,z6]),(0,[z1,z2,z243,z16,z3,z19])],[(0,[z1,z2,z3,z873,z8,z5]),(0,[z46,z1,z2,z8,z5,z730]),(0,[z874,z2,z17,z8,z5,z6]),(0,[z875,z2,z3,z8,z5,z6])],[(0,[z1,z2,z876,z8,z5,z6])]],
   [[(0,[z216,z28,z24,z8,z5,z6]),(0,[z13,z1,z2,z606,z8,z5]),(0,[z13,z2,z195,z8,z284,z6]),(0,[z222,z21,z2,z72,z5,z6]),(0,[z1,z2,z8,z5,z877,z6]),(0,[z345,z2,z3,z8,z5,z12]),(0,[z1,z2,z878,z3,z8,z5])],[(0,[z1,z2,z3,z879,z5,z6]),(0,[z0,z731,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z880]),(0,[z1,z881,z26,z8,z5,z6]),(0,[z1,z2,z26,z8,z5,z31]),(0,[z1,z882,z3,z8,z5,z6]),(1,[z1,z2,z65,z552,z3])],[(0,[z520,z1,z26,z8,z5,z6]),(0,[z13,z2,z195,z285,z5,z6]),(0,[z424,z2,z3,z8,z5,z12]),(0,[z1,z2,z81,z8,z5,z331]),(0,[z1,z2,z8,z883,z5,z6]),(0,[z1,z2,z3,z8,z5,z884])],[(0,[z13,z1,z2,z8,z66,z6]),(0,[z21,z1,z2,z152,z5,z6]),(0,[z13,z1,z2,z8,z885,z6]),(0,[z1,z14,z3,z8,z5,z361]),(0,[z1,z2,z3,z886,z5,z6]),(0,[z1,z2,z887,z17,z8,z5])],[(0,[z13,z1,z26,z8,z5,z12]),(0,[z2,z3,z744,z8,z5,z6]),(0,[z21,z1,z2,z8,z5,z110]),(0,[z21,z1,z2,z5,z6,z116]),(0,[z1,z2,z3,z8,z5,z888])],[(0,[z1,z2,z3,z8,z889,z6]),(0,[z1,z2,z807,z8,z5,z6]),(0,[z216,z28,z210,z8,z5,z6]),(0,[z45,z2,z3,z8,z55,z6]),(0,[z1,z58,z24,z8,z73,z6]),(0,[z1,z890,z3,z8,z5,z6]),(0,[z1,z2,z106,z8,z5,z278])],[(0,[z45,z2,z24,z8,z55,z6]),(0,[z46,z1,z2,z8,z5,z31])],[(0,[z1,z2,z835,z8,z5,z6]),(1,[z1,z2,z8,z5,z755]),(0,[z1,z2,z24,z285,z5,z6]),(0,[z222,z2,z71,z72,z5,z6]),(0,[z1,z2,z51,z33,z5,z31]),(0,[z1,z2,z24,z8,z785,z6]),(0,[z891,z1,z2,z8,z5,z6])],[(0,[z13,z1,z892,z8,z5,z6]),(0,[z13,z63,z2,z8,z5,z12]),(0,[z1,z2,z8,z5,z893,z12]),(0,[z1,z2,z277,z8,z5,z12]),(0,[z377,z2,z3,z8,z5,z12])],[(0,[z1,z2,z24,z8,z77,z6]),(0,[z1,z894,z26,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z211]),(0,[z1,z2,z8,z5,z6,z895]),(0,[z1,z2,z369,z8,z94,z6]),(0,[z1,z114,z175,z8,z5,z115]),(0,[z1,z2,z16,z3,z8,z19])],[(0,[z1,z2,z17,z8,z5,z392]),(0,[z1,z653,z17,z8,z5,z6]),(0,[z1,z2,z71,z8,z5,z12]),(0,[z1,z2,z8,z896,z5,z6])],[(0,[z1,z2,z897,z8,z5,z6]),(0,[z1,z2,z898,z8,z5,z6])],[(0,[z7,z133,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z899]),(0,[z1,z109,z3,z8,z5,z264]),(0,[z1,z2,z3,z8,z5,z730]),(0,[z1,z2,z243,z3,z249,z5])],[(0,[z1,z2,z243,z3,z5,z6])],[(0,[z1,z26,z17,z8,z5,z6]),(0,[z13,z1,z2,z8,z284,z12]),(0,[z40,z2,z3,z8,z147,z6]),(0,[z1,z2,z17,z606,z8,z5]),(0,[z1,z597,z2,z65,z3,z6])],[(0,[z1,z2,z3,z8,z385,z6]),(0,[z1,z2,z112,z8,z5,z287])]],
   [[(0,[z13,z1,z2,z285,z5,z12]),(0,[z1,z2,z900,z8,z5,z6]),(0,[z1,z2,z106,z8,z5,z56]),(0,[z1,z2,z17,z901,z5,z6]),(0,[z1,z902,z3,z8,z5,z6])],[(0,[z1,z68,z3,z8,z69,z31]),(0,[z567,z2,z3,z8,z5,z31]),(0,[z1,z2,z903,z3,z8,z5])],[(0,[z215,z2,z133,z8,z5,z6]),(0,[z1,z17,z8,z281,z5,z6]),(0,[z1,z2,z3,z8,z5,z904])],[(0,[z1,z2,z3,z8,z905,z6]),(0,[z2,z3,z72,z714,z5,z6]),(0,[z2,z3,z8,z612,z5,z12]),(0,[z1,z82,z83,z90,z5,z6])],[(0,[z1,z2,z3,z8,z5,z31]),(0,[z46,z2,z7,z8,z5,z6]),(0,[z1,z2,z906,z8,z5,z6])],[(0,[z1,z2,z3,z907,z5,z6])],[(0,[z1,z2,z3,z8,z66,z361]),(0,[z45,z2,z3,z8,z55,z110]),(0,[z1,z2,z8,z5,z908,z12])],[(0,[z13,z1,z58,z8,z73,z6]),(1,[z46,z2,z8,z5,z12]),(0,[z1,z2,z8,z5,z909,z6]),(0,[z1,z2,z910,z8,z5,z6]),(1,[z1,z3,z8,z5,z869])],[(0,[z1,z26,z26,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z911]),(0,[z1,z2,z125,z3,z55,z6]),(0,[z1,z2,z3,z197,z147,z6]),(0,[z1,z2,z24,z8,z5,z174]),(0,[z1,z2,z912,z8,z5,z6]),(0,[z1,z2,z913,z8,z5,z6]),(0,[z1,z2,z24,z8,z249,z18])],[(0,[z13,z1,z2,z8,z5,z20]),(0,[z1,z2,z3,z35,z75,z31]),(0,[z1,z2,z17,z8,z5,z914])],[(0,[z915,z1,z2,z8,z5,z6]),(0,[z1,z24,z164,z8,z5,z6]),(0,[z1,z2,z916,z8,z5,z6]),(0,[z1,z114,z24,z8,z5,z115]),(0,[z1,z3,z8,z5,z869,z6])],[(0,[z1,z2,z86,z8,z5,z31]),(0,[z874,z2,z3,z8,z5,z6])],[(0,[z13,z0,z2,z8,z5,z12]),(0,[z1,z2,z8,z707,z5,z6]),(0,[z1,z2,z917,z8,z5,z6]),(0,[z1,z2,z552,z3,z8,z5])],[(0,[z13,z1,z2,z8,z6,z36]),(0,[z21,z2,z8,z612,z5,z6])],[(0,[z222,z2,z24,z72,z5,z6]),(0,[z1,z2,z918,z8,z5,z6])],[(0,[z1,z393,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z741]),(0,[z1,z2,z106,z8,z5,z354])]],
   [[(0,[z1,z26,z8,z5,z919,z6]),(0,[z1,z2,z3,z5,z12,z116]),(0,[z1,z2,z3,z8,z5,z920]),(0,[z1,z2,z24,z248,z5,z11]),(0,[z1,z2,z65,z552,z3,z5])],[(0,[z1,z2,z921,z8,z5,z6]),(0,[z46,z1,z2,z805,z5,z6]),(0,[z1,z109,z17,z8,z5,z280]),(0,[z1,z2,z65,z17,z76,z6]),(0,[z1,z2,z922,z8,z5,z6]),(0,[z1,z2,z3,z8,z923,z6]),(0,[z1,z2,z65,z3,z398,z6]),(0,[z1,z2,z16,z3,z8,z204])],[(0,[z1,z2,z3,z8,z5,z924]),(0,[z13,z222,z2,z72,z5,z6]),(0,[z1,z2,z925,z8,z5,z6])],[(0,[z1,z2,z254,z8,z5,z6]),(0,[z102,z1,z26,z8,z5,z6])],[(0,[z1,z2,z3,z152,z5,z31]),(0,[z1,z2,z926,z3,z8,z12]),(0,[z142,z1,z24,z8,z5,z6])],[(0,[z13,z431,z2,z8,z5,z6]),(0,[z1,z2,z8,z5,z111,z31]),(0,[z1,z2,z927,z8,z5,z31]),(0,[z1,z2,z113,z8,z5,z31]),(0,[z1,z2,z24,z8,z5,z738]),(0,[z1,z2,z3,z928,z5,z6]),(0,[z1,z929,z3,z8,z5,z6])],[],[(0,[z21,z378,z2,z8,z5,z6]),(0,[z1,z2,z17,z8,z5,z20])],[(0,[z1,z731,z3,z8,z5,z6]),(0,[z215,z1,z26,z8,z5,z6]),(0,[z13,z1,z2,z65,z76,z6]),(0,[z1,z2,z106,z8,z5,z361]),(0,[z1,z2,z8,z242,z5,z6])],[(0,[z1,z2,z17,z8,z5,z304]),(0,[z21,z2,z286,z8,z5,z6]),(0,[z1,z930,z3,z8,z5,z6]),(0,[z1,z2,z931,z8,z5,z6]),(0,[z1,z2,z771,z8,z5,z6])],[(0,[z13,z1,z2,z8,z932,z6]),(0,[z1,z2,z3,z8,z346,z6]),(0,[z1,z2,z3,z8,z5,z933])],[(0,[z63,z2,z3,z8,z5,z12])],[(0,[z21,z2,z8,z686,z5,z6]),(0,[z1,z2,z3,z8,z5,z934])],[(0,[z13,z1,z26,z285,z5,z6]),(0,[z102,z1,z2,z8,z284,z6]),(0,[z935,z1,z2,z8,z5,z6])],[(0,[z13,z1,z2,z8,z5,z6]),(0,[z13,z1,z2,z8,z758,z6]),(0,[z13,z1,z2,z125,z5,z6]),(0,[z89,z2,z3,z108,z5,z403]),(0,[z1,z2,z3,z259,z5,z6]),(0,[z1,z2,z3,z936,z5,z6])],[(0,[z102,z1,z2,z285,z5,z6]),(0,[z1,z2,z3,z35,z167,z6]),(0,[z1,z2,z3,z805,z5,z6]),(0,[z1,z170,z17,z8,z5,z6]),(0,[z1,z2,z937,z3,z8,z6])]],
   [[(0,[z1,z2,z442,z8,z5,z6]),(1,[z1,z2,z3,z5,z728])],[(0,[z1,z2,z8,z5,z31,z755]),(0,[z1,z2,z3,z8,z938,z6])],[(0,[z1,z687,z17,z8,z5,z6]),(0,[z1,z939,z3,z8,z5,z6])],[(0,[z13,z1,z2,z35,z75,z6]),(0,[z21,z1,z2,z8,z5,z196]),(0,[z1,z940,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z941,z6]),(0,[z1,z2,z3,z8,z5,z942])],[(0,[z40,z21,z2,z8,z147,z6]),(0,[z21,z2,z286,z8,z5,z96]),(0,[z2,z583,z3,z8,z5,z31]),(0,[z1,z2,z943,z8,z5,z6]),(0,[z1,z2,z62,z34,z5,z6]),(0,[z1,z2,z157,z225,z3,z5])],[(0,[z1,z2,z8,z944,z5,z6]),(0,[z1,z2,z945,z3,z8,z6]),(0,[z1,z2,z51,z707,z5,z6])],[(0,[z1,z2,z163,z8,z5,z6]),(0,[z13,z21,z2,z8,z66,z6]),(0,[z21,z1,z2,z8,z309,z5]),(0,[z1,z2,z146,z8,z5,z96]),(0,[z1,z2,z24,z8,z5,z236]),(0,[z1,z2,z157,z24,z5,z120]),(0,[z1,z2,z3,z75,z658,z6])],[(0,[z1,z2,z3,z8,z5,z814]),(0,[z2,z286,z744,z8,z5,z6]),(0,[z1,z2,z530,z24,z8,z6]),(0,[z1,z532,z24,z8,z5,z6]),(0,[z1,z2,z946,z8,z5,z6]),(0,[z1,z2,z125,z336,z3,z5])],[(0,[z1,z2,z3,z8,z5,z354]),(0,[z1,z2,z51,z8,z66,z6]),(0,[z476,z21,z2,z8,z5,z6]),(0,[z1,z2,z947,z8,z5,z6]),(0,[z1,z816,z3,z8,z5,z6]),(0,[z1,z458,z24,z8,z5,z6]),(0,[z1,z2,z3,z149,z8,z6]),(1,[z1,z2,z3,z8,z723])],[(0,[z255,z1,z2,z717,z5,z6]),(0,[z13,z1,z2,z8,z5,z96])],[(0,[z1,z2,z244,z8,z5,z6]),(0,[z1,z2,z948,z8,z5,z6]),(0,[z1,z184,z17,z8,z5,z6]),(0,[z1,z2,z24,z8,z5,z858])],[(0,[z63,z1,z26,z8,z5,z6]),(0,[z13,z2,z8,z5,z55,z12]),(0,[z1,z2,z949,z8,z5,z31]),(0,[z1,z2,z950,z3,z8,z5]),(0,[z1,z2,z24,z8,z5,z860]),(0,[z1,z2,z951,z3,z8,z5])],[(0,[z1,z2,z54,z8,z66,z6]),(0,[z45,z2,z3,z8,z952,z6]),(0,[z1,z2,z3,z41,z5,z160]),(0,[z2,z3,z8,z5,z594,z31])],[(0,[z1,z2,z3,z8,z5,z953]),(0,[z1,z2,z954,z8,z5,z6])],[(0,[z1,z2,z955,z8,z5,z6]),(0,[z956,z1,z2,z8,z5,z6]),(0,[z517,z2,z3,z8,z5,z12]),(0,[z1,z2,z3,z8,z5,z957])],[(0,[z13,z1,z2,z8,z5,z110]),(0,[z13,z1,z2,z5,z6,z116]),(0,[z1,z866,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z958]),(0,[z89,z2,z428,z108,z5,z6])]],
   [[(0,[z1,z2,z8,z5,z211,z278]),(0,[z1,z2,z959,z8,z5,z6]),(0,[z246,z1,z24,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z960]),(0,[z1,z2,z3,z35,z593,z6])],[(0,[z1,z2,z3,z8,z5,z361]),(0,[z1,z14,z17,z8,z5,z6]),(0,[z1,z2,z71,z8,z5,z31]),(0,[z1,z2,z439,z3,z5,z70]),(0,[z1,z2,z3,z8,z5,z961])],[(0,[z1,z2,z152,z285,z5,z6]),(0,[z1,z2,z3,z8,z962,z6])],[(0,[z1,z26,z3,z8,z66,z6]),(0,[z1,z2,z285,z5,z141,z6]),(0,[z963,z1,z2,z8,z5,z6]),(0,[z127,z2,z3,z8,z5,z31]),(0,[z1,z2,z964,z8,z5,z12])],[(0,[z13,z28,z2,z8,z5,z12]),(0,[z1,z2,z3,z965,z5,z6]),(0,[z1,z2,z3,z41,z5,z174])],[(0,[z1,z26,z72,z8,z5,z6]),(0,[z13,z1,z2,z8,z284,z31]),(0,[z45,z2,z3,z8,z55,z196])],[(0,[z1,z2,z3,z8,z5,z966]),(0,[z272,z2,z3,z8,z5,z31])],[(0,[z1,z2,z17,z8,z5,z96]),(0,[z1,z2,z175,z8,z5,z31]),(0,[z1,z98,z24,z8,z5,z6]),(0,[z1,z2,z967,z8,z5,z6])],[(0,[z1,z2,z8,z968,z5,z6]),(0,[z13,z2,z195,z8,z5,z211]),(0,[z46,z89,z2,z8,z5,z6]),(0,[z1,z2,z969,z8,z5,z6]),(0,[z1,z2,z970,z8,z385,z6]),(0,[z1,z2,z3,z197,z5,z160]),(0,[z1,z2,z3,z8,z5,z971]),(0,[z1,z2,z972,z8,z5,z6]),(0,[z1,z2,z973,z8,z5,z6])],[(0,[z246,z1,z312,z8,z5,z6]),(0,[z1,z26,z8,z974,z5,z6]),(0,[z89,z2,z107,z108,z5,z6]),(0,[z1,z2,z83,z8,z5,z6]),(0,[z1,z82,z17,z90,z5,z6]),(0,[z1,z2,z243,z16,z3,z5])],[(0,[z1,z7,z17,z8,z5,z12]),(0,[z327,z1,z2,z8,z66,z6]),(0,[z1,z2,z975,z8,z5,z6]),(0,[z1,z2,z976,z3,z5,z12]),(0,[z1,z977,z3,z8,z5,z6])],[(0,[z1,z26,z157,z8,z5,z6]),(0,[z1,z14,z26,z8,z5,z6]),(0,[z1,z2,z81,z8,z5,z6]),(0,[z1,z2,z157,z225,z3,z8])],[(0,[z1,z2,z3,z8,z5,z755]),(0,[z515,z2,z3,z108,z5,z6]),(0,[z1,z2,z3,z8,z5,z978])],[(0,[z1,z2,z24,z8,z5,z211]),(0,[z1,z2,z3,z41,z5,z12])],[(0,[z1,z2,z3,z979,z5,z6]),(0,[z215,z1,z2,z8,z5,z12]),(0,[z1,z2,z65,z3,z555,z6]),(0,[z1,z980,z3,z8,z5,z6])],[(0,[z117,z21,z2,z8,z5,z6])]],
   [[(0,[z46,z45,z2,z8,z5,z6]),(0,[z1,z2,z17,z8,z5,z981]),(0,[z64,z1,z105,z3,z99,z5]),(0,[z1,z68,z407,z8,z69,z6])],[(0,[z1,z2,z3,z152,z5,z361]),(0,[z63,z21,z2,z8,z5,z12]),(0,[z1,z2,z3,z72,z385,z6])],[(0,[z13,z1,z2,z982,z5,z6]),(0,[z13,z40,z2,z8,z147,z6]),(0,[z1,z2,z3,z8,z826,z6]),(0,[z1,z2,z54,z8,z94,z6]),(0,[z40,z2,z24,z8,z147,z6]),(0,[z1,z2,z983,z3,z8,z5]),(0,[z1,z17,z8,z5,z6,z374]),(0,[z1,z2,z3,z984,z5,z6]),(0,[z1,z2,z157,z3,z5,z728])],[(0,[z13,z1,z2,z8,z5,z143]),(0,[z1,z26,z8,z5,z31,z6]),(0,[z13,z2,z195,z8,z5,z31]),(0,[z1,z2,z24,z8,z385,z6]),(0,[z1,z2,z65,z3,z76,z31]),(0,[z1,z2,z407,z8,z5,z6]),(0,[z1,z2,z8,z5,z6,z985])],[(0,[z1,z2,z8,z5,z6,z986]),(0,[z13,z216,z28,z8,z5,z6]),(1,[z1,z26,z8,z284,z6]),(0,[z13,z1,z14,z8,z284,z6]),(0,[z520,z1,z2,z8,z5,z211]),(0,[z1,z2,z17,z8,z66,z6]),(0,[z1,z2,z8,z987,z5,z12]),(0,[z1,z2,z3,z8,z988,z5])],[(0,[z1,z26,z106,z8,z5,z6]),(0,[z21,z1,z2,z8,z5,z989]),(0,[z990,z1,z2,z8,z5,z6])],[(0,[z1,z2,z991,z8,z5,z6]),(1,[z1,z26,z285,z5,z6]),(0,[z13,z1,z14,z285,z5,z6]),(0,[z13,z1,z2,z152,z66,z6])],[(0,[z255,z1,z2,z8,z284,z6]),(0,[z1,z2,z3,z992,z5,z6]),(0,[z1,z2,z157,z3,z5,z120]),(0,[z1,z2,z225,z3,z248,z8])],[(0,[z13,z1,z790,z8,z5,z6]),(0,[z1,z2,z993,z8,z5,z6]),(0,[z1,z2,z24,z8,z5,z31]),(0,[z1,z2,z530,z3,z8,z6])],[(0,[z255,z1,z2,z285,z5,z6])],[(0,[z1,z312,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z726]),(0,[z246,z1,z252,z8,z5,z6]),(0,[z1,z2,z994,z8,z5,z6]),(0,[z1,z2,z347,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z995]),(0,[z64,z1,z3,z99,z5,z6])],[(0,[z0,z393,z7,z8,z5,z6]),(0,[z1,z2,z3,z152,z5,z211]),(0,[z21,z1,z2,z8,z5,z223])],[(0,[z1,z2,z3,z8,z996,z5]),(0,[z1,z2,z210,z8,z5,z31]),(0,[z1,z2,z997,z8,z5,z6]),(0,[z1,z998,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z999,z12]),(0,[z1,z2,z8,z5,z31,z986]),(0,[z1,z2,z17,z1000,z5,z6]),(1,[z1,z3,z8,z862,z6]),(0,[z1,z2,z8,z94,z1001,z6])],[(0,[z1,z2,z3,z8,z732,z6]),(0,[z1002,z1,z2,z8,z5,z6]),(0,[z1003,z2,z17,z8,z5,z6])],[]],
   [[(0,[z13,z617,z2,z8,z5,z6]),(0,[z1,z26,z62,z8,z5,z6]),(0,[z89,z2,z3,z108,z5,z12]),(0,[z1,z2,z3,z1004,z8,z5]),(0,[z1,z2,z3,z5,z1005,z12]),(0,[z1,z2,z225,z3,z8,z12]),(0,[z1,z2,z1006,z8,z5,z6]),(0,[z1,z2,z243,z16,z3,z8])],[(0,[z1,z2,z17,z8,z5,z143]),(0,[z13,z21,z2,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z724]),(0,[z1,z2,z369,z8,z5,z6]),(0,[z1,z2,z1007,z8,z5,z6])],[(0,[z1,z2,z8,z5,z1008,z6]),(0,[z46,z1,z2,z901,z5,z6])],[(0,[z1,z2,z1009,z8,z5,z6]),(0,[z222,z1,z26,z8,z5,z6]),(0,[z1,z2,z8,z5,z211,z361]),(0,[z21,z1,z2,z8,z5,z1010]),(0,[z21,z1,z2,z41,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1011])],[(0,[z1,z2,z3,z318,z93,z6]),(0,[z1,z2,z3,z8,z5,z1012])],[(0,[z1,z2,z1013,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1014]),(0,[z1,z2,z54,z8,z5,z6]),(0,[z1,z2,z1015,z8,z5,z6]),(0,[z1,z2,z1016,z8,z5,z6]),(0,[z1,z2,z17,z1017,z8,z6]),(0,[z1018,z2,z3,z8,z5,z6])],[(0,[z13,z2,z192,z8,z5,z6]),(0,[z2,z3,z133,z8,z5,z12])],[(0,[z23,z1,z2,z8,z5,z6]),(0,[z1,z2,z1019,z8,z5,z6]),(0,[z1,z2,z65,z3,z588,z6]),(0,[z1,z2,z24,z928,z5,z6])],[(0,[z1,z2,z3,z8,z5,z392]),(0,[z1,z2,z3,z868,z5,z6]),(0,[z188,z1,z26,z8,z5,z6]),(0,[z13,z294,z2,z8,z5,z6]),(0,[z1,z2,z1020,z8,z5,z6]),(0,[z1,z2,z409,z8,z5,z12]),(0,[z1,z24,z17,z8,z5,z31]),(0,[z1,z2,z157,z3,z221,z5])],[(0,[z1,z2,z3,z8,z5,z1021]),(0,[z1,z1022,z2,z8,z5,z6]),(0,[z117,z2,z3,z72,z5,z6]),(0,[z1,z2,z3,z8,z291,z57])],[(0,[z1,z2,z1023,z8,z5,z6]),(0,[z13,z21,z2,z8,z5,z96]),(1,[z1,z2,z707,z5,z6])],[(0,[z1,z2,z3,z8,z5,z981]),(0,[z1,z2,z1024,z8,z5,z6]),(0,[z1,z2,z712,z3,z5,z6]),(0,[z1,z58,z2,z125,z3,z6]),(0,[z1,z2,z1025,z8,z5,z6])],[(0,[z1,z26,z3,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z196]),(0,[z1,z2,z3,z8,z769,z6]),(0,[z1,z2,z24,z8,z346,z6]),(0,[z1,z2,z17,z8,z6,z36]),(0,[z1,z2,z3,z606,z8,z5]),(0,[z1,z2,z65,z3,z768,z6])],[(0,[z1,z28,z163,z8,z5,z6]),(0,[z13,z64,z1,z99,z5,z6]),(0,[z63,z2,z24,z8,z5,z12]),(0,[z1,z130,z24,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z1026]),(1,[z1,z26,z8,z5,z12]),(0,[z1,z26,z8,z99,z5,z6]),(0,[z1,z26,z8,z69,z5,z6]),(0,[z13,z1,z14,z8,z5,z12]),(0,[z1027,z1,z2,z8,z5,z6]),(0,[z21,z1,z2,z243,z5,z6]),(0,[z1,z2,z3,z901,z5,z6]),(0,[z1,z2,z3,z8,z18,z723])],[(0,[z13,z21,z2,z152,z5,z6]),(0,[z13,z1,z1028,z8,z5,z6]),(0,[z2,z3,z145,z8,z5,z12]),(0,[z1,z2,z3,z8,z5,z1029])],[(0,[z1,z2,z3,z8,z779,z6]),(0,[z13,z1,z2,z8,z284,z361]),(0,[z13,z1,z2,z1030,z5,z6]),(0,[z1,z2,z252,z8,z5,z31]),(0,[z21,z2,z133,z8,z5,z6]),(0,[z1,z2,z1031,z8,z5,z6]),(0,[z1,z2,z442,z72,z5,z6]),(0,[z1,z2,z1032,z8,z5,z12]),(0,[z2,z3,z8,z5,z1033,z6]),(0,[z1,z2,z24,z259,z5,z6]),(0,[z1,z2,z1034,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1035]),(0,[z1,z2,z3,z8,z93,z52]),(0,[z255,z1,z2,z8,z5,z12]),(0,[z13,z1,z26,z8,z5,z211]),(0,[z1,z2,z51,z152,z5,z6]),(0,[z1,z124,z17,z8,z5,z6]),(0,[z1,z2,z530,z3,z108,z6]),(0,[z1036,z1,z2,z8,z5,z6])],[(0,[z1,z2,z423,z8,z5,z12]),(0,[z1,z2,z3,z1037,z5,z6]),(0,[z1,z1038,z2,z8,z5,z6]),(0,[z1,z2,z8,z1001,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1039]),(0,[z378,z28,z3,z8,z5,z6]),(0,[z544,z1,z26,z8,z5,z6]),(0,[z1,z2,z336,z17,z8,z5]),(0,[z1,z68,z467,z8,z69,z6]),(0,[z1,z2,z1040,z8,z5,z6])],[(0,[z1,z2,z3,z8,z1041,z6]),(0,[z13,z1,z1042,z8,z5,z6]),(0,[z1,z14,z3,z8,z66,z6]),(0,[z1,z132,z17,z8,z5,z6])],[(0,[z1,z2,z3,z793,z5,z6]),(0,[z1,z2,z3,z8,z5,z1043]),(0,[z1,z2,z428,z8,z5,z12]),(0,[z200,z2,z3,z8,z55,z6]),(0,[z2,z8,z5,z31,z12,z56])],[(0,[z13,z1,z1044,z8,z5,z6]),(0,[z1,z2,z8,z5,z6,z1045]),(0,[z1,z2,z467,z8,z5,z6])],[(0,[z13,z2,z697,z8,z5,z6]),(0,[z1,z2,z3,z153,z5,z460]),(0,[z1,z2,z3,z8,z5,z914]),(0,[z1,z2,z3,z8,z5,z1046]),(0,[z1,z2,z51,z448,z5,z6]),(0,[z1,z2,z65,z3,z668,z6])],[(0,[z1,z2,z1047,z8,z5,z6]),(0,[z1048,z1,z2,z8,z5,z6]),(0,[z1049,z1,z2,z8,z5,z6]),(0,[z1,z2,z1050,z8,z5,z6]),(0,[z1,z2,z3,z1000,z5,z6])],[(0,[z64,z21,z1,z99,z5,z6]),(0,[z21,z2,z145,z8,z5,z6]),(0,[z1,z2,z1051,z8,z5,z31]),(0,[z1,z2,z3,z8,z249,z723])],[(0,[z1,z2,z3,z1052,z5,z6]),(0,[z1,z2,z3,z8,z284,z12]),(0,[z21,z1,z2,z8,z5,z403]),(0,[z1,z2,z24,z8,z5,z354]),(0,[z1,z2,z1053,z3,z8,z5]),(0,[z1,z68,z17,z8,z69,z6]),(0,[z1,z2,z24,z149,z8,z6])],[(0,[z13,z1,z2,z8,z284,z211]),(0,[z1,z2,z3,z8,z1054,z6])],[(0,[z13,z1,z26,z8,z5,z31]),(0,[z1,z26,z3,z152,z5,z6]),(0,[z2,z17,z8,z5,z31,z12]),(0,[z1,z2,z3,z8,z12,z1055]),(0,[z1,z2,z3,z8,z249,z237])],[(0,[z1,z2,z17,z8,z5,z6]),(0,[z13,z1,z2,z285,z5,z211]),(1,[z2,z3,z8,z952,z6]),(0,[z1,z2,z1056,z8,z5,z6]),(0,[z1,z2,z1057,z8,z5,z6])]],
   [[(0,[z13,z2,z195,z8,z5,z361]),(0,[z1,z2,z3,z1058,z5,z6])],[(0,[z13,z1,z2,z152,z5,z6]),(0,[z13,z1,z2,z8,z5,z1059]),(0,[z1,z2,z107,z8,z5,z12]),(0,[z1,z129,z3,z8,z5,z162]),(0,[z1,z2,z8,z5,z31,z1045]),(0,[z1,z554,z24,z8,z5,z6]),(0,[z1,z2,z3,z606,z149,z8]),(0,[z1,z109,z3,z8,z5,z280])],[(0,[z13,z1,z2,z8,z5,z795]),(0,[z21,z1,z2,z1060,z5,z6]),(0,[z1,z2,z783,z197,z5,z6]),(0,[z1,z2,z277,z8,z5,z31]),(0,[z1,z609,z24,z8,z5,z6]),(0,[z1,z2,z1061,z8,z5,z6])],[(0,[z1,z2,z3,z318,z5,z52]),(0,[z0,z7,z3,z8,z93,z6]),(0,[z0,z7,z3,z8,z5,z12]),(0,[z1,z2,z126,z8,z371,z6]),(0,[z1062,z2,z3,z8,z5,z6])],[(0,[z1,z26,z8,z75,z5,z6]),(0,[z1,z2,z226,z8,z5,z12]),(0,[z1,z2,z17,z35,z75,z6])],[(0,[z1,z2,z3,z4,z5,z52]),(0,[z1,z2,z3,z1063,z5,z6]),(0,[z215,z1,z2,z8,z5,z31]),(0,[z1,z2,z24,z8,z5,z361]),(0,[z1,z2,z1064,z8,z5,z6]),(0,[z1,z2,z1065,z8,z5,z6])],[(0,[z137,z21,z2,z8,z5,z6]),(0,[z222,z2,z3,z72,z5,z223]),(0,[z1,z189,z3,z8,z69,z6]),(0,[z1,z2,z1066,z8,z5,z6]),(0,[z1,z2,z1067,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z20])],[(0,[z2,z3,z8,z5,z666,z31])],[(0,[z1,z2,z3,z8,z5,z304]),(0,[z1,z2,z26,z8,z5,z6]),(0,[z1,z2,z775,z8,z5,z6]),(0,[z1,z2,z106,z8,z5,z292]),(0,[z1,z68,z2,z125,z3,z6]),(0,[z1,z1068,z2,z8,z5,z6]),(0,[z1,z2,z1069,z3,z8,z6]),(0,[z1,z2,z157,z3,z5,z204])],[(0,[z1,z2,z3,z1070,z5,z6]),(0,[z1,z2,z24,z8,z5,z304]),(0,[z13,z1,z2,z285,z5,z31])],[(0,[z1,z58,z3,z8,z862,z6]),(0,[z1,z2,z3,z8,z5,z1071])],[(0,[z1,z2,z3,z8,z5,z1072]),(0,[z1073,z1,z2,z8,z5,z6])],[(0,[z617,z2,z3,z108,z5,z6]),(0,[z201,z2,z3,z8,z5,z12]),(0,[z1,z2,z1074,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z821]),(0,[z1,z2,z65,z3,z693,z6]),(0,[z1,z2,z1075,z8,z5,z6])],[(0,[z1,z2,z17,z152,z5,z6]),(0,[z1,z2,z3,z453,z5,z11]),(0,[z1,z2,z3,z8,z5,z1076]),(0,[z1,z2,z1077,z8,z5,z6]),(0,[z1,z2,z51,z33,z5,z6])]],
   [[(0,[z1,z2,z3,z318,z77,z6]),(0,[z255,z1,z26,z8,z5,z6]),(0,[z1,z2,z1078,z8,z5,z6]),(0,[z1,z26,z8,z5,z211,z6]),(0,[z13,z1,z2,z8,z1079,z6]),(0,[z21,z1,z2,z225,z8,z6]),(0,[z1,z2,z17,z8,z5,z110]),(0,[z1,z2,z17,z5,z6,z116])],[(0,[z1,z2,z3,z8,z1080,z6]),(0,[z216,z1,z26,z8,z5,z6]),(0,[z13,z1,z2,z1081,z5,z6]),(0,[z1,z2,z1082,z8,z5,z6]),(0,[z1,z58,z409,z8,z73,z6]),(0,[z1,z2,z3,z8,z5,z1083]),(0,[z1,z2,z8,z5,z6,z1084])],[(0,[z21,z1,z2,z8,z284,z6]),(0,[z1,z600,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z1085,z6]),(0,[z1,z109,z113,z8,z5,z280])],[(0,[z0,z7,z3,z318,z5,z6]),(0,[z1,z2,z3,z197,z5,z174]),(0,[z1,z2,z258,z8,z5,z12])],[(0,[z2,z3,z8,z1086,z5,z6]),(0,[z1,z2,z123,z199,z5,z6])],[(0,[z0,z7,z3,z4,z5,z6]),(0,[z1,z2,z8,z1087,z5,z6]),(0,[z587,z2,z3,z8,z5,z12]),(0,[z1,z2,z1088,z8,z5,z6]),(0,[z1,z2,z530,z1065,z8,z6]),(0,[z1,z2,z1089,z8,z5,z6]),(0,[z1,z2,z3,z8,z1090,z6]),(0,[z1,z2,z3,z8,z723,z19])],[(0,[z1,z2,z252,z8,z5,z354]),(0,[z21,z1,z2,z336,z8,z5]),(0,[z1,z2,z1091,z8,z5,z6]),(0,[z1,z2,z1092,z8,z5,z6])],[(0,[z0,z312,z7,z8,z5,z6]),(0,[z1,z26,z286,z8,z5,z6]),(0,[z1,z80,z17,z8,z5,z12]),(0,[z1,z1093,z3,z8,z5,z12])],[(0,[z1,z2,z3,z8,z93,z12]),(0,[z1,z26,z8,z108,z5,z6])],[(0,[z215,z1,z252,z8,z5,z6]),(0,[z1,z2,z439,z3,z5,z120]),(0,[z1,z2,z125,z24,z5,z6]),(0,[z1,z68,z3,z8,z69,z6]),(0,[z1094,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1095])],[(0,[z1,z2,z413,z8,z5,z12]),(0,[z1,z2,z3,z8,z268,z237]),(0,[z1,z2,z3,z8,z6,z1096]),(0,[z1,z2,z3,z8,z5,z1097])],[],[(1,[z1,z26,z8,z5,z211]),(0,[z1,z2,z3,z197,z5,z12]),(0,[z1,z2,z1098,z8,z5,z6]),(0,[z1,z2,z1099,z8,z5,z6])],[(0,[z1,z2,z1100,z3,z8,z5]),(0,[z21,z1,z2,z8,z5,z160]),(0,[z21,z1,z2,z8,z5,z266]),(0,[z1,z2,z1101,z8,z5,z6]),(0,[z1,z17,z465,z8,z5,z6]),(0,[z1,z2,z3,z5,z11,z518])],[(0,[z1,z2,z3,z8,z77,z52]),(0,[z1,z3,z8,z5,z862,z6])],[(0,[z1,z2,z8,z1102,z5,z6]),(0,[z13,z23,z2,z8,z5,z6]),(0,[z64,z1,z24,z99,z5,z6])]],
   [[(0,[z1,z2,z428,z285,z5,z6]),(0,[z13,z2,z590,z8,z5,z6]),(0,[z21,z1,z2,z1103,z5,z6]),(0,[z21,z2,z8,z5,z31,z12]),(0,[z1,z2,z3,z8,z5,z748]),(0,[z1,z2,z3,z5,z12,z745]),(0,[z1,z301,z17,z8,z5,z6])],[(0,[z1,z14,z3,z8,z5,z6]),(0,[z0,z7,z3,z8,z5,z52]),(0,[z1,z2,z26,z8,z66,z6]),(0,[z1,z2,z3,z35,z75,z6])],[(0,[z1,z2,z1104,z3,z5,z6]),(0,[z40,z1,z26,z8,z5,z6]),(0,[z1105,z1,z2,z8,z5,z6]),(0,[z194,z2,z3,z8,z5,z31]),(0,[z1,z2,z1106,z8,z5,z6])],[(0,[z1,z1107,z3,z8,z5,z6]),(0,[z1,z2,z8,z5,z12,z1108]),(0,[z2,z697,z3,z8,z5,z31]),(0,[z1,z2,z3,z8,z31,z1096]),(0,[z1,z2,z17,z8,z1109,z5]),(0,[z1,z2,z100,z8,z37,z6]),(0,[z1,z2,z721,z3,z5,z6]),(0,[z1,z2,z62,z707,z5,z6]),(0,[z1,z2,z3,z8,z5,z1110]),(0,[z1,z2,z157,z3,z206,z5])],[(0,[z1,z2,z1111,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1112]),(0,[z1,z2,z1113,z8,z5,z6])],[(0,[z1,z2,z3,z285,z284,z6]),(0,[z1,z585,z17,z8,z5,z6])],[(0,[z13,z1,z2,z1114,z5,z6]),(0,[z13,z2,z78,z8,z5,z6]),(0,[z1,z2,z3,z766,z5,z6]),(0,[z1,z2,z1115,z8,z5,z6])],[(1,[z1,z26,z8,z5,z31]),(0,[z1,z26,z8,z284,z5,z6]),(0,[z13,z89,z2,z108,z5,z6]),(0,[z1,z2,z3,z8,z5,z96]),(0,[z1,z2,z197,z855,z5,z6]),(0,[z1116,z2,z3,z8,z5,z6]),(0,[z1,z68,z3,z8,z862,z6])],[(0,[z1,z2,z3,z318,z5,z12]),(0,[z215,z1,z2,z8,z5,z814]),(0,[z1,z2,z382,z3,z8,z19]),(0,[z1,z2,z225,z17,z8,z6])],[(0,[z215,z1,z2,z8,z5,z354]),(0,[z1,z574,z24,z8,z5,z6]),(0,[z1,z82,z3,z90,z5,z6])],[(0,[z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z93,z6]),(0,[z1,z2,z442,z8,z147,z6])],[(0,[z13,z1,z26,z8,z5,z361]),(0,[z13,z1,z2,z243,z5,z6]),(0,[z21,z2,z8,z5,z6,z234]),(0,[z1,z2,z3,z8,z5,z1117]),(0,[z1,z2,z1118,z3,z8,z5]),(0,[z1,z2,z423,z8,z5,z31]),(0,[z1119,z1,z2,z8,z5,z6])],[(0,[z1,z2,z3,z8,z776,z6]),(0,[z1,z2,z1120,z8,z5,z31]),(0,[z1,z2,z3,z8,z1121,z6]),(0,[z1,z2,z3,z8,z249,z628]),(0,[z1,z2,z3,z248,z5,z728])],[(0,[z1,z26,z67,z8,z5,z6]),(0,[z13,z26,z195,z8,z5,z6]),(0,[z21,z1,z2,z8,z5,z1122]),(0,[z1,z2,z3,z1123,z5,z6])],[(0,[z21,z1,z2,z8,z93,z6]),(0,[z0,z7,z3,z8,z77,z6]),(0,[z1,z2,z24,z8,z5,z392]),(0,[z21,z1,z2,z8,z5,z12]),(0,[z1,z2,z67,z8,z141,z12]),(0,[z1,z2,z1124,z8,z5,z31]),(0,[z46,z1,z2,z8,z5,z914]),(0,[z1,z2,z1125,z8,z5,z6])],[(0,[z13,z424,z2,z8,z5,z6])]],
   [[(0,[z21,z1,z2,z8,z5,z1126]),(0,[z1,z1127,z2,z8,z5,z6])],[(0,[z1,z2,z1128,z8,z5,z6]),(0,[z1,z14,z3,z152,z5,z6]),(0,[z1,z2,z1129,z8,z5,z6]),(0,[z1,z2,z3,z1130,z5,z6]),(0,[z1,z2,z1131,z8,z5,z6]),(0,[z1,z2,z3,z707,z5,z6]),(0,[z1,z2,z3,z8,z5,z1132])],[(0,[z1,z2,z3,z8,z5,z1133]),(0,[z1,z26,z24,z8,z5,z6]),(0,[z1,z2,z33,z285,z5,z6]),(0,[z21,z1,z2,z197,z5,z6]),(0,[z1,z2,z71,z34,z5,z6]),(0,[z1,z2,z24,z606,z8,z5])],[(0,[z1,z26,z35,z8,z5,z6]),(0,[z13,z1,z2,z865,z5,z6]),(0,[z1,z2,z8,z5,z749,z12]),(0,[z2,z3,z8,z5,z12,z179]),(0,[z1,z129,z3,z8,z5,z115])],[(0,[z1,z2,z3,z8,z885,z6]),(0,[z13,z1,z2,z8,z309,z5]),(0,[z1,z2,z3,z8,z66,z6]),(0,[z2,z3,z714,z108,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1134]),(0,[z21,z1,z2,z8,z709,z6]),(0,[z1,z2,z8,z5,z755,z12]),(0,[z46,z2,z72,z8,z5,z6]),(0,[z150,z2,z3,z8,z147,z6]),(0,[z1,z2,z3,z8,z5,z1135]),(0,[z1,z2,z1136,z8,z5,z6])],[(0,[z1,z2,z8,z5,z306,z12]),(0,[z1,z2,z24,z8,z779,z6])],[(0,[z13,z1,z2,z285,z5,z361]),(0,[z13,z1,z2,z8,z1137,z6]),(0,[z1,z2,z3,z8,z952,z6]),(0,[z1,z2,z1138,z3,z8,z5]),(0,[z1,z2,z3,z1139,z5,z6]),(0,[z1,z2,z1140,z8,z5,z6])],[(0,[z1,z28,z17,z8,z5,z6]),(0,[z1,z2,z1141,z8,z5,z6]),(0,[z89,z2,z3,z108,z5,z236]),(0,[z1,z2,z1142,z8,z5,z6]),(0,[z1,z2,z763,z3,z5,z12]),(0,[z2,z3,z8,z156,z5,z12]),(0,[z1,z2,z24,z1037,z5,z6])],[(0,[z1,z1143,z17,z8,z5,z6]),(0,[z255,z1,z14,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z1144]),(0,[z21,z1,z2,z8,z5,z719])],[(0,[z216,z28,z3,z8,z5,z12]),(0,[z1,z3,z8,z5,z6,z838]),(0,[z1,z2,z125,z3,z5,z6]),(0,[z1,z2,z1145,z8,z5,z6])],[(0,[z2,z731,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z385,z223]),(0,[z1,z2,z570,z8,z5,z400])],[(0,[z216,z28,z413,z8,z5,z6]),(0,[z13,z1,z930,z8,z5,z6]),(0,[z1,z2,z8,z1146,z5,z6]),(0,[z1,z2,z8,z5,z1147,z6]),(0,[z1,z2,z126,z8,z94,z12]),(0,[z1,z2,z3,z5,z6,z1148])],[(0,[z1,z26,z8,z285,z5,z6]),(0,[z1149,z1,z2,z8,z5,z6]),(0,[z2,z81,z8,z5,z31,z12]),(0,[z2,z17,z8,z5,z815,z6]),(0,[z1,z2,z24,z8,z5,z1046]),(0,[z1,z2,z8,z5,z870,z6])],[(0,[z21,z1,z2,z318,z5,z6]),(0,[z46,z1,z28,z8,z5,z6]),(0,[z1,z2,z1150,z8,z5,z6]),(0,[z1003,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z1151,z8,z5])],[(0,[z1,z1152,z2,z8,z5,z6]),(0,[z1,z2,z17,z8,z5,z196]),(0,[z1,z58,z3,z8,z73,z12]),(0,[z2,z192,z3,z8,z5,z31])]],
   [[(0,[z21,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z982,z5,z6]),(0,[z45,z2,z3,z8,z55,z12]),(0,[z1,z2,z3,z8,z1153,z6])],[(0,[z1,z2,z3,z8,z5,z143]),(0,[z1,z2,z3,z285,z5,z12]),(0,[z40,z2,z3,z41,z147,z6]),(0,[z1,z2,z457,z8,z5,z6]),(0,[z1,z2,z24,z8,z1054,z6])],[(0,[z1,z28,z26,z8,z5,z6]),(0,[z1,z82,z2,z530,z3,z6])],[(0,[z1,z2,z3,z8,z77,z12]),(0,[z1,z2,z816,z8,z5,z6]),(0,[z1,z2,z105,z24,z8,z5]),(0,[z1,z2,z3,z8,z5,z1154])],[(0,[z1,z7,z17,z8,z5,z31]),(0,[z1,z2,z3,z152,z66,z6]),(0,[z1,z2,z8,z5,z1155,z6])],[(0,[z1,z2,z3,z5,z31,z1148]),(0,[z1,z109,z24,z8,z5,z280])],[(0,[z28,z7,z17,z8,z5,z6]),(0,[z1,z114,z26,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1156]),(0,[z1,z2,z787,z8,z5,z6]),(0,[z1,z2,z1157,z3,z5,z6])],[(0,[z1,z2,z1158,z3,z8,z5]),(0,[z1,z26,z65,z8,z5,z6]),(0,[z1,z2,z3,z41,z5,z31]),(0,[z1,z2,z1159,z8,z5,z31]),(0,[z1,z17,z8,z5,z512,z6]),(0,[z1,z2,z797,z3,z8,z6]),(0,[z1,z2,z3,z1017,z8,z6])],[(0,[z2,z3,z8,z5,z796,z12]),(0,[z2,z24,z8,z5,z31,z12]),(0,[z1,z2,z243,z3,z5,z12])],[(0,[z1,z2,z3,z1160,z8,z6]),(0,[z1,z26,z1161,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z911]),(0,[z1,z2,z1162,z8,z5,z31])],[(0,[z1,z2,z258,z8,z5,z31])],[(0,[z21,z1,z26,z8,z5,z6]),(0,[z1,z2,z24,z8,z5,z20]),(0,[z1,z2,z1163,z8,z5,z31]),(0,[z1,z671,z24,z8,z5,z6])],[(0,[z21,z1,z2,z8,z5,z52]),(0,[z216,z731,z3,z8,z5,z6]),(0,[z1,z2,z3,z1164,z8,z5]),(0,[z1,z2,z3,z8,z5,z1165])],[(0,[z13,z2,z626,z8,z5,z6]),(0,[z40,z2,z3,z197,z147,z6]),(0,[z391,z2,z3,z8,z5,z31])],[(0,[z1,z2,z1166,z8,z5,z6]),(0,[z1,z80,z17,z8,z5,z31]),(0,[z1,z2,z3,z8,z6,z36])],[(0,[z1,z2,z3,z8,z93,z31]),(0,[z1,z2,z175,z8,z5,z6]),(0,[z1,z2,z67,z8,z166,z6])]],
   [[(0,[z1,z2,z1167,z8,z5,z6]),(0,[z1168,z2,z3,z8,z5,z6])],[(0,[z46,z1,z2,z8,z5,z6]),(0,[z1,z2,z8,z5,z392,z1169]),(0,[z1,z2,z3,z8,z6,z1170]),(0,[z1,z2,z3,z1171,z5,z6]),(0,[z1,z2,z16,z3,z116,z19])],[(0,[z1,z2,z8,z5,z909,z12]),(0,[z1,z2,z810,z8,z5,z12]),(0,[z1,z2,z1172,z8,z5,z6])],[(0,[z1,z2,z3,z197,z5,z31]),(0,[z1,z2,z913,z8,z5,z12]),(0,[z2,z3,z8,z5,z12,z234]),(0,[z1,z2,z1173,z8,z5,z6]),(0,[z1,z2,z3,z248,z5,z386]),(0,[z1174,z1,z2,z8,z5,z6])],[(1,[z1,z26,z8,z5,z361]),(0,[z575,z21,z2,z8,z5,z6]),(0,[z1,z2,z1175,z8,z5,z6]),(0,[z1,z2,z3,z8,z249,z621]),(0,[z1,z2,z1176,z8,z5,z6])],[(0,[z1,z2,z3,z4,z77,z6]),(0,[z2,z744,z195,z8,z5,z6]),(0,[z1,z2,z970,z8,z5,z6])],[(0,[z13,z40,z2,z8,z5,z12]),(0,[z1,z2,z3,z8,z346,z223]),(0,[z1,z2,z8,z385,z1177,z6]),(0,[z1,z2,z355,z308,z5,z6]),(0,[z1,z2,z126,z8,z1001,z6])],[(0,[z21,z1,z2,z285,z5,z6]),(0,[z1,z26,z8,z5,z1178,z6]),(0,[z1,z2,z3,z8,z31,z36]),(0,[z1,z2,z3,z8,z5,z1179])],[(0,[z222,z2,z3,z72,z5,z12]),(0,[z1,z636,z17,z8,z5,z6])],[(0,[z21,z1,z2,z8,z77,z6]),(0,[z1,z109,z26,z8,z5,z6]),(0,[z13,z1,z2,z1180,z5,z6]),(0,[z21,z1,z2,z8,z789,z6]),(0,[z40,z2,z8,z147,z111,z6])],[(0,[z13,z1,z2,z8,z5,z223]),(0,[z89,z2,z3,z108,z5,z31]),(1,[z2,z3,z8,z5,z796]),(0,[z1,z2,z225,z3,z8,z31]),(0,[z1,z2,z3,z8,z5,z1181])],[(0,[z215,z1,z2,z8,z5,z392]),(0,[z1,z2,z3,z8,z932,z6]),(0,[z21,z2,z8,z5,z307,z6]),(0,[z1,z2,z1182,z8,z5,z6]),(0,[z46,z127,z2,z8,z5,z6])],[(0,[z1,z2,z26,z152,z5,z6]),(0,[z222,z2,z3,z714,z5,z6]),(0,[z1,z2,z1183,z8,z5,z6])],[(0,[z1,z2,z8,z368,z5,z12]),(0,[z1,z3,z8,z5,z12,z852]),(0,[z1,z68,z24,z8,z69,z6]),(0,[z1,z2,z456,z8,z5,z292])],[(0,[z1,z2,z254,z8,z5,z12]),(0,[z1,z2,z254,z8,z93,z6]),(0,[z13,z222,z2,z8,z5,z12])],[(0,[z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z318,z5,z31]),(0,[z1,z2,z3,z8,z758,z6]),(0,[z13,z1,z14,z8,z5,z211]),(0,[z2,z3,z8,z952,z55,z6]),(0,[z1,z2,z822,z8,z5,z6])]],
   [[(0,[z1,z2,z24,z8,z5,z6]),(0,[z303,z1,z26,z8,z5,z6]),(0,[z13,z14,z195,z8,z5,z6]),(0,[z1,z2,z3,z1030,z5,z6]),(0,[z630,z21,z2,z8,z5,z6]),(0,[z1,z2,z1184,z3,z8,z5])],[(0,[z13,z1,z2,z41,z5,z6]),(0,[z1,z1044,z3,z8,z5,z6])],[(0,[z255,z1,z2,z8,z5,z211]),(0,[z23,z2,z286,z8,z5,z6])],[(0,[z1,z313,z17,z8,z5,z6]),(0,[z2,z133,z17,z8,z5,z12]),(0,[z1,z576,z17,z8,z5,z6]),(0,[z1,z109,z79,z3,z8,z5])],[(0,[z1,z2,z1185,z8,z5,z6]),(0,[z1,z2,z409,z8,z5,z31]),(0,[z1,z2,z32,z8,z489,z6]),(0,[z1,z2,z105,z3,z8,z5])],[(0,[z1,z14,z24,z8,z5,z6]),(0,[z1,z2,z8,z5,z6,z1186]),(0,[z1,z2,z24,z35,z75,z6]),(0,[z1,z2,z8,z1187,z5,z6])],[(0,[z1,z2,z8,z5,z1188,z143]),(0,[z1,z2,z86,z8,z5,z6])],[(0,[z1,z26,z8,z5,z141,z6]),(0,[z1,z1189,z2,z8,z5,z6])],[(0,[z21,z1,z2,z8,z5,z174]),(0,[z21,z1,z2,z8,z249,z18]),(0,[z1,z2,z17,z8,z5,z223]),(0,[z1,z321,z17,z8,z5,z6]),(0,[z1,z2,z336,z3,z259,z5])],[],[(0,[z1,z2,z3,z1190,z5,z6]),(0,[z13,z1,z14,z8,z5,z31]),(0,[z21,z1,z2,z8,z5,z812]),(0,[z1,z2,z503,z34,z5,z6]),(0,[z1,z2,z65,z552,z3,z6])],[(0,[z1,z2,z3,z8,z284,z211]),(0,[z376,z21,z2,z8,z5,z6]),(0,[z1,z2,z24,z8,z5,z96]),(0,[z1,z2,z65,z552,z3,z76]),(0,[z1,z2,z3,z8,z5,z1191])],[(0,[z2,z3,z358,z8,z5,z12])],[(0,[z255,z1,z2,z8,z5,z31]),(0,[z13,z1,z2,z197,z5,z6]),(0,[z1,z2,z3,z285,z5,z211]),(0,[z1,z2,z8,z5,z306,z31]),(0,[z1,z82,z24,z90,z5,z6]),(0,[z1,z2,z1192,z8,z5,z6]),(0,[z1,z2,z1193,z8,z5,z6])],[(0,[z1,z2,z254,z318,z5,z6]),(0,[z1,z2,z8,z5,z1194,z6]),(0,[z1,z2,z1195,z8,z5,z6]),(0,[z1,z2,z8,z5,z31,z1186])],[(0,[z1,z2,z3,z152,z5,z6]),(0,[z1,z2,z3,z8,z5,z1059]),(0,[z616,z2,z3,z8,z55,z6]),(0,[z1,z2,z17,z41,z5,z6]),(0,[z1,z2,z3,z8,z5,z1196]),(0,[z1,z2,z8,z5,z74,z870])]],
   [[(0,[z1,z2,z254,z4,z5,z6]),(0,[z1,z2,z3,z8,z1197,z6]),(0,[z1,z2,z3,z8,z5,z795]),(0,[z13,z271,z2,z8,z5,z6]),(0,[z1,z2,z8,z5,z111,z6]),(0,[z21,z1,z2,z820,z5,z6]),(0,[z21,z1,z2,z248,z5,z11]),(0,[z1,z2,z927,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z110]),(0,[z1,z2,z945,z3,z8,z12]),(0,[z1,z2,z113,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z116])],[(0,[z1,z2,z163,z8,z5,z12]),(0,[z1,z2,z163,z8,z93,z6]),(0,[z216,z28,z3,z8,z5,z31]),(0,[z1,z26,z8,z1198,z5,z6]),(0,[z1,z26,z8,z5,z6,z19]),(0,[z1,z2,z428,z8,z5,z31]),(0,[z1,z2,z125,z3,z147,z6]),(0,[z630,z2,z3,z8,z147,z6]),(0,[z1,z2,z8,z5,z848,z6])],[(0,[z13,z1,z2,z717,z5,z6]),(0,[z1,z2,z8,z5,z12,z56]),(0,[z1,z24,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1199])],[(0,[z1,z2,z1143,z8,z5,z6]),(0,[z13,z2,z195,z8,z66,z6]),(0,[z1,z2,z67,z8,z66,z6]),(0,[z364,z2,z3,z8,z5,z12])],[(0,[z13,z1,z2,z8,z5,z719]),(0,[z1,z2,z3,z1200,z5,z6]),(0,[z1,z2,z8,z5,z1201,z6]),(0,[z1,z2,z1202,z8,z5,z6])],[(0,[z1,z1203,z2,z8,z5,z6])],[(0,[z1,z2,z3,z8,z284,z31]),(0,[z1,z605,z17,z8,z5,z6]),(0,[z1,z58,z3,z8,z73,z31])],[(0,[z1,z2,z1204,z8,z5,z6]),(0,[z1,z2,z105,z3,z149,z8])],[(0,[z1,z2,z3,z285,z5,z31]),(0,[z1,z2,z24,z8,z66,z6]),(0,[z1,z2,z126,z8,z284,z6]),(0,[z1,z2,z3,z453,z5,z119]),(0,[z1,z2,z17,z8,z1205,z6]),(0,[z1,z2,z3,z1206,z5,z6]),(0,[z1207,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z5,z728,z120])],[(0,[z380,z1,z24,z8,z5,z6]),(0,[z1,z2,z3,z5,z31,z116])],[(0,[z1,z2,z3,z8,z77,z31]),(0,[z1,z2,z252,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z403]),(0,[z1,z2,z126,z285,z5,z6]),(0,[z1,z2,z1208,z8,z5,z6])],[(0,[z440,z1,z26,z8,z5,z6]),(0,[z21,z1,z2,z105,z8,z5]),(0,[z1,z2,z107,z8,z5,z31]),(0,[z40,z2,z3,z8,z147,z160])],[(0,[z1,z2,z254,z8,z5,z52]),(0,[z246,z1,z413,z8,z5,z6]),(0,[z1,z2,z3,z197,z55,z6]),(0,[z1,z3,z8,z69,z862,z6])],[(0,[z0,z7,z3,z8,z5,z31]),(0,[z27,z1,z2,z8,z337,z6]),(0,[z1,z359,z17,z8,z5,z6]),(0,[z1,z2,z65,z24,z76,z6]),(0,[z1,z1209,z2,z8,z5,z6]),(0,[z1,z2,z125,z3,z309,z5])],[(0,[z1,z2,z1210,z8,z5,z6]),(0,[z1,z832,z3,z8,z5,z6]),(0,[z21,z1,z2,z8,z5,z837]),(0,[z1,z2,z226,z8,z5,z31]),(0,[z1,z2,z16,z3,z8,z432]),(0,[z1,z2,z157,z225,z3,z6])],[(0,[z1,z2,z3,z1081,z5,z6]),(0,[z0,z21,z7,z8,z5,z6]),(0,[z1,z2,z1211,z8,z5,z6]),(0,[z1,z2,z225,z3,z11,z6])]],
   [[(0,[z1,z2,z1212,z3,z8,z5]),(0,[z1,z2,z887,z3,z8,z5]),(0,[z1,z2,z1213,z3,z8,z5])],[(0,[z1,z2,z163,z318,z5,z6]),(0,[z1,z2,z1214,z8,z5,z6]),(0,[z13,z1,z2,z8,z66,z12]),(0,[z21,z1,z2,z8,z5,z844])],[(0,[z216,z1,z252,z8,z5,z6]),(0,[z89,z2,z17,z108,z5,z6]),(0,[z1,z2,z3,z1215,z8,z6])],[(0,[z1,z2,z163,z4,z5,z6]),(0,[z1,z2,z3,z8,z1216,z6]),(0,[z1,z2,z8,z285,z66,z6]),(0,[z40,z2,z3,z8,z147,z174]),(0,[z1,z2,z1051,z8,z5,z6]),(0,[z2,z8,z5,z306,z31,z12]),(0,[z1,z2,z157,z3,z5,z388]),(0,[z1,z2,z3,z8,z1109,z5])],[(0,[z1,z2,z3,z8,z1217,z6]),(0,[z1,z2,z8,z5,z1188,z6]),(0,[z1,z2,z152,z34,z5,z6]),(0,[z46,z21,z2,z8,z5,z6]),(0,[z63,z2,z8,z5,z306,z12]),(0,[z2,z244,z8,z5,z31,z12])],[(0,[z1,z2,z24,z8,z5,z143]),(0,[z1,z26,z8,z5,z6,z12]),(0,[z1,z2,z252,z8,z5,z96]),(0,[z1,z2,z158,z34,z5,z6]),(0,[z1,z2,z1218,z8,z5,z6]),(0,[z1,z2,z17,z8,z309,z5])],[(0,[z1,z2,z1219,z8,z5,z6]),(0,[z13,z567,z2,z8,z5,z6]),(0,[z21,z1,z2,z8,z5,z236]),(0,[z1,z2,z1220,z3,z8,z5]),(0,[z1,z2,z949,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1221]),(0,[z1,z2,z3,z8,z5,z1222])],[(0,[z13,z1,z2,z8,z5,z52]),(0,[z440,z1,z2,z285,z5,z6])],[(0,[z255,z1,z2,z8,z779,z6]),(0,[z21,z1,z2,z530,z8,z6]),(0,[z1,z2,z17,z8,z5,z403]),(0,[z1,z2,z1223,z8,z5,z6])],[(0,[z1,z2,z254,z8,z77,z6]),(0,[z1,z2,z3,z8,z5,z1224])],[(0,[z46,z216,z2,z8,z5,z6]),(0,[z222,z2,z3,z72,z385,z6]),(0,[z1,z2,z8,z5,z893,z6])],[(0,[z1,z2,z65,z3,z118,z6])],[(0,[z0,z7,z254,z8,z5,z6]),(0,[z1,z2,z71,z8,z5,z6]),(0,[z21,z2,z744,z8,z5,z6]),(0,[z40,z2,z3,z8,z147,z12]),(0,[z1,z2,z16,z17,z8,z19])],[(0,[z1,z1225,z2,z8,z5,z6]),(0,[z21,z276,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z385,z12]),(0,[z1,z68,z3,z338,z8,z6]),(0,[z1,z1226,z2,z8,z5,z6])],[(0,[z13,z1,z2,z225,z8,z6]),(0,[z1,z26,z195,z8,z5,z6]),(0,[z1,z2,z900,z8,z5,z12]),(0,[z315,z2,z3,z8,z5,z31]),(0,[z1,z2,z243,z3,z18,z6])],[(0,[z1,z2,z163,z8,z5,z52]),(0,[z1,z2,z16,z3,z8,z693])]],
   [[(0,[z1,z2,z1227,z8,z5,z6]),(0,[z13,z1,z2,z8,z284,z6]),(0,[z2,z3,z8,z5,z31,z796]),(0,[z1,z2,z1228,z8,z5,z31]),(0,[z1,z2,z819,z3,z8,z31]),(0,[z1,z2,z243,z17,z5,z6])],[(0,[z1,z2,z3,z8,z1229,z5]),(0,[z13,z1,z2,z1230,z5,z6]),(0,[z1,z2,z8,z5,z306,z354]),(0,[z1,z2,z3,z108,z385,z6]),(0,[z1,z468,z3,z8,z5,z190]),(0,[z1,z2,z17,z1231,z8,z5]),(0,[z64,z1,z258,z99,z5,z6]),(0,[z1,z2,z1232,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z724]),(0,[z13,z1,z2,z285,z5,z6]),(0,[z21,z1,z2,z157,z5,z120]),(0,[z1,z2,z3,z8,z5,z796]),(0,[z1,z2,z24,z8,z6,z36])],[(0,[z1,z26,z8,z5,z18,z6]),(0,[z1,z2,z530,z3,z8,z12]),(0,[z1,z2,z24,z8,z5,z724])],[(0,[z1,z2,z413,z8,z5,z31]),(0,[z13,z1,z2,z8,z791,z6]),(0,[z13,z1,z2,z336,z8,z5]),(0,[z1,z2,z8,z368,z5,z31]),(0,[z1,z2,z3,z8,z5,z1233]),(0,[z1,z1234,z2,z8,z5,z6]),(1,[z1,z2,z243,z16,z3])],[(0,[z1,z2,z244,z8,z5,z138])],[(0,[z1,z2,z8,z5,z1235,z6]),(0,[z1,z2,z8,z5,z6,z1236]),(0,[z1,z2,z146,z8,z5,z870])],[(0,[z1,z2,z3,z8,z5,z1237]),(0,[z13,z1,z14,z8,z5,z361]),(0,[z1238,z1,z2,z8,z5,z6]),(1,[z1,z2,z8,z1001,z6]),(0,[z1,z2,z3,z8,z5,z1239])],[(0,[z1,z2,z8,z5,z908,z6]),(0,[z1,z2,z126,z8,z667,z6])],[(0,[z1,z2,z1240,z8,z5,z6])],[(0,[z1,z26,z8,z5,z6,z120]),(0,[z255,z1,z2,z8,z5,z361]),(0,[z1,z2,z3,z8,z5,z1241])],[(0,[z1,z2,z3,z8,z5,z1242]),(0,[z13,z1,z2,z8,z5,z160]),(0,[z1,z1243,z2,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z266]),(0,[z1,z2,z8,z5,z1244,z6]),(0,[z1,z2,z24,z8,z5,z1179])],[(0,[z1,z2,z163,z8,z77,z6]),(0,[z1,z2,z71,z152,z5,z6]),(0,[z1,z2,z369,z8,z5,z12]),(0,[z1,z2,z830,z8,z5,z31]),(0,[z1,z2,z3,z8,z1245,z6]),(0,[z1,z2,z3,z8,z5,z1246]),(0,[z1,z2,z1247,z8,z5,z6])],[(0,[z1,z393,z2,z8,z5,z12]),(0,[z21,z1,z2,z8,z5,z211]),(1,[z1,z2,z8,z5,z719]),(0,[z1,z2,z24,z8,z1245,z6])],[(0,[z13,z1,z26,z8,z66,z6]),(0,[z13,z2,z8,z5,z31,z12]),(0,[z13,z2,z195,z8,z5,z6]),(0,[z1,z2,z65,z3,z76,z6])],[(0,[z0,z7,z163,z8,z5,z6]),(0,[z13,z1,z1248,z8,z5,z6]),(0,[z1,z2,z428,z34,z5,z6]),(0,[z1,z2,z3,z8,z5,z196]),(0,[z1,z2,z8,z5,z31,z1236]),(0,[z1,z2,z552,z17,z8,z5]),(0,[z64,z1,z140,z3,z5,z6])]],
   [[(0,[z13,z1,z2,z152,z284,z6])],[(0,[z1,z2,z3,z865,z5,z6]),(0,[z215,z1,z2,z8,z5,z981]),(0,[z1,z2,z1249,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z1250]),(0,[z1,z2,z3,z8,z1251,z6]),(0,[z1252,z2,z3,z8,z5,z6])],[(0,[z1,z2,z1253,z8,z5,z6]),(0,[z1,z471,z17,z8,z5,z6])],[(0,[z1,z82,z26,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z174]),(0,[z13,z1,z2,z8,z249,z18]),(0,[z1,z2,z3,z8,z284,z361]),(0,[z241,z1,z2,z8,z220,z6]),(0,[z21,z1,z2,z8,z385,z6]),(0,[z1,z2,z24,z8,z758,z6]),(0,[z1,z2,z8,z5,z1254,z6])],[(0,[z1,z2,z3,z4,z5,z31])],[(0,[z1,z2,z3,z285,z5,z361]),(0,[z1,z2,z3,z8,z1137,z6]),(0,[z222,z2,z3,z72,z346,z6]),(0,[z1,z2,z8,z5,z1177,z6]),(0,[z1,z2,z3,z8,z5,z1255]),(0,[z1,z1256,z2,z8,z5,z6])],[(0,[z1,z2,z8,z94,z337,z6]),(0,[z1,z2,z3,z859,z5,z6]),(0,[z1,z2,z8,z242,z5,z12])],[(0,[z1,z2,z3,z8,z5,z1144]),(0,[z21,z2,z286,z8,z5,z12]),(0,[z1,z2,z931,z8,z5,z12]),(0,[z117,z2,z3,z8,z5,z12])],[(0,[z1,z2,z210,z8,z5,z6]),(0,[z1,z312,z17,z8,z5,z6]),(0,[z21,z1,z2,z8,z5,z31]),(0,[z13,z2,z687,z8,z5,z6]),(0,[z1,z2,z3,z8,z346,z12]),(0,[z642,z2,z3,z72,z5,z6]),(0,[z1,z2,z67,z8,z141,z31])],[(0,[z1,z2,z1257,z8,z5,z6]),(0,[z1258,z1,z2,z8,z5,z6]),(0,[z1,z2,z17,z8,z5,z160]),(0,[z1,z2,z854,z8,z5,z31]),(0,[z1,z2,z552,z3,z75,z5])],[(0,[z13,z1,z2,z285,z66,z6]),(0,[z13,z1,z882,z8,z5,z6]),(0,[z1,z1259,z2,z8,z5,z6])],[(0,[z13,z1,z2,z248,z5,z11]),(0,[z1,z2,z3,z1260,z5,z6])],[(0,[z13,z1,z2,z8,z93,z6]),(0,[z1,z28,z1143,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z12]),(0,[z1,z2,z3,z259,z5,z12]),(0,[z1,z17,z8,z5,z6,z615]),(0,[z1,z288,z2,z65,z3,z6])],[(0,[z1,z1261,z26,z8,z5,z6]),(0,[z1,z26,z8,z5,z76,z6]),(0,[z1,z2,z3,z8,z1262,z5])],[(0,[z1,z2,z1263,z8,z5,z6]),(0,[z13,z2,z195,z152,z5,z6]),(0,[z1,z2,z442,z8,z5,z12]),(0,[z1,z2,z3,z8,z5,z869])],[(0,[z0,z7,z3,z8,z5,z304]),(0,[z1,z2,z3,z1264,z5,z6]),(0,[z1,z2,z1265,z3,z8,z5]),(0,[z1,z26,z248,z8,z5,z6]),(0,[z13,z1,z713,z8,z5,z6]),(0,[z1,z482,z3,z8,z5,z264]),(0,[z1,z17,z8,z5,z620,z6])]],
   [[(0,[z1,z413,z17,z8,z5,z6]),(0,[z1,z26,z152,z8,z5,z6]),(0,[z1,z2,z8,z284,z66,z6]),(0,[z1,z2,z1266,z3,z8,z5]),(0,[z2,z438,z3,z8,z5,z12]),(0,[z1,z2,z146,z8,z5,z306]),(0,[z694,z2,z3,z8,z5,z12]),(0,[z1,z2,z1267,z8,z5,z6])],[(0,[z13,z1,z2,z1268,z5,z6]),(0,[z414,z1,z2,z8,z5,z96]),(0,[z1,z2,z16,z3,z706,z8])],[(0,[z215,z1,z2,z8,z5,z143]),(0,[z1,z2,z442,z108,z5,z6]),(0,[z1,z2,z62,z34,z5,z12])],[(0,[z1269,z1,z2,z8,z5,z6]),(0,[z1,z2,z24,z152,z5,z6]),(0,[z1,z2,z8,z1270,z5,z6]),(0,[z1271,z2,z3,z8,z5,z6])],[(0,[z1,z2,z24,z8,z5,z110]),(0,[z1,z2,z24,z8,z5,z795]),(0,[z1,z2,z24,z5,z6,z116]),(0,[z1,z2,z157,z3,z232,z5])],[(0,[z46,z1,z7,z8,z5,z6]),(0,[z64,z1,z423,z99,z5,z6]),(0,[z1,z2,z1272,z8,z5,z6])],[(0,[z1,z2,z1124,z8,z5,z6]),(0,[z21,z1,z2,z552,z8,z5]),(0,[z1,z2,z369,z8,z141,z6]),(0,[z1,z2,z3,z149,z8,z12]),(0,[z365,z2,z3,z8,z5,z12]),(0,[z1,z2,z1273,z3,z8,z5]),(0,[z1,z2,z126,z8,z94,z31]),(0,[z1,z24,z816,z8,z5,z6]),(0,[z1,z2,z3,z1274,z5,z6]),(0,[z1,z2,z1275,z8,z5,z6])],[(0,[z21,z1,z14,z8,z5,z6]),(0,[z1,z26,z8,z249,z5,z6]),(0,[z1,z2,z808,z8,z5,z6])],[(0,[z46,z215,z2,z8,z5,z6]),(0,[z1,z2,z244,z8,z5,z12]),(0,[z1,z2,z948,z8,z5,z12]),(0,[z1,z2,z3,z1276,z8,z5]),(0,[z1,z2,z3,z8,z5,z1277])],[(0,[z1,z2,z3,z8,z5,z1278]),(0,[z1,z2,z3,z1279,z8,z6]),(0,[z13,z21,z26,z8,z5,z6]),(0,[z1,z2,z8,z5,z12,z895])],[(0,[z1,z2,z17,z8,z93,z6]),(0,[z1,z1280,z2,z8,z5,z6]),(0,[z45,z2,z3,z8,z55,z31]),(0,[z1,z2,z17,z8,z5,z12]),(0,[z1,z2,z17,z8,z1281,z6])],[(0,[z328,z1,z252,z8,z5,z6])],[(0,[z13,z1,z2,z318,z5,z6]),(0,[z13,z1,z2,z152,z5,z12]),(0,[z1,z1042,z3,z8,z5,z6]),(0,[z1,z1282,z3,z8,z5,z6]),(0,[z1,z2,z54,z8,z141,z6]),(0,[z1,z2,z1283,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z1284]),(0,[z1,z2,z1285,z3,z5,z6]),(0,[z1286,z1,z2,z8,z5,z6])],[(0,[z215,z1,z28,z8,z5,z6]),(0,[z13,z2,z583,z8,z5,z6]),(0,[z1,z2,z1287,z8,z5,z6])],[(0,[z13,z1,z2,z4,z5,z6]),(0,[z1,z2,z8,z5,z6,z719]),(0,[z21,z1,z2,z8,z346,z6]),(0,[z1,z2,z17,z197,z5,z6]),(0,[z246,z1,z24,z8,z5,z12]),(0,[z1,z2,z950,z17,z8,z5])],[(0,[z1,z2,z244,z8,z5,z306]),(0,[z1,z2,z348,z3,z8,z432])]],
   [[(0,[z455,z2,z3,z8,z5,z12]),(0,[z1,z2,z3,z8,z5,z1288]),(0,[z1,z82,z3,z766,z5,z6])],[(0,[z13,z1,z2,z8,z5,z236]),(0,[z1,z2,z3,z8,z1079,z6]),(0,[z1,z2,z3,z8,z5,z989]),(0,[z127,z2,z3,z8,z5,z796]),(0,[z1289,z2,z3,z8,z5,z6])],[(0,[z21,z1,z2,z259,z5,z6]),(0,[z1,z2,z243,z3,z5,z31]),(1,[z1,z2,z8,z5,z870])],[(0,[z1,z2,z3,z8,z5,z1290]),(0,[z255,z1,z2,z8,z5,z392]),(0,[z13,z21,z2,z8,z284,z6]),(0,[z1,z2,z285,z5,z66,z6]),(0,[z1,z2,z369,z8,z284,z6]),(0,[z21,z1,z68,z8,z69,z6]),(0,[z21,z1,z114,z8,z5,z115]),(0,[z40,z2,z3,z8,z147,z31])],[(0,[z1,z2,z3,z8,z93,z304]),(0,[z1,z2,z3,z8,z385,z31]),(0,[z1,z2,z172,z8,z141,z6])],[(0,[z1,z2,z964,z8,z5,z6]),(0,[z13,z21,z2,z285,z5,z6]),(0,[z1,z1248,z3,z8,z5,z6])],[(0,[z1,z7,z163,z8,z5,z6]),(0,[z1,z2,z3,z8,z1291,z6]),(0,[z1,z26,z8,z147,z5,z6])],[(0,[z1292,z1,z26,z8,z5,z6]),(1,[z1,z26,z8,z66,z6]),(0,[z13,z2,z744,z8,z5,z6]),(0,[z1,z2,z8,z5,z31,z719]),(0,[z21,z1,z82,z90,z5,z6]),(0,[z222,z2,z72,z368,z5,z6]),(0,[z1,z2,z83,z8,z5,z12]),(0,[z722,z2,z17,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1293]),(0,[z13,z1,z2,z8,z5,z753]),(0,[z1,z2,z3,z8,z5,z223]),(0,[z1,z2,z1294,z3,z5,z6]),(0,[z1,z1295,z3,z8,z5,z6])],[(0,[z13,z1,z26,z8,z5,z6]),(0,[z1,z2,z3,z8,z1296,z6]),(0,[z1,z2,z81,z8,z5,z12]),(0,[z464,z2,z3,z8,z5,z31]),(0,[z1,z2,z8,z1001,z141,z6])],[(0,[z1,z2,z17,z318,z5,z6]),(0,[z46,z1,z2,z8,z1205,z6]),(0,[z1,z2,z503,z419,z5,z6]),(0,[z1,z2,z3,z8,z768,z6]),(0,[z1,z2,z3,z35,z6,z470])],[(0,[z13,z2,z480,z8,z5,z6]),(0,[z21,z1,z2,z8,z5,z814]),(0,[z1,z2,z1078,z8,z5,z12]),(0,[z1,z2,z1297,z3,z8,z5])],[(0,[z1,z2,z17,z4,z5,z6]),(0,[z1,z2,z976,z3,z5,z6]),(0,[z1,z2,z3,z1298,z8,z5]),(0,[z21,z1,z2,z8,z5,z354]),(0,[z21,z1,z2,z149,z8,z6]),(0,[z21,z1,z2,z16,z8,z19]),(0,[z1,z2,z530,z3,z72,z6])],[(0,[z731,z7,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1299,z6]),(0,[z1,z2,z1300,z8,z5,z6]),(0,[z327,z1,z26,z8,z5,z6]),(0,[z1,z22,z3,z8,z5,z15]),(0,[z1,z2,z1301,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1302]),(0,[z1,z2,z277,z8,z5,z6])],[(0,[z1,z2,z1303,z8,z5,z6]),(0,[z13,z45,z2,z8,z55,z6]),(0,[z45,z2,z8,z242,z55,z6]),(0,[z1304,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1010]),(0,[z1,z2,z1305,z8,z5,z6]),(0,[z1,z2,z3,z41,z5,z6]),(0,[z1,z2,z3,z8,z1306,z6]),(0,[z1,z2,z8,z1307,z5,z6])]],
   [[(0,[z215,z1,z2,z8,z5,z6]),(0,[z1,z1308,z2,z8,z5,z6]),(0,[z1,z26,z3,z8,z284,z6]),(0,[z64,z1,z2,z530,z3,z6])],[(0,[z1,z2,z1309,z8,z5,z6]),(0,[z1,z2,z407,z8,z5,z12]),(0,[z1,z2,z336,z24,z8,z5]),(0,[z1,z58,z140,z3,z8,z6]),(0,[z1,z2,z125,z1077,z5,z6]),(0,[z1,z2,z65,z442,z76,z6])],[(0,[z1,z2,z8,z5,z6,z1169]),(0,[z1,z2,z1310,z8,z5,z6]),(0,[z1,z26,z3,z285,z5,z6]),(0,[z1311,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1312])],[(1,[z1,z2,z285,z66,z6]),(0,[z1,z2,z1313,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1314]),(0,[z1,z58,z3,z259,z73,z6])],[(0,[z1,z2,z3,z318,z5,z304]),(0,[z1,z393,z2,z8,z5,z31]),(0,[z1,z2,z1315,z8,z5,z6]),(0,[z1,z2,z3,z290,z75,z6]),(0,[z1,z2,z3,z8,z5,z1316])],[(0,[z21,z1,z2,z8,z5,z361]),(0,[z1,z2,z1317,z8,z5,z6]),(0,[z1,z461,z17,z8,z5,z6]),(0,[z1,z17,z8,z657,z5,z6]),(0,[z1,z82,z3,z452,z5,z6]),(0,[z1,z2,z1318,z8,z5,z6])],[(0,[z1,z2,z3,z4,z5,z304]),(0,[z1,z2,z8,z987,z5,z6]),(0,[z1,z2,z1319,z8,z5,z6]),(0,[z23,z1,z2,z8,z5,z800]),(0,[z1,z2,z243,z16,z3,z6])],[(0,[z13,z1,z2,z8,z77,z6]),(0,[z1,z2,z3,z1114,z5,z6]),(0,[z1,z2,z1320,z8,z5,z6])],[(0,[z1,z2,z254,z8,z5,z31]),(0,[z1,z2,z17,z8,z5,z52]),(0,[z1,z312,z2,z8,z5,z12]),(0,[z13,z464,z2,z8,z5,z6]),(0,[z1,z2,z347,z8,z5,z12]),(0,[z2,z17,z8,z5,z1033,z6]),(0,[z1,z2,z3,z8,z1205,z6])],[(0,[z13,z1,z26,z152,z5,z6]),(0,[z1,z2,z1321,z8,z5,z6]),(0,[z64,z1,z3,z99,z5,z12]),(0,[z1,z198,z24,z8,z5,z6])],[(0,[z21,z1,z2,z8,z5,z304]),(0,[z1,z2,z157,z17,z5,z120]),(0,[z1,z2,z3,z8,z5,z1322])],[(0,[z1,z645,z17,z8,z5,z6]),(0,[z215,z1,z2,z8,z5,z96]),(0,[z1,z998,z3,z8,z5,z12]),(0,[z1,z2,z530,z17,z8,z6])],[(0,[z216,z28,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z1001,z6])],[(0,[z1,z26,z33,z8,z5,z6]),(0,[z1,z2,z8,z242,z5,z31]),(0,[z1,z2,z530,z3,z606,z8]),(0,[z1,z2,z65,z3,z266,z76])],[(0,[z13,z1,z2,z8,z385,z6]),(0,[z1,z2,z3,z8,z5,z1323]),(0,[z1,z2,z3,z5,z6,z1324])],[(0,[z1,z2,z3,z8,z999,z6]),(0,[z28,z731,z3,z8,z5,z6]),(0,[z13,z21,z2,z8,z5,z12]),(0,[z1,z2,z3,z8,z346,z31]),(0,[z1,z2,z3,z8,z5,z1325])]],
   [[(0,[z1,z2,z3,z717,z5,z6]),(0,[z21,z1,z2,z8,z5,z755]),(0,[z1,z2,z1326,z8,z5,z6]),(0,[z642,z2,z3,z8,z147,z6]),(0,[z63,z2,z3,z8,z5,z796]),(0,[z1,z114,z3,z522,z8,z5])],[(0,[z1,z2,z1327,z8,z5,z6]),(0,[z1,z2,z17,z8,z284,z6]),(0,[z1,z58,z17,z8,z73,z6])],[(0,[z1,z2,z3,z5,z1005,z6]),(0,[z89,z2,z3,z108,z5,z6]),(0,[z1,z2,z3,z8,z5,z1328])],[(0,[z1,z477,z17,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z31]),(0,[z1,z2,z17,z285,z5,z6]),(0,[z1,z2,z24,z8,z5,z196])],[(0,[z1,z2,z1329,z8,z5,z6]),(0,[z2,z3,z8,z714,z5,z6]),(0,[z1330,z1,z2,z8,z5,z6]),(0,[z1331,z1,z2,z8,z5,z6])],[(0,[z1,z2,z17,z8,z77,z6]),(0,[z1,z2,z54,z8,z5,z12]),(0,[z2,z3,z8,z147,z952,z6]),(0,[z1,z2,z442,z8,z5,z31]),(0,[z1,z2,z24,z865,z5,z6]),(0,[z255,z2,z184,z8,z5,z6]),(0,[z1,z2,z65,z3,z373,z6]),(0,[z1,z2,z3,z8,z309,z5])],[(0,[z1,z2,z24,z8,z309,z5])],[(0,[z1,z2,z3,z1332,z8,z5]),(0,[z23,z1,z2,z8,z5,z12])],[(0,[z0,z7,z17,z8,z5,z6]),(0,[z1,z2,z1333,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z811]),(0,[z1,z2,z3,z8,z5,z403]),(0,[z1,z2,z3,z8,z5,z1334])],[(0,[z1,z2,z926,z3,z8,z6]),(0,[z13,z2,z8,z5,z339,z6]),(0,[z1,z2,z1335,z8,z5,z6]),(1,[z1,z816,z8,z5,z6])],[(0,[z1,z17,z8,z5,z670,z6]),(0,[z1,z2,z3,z248,z155,z5])],[(0,[z1,z2,z163,z8,z5,z31]),(0,[z1,z2,z26,z8,z284,z6]),(0,[z13,z194,z2,z8,z5,z6]),(0,[z1,z22,z3,z8,z5,z280]),(0,[z1,z114,z3,z8,z5,z869])],[(0,[z1,z26,z3,z8,z5,z12]),(0,[z40,z2,z3,z8,z952,z6]),(0,[z1,z2,z409,z8,z5,z6]),(0,[z1,z2,z17,z8,z5,z266]),(0,[z1,z3,z8,z5,z869,z280]),(0,[z1,z2,z3,z75,z6,z447])],[(0,[z1,z2,z26,z285,z5,z6]),(0,[z1,z2,z947,z8,z5,z31])],[(0,[z1,z2,z1336,z8,z5,z6]),(0,[z89,z1,z26,z8,z5,z6]),(0,[z469,z1,z26,z8,z5,z6]),(0,[z1,z2,z3,z1060,z5,z6]),(0,[z1337,z1,z2,z8,z5,z6]),(0,[z1,z2,z106,z8,z5,z870])],[(0,[z1,z2,z3,z8,z77,z304]),(0,[z13,z1,z774,z8,z5,z6]),(0,[z13,z2,z8,z352,z5,z6]),(0,[z1,z26,z8,z94,z5,z6]),(0,[z405,z1,z2,z158,z5,z6]),(0,[z1,z2,z244,z8,z5,z31]),(0,[z1,z2,z24,z1260,z5,z6]),(0,[z1,z2,z3,z8,z5,z723])]],
   [[(0,[z1,z26,z8,z5,z55,z6]),(0,[z13,z1,z2,z8,z66,z211]),(0,[z1,z2,z8,z5,z719,z12]),(0,[z1,z2,z3,z8,z1338,z6])],[(0,[z13,z1,z2,z552,z8,z5]),(0,[z1,z2,z3,z1231,z8,z5]),(0,[z1,z109,z390,z3,z8,z5]),(0,[z1,z1339,z2,z3,z8,z5])],[(1,[z1,z26,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1340]),(0,[z13,z1,z14,z8,z5,z6]),(0,[z45,z1,z26,z8,z5,z6]),(0,[z544,z1,z2,z8,z66,z6]),(0,[z1,z2,z336,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z1341]),(0,[z1,z28,z17,z8,z5,z12]),(0,[z1,z26,z8,z5,z115,z6]),(0,[z1,z47,z17,z8,z5,z6]),(0,[z1,z2,z8,z5,z6,z1108]),(0,[z46,z2,z8,z147,z5,z6]),(0,[z1,z2,z3,z8,z5,z1342]),(0,[z1,z2,z1343,z8,z5,z6])],[(0,[z1,z2,z17,z8,z5,z174]),(0,[z1,z2,z1344,z8,z5,z6]),(0,[z1,z2,z1032,z8,z5,z6]),(0,[z1,z2,z17,z8,z249,z18]),(0,[z1,z2,z1345,z3,z8,z6]),(0,[z1,z2,z3,z8,z862,z6]),(0,[z1,z2,z1346,z8,z5,z6])],[(0,[z255,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z1347,z6]),(0,[z1,z312,z26,z8,z5,z6]),(0,[z1,z1348,z2,z8,z5,z6]),(0,[z305,z1,z2,z8,z5,z354]),(0,[z1,z2,z1349,z8,z5,z6]),(0,[z1,z2,z125,z3,z5,z12]),(0,[z630,z2,z3,z8,z5,z12]),(0,[z46,z2,z8,z5,z6,z12]),(0,[z246,z1,z24,z8,z5,z31])],[(0,[z215,z216,z28,z8,z5,z6]),(0,[z1,z2,z467,z8,z5,z12]),(0,[z1,z2,z3,z8,z291,z18]),(0,[z1,z2,z423,z8,z5,z6]),(0,[z1,z114,z17,z8,z5,z115])],[(0,[z1,z2,z1120,z8,z5,z6]),(0,[z1,z2,z1350,z8,z5,z6]),(0,[z1,z1351,z2,z8,z5,z6]),(0,[z1,z2,z1352,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1353])],[(0,[z1,z2,z1050,z8,z5,z12]),(0,[z1,z92,z17,z8,z5,z6]),(0,[z1,z2,z1354,z8,z5,z6])],[(0,[z13,z1,z2,z8,z346,z6]),(0,[z13,z1,z2,z105,z8,z5]),(0,[z1,z2,z244,z8,z5,z278]),(0,[z1,z2,z355,z33,z5,z6])],[(0,[z1,z2,z8,z5,z96,z278]),(0,[z222,z2,z17,z72,z5,z6]),(0,[z2,z17,z8,z1086,z5,z6]),(0,[z1,z2,z1355,z8,z5,z6])],[(0,[z13,z1,z2,z8,z66,z31]),(0,[z21,z1,z2,z8,z5,z1014]),(0,[z1,z2,z71,z33,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1356]),(0,[z46,z2,z17,z8,z5,z12]),(0,[z1,z2,z17,z248,z5,z11])],[(1,[z46,z7,z8,z5,z6]),(0,[z13,z1,z2,z8,z839,z6])],[(0,[z21,z1,z2,z8,z5,z392]),(0,[z46,z2,z195,z8,z5,z6]),(0,[z1,z2,z83,z8,z5,z31]),(0,[z1,z109,z3,z8,z5,z869])],[(0,[z13,z1,z2,z8,z5,z842]),(0,[z1,z26,z8,z34,z5,z6]),(0,[z1,z2,z3,z1230,z5,z6]),(0,[z1,z2,z1357,z8,z5,z6])]],
   [[(0,[z13,z1,z2,z8,z5,z846]),(0,[z1,z2,z351,z8,z5,z278]),(0,[z1358,z1,z2,z8,z5,z6])],[(0,[z21,z1,z2,z8,z5,z981]),(0,[z2,z3,z8,z952,z5,z6]),(0,[z1,z2,z3,z8,z5,z1359])],[(0,[z13,z0,z7,z8,z5,z6]),(1,[z1,z26,z152,z5,z6]),(0,[z13,z1,z82,z90,z5,z6]),(0,[z21,z1,z2,z606,z8,z5]),(0,[z222,z2,z3,z72,z5,z20]),(0,[z1,z2,z707,z34,z5,z6])],[(0,[z0,z1,z26,z8,z5,z6]),(0,[z1,z2,z1360,z3,z8,z5]),(0,[z1,z2,z1361,z8,z5,z6]),(0,[z1,z14,z3,z8,z284,z6]),(0,[z1,z2,z3,z768,z76,z6]),(0,[z1,z2,z3,z5,z768,z6])],[(0,[z1,z2,z3,z248,z5,z460]),(0,[z1,z2,z225,z24,z8,z6]),(0,[z1,z2,z65,z157,z16,z3])],[(0,[z1,z14,z3,z285,z5,z6]),(0,[z1,z2,z8,z5,z96,z56]),(0,[z1,z3,z766,z99,z5,z6]),(0,[z1,z2,z65,z3,z322,z6])],[(0,[z13,z1,z2,z530,z8,z6]),(0,[z551,z1,z3,z99,z5,z6]),(0,[z63,z2,z244,z8,z5,z12]),(0,[z1,z2,z226,z8,z5,z6])],[(0,[z1,z2,z26,z8,z5,z12]),(0,[z13,z1,z2,z16,z8,z19]),(0,[z139,z2,z3,z8,z5,z12]),(0,[z1,z2,z3,z8,z5,z870])],[(0,[z1,z2,z1362,z3,z8,z6]),(0,[z89,z21,z2,z108,z5,z6]),(0,[z1,z2,z8,z5,z1363,z6]),(0,[z1,z2,z106,z8,z5,z306]),(0,[z1,z2,z407,z8,z5,z31]),(0,[z1,z2,z1364,z8,z5,z6])],[(0,[z1,z1365,z26,z8,z5,z6]),(0,[z1,z26,z8,z5,z6,z278]),(0,[z1,z1366,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z160]),(0,[z1,z2,z3,z1367,z5,z6]),(0,[z1,z2,z1166,z8,z5,z12]),(0,[z1,z2,z3,z8,z5,z800]),(0,[z1,z2,z3,z8,z5,z1368]),(0,[z1,z2,z3,z8,z5,z266])],[(0,[z216,z28,z3,z8,z5,z392]),(0,[z13,z1,z14,z8,z66,z6]),(0,[z1,z2,z3,z1180,z5,z6]),(0,[z21,z1,z2,z8,z1041,z6]),(0,[z476,z2,z3,z8,z5,z31]),(0,[z1,z2,z3,z8,z5,z1369])],[(0,[z21,z1,z2,z8,z5,z1043]),(0,[z1,z2,z1370,z8,z5,z6])],[(0,[z1,z2,z3,z1103,z5,z6]),(0,[z1,z2,z24,z8,z5,z223]),(0,[z2,z3,z8,z5,z12,z490]),(0,[z46,z1,z2,z8,z1281,z6])],[(0,[z255,z1,z2,z8,z66,z6]),(0,[z45,z2,z54,z8,z55,z6]),(0,[z1,z2,z51,z33,z5,z12]),(0,[z1,z2,z530,z3,z8,z31])],[(0,[z46,z7,z17,z8,z5,z6]),(0,[z1,z2,z442,z8,z55,z6]),(0,[z1,z2,z3,z8,z1371,z6])],[(0,[z1,z7,z17,z8,z5,z6]),(0,[z1,z892,z3,z8,z5,z6]),(1,[z1,z3,z766,z5,z6])]],
   [[(0,[z13,z1,z2,z8,z5,z361]),(0,[z13,z1,z2,z157,z5,z120]),(0,[z40,z2,z369,z8,z147,z6]),(0,[z64,z1,z3,z99,z5,z31])],[(0,[z13,z1,z2,z8,z962,z6]),(0,[z1,z2,z3,z8,z6,z1055]),(0,[z1,z2,z3,z8,z5,z1372]),(0,[z1373,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z1374,z5,z6]),(0,[z1375,z2,z3,z8,z5,z6])],[(0,[z1,z2,z17,z8,z5,z236]),(0,[z1,z2,z1159,z8,z5,z6])],[(0,[z13,z1,z2,z965,z5,z6]),(0,[z1,z2,z24,z41,z5,z6]),(0,[z1,z82,z226,z90,z5,z6])],[(0,[z1,z2,z8,z5,z96,z354]),(0,[z1,z2,z1162,z8,z5,z6])],[(0,[z1,z2,z382,z3,z8,z417]),(0,[z1,z674,z17,z8,z5,z6]),(0,[z1,z2,z258,z8,z5,z6])],[(0,[z216,z21,z28,z8,z5,z6]),(0,[z13,z21,z2,z8,z5,z31]),(0,[z21,z1,z109,z8,z5,z280]),(0,[z1,z2,z369,z8,z5,z31]),(0,[z1,z2,z1163,z8,z5,z6])],[(0,[z1,z26,z477,z8,z5,z6]),(0,[z1,z68,z3,z8,z69,z12]),(0,[z1,z3,z8,z766,z5,z6])],[(0,[z1,z2,z8,z1376,z5,z6]),(0,[z1,z26,z3,z8,z5,z211]),(0,[z1,z2,z3,z285,z66,z6]),(0,[z1,z2,z146,z8,z5,z211]),(0,[z1,z2,z8,z1377,z5,z6]),(0,[z1,z2,z1228,z8,z5,z6]),(0,[z2,z3,z8,z5,z31,z12])],[(0,[z21,z1,z58,z8,z73,z6]),(0,[z1,z2,z3,z8,z5,z1122]),(0,[z1,z2,z3,z8,z1378,z6]),(0,[z1,z1093,z3,z8,z5,z6]),(0,[z1,z80,z17,z8,z5,z6]),(0,[z1,z1379,z2,z8,z5,z6])],[(0,[z1,z2,z3,z8,z93,z6]),(0,[z1,z2,z3,z8,z5,z12]),(0,[z255,z1,z2,z8,z5,z143]),(0,[z1,z1028,z3,z8,z5,z6]),(0,[z1,z2,z1380,z3,z8,z5]),(0,[z1,z2,z3,z8,z1281,z6]),(0,[z1,z2,z100,z8,z94,z6])],[(0,[z255,z216,z28,z8,z5,z6]),(0,[z13,z1,z2,z8,z5,z211]),(0,[z13,z1,z2,z8,z5,z755]),(0,[z21,z1,z2,z8,z5,z20]),(0,[z1,z404,z3,z8,z73,z6]),(0,[z1381,z1,z2,z8,z5,z6]),(0,[z1,z2,z67,z8,z1001,z6])],[(0,[z1,z2,z413,z8,z5,z6]),(0,[z1,z26,z8,z5,z6,z280]),(0,[z1,z2,z244,z8,z5,z361]),(0,[z1,z2,z3,z8,z5,z1126]),(0,[z1,z2,z54,z8,z5,z31]),(0,[z1,z2,z1016,z8,z5,z31]),(0,[z1,z2,z1382,z8,z5,z6]),(0,[z1,z58,z125,z3,z73,z6])],[(0,[z1,z2,z1383,z8,z5,z6]),(0,[z1,z2,z3,z1384,z5,z6])],[(0,[z1,z2,z3,z197,z5,z6]),(0,[z1,z2,z1385,z8,z5,z6])],[(0,[z1,z2,z3,z1386,z5,z6]),(0,[z13,z527,z2,z8,z5,z6]),(0,[z1,z14,z3,z8,z5,z12]),(0,[z1,z2,z3,z1268,z5,z6]),(0,[z1,z2,z3,z35,z75,z12]),(0,[z1,z2,z608,z8,z166,z6]),(0,[z1,z2,z3,z824,z5,z6]),(0,[z1,z2,z1387,z8,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 478) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 478).take 479) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 957).take 490) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1447).take 114) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1561)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [478, 479, 490, 114] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 96).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 96).take 86).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 182).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 273).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 371).take 89).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 460).take 52).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [96, 86, 91, 98, 89, 52] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38649

theorem PEqualNP.Outside.L_meta_38649 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808362 * 2 ^ 32 + 4241025160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808362 * 2 ^ 32 + 4241025160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38649.solve